/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import CaseStudies.Hashbrown.Proofs.StdCli.StartupLayout
public import CaseStudies.Hashbrown.Proofs.StdCli.MemOps
public import ProofLib.StdStartup.TopInit
import ProofLib.StdStartup.StartupCompose
import ProofLib.StdStartup.MuslStage1
import ProofLib.StdStartup.MuslTls
import ProofLib.StdStartup.StdDetect
import ProofLib.StdStartup.LangStartPre
import ProofLib.StdStartup.OutlineAtomics
public import ProofLib.SepLogic.WP.StepsProcess
public import ProofLib.SepLogic.WP.StepsProcessSyscalls
public import ProofLib.SepLogic.WP.StepsProcessLlsc
import ProofLib.SyscallModels
public meta import ProofLib.LiteralFetchLint
import ProofLib.BV.Arith
import ProofLib.BV.WidthNorm

/-!
# Layout-Generic Pre-`userMain` Startup Proof

Layout-generic `_start` to `userMain` execution for stock-`musl` LLD-linked `hashbrown_cli.elf`,
covering `static_init_tls`, `libc_start_init` (`__init_cpu_features`), and `lang_start_internal`
(`ThreadId`, stdio `poll`, `SIGPIPE`, `sysconf`, alternate signal-stack setup, and
`SIGSEGV`/`SIGBUS` `rt_sigaction`).
-/

set_option autoImplicit false

@[expose] public section

namespace CaseStudies.Hashbrown.Proofs.StdCli

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection ProofLib.StdStartup StdBinaryLayout

/-! ## Alternate Signal-Stack Size Helpers and `HbPreMainCode` -/

/-- Requested usable alternate signal stack size `max (getauxval(AT_MINSIGSTKSZ)) 0x3000`
    computed identically by `make_handler` (`stack_overflow::imp::make_handler`) and
    `drop_handler` (`stack_overflow::imp::drop_handler`). -/
def hbAltstackReqSz (entries : List (BitVec 64 × BitVec 64)) : Nat :=
  let v := ((entries.find? (·.1 == 51#64)).map Prod.snd).getD 0#64
  max v.toNat 12288

/-- Page-aligned usable alternate signal stack byte length (`pageAlignUp (hbAltstackReqSz entries)`),
    matching `HbAltstackInv` (`[altBase, altBase + 4096)` guard page + `[altBase + 4096, + altRawSz)` RW). -/
def hbExpectedAltRawSz (entries : List (BitVec 64 × BitVec 64)) : Nat :=
  Arm64.pageAlignUp (hbAltstackReqSz entries)

theorem hbExpectedAltRawSz_spec {entries : List (BitVec 64 × BitVec 64)}
    (hbnd : ∀ e ∈ entries, e.1 = 51#64 → e.2.toNat ≤ 524288) :
    hbExpectedAltRawSz entries % 4096 = 0 ∧
    12288 ≤ hbExpectedAltRawSz entries ∧
    hbExpectedAltRawSz entries ≤ 524288 := by
  have hreq : 12288 ≤ hbAltstackReqSz entries ∧ hbAltstackReqSz entries ≤ 524288 := by
    unfold hbAltstackReqSz
    cases hfind : entries.find? (·.1 == 51#64) with
    | none => simp
    | some kv =>
      have hmem := List.mem_of_find?_eq_some hfind
      have heq : kv.1 = 51#64 := by simpa using List.find?_some hfind
      have hle := hbnd kv hmem heq
      simp only [Option.map_some, Option.getD_some]
      omega
  unfold hbExpectedAltRawSz Arm64.pageAlignUp Arm64.PAGE_SIZE
  omega

local macro "iAdrp " rd:term:arg pc:term:arg t:term:arg : term =>
  `(Instr.adr true $rd (adrpOff $pc $t))
local macro "iAdr " rd:term:arg pc:term:arg t:term:arg : term =>
  `(Instr.adr false $rd (($t) - ($pc)))
local macro "iAddLo12 " rd:term:arg rn:term:arg t:term:arg : term =>
  `(Instr.addSubImm .W64 .ADD $rd $rn (($t).truncate 12) false)
local macro "iLdr64Lo12 " rt:term:arg rn:term:arg t:term:arg : term =>
  `(Instr.ldr .W64 .X64 false $rt (.Offset $rn (pageLo12 $t)))
local macro "iStr64Lo12 " rt:term:arg rn:term:arg t:term:arg : term =>
  `(Instr.str .X64 $rt (.Offset $rn (pageLo12 $t)))
local macro "iLdr32Lo12 " rt:term:arg rn:term:arg t:term:arg : term =>
  `(Instr.ldr .W32 .W32 false $rt (.Offset $rn (pageLo12 $t)))
local macro "iStr32Lo12 " rt:term:arg rn:term:arg t:term:arg : term =>
  `(Instr.str .W32 $rt (.Offset $rn (pageLo12 $t)))
local macro "iLdr8Lo12 " rt:term:arg rn:term:arg t:term:arg : term =>
  `(Instr.ldr .W32 .B8 false $rt (.Offset $rn (pageLo12 $t)))
local macro "iStr8Lo12 " rt:term:arg rn:term:arg t:term:arg : term =>
  `(Instr.str .B8 $rt (.Offset $rn (pageLo12 $t)))
local macro "iBl " pc:term:arg t:term:arg : term =>
  `(Instr.bl (($t) - ($pc)))
local macro "iB " pc:term:arg t:term:arg : term =>
  `(Instr.b (($t) - ($pc)))

def hbLibcStartMainInstrs (L : StdBinaryLayout) : List Instr :=
  (libcStartMainInstrs L).take 14 ++
  [decodeWord 0xd503201f#32, iAdr .x3 (L.libcStartMainAddr + 0x3c#64) L.libcStartMainStage2Addr] ++
  (libcStartMainInstrs L).drop 16

def hbInitLibcPreInstrs (C : HbCliLayout) (S : HbStartupLayout) : List Instr :=
  let L := C.std
  (initLibcInstrs L).take 12 ++
  [iAdrp .x0 (L.initLibcAddr + 0x30#64) S.gotEnvironAddr, decodeWord 0xd2800002#32,
   iLdr64Lo12 .x0 .x0 S.gotEnvironAddr] ++
  ((initLibcInstrs L).drop 15).take 29 ++
  [iAdrp .x2 (L.initLibcAddr + 0xb0#64) S.gotPrognameFullAddr,
   iAdrp .x1 (L.initLibcAddr + 0xb4#64) S.gotPrognameAddr,
   .addSubImm .W64 .ADD .x0 .x20 1#12 false,
   iLdr64Lo12 .x2 .x2 S.gotPrognameFullAddr,
   iLdr64Lo12 .x1 .x1 S.gotPrognameAddr,
   .str .X64 .x20 (.Offset .x2 0#64),
   .logicalShift .W64 .ORR .x2 .xzr .x1 .LSL 0,
   .str .X64 .x20 (.Offset .x1 0#64),
   .b 0x1c#64]

def hbStaticInitTlsInstrs (L : StdBinaryLayout) : List Instr :=
  (staticInitTlsInstrs L).take 98 ++
  [decodeWord 0xd503201f#32, iAdr .x0 (L.staticInitTlsAddr + 0x18c#64) L.builtinTlsAddr] ++
  (staticInitTlsInstrs L).drop 100

def hbStage1Chunks (C : HbCliLayout) (S : HbStartupLayout) : List CodeChunk :=
  let L := C.std
  [ .instrs0 L.startAddr (startInstrs L),
    .instrs0 L.startCAddr (startCInstrs L),
    .instrs0 L.libcStartMainAddr (hbLibcStartMainInstrs L),
    .instrs0 L.initLibcAddr (hbInitLibcPreInstrs C S),
    .instrs L.initLibcAddr 0xe8 (((initLibcInstrs L).drop 58).take 14),
    .instrs L.initLibcAddr 0x16c (((initLibcInstrs L).drop 91).take 6),
    .instrs L.initLibcAddr 0x1c8 ((initLibcInstrs L).drop 114),
    .words L.dummy1Addr dummy1Words,
    .instrs0 L.staticInitTlsAddr (hbStaticInitTlsInstrs L),
    .instrs0 L.copyTlsAddr (copyTlsInstrs L),
    .instrs0 L.initTpAddr (initTpInstrs L),
    .words L.setThreadAreaAddr setThreadAreaWords ]

def hbCpuCtorWords0 : List (BitVec 32) :=
  [ 0xa9bc53f3#32, 0xa9015bf5#32, 0xa90263f7#32, 0xa9037bf9#32, 0xb6f014a0#32, 0xf9400021#32,
    0x92790024#32, 0x926e0039#32, 0x927d0038#32, 0x927c0037#32, 0x927b0036#32, 0x927a0035#32,
    0x92400034#32, 0x92700033#32, 0x9273003e#32, 0x92780032#32, 0x92760031#32, 0x92750030#32,
    0x926f002f#32, 0x9261002e#32, 0x9269002d#32, 0x925b002c#32, 0x9268002b#32, 0x9267002a#32,
    0x92550029#32, 0x925e0028#32, 0x92520027#32, 0x92720026#32, 0x927f0022#32, 0x92790005#32,
    0xd2900001#32, 0x36380060#32, 0xd2908001#32, 0xd2808005#32, 0xf27c001f#32 ]

def hbCpuCtorWords1 : List (BitVec 32) :=
  [ 0x9a8110a1#32, 0xf100009f#32, 0xb27e0024#32, 0x9a811081#32, 0xf26d001f#32, 0xb27b0024#32,
    0x9a811081#32, 0xf26c001f#32, 0xb27c0024#32, 0x9a811081#32, 0xf269001f#32, 0xb27d0024#32,
    0x9a811081#32, 0xf277001f#32, 0xb2700024#32, 0x9a811081#32, 0xf268001f#32, 0xb26f0024#32,
    0x9a811081#32, 0xf274001f#32, 0xb27a0024#32, 0x9a811081#32, 0xf27a001f#32, 0xb2740024#32,
    0x9a811081#32, 0xf273001f#32, 0xb26c0024#32, 0x9a811081#32, 0xf272001f#32, 0xb26b0024#32,
    0x9a811081#32, 0xf263001f#32, 0xb2520024#32, 0x9a811081#32, 0xf264001f#32, 0xb24f0024#32,
    0x9a811081#32, 0xf100033f#32, 0xb2540024#32, 0x9a811081#32, 0xf100031f#32, 0xb25a0024#32,
    0x9a811081#32 ]

def hbCpuCtorWords2 : List (BitVec 32) :=
  [ 0xf10002ff#32, 0xb2590024#32, 0x9a811081#32, 0xf10002df#32, 0xb2580024#32, 0x9a811081#32,
    0xf10002bf#32, 0xb2570024#32, 0x9a811081#32, 0xf278001f#32, 0xaa144c21#32, 0xb2790024#32,
    0x9a811081#32, 0xf100027f#32, 0xb2400024#32, 0x9a811081#32, 0xf10003df#32, 0xb2660024#32,
    0x9a811081#32, 0xf100025f#32, 0xb2680024#32, 0x9a811081#32, 0xf100023f#32, 0xb25e0024#32,
    0x9a811081#32, 0xf100021f#32, 0xb25d0024#32, 0x9a811081#32, 0xf10001ff#32, 0xb24e0024#32,
    0x9a811081#32, 0xf10001df#32, 0xb24a0024#32, 0x9a811081#32, 0xf10001bf#32, 0xb2560024#32,
    0x9a811081#32, 0xf100019f#32, 0xb2470024#32, 0x9a811081#32, 0xf100017f#32, 0xb2480024#32,
    0x9a811081#32 ]

def hbCpuCtorWords3 : List (BitVec 32) :=
  [ 0xf100015f#32, 0xb2490024#32, 0x9a811081#32, 0xf100013f#32, 0xb2450024#32, 0x9a811081#32,
    0xf100011f#32, 0xb2750024#32, 0x9a811081#32, 0xf240001f#32, 0xb2780424#32, 0x9a811081#32,
    0xf270001f#32, 0xb26e0024#32, 0x9a811081#32, 0xf271001f#32, 0xb26a0024#32, 0x9a811081#32,
    0xf266001f#32, 0xb2690024#32, 0x9a811081#32, 0xf10000ff#32, 0xb2460024#32, 0x9a811081#32,
    0xf10000df#32, 0xb2650024#32, 0x9a811081#32, 0xf26a001f#32, 0xb2620024#32, 0x9a811081#32,
    0xf100005f#32, 0xb25c0022#32, 0x9a811041#32, 0xf26f001f#32, 0xb2730020#32, 0x9a811001#32,
    0xb2410021#32, 0xf9000061#32, 0xa9415bf5#32, 0xa94263f7#32, 0xa9437bf9#32, 0xa8c453f3#32,
    0xd65f03c0#32 ]

def hbStage2Chunks (C : HbCliLayout) (S : HbStartupLayout) : List CodeChunk :=
  let L := C.std
  [ .instrs0 L.libcStartMainStage2Addr (libcStartMainStage2EntryInstrs L),
    .instrs0 L.libcStartInitAddr (decodeWords [0xa9be7bfd#32, 0x910003fd#32, 0xa90153f3#32] ++
      [ iAdrp .x19 (L.libcStartInitAddr + 0x0c#64) S.gotInitArrayStartAddr,
        iAdrp .x20 (L.libcStartInitAddr + 0x10#64) S.gotInitArrayEndAddr,
        iBl (L.libcStartInitAddr + 0x14#64) L.initFnAddr,
        iLdr64Lo12 .x19 .x19 S.gotInitArrayStartAddr, iLdr64Lo12 .x20 .x20 S.gotInitArrayEndAddr ] ++
      decodeWords [0xeb14027f#32, 0x54000082#32, 0xf8408660#32, 0xd63f0000#32,
                   0x17fffffc#32, 0xa94153f3#32, 0xa8c27bfd#32, 0xd65f03c0#32]),
    .words L.initFnAddr initFnWords,
    .instrs0 L.doInitAddr [ iAdrp .x1 L.doInitAddr L.initializedAddr,
      iLdr8Lo12 .x0 .x1 L.initializedAddr, decodeWord 0x35000160#32,
      iAdrp .x0 (L.doInitAddr + 0x0c#64) (L.gotAddr + 0x30#64), decodeWord 0x52800022#32,
      iStr8Lo12 .x2 .x1 L.initializedAddr, iLdr64Lo12 .x0 .x0 (L.gotAddr + 0x30#64),
      decodeWord 0xb40000c0#32 ],
    .words (L.doInitAddr + 0x34#64) [0xd65f03c0#32],
    .instrs0 L.getauxvalAddr (getauxvalInstrs L),
    .words L.errnoLocationAddr [0xd53bd040#32, 0xd1029000#32, 0xd65f03c0#32],
    .instrs0 L.initLseAddr (decodeWords [0xf81f0ffe#32, 0xd2800200#32] ++
      [ iBl (L.initLseAddr + 0x08#64) L.getauxvalAddr, decodeWord 0x53082000#32,
        iAdrp .x1 (L.initLseAddr + 0x10#64) L.haveLseAtomicsAddr, decodeWord 0xf84107fe#32,
        iStr8Lo12 .x0 .x1 L.haveLseAtomicsAddr, decodeWord 0xd65f03c0#32 ]),
    .instrs0 S.initCpuFeaturesAddr ([decodeWord 0xd503201f#32,
      iAdr .x0 (S.initCpuFeaturesAddr + 0x04#64) S.cpuFeaturesGlobalAddr] ++
      decodeWords [0xf9400000#32, 0xb4000040#32, 0xd65f03c0#32, 0xa9bd7bf3#32, 0xd2800200#32] ++
      [iBl (S.initCpuFeaturesAddr + 0x1c#64) L.getauxvalAddr] ++
      decodeWords [0xaa0003f3#32, 0xd2800340#32] ++
      [iBl (S.initCpuFeaturesAddr + 0x28#64) L.getauxvalAddr] ++
      decodeWords [0xaa0003e2#32, 0xd2800303#32, 0xb2420260#32, 0x9100a3e1#32,
                   0xa901cfe3#32, 0xf90017e2#32] ++
      [iBl (S.initCpuFeaturesAddr + 0x44#64) S.initCpuFeaturesCtorAddr] ++
      decodeWords [0xa8c37bf3#32, 0xd65f03c0#32]),
    .words S.initCpuFeaturesCtorAddr hbCpuCtorWords0,
    .instrs S.initCpuFeaturesCtorAddr 0x8c
      ([iAdrp .x3 (S.initCpuFeaturesCtorAddr + 0x8c#64) S.cpuFeaturesGlobalAddr] ++
       decodeWords [0x9a851021#32, 0xf265001f#32, 0xb27f0025#32] ++
       [iAddLo12 .x3 .x3 S.cpuFeaturesGlobalAddr]),
    .words (S.initCpuFeaturesCtorAddr + 0xa0#64) hbCpuCtorWords1,
    .words (S.initCpuFeaturesCtorAddr + 0x14c#64) hbCpuCtorWords2,
    .words (S.initCpuFeaturesCtorAddr + 0x1f8#64) hbCpuCtorWords3 ]

def hbSigAndSysChunks (C : HbCliLayout) (S : HbStartupLayout) : List CodeChunk :=
  let L := C.std; let sm := L.libcSigactionAddr + 0x30#64
  [ .words L.sccpAddr sccpWords, .instrs0 L.syscallCpAddr (syscallCpInstrs L),
    .words L.syscallRetAddr syscallRetNonnegWords, .instrs0 L.pollAddr (pollInstrs L),
    .instrs0 L.signalAddr (decodeWords (signalWords.take 17) ++
      [iBl (L.signalAddr + 0x44#64) L.sigactionAddr] ++ decodeWords (signalWords.drop 18)),
    .instrs0 L.sigactionAddr (sigactionFastInstrs L),
    .words L.libcSigactionAddr libcSigactionHeadWords,
    .instrs0 sm (decodeWords [0x51000401#32, 0xd2800022#32, 0xd503201f#32] ++
      [iAdr .x0 (sm + 0x0c#64) S.handlerSetAddr] ++
      decodeWords [0x93437c23#32, 0x9ac12041#32, 0x927de462#32, 0x8b020000#32,
                   0x35000161#32, 0xeb4183ff#32, 0xd360fc21#32, 0x540001c1#32] ++
      [iAdrp .x0 (sm + 0x30#64) (L.libcAddr + 1#64), iLdr8Lo12 .x0 .x0 (L.libcAddr + 1#64)] ++
      decodeWords [0x34000220#32, 0xb9408880#32, 0x36e003a0#32, 0xf9400086#32,
                   0x14000022#32, 0x2a0103e5#32, 0x885ffc03#32, 0x2a0300a3#32,
                   0x8802fc03#32, 0x35ffffa2#32, 0x17fffff1#32, 0x91001000#32,
                   0x885ffc03#32, 0x2a030023#32, 0x8802fc03#32, 0x35ffffa2#32, 0x17ffffee#32] ++
      [iAdrp .x5 (sm + 0x7c#64) S.unmaskDoneAddr, iLdr32Lo12 .x0 .x5 S.unmaskDoneAddr] ++
      decodeWords [0x35fffdc0#32, 0xd2c00066#32, 0x910143e1#32, 0xd28010e8#32,
                   0xd2800020#32, 0xd2800002#32, 0xd2800103#32, 0xf9002be6#32,
                   0xd4000001#32, 0x52800020#32] ++
      [ iStr32Lo12 .x0 .x5 S.unmaskDoneAddr, decodeWord 0x17ffffe3#32, decodeWord 0xd5033bbf#32,
        iAdrp .x0 (sm + 0xb8#64) S.eintrValidFlagAddr, decodeWord 0x52800021#32,
        iStr32Lo12 .x1 .x0 S.eintrValidFlagAddr, decodeWord 0xd5033bbf#32, decodeWord 0xf9400086#32 ]),
    .instrs L.libcSigactionAddr 0xfc (libcSigactionIgnTailInstrs L),
    .instrs0 L.sysconfAddr ((sysconfPagesizeInstrs L).take 6 ++
      [decodeWord 0xd503201f#32, iAdr .x0 (L.sysconfAddr + 0x1c#64) L.sysconfValuesAddr] ++
      (sysconfPagesizeInstrs L).drop 8),
    .words (L.sysconfAddr + 0xd8#64) sysconfEpilogueWords,
    .instrs0 S.sigaltstackAddr (
      decodeWords [0xa9bf7bfd#32, 0x910003fd#32, 0xb4000100#32, 0xb9400802#32,
                   0x370800a2#32, 0xf9400804#32, 0xd282ffe3#32, 0xeb03009f#32,
                   0x540000e9#32, 0x37000182#32, 0xd2801088#32, 0xd4000001#32] ++
      [iBl (S.sigaltstackAddr + 0x30#64) L.syscallRetAddr] ++ decodeWords [0xa8c17bfd#32, 0xd65f03c0#32]),
    .instrs0 S.mmapWrapperAddr (
      decodeWords [0xa9bc7bfd#32, 0xf2402cbf#32, 0x910003fd#32, 0x54000381#32,
                   0xa90153f3#32, 0xaa0003f4#32, 0xb27ff7e0#32, 0xeb00003f#32,
                   0x540003a8#32, 0xa9025bf5#32, 0x2a0303f3#32, 0x2a0203f6#32,
                   0x2a0403f5#32, 0x372003b3#32, 0x93407ec2#32, 0x93407ea4#32,
                   0xaa1403e0#32, 0x93407e63#32, 0xd2801bc8#32, 0xd4000001#32,
                   0xf100029f#32, 0xba410800#32, 0x540000a1#32, 0x121c0673#32,
                   0x92800160#32, 0x7100827f#32, 0xda9f0000#32, 0xa94153f3#32,
                   0xa9425bf5#32, 0xa8c47bfd#32] ++ [iB (S.mmapWrapperAddr + 0x78#64) L.syscallRetAddr]),
    .instrs0 S.mprotectWrapperAddr ([decodeWord 0xa9bf7bfd#32,
      iAdrp .x4 (S.mprotectWrapperAddr + 0x04#64) (L.libcAddr + 0x30#64),
      decodeWord 0xaa0003e3#32, decodeWord 0x910003fd#32, iLdr64Lo12 .x4 .x4 (L.libcAddr + 0x30#64)] ++
      decodeWords [0xd2801c48#32, 0x93407c42#32, 0xd1000480#32, 0xcb0403e4#32,
                   0x8b010001#32, 0x8a040060#32, 0x8b010063#32, 0x8a040061#32,
                   0xcb000021#32, 0xd4000001#32] ++
      [iBl (S.mprotectWrapperAddr + 0x3c#64) L.syscallRetAddr] ++
      decodeWords [0xa8c17bfd#32, 0xd65f03c0#32]) ]

def hbMakeHandlerChunks (C : HbCliLayout) (S : HbStartupLayout) : List CodeChunk :=
  let L := C.std; let mh := C.makeStackHandlerAddr; let mhb := mh + 0xb8#64
  [ .instrs0 mh (
      decodeWords [0xd10243ff#32, 0xa9067bfd#32, 0xf9003bf5#32, 0xa9084ff4#32, 0x910183fd#32] ++
      [iAdrp .x8 (mh + 0x14#64) C.needAltstackAddr, iAddLo12 .x8 .x8 C.needAltstackAddr] ++
      decodeWords [0x08dffd08#32, 0x34000a28#32, 0x370004a0#32]),
    .instrs mh 0xb8 (
      decodeWords [0x910003e1#32, 0xaa1f03e0#32, 0xa9007fff#32, 0xf9000bff#32] ++
      [iBl (mhb + 0x10#64) S.sigaltstackAddr] ++
      decodeWords [0x394023e8#32, 0xaa1f03e0#32, 0x360803e8#32, 0x52800660#32] ++
      [ iBl (mhb + 0x24#64) L.getauxvalAddr, iAdrp .x8 (mhb + 0x28#64) L.pageSizeGlobalAddr,
        decodeWord 0xf1400c1f#32, decodeWord 0x52860009#32, iLdr64Lo12 .x19 .x8 L.pageSizeGlobalAddr ] ++
      decodeWords [0x9a898015#32, 0x52800443#32, 0xaa1f03e0#32, 0x52800062#32,
                   0x72a00043#32, 0x8b1302a1#32, 0x12800004#32, 0xaa1f03e5#32] ++
      [iBl (mhb + 0x58#64) S.mmapWrapperAddr] ++
      decodeWords [0xb100041f#32, 0x54000320#32, 0xaa1303e1#32, 0x2a1f03e2#32, 0xaa0003f4#32] ++
      [iBl (mhb + 0x70#64) S.mprotectWrapperAddr] ++
      decodeWords [0x35000560#32, 0x8b130288#32, 0x910003e0#32, 0xaa1f03e1#32,
                   0xb9000bff#32, 0xf90003e8#32, 0xf9000bf5#32] ++
      [iBl (mhb + 0x90#64) S.sigaltstackAddr] ++
      decodeWords [0xf94003e0#32, 0xa9484ff4#32, 0xf9403bf5#32, 0xa9467bfd#32,
                   0x910243ff#32, 0xd65f03c0#32]) ]

def hbLangStartChunks (C : HbCliLayout) (S : HbStartupLayout) : List CodeChunk :=
  let L := C.std; let ls := C.langStartInternalAddr; let lsm := ls + 0x1f8#64
  [ .instrs0 L.cMainAddr (
      decodeWords [0xd10083ff#32, 0x93407c02#32, 0xaa0103e3#32, 0xd503201f#32] ++
      [ iAdr .x8 (L.cMainAddr + 0x10#64) L.userMainAddr, decodeWord 0xd503201f#32,
        iAdr .x1 (L.cMainAddr + 0x18#64) C.langStartVtableAddr ] ++
      decodeWords [0x910023e0#32, 0x2a1f03e4#32, 0xa9017bfd#32, 0x910043fd#32, 0xf90007e8#32] ++
      [iBl (L.cMainAddr + 0x30#64) ls]),
    .instrs0 ls (
      decodeWords [0xd10403ff#32, 0xa90a7bfd#32, 0xa90b6ffc#32, 0xa90c67fa#32,
                   0xa90d5ff8#32, 0xa90e57f6#32, 0xa90f4ff4#32, 0x910283fd#32,
                   0x2a0403f7#32, 0xaa0303f4#32, 0xaa0203f6#32, 0xaa0103f5#32,
                   0xaa0003f3#32, 0xd2a00000#32, 0xf2800b00#32, 0xd503201f#32,
                   0xd503201f#32, 0xd53bd05b#32, 0xf8606b7c#32, 0xb500023c#32] ++
      [ iAdrp .x8 (ls + 0x50#64) L.threadIdCounterAddr, decodeWord 0xaa0003f8#32,
        iAdrp .x25 (ls + 0x58#64) L.threadIdCounterAddr,
        iAddLo12 .x25 .x25 L.threadIdCounterAddr, iLdr64Lo12 .x26 .x8 L.threadIdCounterAddr ] ++
      decodeWords [0xb100075f#32, 0x54002020#32, 0x91000741#32, 0xaa1a03e0#32,
                   0xaa1903e2#32, 0x9100075c#32] ++
      [iBl (ls + 0x7c#64) L.cas8RelaxAddr] ++
      decodeWords [0xeb1a001f#32, 0xaa0003fa#32, 0x54fffee1#32, 0xf8386b7c#32] ++
      [iAdrp .x8 (ls + 0x90#64) S.mainThreadAddr, iStr64Lo12 .x28 .x8 S.mainThreadAddr] ++
      decodeWords [0x52800028#32, 0xa90023ff#32, 0x52800048#32, 0xf9000be8#32,
                   0x910003e0#32, 0x52800061#32, 0x2a1f03e2#32] ++
      [iBl (ls + 0xb4#64) L.pollAddr] ++ decodeWords [0x3100041f#32, 0x54001a21#32]),
    .words (ls + 0x400#64) [0x910003e8#32, 0xaa1f03fa#32, 0x12800019#32, 0xb27f051c#32,
      0x8b1a0398#32, 0x9100235a#32, 0x14000002#32, 0x9100235a#32,
      0xf100835f#32, 0x54ffeea0#32, 0x78408708#32, 0x362fff88#32],
    .words lsm [0x12001ee8#32, 0x52800021#32, 0x7100051f#32, 0x5400010c#32, 0x340001e8#32],
    .instrs ls 0x244 ([decodeWord 0x528001a0#32, iBl (lsm + 0x50#64) L.signalAddr,
      decodeWord 0xb100041f#32, decodeWord 0x54001120#32, decodeWord 0x528003c0#32,
      iBl (lsm + 0x60#64) L.sysconfAddr, decodeWord 0x6f00e400#32,
      iAdrp .x8 (lsm + 0x68#64) L.pageSizeGlobalAddr, decodeWord 0x910003e2#32,
      iStr64Lo12 .x0 .x8 L.pageSizeGlobalAddr, decodeWord 0x52800160#32,
      decodeWord 0xaa1f03e1#32, iLdr64Lo12 .xzr .x8 L.pageSizeGlobalAddr] ++
      decodeWords [0xf9004bff#32, 0xad0083e0#32, 0xad0183e0#32, 0xad0283e0#32,
                   0xad0383e0#32, 0x3d8003e0#32] ++
      [iBl (lsm + 0x98#64) L.sigactionAddr] ++ decodeWords [0xf94003e8#32, 0xb4000108#32]),
    .instrs ls 0x2b8 ([iAdrp .x8 (lsm + 0xc0#64) C.needAltstackAddr,
      iLdr8Lo12 .x8 .x8 C.needAltstackAddr, decodeWord 0x35000128#32, decodeWord 0x52800028#32,
      iAdrp .x9 (lsm + 0xd0#64) C.needAltstackAddr, iAddLo12 .x9 .x9 C.needAltstackAddr,
      decodeWord 0x089ffd28#32, decodeWord 0x52800020#32,
      iBl (lsm + 0xe0#64) C.makeStackHandlerAddr,
      iAdrp .x8 (lsm + 0xe4#64) C.mainAltstackAddr, iStr64Lo12 .x0 .x8 C.mainAltstackAddr] ++
      decodeWords [0x52800088#32, 0x910003e1#32, 0x52800160#32, 0x72a10008#32,
                   0xaa1f03e2#32, 0xb9008be8#32, 0xd503201f#32] ++
      [iAdr .x8 (lsm + 0x108#64) S.signalHandlerAddr, decodeWord 0xf90003e8#32,
       iBl (lsm + 0x110#64) L.sigactionAddr] ++
      decodeWords [0x910003e2#32, 0x528000e0#32, 0xaa1f03e1#32] ++
      [ iBl (lsm + 0x120#64) L.sigactionAddr, decodeWord 0xf94003e8#32, decodeWord 0xb50002c8#32,
        iAdrp .x8 (lsm + 0x12c#64) C.needAltstackAddr, iLdr8Lo12 .x8 .x8 C.needAltstackAddr,
        decodeWord 0x35000128#32 ]),
    .instrs ls 0x350 (
      decodeWords [0x52800088#32, 0x910003e1#32, 0x528000e0#32, 0x72a10008#32,
                   0xaa1f03e2#32, 0xb9008be8#32, 0xd503201f#32] ++
      [ iAdr .x8 (lsm + 0x174#64) S.signalHandlerAddr, decodeWord 0xf90003e8#32,
        iBl (lsm + 0x17c#64) L.sigactionAddr, iAdrp .x8 (lsm + 0x180#64) L.argcGlobalAddr,
        iAddLo12 .x8 .x8 L.argcGlobalAddr ] ++
      decodeWords [0xf9000116#32, 0xf9000514#32, 0xf94016a8#32, 0xaa1303e0#32, 0xd63f0100#32]),
    .instrs0 C.langStartClosureAddr (decodeWords [0xa9bf7bfd#32, 0x910003fd#32, 0xf9400000#32] ++
      [iBl (C.langStartClosureAddr + 0x0c#64) L.beginShortBacktraceAddr]),
    .words L.beginShortBacktraceAddr beginShortBacktraceWords ]

/-- Decidable code-presence bundle for `_start` to `userMain`, outline atomics, and `MemOps` on `P`. -/
structure HbPreMainCode (P : Program) (C : HbCliLayout) (S : HbStartupLayout) : Prop where
  no_hooks    : P.NoHooks
  svc_eq      : P.svc = Syscall.standard
  ne_memset   : C.std.initLibcAddr + 0x28#64 ≠ C.std.memsetAddr
  ne_tls      : C.std.initLibcAddr + 0x108#64 ≠ C.std.staticInitTlsAddr
  ne_stage2   : C.std.libcStartMainAddr + 0x50#64 ≠ C.std.libcStartMainStage2Addr
  stage1      : CodeChunks P (hbStage1Chunks C S)
  stage2      : CodeChunks P (hbStage2Chunks C S)
  sigSys      : CodeChunks P (hbSigAndSysChunks C S)
  makeHandler : CodeChunks P (hbMakeHandlerChunks C S)
  langStart   : CodeChunks P (hbLangStartChunks C S)
  cas8Relax   : hasInstrs P C.std.cas8RelaxAddr (cas8RelaxInstrs C.std)
  cas4Acq     : hasInstrs P C.std.cas4AcqAddr (cas4AcqInstrs C.std)
  cas8Acq     : hasInstrs P C.std.cas8AcqAddr (cas8AcqInstrs C.std)
  swp4Rel     : hasInstrs P C.std.swp4RelAddr (swp4RelInstrs C.std)
  memOps      : HbMemOpsCode P C

theorem HbPreMainCode.atomics {P : Program} {C : HbCliLayout} {S : HbStartupLayout}
    (hc : HbPreMainCode P C S) :
    StdOutlineAtomics P C.std.haveLseAtomicsAddr C.std.cas8RelaxAddr
      C.std.cas4AcqAddr C.std.cas8AcqAddr C.std.swp4RelAddr :=
  stdOutlineAtomics_of_hasInstrs P C.std hc.cas8Relax hc.cas4Acq hc.cas8Acq hc.swp4Rel

theorem HbPreMainCode.atomicsNonVm {P : Program} {C : HbCliLayout} {S : HbStartupLayout}
    (hc : HbPreMainCode P C S) :
    StdOutlineAtomics (P.withSvc nonVmSvc) C.std.haveLseAtomicsAddr C.std.cas8RelaxAddr
      C.std.cas4AcqAddr C.std.cas8AcqAddr C.std.swp4RelAddr :=
  stdOutlineAtomics_of_hasInstrs (P.withSvc nonVmSvc) C.std
    (fun i hi => hc.cas8Relax i hi)
    (fun i hi => hc.cas4Acq i hi)
    (fun i hi => hc.cas8Acq i hi)
    (fun i hi => hc.swp4Rel i hi)

/-- $O(k \log N)$ boolean `WordTree` validator for `HbPreMainCode`. -/
def checkHbPreMainCode (C : HbCliLayout) (S : HbStartupLayout)
    (base : BitVec 64) (t : WordTree) : Bool :=
  let L := C.std
  (L.initLibcAddr + 0x28#64 != L.memsetAddr) &&
  (L.initLibcAddr + 0x108#64 != L.staticInitTlsAddr) &&
  (L.libcStartMainAddr + 0x50#64 != L.libcStartMainStage2Addr) &&
  (hbStage1Chunks C S).all (checkCodeChunk base t) &&
  (hbStage2Chunks C S).all (checkCodeChunk base t) &&
  (hbSigAndSysChunks C S).all (checkCodeChunk base t) &&
  (hbMakeHandlerChunks C S).all (checkCodeChunk base t) &&
  (hbLangStartChunks C S).all (checkCodeChunk base t) &&
  checkCodeChunk base t (.instrs0 L.cas8RelaxAddr (cas8RelaxInstrs L)) &&
  checkCodeChunk base t (.instrs0 L.cas4AcqAddr (cas4AcqInstrs L)) &&
  checkCodeChunk base t (.instrs0 L.cas8AcqAddr (cas8AcqInstrs L)) &&
  checkCodeChunk base t (.instrs0 L.swp4RelAddr (swp4RelInstrs L)) &&
  checkHbMemOpsCode C base t

private theorem hbCodeChunks_of_all {P : Program} {b : BitVec 64} {t : WordTree}
    (hc : ∀ {c : CodeChunk}, checkCodeChunk b t c = true → c.holds P) :
    ∀ {cs : List CodeChunk}, cs.all (checkCodeChunk b t) = true → CodeChunks P cs
  | [], _ => trivial
  | [_], h => hc (by simpa using h)
  | _ :: _ :: _, h => by
    rw [List.all_cons, Bool.and_eq_true] at h
    exact ⟨hc h.1, hbCodeChunks_of_all hc h.2⟩

theorem hbPreMainCode_of_wordTree {P : Program} {C : HbCliLayout} {S : HbStartupLayout}
    {t : WordTree} (n : Nat) (hcode : P.code = t.toBytes) (hwf : t.checkSize? = some n)
    (hsvc : P.svc = Syscall.standard := by rfl)
    (hstubs : P.stubs = [] := by rfl) (hsyms : P.symbols = [] := by rfl)
    (hext : ∀ sym, (P.externs sym).isNone = true := by intro _; rfl)
    (hovr : ∀ sym, (P.overrides sym).isNone = true := by intro _; rfl)
    (hok : checkHbPreMainCode C S P.base t = true) :
    HbPreMainCode P C S := by
  have hno_hooks : P.NoHooks := Program.NoHooks.of_eq_none
    (funext fun s => Option.isNone_iff_eq_none.mp (hext s))
    (funext fun s => Option.isNone_iff_eq_none.mp (hovr s))
  have hc : ∀ {c : CodeChunk}, checkCodeChunk P.base t c = true → c.holds P := by
    rintro (⟨a, ws⟩ | ⟨b, is⟩ | ⟨b, o, is⟩) h
    · simp only [checkCodeChunk, checkCleanupWordsAt, Bool.and_eq_true, decide_eq_true_eq] at h
      exact hasWords_of_wordTree n hcode hwf rfl h.1 hstubs hsyms h.2
    all_goals
      simp only [checkCodeChunk, checkCleanupInstrsAt, Bool.and_eq_true, decide_eq_true_eq] at h
      exact hasInstrs_of_wordTree n hcode hwf (beq_iff_eq.mp h.1.1) h.1.2 hext hovr h.2
  simp only [checkHbPreMainCode, Bool.and_eq_true, bne_iff_ne] at hok
  rcases hok with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hne1, hne2⟩, hne3⟩, hs1⟩, hs2⟩, hss⟩, hmh⟩, hls⟩, hc1⟩, hc2⟩, hc3⟩, hc4⟩, hm⟩
  exact
    { no_hooks := hno_hooks
      svc_eq := hsvc
      ne_memset := hne1
      ne_tls := hne2
      ne_stage2 := hne3
      stage1 := hbCodeChunks_of_all hc hs1
      stage2 := hbCodeChunks_of_all hc hs2
      sigSys := hbCodeChunks_of_all hc hss
      makeHandler := hbCodeChunks_of_all hc hmh
      langStart := hbCodeChunks_of_all hc hls
      cas8Relax := hc hc1
      cas4Acq := hc hc2
      cas8Acq := hc hc3
      swp4Rel := hc hc4
      memOps := hbMemOpsCode_of_wordTree n hcode hwf hext hovr hm }

/-! ## `CodeChunk` Fetch Extraction and Stage-1 `musl` Startup -/

def hbFetchAtAcc (P : Program) (base : BitVec 64) : Nat → List Instr → Prop → Prop
  | _, [], acc => acc
  | off, x :: xs, acc => P.fetch (base + BitVec.ofNat 64 off) = some x ∧ hbFetchAtAcc P base (off + 4) xs acc

private theorem hbFetchAtAcc_of_fn {P : Program} {base : BitVec 64} {acc : Prop} (hacc : acc) :
    ∀ (off : Nat) (is : List Instr),
      (∀ i (hi : i < is.length), P.fetch (base + BitVec.ofNat 64 (off + 4 * i)) = some (is[i]'hi)) →
      hbFetchAtAcc P base off is acc
  | _, [], _ => hacc
  | off, _ :: xs, h =>
    ⟨by simpa using h 0 (Nat.zero_lt_succ _),
     hbFetchAtAcc_of_fn hacc (off + 4) xs fun i hi => by
       simpa [show off + 4 + 4 * i = off + 4 * (i + 1) by omega] using h (i + 1) (Nat.succ_lt_succ hi)⟩

def hbChunkStepAcc (P : Program) (acc : Prop) : CodeChunk → Prop
  | .words a ws => P.hasCode a ws ∧ acc
  | .instrs0 b is => hbFetchAtAcc P b 0 is acc
  | .instrs b o is => hbFetchAtAcc P b o is acc

def HbCodeStepFacts (P : Program) : List CodeChunk → Prop
  | [] => True
  | c :: cs => hbChunkStepAcc P (HbCodeStepFacts P cs) c

private theorem hbChunk_toStepAcc {P : Program} {acc : Prop} (hacc : acc) :
    ∀ {c : CodeChunk}, c.holds P → hbChunkStepAcc P acc c
  | .words _ _, h => ⟨h, hacc⟩
  | .instrs0 _ _, h => hbFetchAtAcc_of_fn hacc 0 _ fun i hi => by simpa using h i hi
  | .instrs _ o _, h => hbFetchAtAcc_of_fn hacc o _ fun i hi => by
      rw [BitVec.ofNat_add, ← BitVec.add_assoc]; exact h i hi

theorem hbCodeChunks_toStepFacts {P : Program} :
    ∀ {cs : List CodeChunk}, CodeChunks P cs → HbCodeStepFacts P cs
  | [], _ => trivial
  | [_], h => hbChunk_toStepAcc trivial h
  | _ :: _ :: _, ⟨h1, h2⟩ => hbChunk_toStepAcc (hbCodeChunks_toStepFacts h2) h1

/-- Page-floor (`4096 ≤ altBase.toNat`) variant of `HbAltstackInv`, matching `sanitizeMmapAddr`'s
    unconditional `PAGE_SIZE = 4096` floor on arbitrary `inputs.init.oracle.mmap 0` hints. -/
def HbAltstackInv4k (C : HbCliLayout) (S : HbStartupLayout)
    (altOpt : Option (BitVec 64 × Nat)) : SepProp :=
  (S.threadInfoRootAddr ↦₆₄ 0#64) ∗
  ((S.threadInfoRootAddr + 8#64) ↦₆₄ 0#64) ∗
  ((S.threadInfoRootAddr + 16#64) ↦₆₄ 0#64) ∗
  (S.threadInfoLockAddr ↦₃₂ 0#32) ∗
  ((S.threadInfoLockAddr + 4#64) ↦₈ 0#8) ∗
  ((S.threadInfoLockAddr + 8#64) ↦₆₄ 0#64) ∗
  match altOpt with
  | none =>
    (C.mainAltstackAddr ↦₆₄ 0#64)
  | some (altBase, altRawSz) =>
    ⌜4096 ≤ altBase.toNat ∧
      altBase.toNat % 4096 = 0 ∧
      altRawSz % 4096 = 0 ∧
      12288 ≤ altRawSz ∧
      altRawSz ≤ 524288 ∧
      altBase.toNat + altRawSz + 4096 ≤ 2 ^ 48⌝ ∗
    (C.mainAltstackAddr ↦₆₄ (altBase + 4096#64)) ∗
    memRegionProtNone altBase 4096 ∗
    memRegion (altBase + 4096#64) altRawSz

theorem HbAltstackInv4k.toHbAltstackInv {C : HbCliLayout} {S : HbStartupLayout}
    {altOpt : Option (BitVec 64 × Nat)}
    (hmin : ∀ altBase altRawSz, altOpt = some (altBase, altRawSz) → 65536 ≤ altBase.toNat) :
    HbAltstackInv4k C S altOpt ⊢ HbAltstackInv C S altOpt := by
  unfold HbAltstackInv4k HbAltstackInv
  cases altOpt with
  | none => exact Entails.refl _
  | some p =>
    rcases p with ⟨altBase, altRawSz⟩
    have hm := hmin altBase altRawSz rfl
    dsimp only
    apply sepConj_mono_right; apply sepConj_mono_right; apply sepConj_mono_right
    apply sepConj_mono_right; apply sepConj_mono_right; apply sepConj_mono_right
    rw [← emp_sepConj (⌜_⌝ ∗ _), sepConj_comm ⌜_⌝ _]
    refine entails_pure_in_frame fun h => ?_
    rw [emp_sepConj, ← SepFrameInfer.pure_intro_eq ⟨hm, h.2⟩]
    exact Entails.refl _

end CaseStudies.Hashbrown.Proofs.StdCli

