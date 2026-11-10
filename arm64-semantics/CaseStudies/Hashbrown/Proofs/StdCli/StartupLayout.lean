/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import CaseStudies.Hashbrown.Proofs.StdCli.Layout
public import ProofLib.StdStartup.StackInit
public import ProofLib.StdStartup.Layout

/-!
# 4-Segment Startup and Teardown Layout

Defines the symbolic 4-segment `ET_EXEC` layout `(C : HbCliLayout)` and `(S : HbStartupLayout)`,
the decidable validator `HbMatchesImage`, initial-state `SupportedOn` read-only freezing
(`hbLoadState_initial`), and post-`main` frame invariants.
-/

set_option autoImplicit false

@[expose] public section

namespace CaseStudies.Hashbrown.Proofs.StdCli

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.StdStartup
open CaseStudies.Hashbrown CaseStudies.Hashbrown.Proofs

/-! ## Supplementary Startup and Teardown Layout (`HbStartupLayout`) -/

structure HbStartupLayout where
  fcntlAddr               : BitVec 64
  openAddr                : BitVec 64
  dupAddr                 : BitVec 64
  initCpuFeaturesAddr     : BitVec 64
  initCpuFeaturesCtorAddr : BitVec 64
  sigaltstackAddr         : BitVec 64
  mmapWrapperAddr         : BitVec 64
  mprotectWrapperAddr     : BitVec 64
  munmapWrapperAddr       : BitVec 64
  vmWaitAddr              : BitVec 64
  signalHandlerAddr       : BitVec 64

  gotEnvironAddr          : BitVec 64
  gotPrognameFullAddr     : BitVec 64
  gotPrognameAddr         : BitVec 64
  gotInitArrayStartAddr   : BitVec 64
  gotInitArrayEndAddr     : BitVec 64
  gotFiniArrayEndAddr     : BitVec 64
  gotFiniArrayStartAddr   : BitVec 64

  eintrValidFlagAddr      : BitVec 64
  mainThreadAddr          : BitVec 64
  threadInfoRootAddr      : BitVec 64
  threadInfoLockAddr      : BitVec 64
  handlerSetAddr          : BitVec 64
  unmaskDoneAddr          : BitVec 64
  cpuFeaturesGlobalAddr   : BitVec 64
  deriving DecidableEq, Repr

def hbTdataWords : List (BitVec 64) :=
  [0#64, 1#64, 0#64, 0#64, 8#64, 0#64]

def hbTdataBytes : List (BitVec 8) :=
  hbTdataWords.flatMap unpack64

@[simp] theorem hbTdataBytes_length : hbTdataBytes.length = 48 := rfl

def hbLangStartVtableBytes (C : HbCliLayout) : List (BitVec 8) :=
  unpack64 0#64 ++
  unpack64 8#64 ++
  unpack64 8#64 ++
  unpack64 C.langStartShimAddr ++
  unpack64 C.langStartClosureAddr ++
  unpack64 C.langStartClosureAddr

def HbLangStartVtableRo (C : HbCliLayout) : SepProp :=
  let a := C.langStartVtableAddr
  (a ↦₆₄ᵣ 0#64) ∗
  ((a + 0x08#64) ↦₆₄ᵣ 8#64) ∗
  ((a + 0x10#64) ↦₆₄ᵣ 8#64) ∗
  ((a + 0x18#64) ↦₆₄ᵣ C.langStartShimAddr) ∗
  ((a + 0x20#64) ↦₆₄ᵣ C.langStartClosureAddr) ∗
  ((a + 0x28#64) ↦₆₄ᵣ C.langStartClosureAddr)

theorem pointsToBytesRO_hbLangStartVtableBytes (C : HbCliLayout) :
    (C.langStartVtableAddr ↦ᵣ hbLangStartVtableBytes C) = HbLangStartVtableRo C := by
  unfold hbLangStartVtableBytes HbLangStartVtableRo
  simp only [List.append_assoc, pointsToBytesRO_append, unpack64_length, ← pointsTo64RO_eq_pointsToBytesRO]
  rw [show BitVec.ofNat 64 8 = 0x08#64 from rfl,
      show C.langStartVtableAddr + 0x08#64 + 0x08#64 = C.langStartVtableAddr + 0x10#64 by bv_omega,
      show C.langStartVtableAddr + 0x10#64 + 0x08#64 = C.langStartVtableAddr + 0x18#64 by bv_omega,
      show C.langStartVtableAddr + 0x18#64 + 0x08#64 = C.langStartVtableAddr + 0x20#64 by bv_omega,
      show C.langStartVtableAddr + 0x20#64 + 0x08#64 = C.langStartVtableAddr + 0x28#64 by bv_omega]

theorem pointsToBytesRO_adapterWriteVtableBytes (C : HbCliLayout) :
    (C.adapterWriteVtableAddr ↦ᵣ adapterWriteVtableBytes C) = HbAdapterWriteVtableRo C := by
  unfold adapterWriteVtableBytes HbAdapterWriteVtableRo
  simp only [List.append_assoc, pointsToBytesRO_append, unpack64_length, ← pointsTo64RO_eq_pointsToBytesRO]
  rw [show BitVec.ofNat 64 8 = 0x08#64 from rfl,
      show C.adapterWriteVtableAddr + 0x08#64 + 0x08#64 = C.adapterWriteVtableAddr + 0x10#64 by bv_omega,
      show C.adapterWriteVtableAddr + 0x10#64 + 0x08#64 = C.adapterWriteVtableAddr + 0x18#64 by bv_omega,
      show C.adapterWriteVtableAddr + 0x18#64 + 0x08#64 = C.adapterWriteVtableAddr + 0x20#64 by bv_omega,
      show C.adapterWriteVtableAddr + 0x20#64 + 0x08#64 = C.adapterWriteVtableAddr + 0x28#64 by bv_omega]

structure HbStartupLayout.Valid (C : HbCliLayout) (S : HbStartupLayout) : Prop where
  seg_order              : C.roSegIdx < C.rxSegIdx ∧ C.rxSegIdx < C.relroSegIdx ∧ C.relroSegIdx < C.rwSegIdx
  std_phdrSeg_eq         : C.std.phdrSegIdx = C.roSegIdx
  std_roSeg_eq           : C.std.roSegIdx = C.roSegIdx
  std_rxSeg_eq           : C.std.rxSegIdx = C.rxSegIdx
  std_rwSeg_eq           : C.std.rwSegIdx = C.rwSegIdx
  argv_eq                : C.std.argvGlobalAddr = C.std.argcGlobalAddr + 8#64
  cMainEntry_eq          : C.cMainEntryAddr = C.std.cMainAddr
  gotEnviron_align       : S.gotEnvironAddr.toNat % 8 = 0
  gotPrognameFull_align  : S.gotPrognameFullAddr.toNat % 8 = 0
  gotProgname_align      : S.gotPrognameAddr.toNat % 8 = 0
  gotInitArrayStart_align : S.gotInitArrayStartAddr.toNat % 8 = 0
  gotInitArrayEnd_align  : S.gotInitArrayEndAddr.toNat % 8 = 0
  gotFiniArrayEnd_align  : S.gotFiniArrayEndAddr.toNat % 8 = 0
  gotFiniArrayStart_align : S.gotFiniArrayStartAddr.toNat % 8 = 0
  eintrValidFlag_align   : S.eintrValidFlagAddr.toNat % 4 = 0
  oflHead_align          : C.std.oflHeadAddr.toNat % 8 = 0
  oflLock_align          : C.std.oflLockAddr.toNat % 4 = 0
  stdinUsed_align        : C.std.stdinUsedAddr.toNat % 8 = 0
  stdoutUsed_align       : C.std.stdoutUsedAddr.toNat % 8 = 0
  stderrUsed_align       : C.std.stderrUsedAddr.toNat % 8 = 0
  stderrFile_align       : C.std.stderrFileAddr.toNat % 8 = 0
  langStartVt_align      : C.langStartVtableAddr.toNat % 8 = 0
  langStartVt_noWrap     : C.langStartVtableAddr.toNat + 48 ≤ 2 ^ 48
  cleanupVt_align        : C.std.cleanupVtableAddr.toNat % 8 = 0
  cleanupVt_noWrap       : C.std.cleanupVtableAddr.toNat + 40 ≤ 2 ^ 48
  stdoutVt_align         : C.std.stdoutVtableAddr.toNat % 8 = 0
  stdoutVt_noWrap        : C.std.stdoutVtableAddr.toNat + 40 ≤ 2 ^ 48
  tlsImage_align         : C.std.tlsImageAddr.toNat % 8 = 0
  tlsImage_noWrap        : C.std.tlsImageAddr.toNat + 48 ≤ 2 ^ 48
  initArray_align        : C.std.initArrayAddr.toNat % 8 = 0
  initArray_noWrap       : C.std.initArrayAddr.toNat + 24 ≤ 2 ^ 48
  finiArray_align        : C.std.finiArrayAddr.toNat % 8 = 0
  finiArray_noWrap       : C.std.finiArrayAddr.toNat + 8 ≤ 2 ^ 48
  got_align              : C.std.gotAddr.toNat % 8 = 0
  got_noWrap             : C.std.gotAddr.toNat + 56 ≤ 2 ^ 48
  builtinTls_align       : C.std.builtinTlsAddr.toNat % 16 = 0
  builtinTls_lo          : 65536 ≤ C.std.builtinTlsAddr.toNat
  builtinTls_noWrap      : C.std.builtinTlsAddr.toNat + 0x150 ≤ 2 ^ 48
  mainTls_align          : C.std.mainTlsAddr.toNat % 8 = 0
  mainTls_nz             : C.std.mainTlsAddr ≠ 0#64
  mainTls_noWrap         : C.std.mainTlsAddr.toNat + 48 ≤ 2 ^ 48
  libc_align             : C.std.libcAddr.toNat % 8 = 0
  libc_noWrap            : C.std.libcAddr.toNat + 104 ≤ 2 ^ 48
  argc_align             : C.std.argcGlobalAddr.toNat % 8 = 0
  argc_noWrap            : C.std.argcGlobalAddr.toNat + 16 ≤ 2 ^ 48
  needAltstack_noWrap    : C.needAltstackAddr.toNat + 1 ≤ 2 ^ 48
  mainAltstack_align     : C.mainAltstackAddr.toNat % 8 = 0
  mainAltstack_noWrap    : C.mainAltstackAddr.toNat + 8 ≤ 2 ^ 48
  pageSizeGlobal_align   : C.std.pageSizeGlobalAddr.toNat % 8 = 0
  pageSizeGlobal_noWrap  : C.std.pageSizeGlobalAddr.toNat + 8 ≤ 2 ^ 48
  exitingTid_align       : C.std.exitingThreadIdAddr.toNat % 8 = 0
  exitingTid_noWrap      : C.std.exitingThreadIdAddr.toNat + 8 ≤ 2 ^ 48
  mainThread_align       : S.mainThreadAddr.toNat % 8 = 0
  mainThread_noWrap      : S.mainThreadAddr.toNat + 8 ≤ 2 ^ 48
  threadInfoRoot_align   : S.threadInfoRootAddr.toNat % 8 = 0
  threadInfoRoot_noWrap  : S.threadInfoRootAddr.toNat + 24 ≤ 2 ^ 48
  threadInfoLock_align   : S.threadInfoLockAddr.toNat % 8 = 0
  threadInfoLock_noWrap  : S.threadInfoLockAddr.toNat + 16 ≤ 2 ^ 48
  handlerSet_align       : S.handlerSetAddr.toNat % 8 = 0
  handlerSet_noWrap      : S.handlerSetAddr.toNat + 8 ≤ 2 ^ 48
  unmaskDone_align       : S.unmaskDoneAddr.toNat % 4 = 0
  unmaskDone_noWrap      : S.unmaskDoneAddr.toNat + 4 ≤ 2 ^ 48
  cpuFeatures_align      : S.cpuFeaturesGlobalAddr.toNat % 8 = 0
  cpuFeatures_noWrap     : S.cpuFeaturesGlobalAddr.toNat + 8 ≤ 2 ^ 48
  haveLse_noWrap         : C.std.haveLseAtomicsAddr.toNat + 1 ≤ 2 ^ 48

/-! ## Segment Slice and Atom Lists and `SepProp` Bundles -/

def hbAllCodeAddrs (C : HbCliLayout) (S : HbStartupLayout) : List (BitVec 64) :=
  C.std.codeAddrs ++
  [ C.cMainEntryAddr, C.langStartClosureAddr, C.langStartShimAddr, C.langStartInternalAddr,
    C.makeStackHandlerAddr, C.dropStackHandlerAddr,
    S.fcntlAddr, S.openAddr, S.dupAddr, S.initCpuFeaturesAddr, S.initCpuFeaturesCtorAddr,
    S.sigaltstackAddr, S.mmapWrapperAddr, S.mprotectWrapperAddr, S.munmapWrapperAddr,
    S.vmWaitAddr, S.signalHandlerAddr ]

def hbRoSegSlices (C : HbCliLayout) : List (BitVec 64 × List (BitVec 8)) :=
  [ (C.std.phdrAddr, C.std.phdrBytes),
    (C.langStartVtableAddr, hbLangStartVtableBytes C),
    (C.std.emptyCStrAddr, [0#8]),
    (C.std.sysconfValuesAddr + 60#64, [0x04#8, 0xff#8]),
    (C.std.devNullStdAddr, devNullBytes),
    (C.std.devNullLibcAddr, devNullBytes),
    (C.falseNlAddr, falseNlBytes),
    (C.trueNlAddr, trueNlBytes),
    (C.pfxInsertAddr, pfxInsertBytes),
    (C.pfxRemoveAddr, pfxRemoveBytes),
    (C.pfxGetAddr, pfxGetBytes),
    (C.pfxContainsAddr, pfxContainsBytes),
    (C.pfxWithCapAddr, pfxWithCapBytes),
    (C.cmdLenAddr, cmdLenBytes),
    (C.cmdIsEmptyAddr, cmdIsEmptyBytes),
    (C.cmdClearAddr, cmdClearBytes),
    (C.errInvalidCmdAddr, errInvalidCmdBytes),
    (C.noneNlAddr, noneNlBytes),
    (C.nlByteAddr, nlByteBytes),
    (C.errLineTooLongAddr, errLineTooLongBytes),
    (C.decDigitsLutAddr, decDigitsLutBytes),
    (C.mallocng.roTablesAddr, mallocngRoTablesBytes),
    (C.hbPl.ρ hbEmptyCtrlSym, List.replicate 8 0xff#8),
    (C.hbPl.ρ hbEmptyMapSym, Obj.bytesLE 8 (C.hbPl.ρ hbEmptyCtrlSym) ++ List.replicate 24 0#8) ]

def hbRelroRoSlices (C : HbCliLayout) : List (BitVec 64 × List (BitVec 8)) :=
  [ (C.std.tlsImageAddr, hbTdataBytes),
    (C.std.cleanupVtableAddr, vtableBytes C.std.cleanupVtableShimAddr C.std.cleanupClosureAddr),
    (C.std.stdoutVtableAddr, vtableBytes C.std.stdoutVtableShimAddr C.std.stdoutCleanupClosureAddr),
    (C.stdoutInitVtableAddr, vtableBytes C.stdoutInitShimAddr C.stdoutInitClosureAddr),
    (C.stdinInitVtableAddr, vtableBytes C.stdinInitShimAddr C.stdinInitClosureAddr),
    (C.adapterWriteVtableAddr, adapterWriteVtableBytes C),
    (C.osFunctionsGotAddr, unpack64 C.osFunctionsAddr) ]

def hbRelroRwAtoms (C : HbCliLayout) (S : HbStartupLayout) : List RwAtom :=
  [ .u64 C.std.finiArrayAddr C.std.doFiniAddr,
    .u64 C.std.initArrayAddr C.std.initLseAddr,
    .u64 (C.std.initArrayAddr + 0x08#64) C.std.doInitAddr,
    .u64 (C.std.initArrayAddr + 0x10#64) S.initCpuFeaturesAddr,
    .u64 C.std.gotAddr 0#64,
    .u64 (C.std.gotAddr + 0x08#64) C.std.finiFnAddr,
    .u64 (C.std.gotAddr + 0x10#64) C.std.initFnAddr,
    .u64 (C.std.gotAddr + 0x18#64) C.std.cMainAddr,
    .u64 (C.std.gotAddr + 0x20#64) 0#64,
    .u64 (C.std.gotAddr + 0x28#64) 0#64,
    .u64 (C.std.gotAddr + 0x30#64) 0#64,
    .u64 S.gotEnvironAddr C.std.environAddr,
    .u64 S.gotPrognameFullAddr C.std.prognameFullAddr,
    .u64 S.gotPrognameAddr C.std.prognameAddr,
    .u64 S.gotInitArrayStartAddr C.std.initArrayAddr,
    .u64 S.gotInitArrayEndAddr (C.std.initArrayAddr + 0x18#64),
    .u64 S.gotFiniArrayEndAddr (C.std.finiArrayAddr + 0x08#64),
    .u64 S.gotFiniArrayStartAddr C.std.finiArrayAddr ]

def hbRwRoSlices (C : HbCliLayout) : List (BitVec 64 × List (BitVec 8)) :=
  [ (C.captureUsedAddr, [0#8]),
    (C.globalPanicCountAddr, unpack64 0#64) ]

def hbMallocngBssAtoms (C : HbCliLayout) : List RwAtom :=
  [ .u32 C.mallocng.mallocLockAddr 0#32,
    .u32 C.mallocng.alignedAllocReplacedAddr 0#32,
    .u32 C.mallocng.mallocReplacedAddr 0#32,
    .bytes C.mallocng.mallocCtxAddr (List.replicate 928 0#8) ]

def hbExtraRwAtoms (C : HbCliLayout) (S : HbStartupLayout) : List RwAtom :=
  [ .bytes C.stdinGlobalAddr (List.replicate 48 0#8),
    .u32 (C.stdinGlobalAddr + 0x30#64) 3#32,
    .u32 (C.stdinGlobalAddr + 0x34#64) 0#32,
    .bytes C.stderrGlobalAddr (List.replicate 24 0#8),
    .u32 C.std.threadListLockAddr 0#32,
    .u64 C.std.sysinfoAddr 0#64,
    .u64 C.std.hwcapAddr 0#64,
    .u32 S.eintrValidFlagAddr 0#32,
    .u8 C.std.finalizedAddr 0#8,
    .u8 C.std.initializedAddr 0#8,
    .u8 C.needAltstackAddr 0#8,
    .u64 S.mainThreadAddr 0#64,
    .u64 C.std.argcGlobalAddr 0#64,
    .u64 C.std.argvGlobalAddr 0#64,
    .u64 S.threadInfoRootAddr 0#64,
    .u64 (S.threadInfoRootAddr + 8#64) 0#64,
    .u64 (S.threadInfoRootAddr + 16#64) 0#64,
    .u32 S.threadInfoLockAddr 0#32,
    .u8 (S.threadInfoLockAddr + 4#64) 0#8,
    .u64 (S.threadInfoLockAddr + 8#64) 0#64,
    .u64 C.mainAltstackAddr 0#64,
    .u64 C.std.pageSizeGlobalAddr 0#64,
    .u64 C.std.threadIdCounterAddr 0#64,
    .u64 C.std.exitingThreadIdAddr 0#64,
    .u64 C.std.environAddr 0#64,
    .u64 C.std.prognameAddr 0#64,
    .u64 C.std.prognameFullAddr 0#64,
    .u64 S.handlerSetAddr 0#64,
    .u32 S.unmaskDoneAddr 0#32,
    .u64 C.std.stdoutUsedAddr 0#64,
    .u64 C.std.stdinUsedAddr 0#64,
    .u64 C.std.oflHeadAddr 0#64,
    .u32 C.std.oflLockAddr 0#32,
    .u64 S.cpuFeaturesGlobalAddr 0#64,
    .u8 C.std.haveLseAtomicsAddr 0#8 ]

def hbRwNonStderrAtoms (C : HbCliLayout) (S : HbStartupLayout) : List RwAtom :=
  C.std.dataNoStderrAtoms ++ C.std.libcAtoms ++ C.std.tlsAtoms ++
    hbMallocngBssAtoms C ++ hbExtraRwAtoms C S

def hbAllRwSegAtoms (C : HbCliLayout) (S : HbStartupLayout) : List RwAtom :=
  C.std.dataNoStderrAtoms ++ C.std.stderrFileAtoms ++ C.std.libcAtoms ++ C.std.tlsAtoms ++
    hbMallocngBssAtoms C ++ hbExtraRwAtoms C S

def HbRelroRwGlobals (C : HbCliLayout) (S : HbStartupLayout) : SepProp :=
  rwAtomListSep (hbRelroRwAtoms C S)

def HbExtraRwGlobals (C : HbCliLayout) (S : HbStartupLayout) : SepProp :=
  rwAtomListSep (hbExtraRwAtoms C S)

def HbStartupRoAll (C : HbCliLayout) : SepProp :=
  StdRoConstants C.std ∗
  HbLangStartVtableRo C ∗
  (C.std.tlsImageAddr ↦ᵣ hbTdataBytes) ∗
  HbCliRoData C ∗
  (C.mallocng.roTablesAddr ↦ᵣ mallocngRoTablesBytes) ∗
  hbRodata C.hbPl

theorem hbMallocngBssAtoms_sep_eq {C : HbCliLayout} :
    rwAtomListSep (hbMallocngBssAtoms C) = MallocngInitialBss C.mallocng := by
  unfold hbMallocngBssAtoms MallocngInitialBss
  simp only [rwAtomListSep, RwAtom.toSepProp]

theorem hbAllRwSegAtoms_sep_eq {C : HbCliLayout} {S : HbStartupLayout} :
    rwAtomListSep (hbAllRwSegAtoms C S) =
      StdDataGlobals C.std ∗ StdLibcGlobals C.std ∗ StdTlsGlobals C.std ∗
        MallocngInitialBss C.mallocng ∗ HbExtraRwGlobals C S := by
  unfold hbAllRwSegAtoms StdDataGlobals StdStderrFile StdLibcGlobals StdTlsGlobals HbExtraRwGlobals
  simp only [rwAtomListSep_append, hbMallocngBssAtoms_sep_eq, sepConj_assoc]

/-! ## Decidable 4-Segment `ElfImage` Validator (`HbMatchesImage`) -/

def checkHbPhdrTable (C : HbCliLayout) : Bool :=
  let L := C.std
  0 < L.phnum && L.phdrAddr.toNat % 8 == 0 && L.phdrBytes.length == L.phnum * 56 &&
  L.tlsPhdrIdx < L.phnum && L.tlsImageAddr.toNat % 8 == 0 &&
  listReadU32LE L.phdrBytes 0 == 6 && listReadU64LE L.phdrBytes 16 == L.phdrAddr.toNat &&
  (List.range L.phnum).all fun i =>
    let off := i * 56; let ptype := listReadU32LE L.phdrBytes off
    let pvaddr := listReadU64LE L.phdrBytes (off + 16); let pfilesz := listReadU64LE L.phdrBytes (off + 32)
    let pmemsz := listReadU64LE L.phdrBytes (off + 40); let palign := listReadU64LE L.phdrBytes (off + 48)
    ptype != 2 && (if ptype == 6 then pvaddr == L.phdrAddr.toNat else true) &&
    (if ptype == 0x6474e551 then pmemsz == 0 else true) &&
    (if i == L.tlsPhdrIdx then
      ptype == 7 && pvaddr == L.tlsImageAddr.toNat && pfilesz == 0x30 && pmemsz == 0x50 && palign == 8
     else ptype != 7)

def checkHbRoSegment (C : HbCliLayout) (roSeg : Snapshot.Region) (roLen : Nat) : Bool :=
  roSeg.perm == Perm.ro && C.std.sysconfValuesAddr.toNat % 2 == 0 &&
  (hbRoSegSlices C).all (fun (a, bs) => checkSegSlice roSeg roLen a bs)

def checkHbRelroSegment (C : HbCliLayout) (S : HbStartupLayout)
    (relroSeg : Snapshot.Region) (relroLen : Nat) : Bool :=
  let roIvs := (hbRelroRoSlices C).map fun (a, bs) => (a.toNat, bs.length)
  let rwIvs := (hbRelroRwAtoms C S).map fun x => (x.addr.toNat, x.rawBytes.length)
  relroSeg.perm == Perm.rw &&
  (hbRelroRoSlices C).all (fun (a, bs) => checkSegSlice relroSeg relroLen a bs) &&
  (hbRelroRwAtoms C S).all (fun x =>
    x.addr.toNat % x.align == 0 && checkSegSlice relroSeg relroLen x.addr x.rawBytes) &&
  intervalsPairwiseDisjoint (roIvs ++ rwIvs)

def checkHbRwSegment (C : HbCliLayout) (S : HbStartupLayout)
    (rwSeg : Snapshot.Region) (rwLen : Nat) : Bool :=
  let roIvs := (hbRwRoSlices C).map fun (a, bs) => (a.toNat, bs.length)
  let rwIvs := (hbAllRwSegAtoms C S).map fun x => (x.addr.toNat, x.rawBytes.length)
  let nonStderrIvs := roIvs ++ ((hbRwNonStderrAtoms C S).map fun x => (x.addr.toNat, x.rawBytes.length))
  rwSeg.perm == Perm.rw &&
  rwSeg.start.toNat ≤ C.std.stderrFileAddr.toNat &&
  C.std.stderrFileAddr.toNat + 0xe8 ≤ rwSeg.start.toNat + rwLen &&
  (hbRwRoSlices C).all (fun (a, bs) => checkSegSlice rwSeg rwLen a bs) &&
  (hbAllRwSegAtoms C S).all (fun x =>
    x.addr.toNat % x.align == 0 && checkSegSlice rwSeg rwLen x.addr x.rawBytes) &&
  nonStderrIvs.all (intervalDisjoint (C.std.stderrFileAddr.toNat, 0xe8)) &&
  intervalsPairwiseDisjoint (roIvs ++ rwIvs)

def HbMatchesImage (C : HbCliLayout) (S : HbStartupLayout) (img : ElfImage) : Bool :=
  fastWellFormed img &&
  img.entry == C.std.startAddr &&
  img.phdrVaddr == C.std.phdrAddr &&
  img.phnum == C.std.phnum &&
  img.brkStart == C.std.brkStart &&
  decide (65536 ≤ C.std.brkStart.toNat ∧ C.std.brkStart.toNat ≤ 5 * 2 ^ 20) &&
  checkHbPhdrTable C &&
  match img.segments[C.roSegIdx]?, img.segments[C.rxSegIdx]?,
        img.segments[C.relroSegIdx]?, img.segments[C.rwSegIdx]? with
  | some roSeg, some rxSeg, some relroSeg, some rwSeg =>
    withForcedNat (fastLen512 4096 roSeg.bytes) fun roLen =>
    withForcedNat (fastLen512 4096 rxSeg.bytes) fun rxLen =>
    withForcedNat (fastLen512 4096 relroSeg.bytes) fun relroLen =>
    withForcedNat (fastLen512 4096 rwSeg.bytes) fun rwLen =>
      rxSeg.perm == Perm.rx &&
      (hbAllCodeAddrs C S).all (fun a => a.toNat % 4 == 0 &&
        rxSeg.start.toNat ≤ a.toNat && a.toNat + 4 ≤ rxSeg.start.toNat + rxLen) &&
      checkHbRoSegment C roSeg roLen &&
      checkHbRelroSegment C S relroSeg relroLen &&
      checkHbRwSegment C S rwSeg rwLen
  | _, _, _, _ => false

/-! ## Initial-Load Extraction and `SupportedOn` Freezing (`hbLoadState_initial`) -/

abbrev HbInitialStackScratchBytes : Nat := 524288

def HbInitialStackSep (img : ElfImage) (inputs : ProcessInputs) : SepProp :=
  let L := StackLayout.of img inputs
  memRegion (L.sp0 - BitVec.ofNat 64 HbInitialStackScratchBytes) HbInitialStackScratchBytes ∗
  (L.sp0 ↦₆₄ᵣ BitVec.ofNat 64 inputs.argv.length) ∗
  (L.argvTableAddr ↦₆₄ᵣ* (L.argvAddrs ++ [0#64])) ∗
  (L.envpTableAddr ↦₆₄ᵣ* (L.envpAddrs ++ [0#64])) ∗
  (L.auxvTableAddr ↦ₛ encodeAuxvBytes L.auxvEntries) ∗
  (L.randomAddr ↦ₛ inputs.init.auxv.randomBytes) ∗
  (L.platformAddr ↦ᵣ platformCStringBytes) ∗
  (L.argvBase ↦ᵣ L.upperStrBytes)

private theorem hbSupportedOn_emp (m : Memory) :
    SupportedOn 0#64 (fun _ => False) m (|==> emp) := by
  have hs := SupportedOn.of_holdsBytes_ro0 (addr := 0#64) (bs := []) (m := m) (by decide)
    (fun _ hi => nomatch hi)
  rw [pointsToBytesRO_nil] at hs
  exact hs.widen (fun _ ⟨_, hk⟩ => by simp at hk)

private theorem supportedOn_roSlices_rwSeg {m : Memory} (slices : List (BitVec 64 × List (BitVec 8)))
    (hhb : ∀ p ∈ slices, p.1.toNat + p.2.length < 2 ^ 64 ∧ Obj.HoldsBytes m p.1 p.2 (fun _ => Perm.rw))
    (hdisj : intervalsPairwiseDisjoint (slices.map fun p => (p.1.toNat, p.2.length)) = true) :
    SupportedOn 0#64 (fun k => ∃ p ∈ slices, p.1.toNat ≤ k ∧ k < p.1.toNat + p.2.length)
      m (|==> roSliceListSep slices) := by
  induction slices with
  | nil =>
    rw [roSliceListSep]
    exact (hbSupportedOn_emp m).widen (fun _ h => nomatch h)
  | cons p ps ih =>
    rcases p with ⟨a, bs⟩
    simp only [List.map_cons, intervalsPairwiseDisjoint, Bool.and_eq_true] at hdisj
    have ⟨hbnd, hb⟩ := hhb (a, bs) (List.mem_cons_self ..)
    have hs_hd := SupportedOn.of_holdsBytes_ro0 hbnd hb
    have hs_tl := ih (fun q hq => hhb q (List.mem_cons_of_mem _ hq)) hdisj.2
    have hsep := ProofLib.SupportedOn.sepConj hs_hd hs_tl (by
      rintro k ⟨hk1, hk2⟩ ⟨q, hq, hq1, hq2⟩
      have hd := List.all_eq_true.mp hdisj.1 _
        (List.mem_map_of_mem (f := fun p : BitVec 64 × List (BitVec 8) => (p.1.toNat, p.2.length)) hq)
      unfold intervalDisjoint at hd
      dsimp only at hk1 hk2 hd
      simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hd
      omega)
    have hupd := ProofLib.SupportedOn.mono (bupd_sep (Entails.refl _) (Entails.refl _)) hsep
    rw [← roSliceListSep_cons] at hupd
    exact hupd.widen (by
      rintro k (hk | ⟨q, hq, hk⟩)
      · exact ⟨(a, bs), List.mem_cons_self .., hk⟩
      · exact ⟨q, List.mem_cons_of_mem _ hq, hk⟩)

private theorem intervalsPairwiseDisjoint_split {xs ys : List (Nat × Nat)}
    (h : intervalsPairwiseDisjoint (xs ++ ys) = true) :
    intervalsPairwiseDisjoint xs = true ∧
    intervalsPairwiseDisjoint ys = true ∧
    (∀ u ∈ xs, ∀ v ∈ ys, intervalDisjoint u v = true) := by
  induction xs with
  | nil => exact ⟨rfl, h, fun _ hu => nomatch hu⟩
  | cons x xr ih =>
    simp only [List.cons_append, intervalsPairwiseDisjoint, List.all_append, Bool.and_eq_true] at h
    obtain ⟨⟨hx_xr, hx_ys⟩, hrest⟩ := h
    obtain ⟨hxr, hys, hcross⟩ := ih hrest
    refine ⟨?_, hys, ?_⟩
    · simp only [intervalsPairwiseDisjoint, Bool.and_eq_true]; exact ⟨hx_xr, hxr⟩
    · intro u hu v hv
      rcases List.mem_cons.mp hu with rfl | hu'
      · exact List.all_eq_true.mp hx_ys v hv
      · exact hcross u hu' v hv

theorem HbMatchesImage.unpack {C : HbCliLayout} {S : HbStartupLayout} {img : ElfImage}
    (h : HbMatchesImage C S img = true) :
    img.WellFormed = true ∧
    img.entry = C.std.startAddr ∧
    img.phdrVaddr = C.std.phdrAddr ∧
    img.phnum = C.std.phnum ∧
    img.brkStart = C.std.brkStart ∧
    (65536 ≤ C.std.brkStart.toNat ∧ C.std.brkStart.toNat ≤ 5 * 2 ^ 20) ∧
    checkHbPhdrTable C = true ∧
    ∃ roSeg rxSeg relroSeg rwSeg,
      img.segments[C.roSegIdx]? = some roSeg ∧
      img.segments[C.rxSegIdx]? = some rxSeg ∧
      img.segments[C.relroSegIdx]? = some relroSeg ∧
      img.segments[C.rwSegIdx]? = some rwSeg ∧
      rxSeg.perm = Perm.rx ∧
      ((hbAllCodeAddrs C S).all fun a => a.toNat % 4 == 0 &&
        rxSeg.start.toNat ≤ a.toNat && a.toNat + 4 ≤ rxSeg.start.toNat + rxSeg.bytes.length) = true ∧
      checkHbRoSegment C roSeg roSeg.bytes.length = true ∧
      checkHbRelroSegment C S relroSeg relroSeg.bytes.length = true ∧
      checkHbRwSegment C S rwSeg rwSeg.bytes.length = true := by
  unfold HbMatchesImage at h; rw [fastWellFormed_eq] at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hwf, hent⟩, hphv⟩, hphn⟩, hbrk⟩, hbrkle⟩, hphdr⟩, hm⟩ := h
  refine ⟨hwf, hent, hphv, hphn, hbrk, hbrkle, hphdr, ?_⟩
  split at hm <;> try contradiction
  rename_i roSeg rxSeg relroSeg rwSeg h0 h1 h2 h3
  simp only [withForcedNat_eq, fastLen512_eq_length, Bool.and_eq_true, beq_iff_eq] at hm
  obtain ⟨⟨⟨⟨hrxP, hcode⟩, hroC⟩, hrelC⟩, hrwC⟩ := hm
  exact ⟨roSeg, rxSeg, relroSeg, rwSeg, h0, h1, h2, h3, hrxP, hcode, hroC, hrelC, hrwC⟩

private theorem hb_regionAlignedValid_bounds {r : Snapshot.Region} (hv : regionAlignedValid r = true) :
    Obj.pageSize ≤ r.start.toNat ∧ r.start.toNat % Obj.pageSize = 0 ∧
      0 < r.bytes.length ∧ r.start.toNat + r.bytes.length ≤ 2 ^ 48 := by
  unfold regionAlignedValid at hv; simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hv
  exact ⟨hv.1.1.1.1.1.1, hv.1.1.1.1.1.2, hv.1.1.1.1.2, hv.1.1.2⟩

private theorem hb_regionAlignedValid_of_disjoint {regions : List Snapshot.Region}
    (hd : regionsDisjointAndAligned regions = true) {r : Snapshot.Region} (hr : r ∈ regions) :
    regionAlignedValid r = true := by
  match regions with
  | [] => nomatch hr | [_] => rw [List.mem_singleton.mp hr]; exact hd
  | r1 :: r2 :: rest =>
    simp only [regionsDisjointAndAligned, Bool.and_eq_true] at hd
    rcases List.mem_cons.mp hr with rfl | hr'; · exact hd.1.1
    exact hb_regionAlignedValid_of_disjoint hd.2 hr'

private theorem hb_start_lt_tail_of_disjoint {r1 : Snapshot.Region} {tail : List Snapshot.Region}
    (hd : regionsDisjointAndAligned (r1 :: tail) = true) {q : Snapshot.Region} (hq : q ∈ tail) :
    r1.start.toNat + r1.bytes.length ≤ q.start.toNat := by
  match tail with
  | [] => nomatch hq
  | r2 :: rest =>
    simp only [regionsDisjointAndAligned, Bool.and_eq_true, decide_eq_true_eq] at hd
    rcases List.mem_cons.mp hq with rfl | hq'; · exact hd.1.2
    have ⟨_, _, hpos, _⟩ := hb_regionAlignedValid_bounds
      (hb_regionAlignedValid_of_disjoint hd.2 (List.mem_cons.mpr (Or.inl rfl)))
    have ih := hb_start_lt_tail_of_disjoint hd.2 hq'; omega

private theorem seg_disjoint_of_lt {regions : List Snapshot.Region}
    (hd : regionsDisjointAndAligned regions = true) {i j : Nat}
    (hij : i < j) (hj : j < regions.length) :
    regions[i].start.toNat + regions[i].bytes.length ≤ regions[j].start.toNat := by
  induction i generalizing regions j with
  | zero =>
    match regions, j with
    | [] , _ => nomatch hj
    | [_], 0 => nomatch hij
    | [_], _ + 1 => simp at hj
    | r1 :: r2 :: rest, j' + 1 =>
      have hj' : j' < (r2 :: rest).length := Nat.lt_of_succ_lt_succ hj
      exact hb_start_lt_tail_of_disjoint hd (List.getElem_mem hj')
  | succ i' ih =>
    match regions, j with
    | [], _ => nomatch hj
    | [_], 0 => nomatch hij
    | [_], _ + 1 => simp at hj
    | _ :: r2 :: rest, j' + 1 =>
      simp only [regionsDisjointAndAligned, Bool.and_eq_true] at hd
      exact ih hd.2 (Nat.lt_of_succ_lt_succ hij) (Nat.lt_of_succ_lt_succ hj)

theorem HbMatchesImage.codeLoaded {C : HbCliLayout} {S : HbStartupLayout} {img : ElfImage}
    {inputs : ProcessInputs} {s0 : State}
    (hS : S.Valid C) (h : HbMatchesImage C S img = true) (hload : img.loadState inputs = .ok s0) :
    (C.std.rxProgram img).CodeLoaded s0.mem := by
  obtain ⟨hwf, _, _, _, _, _, _, _, rxSeg, _, _, _, hrx, _, _, hperm, _⟩ := HbMatchesImage.unpack h
  unfold StdBinaryLayout.rxProgram
  rw [hS.std_rxSeg_eq, hrx]; dsimp only []
  obtain ⟨hidx, rfl⟩ := List.getElem?_eq_some_iff.mp hrx
  have hd : regionsDisjointAndAligned img.segments = true := by
    unfold ElfImage.WellFormed at hwf; simp only [Bool.and_eq_true] at hwf; exact hwf.1.1.1.2
  have ⟨_, _, _, _, hseg_all⟩ := wellFormed_segments_bounds hwf
  have ⟨hlo, _, hhi_brk⟩ := hseg_all img.segments[C.rxSegIdx] (List.getElem_mem hidx)
  have hbrk_le : img.brkStart.toNat ≤ 2 ^ 48 := by
    rw [(HbMatchesImage.unpack h).2.2.2.2.1]; have := (HbMatchesImage.unpack h).2.2.2.2.2.1.2; omega
  have htake : (img.segments.take C.rxSegIdx).all (Snapshot.Below img.segments[C.rxSegIdx].start) = true := by
    rw [List.all_eq_true]
    intro q hq
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hq
    rw [List.length_take] at hk
    have hk_lt : k < C.rxSegIdx := Nat.lt_of_lt_of_le hk (Nat.min_le_left _ _)
    rw [List.getElem_take]
    simp only [Snapshot.Below, decide_eq_true_eq]
    exact seg_disjoint_of_lt hd hk_lt hidx
  have hal4 : img.segments[C.rxSegIdx].start.toNat % 4 = 0 := by
    have ⟨_, halp, _, _⟩ := hb_regionAlignedValid_bounds
      (hb_regionAlignedValid_of_disjoint hd (List.getElem_mem hidx))
    unfold Obj.pageSize at halp; omega
  have hhb := ElfImage.holdsBytes_of_segment_slice img hload C.rxSegIdx hidx htake
    (by omega) 0 img.segments[C.rxSegIdx].bytes (by rw [List.drop_zero, List.take_length])
  rw [BitVec.add_zero, hperm] at hhb
  exact Program.CodeLoaded.intro hal4 (by dsimp only []; omega) hhb

private theorem combine_roAll (C : HbCliLayout) :
    roSliceListSep (hbRoSegSlices C) ∗ roSliceListSep (hbRelroRoSlices C) ∗ roSliceListSep (hbRwRoSlices C) =
      HbStartupRoAll C := by
  unfold hbRoSegSlices hbRelroRoSlices hbRwRoSlices HbStartupRoAll StdRoConstants HbCliRoData hbRodata
  simp only [roSliceListSep, pointsToBytesRO_hbLangStartVtableBytes, pointsToBytesRO_vtableBytes,
    pointsToBytesRO_adapterWriteVtableBytes, pointsToBytesRO_singleton, pointsToBytesRO2_eq_pointsTo16RO,
    ← pointsTo64RO_eq_pointsToBytesRO]
  have h16 : ((0xff#8 ++ 0x04#8) : BitVec 16) = 0xff04#16 := rfl
  rw [h16]
  ac_rfl

theorem hbLoadState_initial {C : HbCliLayout} {S : HbStartupLayout} {img : ElfImage}
    {inputs : ProcessInputs} {s0 : State}
    (hS : S.Valid C) (hm : HbMatchesImage C S img = true)
    (hvalid : inputs.Valid) (hload : img.loadState inputs = .ok s0) :
    InitialStackInfo img inputs s0 ∧
    (C.std.rxProgram img).CodeLoaded s0.mem ∧
    (s0.mem ⊨
      HbStartupRoAll C ∗
      HbRelroRwGlobals C S ∗
      StdDataGlobals C.std ∗
      StdLibcGlobals C.std ∗
      StdTlsGlobals C.std ∗
      MallocngInitialBss C.mallocng ∗
      HbExtraRwGlobals C S ∗
      HbInitialStackSep img inputs) := by
  obtain ⟨hwf, _, _, _, hbrk_eq, ⟨hbrk_lo, hbrk_hi⟩, _,
    roSeg, rxSeg, relroSeg, rwSeg, hro, _, hrel, hrw, _, _, hroC, hrelC, hrwC⟩ :=
    HbMatchesImage.unpack hm
  have hstk_floor : STACK_BASE_MIN ≤ inputs.init.stackTop.toNat - inputs.init.stackSize :=
    hvalid.2.1.2.base_floor
  have hbrk_le_stk : img.brkStart.toNat ≤ inputs.init.stackTop.toNat - inputs.init.stackSize := by
    rw [hbrk_eq]; unfold STACK_BASE_MIN at hstk_floor; omega
  have hinfo := loadState_initialStackInfo hwf hvalid hbrk_le_stk hload
  have hcode := HbMatchesImage.codeLoaded hS hm hload
  refine ⟨hinfo, hcode, ?_⟩
  have ⟨_, _, _, _, hseg_all⟩ := wellFormed_segments_bounds hwf
  have hd : regionsDisjointAndAligned img.segments = true := by
    unfold ElfImage.WellFormed at hwf; simp only [Bool.and_eq_true] at hwf; exact hwf.1.1.1.2
  obtain ⟨hrel_idx, rfl⟩ := List.getElem?_eq_some_iff.mp hrel
  obtain ⟨hrw_idx, rfl⟩ := List.getElem?_eq_some_iff.mp hrw
  have hrel_rw_disj : img.segments[C.relroSegIdx].start.toNat + img.segments[C.relroSegIdx].bytes.length ≤
      img.segments[C.rwSegIdx].start.toNat :=
    seg_disjoint_of_lt hd hS.seg_order.2.2 hrw_idx
  have ⟨_, _, hrw_end_brk⟩ := hseg_all img.segments[C.rwSegIdx] (List.getElem_mem hrw_idx)
  have ⟨hrel_lo, _, _⟩ := hseg_all img.segments[C.relroSegIdx] (List.getElem_mem hrel_idx)
  unfold checkHbRelroSegment at hrelC
  simp only [Bool.and_eq_true, beq_iff_eq] at hrelC
  obtain ⟨⟨⟨hrel_perm, hrel_roS⟩, hrel_rwA⟩, hrel_disj⟩ := hrelC
  obtain ⟨hrel_roD, hrel_rwD, hrel_cross⟩ := intervalsPairwiseDisjoint_split hrel_disj
  have hs_rel_ro := supportedOn_roSlices_rwSeg (m := s0.mem) (hbRelroRoSlices C) (fun p hp => by
    have hpC := List.all_eq_true.mp hrel_roS p hp
    have ⟨hhb, _, hhi⟩ := holdsBytes_of_checkSegSlice hwf hload hrel hpC
    rw [hrel_perm] at hhb; exact ⟨by omega, hhb⟩) hrel_roD
  have hs_rel_rw := SupportedOn.bupd_intro (supportedOn_rwAtomList (m := s0.mem) (hbRelroRwAtoms C S)
    (fun x hx => by
      have hxC := List.all_eq_true.mp hrel_rwA x hx; simp only [Bool.and_eq_true] at hxC
      have ⟨hhb, _, hhi⟩ := holdsBytes_of_checkSegSlice hwf hload hrel hxC.2
      rw [hrel_perm] at hhb; exact ⟨by omega, hhb⟩) hrel_rwD)
  have hs_rel : SupportedOn 0#64
      (fun k => img.segments[C.relroSegIdx].start.toNat ≤ k ∧
        k < img.segments[C.relroSegIdx].start.toNat + img.segments[C.relroSegIdx].bytes.length)
      s0.mem (|==> (roSliceListSep (hbRelroRoSlices C) ∗ HbRelroRwGlobals C S)) := by
    have hsep := ProofLib.SupportedOn.sepConj hs_rel_ro hs_rel_rw (by
      rintro k ⟨p, hp, hp1, hp2⟩ ⟨x, hx, hx1, hx2⟩
      have hc := hrel_cross (p.1.toNat, p.2.length) (List.mem_map_of_mem hp)
        (x.addr.toNat, x.rawBytes.length) (List.mem_map_of_mem hx)
      unfold intervalDisjoint at hc; simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hc; omega)
    refine (ProofLib.SupportedOn.mono (bupd_sep (Entails.refl _) (Entails.refl _)) hsep).widen ?_
    rintro k (⟨p, hp, hk1, hk2⟩ | ⟨x, hx, hk1, hk2⟩)
    · have hpC := List.all_eq_true.mp hrel_roS p hp
      unfold checkSegSlice at hpC; simp only [Bool.and_eq_true, decide_eq_true_eq] at hpC; omega
    · have hxC := List.all_eq_true.mp hrel_rwA x hx; simp only [Bool.and_eq_true] at hxC
      have hb := hxC.2; unfold checkSegSlice at hb; simp only [Bool.and_eq_true, decide_eq_true_eq] at hb; omega
  unfold checkHbRwSegment at hrwC
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hrwC
  obtain ⟨⟨⟨⟨⟨⟨hrw_perm, _⟩, _⟩, hrw_roS⟩, hrw_rwA⟩, _⟩, hrw_disj⟩ := hrwC
  obtain ⟨hrw_roD, hrw_rwD, hrw_cross⟩ := intervalsPairwiseDisjoint_split hrw_disj
  have hs_rw_ro := supportedOn_roSlices_rwSeg (m := s0.mem) (hbRwRoSlices C) (fun p hp => by
    have hpC := List.all_eq_true.mp hrw_roS p hp
    have ⟨hhb, _, hhi⟩ := holdsBytes_of_checkSegSlice hwf hload hrw hpC
    rw [hrw_perm] at hhb; exact ⟨by omega, hhb⟩) hrw_roD
  have hs_rw_rw := SupportedOn.bupd_intro (supportedOn_rwAtomList (m := s0.mem) (hbAllRwSegAtoms C S)
    (fun x hx => by
      have hxC := List.all_eq_true.mp hrw_rwA x hx; simp only [Bool.and_eq_true] at hxC
      have ⟨hhb, _, hhi⟩ := holdsBytes_of_checkSegSlice hwf hload hrw hxC.2
      rw [hrw_perm] at hhb; exact ⟨by omega, hhb⟩) hrw_rwD)
  have hs_rw : SupportedOn 0#64
      (fun k => img.segments[C.rwSegIdx].start.toNat ≤ k ∧
        k < img.segments[C.rwSegIdx].start.toNat + img.segments[C.rwSegIdx].bytes.length)
      s0.mem (|==> (roSliceListSep (hbRwRoSlices C) ∗ rwAtomListSep (hbAllRwSegAtoms C S))) := by
    have hsep := ProofLib.SupportedOn.sepConj hs_rw_ro hs_rw_rw (by
      rintro k ⟨p, hp, hp1, hp2⟩ ⟨x, hx, hx1, hx2⟩
      have hc := hrw_cross (p.1.toNat, p.2.length) (List.mem_map_of_mem hp)
        (x.addr.toNat, x.rawBytes.length) (List.mem_map_of_mem hx)
      unfold intervalDisjoint at hc; simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hc; omega)
    refine (ProofLib.SupportedOn.mono (bupd_sep (Entails.refl _) (Entails.refl _)) hsep).widen ?_
    rintro k (⟨p, hp, hk1, hk2⟩ | ⟨x, hx, hk1, hk2⟩)
    · have hpC := List.all_eq_true.mp hrw_roS p hp
      unfold checkSegSlice at hpC; simp only [Bool.and_eq_true, decide_eq_true_eq] at hpC; omega
    · have hxC := List.all_eq_true.mp hrw_rwA x hx; simp only [Bool.and_eq_true] at hxC
      have hb := hxC.2; unfold checkSegSlice at hb; simp only [Bool.and_eq_true, decide_eq_true_eq] at hb; omega
  have hK : HbInitialStackScratchBytes ≤ max 262144 (inputs.init.stackSize / 2) := by
    have hfl := hvalid.2.1.2.size_floor
    unfold STK_LIM at hfl; unfold HbInitialStackScratchBytes; omega
  have hs_stk := hinfo.stack_supportedOn_bupd hvalid.2.1.1.random16 hK
  have hsp_lo : img.brkStart.toNat ≤ (StackLayout.of img inputs).sp0.toNat - HbInitialStackScratchBytes := by
    have hhr := hinfo.sp0_headroom
    have hfl := hvalid.2.1.2.size_floor
    unfold STK_LIM at hfl; unfold HbInitialStackScratchBytes; omega
  have hs_elf := SupportedOn.sepConj_bupd_interval
    (lo := img.segments[C.relroSegIdx].start.toNat) (hi := img.brkStart.toNat)
    hs_rel hs_rw (Or.inl hrel_rw_disj) (by omega) (by omega)
  have hs_all := SupportedOn.sepConj_bupd_interval
    (lo := img.segments[C.relroSegIdx].start.toNat) (hi := inputs.init.stackTop.toNat)
    hs_elf hs_stk (Or.inl hsp_lo) (by omega)
    (by have hhr := hinfo.sp0_headroom; have han := hinfo.addrs_nat; dsimp only at han; omega)
  have hsat_mut := SupportedOn.satisfies_bupd hs_all
  unfold checkHbRoSegment at hroC
  simp only [Bool.and_eq_true, beq_iff_eq] at hroC
  obtain ⟨⟨hro_perm, _⟩, hro_all⟩ := hroC
  have hsat_ro : ∀ (slices : List (BitVec 64 × List (BitVec 8))) {Q : SepProp},
      (slices.all fun (a, bs) => checkSegSlice roSeg roSeg.bytes.length a bs) = true →
      (s0.mem ⊨ Q) → (s0.mem ⊨ roSliceListSep slices ∗ Q) := by
    intro slices
    induction slices with
    | nil => intro Q _ hQ; rw [roSliceListSep, emp_sepConj]; exact hQ
    | cons hd_s tl_s ih =>
      rcases hd_s with ⟨a, bs⟩
      intro Q hall hQ
      simp only [List.all_cons, Bool.and_eq_true] at hall
      have ⟨hhb, _, hhi⟩ := holdsBytes_of_checkSegSlice hwf hload hro hall.1
      rw [hro_perm] at hhb
      rw [roSliceListSep_cons, sepConj_assoc]
      exact Satisfies.rodata_intro (holdsBytes_ro hhb).1 (holdsBytes_ro hhb).2 (by omega) (ih hall.2 hQ)
  have hfull := hsat_ro (hbRoSegSlices C) hro_all hsat_mut
  rw [hbAllRwSegAtoms_sep_eq] at hfull
  have heq :
      roSliceListSep (hbRoSegSlices C) ∗
        (((roSliceListSep (hbRelroRoSlices C) ∗ HbRelroRwGlobals C S) ∗
          (roSliceListSep (hbRwRoSlices C) ∗
           (StdDataGlobals C.std ∗ StdLibcGlobals C.std ∗ StdTlsGlobals C.std ∗
            MallocngInitialBss C.mallocng ∗ HbExtraRwGlobals C S))) ∗
         HbInitialStackSep img inputs) =
      HbStartupRoAll C ∗ HbRelroRwGlobals C S ∗ StdDataGlobals C.std ∗ StdLibcGlobals C.std ∗
        StdTlsGlobals C.std ∗ MallocngInitialBss C.mallocng ∗ HbExtraRwGlobals C S ∗
        HbInitialStackSep img inputs := by
    rw [← combine_roAll C]
    ac_rfl
  change s0.mem ⊨ roSliceListSep (hbRoSegSlices C) ∗
    (((roSliceListSep (hbRelroRoSlices C) ∗ HbRelroRwGlobals C S) ∗
      (roSliceListSep (hbRwRoSlices C) ∗
       (StdDataGlobals C.std ∗ StdLibcGlobals C.std ∗ StdTlsGlobals C.std ∗
        MallocngInitialBss C.mallocng ∗ HbExtraRwGlobals C S))) ∗
     HbInitialStackSep img inputs) at hfull
  rwa [heq] at hfull

/-! ## Shared Altstack Descriptor and Saved Caller-Frame Bundle (`StartupPre` and `StartupPost`) -/

/-- Optional signal alternate stack mapped during `lang_start_internal` (`make_handler`) and
    unmapped during `cleanupClosure` (`drop_handler`), framed as a `SepProp`:
    - `altOpt = none`: `[MAIN_ALTSTACK] = 0#64`;
    - `altOpt = some (altBase, altRawSz)`: anonymous mapping `[altBase, altBase + altRawSz + 4096)`
      owning `memRegionProtNone altBase 4096 ∗ memRegion (altBase + 4096#64) altRawSz`
      (`12288 <= altRawSz <= 524288`, page-aligned), with `[MAIN_ALTSTACK] = altBase + 4096#64`. -/
def HbAltstackInv (C : HbCliLayout) (S : HbStartupLayout)
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
    ⌜65536 ≤ altBase.toNat ∧
      altBase.toNat % 4096 = 0 ∧
      altRawSz % 4096 = 0 ∧
      12288 ≤ altRawSz ∧
      altRawSz ≤ 524288 ∧
      altBase.toNat + altRawSz + 4096 ≤ 2 ^ 48⌝ ∗
    (C.mainAltstackAddr ↦₆₄ (altBase + 4096#64)) ∗
    memRegionProtNone altBase 4096 ∗
    memRegion (altBase + 4096#64) altRawSz

def HbCallerFrames (C : HbCliLayout) (sp0 : BitVec 64) : SepProp :=
  ((sp0 - 0x170#64) ↦₆₄ (sp0 - 0x160#64)) ∗
  ((sp0 - 0x168#64) ↦₆₄ (C.langStartClosureAddr + 0x10#64)) ∗
  ((sp0 - 0x160#64) ↦₆₄ (sp0 - 0xb0#64)) ∗
  ((sp0 - 0x158#64) ↦₆₄ (C.langStartInternalAddr + 0x394#64)) ∗
  stackAt (sp0 - 0xb0#64) 160 ∗
  ((sp0 - 0xb0#64) ↦₆₄ (sp0 - 0x40#64)) ∗
  ((sp0 - 0xa8#64) ↦₆₄ (C.std.cMainAddr + 0x34#64)) ∗
  stackAt (sp0 - 0x40#64) 96 ∗
  (∃∗ fp_cm : BitVec 64, (sp0 - 0x40#64) ↦₆₄ fp_cm) ∗
  ((sp0 - 0x38#64) ↦₆₄ (C.std.libcStartMainStage2Addr + 0x38#64)) ∗
  stackAt sp0 48

def HbMuslExitGlobalsNoNeedLocks (C : HbCliLayout) (S : HbStartupLayout)
    (finalized : BitVec 8) : SepProp :=
  let L := C.std
  (L.finiArrayAddr ↦₆₄ L.doFiniAddr) ∗
  ((L.gotAddr + 0x20#64) ↦₆₄ 0#64) ∗
  ((L.gotAddr + 0x28#64) ↦₆₄ 0#64) ∗
  (S.gotFiniArrayEndAddr ↦₆₄ (L.finiArrayAddr + 0x08#64)) ∗
  (S.gotFiniArrayStartAddr ↦₆₄ L.finiArrayAddr) ∗
  (L.finalizedAddr ↦₈ finalized) ∗
  (L.oflHeadAddr ↦₆₄ 0#64) ∗
  (L.oflLockAddr ↦₃₂ 0#32) ∗
  (L.stdinUsedAddr ↦₆₄ 0#64) ∗
  (L.stdoutUsedAddr ↦₆₄ 0#64) ∗
  (L.stderrUsedAddr ↦₆₄ L.stderrFileAddr) ∗
  StdStderrFile L

def HbPostMainGlobals (C : HbCliLayout) (S : HbStartupLayout) : SepProp :=
  let L := C.std
  (L.cleanupOnceAddr ↦₃₂ 3#32) ∗
  StdVtableRo L.cleanupVtableAddr L.cleanupVtableShimAddr L.cleanupClosureAddr ∗
  StdVtableRo L.stdoutVtableAddr L.stdoutVtableShimAddr L.stdoutCleanupClosureAddr ∗
  (L.pageSizeGlobalAddr ↦₆₄ 4096#64) ∗
  (L.exitingThreadIdAddr ↦₆₄ 0#64) ∗
  HbMuslExitGlobalsNoNeedLocks C S 0#8

end CaseStudies.Hashbrown.Proofs.StdCli
