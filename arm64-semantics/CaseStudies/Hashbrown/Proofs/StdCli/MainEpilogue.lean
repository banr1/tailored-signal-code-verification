/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import CaseStudies.Hashbrown.Proofs.StdCli.Shims
public import CaseStudies.Hashbrown.Proofs.StdCli.StdinAndVec
public import CaseStudies.Hashbrown.Proofs.StdCli.SyscallsAndStderr
public import CaseStudies.Hashbrown.Proofs.StdCli.MainPure
public import CaseStudies.Hashbrown.Proofs.PlacedCode
public meta import ProofLib.LiteralFetchLint
import ProofLib.BV

/-!
# Main Code Bundle and Vec-Drop Epilogue

Symbolic code bundle (`HbUserMainCode`), `WordTree` validator, and separation-logic proofs for
`hashbrown_cli::main`'s `0xe0`-byte stack frame and `Vec<u8>` deallocation epilogues.
-/

set_option autoImplicit false

@[expose] public section

namespace CaseStudies.Hashbrown.Proofs.StdCli

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection ProofLib.StdStartup
open CaseStudies.Hashbrown CaseStudies.Hashbrown.Proofs

local macro "iAdrp " rd:term:arg pc:term:arg t:term:arg : term =>
  `(Instr.adr true $rd (adrpOff $pc $t))
local macro "iAdr " rd:term:arg pc:term:arg t:term:arg : term =>
  `(Instr.adr false $rd ($t - $pc))
local macro "iAddLo12 " rd:term:arg rn:term:arg t:term:arg : term =>
  `(Instr.addSubImm .W64 .ADD $rd $rn (($t).truncate 12) false)
local macro "iBl " pc:term:arg t:term:arg : term =>
  `(Instr.bl ($t - $pc))
local macro "iB " pc:term:arg t:term:arg : term =>
  `(Instr.b ($t - $pc))

def hbStdioStdinChunks (C : HbCliLayout) : List CodeChunk :=
  let b := C.stdioStdinAddr
  [ .instrs0 b
      [iAdrp .x8 b (C.stdinGlobalAddr + 0x30#64),
       iAddLo12 .x8 .x8 (C.stdinGlobalAddr + 0x30#64)],
    .words (b + 0x08#64) [0x88dffd08#32, 0x35000088#32, 0xd503201f#32],
    .instrs b 0x14 [iAdr .x0 (b + 0x14#64) C.stdinGlobalAddr],
    .words (b + 0x18#64) [0xd65f03c0#32, 0xa9bf7bfd#32, 0x910003fd#32],
    .instrs b 0x24 [iBl (b + 0x24#64) C.stdinOnceLockInitAddr],
    .words (b + 0x28#64) [0xa8c17bfd#32, 0xd503201f#32],
    .instrs b 0x30 [iAdr .x0 (b + 0x30#64) C.stdinGlobalAddr],
    .words (b + 0x34#64) [0xd65f03c0#32] ]

def hbStdinReadToEndChunks (C : HbCliLayout) : List CodeChunk :=
  let b := C.stdinReadToEndAddr
  [ .words b
      [0xa9bc7bfd#32, 0xf9000bf7#32, 0xa90257f6#32, 0xa9034ff4#32, 0x910003fd#32,
       0xf9400013#32, 0xaa0103f4#32, 0x2a1f03e0#32, 0x52800021#32, 0xaa1303e2#32],
    .instrs b 0x28 [iBl (b + 0x28#64) C.std.cas4AcqAddr],
    .words (b + 0x2c#64) [0x7100001f#32, 0x540003a1#32, 0xd503201f#32],
    .instrs b 0x38 [iAdr .x23 (b + 0x38#64) C.globalPanicCountAddr],
    .words (b + 0x3c#64)
      [0xf94002e8#32, 0xf240f91f#32, 0x540003e1#32, 0x2a1f03f6#32,
       0x3940127f#32, 0x91002260#32, 0xaa1403e1#32],
    .instrs b 0x58 [iBl (b + 0x58#64) C.bufReaderReadToEndAddr],
    .words (b + 0x5c#64)
      [0xaa0003f4#32, 0xaa0103f5#32, 0x37000096#32, 0xf94002e8#32,
       0xf240f91f#32, 0x540003a1#32, 0x2a1f03e0#32, 0xaa1303e1#32],
    .instrs b 0x7c [iBl (b + 0x7c#64) C.std.swp4RelAddr],
    .words (b + 0x80#64)
      [0x7100081f#32, 0x54000240#32, 0xaa1403e0#32, 0xaa1503e1#32, 0xa9434ff4#32,
       0xf9400bf7#32, 0xa94257f6#32, 0xa8c47bfd#32, 0xd65f03c0#32] ]

def hbBufReaderReadToEndChunks (C : HbCliLayout) : List CodeChunk :=
  let b := C.bufReaderReadToEndAddr
  [ .words b
      [0xd10203ff#32, 0xa9027bfd#32, 0xf9001bfb#32, 0xa90467fa#32, 0xa9055ff8#32,
       0xa90657f6#32, 0xa9074ff4#32, 0x910083fd#32, 0xaa0003f6#32, 0xf9400c1a#32,
       0xf9400837#32, 0xf8410ed8#32, 0xf9400028#32, 0xf9400019#32, 0xcb180353#32,
       0xcb170109#32, 0xeb09027f#32, 0x54000369#32],
    .words (b + 0xb0#64) [0xeb18035f#32, 0x54000100#32],
    .words (b + 0xd4#64)
      [0x8b1302e8#32, 0xaa0103e0#32, 0xa9007edf#32, 0xf9000828#32, 0xaa1f03e1#32],
    .instrs b 0xe8 [iBl (b + 0xe8#64) C.defaultReadToEndAddr],
    .words (b + 0xec#64) [0x36000180#32],
    .words (b + 0x11c#64) [0xaa1f03e0#32, 0x14000003#32],
    .words (b + 0x12c#64)
       [0x8b010274#32, 0xaa1403e1#32, 0xa9474ff4#32, 0xf9401bfb#32, 0xa94657f6#32,
        0xa9455ff8#32, 0xa94467fa#32, 0xa9427bfd#32, 0x910203ff#32, 0xd65f03c0#32] ]

def hbDefaultReadToEndChunks (C : HbCliLayout) : List CodeChunk :=
  let b := C.defaultReadToEndAddr
  [ .words b
      [0xd10243ff#32, 0xa9037bfd#32, 0xa9046ffc#32, 0xa90567fa#32, 0xa9065ff8#32,
       0xa90757f6#32, 0xa9084ff4#32, 0x9100c3fd#32, 0xf940081c#32, 0xf940001b#32,
       0xaa0103fa#32, 0xaa0003f3#32, 0xf100043f#32, 0x54000241#32],
    .words (b + 0x7c#64)
      [0x52840019#32, 0xcb1c0368#32, 0xf100811f#32, 0x54000262#32, 0xaa1303e0#32],
    .instrs b 0x90 [iBl (b + 0x90#64) C.smallProbeReadAddr],
    .words (b + 0x94#64)
      [0xf100041f#32, 0xaa0103f8#32, 0x54000d60#32, 0xb4000158#32,
       0xf90003fc#32, 0xf9400a7c#32, 0xf9400276#32, 0xd503201f#32],
    .instrs b 0xb4 [iAdr .x21 (b + 0xb4#64) C.defaultOsFunctionsAddr],
    .words (b + 0xb8#64)
      [0xa900ebfb#32, 0xeb16039f#32, 0x54000180#32, 0x14000015#32,
       0xaa1f03e0#32, 0x1400005f#32],
    .words (b + 0xf0#64) [0xeb1b02df#32, 0x54000121#32, 0xaa1303e0#32],
    .instrs b 0xfc [iBl (b + 0xfc#64) C.smallProbeReadAddr],
    .words (b + 0x100#64)
      [0xf100041f#32, 0xaa0103f8#32, 0x54000a00#32, 0xf9400a7c#32, 0xb4000af8#32,
       0xf9400276#32, 0xf9400677#32, 0xeb16039f#32, 0x540006c0#32, 0xf9400276#32,
       0xcb1c02c8#32, 0x92f00009#32, 0xaa1903f4#32, 0xeb08033f#32, 0x8b1c02e1#32,
       0x2a1f03e0#32, 0x9a883328#32, 0xeb09011f#32, 0x9a893119#32, 0xaa1903e2#32],
    .instrs b 0x150 [iBl (b + 0x150#64) C.readAddr],
    .words (b + 0x154#64)
      [0xb100041f#32, 0x54000120#32, 0x8b1c001c#32, 0xf9000a7c#32, 0xb4000860#32,
       0x7200035f#32, 0xda9f1299#32, 0xeb16039f#32, 0x54fffbe0#32, 0x17ffffe8#32],
    .words (b + 0x1f8#64)
      [0xd37ffac8#32, 0x910082c9#32, 0x910063e0#32, 0xaa1603e1#32, 0xaa1703e2#32,
       0x52800024#32, 0xeb08013f#32, 0x52800025#32, 0x9a888138#32, 0xaa1803e3#32],
    .instrs b 0x220 [iBl (b + 0x220#64) C.rawVecFinishGrowAddr],
    .words (b + 0x224#64)
      [0xf9400fe8#32, 0xf100051f#32, 0x54000280#32, 0xf94013f7#32,
       0xaa1803f6#32, 0xa9005e78#32, 0x17ffffbb#32],
    .words (b + 0x248#64)
      [0xaa1803e1#32, 0xa9484ff4#32, 0xa94757f6#32, 0xa9465ff8#32, 0xa94567fa#32,
       0xa9446ffc#32, 0xa9437bfd#32, 0x910243ff#32, 0xd65f03c0#32, 0xaa1f03e0#32,
       0xf94003e8#32, 0xcb080398#32, 0x17fffff4#32] ]

abbrev hbMainPrologueWords : List (BitVec 32) :=
  [0xd10383ff#32, 0xa9087bfd#32, 0xf9004bfb#32, 0xa90a67fa#32, 0xa90b5ff8#32,
   0xa90c57f6#32, 0xa90d4ff4#32, 0x910203fd#32, 0x52800028#32, 0xf9000fff#32,
   0xa900a3ff#32]

abbrev hbMainEpilogueRetWords : List (BitVec 32) :=
  [0x2a1303e0#32, 0xa94d4ff4#32, 0xf9404bfb#32, 0xa94c57f6#32, 0xa94b5ff8#32,
   0xa94a67fa#32, 0xa9487bfd#32, 0x910383ff#32, 0xd65f03c0#32]

abbrev hbMainScanWords : List (BitVec 32) :=
  [0xf9400fe8#32, 0xb40003e8#32, 0xf9400be9#32, 0xd100050a#32, 0x2a1f03eb#32,
   0x386a692c#32, 0x7100299f#32, 0x9a880156#32, 0xaa0903ea#32, 0xaa1603e8#32,
   0x14000004#32, 0x5280002b#32, 0xf140059f#32, 0x540011e8#32, 0x3700028b#32,
   0xaa1f03ec#32, 0xb4ffff68#32, 0x386c694b#32, 0x7100297f#32, 0x540000e0#32,
   0x9100058c#32, 0xeb0c011f#32, 0x54ffff61#32, 0x5280002b#32, 0xaa0803ec#32,
   0x17fffff3#32, 0xaa2c03ed#32, 0x8b0c014a#32, 0x2a1f03eb#32, 0x8b0801a8#32,
   0x9100054a#32, 0x17ffffed#32, 0x2a1f03f3#32, 0x17ffffd0#32]

def hbRustMainReadScanChunks (C : HbCliLayout) : List CodeChunk :=
  let u := C.std.userMainAddr
  [ .words u hbMainPrologueWords,
    .instrs u 0x2c [iBl (u + 0x2c#64) C.stdioStdinAddr],
    .words (u + 0x30#64) [0xf90013e0#32, 0x910083e0#32, 0x910023e1#32],
    .instrs u 0x3c [iBl (u + 0x3c#64) C.stdinReadToEndAddr],
    .words (u + 0x40#64) [0xb40003a0#32],
    .words (u + 0x78#64)
      [0xf94007e1#32, 0x2a1303e0#32, 0xb40000a1#32, 0xf9400be0#32, 0x52800022#32],
    .instrs u 0x8c [iBl (u + 0x8c#64) C.rustDeallocAddr],
    .words (u + 0x90#64) hbMainEpilogueRetWords,
    .words (u + 0xb4#64) hbMainScanWords,
    .words (u + 0x310#64)
      [0xf94007e1#32, 0x2a1f03f3#32, 0x2a1f03e0#32, 0xb5ffeb41#32,
       0x17ffff5d#32, 0xd503201f#32],
    .instrs u 0x328 [iAdr .x8 (u + 0x328#64) C.stderrGlobalAddr],
    .words (u + 0x32c#64) [0xd503201f#32],
    .instrs u 0x330 [iAdr .x1 (u + 0x330#64) C.errLineTooLongAddr],
    .words (u + 0x334#64) [0x910083e0#32, 0x528002a2#32, 0xf90013e8#32],
    .instrs u 0x340 [iBl (u + 0x340#64) C.stderrWriteAllAddr],
    .words (u + 0x344#64) [0xb40001a0#32],
    .words (u + 0x378#64) [0x52800033#32, 0x17ffff3f#32] ]

def hbUserMainChunks (C : HbCliLayout) : List CodeChunk :=
  hbStdioStdinChunks C ++ hbStdinReadToEndChunks C ++ hbBufReaderReadToEndChunks C ++
    hbDefaultReadToEndChunks C ++ hbRustMainReadScanChunks C

structure HbUserMainCode (P : Program) (C : HbCliLayout) : Prop where
  stdioStdin     : CodeChunks P (hbStdioStdinChunks C)
  stdinReadToEnd : CodeChunks P (hbStdinReadToEndChunks C)
  bufReaderRead  : CodeChunks P (hbBufReaderReadToEndChunks C)
  defaultRead    : CodeChunks P (hbDefaultReadToEndChunks C)
  rustMain       : CodeChunks P (hbRustMainReadScanChunks C)

section WordTreeCheck

private theorem hbMainCodeChunk_withSvc {P : Program} {svc : State → State} :
    ∀ {c : CodeChunk}, c.holds P → c.holds (P.withSvc svc)
  | .words _ _, h => h
  | .instrs0 _ _, h => fun i hi => by rw [Program.withSvc_fetch]; exact h i hi
  | .instrs _ _ _, h => fun i hi => by rw [Program.withSvc_fetch]; exact h i hi

private theorem hbMainCodeChunks_withSvc {P : Program} {svc : State → State} :
    ∀ {cs : List CodeChunk}, CodeChunks P cs → CodeChunks (P.withSvc svc) cs
  | [], _ => trivial
  | [_], h => hbMainCodeChunk_withSvc h
  | _ :: _ :: _, ⟨h1, h2⟩ => ⟨hbMainCodeChunk_withSvc h1, hbMainCodeChunks_withSvc h2⟩

theorem HbUserMainCode.withSvc {P : Program} {C : HbCliLayout} (svc : State → State)
    (h : HbUserMainCode P C) :
    HbUserMainCode (P.withSvc svc) C :=
  ⟨hbMainCodeChunks_withSvc h.stdioStdin,
   hbMainCodeChunks_withSvc h.stdinReadToEnd,
   hbMainCodeChunks_withSvc h.bufReaderRead,
   hbMainCodeChunks_withSvc h.defaultRead,
   hbMainCodeChunks_withSvc h.rustMain⟩

private theorem hbMainCodeChunks_append {P : Program} :
    ∀ {xs ys : List CodeChunk}, CodeChunks P xs → CodeChunks P ys → CodeChunks P (xs ++ ys)
  | [], _, _, hy => hy
  | [_], [], hx, _ => hx
  | [_], _ :: _, hx, hy => ⟨hx, hy⟩
  | _ :: _ :: _, _, ⟨h1, h2⟩, hy => ⟨h1, hbMainCodeChunks_append h2 hy⟩

theorem HbUserMainCode.allChunks {P : Program} {C : HbCliLayout} (h : HbUserMainCode P C) :
    CodeChunks P (hbUserMainChunks C) :=
  hbMainCodeChunks_append
    (hbMainCodeChunks_append
      (hbMainCodeChunks_append
        (hbMainCodeChunks_append h.stdioStdin h.stdinReadToEnd)
        h.bufReaderRead)
      h.defaultRead)
    h.rustMain

private theorem hbMainCodeChunks_of_check {P : Program} {b : BitVec 64} {t : WordTree}
    (hc : ∀ {c : CodeChunk}, checkCodeChunk b t c = true → c.holds P) :
    ∀ {cs : List CodeChunk}, cs.all (checkCodeChunk b t) = true → CodeChunks P cs
  | [], _ => trivial
  | [_], h => hc (by simpa using h)
  | _ :: _ :: _, h => by
    rw [List.all_cons, Bool.and_eq_true] at h
    exact ⟨hc h.1, hbMainCodeChunks_of_check hc h.2⟩

def checkHbUserMainCode (C : HbCliLayout) (base : BitVec 64) (t : WordTree) : Bool :=
  (hbStdioStdinChunks C).all (checkCodeChunk base t) &&
  (hbStdinReadToEndChunks C).all (checkCodeChunk base t) &&
  (hbBufReaderReadToEndChunks C).all (checkCodeChunk base t) &&
  (hbDefaultReadToEndChunks C).all (checkCodeChunk base t) &&
  (hbRustMainReadScanChunks C).all (checkCodeChunk base t)

theorem hbUserMainCode_of_wordTree {P : Program} {C : HbCliLayout} {t : WordTree}
    (n : Nat) (hcode : P.code = t.toBytes) (hwf : t.checkSize? = some n)
    (hstubs : P.stubs = [] := by rfl) (hsyms : P.symbols = [] := by rfl)
    (hext : ∀ sym, (P.externs sym).isNone = true := by intro _; rfl)
    (hovr : ∀ sym, (P.overrides sym).isNone = true := by intro _; rfl)
    (hok : checkHbUserMainCode C P.base t = true) :
    HbUserMainCode P C := by
  have hc : ∀ {c : CodeChunk}, checkCodeChunk P.base t c = true → c.holds P := by
    rintro (⟨a, ws⟩ | ⟨b, is⟩ | ⟨b, o, is⟩) h
    · simp only [checkCodeChunk, checkCleanupWordsAt, Bool.and_eq_true, decide_eq_true_eq] at h
      exact hasWords_of_wordTree n hcode hwf rfl h.1 hstubs hsyms h.2
    all_goals
      simp only [checkCodeChunk, checkCleanupInstrsAt, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      exact hasInstrs_of_wordTree n hcode hwf h.1.1 h.1.2 hext hovr h.2
  unfold checkHbUserMainCode at hok
  simp only [Bool.and_eq_true] at hok
  rcases hok with ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
  exact ⟨hbMainCodeChunks_of_check hc h1,
         hbMainCodeChunks_of_check hc h2,
         hbMainCodeChunks_of_check hc h3,
         hbMainCodeChunks_of_check hc h4,
         hbMainCodeChunks_of_check hc h5⟩

end WordTreeCheck

theorem codeChunks_getElem? {P : Program} :
    ∀ {cs : List CodeChunk} {i : Nat} {c : CodeChunk},
      CodeChunks P cs → cs[i]? = some c → c.holds P
  | [x], 0, _, hx, h => by cases h; exact hx
  | [_], _ + 1, _, _, h => by simp at h
  | x :: _ :: _, 0, _, ⟨hx, _⟩, h => by cases h; exact hx
  | _ :: _ :: _, _ + 1, _, ⟨_, hr⟩, h => codeChunks_getElem? hr h

theorem codeChunks_of_forall {P : Program} :
    ∀ {cs : List CodeChunk}, (∀ c ∈ cs, c.holds P) → CodeChunks P cs
  | [], _ => trivial
  | [c], h => h c (List.Mem.head [])
  | c :: _d :: _rest, h =>
    ⟨h c (List.Mem.head _), codeChunks_of_forall (fun x hx => h x (List.Mem.tail c hx))⟩

theorem codeChunks_select {P : Program} {cs : List CodeChunk}
    (hc : CodeChunks P cs) (idxs : List Nat) :
    CodeChunks P (idxs.filterMap (fun i => cs[i]?)) := by
  refine codeChunks_of_forall fun c hmem => ?_
  rw [List.mem_filterMap] at hmem
  obtain ⟨i, _, hi⟩ := hmem
  exact codeChunks_getElem? hc hi

local macro "unpack_hb_main_code " chunks:ident h:term : tactic => `(tactic| (
  have _hc := chunksToStepFacts $h
  simp only [$chunks:ident, chunksStepFacts, chunkStepAcc, fetchAtAcc,
    Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at _hc
  (repeat obtain ⟨_, _hc⟩ := _hc); try clear _hc))

local macro "wp_a" : term => `(by simp [wp_norm, arm64_norm, bv_lin_norm, *] <;> try bv_lin)

/-- Saved 11 callee-saved / frame-pointer / link-register 64-bit slots at
    `[sp_m + 0x80 .. sp_m + 0x98)` and `[sp_m + 0xa0 .. sp_m + 0xe0)`
    stored by `hashbrown_cli::main`'s prologue (`u + 0x004..0x018`).
    Note: `[sp_m + 0x98 .. sp_m + 0xa0)` (`[x29 + 0x18]`) is a local scratch slot,
    and `x28` is never modified by `hashbrown_cli::main`. -/
def HbMainSavedRegs (sp_m : BitVec 64) (s_main : State) : SepProp :=
  ((sp_m + 0x80#64) ↦₆₄ s_main.readReg64 .x29) ∗
  ((sp_m + 0x88#64) ↦₆₄ s_main.readReg64 .lr) ∗
  ((sp_m + 0x90#64) ↦₆₄ s_main.readReg64 .x27) ∗
  ((sp_m + 0xa0#64) ↦₆₄ s_main.readReg64 .x26) ∗
  ((sp_m + 0xa8#64) ↦₆₄ s_main.readReg64 .x25) ∗
  ((sp_m + 0xb0#64) ↦₆₄ s_main.readReg64 .x24) ∗
  ((sp_m + 0xb8#64) ↦₆₄ s_main.readReg64 .x23) ∗
  ((sp_m + 0xc0#64) ↦₆₄ s_main.readReg64 .x22) ∗
  ((sp_m + 0xc8#64) ↦₆₄ s_main.readReg64 .x21) ∗
  ((sp_m + 0xd0#64) ↦₆₄ s_main.readReg64 .x20) ∗
  ((sp_m + 0xd8#64) ↦₆₄ s_main.readReg64 .x19)

theorem stackAt_split_main (sp : BitVec 64) (a b : Nat) {n : Nat}
    (hab : n = a + b := by rfl) (h : a + b ≤ 2 ^ 64 := by decide) :
    stackAt sp n = stackAt (sp - BitVec.ofNat 64 a) b ∗ stackAt sp a := by
  subst hab; rw [stackAt_split_bottom sp a b h]; unfold stackAt; rw [BitVec.sub_sub, BitVec.ofNat_add]

theorem memRegion_eq_cell8 (a : BitVec 64) : memRegion a 8 = cells a 1 := by
  have h := stackAt_eq_cells (a + 8#64) 1
  unfold stackAt at h
  have ha : a + 8#64 - BitVec.ofNat 64 (8 * 1) = a := by bv_lin
  simpa [ha] using h

theorem hbMainStack_split (sp_top : BitVec 64) {sp_m : BitVec 64}
    (hsp_m : sp_m = sp_top - 0xe0#64 := by rfl) :
    stackAt sp_top 261984 =
      stackAt sp_m (261984 - 224) ∗
      memRegion sp_m 8 ∗
      cells (sp_m + 0x08#64) 3 ∗
      stackAt (sp_m + 0x80#64) 96 ∗
      cells (sp_m + 0x80#64) 3 ∗
      memRegion (sp_m + 0x98#64) 8 ∗
      cells (sp_m + 0xa0#64) 8 := by
  have h1 : stackAt sp_top 261984 = stackAt sp_m (261984 - 224) ∗ stackAt sp_top 224 := by
    rw [hsp_m]; exact stackAt_split_main sp_top 224 (261984 - 224)
  have h2 : stackAt sp_top 224 = stackAt (sp_m + 0xa0#64) 160 ∗ cells (sp_m + 0xa0#64) 8 := by
    rw [stackAt_split_main sp_top 64 160]
    have hs64 : stackAt sp_top 64 = cells (sp_m + 0xa0#64) 8 := by
      have heq := stackAt_eq_cells sp_top 8
      simpa [show sp_top - BitVec.ofNat 64 (8 * 8) = sp_m + 0xa0#64 by rw [hsp_m]; bv_lin] using heq
    have ha : sp_top - BitVec.ofNat 64 64 = sp_m + 0xa0#64 := by rw [hsp_m]; bv_lin
    rw [hs64, ha]
  have h3 : stackAt (sp_m + 0xa0#64) 160 =
      stackAt (sp_m + 0x98#64) 152 ∗ memRegion (sp_m + 0x98#64) 8 := by
    rw [stackAt_split_main (sp_m + 0xa0#64) 8 152]
    unfold stackAt
    have hb : sp_m + 0xa0#64 - BitVec.ofNat 64 8 = sp_m + 0x98#64 := by bv_lin
    rw [hb]
  have h4 : stackAt (sp_m + 0x98#64) 152 =
      stackAt (sp_m + 0x80#64) 128 ∗ cells (sp_m + 0x80#64) 3 := by
    rw [stackAt_split_main (sp_m + 0x98#64) 24 128,
        show (24 : Nat) = 8 * 3 from rfl, stackAt_eq_cells (sp_m + 0x98#64) 3]
    have hc : sp_m + 0x98#64 - BitVec.ofNat 64 24 = sp_m + 0x80#64 := by bv_lin
    rw [hc]
  have h5 : stackAt (sp_m + 0x80#64) 128 =
      stackAt (sp_m + 0x20#64) 32 ∗ stackAt (sp_m + 0x80#64) 96 := by
    rw [stackAt_split_main (sp_m + 0x80#64) 96 32]
    have hd : sp_m + 0x80#64 - BitVec.ofNat 64 96 = sp_m + 0x20#64 := by bv_lin
    rw [hd]
  have h6 : stackAt (sp_m + 0x20#64) 32 =
      memRegion sp_m 8 ∗ cells (sp_m + 0x08#64) 3 := by
    rw [stackAt_split_main (sp_m + 0x20#64) 24 8,
        show (24 : Nat) = 8 * 3 from rfl, stackAt_eq_cells (sp_m + 0x20#64) 3]
    have he : sp_m + 0x20#64 - BitVec.ofNat 64 24 = sp_m + 0x08#64 := by bv_lin
    rw [he]
    unfold stackAt
    have hf : sp_m + 0x08#64 - BitVec.ofNat 64 8 = sp_m := by bv_lin
    rw [hf]
  rw [h1, h2, h3, h4, h5, h6]
  apply Entails.antisymm <;> sep_entail

private theorem cell_one {a : BitVec 64} (v : BitVec 64) :
    (a ↦₆₄ v) ⊢ cells a 1 := by
  rw [cells_succ, cells_zero]
  exact Entails.sepExists_right v (by sep_entail)

private theorem cell_cons {a a' : BitVec 64} {k : Nat} (v : BitVec 64) {R : SepProp}
    (h : R ⊢ cells a' k) (ha : a + 8#64 = a' := by bv_lin) :
    ((a ↦₆₄ v) ∗ R) ⊢ cells a (k + 1) := by
  subst ha; rw [cells_succ]
  exact Entails.sepExists_right v (sepConj_mono_right h)

theorem hbMainStack_repack_entails (s_main : State) {sp_m : BitVec 64}
    (hsp_m : sp_m = s_main.sp - 0xe0#64) (v0 v1 v2 : BitVec 64) :
    stackAt sp_m (261984 - 224) ∗
      memRegion sp_m 8 ∗
      ((sp_m + 0x08#64) ↦₆₄ v0) ∗ ((sp_m + 0x10#64) ↦₆₄ v1) ∗ ((sp_m + 0x18#64) ↦₆₄ v2) ∗
      stackAt (sp_m + 0x80#64) 96 ∗
      HbMainSavedRegs sp_m s_main ∗
      memRegion (sp_m + 0x98#64) 8 ⊢
    stackAt s_main.sp 261984 := by
  have hc3 :
      ((sp_m + 0x08#64) ↦₆₄ v0) ∗ ((sp_m + 0x10#64) ↦₆₄ v1) ∗ ((sp_m + 0x18#64) ↦₆₄ v2) ⊢
      cells (sp_m + 0x08#64) 3 :=
    cell_cons v0 (cell_cons v1 (cell_one v2))
  have hcs3 :
      ((sp_m + 0x80#64) ↦₆₄ s_main.readReg64 .x29) ∗
      ((sp_m + 0x88#64) ↦₆₄ s_main.readReg64 .lr) ∗
      ((sp_m + 0x90#64) ↦₆₄ s_main.readReg64 .x27) ⊢
      cells (sp_m + 0x80#64) 3 :=
    cell_cons _ (cell_cons _ (cell_one _))
  have hcs8 :
      ((sp_m + 0xa0#64) ↦₆₄ s_main.readReg64 .x26) ∗
      ((sp_m + 0xa8#64) ↦₆₄ s_main.readReg64 .x25) ∗
      ((sp_m + 0xb0#64) ↦₆₄ s_main.readReg64 .x24) ∗
      ((sp_m + 0xb8#64) ↦₆₄ s_main.readReg64 .x23) ∗
      ((sp_m + 0xc0#64) ↦₆₄ s_main.readReg64 .x22) ∗
      ((sp_m + 0xc8#64) ↦₆₄ s_main.readReg64 .x21) ∗
      ((sp_m + 0xd0#64) ↦₆₄ s_main.readReg64 .x20) ∗
      ((sp_m + 0xd8#64) ↦₆₄ s_main.readReg64 .x19) ⊢
      cells (sp_m + 0xa0#64) 8 :=
    cell_cons _ (cell_cons _ (cell_cons _ (cell_cons _
      (cell_cons _ (cell_cons _ (cell_cons _ (cell_one _)))))))
  dsimp only [HbMainSavedRegs]
  rw [hbMainStack_split s_main.sp hsp_m]
  exact entails_mono_atom hc3 (hQ :=
    entails_mono_atom hcs3 (hQ :=
      entails_mono_atom hcs8))

theorem hbMainStack_repack (s_main : State) {sp_m : BitVec 64}
    (hsp_m : sp_m = s_main.sp - 0xe0#64) (v0 v1 v2 : BitVec 64) {m : Memory} {R : SepProp}
    (hm : m ⊨ (stackAt sp_m (261984 - 224) ∗
      memRegion sp_m 8 ∗
      ((sp_m + 0x08#64) ↦₆₄ v0) ∗ ((sp_m + 0x10#64) ↦₆₄ v1) ∗ ((sp_m + 0x18#64) ↦₆₄ v2) ∗
      stackAt (sp_m + 0x80#64) 96 ∗
      HbMainSavedRegs sp_m s_main ∗
      memRegion (sp_m + 0x98#64) 8) ∗ R) :
    m ⊨ stackAt s_main.sp 261984 ∗ R :=
  Satisfies.mono (sepConj_mono_left (hbMainStack_repack_entails s_main hsp_m v0 v1 v2)) hm

theorem SepWP.with_keepsFrozen {prog : Program} {target : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop}
    (h : SepWP prog target s P (fun sf Pf => s.mem.KeepsFrozen sf.mem → post sf Pf)) :
    SepWP prog target s P post :=
  SepWP.mono_frozen (Φ := s.mem.KeepsFrozen) (fun _ _ => Memory.KeepsFrozen.trans)
    (Memory.KeepsFrozen.refl s.mem) h (fun _ _ _ _ hkf hp => hp hkf)

theorem call_free {P : Program} {addrs : MallocngAddrs} {lim : MallocngLimits}
    {target_pc ret_pc sp_call : BitVec 64}
    (M : MallocngCoreIface P addrs lim) (γ : GhostName)
    {lc blk req : Nat} {ptr : BitVec 64} {e0 : BitVec 32}
    {s0 s : State} {Pre F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hvm : VmFieldsPreserved s0 s := by exact ⟨rfl, rfl, rfl, fun _ => rfl⟩)
    (hptr_nz : ptr ≠ 0#64)
    (hpre : ∀ R : SepProp, (s.mem ⊨ Pre ∗ R) →
      (s.mem ⊨ (M.Heap γ lc blk s0 ∗ M.Block γ ptr req ∗ memRegion ptr req ∗
        (muslErrnoAddr s0 ↦₃₂ e0) ∗ stackAt sp_call MallocngStackBytes) ∗ (F ∗ R)))
    (hnext : ∀ (sf : State) (e1 : BitVec 32),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → CalleeSavedPreserved s sf →
      MallocngStatePreserved s sf →
      SepWP P target_pc sf
        ((M.Heap γ (lc - mallocngBlockCost req) (blk - 1) sf ∗
          (muslErrnoAddr sf ↦₃₂ e1) ∗ stackAt sp_call MallocngStackBytes) ∗ F) post oom)
    (hpc : s.pc = addrs.freeAddr := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hrun : s.status = .Running := by simp only [arm64_norm, *])
    (hsp_call : s.sp = sp_call := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (herr0 : muslErrnoAddr s0 = muslErrnoAddr s := by simp [muslErrnoAddr, wp_norm, arm64_norm, *])
    (hsp_align : s.spAligned = true := by
      simp (config := { decide := true }) only [State.spAligned, arm64_norm, *]
      try (simp only [State.spAligned, beq_iff_eq] at *; bv_bits))
    (hlr : s.readReg64 Reg.lr = ret_pc := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hx0 : s.readReg64 .x0 = ptr := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (h_oom : ∀ R' sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ (⌜False⌝ : SepProp) ∗ (F ∗ R')) → (sf.mem ⊨ oom sf ∗ R') := by wp_close_oom_default) :
    SepWP P target_pc s Pre post oom := by
  refine SepWP.call_subroutine_frame (M.free_ok γ) (x := (lc, blk, some req, e0)) (F := F)
    hpc hrun hsp_align hlr ?_ (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h) ?_ h_oom
  · intro R hm
    dsimp only; simp only [sepConj_assoc]
    have hp : s.readReg64 (.gpr 0#5) = ptr := by simpa [Reg.x0] using hx0
    rw [hp, sepConj_pull_pure, satisfies_pure_sepConj]
    refine ⟨hptr_nz, ?_⟩
    have hm' := hpre R hm
    rw [herr0, ← hsp_call] at hm'
    exact Satisfies.mono (sepConj_mono (vmHeapTransport M hvm) (Entails.refl _))
      (by simpa only [sepConj_assoc] using hm')
  · intro sf hpc_f hrun_f hsp_f hcs_f
    dsimp only; simp only [sepConj_assoc]
    apply SepWP.pure_elim; intro hmsp
    have herr_eq : muslErrnoAddr s = muslErrnoAddr sf := by simp [muslErrnoAddr, hmsp.2.2.2.1]
    rw [herr_eq, hsp_call]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWP.exists_elim fun e1 => ?_
    exact SepWP.weaken_pre (by sep_frame) (hnext sf e1 hpc_f hrun_f hsp_f hcs_f hmsp)

theorem hbMain_ret_wp {P : Program} {C : HbCliLayout} {lim : MallocngLimits}
    (hc : HbUserMainCode P C) (M : MallocngCoreIface P C.mallocng lim) (γ : GhostName)
    {sp_m v0 v1 v2 : BitVec 64} {lcRest blkRest : Nat} {e0 : BitVec 32}
    {s_main s_ref s : State} {Pre F : SepProp} {post : State → SepProp → Prop}
    (hsvc : P.svc = Syscall.standard) (hext : ∀ pc, P.externAt? pc = none)
    (hsp_m : sp_m = s_main.sp - 0xe0#64) (hsp_main_al : s_main.spAligned = true)
    (hpc : s.pc = C.std.userMainAddr + 0x94#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp_m)
    (hx28 : s.readReg64 .x28 = s_main.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s_main)
    (hmsp_ref : MallocngStatePreserved s_ref s)
    (hpre : Pre ⊢
      stackAt sp_m (261984 - 224) ∗
      memRegion sp_m 8 ∗
      ((sp_m + 0x08#64) ↦₆₄ v0) ∗ ((sp_m + 0x10#64) ↦₆₄ v1) ∗ ((sp_m + 0x18#64) ↦₆₄ v2) ∗
      stackAt (sp_m + 0x80#64) 96 ∗
      HbMainSavedRegs sp_m s_main ∗
      memRegion (sp_m + 0x98#64) 8 ∗
      M.Heap γ lcRest blkRest s ∗ (muslErrnoAddr s ↦₃₂ e0) ∗ F)
    (hnext : ∀ (s_ret : State) (e_ret : BitVec 32) (Pf : SepProp),
      s_ret.sp = s_main.sp →
      (s_ret.readReg32 .x0).truncate 8 = (s.readReg32 .x0).truncate 8 →
      CalleeSavedPreserved s_main s_ret → MallocngStatePreserved s_ref s_ret →
      (Pf ⊢ M.Heap γ lcRest blkRest s_ret ∗ (muslErrnoAddr s_ret ↦₃₂ e_ret) ∗
        stackAt s_ret.sp 261984 ∗ F) → post s_ret Pf) :
    SepWP P (s_main.readReg64 .lr) s Pre post := by
  cases hsp.symm
  have hsp_al : s.spAligned = true := by
    simp only [State.spAligned, hsp_m]; exact s_main.spAligned_sub 0xe0#64 hsp_main_al
  apply SepWP.weaken_pre hpre
  apply SepWP.with_keepsFrozen
  refine SepWP.of_nonVm hext hsvc ?_
  have hc_nv := (hc.withSvc nonVmSvc).rustMain
  unpack_hb_main_code hbRustMainReadScanChunks hc_nv
  dsimp only [HbMainSavedRegs]
  wp_steps
  refine SepWP.weaken_pre_frame
    (P' := stackAt s_main.sp 261984 ∗ M.Heap γ lcRest blkRest s ∗ (muslErrnoAddr s ↦₃₂ e0) ∗ F)
    (fun R hm => ?_) ?_
  · rw [sepConj_assoc]
    apply hbMainStack_repack s_main hsp_m v0 v1 v2
    dsimp only [HbMainSavedRegs]; sep_frame
  · refine SepWP.done ?_ ?_ (fun hvm hkf => ?_)
    · simp [wp_norm, arm64_norm]
    · simp [wp_norm, arm64_norm, hrun]
    · have hsp_eq : s.sp + 224#64 = s_main.sp := by rw [hsp_m]; bv_lin
      refine hnext _ e0 _
        (by simp only [wp_norm, arm64_norm]; try exact hsp_eq)
        (by simp [wp_norm, arm64_norm])
        (by simp [CalleeSavedPreserved.iff_regs, wp_norm, arm64_norm, hx28, hvregs])
        (MallocngStatePreserved.trans hmsp_ref ⟨rfl, rfl, rfl, rfl, hkf⟩) ?_
      simp only [muslErrnoAddr, wp_norm, arm64_norm]; try rw [hsp_eq]
      exact entails_mono_atom (vmHeapTransport M hvm) (hQ := by sep_frame)

theorem hbMain_deallocFrom84_wp {P : Program} {C : HbCliLayout} {lim : MallocngLimits}
    (hc : HbUserMainCode P C) (hcShims : HbShimsCode P C)
    (M : MallocngCoreIface P C.mallocng lim) (γ : GhostName)
    {sp_m vecPtr v0 v2 : BitVec 64} {cap lcRest blkRest : Nat} {e0 : BitVec 32}
    {s_main s_ref s : State} {Pre F : SepProp} {post : State → SepProp → Prop}
    (hsvc : P.svc = Syscall.standard) (hext : ∀ pc, P.externAt? pc = none)
    (hptr_nz : vecPtr ≠ 0#64)
    (hsp_m : sp_m = s_main.sp - 0xe0#64) (hsp_main_al : s_main.spAligned = true)
    (hpc : s.pc = C.std.userMainAddr + 0x84#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp_m)
    (hx28 : s.readReg64 .x28 = s_main.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s_main)
    (hmsp_ref : MallocngStatePreserved s_ref s)
    (hpre : Pre ⊢
      memRegion sp_m 8 ∗
      ((sp_m + 0x08#64) ↦₆₄ v0) ∗ ((sp_m + 0x10#64) ↦₆₄ vecPtr) ∗ ((sp_m + 0x18#64) ↦₆₄ v2) ∗
      M.Block γ vecPtr cap ∗ memRegion vecPtr cap ∗
      HbMainSavedRegs sp_m s_main ∗ memRegion (sp_m + 0x98#64) 8 ∗
      stackAt (sp_m + 0x80#64) 96 ∗ stackAt sp_m (261984 - 224) ∗
      M.Heap γ (lcRest + mallocngBlockCost cap) (blkRest + 1) s ∗
      (muslErrnoAddr s ↦₃₂ e0) ∗ F)
    (hnext : ∀ (s_ret : State) (e_ret : BitVec 32) (Pf : SepProp),
      s_ret.sp = s_main.sp →
      (s_ret.readReg32 .x0).truncate 8 = (s.readReg32 .x19).truncate 8 →
      CalleeSavedPreserved s_main s_ret → MallocngStatePreserved s_ref s_ret →
      (Pf ⊢ M.Heap γ lcRest blkRest s_ret ∗ (muslErrnoAddr s_ret ↦₃₂ e_ret) ∗
        stackAt s_ret.sp 261984 ∗ F) → post s_ret Pf) :
    SepWP P (s_main.readReg64 .lr) s Pre post := by
  cases hsp.symm
  have hsp_al : s.spAligned = true := by
    simp only [State.spAligned, hsp_m]; exact s_main.spAligned_sub 0xe0#64 hsp_main_al
  apply SepWP.weaken_pre hpre
  refine SepWP.seq_nonVm (mid := C.rustDeallocAddr) hext hsvc ?_
  have hc_nv := (hc.withSvc nonVmSvc).rustMain
  unpack_hb_main_code hbRustMainReadScanChunks hc_nv
  wp_steps
  conv in State.setPC _ _ => arg 2; rw [bv64_add_sub_cancel]
  refine SepWP.done rfl (by simp [wp_norm, arm64_norm, hrun]) (fun _hvm0 => ?_)
  have hf0 := hcShims.dealloc.fetch_at_zero
  have hf1 := hcShims.rdlDealloc.fetch_at_zero
  wp_step
  conv in State.setPC _ _ => arg 2; rw [bv64_add_sub_cancel]
  wp_step
  conv in State.setPC _ _ => arg 2; rw [bv64_add_sub_cancel]
  have hstk_split := stackAt_split_main s.sp MallocngStackBytes (261984 - 224 - MallocngStackBytes) (n := 261984 - 224)
  conv => arg 4; rw [hstk_split]
  refine call_free M γ (s0 := s) ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
      by simp [wp_norm, arm64_norm], fun a => by simp [wp_norm, arm64_norm]⟩ hptr_nz
    (lc := lcRest + mallocngBlockCost cap) (blk := blkRest + 1) (req := cap)
    (sp_call := s.sp) (ret_pc := C.std.userMainAddr + 0x90#64)
    (by sep_frame)
    (fun s1 e1 hpc1 hrun1 hsp1 hcs1 hmsp1 => ?_)
    (hpc := rfl) (hrun := by simp [wp_norm, arm64_norm, hrun])
    (hsp_call := by simp [wp_norm, arm64_norm])
    (herr0 := by simp [muslErrnoAddr, wp_norm, arm64_norm])
    (hsp_align := by simpa [State.spAligned, wp_norm, arm64_norm] using hsp_al)
    (hlr := wp_a) (hx0 := by simp [wp_norm, arm64_norm])
  rw [Nat.add_sub_cancel, Nat.add_sub_cancel]
  have hsp1_eq : s1.sp = s.sp := by simpa [wp_norm, arm64_norm] using hsp1
  have hx19_1 : (s1.readReg32 .x19).truncate 8 = (s.readReg32 .x19).truncate 8 := by
    have h19 := hcs1.readReg64_x19
    simp only [State.readReg32, Reg.x19] at h19 ⊢
    have h19' : s1.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) := by
      simpa [wp_norm, arm64_norm] using h19
    rw [h19']
  have hx28_1 : s1.readReg64 .x28 = s_main.readReg64 .x28 := by
    have h28 := hcs1.readReg64_x28
    have h28' : s1.readReg64 .x28 = s.readReg64 .x28 := by simpa [wp_norm, arm64_norm] using h28
    exact h28'.trans hx28
  have hvregs1 : calleeSavedVRegs s1 = calleeSavedVRegs s_main := by
    have hv := hcs1.vregs; simp only [wp_norm, arm64_norm] at hv; exact hv.trans hvregs
  have hmsp01 : MallocngStatePreserved s_ref s1 :=
    MallocngStatePreserved.trans hmsp_ref
      (MallocngStatePreserved.trans ⟨rfl, rfl, rfl, rfl, Memory.KeepsFrozen.refl s.mem⟩ hmsp1)
  refine SepWP.seq_nonVm (mid := C.std.userMainAddr + 0x94#64) hext hsvc ?_
  have hc_nv2 := (hc.withSvc nonVmSvc).rustMain
  unpack_hb_main_code hbRustMainReadScanChunks hc_nv2
  wp_steps
  refine SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun1]) (fun hvm2 => ?_)
  apply sepWP_mono_atom (vmHeapTransport M hvm2)
  exact hbMain_ret_wp hc M γ hsvc hext hsp_m hsp_main_al
    wp_a (by simp [wp_norm, arm64_norm, hrun1]) (by simp [wp_norm, arm64_norm, hsp1_eq])
    (by simp [wp_norm, arm64_norm, hx28_1]) (by simp [wp_norm, arm64_norm, hvregs1])
    (MallocngStatePreserved.trans hmsp01 ⟨rfl, rfl, rfl, rfl, Memory.KeepsFrozen.refl s1.mem⟩)
    (by rw [hstk_split]; simp [muslErrnoAddr, wp_norm, arm64_norm]; sep_frame)
    (fun s_ret e_ret Pf hsp_r hx0_r hcs_r hmsp_r hPf =>
      hnext s_ret e_ret Pf hsp_r
        (hx0_r.trans (by simpa [wp_norm, arm64_norm] using hx19_1))
        hcs_r hmsp_r hPf)

theorem hbMain_epilogue_wp {P : Program} {C : HbCliLayout} {lim : MallocngLimits}
    (hc : HbUserMainCode P C) (hcShims : HbShimsCode P C)
    (M : MallocngCoreIface P C.mallocng lim) (γ : GhostName)
    {sp_m vecPtr : BitVec 64} {cap lcRest blkRest : Nat} {bs : List (BitVec 8)} {e0 : BitVec 32}
    {s_main s : State} {Pre F : SepProp} {post : State → SepProp → Prop}
    (hsvc : P.svc = Syscall.standard := by rfl)
    (hext : ∀ pc, P.externAt? pc = none := by intro _; rfl)
    (hsp_m : sp_m = s_main.sp - 0xe0#64) (hsp_main_al : s_main.spAligned = true)
    (hpc : s.pc = C.std.userMainAddr + 0x78#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp_m)
    (hx28 : s.readReg64 .x28 = s_main.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s_main)
    (hpre : Pre ⊢
      HbByteVec M γ (sp_m + 0x08#64) cap vecPtr bs ∗
      memRegion sp_m 8 ∗
      HbMainSavedRegs sp_m s_main ∗
      memRegion (sp_m + 0x98#64) 8 ∗
      stackAt (sp_m + 0x80#64) 96 ∗
      stackAt sp_m (261984 - 224) ∗
      M.Heap γ (lcRest + hbByteVecCost cap) (blkRest + hbByteVecBlocks cap) s ∗
      (muslErrnoAddr s ↦₃₂ e0) ∗ F)
    (hnext : ∀ (s_ret : State) (e_ret : BitVec 32) (Pf : SepProp),
      s_ret.sp = s_main.sp →
      (s_ret.readReg32 .x0).truncate 8 = (s.readReg32 .x19).truncate 8 →
      CalleeSavedPreserved s_main s_ret → MallocngStatePreserved s s_ret →
      (Pf ⊢ M.Heap γ lcRest blkRest s_ret ∗ (muslErrnoAddr s_ret ↦₃₂ e_ret) ∗
        stackAt s_ret.sp 261984 ∗ F) → post s_ret Pf) :
    SepWP P (s_main.readReg64 .lr) s Pre post := by
  cases hsp.symm
  have hsp_al : s.spAligned = true := by
    simp only [State.spAligned, hsp_m]; exact s_main.spAligned_sub 0xe0#64 hsp_main_al
  apply SepWP.weaken_pre hpre
  rcases Nat.eq_zero_or_pos cap with rfl | hcap_pos
  · conv => arg 4; simp only [HbByteVec, HbByteVecBuf, hbByteVecCost, hbByteVecBlocks,
      ↓reduceIte, Nat.add_zero, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd,
      sepConj_assoc, sepConj_pull_pure]
    refine SepWP.pure_elim fun ⟨_, _⟩ => ?_
    refine SepWP.seq_nonVm (mid := C.std.userMainAddr + 0x94#64) hext hsvc ?_
    have hc_nv := (hc.withSvc nonVmSvc).rustMain
    unpack_hb_main_code hbRustMainReadScanChunks hc_nv
    wp_steps
    refine SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun]) (fun hvm1 => ?_)
    apply sepWP_mono_atom (vmHeapTransport M hvm1)
    exact hbMain_ret_wp hc M γ hsvc hext hsp_m hsp_main_al
      wp_a (by simp [wp_norm, arm64_norm, hrun]) (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hx28]) (by simp [wp_norm, arm64_norm, hvregs])
      ⟨rfl, rfl, rfl, rfl, Memory.KeepsFrozen.refl s.mem⟩
      (by simp [muslErrnoAddr, wp_norm, arm64_norm]; sep_frame)
      (fun s_ret e_ret Pf hsp_r hx0_r hcs_r hmsp_r hPf =>
        hnext s_ret e_ret Pf hsp_r (by simpa [wp_norm, arm64_norm] using hx0_r) hcs_r hmsp_r hPf)
  · have hcap_ne : cap ≠ 0 := by omega
    conv => arg 4; simp only [HbByteVec, HbByteVecBuf, hbByteVecCost, hbByteVecBlocks,
      hcap_ne, ↓reduceIte, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc, sepConj_pull_pure]
    refine SepWP.pure_elim fun ⟨hptr_nz, _, hptr_nw, hlen_le⟩ => ?_
    have hreg_merge : (vecPtr ↦ₛ bs) ∗ memRegion (vecPtr + BitVec.ofNat 64 bs.length) (cap - bs.length) ⊢
        memRegion vecPtr cap := by
      rw [memRegion_split_le vecPtr bs.length cap hlen_le (by omega)]
      exact sepConj_mono_left (pointsToBytes_entails_memRegion vecPtr bs)
    apply sepWP_mono_atom hreg_merge
    have hcap_bv_nz : BitVec.ofNat 64 cap ≠ 0#64 := by
      intro heq; have ht := congrArg BitVec.toNat heq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
      simp only [BitVec.toNat_ofNat] at ht; omega
    refine SepWP.seq_nonVm (mid := C.std.userMainAddr + 0x84#64) hext hsvc ?_
    have hc_nv := (hc.withSvc nonVmSvc).rustMain
    unpack_hb_main_code hbRustMainReadScanChunks hc_nv
    wp_steps; (try simp only [beq_iff_eq, hcap_bv_nz, ↓reduceIte])
    refine SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun]) (fun hvm1 => ?_)
    apply sepWP_mono_atom (vmHeapTransport M hvm1)
    exact hbMain_deallocFrom84_wp hc hcShims M γ hsvc hext hptr_nz hsp_m hsp_main_al
      wp_a (by simp [wp_norm, arm64_norm, hrun]) (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hx28]) (by simp [wp_norm, arm64_norm, hvregs])
      ⟨rfl, rfl, rfl, rfl, Memory.KeepsFrozen.refl s.mem⟩
      (by simp [muslErrnoAddr, wp_norm, arm64_norm]; sep_frame)
      (fun s_ret e_ret Pf hsp_r hx0_r hcs_r hmsp_r hPf =>
        hnext s_ret e_ret Pf hsp_r (by simpa [wp_norm, arm64_norm] using hx0_r) hcs_r hmsp_r hPf)

theorem hbMain_epilogue_from310_wp {P : Program} {C : HbCliLayout} {lim : MallocngLimits}
    (hc : HbUserMainCode P C) (hcShims : HbShimsCode P C)
    (M : MallocngCoreIface P C.mallocng lim) (γ : GhostName)
    {sp_m vecPtr : BitVec 64} {cap lcRest blkRest : Nat} {bs : List (BitVec 8)} {e0 : BitVec 32}
    {s_main s : State} {Pre F : SepProp} {post : State → SepProp → Prop}
    (hsvc : P.svc = Syscall.standard := by rfl)
    (hext : ∀ pc, P.externAt? pc = none := by intro _; rfl)
    (hsp_m : sp_m = s_main.sp - 0xe0#64) (hsp_main_al : s_main.spAligned = true)
    (hpc : s.pc = C.std.userMainAddr + 0x310#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp_m)
    (hx28 : s.readReg64 .x28 = s_main.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s_main)
    (hpre : Pre ⊢
      HbByteVec M γ (sp_m + 0x08#64) cap vecPtr bs ∗
      memRegion sp_m 8 ∗
      HbMainSavedRegs sp_m s_main ∗
      memRegion (sp_m + 0x98#64) 8 ∗
      stackAt (sp_m + 0x80#64) 96 ∗
      stackAt sp_m (261984 - 224) ∗
      M.Heap γ (lcRest + hbByteVecCost cap) (blkRest + hbByteVecBlocks cap) s ∗
      (muslErrnoAddr s ↦₃₂ e0) ∗ F)
    (hnext : ∀ (s_ret : State) (e_ret : BitVec 32) (Pf : SepProp),
      s_ret.sp = s_main.sp →
      (s_ret.readReg32 .x0).truncate 8 = 0#8 →
      CalleeSavedPreserved s_main s_ret → MallocngStatePreserved s s_ret →
      (Pf ⊢ M.Heap γ lcRest blkRest s_ret ∗ (muslErrnoAddr s_ret ↦₃₂ e_ret) ∗
        stackAt s_ret.sp 261984 ∗ F) → post s_ret Pf) :
    SepWP P (s_main.readReg64 .lr) s Pre post := by
  cases hsp.symm
  have hsp_al : s.spAligned = true := by
    simp only [State.spAligned, hsp_m]; exact s_main.spAligned_sub 0xe0#64 hsp_main_al
  apply SepWP.weaken_pre hpre
  rcases Nat.eq_zero_or_pos cap with rfl | hcap_pos
  · conv => arg 4; simp only [HbByteVec, HbByteVecBuf, hbByteVecCost, hbByteVecBlocks,
      ↓reduceIte, Nat.add_zero, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd,
      sepConj_assoc, sepConj_pull_pure]
    refine SepWP.pure_elim fun ⟨_, _⟩ => ?_
    refine SepWP.seq_nonVm (mid := C.std.userMainAddr + 0x94#64) hext hsvc ?_
    have hc_nv := (hc.withSvc nonVmSvc).rustMain
    unpack_hb_main_code hbRustMainReadScanChunks hc_nv
    wp_steps
    refine SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun]) (fun hvm1 => ?_)
    apply sepWP_mono_atom (vmHeapTransport M hvm1)
    exact hbMain_ret_wp hc M γ hsvc hext hsp_m hsp_main_al
      wp_a (by simp [wp_norm, arm64_norm, hrun]) (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hx28]) (by simp [wp_norm, arm64_norm, hvregs])
      ⟨rfl, rfl, rfl, rfl, Memory.KeepsFrozen.refl s.mem⟩
      (by simp [muslErrnoAddr, wp_norm, arm64_norm]; sep_frame)
      (fun s_ret e_ret Pf hsp_r hx0_r hcs_r hmsp_r hPf =>
        hnext s_ret e_ret Pf hsp_r (by simpa [wp_norm, arm64_norm] using hx0_r) hcs_r hmsp_r hPf)
  · have hcap_ne : cap ≠ 0 := by omega
    conv => arg 4; simp only [HbByteVec, HbByteVecBuf, hbByteVecCost, hbByteVecBlocks,
      hcap_ne, ↓reduceIte, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc, sepConj_pull_pure]
    refine SepWP.pure_elim fun ⟨hptr_nz, _, hptr_nw, hlen_le⟩ => ?_
    have hreg_merge : (vecPtr ↦ₛ bs) ∗ memRegion (vecPtr + BitVec.ofNat 64 bs.length) (cap - bs.length) ⊢
        memRegion vecPtr cap := by
      rw [memRegion_split_le vecPtr bs.length cap hlen_le (by omega)]
      exact sepConj_mono_left (pointsToBytes_entails_memRegion vecPtr bs)
    apply sepWP_mono_atom hreg_merge
    have hcap_bv_nz : BitVec.ofNat 64 cap ≠ 0#64 := by
      intro heq; have ht := congrArg BitVec.toNat heq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
      simp only [BitVec.toNat_ofNat] at ht; omega
    refine SepWP.seq_nonVm (mid := C.std.userMainAddr + 0x84#64) hext hsvc ?_
    have hc_nv := (hc.withSvc nonVmSvc).rustMain
    unpack_hb_main_code hbRustMainReadScanChunks hc_nv
    wp_steps; (try simp only [beq_iff_eq, hcap_bv_nz, not_false_eq_true, ↓reduceIte])
    refine SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun]) (fun hvm1 => ?_)
    apply sepWP_mono_atom (vmHeapTransport M hvm1)
    exact hbMain_deallocFrom84_wp hc hcShims M γ hsvc hext hptr_nz hsp_m hsp_main_al
      wp_a (by simp [wp_norm, arm64_norm, hrun]) (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hx28]) (by simp [wp_norm, arm64_norm, hvregs])
      ⟨rfl, rfl, rfl, rfl, Memory.KeepsFrozen.refl s.mem⟩
      (by simp [muslErrnoAddr, wp_norm, arm64_norm]; sep_frame)
      (fun s_ret e_ret Pf hsp_r hx0_r hcs_r hmsp_r hPf =>
        hnext s_ret e_ret Pf hsp_r (by simpa [wp_norm, arm64_norm] using hx0_r) hcs_r hmsp_r hPf)

end CaseStudies.Hashbrown.Proofs.StdCli
