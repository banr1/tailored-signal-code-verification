/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import CaseStudies.Hashbrown.Proofs.StdCli.Layout
public import ProofLib.SepLogic.WP
public import ProofLib.SepLogic.CFG
public import ProofLib.BV
public import ProofLib.AsciiNum

/-!
# Placement-Generic `core::fmt::write` and `<u64 as Display>::fmt` Base Infrastructure

Defines the symbolic instruction bundle (`HbFmtCode`), process-state preservation predicates
(`FmtPureStatePreserved`, `FmtIoStatePreserved`), decimal digit formatting and `DEC_DIGITS_LUT`
lookup lemmas, abstract writer interface (`HbFmtWriter`), and the specification and proof for
`Formatter::pad_integral::write_prefix` parameterized over `C : HbCliLayout`.
-/

set_option autoImplicit false

@[expose] public section

namespace CaseStudies.Hashbrown.Proofs.StdCli

open Arm64 Arm64.Process ProofLib ProofLib.StdStartup ProofLib.ProgramReflection
open CaseStudies.Hashbrown

/-! ## `.rodata` Format Template and Symbolic `HbFmtCode` Bundle -/

/-- 4-byte compact `fmt::Arguments` bytecode template for `println!("{v}")`:
    - `0xc0#8`: format next `Argument` with default `Formatter` options (`0x60000020#32`, width `0`),
    - `0x01#8, 0x0a#8`: 1-byte literal piece `"\n"`,
    - `0x00#8`: end of template. -/
def fmtValNlTemplateBytes : List (BitVec 8) :=
  [0xc0#8, 0x01#8, 0x0a#8, 0x00#8]

@[simp] theorem fmtValNlTemplateBytes_length : fmtValNlTemplateBytes.length = 4 := rfl

def padIntegralWritePrefixWords : List (BitVec 32) := [
  0xa9bd7bfd#32, 0xa90157f6#32, 0xa9024ff4#32, 0x910003fd#32,
  0xaa0403f3#32, 0xaa0303f4#32, 0xaa0103f5#32, 0x3100045f#32,
  0xaa0003f6#32, 0x54000160#32, 0xf94012a8#32, 0xaa1603e0#32,
  0x2a0203e1#32, 0xd63f0100#32, 0x360000c0#32, 0x52800020#32,
  0xa9424ff4#32, 0xa94157f6#32, 0xa8c37bfd#32, 0xd65f03c0#32,
  0xb4000134#32, 0xf9400ea3#32, 0xaa1603e0#32, 0xaa1403e1#32,
  0xaa1303e2#32, 0xa9424ff4#32, 0xa94157f6#32, 0xa8c37bfd#32,
  0xd61f0060#32, 0x2a1f03e0#32, 0xa9424ff4#32, 0xa94157f6#32,
  0xa8c37bfd#32, 0xd65f03c0#32
]

def coreFmtWriteWords : List (BitVec 32) := [
  0xd101c3ff#32, 0xa9027bfd#32, 0xa90367fa#32, 0xa9045ff8#32,
  0xa90557f6#32, 0xa9064ff4#32, 0x910083fd#32, 0xaa0303f3#32,
  0xaa0103f5#32, 0xaa0003f4#32, 0x370009b3#32, 0x39400048#32,
  0x34000ae8#32, 0xf9400eb8#32, 0x5280041a#32, 0xaa1f03f9#32,
  0x72ac001a#32, 0x1400000c#32, 0x8b191268#32, 0x910023e1#32,
  0xa9016bf5#32, 0xf90007f4#32, 0xa9402100#32, 0xd63f0100#32,
  0x370009a0#32, 0x91000739#32, 0x394002c8#32, 0xaa1603e2#32,
  0x340008e8#32, 0x91000456#32, 0x37380128#32, 0x2a0803f7#32,
  0xaa1403e0#32, 0xaa1603e1#32, 0xaa1703e2#32, 0xd63f0300#32,
  0x37000820#32, 0x8b1702d6#32, 0x17fffff4#32, 0x7102011f#32,
  0x54000180#32, 0x7103011f#32, 0x54fffd00#32, 0x37000248#32,
  0x52800409#32, 0x72ac0009#32, 0x36080248#32, 0x784026ca#32,
  0x36100248#32, 0x784026cb#32, 0x37180248#32, 0x14000012#32,
  0x78401056#32, 0x91000c57#32, 0xaa1403e0#32, 0xaa1703e1#32,
  0xaa1603e2#32, 0xd63f0300#32, 0x37000560#32, 0x8b1602f6#32,
  0x17ffffde#32, 0xb8401049#32, 0x91001456#32, 0x370ffe08#32,
  0xaa1f03ea#32, 0x3717fe08#32, 0xaa1f03eb#32, 0x36180048#32,
  0x784026d9#32, 0x372001c8#32, 0x36280068#32, 0x8b0b1268#32,
  0x7940110b#32, 0x8b191268#32, 0x910023e1#32, 0xb9001be9#32,
  0x79003bea#32, 0xa9402100#32, 0x79003feb#32, 0xa900d7f4#32,
  0xd63f0100#32, 0x3607f900#32, 0x14000013#32, 0x8b0a126a#32,
  0x7940114a#32, 0x372ffe48#32, 0x17fffff3#32, 0xd341fe68#32,
  0xf9400ea3#32, 0xaa1403e0#32, 0xaa0203e1#32, 0xaa0803e2#32,
  0xa9464ff4#32, 0xa94557f6#32, 0xa9445ff8#32, 0xa94367fa#32,
  0xa9427bfd#32, 0x9101c3ff#32, 0xd61f0060#32, 0x2a1f03e0#32,
  0x14000002#32, 0x52800020#32, 0xa9464ff4#32, 0xa94557f6#32,
  0xa9445ff8#32, 0xa94367fa#32, 0xa9427bfd#32, 0x9101c3ff#32,
  0xd65f03c0#32
]

def u64FmtInnerPrologueWords : List (BitVec 32) := [
  0xa9bf7bfd#32, 0x910003fd#32, 0xf10fa01f#32, 0xd503201f#32
]

def u64FmtInnerLutInstrs (C : HbCliLayout) : List Instr := [
  .adr false .x9 (C.decDigitsLutAddr - (C.u64FmtInnerAddr + 0x10#64))
]

def u64FmtInnerDigitsWords : List (BitVec 32) := [
  0x540006e3#32, 0xd28b296d#32, 0x5292cff1#32, 0xaa1f03eb#32,
  0xf2a710cd#32, 0xd100082c#32, 0x5284e20e#32, 0xf2d8bacd#32,
  0x52828f6f#32, 0x52800c90#32, 0xf2e68dad#32, 0x72a01311#32,
  0xaa0003f2#32, 0x8b0b0045#32, 0xd10010a8#32, 0xeb02011f#32,
  0x54000842#32, 0x9bcd7e48#32, 0xd1000ca7#32, 0x8b020185#32,
  0xeb0200ff#32, 0xd34bfd0a#32, 0x1b0ec943#32, 0x53023c68#32,
  0x1b0f7d08#32, 0x53117d04#32, 0x8b244528#32, 0x39400106#32,
  0x381fe0a6#32, 0x54000842#32, 0x8b0b0046#32, 0x39400507#32,
  0xd10008c8#32, 0xeb02011f#32, 0x381ff0a7#32, 0x540005e2#32,
  0x1b108c88#32, 0xd10004c3#32, 0xeb02007f#32, 0x8b282528#32,
  0x39400104#32, 0x38226984#32, 0x540005c2#32, 0x39400508#32,
  0x8b020183#32, 0xeb11025f#32, 0xd100116b#32, 0xd100118c#32,
  0xaa0a03f2#32, 0x39000468#32, 0x54fffb68#32, 0x8b0b0042#32,
  0xf100295f#32, 0x540000a2#32, 0x1400000f#32, 0xaa0003ea#32,
  0xf100281f#32, 0x54000183#32, 0x53023d48#32, 0x52828f6b#32,
  0xd1000842#32, 0x1b0b7d08#32, 0x52800c8b#32, 0x53117d08#32,
  0x1b0ba90a#32, 0x92403d4a#32, 0x786a792a#32, 0x7822682a#32,
  0xaa0803ea#32, 0xb40000a0#32, 0xb500008a#32, 0xaa0203e0#32,
  0xa8c17bfd#32, 0xd65f03c0#32, 0xd37f0d48#32, 0xd1000442#32,
  0x8b080128#32, 0x39400508#32, 0x38226828#32, 0xaa0203e0#32,
  0xa8c17bfd#32, 0xd65f03c0#32
]

def padIntegralPrologueWords : List (BitVec 32) := [
  0xd101c3ff#32, 0xa9017bfd#32, 0xa9026ffc#32, 0xa90367fa#32,
  0xa9045ff8#32, 0xa90557f6#32, 0xa9064ff4#32, 0x910043fd#32,
  0xb940101a#32, 0x528005aa#32, 0xaa0503f3#32, 0xaa0403fc#32,
  0xaa0303f6#32, 0xaa0003f5#32, 0x926b0348#32, 0xd3555749#32,
  0x7100011f#32, 0x52800568#32, 0x5a9f1108#32, 0x7100003f#32,
  0x9a9f1529#32, 0x1a8a1118#32, 0x8b05013b#32, 0x37b8033a#32,
  0xaa1f03f7#32, 0x79402ab4#32, 0xeb14037f#32, 0x54000e43#32,
  0xa94056b9#32, 0x2a1803e2#32, 0xaa1703e3#32, 0xaa1603e4#32,
  0xaa1903e0#32, 0xaa1503e1#32
]

def padIntegralCallPrefixInstrs (C : HbCliLayout) : List Instr := [
  .bl (C.padIntegralWritePrefixAddr - (C.padIntegralAddr + 0x88#64))
]

def padIntegralTailWords : List (BitVec 32) := [
  0x370016a0#32, 0xf9400ea3#32, 0xaa1903e0#32, 0xaa1c03e1#32,
  0xaa1303e2#32, 0xa9464ff4#32, 0xa94557f6#32, 0xa9445ff8#32,
  0xa94367fa#32, 0xa9426ffc#32, 0xa9417bfd#32, 0x9101c3ff#32,
  0xd61f0060#32
]

def u64DisplayPrologueWords : List (BitVec 32) := [
  0xd10143ff#32, 0xa9027bfd#32, 0xf9001bf5#32, 0xa9044ff4#32,
  0x910083fd#32, 0xf9400000#32, 0xaa0103f3#32, 0x910033e1#32,
  0x52800282#32, 0x52800294#32, 0x910033f5#32
]

def u64DisplayCallInnerInstrs (C : HbCliLayout) : List Instr := [
  .bl (C.u64FmtInnerAddr - (C.u64DisplayFmtAddr + 0x2c#64))
]

def u64DisplayMidWords : List (BitVec 32) := [
  0xcb000285#32, 0x8b0002a4#32, 0xaa1303e0#32, 0x52800021#32,
  0x52800022#32, 0xaa1f03e3#32
]

def u64DisplayCallPadInstrs (C : HbCliLayout) : List Instr := [
  .bl (C.padIntegralAddr - (C.u64DisplayFmtAddr + 0x48#64))
]

def u64DisplayEpilogueWords : List (BitVec 32) := [
  0xa9444ff4#32, 0xf9401bf5#32, 0xa9427bfd#32, 0x910143ff#32,
  0xd65f03c0#32
]

def hbFmtChunks (C : HbCliLayout) : List CodeChunk := [
  .words C.padIntegralWritePrefixAddr padIntegralWritePrefixWords,
  .words C.coreFmtWriteAddr coreFmtWriteWords,
  .words C.u64FmtInnerAddr u64FmtInnerPrologueWords,
  .instrs C.u64FmtInnerAddr 0x10 (u64FmtInnerLutInstrs C),
  .words (C.u64FmtInnerAddr + 0x14#64) u64FmtInnerDigitsWords,
  .words C.padIntegralAddr padIntegralPrologueWords,
  .instrs C.padIntegralAddr 0x88 (padIntegralCallPrefixInstrs C),
  .words (C.padIntegralAddr + 0x8c#64) padIntegralTailWords,
  .words C.u64DisplayFmtAddr u64DisplayPrologueWords,
  .instrs C.u64DisplayFmtAddr 0x2c (u64DisplayCallInnerInstrs C),
  .words (C.u64DisplayFmtAddr + 0x30#64) u64DisplayMidWords,
  .instrs C.u64DisplayFmtAddr 0x48 (u64DisplayCallPadInstrs C),
  .words (C.u64DisplayFmtAddr + 0x4c#64) u64DisplayEpilogueWords
]

/-- Symbolic code bundle for `core::fmt::write`, `<u64 as Display>::fmt`,
    `u64::__fmt_inner`, `Formatter::pad_integral`, and `Formatter::pad_integral::write_prefix`. -/
structure HbFmtCode (P : Program) (C : HbCliLayout) : Prop where
  padPrefix_words   : P.hasWords C.padIntegralWritePrefixAddr padIntegralWritePrefixWords
  coreWrite_words   : P.hasWords C.coreFmtWriteAddr coreFmtWriteWords
  u64InnerPrologue  : P.hasWords C.u64FmtInnerAddr u64FmtInnerPrologueWords
  u64InnerLut       : hasInstrs P (C.u64FmtInnerAddr + 0x10#64) (u64FmtInnerLutInstrs C)
  u64InnerDigits    : P.hasWords (C.u64FmtInnerAddr + 0x14#64) u64FmtInnerDigitsWords
  padIntPrologue    : P.hasWords C.padIntegralAddr padIntegralPrologueWords
  padIntCallPrefix  : hasInstrs P (C.padIntegralAddr + 0x88#64) (padIntegralCallPrefixInstrs C)
  padIntTail        : P.hasWords (C.padIntegralAddr + 0x8c#64) padIntegralTailWords
  u64Prologue       : P.hasWords C.u64DisplayFmtAddr u64DisplayPrologueWords
  u64CallInner      : hasInstrs P (C.u64DisplayFmtAddr + 0x2c#64) (u64DisplayCallInnerInstrs C)
  u64Mid_words      : P.hasWords (C.u64DisplayFmtAddr + 0x30#64) u64DisplayMidWords
  u64CallPad        : hasInstrs P (C.u64DisplayFmtAddr + 0x48#64) (u64DisplayCallPadInstrs C)
  u64Epilogue       : P.hasWords (C.u64DisplayFmtAddr + 0x4c#64) u64DisplayEpilogueWords

theorem HbFmtCode.withSvc {P : Program} {C : HbCliLayout} (svc : State → State)
    (h : HbFmtCode P C) : HbFmtCode (P.withSvc svc) C where
  padPrefix_words  := h.padPrefix_words
  coreWrite_words  := h.coreWrite_words
  u64InnerPrologue := h.u64InnerPrologue
  u64InnerLut      := fun i hi => by rw [Program.withSvc_fetch]; exact h.u64InnerLut i hi
  u64InnerDigits   := h.u64InnerDigits
  padIntPrologue   := h.padIntPrologue
  padIntCallPrefix := fun i hi => by rw [Program.withSvc_fetch]; exact h.padIntCallPrefix i hi
  padIntTail       := h.padIntTail
  u64Prologue      := h.u64Prologue
  u64CallInner     := fun i hi => by rw [Program.withSvc_fetch]; exact h.u64CallInner i hi
  u64Mid_words     := h.u64Mid_words
  u64CallPad       := fun i hi => by rw [Program.withSvc_fetch]; exact h.u64CallPad i hi
  u64Epilogue      := h.u64Epilogue

/-- `O(k log N)` boolean `WordTree` validator discharging `HbFmtCode P C`. -/
def checkHbFmtCode (C : HbCliLayout) (base : BitVec 64) (t : WordTree) : Bool :=
  (hbFmtChunks C).all (checkCodeChunk base t)

theorem hbFmtCode_of_wordTree {P : Program} {C : HbCliLayout} {t : WordTree} (n : Nat)
    (hcode : P.code = t.toBytes) (hwf : t.checkSize? = some n)
    (hstubs : P.stubs = [] := by rfl) (hsyms : P.symbols = [] := by rfl)
    (hext : ∀ sym, (P.externs sym).isNone = true := by intro _; rfl)
    (hovr : ∀ sym, (P.overrides sym).isNone = true := by intro _; rfl)
    (hok : checkHbFmtCode C P.base t = true) :
    HbFmtCode P C := by
  have hc : ∀ {c : CodeChunk}, checkCodeChunk P.base t c = true → c.holds P := by
    rintro (⟨a, ws⟩ | ⟨b, is⟩ | ⟨b, o, is⟩) h
    · simp only [checkCodeChunk, checkCleanupWordsAt, Bool.and_eq_true, decide_eq_true_eq] at h
      exact hasWords_of_wordTree n hcode hwf rfl h.1 hstubs hsyms h.2
    all_goals
      simp only [checkCodeChunk, checkCleanupInstrsAt, Bool.and_eq_true, beq_iff_eq,
        decide_eq_true_eq] at h
      exact hasInstrs_of_wordTree n hcode hwf h.1.1 h.1.2 hext hovr h.2
  unfold checkHbFmtCode hbFmtChunks at hok
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hok
  rcases hok with ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13⟩
  exact ⟨hc c1, hc c2, hc c3, hc c4, hc c5, hc c6, hc c7, hc c8, hc c9, hc c10, hc c11, hc c12, hc c13⟩

/-! ## Process-State Preservation -/

/-- Non-CPU process state fields preserved across pure user-space formatting steps. -/
def FmtPureStatePreserved (s0 sf : State) : Prop :=
  ProcessFieldsPreserved s0 sf ∧
  sf.oracle = s0.oracle ∧ sf.oracleIdx = s0.oracleIdx ∧ sf.symtab = s0.symtab

/-- Non-trace process state fields preserved across `stdout` formatting (`SYS_write(1, ...)`
    appends to `sf.trace` while leaving all other kernel/process fields unchanged). -/
def FmtIoStatePreserved (s0 sf : State) : Prop :=
  sf.fs = s0.fs ∧ sf.tpidrEl0 = s0.tpidrEl0 ∧
  sf.sigActions = s0.sigActions ∧ sf.brk = s0.brk ∧ sf.brkStart = s0.brkStart ∧
  sf.physMemAvail = s0.physMemAvail ∧ (∀ a, sf.mem.perm a = s0.mem.perm a) ∧
  sf.oracle = s0.oracle ∧ sf.oracleIdx = s0.oracleIdx ∧ sf.symtab = s0.symtab

theorem FmtPureStatePreserved.refl (s : State) : FmtPureStatePreserved s s :=
  ⟨ProcessFieldsPreserved.refl s, rfl, rfl, rfl⟩

theorem FmtPureStatePreserved.trans {s0 s1 s2 : State}
    (h01 : FmtPureStatePreserved s0 s1) (h12 : FmtPureStatePreserved s1 s2) :
    FmtPureStatePreserved s0 s2 :=
  ⟨ProcessFieldsPreserved.trans h01.1 h12.1,
   h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1, h12.2.2.2.trans h01.2.2.2⟩

theorem FmtPureStatePreserved.toIo {s0 sf : State} (h : FmtPureStatePreserved s0 sf) :
    FmtIoStatePreserved s0 sf :=
  ⟨h.1.1, h.1.2.2.1, h.1.2.2.2.1, h.1.2.2.2.2.1, h.1.2.2.2.2.2.1,
   h.1.2.2.2.2.2.2.1, h.1.2.2.2.2.2.2.2, h.2.1, h.2.2.1, h.2.2.2⟩

theorem FmtIoStatePreserved.refl (s : State) : FmtIoStatePreserved s s :=
  (FmtPureStatePreserved.refl s).toIo

theorem FmtIoStatePreserved.trans {s0 s1 s2 : State}
    (h01 : FmtIoStatePreserved s0 s1) (h12 : FmtIoStatePreserved s1 s2) :
    FmtIoStatePreserved s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1,
   h12.2.2.2.1.trans h01.2.2.2.1, h12.2.2.2.2.1.trans h01.2.2.2.2.1,
   h12.2.2.2.2.2.1.trans h01.2.2.2.2.2.1,
   fun a => (h12.2.2.2.2.2.2.1 a).trans (h01.2.2.2.2.2.2.1 a),
   h12.2.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.2.1,
   h12.2.2.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.2.2.1,
   h12.2.2.2.2.2.2.2.2.2.trans h01.2.2.2.2.2.2.2.2.2⟩

def CpuAuxPreserved (s0 sf : State) : Prop :=
  sf.tpidrEl0 = s0.tpidrEl0 ∧ sf.sigActions = s0.sigActions ∧
  sf.oracle = s0.oracle ∧ sf.symtab = s0.symtab

theorem CpuAuxPreserved.refl (s : State) : CpuAuxPreserved s s :=
  ⟨rfl, rfl, rfl, rfl⟩

@[local simp] theorem cpuAux_writeReg64 (s0 s : State) (r : Reg) (v : BitVec 64) :
    CpuAuxPreserved s0 (s.writeReg64 r v) ↔ CpuAuxPreserved s0 s := by
  cases r <;> simp [State.writeReg64, CpuAuxPreserved]

@[local simp] theorem cpuAux_writeReg32 (s0 s : State) (r : Reg) (v : BitVec 32) :
    CpuAuxPreserved s0 (s.writeReg32 r v) ↔ CpuAuxPreserved s0 s := by
  simp [State.writeReg32]

@[local simp] theorem cpuAux_writeReg (s0 s : State) (w : RegWidth) (r : Reg) (v : BitVec 64) :
    CpuAuxPreserved s0 (s.writeReg w r v) ↔ CpuAuxPreserved s0 s := by
  cases w <;> simp [State.writeReg]

@[local simp] theorem cpuAux_setPState (s0 s : State) (p : PState) :
    CpuAuxPreserved s0 (s.setPState p) ↔ CpuAuxPreserved s0 s := Iff.rfl

@[local simp] theorem cpuAux_advancePC (s0 s : State) :
    CpuAuxPreserved s0 s.advancePC ↔ CpuAuxPreserved s0 s := Iff.rfl

@[local simp] theorem cpuAux_setPC (s0 s : State) (pc : BitVec 64) :
    CpuAuxPreserved s0 (s.setPC pc) ↔ CpuAuxPreserved s0 s := Iff.rfl

@[local simp] theorem cpuAux_setMem (s0 s : State) (m : Memory) :
    CpuAuxPreserved s0 (s.setMem m) ↔ CpuAuxPreserved s0 s := Iff.rfl

private theorem fmtPure_of_nonSyscall_cpuAux {s0 sf : State}
    (hn : ProofLib.NonSyscallPreserved s0 sf) (hc : CpuAuxPreserved s0 sf) :
    FmtPureStatePreserved s0 sf :=
  ⟨⟨hn.2.2.2.2.2.2, hn.1, hc.1, hc.2.1, hn.2.2.1, hn.2.2.2.1, hn.2.2.2.2.1,
    fun a => congrFun hn.2.1 a⟩,
   hc.2.2.1, hn.2.2.2.2.2.1.1, hc.2.2.2⟩

private theorem steps_lift_pure_fmt {P : Program} (hext : ∀ pc, P.externAt? pc = none)
    {sa sf : State} (hsteps : Steps (P.withSvc noSyscalls) sa sf) (hrun_f : sf.status = .Running) :
    Steps P sa sf ∧ ProofLib.NonSyscallPreserved sa sf := by
  induction hsteps with
  | refl _ => exact ⟨Steps.refl _, ProofLib.NonSyscallPreserved.refl _⟩
  | @step s1 s2 _ h1 hrest ih =>
    have hrun2 : s2.status = .Running := by
      cases hrest with
      | refl => exact hrun_f
      | step hs2 _ => exact hs2.running_of_step
    cases h1 with
    | halt_unmapped _ _ _ => cases hrun2
    | extern _ hex _ _ => rw [externAt?_withSvc, hext] at hex; cases hex
    | extern_fault _ hex _ => rw [externAt?_withSvc, hext] at hex; cases hex
    | @exec inst hrun1 hfm =>
      have hfm' : P.fetchMem s1.mem s1.pc = some inst := hfm
      have hnot_svc0 : inst.isSvc0 = false := by
        cases ht : inst.isSvc0 with
        | false => rfl
        | true =>
          cases inst with
          | system isHalt imm =>
            cases isHalt with
            | true => simp [Instr.isSvc0] at ht
            | false =>
              simp only [Instr.isSvc0, Bool.not_false, Bool.true_and, beq_iff_eq] at ht
              subst ht
              simp [Program.evalInst, Program.withSvc, execInstWithSvc_svc0, noSyscalls,
                State.setStatus] at hrun2
          | _ => simp [Instr.isSvc0] at ht
      have heval_no : (P.withSvc noSyscalls).evalInst inst s1 = execInst inst s1 :=
        evalInst_eq_execInst_of_not_isSvc0 hnot_svc0 s1
      have heval_p : P.evalInst inst s1 = execInst inst s1 :=
        evalInst_eq_execInst_of_not_isSvc0 hnot_svc0 s1
      have hstep_p : Step P s1 ((P.withSvc noSyscalls).evalInst inst s1) := by
        rw [heval_no, ← heval_p]
        exact Step.exec hrun1 hfm'
      have hnsp1 : ProofLib.NonSyscallPreserved s1 ((P.withSvc noSyscalls).evalInst inst s1) := by
        rw [heval_no]
        exact ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hnot_svc0 s1
      obtain ⟨hsteps_rest, hnsp_rest⟩ := ih hrun_f
      exact ⟨Steps.step hstep_p hsteps_rest, hnsp1.trans hnsp_rest⟩

/-- Execute a pure user-space `SepWP` segment under `P.withSvc noSyscalls` to `mid_pc`,
    automatically upgrading `CpuAuxPreserved` into full `FmtPureStatePreserved` (including
    `mem.perm`, `trace`, `fs`, `brk`, `physMemAvail`) before continuing on `P`. -/
theorem SepWP.seq_noSyscalls {P : Program} {mid_pc target_pc : BitVec 64} {s0 : State}
    {Pre : SepProp} {Q : State → SepProp → Prop} {post : State → SepProp → Prop}
    {oom : State → SepProp}
    (hext : ∀ pc, P.externAt? pc = none)
    (hseg : SepWP (P.withSvc noSyscalls) mid_pc s0 Pre
      (fun sm Pm => CpuAuxPreserved s0 sm ∧ Q sm Pm))
    (hcont : ∀ sm Pm, sm.pc = mid_pc → sm.status = .Running →
      FmtPureStatePreserved s0 sm → Q sm Pm →
      SepWP P target_pc sm Pm post oom) :
    SepWP P target_pc s0 Pre post oom := by
  apply SepWP.of_reaches_pc
  intro R hm hL
  have hL' : (P.withSvc noSyscalls).CodeLoaded s0.mem := hL.of_base_code rfl rfl
  obtain ⟨sm, hsteps1, ⟨hpc_m, hrun_m, Pm, hmm, haux, hQ⟩ | ⟨_, hoom⟩⟩ :=
    SepWP.to_reaches_pc hseg hm hL'
  · obtain ⟨hsteps1_P, hnsp⟩ := steps_lift_pure_fmt hext hsteps1 hrun_m
    have hpure := fmtPure_of_nonSyscall_cpuAux hnsp haux
    obtain ⟨sf, hsteps2, hout2⟩ :=
      SepWP.to_reaches_pc (hcont sm Pm hpc_m hrun_m hpure hQ) hmm (hsteps1_P.codeLoaded hL)
    exact ⟨sf, hsteps1_P.trans hsteps2, hout2⟩
  · exact False.elim (not_satisfies_false_sepConj hoom)

/-! ## Decimal Digit Formatting and `DEC_DIGITS_LUT` Lemmas -/

/-- ASCII decimal byte `'0' + d` (`0x30 + d`). -/
@[inline] def decDigitByte (d : Nat) : BitVec 8 :=
  BitVec.ofNat 8 (0x30 + d)

theorem formatDecimal_of_lt_10 {n : Nat} (hn : n < 10) :
    formatDecimalNat n = [decDigitByte n] :=
  ProofLib.AsciiNum.formatDecimalNat_of_lt_10 hn

theorem formatDecimal_of_ge_10 {n : Nat} (hn : 10 ≤ n) :
    formatDecimalNat n = formatDecimalNat (n / 10) ++ [decDigitByte (n % 10)] :=
  ProofLib.AsciiNum.formatDecimalNat_of_ge_10 hn

theorem formatDecimal_two_digits {n : Nat} (hlo : 10 ≤ n) (hhi : n < 100) :
    formatDecimalNat n = [decDigitByte (n / 10), decDigitByte (n % 10)] :=
  ProofLib.AsciiNum.formatDecimalNat_two_digits hlo hhi

theorem formatDecimal_three_digits {n : Nat} (hlo : 100 ≤ n) (hhi : n < 1000) :
    formatDecimalNat n =
      [decDigitByte (n / 100), decDigitByte ((n % 100) / 10), decDigitByte (n % 10)] :=
  ProofLib.AsciiNum.formatDecimalNat_three_digits hlo hhi

/-- Zero-padded 4-digit decimal encoding of `r < 10000`. -/
def fourDecDigits (r : Nat) : List (BitVec 8) :=
  [decDigitByte ((r / 100) / 10), decDigitByte ((r / 100) % 10),
   decDigitByte ((r % 100) / 10), decDigitByte ((r % 100) % 10)]

@[simp] theorem fourDecDigits_length (r : Nat) : (fourDecDigits r).length = 4 := rfl

theorem formatDecimal_div_10000 {n : Nat} (hn : 10000 ≤ n) :
    formatDecimalNat n = formatDecimalNat (n / 10000) ++ fourDecDigits (n % 10000) :=
  ProofLib.AsciiNum.formatDecimalNat_div_10000 hn

theorem formatDecimal_of_1000_lt_10000 {n : Nat} (hlo : 1000 ≤ n) (hhi : n < 10000) :
    formatDecimalNat n = fourDecDigits n :=
  ProofLib.AsciiNum.formatDecimalNat_of_1000_lt_10000 hlo hhi

theorem formatDecimal_mem_ascii {n : Nat} {b : BitVec 8} (hb : b ∈ formatDecimalNat n) :
    0x30 ≤ b.toNat ∧ b.toNat ≤ 0x39 :=
  ProofLib.AsciiNum.formatDecimalNat_mem_ascii hb

theorem formatDecimal_not_mem_nl (n : Nat) : 0x0a#8 ∉ formatDecimalNat n :=
  ProofLib.AsciiNum.formatDecimalNat_not_mem_nl n

theorem formatDecimal_length_bounds {n : Nat} (hn : n < 2 ^ 64) :
    1 ≤ (formatDecimalNat n).length ∧ (formatDecimalNat n).length ≤ 20 :=
  ProofLib.AsciiNum.formatDecimalNat_length_bounds hn

/-- Fixed-point reciprocal multiplication identity for `m / 100` on `m < 10000`. -/
theorem magic_div_100 {m : Nat} (hm : m < 10000) :
    ((m / 4) * 5243) / 131072 = m / 100 := by
  omega

/-- Fixed-point reciprocal multiplication identity for `x / 10000` on `x < 2 ^ 64`
    (`0x346dc5d63886594b / 2 ^ 75`). -/
theorem magic_div_10000 {x : Nat} (hx : x < 2 ^ 64) :
    (x * 3777893186295716171) / 37778931862957161709568 = x / 10000 := by
  omega

private theorem decDigitsLutBytes_fin_even :
    ∀ j : Fin 100, decDigitsLutBytes.getD (2 * j.val) 0#8 = decDigitByte (j.val / 10) := by
  decide

private theorem decDigitsLutBytes_fin_odd :
    ∀ j : Fin 100, decDigitsLutBytes.getD (2 * j.val + 1) 0#8 = decDigitByte (j.val % 10) := by
  decide

theorem decDigitsLutBytes_getD_even {i : Nat} (hi : i < 100) :
    decDigitsLutBytes.getD (2 * i) 0#8 = decDigitByte (i / 10) :=
  decDigitsLutBytes_fin_even ⟨i, hi⟩

theorem decDigitsLutBytes_getD_odd {i : Nat} (hi : i < 100) :
    decDigitsLutBytes.getD (2 * i + 1) 0#8 = decDigitByte (i % 10) :=
  decDigitsLutBytes_fin_odd ⟨i, hi⟩

theorem decDigitsLut_focus16 (lut : BitVec 64) {i : Nat} (hi : i < 100) :
    (lut ↦ᵣ decDigitsLutBytes) =
      ((lut + BitVec.ofNat 64 (2 * i)) ↦₁₆ᵣ
        pack16 (decDigitByte (i / 10)) (decDigitByte (i % 10))) ∗
      ((lut ↦ᵣ decDigitsLutBytes.take (2 * i)) ∗
        ((lut + BitVec.ofNat 64 (2 * i + 2)) ↦ᵣ decDigitsLutBytes.drop (2 * i + 2))) := by
  have hlen : 2 * i + 2 ≤ decDigitsLutBytes.length := by
    rw [decDigitsLutBytes_length]; omega
  have hsplit := pointsToBytesRO_split3 lut decDigitsLutBytes (2 * i) 2 hlen
  have h16 := pointsToBytesRO_take2_eq_pointsTo16RO (lut + BitVec.ofNat 64 (2 * i))
    decDigitsLutBytes (2 * i) hlen
  rw [decDigitsLutBytes_getD_even hi, decDigitsLutBytes_getD_odd hi] at h16
  rw [h16] at hsplit
  exact hsplit

theorem decDigitsLut_focus8_pair (lut : BitVec 64) {i : Nat} (hi : i < 100) :
    (lut ↦ᵣ decDigitsLutBytes) =
      (((lut + BitVec.ofNat 64 (2 * i)) ↦₈ᵣ decDigitByte (i / 10)) ∗
       ((lut + BitVec.ofNat 64 (2 * i) + 1#64) ↦₈ᵣ decDigitByte (i % 10))) ∗
      ((lut ↦ᵣ decDigitsLutBytes.take (2 * i)) ∗
        ((lut + BitVec.ofNat 64 (2 * i + 2)) ↦ᵣ decDigitsLutBytes.drop (2 * i + 2))) := by
  have h1 := pointsToBytesRO_append (lut + BitVec.ofNat 64 (2 * i))
    [decDigitByte (i / 10)] [decDigitByte (i % 10)]
  dsimp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil] at h1
  rw [decDigitsLut_focus16 lut hi]
  unfold pack16
  rw [← pointsToBytesRO2_eq_pointsTo16RO, h1, pointsToBytesRO_singleton, pointsToBytesRO_singleton]

theorem decDigitsLut_focus8_odd (lut : BitVec 64) {i : Nat} (hi : i < 10) :
    (lut ↦ᵣ decDigitsLutBytes) =
      ((lut + BitVec.ofNat 64 (2 * i + 1)) ↦₈ᵣ decDigitByte i) ∗
      ((lut ↦ᵣ decDigitsLutBytes.take (2 * i + 1)) ∗
        ((lut + BitVec.ofNat 64 (2 * i + 2)) ↦ᵣ decDigitsLutBytes.drop (2 * i + 2))) := by
  have hlen : (2 * i + 1) + 1 ≤ decDigitsLutBytes.length := by
    rw [decDigitsLutBytes_length]; omega
  have hsplit := pointsToBytesRO_split3 lut decDigitsLutBytes (2 * i + 1) 1 hlen
  have h8 := pointsToBytesRO_take1_eq_pointsTo8RO (lut + BitVec.ofNat 64 (2 * i + 1))
    decDigitsLutBytes (2 * i + 1) (by rw [decDigitsLutBytes_length]; omega)
  rw [decDigitsLutBytes_getD_odd (by omega), show i % 10 = i by omega] at h8
  rw [h8] at hsplit
  exact hsplit

/-! ## Abstract Writer Interface (`HbFmtWriter`) and `pad_integral::write_prefix` -/

theorem SepWP.done {P : Program} {target_pc : BitVec 64} {s : State} {Pre : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = target_pc) (hrun : s.status = .Running) (hpost : post s Pre) :
    SepWP P target_pc s Pre post oom :=
  SepWP.of_reaches_pc fun _ hm _ => ⟨s, .refl s, Or.inl ⟨hpc, hrun, Pre, hm, hpost⟩⟩

/-- Abstract writer contract for `Adapter<StdoutLock>::write_str` (`C.adapterWriteStrAddr`),
    supporting both:
    1. Mutable stack byte slices `slicePtr ↦ₛ bs` (`1 ≤ bs.length ≤ 20`, `0x0a#8 ∉ bs`, emitted by
       `<u64 as Display>::fmt`), and
    2. Read-only `.rodata` newline slices `slicePtr ↦ᵣ bs` (`bs = [0x0a#8]`, emitted by
       `core::fmt::write` on `fmtValNlTemplateBytes`). -/
structure HbFmtWriter (P : Program) (C : HbCliLayout) (writerPtr : BitVec 64)
    (writeStackBytes : Nat) (W : List (BitVec 8) → State → SepProp) : Prop where
  stack_lo : 0x70 ≤ writeStackBytes := by decide
  stack_le : writeStackBytes ≤ 2 ^ 32
  pure_transport : ∀ (emitted : List (BitVec 8)) {s1 s2 : State},
    FmtPureStatePreserved s1 s2 → W emitted s1 ⊢ W emitted s2
  write_str_owned : ∀ (emitted bs : List (BitVec 8)) (slicePtr : BitVec 64),
    1 ≤ bs.length → bs.length ≤ 20 → 0x0a#8 ∉ bs →
    slicePtr ≠ 0#64 → slicePtr.toNat + bs.length + 8 ≤ 2 ^ 64 →
    subroutine_ok P C.adapterWriteStrAddr
      ({ pre := fun (_ : Unit) s0 =>
           ⌜s0.readReg64 .x0 = writerPtr ∧
             s0.readReg64 .x1 = slicePtr ∧
             s0.readReg64 .x2 = BitVec.ofNat 64 bs.length⌝ ∗
           W emitted s0 ∗
           (slicePtr ↦ₛ bs) ∗
           stackFrameAt s0.sp writeStackBytes
         post := fun _ s0 sf =>
           ⌜sf.readReg64 .x0 = 0#64 ∧ FmtIoStatePreserved s0 sf⌝ ∗
           W (emitted ++ bs) sf ∗
           (slicePtr ↦ₛ bs) ∗
           stackFrameAt s0.sp writeStackBytes } : Spec Unit)
  write_str_ro : ∀ (emitted bs : List (BitVec 8)) (slicePtr : BitVec 64),
    bs = [0x0a#8] →
    slicePtr ≠ 0#64 → slicePtr.toNat + bs.length + 8 ≤ Arm64.USER_VA_LIMIT →
    subroutine_ok P C.adapterWriteStrAddr
      ({ pre := fun (_ : Unit) s0 =>
           ⌜s0.readReg64 .x0 = writerPtr ∧
             s0.readReg64 .x1 = slicePtr ∧
             s0.readReg64 .x2 = BitVec.ofNat 64 bs.length⌝ ∗
           W emitted s0 ∗
           (slicePtr ↦ᵣ bs) ∗
           stackFrameAt s0.sp writeStackBytes
         post := fun _ s0 sf =>
           ⌜sf.readReg64 .x0 = 0#64 ∧ FmtIoStatePreserved s0 sf⌝ ∗
           W (emitted ++ bs) sf ∗
           (slicePtr ↦ᵣ bs) ∗
           stackFrameAt s0.sp writeStackBytes } : Spec Unit)

/-- Specification for `Formatter::pad_integral::write_prefix` on the no-sign, no-prefix fast path
    (`w2 = 0xffffffff#32` (`CHAR_NONE`), `x3 = 0#64` (empty prefix)). -/
def padIntegralWritePrefixNoneSpec : Spec Unit where
  pre := fun _ s0 =>
    ⌜s0.readReg32 .x2 = 0xffffffff#32 ∧ s0.readReg64 .x3 = 0#64⌝ ∗
    stackFrameAt s0.sp 0x30
  post := fun _ s0 sf =>
    ⌜sf.readReg64 .x0 = 0#64 ∧ FmtPureStatePreserved s0 sf⌝ ∗
    stackFrameAt s0.sp 0x30
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

theorem cells_sub_one_entails {sp : BitVec 64} (a : Nat) {v : BitVec 64}
    (ha : 8 ≤ a := by decide) :
    ((sp - BitVec.ofNat 64 a) ↦₆₄ v) ⊢ cells (sp - BitVec.ofNat 64 a) 1 := by
  simpa only [sepConj_emp] using cells_sub_succ_entails a 1 (Entails.refl emp) (by decide) ha

theorem padIntegralWritePrefix_none_wp {P : Program} {C : HbCliLayout}
    {target_pc ret_pc sp0 : BitVec 64} {s : State} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : P.hasWords C.padIntegralWritePrefixAddr padIntegralWritePrefixWords)
    (hext : ∀ pc, P.externAt? pc = none)
    (hpc : s.pc = C.padIntegralWritePrefixAddr) (hrun : s.status = .Running)
    (hsp : s.sp = sp0) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hw2 : s.readReg32 .x2 = 0xffffffff#32)
    (hx3 : s.readReg64 .x3 = 0#64)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 = 0#64 → FmtPureStatePreserved s sf →
      SepWP P target_pc sf (stackFrameAt sp0 0x30 ∗ F) post oom) :
    SepWP P target_pc s (stackFrameAt sp0 0x30 ∗ F) post oom := by
  subst hsp
  refine SepWP.seq_noSyscalls (mid_pc := ret_pc)
    (Q := fun sm Pm => (Pm ⊢ stackFrameAt s.sp 0x30 ∗ F) ∧
      sm.sp = s.sp ∧ CalleeSavedPreserved s sm ∧ sm.readReg64 .x0 = 0#64)
    hext ?_ (fun sf Pf hpc_f hrun_f hpure ⟨hent, hsp_f, hcs_f, hx0_f⟩ =>
      SepWP.weaken_pre hent (hnext sf hpc_f hrun_f hsp_f hcs_f hx0_f hpure))
  have hcode : (P.withSvc noSyscalls).hasCode C.padIntegralWritePrefixAddr
      padIntegralWritePrefixWords := hc
  have hw2' : BitVec.truncate 32 (s.readReg64 (.gpr 2#5)) = 0xffffffff#32 := hw2
  have hx3' : s.readReg64 (.gpr 3#5) = 0#64 := hx3
  have hlr' : s.readReg64 (.gpr 30#5) = ret_pc := hlr
  conv => arg 4; rw [← stackAt_eq_stackFrameAt s.sp 48, stackAt_eq_cells s.sp 6]
          simp (disch := decide) only [Nat.reduceMul, ProofLib.cells_sub_succ, Nat.reduceSub,
            ProofLib.cells_zero, sepConj_emp, sepExists_sepConj_right, sepExists_sepConj_left]
  iterate 6 (apply SepWP.exists_elim; intro _)
  wp_steps; wp_steps; wp_steps
  refine SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun])
    ⟨by simp [CpuAuxPreserved.refl],
     by apply sepConj_mono_left
        rw [← stackAt_eq_stackFrameAt s.sp 48, stackAt_eq_cells s.sp 6]
        simp only [Nat.reduceMul]
        iterate 5 (refine cells_sub_succ_entails _ _ ?_; simp only [Nat.reduceSub])
        exact cells_sub_one_entails 8,
     by simp (config := { decide := true }) only [wp_norm, arm64_norm, bv_lin_norm],
     by simp [CalleeSavedPreserved.iff_regs, wp_norm, arm64_norm, *],
     by simp (config := { decide := true }) only [wp_norm, arm64_norm]⟩

theorem padIntegralWritePrefix_none_ok {P : Program} {C : HbCliLayout}
    (hc : P.hasWords C.padIntegralWritePrefixAddr padIntegralWritePrefixWords)
    (hext : ∀ pc, P.externAt? pc = none) :
    subroutine_ok P C.padIntegralWritePrefixAddr padIntegralWritePrefixNoneSpec := by
  refine subroutine_ok_of_sepWP_init fun _ R s0 hpc hrun hpre hsp => ?_
  dsimp only [padIntegralWritePrefixNoneSpec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hw2, hx3⟩, hmem⟩ := hpre
  refine ⟨stackFrameAt s0.sp 0x30 ∗ emp, by simpa [sepConj_emp] using hmem, ?_⟩
  refine padIntegralWritePrefix_none_wp hc hext hpc hrun rfl hsp rfl hw2 hx3
    fun sf hpc_f hrun_f hsp_f hcs_f hx0_f hpure => ?_
  refine SepWP.done hpc_f hrun_f ⟨fun hm => ?_, hsp_f, hcs_f⟩
  rw [sepConj_emp] at hm
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨hx0_f, hpure⟩, hm⟩

end CaseStudies.Hashbrown.Proofs.StdCli
