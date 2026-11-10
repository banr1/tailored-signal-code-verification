/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.BV.Bits
public import ProofLib.Exec
public import ProofLib.Invariant
public import ProofLib.ProgramReflection
public import ProofLib.ObjectLoad
public meta import Lean
public meta import ProofLib.ProgramReflection
import Arm64.Trusted.ISA.Eval
import Arm64.Trusted.Spec.SepLogic

/-!
# Opcode Exclusion Infrastructure

Predicates, decoder characterizations, state-preservation lemmas, and reflective whole-code
checkers (`Program.allInstrs`, `WordTree.allInstrs`, and the `prove_all_instrs` tactic) for
proving instruction-exclusion invariants such as the absence of `SVC` or `MSR TPIDR_EL0` without
unfolding internal `Arm64.decode` branches.
-/

@[expose] public section

namespace Arm64

/-! ## Instruction and Word Predicates -/

/-- AArch64 15-bit system-register encoding `op0:op1:CRn:CRm:op2` (`0b11_011_1101_0000_010`)
    for `TPIDR_EL0`. -/
abbrev sysregTpidrEl0 : BitVec 15 := 0x5e82#15

/-- Whether `inst` is a supervisor call `SVC #imm16`. -/
def Instr.isSvc (inst : Instr) : Bool := by
  cases inst
  case system isHalt _ => exact !isHalt
  all_goals exact false

/-- Whether `inst` is `SVC #0`. -/
def Instr.isSvc0 (inst : Instr) : Bool := by
  cases inst
  case system isHalt imm => exact !isHalt && (imm == 0#16)
  all_goals exact false

/-- Whether `inst` is a software breakpoint `BRK #imm16`. -/
def Instr.isBrk (inst : Instr) : Bool := by
  cases inst
  case system isHalt _ => exact isHalt
  all_goals exact false

/-- Whether `inst` is any system-register write `MSR <sysreg>, Xt`. -/
def Instr.isMsr (inst : Instr) : Bool := by
  cases inst
  case sysReg isRead _ _ => exact !isRead
  all_goals exact false

/-- Whether `inst` writes the specific system register `target` (`MSR <target>, Xt`). -/
def Instr.isMsrSysreg (target : BitVec 15) (inst : Instr) : Bool := by
  cases inst
  case sysReg isRead sr _ => exact !isRead && (sr == target)
  all_goals exact false

/-- Whether `inst` writes `TPIDR_EL0` (`MSR TPIDR_EL0, Xt`). -/
def Instr.isMsrTpidrEl0 (inst : Instr) : Bool :=
  inst.isMsrSysreg sysregTpidrEl0

/-- Whether 32-bit machine word `w` is an `SVC #imm16` encoding (`11010100_000_imm16_00001`). -/
def isSvcWord (w : BitVec 32) : Bool :=
  (w &&& 0xffe0001f#32) == 0xd4000001#32

/-- Whether 32-bit machine word `w` is `SVC #0` (`0xd4000001`). -/
def isSvc0Word (w : BitVec 32) : Bool :=
  w == 0xd4000001#32

/-- Whether 32-bit machine word `w` is a `BRK #imm16` encoding (`11010100_001_imm16_00000`). -/
def isBrkWord (w : BitVec 32) : Bool :=
  (w &&& 0xffe0001f#32) == 0xd4200000#32

/-- Whether 32-bit machine word `w` is a general system-register write `MSR <sysreg>, Xt`
    (`11010101_0001_op1_CRn_CRm_op2_Rt`). -/
def isMsrWord (w : BitVec 32) : Bool :=
  (w &&& 0xfff00000#32) == 0xd5100000#32

/-- Whether 32-bit machine word `w` encodes `MSR <target>, Xt`. -/
def isMsrSysregWord (target : BitVec 15) (w : BitVec 32) : Bool :=
  isMsrWord w && (w.extractLsb' 5 15 == target)

/-- Whether 32-bit machine word `w` encodes `MSR TPIDR_EL0, Xt` (`0xd51bd040 | Rt`). -/
def isMsrTpidrEl0Word (w : BitVec 32) : Bool :=
  (w &&& 0xffffffe0#32) == 0xd51bd040#32

theorem Instr.isSvc0_imp_isSvc {i : Instr} (h : i.isSvc0 = true) : i.isSvc = true := by
  cases i <;> simp_all [Instr.isSvc0, Instr.isSvc]

theorem Instr.isSvc0_eq_false_of_isSvc_eq_false {i : Instr} (h : i.isSvc = false) :
    i.isSvc0 = false := by
  cases h0 : i.isSvc0 with
  | false => rfl
  | true => rw [i.isSvc0_imp_isSvc h0] at h; contradiction

theorem Instr.isMsrSysreg_imp_isMsr {target : BitVec 15} {i : Instr}
    (h : i.isMsrSysreg target = true) : i.isMsr = true := by
  cases i <;> simp_all [Instr.isMsrSysreg, Instr.isMsr]

theorem Instr.isMsrTpidrEl0_imp_isMsr {i : Instr} (h : i.isMsrTpidrEl0 = true) :
    i.isMsr = true :=
  i.isMsrSysreg_imp_isMsr h

theorem Instr.isMsrTpidrEl0_eq_false_of_isMsr_eq_false {i : Instr} (h : i.isMsr = false) :
    i.isMsrTpidrEl0 = false := by
  cases h0 : i.isMsrTpidrEl0 with
  | false => rfl
  | true => rw [i.isMsrTpidrEl0_imp_isMsr h0] at h; contradiction

/-! ## Decoder Characterizations -/

private theorem guard_false_of_mask {w m1 v1 m2 v2 : BitVec 32}
    (h : w &&& m1 = v1)
    (hne : ((v1 &&& m2) == (v2 &&& m1)) = false := by rfl) :
    ((w &&& m2) == v2) = false := by
  apply Bool.eq_false_iff.mpr
  intro heq
  have hw : w &&& m2 = v2 := eq_of_beq heq
  have h1 : (w &&& m1) &&& m2 = v2 &&& m1 := by
    rw [BitVec.and_assoc, BitVec.and_comm m1 m2, ← BitVec.and_assoc, hw]
  rw [h] at h1
  exact absurd (beq_iff_eq.mpr h1) (by simp [hne])

private theorem ite_guard_false_of_mask {α : Type _} {w m1 v1 m2 v2 : BitVec 32} {t e : α}
    (h : w &&& m1 = v1)
    (hne : ((v1 &&& m2) == (v2 &&& m1)) = false := by rfl) :
    (if (w &&& m2) == v2 then t else e) = e := by
  rw [guard_false_of_mask h hne]; rfl

private theorem ite_guard_and_false_of_mask {α : Type _} {w m1 v1 m2 v2 : BitVec 32}
    {r : Bool} {t e : α}
    (h : w &&& m1 = v1)
    (hne : ((v1 &&& m2) == (v2 &&& m1)) = false := by rfl) :
    (if ((w &&& m2) == v2) && r then t else e) = e := by
  rw [guard_false_of_mask h hne, Bool.false_and]; rfl

private theorem ite_word_ne_of_mask {α : Type _} {w m1 v1 c : BitVec 32} {t e : α}
    (h : w &&& m1 = v1)
    (hne : ((c &&& m1) == v1) = false := by rfl) :
    (if w == c then t else e) = e := by
  have hfalse : (w == c) = false := by
    apply Bool.eq_false_iff.mpr
    intro heq
    rw [eq_of_beq heq] at h
    exact absurd (beq_iff_eq.mpr h) (by simp [hne])
  rw [hfalse]; rfl

private def isSystemInstr (inst : Instr) : Bool := by
  cases inst
  case system _ _ => exact true
  all_goals exact false

private def isSysRegInstr (inst : Instr) : Bool := by
  cases inst
  case sysReg _ _ _ => exact true
  all_goals exact false

private theorem ite_some_skip {P : Instr → Bool} {c : Prop} [Decidable c]
    {t e : Option Instr} {x : Instr}
    (h : (if c then t else e) = some x) (hp : P x = true)
    (ht : ∀ y, t = some y → P y = false) :
    e = some x := by
  split at h
  · rw [ht x h] at hp
    contradiction
  · exact h

private theorem ite_some_peel {P : Instr → Bool} {G : Prop} {c : Prop} [Decidable c]
    {t e : Option Instr} {x : Instr} (hp : P x = true)
    (ht : ∀ y, t = some y → P y = false)
    (he : e = some x → G) :
    (if c then t else e) = some x → G := fun h =>
  he (ite_some_skip h hp ht)

local macro "peel_non_matching_branches" h:ident hp:ident : tactic =>
  `(tactic| (
    revert $h:ident
    repeat' (
      refine ite_some_peel $hp (fun y hy => ?_) ?_
      focus (
        try dsimp only [mkLoadStoreInst] at hy
        repeat' (first | (cases hy <;> rfl) | split at hy)
        done))
    intro $h:ident))

private theorem decode_system_forward_svc {w : BitVec 32}
    (h : w &&& 0xffe0001f#32 = 0xd4000001#32) :
    decode w = some (.system false (w.extractLsb' 5 16)) := by
  unfold decode
  dsimp only
  rw [ite_word_ne_of_mask h, beq_iff_eq.mpr h]
  rfl

private theorem decode_system_forward_brk {w : BitVec 32}
    (h : w &&& 0xffe0001f#32 = 0xd4200000#32) :
    decode w = some (.system true (w.extractLsb' 5 16)) := by
  unfold decode
  dsimp only
  rw [ite_word_ne_of_mask h, ite_guard_false_of_mask h, beq_iff_eq.mpr h]
  rfl

private theorem decode_sysReg_forward {w : BitVec 32}
    (h : w &&& 0xffd00000#32 = 0xd5100000#32) :
    decode w =
      some (.sysReg (w.getLsbD 21) (w.extractLsb' 5 15) (Reg.fromZRBits (w.extractLsb' 0 5))) := by
  unfold decode
  dsimp only
  repeat' first
    | rw [ite_word_ne_of_mask h]
    | rw [ite_guard_false_of_mask h]
    | rw [ite_guard_and_false_of_mask h]
  rw [beq_iff_eq.mpr h]
  rfl

private theorem decode_system_only {w : BitVec 32} {isHalt : Bool} {imm : BitVec 16}
    (h : decode w = some (.system isHalt imm)) :
    (isHalt = false ∧ w &&& 0xffe0001f#32 = 0xd4000001#32 ∧ w.extractLsb' 5 16 = imm) ∨
    (isHalt = true ∧ w &&& 0xffe0001f#32 = 0xd4200000#32 ∧ w.extractLsb' 5 16 = imm) := by
  have hp : isSystemInstr (.system isHalt imm) = true := rfl
  unfold decode at h
  dsimp only at h
  have h1 := ite_some_skip h hp fun y hy => by cases hy; rfl
  clear h
  cases hsvc : ((w &&& 0xffe0001f#32) == 0xd4000001#32)
  · simp only [hsvc, Bool.false_eq_true, ↓reduceIte] at h1
    cases hbrk : ((w &&& 0xffe0001f#32) == 0xd4200000#32)
    · simp only [hbrk, Bool.false_eq_true, ↓reduceIte] at h1
      peel_non_matching_branches h1 hp
      contradiction
    · simp only [hbrk, ↓reduceIte] at h1
      injection h1 with hinst
      injection hinst with hh himm
      exact Or.inr ⟨hh.symm, eq_of_beq hbrk, himm⟩
  · simp only [hsvc, ↓reduceIte] at h1
    injection h1 with hinst
    injection hinst with hh himm
    exact Or.inl ⟨hh.symm, eq_of_beq hsvc, himm⟩

private theorem decode_sysReg_only {w : BitVec 32} {isRead : Bool} {sr : BitVec 15} {rt : Reg}
    (h : decode w = some (.sysReg isRead sr rt)) :
    w &&& 0xffd00000#32 = 0xd5100000#32 ∧
      w.getLsbD 21 = isRead ∧
      w.extractLsb' 5 15 = sr ∧
      Reg.fromZRBits (w.extractLsb' 0 5) = rt := by
  have hp : isSysRegInstr (.sysReg isRead sr rt) = true := rfl
  unfold decode at h
  dsimp only at h
  peel_non_matching_branches h hp
  cases hsr : ((w &&& 0xffd00000#32) == 0xd5100000#32)
  · simp only [hsr, Bool.false_eq_true, ↓reduceIte] at h
    peel_non_matching_branches h hp
    contradiction
  · simp only [hsr, ↓reduceIte] at h
    injection h with hinst
    injection hinst with hr hsr_eq hrt_eq
    exact ⟨eq_of_beq hsr, hr, hsr_eq, hrt_eq⟩

/-- Exact encoding characterisation of `SVC #imm16`. -/
theorem decode_eq_svc_iff {w : BitVec 32} {imm : BitVec 16} :
    decode w = some (.system false imm) ↔
      w &&& 0xffe0001f#32 = 0xd4000001#32 ∧ w.extractLsb' 5 16 = imm := by
  constructor
  · intro h
    rcases decode_system_only h with ⟨_, hm, hi⟩ | ⟨hh, _, _⟩
    · exact ⟨hm, hi⟩
    · contradiction
  · rintro ⟨hm, rfl⟩
    exact decode_system_forward_svc hm

/-- `decode w` produces an `SVC` instruction iff `w` has the `SVC` encoding mask. -/
theorem decode_isSvc_iff {w : BitVec 32} :
    (∃ i, decode w = some i ∧ i.isSvc = true) ↔ isSvcWord w = true := by
  constructor
  · rintro ⟨i, hd, hs⟩
    cases i <;> simp [Instr.isSvc] at hs
    rename_i isHalt imm
    cases isHalt <;> simp at hs
    exact beq_iff_eq.mpr (decode_eq_svc_iff.mp hd).1
  · intro hw
    exact ⟨.system false (w.extractLsb' 5 16), decode_system_forward_svc (eq_of_beq hw), rfl⟩

/-- Any non-`SVC` encoding that decodes produces a non-`SVC` instruction. -/
theorem decode_not_isSvc {w : BitVec 32} {i : Instr}
    (hd : decode w = some i) (hw : isSvcWord w = false) :
    i.isSvc = false := by
  cases hi : i.isSvc with
  | false => rfl
  | true =>
    have := decode_isSvc_iff.mp ⟨i, hd, hi⟩
    rw [this] at hw
    contradiction

private theorem svc0_mask_iff (w : BitVec 32) :
    (w &&& 0xffe0001f#32 = 0xd4000001#32 ∧ w.extractLsb' 5 16 = 0#16) ↔ w = 0xd4000001#32 := by
  bv_bits

/-- Exact encoding characterisation of `SVC #0` (`0xd4000001`). -/
theorem decode_eq_svc0_iff {w : BitVec 32} :
    decode w = some (.system false 0#16) ↔ w = 0xd4000001#32 :=
  decode_eq_svc_iff.trans (svc0_mask_iff w)

/-- `decode w` produces `SVC #0` iff `w = 0xd4000001#32`. -/
theorem decode_isSvc0_iff {w : BitVec 32} :
    (∃ i, decode w = some i ∧ i.isSvc0 = true) ↔ isSvc0Word w = true := by
  constructor
  · rintro ⟨i, hd, hs⟩
    cases i <;> simp [Instr.isSvc0] at hs
    rename_i isHalt imm
    cases isHalt <;> simp at hs
    subst hs
    exact beq_iff_eq.mpr (decode_eq_svc0_iff.mp hd)
  · intro hw
    rw [eq_of_beq hw]
    exact ⟨.system false 0#16, rfl, rfl⟩

/-- Any machine word other than `0xd4000001` never decodes to `SVC #0`. -/
theorem decode_not_isSvc0 {w : BitVec 32} {i : Instr}
    (hd : decode w = some i) (hw : isSvc0Word w = false) :
    i.isSvc0 = false := by
  cases hi : i.isSvc0 with
  | false => rfl
  | true =>
    have := decode_isSvc0_iff.mp ⟨i, hd, hi⟩
    rw [this] at hw
    contradiction

/-- Exact encoding characterisation of `BRK #imm16`. -/
theorem decode_eq_brk_iff {w : BitVec 32} {imm : BitVec 16} :
    decode w = some (.system true imm) ↔
      w &&& 0xffe0001f#32 = 0xd4200000#32 ∧ w.extractLsb' 5 16 = imm := by
  constructor
  · intro h
    rcases decode_system_only h with ⟨hh, _, _⟩ | ⟨_, hm, hi⟩
    · contradiction
    · exact ⟨hm, hi⟩
  · rintro ⟨hm, rfl⟩
    exact decode_system_forward_brk hm

/-- `decode w` produces a `BRK` instruction iff `w` has the `BRK` encoding mask. -/
theorem decode_isBrk_iff {w : BitVec 32} :
    (∃ i, decode w = some i ∧ i.isBrk = true) ↔ isBrkWord w = true := by
  constructor
  · rintro ⟨i, hd, hb⟩
    cases i <;> simp [Instr.isBrk] at hb
    rename_i isHalt imm
    cases isHalt <;> simp at hb
    exact beq_iff_eq.mpr (decode_eq_brk_iff.mp hd).1
  · intro hw
    exact ⟨.system true (w.extractLsb' 5 16), decode_system_forward_brk (eq_of_beq hw), rfl⟩

/-- Any non-`BRK` encoding that decodes produces a non-`BRK` instruction. -/
theorem decode_not_isBrk {w : BitVec 32} {i : Instr}
    (hd : decode w = some i) (hw : isBrkWord w = false) :
    i.isBrk = false := by
  cases hi : i.isBrk with
  | false => rfl
  | true =>
    have := decode_isBrk_iff.mp ⟨i, hd, hi⟩
    rw [this] at hw
    contradiction

/-- Exact encoding characterisation of `MRS` / `MSR` (`Instr.sysReg`). -/
theorem decode_eq_sysReg_iff {w : BitVec 32} {isRead : Bool} {sr : BitVec 15} {rt : Reg} :
    decode w = some (.sysReg isRead sr rt) ↔
      w &&& 0xffd00000#32 = 0xd5100000#32 ∧
        w.getLsbD 21 = isRead ∧
        w.extractLsb' 5 15 = sr ∧
        Reg.fromZRBits (w.extractLsb' 0 5) = rt := by
  constructor
  · exact decode_sysReg_only
  · rintro ⟨hm, rfl, rfl, rfl⟩
    exact decode_sysReg_forward hm

private theorem msr_mask_iff (w : BitVec 32) :
    (w &&& 0xffd00000#32 = 0xd5100000#32 ∧ w.getLsbD 21 = false) ↔
      w &&& 0xfff00000#32 = 0xd5100000#32 := by
  bv_bits

private theorem msr_tpidr_mask_iff (w : BitVec 32) :
    (w &&& 0xfff00000#32 = 0xd5100000#32 ∧ w.extractLsb' 5 15 = 0x5e82#15) ↔
      w &&& 0xffffffe0#32 = 0xd51bd040#32 := by
  bv_bits

/-- `decode w` produces an `MSR <sysreg>, Xt` write iff `(w &&& 0xfff00000#32) == 0xd5100000#32`. -/
theorem decode_isMsr_iff {w : BitVec 32} :
    (∃ i, decode w = some i ∧ i.isMsr = true) ↔ isMsrWord w = true := by
  constructor
  · rintro ⟨i, hd, hm⟩
    cases i <;> simp [Instr.isMsr] at hm
    rename_i isRead sr rt
    cases isRead <;> simp at hm
    obtain ⟨hmask, hl, _, _⟩ := decode_eq_sysReg_iff.mp hd
    exact beq_iff_eq.mpr ((msr_mask_iff w).mp ⟨hmask, hl⟩)
  · intro hw
    obtain ⟨hmask, hl⟩ := (msr_mask_iff w).mpr (eq_of_beq hw)
    refine ⟨.sysReg false (w.extractLsb' 5 15) (Reg.fromZRBits (w.extractLsb' 0 5)), ?_, rfl⟩
    rw [decode_sysReg_forward hmask, hl]

/-- Any non-`MSR` encoding that decodes produces a non-`MSR` instruction (for instance, `MRS`). -/
theorem decode_not_isMsr {w : BitVec 32} {i : Instr}
    (hd : decode w = some i) (hw : isMsrWord w = false) :
    i.isMsr = false := by
  cases hi : i.isMsr with
  | false => rfl
  | true =>
    have := decode_isMsr_iff.mp ⟨i, hd, hi⟩
    rw [this] at hw
    contradiction

/-- `decode w` produces `MSR <target>, Xt` iff `isMsrSysregWord target w = true`. -/
theorem decode_isMsrSysreg_iff {target : BitVec 15} {w : BitVec 32} :
    (∃ i, decode w = some i ∧ i.isMsrSysreg target = true) ↔
      isMsrSysregWord target w = true := by
  constructor
  · rintro ⟨i, hd, hm⟩
    cases i <;> simp [Instr.isMsrSysreg] at hm
    rename_i isRead sr rt
    cases isRead <;> simp at hm
    subst hm
    obtain ⟨hmask, hl, hsr, _⟩ := decode_eq_sysReg_iff.mp hd
    unfold isMsrSysregWord isMsrWord
    rw [beq_iff_eq.mpr ((msr_mask_iff w).mp ⟨hmask, hl⟩), beq_iff_eq.mpr hsr]
    rfl
  · intro hw
    unfold isMsrSysregWord at hw
    rw [Bool.and_eq_true] at hw
    obtain ⟨hmsr, hsr⟩ := hw
    obtain ⟨hmask, hl⟩ := (msr_mask_iff w).mpr (eq_of_beq hmsr)
    refine ⟨.sysReg false target (Reg.fromZRBits (w.extractLsb' 0 5)), ?_, ?_⟩
    · rw [decode_sysReg_forward hmask, hl, eq_of_beq hsr]
    · simp [Instr.isMsrSysreg]

/-- Any encoding with `isMsrSysregWord target w = false` never decodes to `MSR <target>, Xt`. -/
theorem decode_not_isMsrSysreg {target : BitVec 15} {w : BitVec 32} {i : Instr}
    (hd : decode w = some i) (hw : isMsrSysregWord target w = false) :
    i.isMsrSysreg target = false := by
  cases hi : i.isMsrSysreg target with
  | false => rfl
  | true =>
    have := decode_isMsrSysreg_iff.mp ⟨i, hd, hi⟩
    rw [this] at hw
    contradiction

/-- `decode w` produces `MSR TPIDR_EL0, Xt` iff `(w &&& 0xffffffe0#32) == 0xd51bd040#32`. -/
theorem decode_isMsrTpidrEl0_iff {w : BitVec 32} :
    (∃ i, decode w = some i ∧ i.isMsrTpidrEl0 = true) ↔ isMsrTpidrEl0Word w = true := by
  unfold Instr.isMsrTpidrEl0 sysregTpidrEl0
  rw [decode_isMsrSysreg_iff]
  unfold isMsrSysregWord isMsrWord isMsrTpidrEl0Word
  simp only [Bool.and_eq_true, beq_iff_eq]
  exact msr_tpidr_mask_iff w

/-- Any machine word with `(w &&& 0xffffffe0#32) != 0xd51bd040#32` never decodes to
    `MSR TPIDR_EL0, Xt` (in particular, `MRS Xt, TPIDR_EL0` `0xd53bd04x` is excluded). -/
theorem decode_not_isMsrTpidrEl0 {w : BitVec 32} {i : Instr}
    (hd : decode w = some i) (hw : isMsrTpidrEl0Word w = false) :
    i.isMsrTpidrEl0 = false := by
  cases hi : i.isMsrTpidrEl0 with
  | false => rfl
  | true =>
    have := decode_isMsrTpidrEl0_iff.mp ⟨i, hd, hi⟩
    rw [this] at hw
    contradiction

/-! ## Execution State Preservation (`execInst`) -/

section ExecPreservationHelpers

set_option maxHeartbeats 1600000

private def proj3 (s : State) :=
  (s.mem.perm, s.trace, s.tpidrEl0)

private theorem proj3_advancePC (s : State) : proj3 s.advancePC = proj3 s := by cases s; rfl
private theorem proj3_setPC (s : State) (pc : BitVec 64) : proj3 (s.setPC pc) = proj3 s := by
  cases s; rfl
private theorem proj3_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    proj3 (s.writeReg64 r v) = proj3 s := by cases s; cases r <;> rfl
private theorem proj3_writeReg32 (s : State) (r : Reg) (v : BitVec 32) :
    proj3 (s.writeReg32 r v) = proj3 s := proj3_writeReg64 s r _
private theorem proj3_writeReg (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    proj3 (s.writeReg w r v) = proj3 s := proj3_writeReg64 s r _
private theorem proj3_writeVReg128 (s : State) (r : BitVec 5) (v : BitVec 128) :
    proj3 (s.writeVReg128 r v) = proj3 s := by cases s; rfl
private theorem proj3_writeVReg64 (s : State) (r : BitVec 5) (v : BitVec 64) :
    proj3 (s.writeVReg64 r v) = proj3 s := proj3_writeVReg128 s r _
private theorem proj3_writeVReg32 (s : State) (r : BitVec 5) (v : BitVec 32) :
    proj3 (s.writeVReg32 r v) = proj3 s := proj3_writeVReg128 s r _
private theorem proj3_setPState (s : State) (ps : PState) :
    proj3 (s.setPState ps) = proj3 s := by cases s; rfl
private theorem proj3_setFpsr (s : State) (f : BitVec 32) :
    proj3 (s.setFpsr f) = proj3 s := by cases s; rfl
private theorem proj3_orFpsr (s : State) (f : BitVec 32) :
    proj3 (s.orFpsr f) = proj3 s := by cases s; rfl
private theorem proj3_setStatus (s : State) (st : ExecStatus) :
    proj3 (s.setStatus st) = proj3 s := by cases s; rfl
private theorem proj3_with_status (s : State) (st : ExecStatus) :
    proj3 { s with status := st } = proj3 s := by cases s; rfl
private theorem proj3_setMem (s : State) (m' : Memory) :
    proj3 (s.setMem m') = (m'.perm, (proj3 s).2.1, (proj3 s).2.2) := by cases s; rfl
private theorem proj3_stepExclOracle (s : State) :
    proj3 s.stepExclOracle = proj3 s := by cases s; rfl
private theorem proj3_eta (s : State) :
    (s.mem.perm, (proj3 s).2.1, (proj3 s).2.2) = proj3 s := rfl

private theorem perm_writeSimdSized (sz : SimdMemSize) (ea : BitVec 64) (v : BitVec 128)
    (m : Memory) : (m.writeSimdSized sz ea v).perm = m.perm := by
  cases sz <;> simp [Memory.writeSimdSized]

private theorem perm_simdStoreRegs_eq (sz : SimdMemSize) (vals : BitVec 5 → BitVec 128) :
    ∀ (n : Nat) (vt : BitVec 5) (ea : BitVec 64) (m : Memory),
      (simdStoreRegs sz vals n vt ea m).perm = m.perm
  | 0, _, _, _ => rfl
  | n + 1, vt, ea, m => by
    unfold simdStoreRegs
    rw [perm_simdStoreRegs_eq sz vals n _ _ _]
    cases sz <;> simp

private theorem proj3_simdLoadRegs (sz : SimdMemSize) (m : Memory) :
    ∀ (n : Nat) (vt : BitVec 5) (ea : BitVec 64) (s : State),
      proj3 (simdLoadRegs sz m n vt ea s) = proj3 s
  | 0, _, _, _ => rfl
  | n + 1, _vt, _ea, s => (proj3_simdLoadRegs sz m n _ _ _).trans (proj3_writeVReg128 s _ _)

private theorem proj3_applySimd (s : State) (rd : BitVec 5) (r : Except String (BitVec 128)) :
    proj3 (applySimdResult s rd r) = proj3 s := by
  cases s; cases r <;> rfl

private theorem proj3_applySimdSat (s : State) (rd : BitVec 5) (r : Except String (BitVec 128))
    (sat : Option (BitVec 32)) :
    proj3 (applySimdSatResult s rd r sat) = proj3 s := by
  cases s; cases r <;> cases sat <;> rfl

private theorem proj3_execAddSubImm (w : Width) (op : AddSubOp) (rd rn : Reg) (imm12 : BitVec 12)
    (sh : Bool) (s : State) : proj3 (execAddSubImm w op rd rn imm12 sh s) = proj3 s := by
  cases s; simp only [execAddSubImm]; (repeat' split) <;> rfl
private theorem proj3_execAddSubExt (w : Width) (op : AddSubOp) (rd rn rm : Reg) (ext : ExtendType)
    (amt : Nat) (s : State) : proj3 (execAddSubExt w op rd rn rm ext amt s) = proj3 s := by
  cases s; simp only [execAddSubExt]; (repeat' split) <;> rfl
private theorem proj3_execAddSubShift (w : Width) (op : AddSubOp) (rd rn rm : Reg) (sh : ShiftType)
    (amt : Nat) (s : State) : proj3 (execAddSubShift w op rd rn rm sh amt s) = proj3 s := by
  cases s; simp only [execAddSubShift]; (repeat' split) <;> rfl
private theorem proj3_execAddSubCarry (w : Width) (op : AddSubOp) (rd rn rm : Reg) (s : State) :
    proj3 (execAddSubCarry w op rd rn rm s) = proj3 s := by
  cases s; simp only [execAddSubCarry]; (repeat' split) <;> rfl
private theorem proj3_execLogicalImm (w : Width) (op : LogicalOp) (rd rn : Reg) (imm : BitVec 64)
    (s : State) : proj3 (execLogicalImm w op rd rn imm s) = proj3 s := by
  cases s; simp only [execLogicalImm]; (repeat' split) <;> rfl
private theorem proj3_execLogicalShift (w : Width) (op : LogicalOp) (rd rn rm : Reg) (sh : ShiftType)
    (amt : Nat) (s : State) : proj3 (execLogicalShift w op rd rn rm sh amt s) = proj3 s := by
  cases s; simp only [execLogicalShift]; (repeat' split) <;> rfl
private theorem proj3_execMoveWide (w : Width) (op : MoveWideOp) (rd : Reg) (imm : BitVec 16)
    (sh : Nat) (s : State) : proj3 (execMoveWide w op rd imm sh s) = proj3 s := by
  cases s; simp only [execMoveWide]; (repeat' split) <;> rfl
private theorem proj3_execBitfield (w : Width) (op : BitfieldOp) (rd rn : Reg)
    (immr imms : Nat) (s : State) : proj3 (execBitfield w op rd rn immr imms s) = proj3 s := by
  cases s; simp only [execBitfield]; (repeat' split) <;> rfl
private theorem proj3_execCondSelect (w : Width) (op : CondSelectOp) (rd rn rm : Reg)
    (cond : CondCode) (s : State) : proj3 (execCondSelect w op rd rn rm cond s) = proj3 s := by
  cases s; simp only [execCondSelect]; (repeat' split) <;> rfl
private theorem proj3_execCondCompare (w : Width) (isSub isImm : Bool) (rn : Reg) (rhs : BitVec 64)
    (rm : Reg) (nzcv : BitVec 4) (cond : CondCode) (s : State) :
    proj3 (execCondCompare w isSub isImm rn rhs rm nzcv cond s) = proj3 s := by
  cases s; simp only [execCondCompare]; (repeat' split) <;> rfl
private theorem proj3_execDataProc1 (w : Width) (op : DataProc1Op) (rd rn : Reg) (s : State) :
    proj3 (execDataProc1 w op rd rn s) = proj3 s := by
  cases s; simp only [execDataProc1]; (repeat' split) <;> rfl
private theorem proj3_execDataProc2 (w : Width) (op : DataProc2Op) (rd rn rm : Reg) (s : State) :
    proj3 (execDataProc2 w op rd rn rm s) = proj3 s := by
  cases s; simp only [execDataProc2]; (repeat' split) <;> rfl
private theorem proj3_execDataProc3 (w : Width) (op : DataProc3Op) (rd rn rm ra : Reg)
    (s : State) : proj3 (execDataProc3 w op rd rn rm ra s) = proj3 s := by
  cases s; simp only [execDataProc3]; (repeat' split) <;> rfl
private theorem proj3_execLdr (w : Width) (sz : MemWidth) (sg : Bool) (rt : Reg) (addr : AddrMode)
    (s : State) : proj3 (execLdr w sz sg rt addr s) = proj3 s := by
  cases s; simp only [execLdr]; (repeat' split) <;> rfl
private theorem proj3_execLdrLit (w : Width) (sz : MemWidth) (sg : Bool) (rt : Reg) (off : BitVec 64)
    (s : State) : proj3 (execLdrLit w sz sg rt off s) = proj3 s := by
  cases s; simp only [execLdrLit]; (repeat' split) <;> rfl
private theorem proj3_execLdp (w : Width) (sg : Bool) (rt1 rt2 : Reg) (addr : AddrMode)
    (s : State) : proj3 (execLdp w sg rt1 rt2 addr s) = proj3 s := by
  cases s; simp only [execLdp]; (repeat' split) <;> rfl
private theorem proj3_execStr (sz : MemWidth) (rt : Reg) (addr : AddrMode) (s : State) :
    proj3 (execStr sz rt addr s) = proj3 s := by
  dsimp only [execStr]
  rcases evalAddrMode s addr with ⟨ea, _ | ⟨base, newBase⟩⟩ <;>
    simp [proj3_advancePC, proj3_setMem, proj3_writeReg64, proj3_setStatus, proj3_eta,
          Memory.perm_writeSized, apply_ite proj3]
private theorem proj3_execStp (w : Width) (rt1 rt2 : Reg) (addr : AddrMode) (s : State) :
    proj3 (execStp w rt1 rt2 addr s) = proj3 s := by
  dsimp only [execStp]
  rcases evalAddrMode s addr with ⟨ea, _ | ⟨base, newBase⟩⟩ <;>
    simp [proj3_advancePC, proj3_setMem, proj3_writeReg64, proj3_setStatus, proj3_eta,
          Memory.perm_writeSized, apply_ite proj3]

private theorem tpidr_advancePC (s : State) : s.advancePC.tpidrEl0 = s.tpidrEl0 := by cases s; rfl
private theorem tpidr_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).tpidrEl0 = s.tpidrEl0 := by cases s; cases r <;> rfl
private theorem tpidr_setMem (s : State) (m : Memory) : (s.setMem m).tpidrEl0 = s.tpidrEl0 := by
  cases s; rfl
private theorem tpidr_setStatus (s : State) (st : ExecStatus) :
    (s.setStatus st).tpidrEl0 = s.tpidrEl0 := by cases s; rfl
private theorem tpidr_nextOracle (s : State) : s.nextOracle.tpidrEl0 = s.tpidrEl0 := by
  cases s; rfl
private theorem tpidr_setSigAction (s : State) (sig : BitVec 32) (act : SigAction) :
    (s.setSigAction sig act).tpidrEl0 = s.tpidrEl0 := by
  cases s; rfl
private theorem tpidr_setSigAltStack (s : State) (sas : SigAltStack) :
    (s.setSigAltStack sas).tpidrEl0 = s.tpidrEl0 := by
  cases s; rfl
private theorem tpidr_setPhysMemAvail (s : State) (n : Nat) :
    (s.setPhysMemAvail n).tpidrEl0 = s.tpidrEl0 := by
  cases s; rfl

private theorem tpidr_execFcntl (s : State) : (execFcntl s).tpidrEl0 = s.tpidrEl0 := by
  cases s; dsimp (config := { zetaHave := true }) only [execFcntl]; (repeat' split) <;> rfl
private theorem tpidr_execIoctl (s : State) : (execIoctl s).tpidrEl0 = s.tpidrEl0 := by
  cases s; dsimp (config := { zetaHave := true }) only [execIoctl]; (repeat' split) <;> rfl
private theorem tpidr_setFs (s : State) (f : FsState) : (s.setFs f).tpidrEl0 = s.tpidrEl0 := by
  cases s; rfl
private theorem tpidr_appendTrace (s : State) (evs : List TraceEvent) :
    (s.appendTrace evs).tpidrEl0 = s.tpidrEl0 := by
  cases s; rfl
private theorem tpidr_execOpenat (s : State) : (execOpenat s).tpidrEl0 = s.tpidrEl0 := by
  dsimp (config := { zetaHave := true }) only [execOpenat, applyOpenVerdict]
  (repeat' split) <;>
    simp only [tpidr_advancePC, tpidr_writeReg64, tpidr_setStatus, tpidr_setFs, tpidr_appendTrace]
private theorem tpidr_execClose (s : State) : (execClose s).tpidrEl0 = s.tpidrEl0 := by
  cases s; dsimp (config := { zetaHave := true }) only [execClose]; (repeat' split) <;> rfl
private theorem tpidr_execLseek (s : State) : (execLseek s).tpidrEl0 = s.tpidrEl0 := by
  cases s; dsimp (config := { zetaHave := true }) only [execLseek]; (repeat' split) <;> rfl
private theorem tpidr_execReadCommon (s : State) (b : Bool) :
    (execReadCommon s b).tpidrEl0 = s.tpidrEl0 := by
  dsimp (config := { zetaHave := true }) only [execReadCommon]
  cases s.fs.fds (BitVec.zeroExtend 64 (s.readReg32 Reg.x0)) with
  | none =>
    simp only [apply_ite State.tpidrEl0, tpidr_advancePC, tpidr_writeReg64, tpidr_setStatus,
      ite_self]
  | some desc =>
    simp only [apply_ite State.tpidrEl0, tpidr_advancePC, tpidr_writeReg64, tpidr_setStatus,
      tpidr_setMem, tpidr_setFs, ite_self]
private theorem tpidr_execWrite (s : State) : (execWrite s).tpidrEl0 = s.tpidrEl0 := by
  dsimp (config := { zetaHave := true }) only [execWrite]
  cases s.fs.fds (BitVec.zeroExtend 64 (s.readReg32 Reg.x0)) with
  | none =>
    simp only [apply_ite State.tpidrEl0, tpidr_advancePC, tpidr_writeReg64, tpidr_setStatus,
      tpidr_appendTrace, ite_self]
  | some desc =>
    simp only [apply_ite State.tpidrEl0, tpidr_advancePC, tpidr_writeReg64, tpidr_setStatus,
      tpidr_setFs, tpidr_appendTrace, ite_self]
private theorem tpidr_execFstat (s : State) : (execFstat s).tpidrEl0 = s.tpidrEl0 := by
  cases s; dsimp (config := { zetaHave := true }) only [execFstat]; (repeat' split) <;> rfl
private theorem tpidr_execPpoll (s : State) : (execPpoll s).tpidrEl0 = s.tpidrEl0 := by
  dsimp (config := { zetaHave := true }) only [execPpoll]
  cases evalPpollEntries s.fs s.mem (s.readReg64 Reg.x0) (s.readReg32 Reg.x1).toNat 0 0 with
  | none =>
    simp only [apply_ite State.tpidrEl0, tpidr_advancePC, tpidr_writeReg64, tpidr_setStatus,
      ite_self]
  | some rc =>
    rcases rc with ⟨m', count⟩
    simp only [apply_ite State.tpidrEl0, tpidr_advancePC, tpidr_writeReg64, tpidr_setStatus,
      tpidr_setMem, ite_self]
private theorem tpidr_execSetTidAddress (s : State) :
    (execSetTidAddress s).tpidrEl0 = s.tpidrEl0 := by cases s; rfl
private theorem tpidr_execSchedGetaffinity (s : State) :
    (execSchedGetaffinity s).tpidrEl0 = s.tpidrEl0 := by
  cases s; dsimp (config := { zetaHave := true }) only [execSchedGetaffinity]; (repeat' split) <;> rfl
private theorem tpidr_execClockGettime (s : State) :
    (execClockGettime s).tpidrEl0 = s.tpidrEl0 := by
  cases s; dsimp (config := { zetaHave := true }) only [execClockGettime]; (repeat' split) <;> rfl
private theorem tpidr_execMmap (s : State) : (execMmap s).tpidrEl0 = s.tpidrEl0 := by
  dsimp (config := { zetaHave := true }) only [execMmap]
  (repeat' split) <;>
    simp only [tpidr_advancePC, tpidr_writeReg64, tpidr_setStatus, tpidr_setMem, tpidr_nextOracle, tpidr_setPhysMemAvail]
private theorem tpidr_execBrk (s : State) : (execBrk s).tpidrEl0 = s.tpidrEl0 := by
  cases s; dsimp (config := { zetaHave := true }) only [execBrk]; (repeat' split) <;> rfl
private theorem tpidr_execMunmap (s : State) : (execMunmap s).tpidrEl0 = s.tpidrEl0 := by
  cases s; dsimp (config := { zetaHave := true }) only [execMunmap]; (repeat' split) <;> rfl
private theorem tpidr_execMremap (s : State) : (execMremap s).tpidrEl0 = s.tpidrEl0 := by
  dsimp (config := { zetaHave := true }) only [execMremap]
  (repeat' split) <;>
    simp only [tpidr_advancePC, tpidr_writeReg64, tpidr_setStatus, tpidr_setMem, tpidr_nextOracle, tpidr_setPhysMemAvail]
private theorem tpidr_execMprotect (s : State) : (execMprotect s).tpidrEl0 = s.tpidrEl0 := by
  cases s; dsimp (config := { zetaHave := true }) only [execMprotect]; (repeat' split) <;> rfl
private theorem tpidr_execMadvise (s : State) : (execMadvise s).tpidrEl0 = s.tpidrEl0 := by
  cases s; dsimp (config := { zetaHave := true }) only [execMadvise]; (repeat' split) <;> rfl
private theorem tpidr_execTkill (s : State) : (execTkill s).tpidrEl0 = s.tpidrEl0 := by
  dsimp (config := { zetaHave := true }) only [execTkill]
  (repeat' split) <;>
    simp only [tpidr_advancePC, tpidr_writeReg64, tpidr_setStatus]
private theorem tpidr_execTgkill (s : State) : (execTgkill s).tpidrEl0 = s.tpidrEl0 := by
  dsimp (config := { zetaHave := true }) only [execTgkill]
  (repeat' split) <;>
    simp only [tpidr_advancePC, tpidr_writeReg64, tpidr_setStatus]
private theorem tpidr_execSigaltstack (s : State) : (execSigaltstack s).tpidrEl0 = s.tpidrEl0 := by
  dsimp (config := { zetaHave := true }) only [execSigaltstack]
  (repeat' split) <;>
    simp only [tpidr_advancePC, tpidr_writeReg64, tpidr_setStatus, tpidr_setMem, tpidr_setSigAltStack]
private theorem tpidr_execRtSigaction (s : State) : (execRtSigaction s).tpidrEl0 = s.tpidrEl0 := by
  dsimp (config := { zetaHave := true }) only [execRtSigaction]
  (repeat' split) <;>
    simp only [tpidr_advancePC, tpidr_writeReg64, tpidr_setStatus, tpidr_setMem, tpidr_setSigAction]
private theorem tpidr_execRtSigprocmask (s : State) : (execRtSigprocmask s).tpidrEl0 = s.tpidrEl0 := by
  cases s; dsimp (config := { zetaHave := true }) only [execRtSigprocmask]; (repeat' split) <;> rfl
private theorem tpidr_execGetpid (s : State) : (execGetpid s).tpidrEl0 = s.tpidrEl0 := by
  cases s; rfl
private theorem tpidr_execGetrandom (s : State) : (execGetrandom s).tpidrEl0 = s.tpidrEl0 := by
  cases s; dsimp (config := { zetaHave := true }) only [execGetrandom]; (repeat' split) <;> rfl

private theorem tpidr_rwvFrame : ProofLib.RwvFrame (fun a b => b.tpidrEl0 = a.tpidrEl0) :=
  ProofLib.RwvFrame.eqOn State.tpidrEl0 (fun _ _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ _ => rfl)
private theorem tpidr_execReadv (s : State) : (execReadv s).tpidrEl0 = s.tpidrEl0 :=
  ProofLib.execReadv_preserves tpidr_rwvFrame (tpidr_execReadCommon · false) s
private theorem tpidr_execWritev (s : State) : (execWritev s).tpidrEl0 = s.tpidrEl0 :=
  ProofLib.execWritev_preserves tpidr_rwvFrame tpidr_execWrite s

private theorem execSyscall_tpidrEl0 (s : State) : (execSyscall s).tpidrEl0 = s.tpidrEl0 := by
  dsimp only [execSyscall, Syscall.standard, Syscall.dispatch]
  split
  · rename_i nr fn h
    have hm := List.mem_of_find?_eq_some h
    simp only [Syscall.standardTable, Syscall.stdioTable, Syscall.fileIoOnlyTable,
      Syscall.pollTable, Syscall.allocTable, Syscall.signalsTable, Syscall.timeTable,
      Syscall.randomTable, Syscall.miscTable,
      List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact tpidr_execReadCommon s false
    · exact tpidr_execWrite s
    · exact tpidr_execReadv s
    · exact tpidr_execWritev s
    · rfl
    · rfl
    · exact tpidr_execFcntl s
    · exact tpidr_execIoctl s
    · exact tpidr_execOpenat s
    · exact tpidr_execClose s
    · exact tpidr_execLseek s
    · exact tpidr_execReadCommon s true
    · exact tpidr_execFstat s
    · exact tpidr_execPpoll s
    · exact tpidr_execBrk s
    · exact tpidr_execMunmap s
    · exact tpidr_execMremap s
    · exact tpidr_execMmap s
    · exact tpidr_execMprotect s
    · exact tpidr_execMadvise s
    · exact tpidr_execTkill s
    · exact tpidr_execTgkill s
    · exact tpidr_execSigaltstack s
    · exact tpidr_execRtSigaction s
    · exact tpidr_execRtSigprocmask s
    · exact tpidr_execClockGettime s
    · exact tpidr_execGetrandom s
    · exact tpidr_execSetTidAddress s
    · exact tpidr_execSchedGetaffinity s
    · exact tpidr_execGetpid s
    · exact tpidr_execGetpid s
  · rfl

private theorem preserves_of_proj3 {p1 p2 p3 : Prop} {s s' : State} (h : proj3 s' = proj3 s) :
    (p1 → s'.mem.perm = s.mem.perm) ∧
    (p2 → s'.trace = s.trace) ∧
    (p3 → s'.tpidrEl0 = s.tpidrEl0) :=
  ⟨fun _ => congrArg Prod.fst h,
   fun _ => congrArg (fun p => p.2.1) h,
   fun _ => congrArg (fun p => p.2.2) h⟩

private theorem bv2_cases (P : BitVec 2 → Prop)
    (h0 : P 0#2) (h1 : P 1#2) (h2 : P 2#2) (h3 : P 3#2) (x : BitVec 2) : P x := by
  rcases x with ⟨n, hn⟩
  match n with
  | 0 => exact h0
  | 1 => exact h1
  | 2 => exact h2
  | 3 => exact h3
  | _ + 4 => omega

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 800000 in
private theorem execInst_preserves (inst : Instr) (s : State) :
    (inst.isSvc0 = false → (execInst inst s).mem.perm = s.mem.perm) ∧
    (inst.isSvc0 = false → (execInst inst s).trace = s.trace) ∧
    (inst.isMsrTpidrEl0 = false → (execInst inst s).tpidrEl0 = s.tpidrEl0) := by
  cases inst
  case extr w rd rn rm lsb =>
    refine preserves_of_proj3 ?_
    cases w <;> dsimp only [execInst, execInstWithSvc] <;> simp [proj3_advancePC, proj3_writeReg]
  case ldpSimd sz vt1 vt2 addr =>
    refine preserves_of_proj3 ?_
    dsimp only [execInst, execInstWithSvc]
    rcases evalAddrMode s addr with ⟨ea, _ | ⟨base, newBase⟩⟩ <;>
      simp [proj3_advancePC, proj3_writeVReg128, proj3_writeReg64, proj3_setStatus,
            apply_ite proj3]
  case stpSimd sz vt1 vt2 addr =>
    refine preserves_of_proj3 ?_
    dsimp only [execInst, execInstWithSvc]
    rcases evalAddrMode s addr with ⟨ea, _ | ⟨base, newBase⟩⟩ <;>
      simp [proj3_advancePC, proj3_setMem, proj3_writeReg64, proj3_setStatus, proj3_eta,
            perm_simdStoreRegs_eq, apply_ite proj3, apply_ite Memory.perm]
  case ldrSimd sz vt addr =>
    refine preserves_of_proj3 ?_
    dsimp only [execInst, execInstWithSvc]
    rcases evalAddrMode s addr with ⟨ea, _ | ⟨base, newBase⟩⟩ <;>
      simp [proj3_advancePC, proj3_writeVReg128, proj3_writeReg64, proj3_setStatus,
            apply_ite proj3]
  case strSimd sz vt addr =>
    refine preserves_of_proj3 ?_
    dsimp only [execInst, execInstWithSvc]
    rcases evalAddrMode s addr with ⟨ea, _ | ⟨base, newBase⟩⟩ <;>
      simp [proj3_advancePC, proj3_setMem, proj3_writeReg64, proj3_setStatus, proj3_eta,
            perm_simdStoreRegs_eq, apply_ite proj3, apply_ite Memory.perm]
  case simdThreeSame q u size rm opcode rn rd =>
    refine preserves_of_proj3 ?_
    dsimp only [execInst, execInstWithSvc]
    by_cases hop : opcode == 0b00011#5
    · simp only [hop, ↓reduceIte]
      revert size
      refine bv2_cases _ ?_ ?_ ?_ ?_ <;> cases u <;>
        first
        | exact (proj3_advancePC _).trans (proj3_writeVReg128 _ _ _)
        | exact proj3_applySimdSat _ _ _ _
    · simp only [hop, Bool.false_eq_true, ↓reduceIte,
        proj3_advancePC, proj3_writeVReg128, proj3_setStatus, proj3_with_status,
        proj3_applySimd, proj3_applySimdSat, apply_ite proj3, ite_self]
  case system isHalt imm =>
    cases isHalt
    · by_cases himm : imm == 0#16
      · have h_eq : imm = 0#16 := of_decide_eq_true himm
        subst h_eq
        simp only [execInst, execInstWithSvc, himm, ↓reduceIte]
        exact ⟨fun h => Bool.noConfusion h, fun h => Bool.noConfusion h,
               fun _ => execSyscall_tpidrEl0 s⟩
      · refine preserves_of_proj3 ?_
        dsimp only [execInst, execInstWithSvc]
        simp [himm, proj3_setStatus]
    · refine preserves_of_proj3 ?_
      dsimp only [execInst, execInstWithSvc]
      by_cases himm : imm == 1#16 <;> simp [himm, proj3_setStatus]
  case sysReg isRead sr rt =>
    cases isRead
    · by_cases hsr : sr == sysregTpidrEl0
      · have h_eq : sr = 0x5e82#15 := of_decide_eq_true hsr
        subst h_eq
        cases s
        exact ⟨fun _ => rfl, fun _ => rfl, fun h => Bool.noConfusion h⟩
      · refine preserves_of_proj3 ?_
        have hne : (sr == 0x5e82#15) = false := Bool.eq_false_of_ne_true hsr
        dsimp only [execInst, execInstWithSvc]
        simp only [hne, Bool.false_eq_true, ↓reduceIte,
          proj3_advancePC, proj3_writeReg64, proj3_setPState, proj3_setFpsr,
          proj3_with_status, apply_ite proj3, ite_self]
    · refine preserves_of_proj3 ?_
      dsimp only [execInst, execInstWithSvc]
      simp only [↓reduceIte,
        proj3_advancePC, proj3_writeReg64, proj3_setPState, proj3_setFpsr,
        proj3_with_status, apply_ite proj3, ite_self]
  case ldr => exact preserves_of_proj3 (by apply proj3_execLdr)
  case ldrLit => exact preserves_of_proj3 (by apply proj3_execLdrLit)
  case str => exact preserves_of_proj3 (by apply proj3_execStr)
  case ldp => exact preserves_of_proj3 (by apply proj3_execLdp)
  case stp => exact preserves_of_proj3 (by apply proj3_execStp)
  case ldnp => exact preserves_of_proj3 (by apply proj3_execLdp)
  case stnp => exact preserves_of_proj3 (by apply proj3_execStp)
  case addSubImm => exact preserves_of_proj3 (by apply proj3_execAddSubImm)
  case logicalImm => exact preserves_of_proj3 (by apply proj3_execLogicalImm)
  case moveWide => exact preserves_of_proj3 (by apply proj3_execMoveWide)
  case bitfield => exact preserves_of_proj3 (by apply proj3_execBitfield)
  case logicalShift => exact preserves_of_proj3 (by apply proj3_execLogicalShift)
  case addSubShift => exact preserves_of_proj3 (by apply proj3_execAddSubShift)
  case addSubExt => exact preserves_of_proj3 (by apply proj3_execAddSubExt)
  case addSubCarry => exact preserves_of_proj3 (by apply proj3_execAddSubCarry)
  case condCompareReg => exact preserves_of_proj3 (by apply proj3_execCondCompare)
  case condCompareImm => exact preserves_of_proj3 (by apply proj3_execCondCompare)
  case condSelect => exact preserves_of_proj3 (by apply proj3_execCondSelect)
  case dataProc1 => exact preserves_of_proj3 (by apply proj3_execDataProc1)
  case dataProc2 => exact preserves_of_proj3 (by apply proj3_execDataProc2)
  case dataProc3 => exact preserves_of_proj3 (by apply proj3_execDataProc3)
  all_goals
    refine preserves_of_proj3 ?_
    dsimp only [execInst, execInstWithSvc]
    simp only [
      proj3_advancePC, proj3_setPC,
      proj3_writeReg64, proj3_writeReg32, proj3_writeReg,
      proj3_writeVReg128, proj3_writeVReg64, proj3_writeVReg32,
      proj3_setPState, proj3_setFpsr, proj3_orFpsr, proj3_setStatus, proj3_with_status,
      proj3_setMem, proj3_stepExclOracle, proj3_eta,
      proj3_applySimd, proj3_applySimdSat, proj3_simdLoadRegs,
      perm_writeSimdSized, perm_simdStoreRegs_eq, Memory.perm_write8, Memory.perm_write16,
      Memory.perm_write32, Memory.perm_write64, Memory.perm_write128, Memory.perm_writeSized,
      apply_ite proj3, apply_ite Prod.fst, apply_ite Memory.perm, ite_self]

private def lfAt (a : BitVec 64) (s : State) : Bool := s.mem.isLazyFree a

private theorem lfAt_advancePC (a : BitVec 64) (s : State) : lfAt a s.advancePC = lfAt a s := by
  cases s; rfl
private theorem lfAt_setPC (a : BitVec 64) (s : State) (pc : BitVec 64) :
    lfAt a (s.setPC pc) = lfAt a s := by cases s; rfl
private theorem lfAt_writeReg64 (a : BitVec 64) (s : State) (r : Reg) (v : BitVec 64) :
    lfAt a (s.writeReg64 r v) = lfAt a s := by cases s; cases r <;> rfl
private theorem lfAt_writeReg32 (a : BitVec 64) (s : State) (r : Reg) (v : BitVec 32) :
    lfAt a (s.writeReg32 r v) = lfAt a s := lfAt_writeReg64 a s r _
private theorem lfAt_writeReg (a : BitVec 64) (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    lfAt a (s.writeReg w r v) = lfAt a s := lfAt_writeReg64 a s r _
private theorem lfAt_writeVReg128 (a : BitVec 64) (s : State) (r : BitVec 5) (v : BitVec 128) :
    lfAt a (s.writeVReg128 r v) = lfAt a s := by cases s; rfl
private theorem lfAt_writeVReg64 (a : BitVec 64) (s : State) (r : BitVec 5) (v : BitVec 64) :
    lfAt a (s.writeVReg64 r v) = lfAt a s := lfAt_writeVReg128 a s r _
private theorem lfAt_writeVReg32 (a : BitVec 64) (s : State) (r : BitVec 5) (v : BitVec 32) :
    lfAt a (s.writeVReg32 r v) = lfAt a s := lfAt_writeVReg128 a s r _
private theorem lfAt_setPState (a : BitVec 64) (s : State) (ps : PState) :
    lfAt a (s.setPState ps) = lfAt a s := by cases s; rfl
private theorem lfAt_setFpsr (a : BitVec 64) (s : State) (f : BitVec 32) :
    lfAt a (s.setFpsr f) = lfAt a s := by cases s; rfl
private theorem lfAt_orFpsr (a : BitVec 64) (s : State) (f : BitVec 32) :
    lfAt a (s.orFpsr f) = lfAt a s := by cases s; rfl
private theorem lfAt_setStatus (a : BitVec 64) (s : State) (st : ExecStatus) :
    lfAt a (s.setStatus st) = lfAt a s := by cases s; rfl
private theorem lfAt_with_status (a : BitVec 64) (s : State) (st : ExecStatus) :
    lfAt a { s with status := st } = lfAt a s := by cases s; rfl
private theorem lfAt_setMem (a : BitVec 64) (s : State) (m' : Memory) :
    lfAt a (s.setMem m') = m'.isLazyFree a := by cases s; rfl
private theorem lfAt_stepExclOracle (a : BitVec 64) (s : State) :
    lfAt a s.stepExclOracle = lfAt a s := by cases s; rfl
private theorem lfAt_applySimd (a : BitVec 64) (s : State) (rd : BitVec 5)
    (r : Except String (BitVec 128)) :
    lfAt a (applySimdResult s rd r) = lfAt a s := by cases s; cases r <;> rfl
private theorem lfAt_applySimdSat (a : BitVec 64) (s : State) (rd : BitVec 5)
    (r : Except String (BitVec 128)) (sat : Option (BitVec 32)) :
    lfAt a (applySimdSatResult s rd r sat) = lfAt a s := by
  cases s; cases r <;> cases sat <;> rfl
private theorem lfAt_simdLoadRegs (a : BitVec 64) (sz : SimdMemSize) (m : Memory) :
    ∀ (n : Nat) (vt : BitVec 5) (ea : BitVec 64) (s : State),
      lfAt a (simdLoadRegs sz m n vt ea s) = lfAt a s
  | 0, _, _, _ => rfl
  | n + 1, _, _, s => (lfAt_simdLoadRegs a sz m n _ _ _).trans (lfAt_writeVReg128 a s _ _)

private theorem lf_writeSized {m : Memory} {sz : MemWidth} {w v a : BitVec 64}
    (h : m.isLazyFree a = false) : (m.writeSized sz w v).isLazyFree a = false := by
  cases sz <;> simp only [Memory.writeSized]
  · exact Memory.isLazyFree_write8_of_false _ _ h
  · exact Memory.isLazyFree_write16_of_false _ _ h
  · exact Memory.isLazyFree_write32_of_false _ _ h
  · exact Memory.isLazyFree_write64_of_false _ _ h

private theorem lf_writeSimdSized {m : Memory} {sz : SimdMemSize} {ea a : BitVec 64} {v : BitVec 128}
    (h : m.isLazyFree a = false) : (m.writeSimdSized sz ea v).isLazyFree a = false := by
  cases sz <;> simp only [Memory.writeSimdSized]
  · exact Memory.isLazyFree_write8_of_false _ _ h
  · exact Memory.isLazyFree_write16_of_false _ _ h
  · exact Memory.isLazyFree_write32_of_false _ _ h
  · exact Memory.isLazyFree_write64_of_false _ _ h
  · exact Memory.isLazyFree_write128_of_false _ _ h

private theorem lf_simdStoreRegs {sz : SimdMemSize} {vals : BitVec 5 → BitVec 128} :
    ∀ {n : Nat} {vt : BitVec 5} {ea : BitVec 64} {m : Memory} {a : BitVec 64},
      m.isLazyFree a = false → (simdStoreRegs sz vals n vt ea m).isLazyFree a = false
  | 0, _, _, _, _, h => h
  | _ + 1, _, _, _, _, h => by
    unfold simdStoreRegs
    exact lf_simdStoreRegs (lf_writeSimdSized h)

private theorem lfAt_execAddSubImm (a : BitVec 64) (w : Width) (op : AddSubOp) (rd rn : Reg)
    (imm12 : BitVec 12) (sh : Bool) (s : State) :
    lfAt a (execAddSubImm w op rd rn imm12 sh s) = lfAt a s := by
  cases s; simp only [execAddSubImm]; (repeat' split) <;> rfl
private theorem lfAt_execAddSubExt (a : BitVec 64) (w : Width) (op : AddSubOp) (rd rn rm : Reg)
    (ext : ExtendType) (amt : Nat) (s : State) :
    lfAt a (execAddSubExt w op rd rn rm ext amt s) = lfAt a s := by
  cases s; simp only [execAddSubExt]; (repeat' split) <;> rfl
private theorem lfAt_execAddSubShift (a : BitVec 64) (w : Width) (op : AddSubOp) (rd rn rm : Reg)
    (sh : ShiftType) (amt : Nat) (s : State) :
    lfAt a (execAddSubShift w op rd rn rm sh amt s) = lfAt a s := by
  cases s; simp only [execAddSubShift]; (repeat' split) <;> rfl
private theorem lfAt_execAddSubCarry (a : BitVec 64) (w : Width) (op : AddSubOp) (rd rn rm : Reg)
    (s : State) : lfAt a (execAddSubCarry w op rd rn rm s) = lfAt a s := by
  cases s; simp only [execAddSubCarry]; (repeat' split) <;> rfl
private theorem lfAt_execLogicalImm (a : BitVec 64) (w : Width) (op : LogicalOp) (rd rn : Reg)
    (imm : BitVec 64) (s : State) : lfAt a (execLogicalImm w op rd rn imm s) = lfAt a s := by
  cases s; simp only [execLogicalImm]; (repeat' split) <;> rfl
private theorem lfAt_execLogicalShift (a : BitVec 64) (w : Width) (op : LogicalOp) (rd rn rm : Reg)
    (sh : ShiftType) (amt : Nat) (s : State) :
    lfAt a (execLogicalShift w op rd rn rm sh amt s) = lfAt a s := by
  cases s; simp only [execLogicalShift]; (repeat' split) <;> rfl
private theorem lfAt_execMoveWide (a : BitVec 64) (w : Width) (op : MoveWideOp) (rd : Reg)
    (imm : BitVec 16) (sh : Nat) (s : State) :
    lfAt a (execMoveWide w op rd imm sh s) = lfAt a s := by
  cases s; simp only [execMoveWide]; (repeat' split) <;> rfl
private theorem lfAt_execBitfield (a : BitVec 64) (w : Width) (op : BitfieldOp) (rd rn : Reg)
    (immr imms : Nat) (s : State) : lfAt a (execBitfield w op rd rn immr imms s) = lfAt a s := by
  cases s; simp only [execBitfield]; (repeat' split) <;> rfl
private theorem lfAt_execCondSelect (a : BitVec 64) (w : Width) (op : CondSelectOp) (rd rn rm : Reg)
    (cond : CondCode) (s : State) : lfAt a (execCondSelect w op rd rn rm cond s) = lfAt a s := by
  cases s; simp only [execCondSelect]; (repeat' split) <;> rfl
private theorem lfAt_execCondCompare (a : BitVec 64) (w : Width) (isSub isImm : Bool) (rn : Reg)
    (rhs : BitVec 64) (rm : Reg) (nzcv : BitVec 4) (cond : CondCode) (s : State) :
    lfAt a (execCondCompare w isSub isImm rn rhs rm nzcv cond s) = lfAt a s := by
  cases s; simp only [execCondCompare]; (repeat' split) <;> rfl
private theorem lfAt_execDataProc1 (a : BitVec 64) (w : Width) (op : DataProc1Op) (rd rn : Reg)
    (s : State) : lfAt a (execDataProc1 w op rd rn s) = lfAt a s := by
  cases s; simp only [execDataProc1]; (repeat' split) <;> rfl
private theorem lfAt_execDataProc2 (a : BitVec 64) (w : Width) (op : DataProc2Op) (rd rn rm : Reg)
    (s : State) : lfAt a (execDataProc2 w op rd rn rm s) = lfAt a s := by
  cases s; simp only [execDataProc2]; (repeat' split) <;> rfl
private theorem lfAt_execDataProc3 (a : BitVec 64) (w : Width) (op : DataProc3Op)
    (rd rn rm ra : Reg) (s : State) : lfAt a (execDataProc3 w op rd rn rm ra s) = lfAt a s := by
  cases s; simp only [execDataProc3]; (repeat' split) <;> rfl
private theorem lfAt_execLdr (a : BitVec 64) (w : Width) (sz : MemWidth) (sg : Bool) (rt : Reg)
    (addr : AddrMode) (s : State) : lfAt a (execLdr w sz sg rt addr s) = lfAt a s := by
  cases s; simp only [execLdr]; (repeat' split) <;> rfl
private theorem lfAt_execLdrLit (a : BitVec 64) (w : Width) (sz : MemWidth) (sg : Bool) (rt : Reg)
    (off : BitVec 64) (s : State) : lfAt a (execLdrLit w sz sg rt off s) = lfAt a s := by
  cases s; simp only [execLdrLit]; (repeat' split) <;> rfl
private theorem lfAt_execLdp (a : BitVec 64) (w : Width) (sg : Bool) (rt1 rt2 : Reg)
    (addr : AddrMode) (s : State) : lfAt a (execLdp w sg rt1 rt2 addr s) = lfAt a s := by
  cases s; simp only [execLdp]; (repeat' split) <;> rfl
private theorem lfAt_execStr (a : BitVec 64) (sz : MemWidth) (rt : Reg) (addr : AddrMode)
    (s : State) (hlf : s.mem.isLazyFree a = false) : lfAt a (execStr sz rt addr s) = false := by
  have hlf' : lfAt a s = false := hlf
  dsimp only [execStr]
  rcases evalAddrMode s addr with ⟨ea, _ | ⟨base, newBase⟩⟩ <;>
    simp only [lfAt_advancePC, lfAt_setMem, lfAt_writeReg64, lfAt_setStatus,
      lf_writeSized, apply_ite (lfAt a), hlf, hlf', ite_self]
private theorem lfAt_execStp (a : BitVec 64) (w : Width) (rt1 rt2 : Reg) (addr : AddrMode)
    (s : State) (hlf : s.mem.isLazyFree a = false) : lfAt a (execStp w rt1 rt2 addr s) = false := by
  have hlf' : lfAt a s = false := hlf
  dsimp only [execStp]
  rcases evalAddrMode s addr with ⟨ea, _ | ⟨base, newBase⟩⟩ <;>
    simp only [lfAt_advancePC, lfAt_setMem, lfAt_writeReg64, lfAt_setStatus,
      lf_writeSized, apply_ite (lfAt a), hlf, hlf', ite_self]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 800000 in
private theorem execInst_isLazyFree_false_inner {inst : Instr} (h : inst.isSvc0 = false)
    (s : State) {a : BitVec 64} (hlf : s.mem.isLazyFree a = false) :
    (execInst inst s).mem.isLazyFree a = false := by
  change lfAt a (execInst inst s) = false
  have hlf' : lfAt a s = false := hlf
  cases inst
  case system isHalt imm =>
    cases isHalt
    · by_cases himm : imm == 0#16
      · have heq : imm = 0#16 := of_decide_eq_true himm; subst heq; simp [Instr.isSvc0] at h
      · dsimp only [execInst, execInstWithSvc]; simp only [himm, Bool.false_eq_true, ↓reduceIte, lfAt_setStatus, hlf']
    · dsimp only [execInst, execInstWithSvc]
      by_cases himm : imm == 1#16 <;> simp [himm, lfAt_setStatus, hlf']
  all_goals clear h
  case extr w rd rn rm lsb =>
    cases w <;> dsimp only [execInst, execInstWithSvc] <;>
      simp only [lfAt_advancePC, lfAt_writeReg, hlf']
  case sysReg isRead sr rt =>
    cases isRead
    · by_cases hsr : sr == sysregTpidrEl0
      · have heq : sr = 0x5e82#15 := of_decide_eq_true hsr; subst heq; cases s; exact hlf
      · have hne : (sr == 0x5e82#15) = false := Bool.eq_false_of_ne_true hsr
        dsimp only [execInst, execInstWithSvc]
        simp only [hne, Bool.false_eq_true, ↓reduceIte, lfAt_advancePC, lfAt_writeReg64,
          lfAt_setPState, lfAt_setFpsr, lfAt_with_status, apply_ite (lfAt a), hlf', ite_self]
    · dsimp only [execInst, execInstWithSvc]
      simp only [↓reduceIte, lfAt_advancePC, lfAt_writeReg64, lfAt_setPState, lfAt_setFpsr,
        lfAt_with_status, apply_ite (lfAt a), hlf', ite_self]
  case simdThreeSame q u size rm opcode rn rd =>
    dsimp only [execInst, execInstWithSvc]
    by_cases hop : opcode == 0b00011#5
    · simp only [hop, ↓reduceIte]
      revert size
      refine bv2_cases _ ?_ ?_ ?_ ?_ <;> cases u <;>
        first
        | exact ((lfAt_advancePC a _).trans (lfAt_writeVReg128 a _ _ _)).trans hlf'
        | exact (lfAt_applySimdSat a _ _ _ _).trans hlf'
    · simp only [hop, Bool.false_eq_true, ↓reduceIte, lfAt_advancePC, lfAt_writeVReg128,
        lfAt_setStatus, lfAt_with_status, lfAt_applySimd, lfAt_applySimdSat,
        apply_ite (lfAt a), hlf', ite_self]
  case ldpSimd sz vt1 vt2 addr | stpSimd sz vt1 vt2 addr | ldrSimd sz vt addr | strSimd sz vt addr =>
    dsimp only [execInst, execInstWithSvc]
    rcases evalAddrMode s addr with ⟨ea, _ | ⟨base, newBase⟩⟩ <;>
      simp only [lfAt_advancePC, lfAt_setMem, lfAt_writeVReg128, lfAt_writeReg64, lfAt_setStatus,
        lf_simdStoreRegs, lf_writeSimdSized, apply_ite (lfAt a),
        apply_ite (fun m : Memory => m.isLazyFree a), hlf, hlf', ite_self]
  case ldr => dsimp only [execInst, execInstWithSvc]; rw [lfAt_execLdr]; exact hlf'
  case ldrLit => dsimp only [execInst, execInstWithSvc]; rw [lfAt_execLdrLit]; exact hlf'
  case str => exact lfAt_execStr a _ _ _ s hlf
  case ldp => dsimp only [execInst, execInstWithSvc]; rw [lfAt_execLdp]; exact hlf'
  case stp => exact lfAt_execStp a _ _ _ _ s hlf
  case ldnp => dsimp only [execInst, execInstWithSvc]; rw [lfAt_execLdp]; exact hlf'
  case stnp => exact lfAt_execStp a _ _ _ _ s hlf
  case addSubImm => dsimp only [execInst, execInstWithSvc]; rw [lfAt_execAddSubImm]; exact hlf'
  case logicalImm => dsimp only [execInst, execInstWithSvc]; rw [lfAt_execLogicalImm]; exact hlf'
  case moveWide => dsimp only [execInst, execInstWithSvc]; rw [lfAt_execMoveWide]; exact hlf'
  case bitfield => dsimp only [execInst, execInstWithSvc]; rw [lfAt_execBitfield]; exact hlf'
  case logicalShift => dsimp only [execInst, execInstWithSvc]; rw [lfAt_execLogicalShift]; exact hlf'
  case addSubShift => dsimp only [execInst, execInstWithSvc]; rw [lfAt_execAddSubShift]; exact hlf'
  case addSubExt => dsimp only [execInst, execInstWithSvc]; rw [lfAt_execAddSubExt]; exact hlf'
  case addSubCarry => dsimp only [execInst, execInstWithSvc]; rw [lfAt_execAddSubCarry]; exact hlf'
  case condCompareReg => dsimp only [execInst, execInstWithSvc]; rw [lfAt_execCondCompare]; exact hlf'
  case condCompareImm => dsimp only [execInst, execInstWithSvc]; rw [lfAt_execCondCompare]; exact hlf'
  case condSelect => dsimp only [execInst, execInstWithSvc]; rw [lfAt_execCondSelect]; exact hlf'
  case dataProc1 => dsimp only [execInst, execInstWithSvc]; rw [lfAt_execDataProc1]; exact hlf'
  case dataProc2 => dsimp only [execInst, execInstWithSvc]; rw [lfAt_execDataProc2]; exact hlf'
  case dataProc3 => dsimp only [execInst, execInstWithSvc]; rw [lfAt_execDataProc3]; exact hlf'
  all_goals
    dsimp only [execInst, execInstWithSvc]
    simp only [
      lfAt_advancePC, lfAt_setPC, lfAt_writeReg64, lfAt_writeReg32, lfAt_writeReg,
      lfAt_writeVReg128, lfAt_writeVReg64, lfAt_writeVReg32,
      lfAt_setPState, lfAt_setFpsr, lfAt_orFpsr, lfAt_setStatus, lfAt_with_status,
      lfAt_setMem, lfAt_stepExclOracle, lfAt_applySimd, lfAt_applySimdSat, lfAt_simdLoadRegs,
      lf_writeSimdSized, lf_simdStoreRegs, lf_writeSized,
      Memory.isLazyFree_write8_of_false, Memory.isLazyFree_write16_of_false,
      Memory.isLazyFree_write32_of_false, Memory.isLazyFree_write64_of_false,
      Memory.isLazyFree_write128_of_false,
      apply_ite (lfAt a), apply_ite Prod.fst, apply_ite (fun m : Memory => m.isLazyFree a),
      hlf, hlf', ite_self]

end ExecPreservationHelpers

/-- Every instruction except `SVC #0` preserves `s.mem.isLazyFree a = false`. -/
theorem execInst_isLazyFree_false_of_not_isSvc0 {inst : Instr} (h : inst.isSvc0 = false)
    (s : State) {a : BitVec 64} (hlf : s.mem.isLazyFree a = false) :
    (execInst inst s).mem.isLazyFree a = false :=
  execInst_isLazyFree_false_inner h s hlf

/-- Every instruction except `SVC #0` preserves `s.mem.perm`. -/
theorem execInst_perm_of_not_isSvc0 {inst : Instr} (h : inst.isSvc0 = false) (s : State) :
    (execInst inst s).mem.perm = s.mem.perm :=
  (execInst_preserves inst s).1 h

/-- Pointwise form of `execInst_perm_of_not_isSvc0`. -/
theorem execInst_perm_apply_of_not_isSvc0 {inst : Instr} (h : inst.isSvc0 = false)
    (s : State) (a : BitVec 64) :
    (execInst inst s).mem.perm a = s.mem.perm a :=
  congrFun (execInst_perm_of_not_isSvc0 h s) a

/-- Every instruction except `SVC #0` preserves `s.trace`. -/
theorem execInst_trace_of_not_isSvc0 {inst : Instr} (h : inst.isSvc0 = false) (s : State) :
    (execInst inst s).trace = s.trace :=
  (execInst_preserves inst s).2.1 h

/-- Every non-`SVC` instruction preserves `s.trace`. -/
theorem execInst_trace_of_not_isSvc {inst : Instr} (h : inst.isSvc = false) (s : State) :
    (execInst inst s).trace = s.trace :=
  execInst_trace_of_not_isSvc0 (inst.isSvc0_eq_false_of_isSvc_eq_false h) s

/-- Every instruction except `MSR TPIDR_EL0, Xt` preserves `s.tpidrEl0` (including `SVC #0`
    and `MRS Xt, TPIDR_EL0`). -/
theorem execInst_tpidrEl0_of_not_isMsrTpidrEl0 {inst : Instr}
    (h : inst.isMsrTpidrEl0 = false) (s : State) :
    (execInst inst s).tpidrEl0 = s.tpidrEl0 :=
  (execInst_preserves inst s).2.2 h

/-- Every non-`MSR` instruction preserves `s.tpidrEl0`. -/
theorem execInst_tpidrEl0_of_not_isMsr {inst : Instr} (h : inst.isMsr = false) (s : State) :
    (execInst inst s).tpidrEl0 = s.tpidrEl0 :=
  execInst_tpidrEl0_of_not_isMsrTpidrEl0 (inst.isMsrTpidrEl0_eq_false_of_isMsr_eq_false h) s

/-! ## Whole-Code Checkers (`Program`, `Code`, `WordTree`) -/

/-- Check `pw` on every 4-byte aligned little-endian word in `bs`. -/
def bytesAllWords (pw : BitVec 32 → Bool) : List (BitVec 8) → Bool
  | b0 :: b1 :: b2 :: b3 :: rest => pw (b3 ++ b2 ++ b1 ++ b0) && bytesAllWords pw rest
  | [] => true
  | [_] => true
  | [_, _] => true
  | [_, _, _] => true

/-- Lift an instruction predicate `p : Instr → Bool` to 32-bit machine words:
    vacuously `true` on undecodable words (`decode w = none`). -/
def instrPredOnWord (p : Instr → Bool) (w : BitVec 32) : Bool :=
  match decode w with
  | some i => p i
  | none => true

theorem bytesAllWords_mono {pw qw : BitVec 32 → Bool}
    (h : ∀ w, pw w = true → qw w = true) :
    ∀ bs, bytesAllWords pw bs = true → bytesAllWords qw bs = true
  | b0 :: b1 :: b2 :: b3 :: rest, hbs => by
    rcases (Bool.and_eq_true _ _).mp hbs with ⟨hw, hrest⟩
    exact (Bool.and_eq_true _ _).mpr ⟨h _ hw, bytesAllWords_mono h rest hrest⟩
  | [], _ => rfl
  | [_], _ => rfl
  | [_, _], _ => rfl
  | [_, _, _], _ => rfl

private theorem bytesAllWords_drop_mul4 {pw : BitVec 32 → Bool}
    {b0 b1 b2 b3 : BitVec 8} {rest : List (BitVec 8)} :
    ∀ (k : Nat) (bs : List (BitVec 8)),
      bytesAllWords pw bs = true →
      bs.drop (4 * k) = b0 :: b1 :: b2 :: b3 :: rest →
      pw (b3 ++ b2 ++ b1 ++ b0) = true
  | 0, _, hbs, hdrop => by
    simp only [Nat.mul_zero, List.drop_zero] at hdrop
    rw [hdrop] at hbs
    exact (Bool.and_eq_true _ _).mp hbs |>.1
  | k + 1, bs, hbs, hdrop => by
    have hstep_eq : 4 * (k + 1) = 4 + 4 * k := by omega
    rw [hstep_eq, ← List.drop_drop] at hdrop
    match bs with
    | [] | [_] | [_, _] | [_, _, _] =>
      simp at hdrop
    | c0 :: c1 :: c2 :: c3 :: tail =>
      have htail : bytesAllWords pw tail = true := (Bool.and_eq_true _ _).mp hbs |>.2
      exact bytesAllWords_drop_mul4 k tail htail hdrop

namespace Program

/-- Check `pw` on every 4-byte aligned word in `prog.code`. -/
def allWords (pw : BitVec 32 → Bool) (prog : Program) : Bool :=
  bytesAllWords pw prog.code

/-- Check `p` on every decoded 4-byte aligned instruction in `prog.code`. -/
def allInstrs (p : Instr → Bool) (prog : Program) : Bool :=
  prog.allWords (instrPredOnWord p)

@[simp] theorem rebase_allWords (pw : BitVec 32 → Bool) (prog : Program) (b : BitVec 64)
    (X : String → Option (State → State)) (O : String → Option (State → State)) :
    (prog.rebase b X O).allWords pw = prog.allWords pw := rfl

@[simp] theorem rebase_allInstrs (p : Instr → Bool) (prog : Program) (b : BitVec 64)
    (X : String → Option (State → State)) (O : String → Option (State → State)) :
    (prog.rebase b X O).allInstrs p = prog.allInstrs p := rfl

theorem allWords_of_code_eq {pw : BitVec 32 → Bool} {prog prog' : Program}
    (hc : prog'.code = prog.code) (h : prog.allWords pw = true) :
    prog'.allWords pw = true := by
  unfold allWords at h ⊢; rw [hc]; exact h

theorem allInstrs_of_code_eq {p : Instr → Bool} {prog prog' : Program}
    (hc : prog'.code = prog.code) (h : prog.allInstrs p = true) :
    prog'.allInstrs p = true :=
  allWords_of_code_eq hc h

theorem allInstrs_of_allWords {pw : BitVec 32 → Bool} {p : Instr → Bool} {prog : Program}
    (himp : ∀ w i, decode w = some i → pw w = false → p i = false)
    (hw : prog.allWords (fun w => !pw w) = true) :
    prog.allInstrs (fun i => !p i) = true := by
  refine bytesAllWords_mono (fun w hpw => ?_) prog.code hw
  unfold instrPredOnWord
  cases hd : decode w with
  | none => rfl
  | some i =>
    cases hbw : pw w with
    | false => simp [himp w i hd hbw]
    | true => rw [hbw] at hpw; contradiction

/-- Every 4-byte aligned word read from `prog` satisfies `pw` when `prog.allWords pw = true`. -/
theorem readWordOff_of_allWords {pw : BitVec 32 → Bool} {prog : Program}
    (hall : prog.allWords pw = true) {off : Nat} {w : BitVec 32}
    (hrw : prog.readWordOff off = some w) :
    pw w = true := by
  unfold readWordOff at hrw
  split at hrw
  · contradiction
  rename_i hal
  split at hrw
  rotate_left
  · contradiction
  rename_i b0 b1 b2 b3 rest hdrop
  injection hrw with hw
  subst hw
  have hk : off = 4 * (off / 4) := by omega
  rw [hk] at hdrop
  exact bytesAllWords_drop_mul4 (off / 4) prog.code hall hdrop

/-- Turn `prog.allInstrs p = true` into `∀ addr i, prog.fetch addr = some i → p i = true`. -/
theorem fetch_of_allInstrs {p : Instr → Bool} {prog : Program}
    (hall : prog.allInstrs p = true) :
    ∀ (addr : BitVec 64) (i : Instr), prog.fetch addr = some i → p i = true := by
  intro addr i hfetch
  unfold fetch at hfetch
  split at hfetch
  · contradiction
  simp only [Option.bind_eq_some_iff] at hfetch
  obtain ⟨w, hrw, hd⟩ := hfetch
  have hpw := readWordOff_of_allWords hall hrw
  unfold instrPredOnWord at hpw
  rw [hd] at hpw
  exact hpw

/-- Rebased form of `fetch_of_allInstrs`, applying directly to `(prog.rebase b X O).fetch addr`
    (including `(code.rebase b X).fetch (b + off)`). -/
theorem rebase_fetch_of_allInstrs {p : Instr → Bool} {prog : Program}
    (hall : prog.allInstrs p = true)
    (b : BitVec 64)
    (X : String → Option (State → State) := fun _ => none)
    (O : String → Option (State → State) := fun _ => none) :
    ∀ (addr : BitVec 64) (i : Instr), (prog.rebase b X O).fetch addr = some i → p i = true :=
  fetch_of_allInstrs (by simpa using hall)

/-- Lift whole-code checking from a canonical code program `prog0` (`prog0.code = li.code`) to
    any linked image `img` with `Obj.Loads li img`. -/
theorem ofImage_allInstrs_of_loads {p : Instr → Bool} {li : Obj.LinkedImage} {img : Obj.Image}
    {prog0 : Program}
    (hL : Obj.Loads li img) (hc : prog0.code = li.code)
    (hall : prog0.allInstrs p = true)
    (X : String → Option (State → State) := fun _ => none)
    (O : String → Option (State → State) := fun _ => none) :
    (Program.ofImage img X O).allInstrs p = true := by
  have himg : (Program.ofImage img X O).code = prog0.code := by
    change img.code = prog0.code
    rw [(ProofLib.ObjectLoad.Loads.canonical hL).1, hc]
  exact allInstrs_of_code_eq himg hall

/-- Alias for `ofImage_allInstrs_of_loads`. -/
abbrev ofImage_allInstrs := @ofImage_allInstrs_of_loads

/-- Every executable byte in `m` (`(m.perm a).x = true`) lies within
    `[prog.base, prog.base + prog.code.length)`. -/
def ExecOnlyIn (prog : Program) (m : Memory) : Prop :=
  ∀ a : BitVec 64, (m.perm a).x = true → (a - prog.base).toNat < prog.code.length

theorem ExecOnlyIn.of_base_code {prog prog' : Program} {m : Memory}
    (h : prog.ExecOnlyIn m) (hb : prog'.base = prog.base) (hc : prog'.code = prog.code) :
    prog'.ExecOnlyIn m := by
  intro a ha; rw [hb, hc]; exact h a ha

theorem ExecOnlyIn.of_perm_eq {prog : Program} {m m' : Memory}
    (h : prog.ExecOnlyIn m) (hperm : m'.perm = m.perm) :
    prog.ExecOnlyIn m' := by
  intro a ha; rw [hperm] at ha; exact h a ha

/-- `Obj.HoldsBytes m base bytes (fun _ => Perm.rx)` is frozen and therefore preserved across any
    `Memory.KeepsFrozen` transition (including every `Step` and `Steps`). -/
theorem holdsBytes_rx_of_keepsFrozen {m m' : Memory} {base : BitVec 64} {bytes : List (BitVec 8)}
    (hH : Obj.HoldsBytes m base bytes (fun _ => Perm.rx))
    (hk : m.KeepsFrozen m') :
    Obj.HoldsBytes m' base bytes (fun _ => Perm.rx) := by
  intro i hi
  obtain ⟨hb, hp, hlf⟩ := hH i hi
  have hf : m.Frozen (base + BitVec.ofNat 64 i) := by
    unfold Memory.Frozen; rw [hp]; rfl
  obtain ⟨hb', hp', hlf', _⟩ := hk _ hf
  exact ⟨hb'.trans hb, hp'.trans hp, hlf'.trans hlf⟩

/-- `Program.loadCode` establishes `Obj.HoldsBytes (prog.loadCode m) prog.base prog.code
    (fun _ => Perm.rx)` for all bytes of `prog.code` (including zero-stub slots). -/
theorem holdsBytes_loadCode (prog : Program) (m : Memory)
    (h_len : prog.base.toNat + prog.code.length ≤ 2 ^ 64) :
    Obj.HoldsBytes (prog.loadCode m) prog.base prog.code (fun _ => Perm.rx) := by
  intro i hi
  have hi' : (prog.base + BitVec.ofNat 64 i - prog.base).toNat = i := by
    have : prog.base + BitVec.ofNat 64 i - prog.base = BitVec.ofNat 64 i := by
      rw [BitVec.add_comm, BitVec.add_sub_cancel]
    rw [this, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hsize : prog.code.toArray.size = prog.code.length := by simp
  have hp_rx : (prog.loadCode m).perm (prog.base + BitVec.ofNat 64 i) = some Perm.rx := by
    simp only [Program.loadCode, Memory.perm_ofFn, hsize, hi', hi, ↓reduceIte,
      Option.map_some, Perm.rwx_rx]
  have hlf : (prog.loadCode m).isLazyFree (prog.base + BitVec.ofNat 64 i) = false := by
    simp only [Program.loadCode, Memory.isLazyFree_ofFn, hsize, hi', hi, ↓reduceIte]
    rfl
  refine ⟨?_, hp_rx, hlf⟩
  simp only [Program.loadCode, Memory.read8_ofFn, hsize, hi', hi, ↓reduceIte]
  simp [hi]

private theorem readWordOff_eq_read32_of_bytes {prog : Program} {m : Memory} {pc : BitVec 64}
    (hbase : prog.base.toNat % 4 = 0)
    (hlen : prog.base.toNat + prog.code.length ≤ 2 ^ 64)
    (hal : pc.toNat % 4 = 0)
    (hexec_bounds : ∀ k : Nat, k < 4 → ((pc + BitVec.ofNat 64 k) - prog.base).toNat < prog.code.length)
    (hbytes : ∀ k : Nat, (hk : ((pc + BitVec.ofNat 64 k) - prog.base).toNat < prog.code.length) →
      k < 4 → m.read8 (pc + BitVec.ofNat 64 k) =
        prog.code[((pc + BitVec.ofNat 64 k) - prog.base).toNat]'hk) :
    prog.readWordOff (pc - prog.base).toNat = some (m.read32 pc) := by
  let off := (pc - prog.base).toNat
  have hpc : pc = prog.base + BitVec.ofNat 64 off := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm prog.base, BitVec.sub_add_cancel]
  have hoff_lt0 : off < prog.code.length := by
    simpa [off] using hexec_bounds 0 (by omega)
  have hpcn : pc.toNat = prog.base.toNat + off := by
    rw [hpc, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := off) (by omega), Nat.mod_eq_of_lt (by omega)]
  have hoff_al : off % 4 = 0 := by omega
  have hstep_off : ∀ k : Nat, k < 4 → ((pc + BitVec.ofNat 64 k) - prog.base).toNat = off + k := by
    intro k hk
    have hklt : off + k < prog.code.length := by
      have hsub : pc + BitVec.ofNat 64 k - prog.base = BitVec.ofNat 64 (off + k) := by
        rw [hpc, BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.add_comm prog.base,
          BitVec.add_sub_cancel]
      have hlt_k := hexec_bounds k hk
      rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hlt_k
      exact hlt_k
    have hsub : pc + BitVec.ofNat 64 k - prog.base = BitVec.ofNat 64 (off + k) := by
      rw [hpc, BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.add_comm prog.base,
        BitVec.add_sub_cancel]
    rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hlen4 : off + 4 ≤ prog.code.length := by
    have h3 := hexec_bounds 3 (by omega)
    rw [hstep_off 3 (by omega)] at h3
    omega
  have hb_at : ∀ k (hk : k < 4),
      m.read8 (pc + BitVec.ofNat 64 k) = prog.code[off + k]'(by omega) := by
    intro k hk
    have hb := hbytes k (hexec_bounds k hk) hk
    simpa only [hstep_off k hk] using hb
  have hdrop : prog.code.drop off =
      prog.code[off] :: prog.code[off + 1] :: prog.code[off + 2] :: prog.code[off + 3] ::
        prog.code.drop (off + 4) := by
    rw [List.drop_eq_getElem_cons (by omega),
        List.drop_eq_getElem_cons (by omega),
        List.drop_eq_getElem_cons (by omega),
        List.drop_eq_getElem_cons (by omega)]
  show prog.readWordOff off = some (m.read32 pc)
  unfold readWordOff
  rw [ite_eq_right_iff.mpr fun h => absurd h (by omega), hdrop]
  simp only [Memory.read32, BitVec.add_zero]
  have b0 : m.read8 pc = prog.code[off] := by simpa using hb_at 0 (by omega)
  rw [b0, hb_at 1 (by omega), hb_at 2 (by omega), hb_at 3 (by omega)]

/-- Lift `prog.allInstrs p = true` to dynamic instruction fetch `prog.fetchMem m pc = some i`
    at any address within `[prog.base, prog.base + prog.code.length - 4]` whenever
    `Obj.HoldsBytes m prog.base prog.code (fun _ => Perm.rx)` holds (without requiring
    `prog.ExecOnlyIn m`, so additional linked startup/driver segments may also be executable). -/
theorem fetchMem_of_allInstrs_holdsBytes_in_code {p : Instr → Bool} {prog : Program} {m : Memory}
    (hall : prog.allInstrs p = true)
    (hbase : prog.base.toNat % 4 = 0)
    (hlen : prog.base.toNat + prog.code.length ≤ 2 ^ 64)
    (hH : Obj.HoldsBytes m prog.base prog.code (fun _ => Perm.rx))
    {pc : BitVec 64} {i : Instr}
    (hin : (pc - prog.base).toNat + 4 ≤ prog.code.length)
    (hfm : prog.fetchMem m pc = some i) :
    p i = true := by
  unfold fetchMem at hfm
  split at hfm
  · contradiction
  split at hfm
  · contradiction
  rename_i hal
  split at hfm
  · contradiction
  have hal0 : pc.toNat % 4 = 0 := by simp at hal; exact hal
  let off := (pc - prog.base).toNat
  have hpc : pc = prog.base + BitVec.ofNat 64 off := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm prog.base, BitVec.sub_add_cancel]
  have hexec_bounds : ∀ k : Nat, k < 4 → ((pc + BitVec.ofNat 64 k) - prog.base).toNat < prog.code.length := by
    intro k hk
    have hsub : pc + BitVec.ofNat 64 k - prog.base = BitVec.ofNat 64 (off + k) := by
      rw [hpc, BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.add_comm prog.base,
        BitVec.add_sub_cancel]
    rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  have hrw := readWordOff_eq_read32_of_bytes hbase hlen hal0 hexec_bounds fun k hk _ => by
    have heq : pc + BitVec.ofNat 64 k =
        prog.base + BitVec.ofNat 64 ((pc + BitVec.ofNat 64 k - prog.base).toNat) := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm prog.base, BitVec.sub_add_cancel]
    simpa only [← heq] using (hH _ hk).1
  have hpw := readWordOff_of_allWords hall hrw
  unfold instrPredOnWord at hpw
  rw [hfm] at hpw
  exact hpw

/-- Lift `prog.allInstrs p = true` to dynamic instruction fetch `prog.fetchMem m pc = some i`
    whenever `Obj.HoldsBytes m prog.base prog.code (fun _ => Perm.rx)` holds and only `prog.code`
    is mapped executable (`prog.ExecOnlyIn m`). Works even when `prog` leaves unreachable extern
    stubs unhooked (`prog.externs sym = none`). -/
theorem fetchMem_of_allInstrs_holdsBytes {p : Instr → Bool} {prog : Program} {m : Memory}
    (hall : prog.allInstrs p = true)
    (hbase : prog.base.toNat % 4 = 0)
    (hlen : prog.base.toNat + prog.code.length ≤ 2 ^ 64)
    (hH : Obj.HoldsBytes m prog.base prog.code (fun _ => Perm.rx))
    (hexec : prog.ExecOnlyIn m) :
    ∀ (pc : BitVec 64) (i : Instr), prog.fetchMem m pc = some i → p i = true := by
  intro pc i hfm
  unfold fetchMem at hfm
  split at hfm
  · contradiction
  split at hfm
  · contradiction
  rename_i hal
  split at hfm
  · contradiction
  rename_i hcan
  have hal0 : pc.toNat % 4 = 0 := by simp at hal; exact hal
  have hexec_bounds : ∀ k : Nat, k < 4 → ((pc + BitVec.ofNat 64 k) - prog.base).toNat < prog.code.length := by
    intro k hk
    have hcx : m.canExec pc 4 = true := by simpa using hcan
    unfold Memory.canExec at hcx
    rw [Memory.allPerm_iff] at hcx
    exact hexec _ (hcx k hk)
  have hrw := readWordOff_eq_read32_of_bytes hbase hlen hal0 hexec_bounds fun k hk _ => by
    have heq : pc + BitVec.ofNat 64 k =
        prog.base + BitVec.ofNat 64 ((pc + BitVec.ofNat 64 k - prog.base).toNat) := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm prog.base, BitVec.sub_add_cancel]
    simpa only [← heq] using (hH _ hk).1
  have hpw := readWordOff_of_allWords hall hrw
  unfold instrPredOnWord at hpw
  rw [hfm] at hpw
  exact hpw

/-- Lift `prog.allInstrs p = true` to `prog.fetchMem m pc = some i` under `prog.CodeLoaded m` and
    `prog.ExecOnlyIn m` (including unhooked extern stubs, since `CodeLoaded` pins every byte of
    `prog.code`). -/
theorem fetchMem_of_allInstrs {p : Instr → Bool} {prog : Program} {m : Memory}
    (hall : prog.allInstrs p = true)
    (hL : prog.CodeLoaded m)
    (hexec : prog.ExecOnlyIn m) :
    ∀ (pc : BitVec 64) (i : Instr), prog.fetchMem m pc = some i → p i = true :=
  fetchMem_of_allInstrs_holdsBytes hall hL.aligned hL.no_wrap
    (fun k hk => ⟨hL.byte_eq k hk, hL.perm_eq k hk, hL.isLazyFree_eq k hk⟩) hexec

end Program

/-! ## `Code` Aliases and `Step` Lifting Lemmas -/

namespace Code

/-- Whole-code 32-bit word checker alias (`Code.allWords pw code = code.allWords pw`). -/
abbrev allWords (pw : BitVec 32 → Bool) (code : Program) : Bool :=
  code.allWords pw

/-- Whole-code instruction checker (`Code.allInstrs p code = code.allInstrs p`). -/
abbrev allInstrs (p : Instr → Bool) (code : Program) : Bool :=
  code.allInstrs p

end Code

theorem Step.holdsBytes_rx {prog : Program} {s s' : State} {base : BitVec 64}
    {bytes : List (BitVec 8)}
    (hstep : Step prog s s')
    (hH : Obj.HoldsBytes s.mem base bytes (fun _ => Perm.rx)) :
    Obj.HoldsBytes s'.mem base bytes (fun _ => Perm.rx) :=
  Program.holdsBytes_rx_of_keepsFrozen hH hstep.keepsFrozen

theorem Steps.holdsBytes_rx {prog : Program} {s s' : State} {base : BitVec 64}
    {bytes : List (BitVec 8)}
    (hsteps : Steps prog s s')
    (hH : Obj.HoldsBytes s.mem base bytes (fun _ => Perm.rx)) :
    Obj.HoldsBytes s'.mem base bytes (fun _ => Perm.rx) :=
  Program.holdsBytes_rx_of_keepsFrozen hH hsteps.keepsFrozen

/-- Any instruction other than `SVC #0` executes identically under `prog.evalInst` and `execInst`,
    regardless of `prog.svc`. -/
theorem evalInst_eq_execInst_of_not_isSvc0 {prog : Program} {i : Instr}
    (h : i.isSvc0 = false) (s : State) :
    prog.evalInst i s = execInst i s := by
  cases i with
  | system isHint imm =>
    cases isHint
    · by_cases himm : imm == 0#16
      · have heq : imm = 0#16 := of_decide_eq_true himm
        subst heq
        simp [Instr.isSvc0] at h
      · simp [Program.evalInst, execInst, execInstWithSvc, himm]
    · simp [Program.evalInst, execInst, execInstWithSvc]
  | _ => rfl

/-- Any instruction other than `MSR TPIDR_EL0, Xt` preserves `s.tpidrEl0` under `prog.evalInst`,
    regardless of `prog.svc` (since `evalSvc` unconditionally preserves `tpidrEl0`). -/
theorem evalInst_tpidrEl0_of_not_isMsrTpidrEl0 {prog : Program} {i : Instr}
    (h : i.isMsrTpidrEl0 = false) (s : State) :
    (prog.evalInst i s).tpidrEl0 = s.tpidrEl0 := by
  by_cases hsvc : i.isSvc0 = true
  · cases i with
    | system isHint imm =>
      cases isHint
      · have heq : imm = 0#16 := by simpa [Instr.isSvc0] using hsvc
        subst heq
        rfl
      · simp [Instr.isSvc0] at hsvc
    | _ => simp [Instr.isSvc0] at hsvc
  · rw [evalInst_eq_execInst_of_not_isSvc0 (Bool.eq_false_iff.mpr hsvc)]
    exact execInst_tpidrEl0_of_not_isMsrTpidrEl0 h s

/-- Any `Step` at a PC with no active hook (`prog.externAt? s.pc = none`) where fetched
    instructions are never `SVC #0` preserves memory permissions and the trace. -/
theorem Step.perm_and_trace_of_noHook {prog : Program} {s s' : State}
    (hnoSvc0 : ∀ i, prog.fetchMem s.mem s.pc = some i → i.isSvc0 = false)
    (hstep : Step prog s s')
    (hext : prog.externAt? s.pc = none) :
    s'.mem.perm = s.mem.perm ∧ s'.trace = s.trace := by
  cases hstep with
  | exec _ h_fetch =>
    have hns := hnoSvc0 _ h_fetch
    rw [evalInst_eq_execInst_of_not_isSvc0 hns]
    exact ⟨execInst_perm_of_not_isSvc0 hns s, execInst_trace_of_not_isSvc0 hns s⟩
  | halt_unmapped _ _ _ => exact ⟨rfl, rfl⟩
  | extern _ h_ext _ _ => rw [hext] at h_ext; contradiction
  | extern_fault _ h_ext _ => rw [hext] at h_ext; contradiction

/-- Any `Step` whose fetched instructions are never `MSR TPIDR_EL0, Xt` and whose active hooks
    preserve `tpidrEl0` preserves `s.tpidrEl0`. -/
theorem Step.tpidrEl0_of_noMsrTpidrEl0 {prog : Program} {s s' : State}
    (hnoMsr : ∀ i, prog.fetchMem s.mem s.pc = some i → i.isMsrTpidrEl0 = false)
    (hhook : ∀ f, prog.externAt? s.pc = some f → (f s).tpidrEl0 = s.tpidrEl0)
    (hstep : Step prog s s') :
    s'.tpidrEl0 = s.tpidrEl0 := by
  cases hstep with
  | exec _ h_fetch => exact evalInst_tpidrEl0_of_not_isMsrTpidrEl0 (hnoMsr _ h_fetch) s
  | halt_unmapped _ _ _ => rfl
  | extern _ h_ext _ _ => exact hhook _ h_ext
  | extern_fault _ _ _ => rfl

end Arm64

/-! ## `WordTree` Checkers and `prove_all_instrs` Tactic -/

namespace ProofLib.ProgramReflection

open Arm64

/-- Check `pw` on every 4-byte leaf of `t` without flattening to a byte list. -/
def WordTree.allWords (pw : BitVec 32 → Bool) : WordTree → Bool
  | .empty => true
  | .leaf b0 b1 b2 b3 => pw (b3 ++ b2 ++ b1 ++ b0)
  | .node _ l r => l.allWords pw && r.allWords pw

/-- Check `p` on every decoded 4-byte leaf of `t`. -/
def WordTree.allInstrs (p : Instr → Bool) (t : WordTree) : Bool :=
  t.allWords (instrPredOnWord p)

private theorem WordTree.bytesAllWords_toBytesAux (pw : BitVec 32 → Bool) :
    ∀ (t : WordTree) (acc : List (BitVec 8)),
      bytesAllWords pw (t.toBytesAux acc) = (t.allWords pw && bytesAllWords pw acc)
  | .empty, acc => by simp [WordTree.toBytesAux, WordTree.allWords]
  | .leaf b0 b1 b2 b3, acc => rfl
  | .node _ l r, acc => by
    simp only [WordTree.toBytesAux, WordTree.allWords,
      WordTree.bytesAllWords_toBytesAux pw l (r.toBytesAux acc),
      WordTree.bytesAllWords_toBytesAux pw r acc, Bool.and_assoc]

/-- Flattening a `WordTree` preserves `bytesAllWords` identically. -/
theorem WordTree.bytesAllWords_toBytes (pw : BitVec 32 → Bool) (t : WordTree) :
    bytesAllWords pw t.toBytes = t.allWords pw := by
  rw [WordTree.toBytes, WordTree.bytesAllWords_toBytesAux]
  exact Bool.and_true _

theorem WordTree.allWords_mono {pw qw : BitVec 32 → Bool}
    (h : ∀ w, pw w = true → qw w = true) :
    ∀ (t : WordTree), t.allWords pw = true → t.allWords qw = true
  | .empty, _ => rfl
  | .leaf _ _ _ _, ht => h _ ht
  | .node _ l r, ht => by
    simp only [WordTree.allWords, Bool.and_eq_true] at ht ⊢
    exact ⟨WordTree.allWords_mono h l ht.1, WordTree.allWords_mono h r ht.2⟩

/-- Reduce `t.allInstrs (fun i => !p i) = true` to a fast bitmask check
    `t.allWords (fun w => !pw w) = true` without running `Arm64.decode` in the kernel. -/
theorem WordTree.allInstrs_of_allWords {pw : BitVec 32 → Bool} {p : Instr → Bool} {t : WordTree}
    (himp : ∀ w i, decode w = some i → pw w = false → p i = false)
    (hw : t.allWords (fun w => !pw w) = true) :
    t.allInstrs (fun i => !p i) = true := by
  refine WordTree.allWords_mono (fun w hpw => ?_) t hw
  unfold instrPredOnWord
  cases hd : decode w with
  | none => rfl
  | some i =>
    cases hbw : pw w with
    | false => simp [himp w i hd hbw]
    | true => rw [hbw] at hpw; contradiction

/-- Prove `prog.allInstrs p = true` via its reflected `WordTree`. -/
theorem Program.allInstrs_of_tree {p : Instr → Bool} {prog : Program} {t : WordTree}
    (hcode : prog.code = t.toBytes)
    (ht : t.allInstrs p = true) :
    prog.allInstrs p = true := by
  unfold Arm64.Program.allInstrs Arm64.Program.allWords
  rw [hcode, WordTree.bytesAllWords_toBytes]
  exact ht

/-- Prove `prog.allInstrs (fun i => !p i) = true` in linear kernel mask-check time via its
    reflected `WordTree` without running `Arm64.decode` per instruction. -/
theorem Program.allInstrs_of_tree_words {pw : BitVec 32 → Bool} {p : Instr → Bool}
    {prog : Program} {t : WordTree}
    (himp : ∀ w i, decode w = some i → pw w = false → p i = false)
    (hcode : prog.code = t.toBytes)
    (ht : t.allWords (fun w => !pw w) = true) :
    prog.allInstrs (fun i => !p i) = true :=
  Program.allInstrs_of_tree hcode (WordTree.allInstrs_of_allWords himp ht)

theorem fetch_false_of_allInstrs_neg {q : Instr → Bool} {prog : Program}
    (hall : prog.allInstrs (fun i => !q i) = true) :
    ∀ (addr : BitVec 64) (i : Instr), prog.fetch addr = some i → q i = false := by
  intro addr i hf
  have h := Arm64.Program.fetch_of_allInstrs hall addr i hf
  cases hq : q i <;> simp_all

theorem fetch_not_of_allInstrs_neg {q : Instr → Bool} {prog : Program}
    (hall : prog.allInstrs (fun i => !q i) = true) :
    ∀ (addr : BitVec 64) (i : Instr), prog.fetch addr = some i → ¬ (q i = true) := by
  intro addr i hf hq
  rw [fetch_false_of_allInstrs_neg hall addr i hf] at hq
  contradiction

theorem rebase_fetch_false_of_allInstrs_neg {q : Instr → Bool} {prog : Program}
    (hall : prog.allInstrs (fun i => !q i) = true)
    (b : BitVec 64)
    (X : String → Option (State → State) := fun _ => none)
    (O : String → Option (State → State) := fun _ => none) :
    ∀ (addr : BitVec 64) (i : Instr), (prog.rebase b X O).fetch addr = some i → q i = false := by
  intro addr i hf
  have h := Arm64.Program.rebase_fetch_of_allInstrs hall b X O addr i hf
  cases hq : q i <;> simp_all

theorem rebase_fetch_not_of_allInstrs_neg {q : Instr → Bool} {prog : Program}
    (hall : prog.allInstrs (fun i => !q i) = true)
    (b : BitVec 64)
    (X : String → Option (State → State) := fun _ => none)
    (O : String → Option (State → State) := fun _ => none) :
    ∀ (addr : BitVec 64) (i : Instr), (prog.rebase b X O).fetch addr = some i → ¬ (q i = true) := by
  intro addr i hf hq
  rw [rebase_fetch_false_of_allInstrs_neg hall b X O addr i hf] at hq
  contradiction

end ProofLib.ProgramReflection

namespace ProofLib.OpcodeExclusion

open Lean Meta Elab Tactic Arm64 ProofLib.ProgramReflection

private meta def findCodeEqTheorem? (progExpr : Expr) : MetaM (Option Expr) := do
  let env ← getEnv
  let some progConst := progExpr.getAppFn.constName? | return none
  if progExpr.isApp then return none
  let cand := progConst.appendAfter "_code_eq"
  if env.contains cand then
    return some (mkConst cand)
  return none

private meta def matchNegInstrPred? (p : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let p ← instantiateMVars p
  let body? : Option (Name × Array Expr) :=
    match p with
    | .lam _ _ b _ =>
      if b.isAppOfArity ``Bool.not 1 then
        let inner := b.appArg!.headBeta
        if inner.getAppArgs.back? == some (.bvar 0) then
          match inner.getAppFn.constName? with
          | some fn => some (fn, inner.getAppArgs.pop)
          | none => none
        else none
      else none
    | _ => none
  let some (fn, extraArgs) := body? | return none
  if fn == ``Instr.isSvc && extraArgs.isEmpty then
    return some (mkConst ``Arm64.isSvcWord, mkConst ``Instr.isSvc, mkConst ``Arm64.decode_not_isSvc)
  if fn == ``Instr.isSvc0 && extraArgs.isEmpty then
    return some (mkConst ``Arm64.isSvc0Word, mkConst ``Instr.isSvc0, mkConst ``Arm64.decode_not_isSvc0)
  if fn == ``Instr.isBrk && extraArgs.isEmpty then
    return some (mkConst ``Arm64.isBrkWord, mkConst ``Instr.isBrk, mkConst ``Arm64.decode_not_isBrk)
  if fn == ``Instr.isMsr && extraArgs.isEmpty then
    return some (mkConst ``Arm64.isMsrWord, mkConst ``Instr.isMsr, mkConst ``Arm64.decode_not_isMsr)
  if fn == ``Instr.isMsrTpidrEl0 && extraArgs.isEmpty then
    return some (mkConst ``Arm64.isMsrTpidrEl0Word, mkConst ``Instr.isMsrTpidrEl0,
      mkConst ``Arm64.decode_not_isMsrTpidrEl0)
  if fn == ``Instr.isMsrSysreg && extraArgs.size == 1 && !extraArgs[0]!.hasLooseBVars then
    let sr := extraArgs[0]!
    return some (mkApp (mkConst ``Arm64.isMsrSysregWord) sr, mkApp (mkConst ``Instr.isMsrSysreg) sr,
      mkApp (mkConst ``Arm64.decode_not_isMsrSysreg) sr)
  return none

private meta def buildWordTreeExpr (progExpr : Expr) : MetaM Expr := do
  let elems ← listElemsWhnf (mkApp (Lean.mkConst ``Program.code) progExpr)
  if elems.size % 4 != 0 then
    throwError "prove_all_instrs: expected `prog.code` byte length to be a multiple of 4, got {elems.size}"
  let leafFn := Lean.mkConst ``WordTree.leaf
  let nodeFn := Lean.mkConst ``WordTree.node
  let emptyTree := Lean.mkConst ``WordTree.empty
  let rec build (fuel : Nat) (lo hi : Nat) : MetaM Expr := do
    match fuel with
    | 0 => return emptyTree
    | fuel' + 1 =>
      let len := hi - lo
      if len == 0 then
        return emptyTree
      else if len == 1 then
        let baseIdx := 4 * lo
        return mkApp4 leafFn elems[baseIdx]! elems[baseIdx + 1]! elems[baseIdx + 2]! elems[baseIdx + 3]!
      else
        let half := len / 2
        let mid := lo + half
        let l ← build fuel' lo mid
        let r ← build fuel' mid hi
        return mkApp3 nodeFn (mkRawNatLit half) l r
  build 64 0 (elems.size / 4)

private meta def stripRebaseExpr (progExpr : Expr) : Expr :=
  if progExpr.isAppOfArity ``Arm64.Program.rebase 4 then
    progExpr.getArg! 0
  else
    progExpr

public theorem close_rebase_not {q : Instr → Bool} {prog : Program}
    {b : BitVec 64} {X O : String → Option (Arm64.State → Arm64.State)} {addr : BitVec 64}
    {i : Instr}
    (hf : (prog.rebase b X O).fetch addr = some i)
    (hall : prog.allInstrs (fun x => !q x) = true) : ¬ (q i = true) :=
  rebase_fetch_not_of_allInstrs_neg hall b X O addr i hf

public theorem close_rebase_false {q : Instr → Bool} {prog : Program}
    {b : BitVec 64} {X O : String → Option (Arm64.State → Arm64.State)} {addr : BitVec 64}
    {i : Instr}
    (hf : (prog.rebase b X O).fetch addr = some i)
    (hall : prog.allInstrs (fun x => !q x) = true) : q i = false :=
  rebase_fetch_false_of_allInstrs_neg hall b X O addr i hf

public theorem close_rebase_pos {p : Instr → Bool} {prog : Program}
    {b : BitVec 64} {X O : String → Option (Arm64.State → Arm64.State)} {addr : BitVec 64}
    {i : Instr}
    (hf : (prog.rebase b X O).fetch addr = some i)
    (hall : prog.allInstrs p = true) : p i = true :=
  Arm64.Program.rebase_fetch_of_allInstrs hall b X O addr i hf

public theorem close_fetch_not {q : Instr → Bool} {prog : Program} {addr : BitVec 64} {i : Instr}
    (hf : prog.fetch addr = some i)
    (hall : prog.allInstrs (fun x => !q x) = true) : ¬ (q i = true) :=
  fetch_not_of_allInstrs_neg hall addr i hf

public theorem close_fetch_false {q : Instr → Bool} {prog : Program} {addr : BitVec 64} {i : Instr}
    (hf : prog.fetch addr = some i)
    (hall : prog.allInstrs (fun x => !q x) = true) : q i = false :=
  fetch_false_of_allInstrs_neg hall addr i hf

public theorem close_fetch_pos {p : Instr → Bool} {prog : Program} {addr : BitVec 64} {i : Instr}
    (hf : prog.fetch addr = some i)
    (hall : prog.allInstrs p = true) : p i = true :=
  Arm64.Program.fetch_of_allInstrs hall addr i hf

private meta def proveProgAllInstrsExpr (p prog : Expr) : MetaM Expr := do
  let innerProg := stripRebaseExpr prog
  let codeEq ← match ← findCodeEqTheorem? innerProg with
    | some pf =>
      if prog == innerProg then pure pf
      else
        let eqTy ← mkEq (mkApp (mkConst ``Program.code) prog) ((← inferType pf).appArg!)
        mkExpectedTypeHint pf eqTy
    | none =>
      let treeExpr ← buildWordTreeExpr prog
      let toBytesExpr := mkApp (mkConst ``WordTree.toBytes) treeExpr
      let eqTy ← mkEq (mkApp (mkConst ``Program.code) prog) toBytesExpr
      mkExpectedTypeHint (← mkEqRefl toBytesExpr) eqTy
  let treeExpr := ((← inferType codeEq).appArg!).appArg!
  if let some (pwFn, pFn, impPf) := ← matchNegInstrPred? p then
    let negPw := mkLambda `w .default (mkApp (mkConst ``BitVec) (mkNatLit 32))
      (mkApp (mkConst ``Bool.not) (mkApp pwFn (.bvar 0)))
    let lhsWords := mkApp2 (mkConst ``WordTree.allWords) negPw treeExpr
    let htPf ← mkEqRefl lhsWords
    return mkAppN (mkConst ``ProofLib.ProgramReflection.Program.allInstrs_of_tree_words)
      #[pwFn, pFn, prog, treeExpr, impPf, codeEq, htPf]
  else
    let lhsTree := mkApp2 (mkConst ``WordTree.allInstrs) p treeExpr
    let htPf ← mkEqRefl lhsTree
    return mkAppN (mkConst ``ProofLib.ProgramReflection.Program.allInstrs_of_tree)
      #[p, prog, treeExpr, codeEq, htPf]

private meta def extractFetchGoalSpec? (targetTy : Expr) (iExpr : Expr) :
    Option (Expr × Expr × Name × Name) :=
  if targetTy.isAppOfArity ``Not 1 then
    if let some (_, lhs, rhs) := targetTy.appArg!.eq? then
      if rhs.isConstOf ``Bool.true then
        let body := lhs.abstract #[iExpr]
        let q := mkLambda `x .default (mkConst ``Instr) body
        let negQ := mkLambda `x .default (mkConst ``Instr) (mkApp (mkConst ``Bool.not) body)
        some (q, negQ, ``close_rebase_not, ``close_fetch_not)
      else none
    else none
  else if let some (_, lhs, rhs) := targetTy.eq? then
    let body := lhs.abstract #[iExpr]
    let pred := mkLambda `x .default (mkConst ``Instr) body
    if rhs.isConstOf ``Bool.false then
      let negQ := mkLambda `x .default (mkConst ``Instr) (mkApp (mkConst ``Bool.not) body)
      some (pred, negQ, ``close_rebase_false, ``close_fetch_false)
    else if rhs.isConstOf ``Bool.true then
      some (pred, pred, ``close_rebase_pos, ``close_fetch_pos)
    else none
  else none

private meta def tryCloseUniversalFetchGoal (g : MVarId) : MetaM Bool := do
  let gTy ← instantiateMVars (← g.getType)
  if !gTy.isForall then return false
  let ok? ← observing? do
    let (_, gIntro) ← g.intros
    gIntro.withContext do
      let lctx ← getLCtx
      let mut fetchHyps : Array (Expr × Expr × Expr × Expr) := #[]
      for decl in lctx do
        if !decl.isImplementationDetail then
          let ty ← instantiateMVars decl.type
          if let some (_, lhs, rhs) := ty.eq? then
            if lhs.isAppOfArity ``Arm64.Program.fetch 2 && rhs.isAppOfArity ``Option.some 2 then
              fetchHyps := fetchHyps.push (mkFVar decl.fvarId, lhs.getArg! 0, lhs.getArg! 1, rhs.appArg!)
      let targetTy ← instantiateMVars (← gIntro.getType)
      for (hf, fetchProg, addrExpr, iExpr) in fetchHyps do
        if let some (predExpr, allPredExpr, rebaseLem, plainLem) := extractFetchGoalSpec? targetTy iExpr then
          if fetchProg.isAppOfArity ``Arm64.Program.rebase 4 then
            let innerProg := fetchProg.getArg! 0
            let bExpr := fetchProg.getArg! 1
            let xExpr := fetchProg.getArg! 2
            let oExpr := fetchProg.getArg! 3
            let hallPf ← proveProgAllInstrsExpr allPredExpr innerProg
            let pf := mkAppN (mkConst rebaseLem)
              #[predExpr, innerProg, bExpr, xExpr, oExpr, addrExpr, iExpr, hf, hallPf]
            gIntro.assign pf
            return ()
          else
            let hallPf ← proveProgAllInstrsExpr allPredExpr fetchProg
            let pf := mkAppN (mkConst plainLem)
              #[predExpr, fetchProg, addrExpr, iExpr, hf, hallPf]
            gIntro.assign pf
            return ()
      throwError "no matching fetch hypothesis"
  return ok?.isSome

public meta def proveAllInstrsImpl : TacticM Unit := do
  let g ← getMainGoal
  if ← tryCloseUniversalFetchGoal g then
    replaceMainGoal []
    return
  let tgt ← instantiateMVars (← g.getType)
  if let some (_, lhsRaw, _) := tgt.eq? then
    let lhs := if lhsRaw.isAppOfArity ``Arm64.Code.allInstrs 2 then
      mkApp2 (mkConst ``Arm64.Program.allInstrs) (lhsRaw.getArg! 0) (lhsRaw.getArg! 1)
    else lhsRaw
    if lhs.isAppOfArity ``Arm64.Program.allInstrs 2 then
      let pf ← proveProgAllInstrsExpr (lhs.getArg! 0) (lhs.getArg! 1)
      g.assign pf
      replaceMainGoal []
      return
    else if lhs.isAppOfArity ``WordTree.allInstrs 2 then
      let p := lhs.getArg! 0
      let treeExpr := lhs.getArg! 1
      if let some (pwFn, pFn, impPf) := ← matchNegInstrPred? p then
        let negPw := mkLambda `w .default (mkApp (mkConst ``BitVec) (mkNatLit 32))
          (mkApp (mkConst ``Bool.not) (mkApp pwFn (.bvar 0)))
        let lhsWords := mkApp2 (mkConst ``WordTree.allWords) negPw treeExpr
        let htPf ← mkEqRefl lhsWords
        let pf := mkAppN (mkConst ``WordTree.allInstrs_of_allWords)
          #[pwFn, pFn, treeExpr, impPf, htPf]
        g.assign pf
        replaceMainGoal []
        return
    let pf ← mkEqRefl lhsRaw
    g.assign pf
    replaceMainGoal []
    return
  throwError "prove_all_instrs: expected concrete boolean equality or fetch exclusion goal, got {tgt}"

/-- Whole-code instruction checker tactic.

    Closes goals of the form:
    - `prog.allInstrs p = true` / `Code.allInstrs p prog = true` / `(prog.rebase b X ...).allInstrs p = true`
    - `tree.allInstrs p = true` / `tree.allWords pw = true`
    - `∀ addr i, prog.fetch addr = some i → ...`
    - `∀ ... addr i, (prog.rebase b X ...).fetch addr = some i → ...`

    Automatically resolves pre-reflected `<prog>_code_eq : <prog>.code = <tree>.toBytes` theorems
    when present (or constructs a balanced `WordTree` from `prog.code` otherwise), rewrites negated
    opcode predicates (`!·.isSvc`, `!·.isSvc0`, `!·.isBrk`, `!·.isMsr`, `!·.isMsrSysreg sr`,
    `!·.isMsrTpidrEl0`) to linear-time bitmask checks on `WordTree` leaves, and discharges the
    resulting concrete boolean equality directly in the Lean kernel (`Eq.refl true`). -/
elab "prove_all_instrs" : tactic => proveAllInstrsImpl

end ProofLib.OpcodeExclusion
