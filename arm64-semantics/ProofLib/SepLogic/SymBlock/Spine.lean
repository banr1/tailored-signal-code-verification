/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.SymBlock.Block
public import ProofLib.Lemmas
import Arm64.Trusted.Spec.SepLogic

/-!
# Write-Spine Presentation for Symbolic Execution

Presents the post-state of reflective whole-block symbolic execution as an ordinary state-update
spine (`spine`, via `changedRegs`, `applyWrites`, `changedVRegs`, and `applyVWrites`) writing only
registers whose symbolic value changed, proves `toState_eq_spine`, and derives `SepWP_block_spine`
and `SepWPp_block_spine`.
-/

@[expose] public section

namespace ProofLib.SymBlock

open Arm64

/-- GPR indices whose symbolic value differs syntactically between `ss0` and `ss`. -/
def changedRegs (ss0 ss : SState) : List Nat :=
  (List.range 31).filter fun i => !decide (ss.reg i = ss0.reg i)

/-- Write `ss.reg i` into `x i` for each listed `i`, in order. -/
def applyWrites (env : Env) (ss : SState) : State → List Nat → State
  | s, [] => s
  | s, i :: t => applyWrites env ss (s.writeReg64 (.gpr (BitVec.ofNat 5 i)) ((ss.reg i).eval env)) t

/-- SIMD/FP register indices whose symbolic value differs syntactically between `ss0` and `ss`. -/
def changedVRegs (ss0 ss : SState) : List Nat :=
  if ss.vregs.isEmpty then [] else (List.range 32).filter fun i => !decide (ss.vreg i = ss0.vreg i)

/-- Write `ss.vreg i` into `v i` for each listed `i`, in order. -/
def applyVWrites (env : Env) (ss : SState) : State → List Nat → State
  | s, [] => s
  | s, i :: t =>
    applyVWrites env ss (s.writeVReg128 (BitVec.ofNat 5 i) ((ss.vreg i).eval env)) t

/-- Final state presented as an update spine over entry state `s`. -/
def spine (ss0 ss : SState) (b : BitVec 64) (env : Env) (s : State) (m : Memory) : State :=
  let s1 := applyWrites env ss s (changedRegs ss0 ss)
  let s2 := applyVWrites env ss s1 (changedVRegs ss0 ss)
  let s3 := if ss.sp = ss0.sp then s2 else s2.writeReg64 .sp (ss.sp.eval env)
  let s4 := if ss.tpidr = ss0.tpidr then s3 else ProofLib.setTpidrEl0 s3 (ss.tpidr.eval env)
  let s5 := if ss.flags = ss0.flags then s4 else s4.setPState (ss.flags.denote env s.pstate)
  ((s5.setPC (ss.pc.denote b env)).setMem m)

/-- Symbolic counterpart of `applyWrites`. -/
def copyRegs (ss : SState) : SState → List Nat → SState
  | a, [] => a
  | a, i :: t => copyRegs ss (a.setReg64 (.gpr (BitVec.ofNat 5 i)) (ss.reg i)) t

/-- Symbolic counterpart of `applyVWrites`. -/
def copyVRegs (ss : SState) : SState → List Nat → SState
  | a, [] => a
  | a, i :: t => copyVRegs ss (a.setVReg128 (BitVec.ofNat 5 i) (ss.vreg i)) t

namespace SState

variable {b : BitVec 64} {env : Env} {s0 : State} {m : Memory}

theorem setReg64_reg_gpr {a : SState} {i k : Nat} {e : SExpr} (hlen : a.regs.length = 31)
    (hi : i < 31) (hk : k < 31) :
    (a.setReg64 (.gpr (BitVec.ofNat 5 i)) e).reg k = if k = i then e else a.reg k := by
  have h31 : BitVec.ofNat 5 i ≠ 31#5 := by
    intro h; have := congrArg BitVec.toNat h; simp at this; omega
  have htn : (BitVec.ofNat 5 i).toNat = i := by simp; omega
  simp only [setReg64, h31, ite_false, reg, htn, List.getD_eq_getElem?_getD]
  by_cases hki : k = i
  · subst hki; simp [hlen, hk]
  · simp [hki, Ne.symm hki]

theorem setVReg128_vreg {a : SState} {i k : Nat} {ve : VExpr} (hvlen : a.vregs.length = 32)
    (hi : i < 32) (hk : k < 32) :
    (a.setVReg128 (BitVec.ofNat 5 i) ve).vreg k = if k = i then ve else a.vreg k := by
  have htn : (BitVec.ofNat 5 i).toNat = i := by simp; omega
  simp only [setVReg128, vreg, htn, List.getD_eq_getElem?_getD]
  by_cases hki : k = i
  · subst hki; simp [hvlen, hk]
  · simp [hki, Ne.symm hki]

theorem copyRegs_fields (ss : SState) :
    ∀ (a : SState) (l : List Nat),
      (copyRegs ss a l).vregs = a.vregs ∧ (copyRegs ss a l).sp = a.sp ∧
      (copyRegs ss a l).tpidr = a.tpidr ∧ (copyRegs ss a l).pc = a.pc ∧
      (copyRegs ss a l).flags = a.flags ∧ (copyRegs ss a l).regs.length = a.regs.length
  | a, [] => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | a, i :: t => by
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ :=
      copyRegs_fields ss (a.setReg64 (.gpr (BitVec.ofNat 5 i)) (ss.reg i)) t
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [copyRegs, h1]; exact setReg64_vregs _ _ _
    · rw [copyRegs, h2]; by_cases h : BitVec.ofNat 5 i = 31#5 <;> simp [setReg64, h]
    · rw [copyRegs, h3]; by_cases h : BitVec.ofNat 5 i = 31#5 <;> simp [setReg64, h]
    · rw [copyRegs, h4]; exact setReg64_pc _ _ _
    · rw [copyRegs, h5]; exact setReg64_flags _ _ _
    · rw [copyRegs, h6]; exact setReg64_length _ _ _

theorem copyRegs_reg (ss : SState) {k : Nat} (hk : k < 31) :
    ∀ (a : SState) (l : List Nat), a.regs.length = 31 → (∀ i ∈ l, i < 31) →
      (copyRegs ss a l).reg k = if k ∈ l then ss.reg k else a.reg k
  | a, [], _, _ => by simp [copyRegs]
  | a, i :: t, hlen, hl => by
    have hi : i < 31 := hl i (by simp)
    rw [copyRegs, copyRegs_reg ss hk _ t (by rw [setReg64_length, hlen]) (fun j hj => hl j (by simp [hj])),
      setReg64_reg_gpr hlen hi hk]
    by_cases hkt : k ∈ t
    · simp [hkt]
    · by_cases hki : k = i
      · subst hki; simp
      · simp [hkt, hki]

theorem copyVRegs_fields (ss : SState) :
    ∀ (a : SState) (l : List Nat),
      (copyVRegs ss a l).regs = a.regs ∧ (copyVRegs ss a l).sp = a.sp ∧
      (copyVRegs ss a l).tpidr = a.tpidr ∧ (copyVRegs ss a l).pc = a.pc ∧
      (copyVRegs ss a l).flags = a.flags ∧ (copyVRegs ss a l).vregs.length = a.vregs.length
  | a, [] => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | a, i :: t => by
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ :=
      copyVRegs_fields ss (a.setVReg128 (BitVec.ofNat 5 i) (ss.vreg i)) t
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [copyVRegs, h1]; rfl
    · rw [copyVRegs, h2]; rfl
    · rw [copyVRegs, h3]; rfl
    · rw [copyVRegs, h4]; rfl
    · rw [copyVRegs, h5]; rfl
    · rw [copyVRegs, h6]; exact setVReg128_length _ _ _

theorem copyVRegs_vreg (ss : SState) {k : Nat} (hk : k < 32) :
    ∀ (a : SState) (l : List Nat), a.vregs.length = 32 → (∀ i ∈ l, i < 32) →
      (copyVRegs ss a l).vreg k = if k ∈ l then ss.vreg k else a.vreg k
  | a, [], _, _ => by simp [copyVRegs]
  | a, i :: t, hvlen, hl => by
    have hi : i < 32 := hl i (by simp)
    rw [copyVRegs,
      copyVRegs_vreg ss hk _ t (by rw [setVReg128_length, hvlen]) (fun j hj => hl j (by simp [hj])),
      setVReg128_vreg hvlen hi hk]
    by_cases hkt : k ∈ t
    · simp [hkt]
    · by_cases hki : k = i
      · subst hki; simp
      · simp [hkt, hki]

theorem applyWrites_toState (ss : SState) :
    ∀ (a : SState) (l : List Nat), a.regs.length = 31 →
      applyWrites env ss (a.toState b env s0 m) l = (copyRegs ss a l).toState b env s0 m
  | a, [], _ => rfl
  | a, i :: t, hlen => by
    rw [applyWrites, toState_writeReg64 a hlen, copyRegs]
    exact applyWrites_toState ss _ t (by rw [setReg64_length, hlen])

theorem applyVWrites_toState (ss : SState) :
    ∀ (a : SState) (l : List Nat), l = [] ∨ a.vregs.length = 32 →
      applyVWrites env ss (a.toState b env s0 m) l = (copyVRegs ss a l).toState b env s0 m
  | a, [], _ => rfl
  | a, i :: t, hl => by
    have hvlen : a.vregs.length = 32 := hl.resolve_left (by simp)
    rw [applyVWrites, toState_writeVReg128 a hvlen, copyVRegs]
    exact applyVWrites_toState ss _ t (Or.inr (by rw [setVReg128_length, hvlen]))

theorem toState_congr {ss1 ss2 : SState} (hr : ∀ k < 31, ss1.reg k = ss2.reg k)
    (hv : ss1.vregs = ss2.vregs ∨
      (ss1.vregs.length = 32 ∧ ss2.vregs.length = 32 ∧ ∀ k < 32, ss1.vreg k = ss2.vreg k))
    (hsp : ss1.sp = ss2.sp) (htpidr : ss1.tpidr = ss2.tpidr)
    (hpc : ss1.pc = ss2.pc) (hfl : ss1.flags = ss2.flags) :
    ss1.toState b env s0 m = ss2.toState b env s0 m := by
  unfold toState
  rw [hsp, htpidr, hpc, hfl]
  simp only [State.mk.injEq, and_true]
  refine ⟨?_, ?_⟩
  · simp only [RegFile.mk.injEq]
    funext j
    split
    · rfl
    · rename_i hj
      have : j.toNat < 31 := by
        have := j.isLt; have : j.toNat ≠ 31 := fun h => hj (BitVec.eq_of_toNat_eq (by simpa using h))
        omega
      rw [hr _ this]
  · rcases hv with hveq | ⟨hl1, hl2, hvk⟩
    · rw [hveq]
    · simp only [VRegFile.mk.injEq]
      funext j
      have hj1 : j.toNat < ss1.vregs.length := hl1 ▸ j.isLt
      have hj2 : j.toNat < ss2.vregs.length := hl2 ▸ j.isLt
      rw [List.getElem?_eq_getElem hj1, List.getElem?_eq_getElem hj2]
      dsimp only
      have hvkj := hvk j.toNat j.isLt
      simp only [vreg, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj1,
        List.getElem?_eq_getElem hj2, Option.getD_some] at hvkj
      rw [hvkj]

end SState

open SState in
theorem toState_eq_spine {ss0 ss : SState} {b : BitVec 64} {env : Env} {s : State} (m : Memory)
    (hlen0 : ss0.regs.length = 31) (hvval0 : VRegsValid ss0.vregs)
    (hvlen_eq : ss.vregs.length = ss0.vregs.length) (hs : ss0.toState b env s s.mem = s) :
    ss.toState b env s m = spine ss0 ss b env s m := by
  have hl : ∀ i ∈ changedRegs ss0 ss, i < 31 := by
    intro i hi; simp only [changedRegs, List.mem_filter, List.mem_range] at hi; exact hi.1
  have hlV : ∀ i ∈ changedVRegs ss0 ss, i < 32 := by
    intro i hi
    unfold changedVRegs at hi
    split at hi
    · simp at hi
    · simp only [List.mem_filter, List.mem_range] at hi; exact hi.1
  have hA : applyWrites env ss s (changedRegs ss0 ss) =
      (copyRegs ss ss0 (changedRegs ss0 ss)).toState b env s s.mem := by
    have := applyWrites_toState (b := b) (env := env) (s0 := s) (m := s.mem) ss ss0
      (changedRegs ss0 ss) hlen0
    rwa [hs] at this
  obtain ⟨hXvregs, hXsp, hXtpidr, hXpc, hXfl, hXlen⟩ := copyRegs_fields ss ss0 (changedRegs ss0 ss)
  have hXreg : ∀ k < 31, (copyRegs ss ss0 (changedRegs ss0 ss)).reg k = ss.reg k := by
    intro k hk
    rw [copyRegs_reg ss hk ss0 _ hlen0 hl]
    split
    · rfl
    · rename_i hn
      simp only [changedRegs, List.mem_filter, List.mem_range, hk, true_and,
        Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at hn
      exact (Classical.not_not.mp hn).symm
  have hAV_pre : changedVRegs ss0 ss = [] ∨
      (copyRegs ss ss0 (changedRegs ss0 ss)).vregs.length = 32 := by
    rcases hvval0 with h0 | h32
    · left
      have hemp : ss.vregs = [] := List.eq_nil_of_length_eq_zero (by rw [hvlen_eq, h0]; rfl)
      simp [changedVRegs, hemp]
    · right; rw [hXvregs, h32]
  have hAV : applyVWrites env ss ((copyRegs ss ss0 (changedRegs ss0 ss)).toState b env s s.mem)
      (changedVRegs ss0 ss) =
      (copyVRegs ss (copyRegs ss ss0 (changedRegs ss0 ss)) (changedVRegs ss0 ss)).toState
        b env s s.mem :=
    applyVWrites_toState ss _ _ hAV_pre
  obtain ⟨hYregs, hYsp, hYtpidr, hYpc, hYfl, hYvlen⟩ :=
    copyVRegs_fields ss (copyRegs ss ss0 (changedRegs ss0 ss)) (changedVRegs ss0 ss)
  have hYreg : ∀ k < 31,
      (copyVRegs ss (copyRegs ss ss0 (changedRegs ss0 ss)) (changedVRegs ss0 ss)).reg k = ss.reg k := by
    intro k hk; simp only [reg, hYregs]; exact hXreg k hk
  have hYv :
      (copyVRegs ss (copyRegs ss ss0 (changedRegs ss0 ss)) (changedVRegs ss0 ss)).vregs = ss.vregs ∨
      ((copyVRegs ss (copyRegs ss ss0 (changedRegs ss0 ss)) (changedVRegs ss0 ss)).vregs.length = 32 ∧
        ss.vregs.length = 32 ∧
        ∀ k < 32, (copyVRegs ss (copyRegs ss ss0 (changedRegs ss0 ss)) (changedVRegs ss0 ss)).vreg k =
          ss.vreg k) := by
    rcases hvval0 with h0 | h32
    · left
      have hemp : ss.vregs = [] := List.eq_nil_of_length_eq_zero (by rw [hvlen_eq, h0]; rfl)
      have hcv : changedVRegs ss0 ss = [] := by simp [changedVRegs, hemp]
      simp [hcv, copyVRegs, hXvregs, h0, hemp]
    · right
      have h32' : ss.vregs.length = 32 := hvlen_eq.trans h32
      refine ⟨by rw [hYvlen, hXvregs, h32], h32', fun k hk => ?_⟩
      rw [copyVRegs_vreg ss hk _ _ (by rw [hXvregs, h32]) hlV]
      split
      · rfl
      · rename_i hn
        have hne : ss.vregs.isEmpty = false := by
          cases hvr : ss.vregs with
          | nil => simp [hvr] at h32'
          | cons _ _ => rfl
        simp only [changedVRegs, hne, Bool.false_eq_true, ite_false, List.mem_filter,
          List.mem_range, hk, true_and, Bool.not_eq_eq_eq_not, Bool.not_true,
          decide_eq_false_iff_not] at hn
        have hXk : (copyRegs ss ss0 (changedRegs ss0 ss)).vreg k = ss0.vreg k := by
          simp [vreg, hXvregs]
        rw [hXk]
        exact (Classical.not_not.mp hn).symm
  unfold spine
  dsimp only
  rw [hA, hAV]
  generalize copyVRegs ss (copyRegs ss ss0 (changedRegs ss0 ss)) (changedVRegs ss0 ss) = Y
    at hYregs hYsp hYtpidr hYpc hYfl hYvlen hYreg hYv
  have hYlen : Y.regs.length = 31 := by rw [hYregs, hXlen, hlen0]
  let Z1 := if ss.sp = ss0.sp then Y else Y.setReg64 .sp ss.sp
  have hZ1 : (if ss.sp = ss0.sp then Y.toState b env s s.mem
      else (Y.toState b env s s.mem).writeReg64 .sp (ss.sp.eval env)) =
      Z1.toState b env s s.mem := by
    dsimp only [Z1]
    by_cases hsp : ss.sp = ss0.sp
    · simp [hsp]
    · simp only [hsp, ite_false]
      exact toState_writeReg64 Y hYlen .sp ss.sp
  have hZ1_sp : Z1.sp = ss.sp := by
    dsimp only [Z1]; by_cases hsp : ss.sp = ss0.sp <;> simp [hsp, hYsp, hXsp, setReg64]
  have hZ1_reg : ∀ k < 31, Z1.reg k = ss.reg k := by
    intro k hk; dsimp only [Z1]
    by_cases hsp : ss.sp = ss0.sp <;> simp only [hsp, ite_true, ite_false, setReg64, reg] <;> exact hYreg k hk
  have hZ1_v : Z1.vregs = ss.vregs ∨
      (Z1.vregs.length = 32 ∧ ss.vregs.length = 32 ∧ ∀ k < 32, Z1.vreg k = ss.vreg k) := by
    dsimp only [Z1]; by_cases hsp : ss.sp = ss0.sp <;> simp only [hsp, ite_true, ite_false, setReg64] <;> exact hYv
  have hZ1_tpidr : Z1.tpidr = ss0.tpidr := by
    dsimp only [Z1]; by_cases hsp : ss.sp = ss0.sp <;> simp [hsp, hYtpidr, hXtpidr, setReg64]
  have hZ1_pc : Z1.pc = ss0.pc := by
    dsimp only [Z1]; by_cases hsp : ss.sp = ss0.sp <;> simp [hsp, hYpc, hXpc, setReg64]
  have hZ1_fl : Z1.flags = ss0.flags := by
    dsimp only [Z1]; by_cases hsp : ss.sp = ss0.sp <;> simp [hsp, hYfl, hXfl, setReg64]
  let Z2 := if ss.tpidr = ss0.tpidr then Z1 else Z1.setTpidr ss.tpidr
  have hZ2 : (if ss.tpidr = ss0.tpidr then Z1.toState b env s s.mem
      else ProofLib.setTpidrEl0 (Z1.toState b env s s.mem) (ss.tpidr.eval env)) =
      Z2.toState b env s s.mem := by
    dsimp only [Z2]; by_cases ht : ss.tpidr = ss0.tpidr <;> simp [ht, ProofLib.setTpidrEl0, toState, setTpidr]
  have hZ2_tpidr : Z2.tpidr = ss.tpidr := by
    dsimp only [Z2]; by_cases ht : ss.tpidr = ss0.tpidr <;> simp [ht, hZ1_tpidr, setTpidr]
  have hZ2_reg : ∀ k < 31, Z2.reg k = ss.reg k := by
    intro k hk; dsimp only [Z2]; by_cases ht : ss.tpidr = ss0.tpidr <;> simp only [ht, ite_true, ite_false, setTpidr, reg] <;> exact hZ1_reg k hk
  have hZ2_v : Z2.vregs = ss.vregs ∨
      (Z2.vregs.length = 32 ∧ ss.vregs.length = 32 ∧ ∀ k < 32, Z2.vreg k = ss.vreg k) := by
    dsimp only [Z2]; by_cases ht : ss.tpidr = ss0.tpidr <;> simp only [ht, ite_true, ite_false, setTpidr] <;> exact hZ1_v
  have hZ2_sp : Z2.sp = ss.sp := by
    dsimp only [Z2]; by_cases ht : ss.tpidr = ss0.tpidr <;> simp [ht, hZ1_sp, setTpidr]
  have hZ2_pc : Z2.pc = ss0.pc := by
    dsimp only [Z2]; by_cases ht : ss.tpidr = ss0.tpidr <;> simp [ht, hZ1_pc, setTpidr]
  have hZ2_fl : Z2.flags = ss0.flags := by
    dsimp only [Z2]; by_cases ht : ss.tpidr = ss0.tpidr <;> simp [ht, hZ1_fl, setTpidr]
  let Z3 := if ss.flags = ss0.flags then Z2 else { Z2 with flags := ss.flags }
  have hZ3 : (if ss.flags = ss0.flags then Z2.toState b env s s.mem
      else (Z2.toState b env s s.mem).setPState (ss.flags.denote env s.pstate)) =
      Z3.toState b env s s.mem := by
    dsimp only [Z3]; by_cases hf : ss.flags = ss0.flags <;> simp [hf, State.setPState, toState]
  have hZ3_fl : Z3.flags = ss.flags := by
    dsimp only [Z3]; by_cases hf : ss.flags = ss0.flags <;> simp [hf, hZ2_fl]
  have hZ3_reg : ∀ k < 31, Z3.reg k = ss.reg k := by
    intro k hk; dsimp only [Z3]; by_cases hf : ss.flags = ss0.flags <;> simp only [hf, ite_true, ite_false, reg] <;> exact hZ2_reg k hk
  have hZ3_v : Z3.vregs = ss.vregs ∨
      (Z3.vregs.length = 32 ∧ ss.vregs.length = 32 ∧ ∀ k < 32, Z3.vreg k = ss.vreg k) := by
    dsimp only [Z3]; by_cases hf : ss.flags = ss0.flags <;> simp only [hf, ite_true, ite_false] <;> exact hZ2_v
  have hZ3_sp : Z3.sp = ss.sp := by
    dsimp only [Z3]; by_cases hf : ss.flags = ss0.flags <;> simp [hf, hZ2_sp]
  have hZ3_tpidr : Z3.tpidr = ss.tpidr := by
    dsimp only [Z3]; by_cases hf : ss.flags = ss0.flags <;> simp [hf, hZ2_tpidr]
  have hZ3_pc : Z3.pc = ss0.pc := by
    dsimp only [Z3]; by_cases hf : ss.flags = ss0.flags <;> simp [hf, hZ2_pc]
  rw [hZ1, hZ2, hZ3, toState_setPC, toState_setMem]
  exact toState_congr (fun k hk => (hZ3_reg k hk).symm)
    (match hZ3_v with
     | Or.inl hveq => Or.inl hveq.symm
     | Or.inr ⟨h1, h2, h3⟩ => Or.inr ⟨h2, h1, fun k hk => (h3 k hk).symm⟩)
    hZ3_sp.symm hZ3_tpidr.symm rfl hZ3_fl.symm

/-- Block rule with the continuation over the write spine (`SepWP`). -/
theorem SepWP_block_spine {prog : Program} {tgt b : BitVec 64} {env : Env} {tbl : Tbl}
    {hints : List Hint} {ss0 ssF : SState} {obl : List SProp} {s : State} {P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp} (base : SExpr) (hbase : base.eval env = b)
    (htbl : TblOK prog b env tbl) (hlen : ss0.regs.length = 31) (hvval : VRegsValid ss0.vregs)
    (hvlen_eq : ssF.vregs.length = ss0.vregs.length)
    (hs : ss0.toState b env s s.mem = s) (hP : P = cellsProp env ss0.cells)
    (hrun : run base tbl hints ss0 = some (ssF, obl)) (hobl : allHold env obl)
    (hnext : ∀ m, SepWP prog tgt (spine ss0 ssF b env s m) (cellsProp env ssF.cells) post oom) :
    SepWP prog tgt s P post oom :=
  SepWP_block hbase htbl hlen hvval hs hP hrun hobl fun m => by
    rw [toState_eq_spine m hlen hvval hvlen_eq hs]; exact hnext m

/-- Panic-aware block rule with the continuation over the write spine (`SepWPp`). -/
theorem SepWPp_block_spine {prog : Program} {ret b : BitVec 64} {env : Env} {tbl : Tbl}
    {hints : List Hint} {ss0 ssF : SState} {obl : List SProp} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp} (base : SExpr) (hbase : base.eval env = b)
    (htbl : TblOK prog b env tbl) (hlen : ss0.regs.length = 31) (hvval : VRegsValid ss0.vregs)
    (hvlen_eq : ssF.vregs.length = ss0.vregs.length)
    (hs : ss0.toState b env s s.mem = s) (hP : P = cellsProp env ss0.cells)
    (hrun : run base tbl hints ss0 = some (ssF, obl)) (hobl : allHold env obl)
    (hnext : ∀ m, SepWPp prog ret (spine ss0 ssF b env s m) (cellsProp env ssF.cells) Q Qp oom) :
    SepWPp prog ret s P Q Qp oom :=
  SepWPp_block hbase htbl hlen hvval hs hP hrun hobl fun m => by
    rw [toState_eq_spine m hlen hvval hvlen_eq hs]; exact hnext m
