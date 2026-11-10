/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Defs

/-!
# Budget-Threaded `try_decrypt_from_record` Callee Specifications

Defines budget-threaded specifications over `RustCliAllocBudget M` for:
1. `dropSessionStructureLocal2Spec` (block `139`, `FreeOnlyEvs`);
2. `dropSessionStructureLocal1Spec` (block `13`, `FreeOnlyEvs`);
3. `setSessionStateSpec` (block `80`, `FreeOnlyEvs`);
4. `growOneSpeCondSpec` and `growOneSpeSpec` (block `75`, `(elemSz, minCap, align) = (48, 4, 8)`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget

open Arm64 ProofLib SepProp
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap sessionStateAt)
open CryptoVerification.LibsignalSession (GrowGhost)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (
  DropSessionStructureGhost SetSessionStateGhost
  dropSessionStructureLocal2Stack dropSessionStructureLocal1Stack
  setSessionStateStack growOneSpeStack
)
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget
  FitsEvents FitsEnv FreeOnlyEvs OomPreserved NullAllowed RustLayoutOk AllocCallPreserved
  not_nullAllowed_of_fitsAllocEvents not_nullAllowed_of_fitsReallocEvents
  rustAllocEvents rustReallocEvents
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rawVecNewCap rawVecGrowEvents)
open CryptoVerification (LibsignalPlacement)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)

/-! ## 1. `drop_glue<SessionStructure> [local#2]` (Block `139`) -/

/-- Budget-threaded specification of `core::ptr::drop_glue::<SessionStructure> [local#2]`
    (Block `139`, `FreeOnlyEvs`, `0` `FitsEnv`). -/
def dropSessionStructureLocal2Spec [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (DropSessionStructureGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.ss ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      sessionStateAt A.repAlloc x.ss x.G x.st ∗ A.pool lim st s ∗
      stackAt s.sp dropSessionStructureLocal2Stack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ FreeOnlyEvs evs⌝ ∗
        memRegion x.ss 344 ∗ A.pool lim (M.stepEvents evs st) sf ∗
        stackAt s0.sp dropSessionStructureLocal2Stack

/-! ## 2. `drop_glue<SessionStructure> [local#1]` (Block `13`) -/

/-- Budget-threaded specification of `core::ptr::drop_glue::<SessionStructure> [local#1]`
    (Block `13`, `FreeOnlyEvs`, `0` `FitsEnv`). -/
def dropSessionStructureLocal1Spec [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (DropSessionStructureGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.ss ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      sessionStateAt A.repAlloc x.ss x.G x.st ∗ A.pool lim st s ∗
      stackAt s.sp dropSessionStructureLocal1Stack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ FreeOnlyEvs evs⌝ ∗
        memRegion x.ss 344 ∗ A.pool lim (M.stepEvents evs st) sf ∗
        stackAt s0.sp dropSessionStructureLocal1Stack

/-! ## 3. `SessionRecord::set_session_state` (Block `80`) -/

/-- Budget-threaded specification of `<SessionRecord>::set_session_state`
    (Block `80`, `FreeOnlyEvs`, `evs = []` when `x.cur = none`). -/
def setSessionStateSpec (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (SetSessionStateGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.record ∧ s.readReg64 .x1 = x.src ∧ x.bs.length = 344⌝ ∗
      (match x.cur with
       | none => ((x.record + 0x18#64) ↦₆₄ noneCap) ∗ memRegion (x.record + 0x20#64) 336
       | some (G, ss) => sessionStateAt A.repAlloc (x.record + 0x18#64) G ss) ∗
      (x.src ↦ₛ x.bs) ∗ A.pool lim st s ∗ stackAt s.sp setSessionStateStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ FreeOnlyEvs evs ∧ (x.cur = none → evs = [])⌝ ∗
        ((x.record + 0x18#64) ↦ₛ x.bs) ∗ (x.src ↦ₛ x.bs) ∗
        A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp setSessionStateStack

/-! ## 4. `RawVec<SignalProtocolError>::grow_one` (Block `75`, `(elemSz, minCap, align) = (48, 4, 8)`) -/

/-- Deterministic `AllocEvent` list emitted by `RawVec<SignalProtocolError>::grow_one`. -/
abbrev growOneSpeEvents (cap : BitVec 64) : List AllocEvent :=
  rawVecGrowEvents 48 4 8 cap

/-- Allocation envelope for `RawVec<SignalProtocolError>::grow_one`. -/
def GrowOneSpeEnv (cap : BitVec 64) (evs : List AllocEvent) : Prop :=
  (cap = 0#64 ∧ evs = rustAllocEvents (4 * 48) 8) ∨
  (cap ≠ 0#64 ∧ evs = rustReallocEvents (cap.toNat * 48) (max (2 * cap.toNat) 4 * 48) 8)

theorem growOneSpeEnv_events (cap : BitVec 64) :
    GrowOneSpeEnv cap (growOneSpeEvents cap) := by
  unfold GrowOneSpeEnv growOneSpeEvents rawVecGrowEvents rawVecNewCap
  by_cases h : cap = 0#64
  · simp only [h, ↓reduceIte, true_and, true_or]
  · exact Or.inr ⟨h, by simp only [h, ↓reduceIte]⟩

theorem growOneSpeEvents_eq_of_env {cap : BitVec 64} {evs : List AllocEvent}
    (h : GrowOneSpeEnv cap evs) :
    evs = growOneSpeEvents cap := by
  unfold growOneSpeEvents rawVecGrowEvents rawVecNewCap
  rcases h with ⟨hz, rfl⟩ | ⟨hnz, rfl⟩
  · simp only [hz, ↓reduceIte]
  · simp only [hnz, ↓reduceIte]

/-- Conditional-OOM budget-threaded contract for `RawVec<SignalProtocolError>::grow_one`
    (retaining the explicit `CapacityOverflow` / `NullAllowed` panic and conditional `onOom`). -/
def growOneSpeCondSpec (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (GrowGhost × M.σ) where
  pre := fun ((v, cap, ptr, bs), st) s =>
    ⌜s.readReg64 .x0 = v ∧ bs.length = cap.toNat * 48 ∧ ptr ≠ 0 ∧
      cap.toNat * 48 < 2 ^ 63⌝ ∗
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
    (if cap = 0 then emp else A.live ptr bs.length 8 ∗ (ptr ↦ₛ bs)) ∗
    A.pool lim st s ∗ stackAt s.sp growOneSpeStack
  post := fun ((v, cap, _, bs), st) s0 sf =>
    let newCap := max (2 * cap.toNat) 4
    ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ p' : BitVec 64,
      ⌜p' ≠ 0 ∧ p'.toNat % 8 = 0⌝ ∗
      (v ↦₆₄ BitVec.ofNat 64 newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
      A.live p' (newCap * 48) 8 ∗ (p' ↦ₛ bs) ∗
      memRegion (p' + BitVec.ofNat 64 bs.length) ((newCap - cap.toNat) * 48)) ∗
    A.pool lim (M.stepEvents (growOneSpeEvents cap) st) sf ∗
    stackAt s0.sp growOneSpeStack
  onPanic := fun ((_, cap, _, _), _) s0 sf =>
    let newBytes := max (2 * cap.toNat) 4 * 48
    ⌜(¬ RustLayoutOk newBytes 8 ∨ NullAllowed newBytes 8) ∧
      sf.fs = s0.fs ∧ sf.trace = s0.trace⌝ ∗ anyHeap
  onOom := fun ((_, cap, _, _), st) s0 sf =>
    let newBytes := max (2 * cap.toNat) 4 * 48
    ⌜RustLayoutOk newBytes 8 ∧
      ¬ FitsEvents M lim st (growOneSpeEvents cap) ∧
      OomPreserved s0 sf⌝

/-- Envelope total-correctness (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`) contract for
    `RawVec<SignalProtocolError>::grow_one` under `max (2 * cap.toNat) 4 * 48 + 8 ≤ 2 ^ 63`
    and `FitsEnv M lim st (GrowOneSpeEnv cap)`. -/
def growOneSpeSpec (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (GrowGhost × M.σ) where
  pre := fun ((v, cap, ptr, bs), st) s =>
    ⌜s.readReg64 .x0 = v ∧ bs.length = cap.toNat * 48 ∧ ptr ≠ 0 ∧
      max (2 * cap.toNat) 4 * 48 + 8 ≤ 2 ^ 63 ∧
      FitsEnv M lim st (GrowOneSpeEnv cap)⌝ ∗
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
    (if cap = 0 then emp else A.live ptr bs.length 8 ∗ (ptr ↦ₛ bs)) ∗
    A.pool lim st s ∗ stackAt s.sp growOneSpeStack
  post := fun ((v, cap, _, bs), st) s0 sf =>
    let newCap := max (2 * cap.toNat) 4
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ GrowOneSpeEnv cap evs⌝ ∗
      (∃∗ p' : BitVec 64,
        ⌜p' ≠ 0 ∧ p'.toNat % 8 = 0⌝ ∗
        (v ↦₆₄ BitVec.ofNat 64 newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
        A.live p' (newCap * 48) 8 ∗ (p' ↦ₛ bs) ∗
        memRegion (p' + BitVec.ofNat 64 bs.length) ((newCap - cap.toNat) * 48)) ∗
      A.pool lim (M.stepEvents evs st) sf ∗
      stackAt s0.sp growOneSpeStack

theorem subroutine_ok_growOneSpe_of_cond {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {P : Program} {entry : BitVec 64}
    (h : subroutine_ok P entry (growOneSpeCondSpec M A lim)) :
    subroutine_ok P entry (growOneSpeSpec M A lim) := by
  apply subroutine_ok.of_codeLoaded
  rintro ⟨⟨v, cap, ptr, bs⟩, st⟩ R s0 hpc hrun hpre hsp _
  dsimp only [growOneSpeSpec] at hpre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc,
      sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hbs, hptr, hfit63, hEnv⟩, hrest⟩
  have hFit : FitsEvents M lim st (growOneSpeEvents cap) :=
    hEnv (growOneSpeEvents cap) (growOneSpeEnv_events cap)
  have hcap63 : cap.toNat * 48 < 2 ^ 63 := by omega
  have hlay : RustLayoutOk (max (2 * cap.toNat) 4 * 48) 8 := by
    refine ⟨⟨by omega, ⟨3, rfl⟩, by omega⟩, by decide⟩
  have hpreC : s0.mem ⊨ (growOneSpeCondSpec M A lim).pre ((v, cap, ptr, bs), st) s0 ∗ R := by
    dsimp only [growOneSpeCondSpec]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc,
        sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hbs, hptr, hcap63⟩, hrest⟩
  refine subroutine_ok.mono_outcome h ((v, cap, ptr, bs), st) R s0 hpc hrun hpreC hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hex⟩ | ⟨ho, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [growOneSpeCondSpec] at hpost
    dsimp only [growOneSpeSpec]
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨growOneSpeEvents cap, ?_⟩
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨⟨hpost.1, growOneSpeEnv_events cap⟩, hpost.2⟩
  · dsimp only [growOneSpeCondSpec] at hpan
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpan
    rcases hpan.1.1 with hnlay | hna
    · exact False.elim (hnlay hlay)
    · exfalso
      unfold growOneSpeEvents rawVecGrowEvents rawVecNewCap at hFit
      by_cases hc0 : cap = 0#64
      · subst hc0
        simp only [↓reduceIte] at hFit
        have hmx : max (2 * (0#64 : BitVec 64).toNat) 4 * 48 = 4 * 48 := by decide
        rw [hmx] at hlay hna
        exact not_nullAllowed_of_fitsAllocEvents hlay hFit hna
      · simp only [hc0, ↓reduceIte] at hFit
        exact not_nullAllowed_of_fitsReallocEvents hlay hFit hna
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hex⟩))
  · dsimp only [growOneSpeCondSpec] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim (hoom.1.2.1 hFit)

end LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
