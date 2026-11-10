/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Proofs.ConsumeMessageKey.Defs
public import LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.ConsumeCodeSym

/-!
# Budget-Threaded Callee Specifications for `RatchetState::consume_message_key`

`VmPreserved` and `RustCliAllocBudget M` specifications for `hmac_sha256` and
`RawVec<MessageKey>::grow_one` (`stride = 104`, `minCap = 4`, `align = 8`), plus allocator hook
forwarding across `sessionExterns`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.ConsumeMessageKey.DefsBudget

open Arm64 ProofLib SepProp
open CryptoGames.HMAC (ShaState)
open CryptoVerification (LibsignalPlacement lsmpl withLsCodeLoaded blkPC_24 blkPl_24)
open CryptoVerification.LibsignalSession (
  HmacGhost GrowGhost sessionExterns
)
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget
  FitsEvents FitsEnv OomPreserved NullAllowed RustLayoutOk
  not_nullAllowed_of_fitsAllocEvents not_nullAllowed_of_fitsReallocEvents
  rustAllocEvents rustReallocEvents
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rawVecNewCap rawVecGrowEvents)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved AllocHooksBudget)

/-! ## `crypto::hmac_sha256` -/

def hmacSpec (F : ShaState → List (BitVec 8) → ShaState) : Spec HmacGhost :=
  withVmPreserved (CryptoVerification.LibsignalSession.hmacSpec F)

/-! ## `RawVec<MessageKey>::grow_one` -/

abbrev growOneEvents (cap : BitVec 64) : List AllocEvent :=
  rawVecGrowEvents 104 4 8 cap

/-- Allocation-event envelope for `RawVec<MessageKey>::grow_one`. -/
def GrowOneEnv (cap : BitVec 64) (evs : List AllocEvent) : Prop :=
  (cap = 0#64 ∧ evs = rustAllocEvents (4 * 104) 8) ∨
  (cap ≠ 0#64 ∧ evs = rustReallocEvents (cap.toNat * 104) (max (2 * cap.toNat) 4 * 104) 8)

theorem growOneEnv_events (cap : BitVec 64) :
    GrowOneEnv cap (growOneEvents cap) := by
  unfold GrowOneEnv growOneEvents rawVecGrowEvents rawVecNewCap
  by_cases h : cap = 0#64
  · simp only [h, ↓reduceIte, true_and, true_or]
  · exact Or.inr ⟨h, by simp only [h, ↓reduceIte]⟩

theorem growOneEvents_eq_of_env {cap : BitVec 64} {evs : List AllocEvent}
    (h : GrowOneEnv cap evs) :
    evs = growOneEvents cap := by
  unfold growOneEvents rawVecGrowEvents rawVecNewCap
  rcases h with ⟨hz, rfl⟩ | ⟨hnz, rfl⟩
  · simp only [hz, ↓reduceIte]
  · simp only [hnz, ↓reduceIte]

/-- Conditional-OOM budget-threaded contract for `RawVec<MessageKey>::grow_one`. -/
def growOneCondSpec (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (GrowGhost × M.σ) where
  pre := fun ((v, cap, ptr, bs), st) s =>
    ⌜s.readReg64 .x0 = v ∧ bs.length = cap.toNat * 104 ∧ ptr ≠ 0 ∧
      cap.toNat * 104 < 2 ^ 63⌝ ∗
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
    (if cap = 0 then emp else A.live ptr bs.length 8 ∗ (ptr ↦ₛ bs)) ∗
    A.pool lim st s ∗ stackAt s.sp 4608
  post := fun ((v, cap, _, bs), st) s0 sf =>
    let newCap := max (2 * cap.toNat) 4
    ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ p' : BitVec 64,
      ⌜p' ≠ 0 ∧ p'.toNat % 8 = 0⌝ ∗
      (v ↦₆₄ BitVec.ofNat 64 newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
      A.live p' (newCap * 104) 8 ∗ (p' ↦ₛ bs) ∗
      memRegion (p' + BitVec.ofNat 64 bs.length) ((newCap - cap.toNat) * 104)) ∗
    A.pool lim (M.stepEvents (growOneEvents cap) st) sf ∗
    stackAt s0.sp 4608
  onPanic := fun ((_, cap, _, _), _) s0 sf =>
    let newBytes := max (2 * cap.toNat) 4 * 104
    ⌜(¬ RustLayoutOk newBytes 8 ∨ NullAllowed newBytes 8) ∧
      sf.fs = s0.fs ∧ sf.trace = s0.trace⌝ ∗ anyHeap
  onOom := fun ((_, cap, _, _), st) s0 sf =>
    let newBytes := max (2 * cap.toNat) 4 * 104
    ⌜RustLayoutOk newBytes 8 ∧
      ¬ FitsEvents M lim st (growOneEvents cap) ∧
      OomPreserved s0 sf⌝

/-- Total-correctness budget contract for `RawVec<MessageKey>::grow_one` under `FitsEnv`. -/
def growOneSpec (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (GrowGhost × M.σ) where
  pre := fun ((v, cap, ptr, bs), st) s =>
    ⌜s.readReg64 .x0 = v ∧ bs.length = cap.toNat * 104 ∧ ptr ≠ 0 ∧
      max (2 * cap.toNat) 4 * 104 + 8 ≤ 2 ^ 63 ∧
      FitsEnv M lim st (GrowOneEnv cap)⌝ ∗
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
    (if cap = 0 then emp else A.live ptr bs.length 8 ∗ (ptr ↦ₛ bs)) ∗
    A.pool lim st s ∗ stackAt s.sp 4608
  post := fun ((v, cap, _, bs), st) s0 sf =>
    let newCap := max (2 * cap.toNat) 4
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ GrowOneEnv cap evs⌝ ∗
      (∃∗ p' : BitVec 64,
        ⌜p' ≠ 0 ∧ p'.toNat % 8 = 0⌝ ∗
        (v ↦₆₄ BitVec.ofNat 64 newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
        A.live p' (newCap * 104) 8 ∗ (p' ↦ₛ bs) ∗
        memRegion (p' + BitVec.ofNat 64 bs.length) ((newCap - cap.toNat) * 104)) ∗
      A.pool lim (M.stepEvents evs st) sf ∗
      stackAt s0.sp 4608

theorem subroutine_ok_growOne_of_cond {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {P : Program} {entry : BitVec 64}
    (h : subroutine_ok P entry (growOneCondSpec M A lim)) :
    subroutine_ok P entry (growOneSpec M A lim) := by
  apply subroutine_ok.of_codeLoaded
  rintro ⟨⟨v, cap, ptr, bs⟩, st⟩ R s0 hpc hrun hpre hsp _
  dsimp only [growOneSpec] at hpre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc,
      sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hbs, hptr, hfit63, hEnv⟩, hrest⟩
  have hFit : FitsEvents M lim st (growOneEvents cap) :=
    hEnv (growOneEvents cap) (growOneEnv_events cap)
  have hcap63 : cap.toNat * 104 < 2 ^ 63 := by omega
  have hlay : RustLayoutOk (max (2 * cap.toNat) 4 * 104) 8 := by
    refine ⟨⟨by omega, ⟨3, rfl⟩, by omega⟩, by decide⟩
  have hpreC : s0.mem ⊨ (growOneCondSpec M A lim).pre ((v, cap, ptr, bs), st) s0 ∗ R := by
    dsimp only [growOneCondSpec]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc,
        sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hbs, hptr, hcap63⟩, hrest⟩
  refine subroutine_ok.mono_outcome h ((v, cap, ptr, bs), st) R s0 hpc hrun hpreC hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hex⟩ | ⟨ho, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [growOneCondSpec] at hpost
    dsimp only [growOneSpec]
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨growOneEvents cap, ?_⟩
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨⟨hpost.1, growOneEnv_events cap⟩, hpost.2⟩
  · dsimp only [growOneCondSpec] at hpan
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpan
    rcases hpan.1.1 with hnlay | hna
    · exact False.elim (hnlay hlay)
    · exfalso
      unfold growOneEvents rawVecGrowEvents rawVecNewCap at hFit
      by_cases hc0 : cap = 0#64
      · subst hc0
        simp only [↓reduceIte] at hFit
        have hmx : max (2 * (0#64 : BitVec 64).toNat) 4 * 104 = 4 * 104 := by decide
        rw [hmx] at hlay hna
        exact not_nullAllowed_of_fitsAllocEvents hlay hFit hna
      · simp only [hc0, ↓reduceIte] at hFit
        exact not_nullAllowed_of_fitsReallocEvents hlay hFit hna
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hex⟩))
  · dsimp only [growOneCondSpec] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim (hoom.1.2.1 hFit)

def GrowOnePlacedOk [LibsignalPlacement] {M : AllocCostModel}
    (H : String → Option (State → State)) (A : RustCliAllocBudget M) (lim : BudgetLimits) : Prop :=
  subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsmpl.base 43)
    (withLsCodeLoaded lsmpl (growOneSpec M A lim))

/-! ## Extern Hook Forwarding -/

theorem allocHooksBudget_sessionExterns [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (alloc : String → Option (State → State)) (hA : AllocHooksBudget M A lim alloc) :
    AllocHooksBudget M A lim (Rust.withPanics (sessionExterns F alloc)) := by
  rcases hA with ⟨ha, hd, hr⟩
  refine ⟨?_, ?_, ?_⟩ <;>
    simpa [HookSat, Rust.withPanics, Rust.isPanicSymbol, sessionExterns] using ‹_›

end LibsignalBinary.Proofs.ConsumeMessageKey.DefsBudget
