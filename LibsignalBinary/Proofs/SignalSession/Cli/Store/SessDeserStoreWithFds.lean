/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# `withFds` to `withFdsGe3Closed` Conversion Lemmas for CLI Store Callees

Converts pure-heap `withFds A` contracts for `sessDeserializeSpecPlaced`, `sessStorePollSpecPlaced`,
`pathSpecPlaced`, `decimalSpecPlaced`, `addrTextSpecPlaced`, `dirPutSpecPlaced`, and
`dirPutStrSpecPlaced` into `withFdsGe3Closed` contracts at `A` when `lim.enforced = true`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.SessDeserStoreWithFds

open Arm64 ProofLib ProofLib.SepLogic SepProp
open CryptoGames.LibsignalSessionApi (SessionRecord)
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost)
open CryptoVerification.SignalSession.Cli
  (AddrTextGhost DecimalGhost DirGhost DirPutGhost DirPutStrGhost PathGhost SessStorePollGhost)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed extract_withFdsGe3Closed withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds
  (withFds withFds_pool_enforced withFds_repAlloc)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (addrTextSpecPlaced decimalSpecPlaced dirPutSpecPlaced dirPutStrSpecPlaced pathSpecPlaced
   sessDeserializeSpecPlaced sessStorePollSpecPlaced)

private theorem subroutine_ok_of_pre_post {α : Type} {P : Program} {entry : BitVec 64}
    {spec1 spec2 : Spec α} {Q : α → State → Prop}
    (hok : subroutine_ok P entry spec1)
    (hpan : spec2.onPanic = spec1.onPanic)
    (hexc : spec2.onExit = spec1.onExit)
    (hoom : spec2.onOom = spec1.onOom)
    (hpre : ∀ x R s0, (s0.mem ⊨ spec2.pre x s0 ∗ R) → Q x s0 ∧ (s0.mem ⊨ spec1.pre x s0 ∗ R))
    (hpost : ∀ x R s0 sf, Q x s0 → (sf.mem ⊨ spec1.post x s0 sf ∗ R) →
      (sf.mem ⊨ spec2.post x s0 sf ∗ R)) :
    subroutine_ok P entry spec2 := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre2 hsp => ?_
  obtain ⟨hq, hpre1⟩ := hpre x R s0 hpre2
  refine hok.mono_outcome x R s0 hpc hrun hpre1 hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hp1⟩ | ⟨hp, hpan1⟩ | ⟨c, hc, hexc1⟩ | ⟨ho, hoom1⟩
  · exact Or.inl ⟨hret, hcc, hpost x R s0 sf hq hp1⟩
  · exact Or.inr (Or.inl ⟨hp, hpan ▸ hpan1⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hexc ▸ hexc1⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hoom ▸ hoom1⟩))

private theorem pre_end3_cro_enforced {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (henf : lim.enforced = true)
    {Cro P1 P2 P3 R : SepProp} {st : M.σ} {s0 : State}
    (hClosed0 : FdsGe3Closed s0.fs)
    (h : s0.mem ⊨ ((P1 ∗ P2 ∗ P3 ∗ A.pool lim st s0) ∗ Cro) ∗ R) :
    s0.mem ⊨ ((P1 ∗ P2 ∗ P3 ∗ (withFds A).pool lim st s0) ∗ Cro) ∗ R := by
  rw [withFds_pool_enforced A henf]
  have hEq :
      ((P1 ∗ P2 ∗ P3 ∗ (⌜FdsGe3Closed s0.fs⌝ ∗ A.pool lim st s0)) ∗ Cro) ∗ R =
      ⌜FdsGe3Closed s0.fs⌝ ∗ (((P1 ∗ P2 ∗ P3 ∗ A.pool lim st s0) ∗ Cro) ∗ R) := by
    sep_ac_rfl
  rw [hEq, satisfies_pure_sepConj]
  exact ⟨hClosed0, h⟩

private theorem pre_end4_cro_enforced {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (henf : lim.enforced = true)
    {Cro P1 P2 P3 P4 R : SepProp} {st : M.σ} {s0 : State}
    (hClosed0 : FdsGe3Closed s0.fs)
    (h : s0.mem ⊨ ((P1 ∗ P2 ∗ P3 ∗ P4 ∗ A.pool lim st s0) ∗ Cro) ∗ R) :
    s0.mem ⊨ ((P1 ∗ P2 ∗ P3 ∗ P4 ∗ (withFds A).pool lim st s0) ∗ Cro) ∗ R := by
  rw [withFds_pool_enforced A henf]
  have hEq :
      ((P1 ∗ P2 ∗ P3 ∗ P4 ∗ (⌜FdsGe3Closed s0.fs⌝ ∗ A.pool lim st s0)) ∗ Cro) ∗ R =
      ⌜FdsGe3Closed s0.fs⌝ ∗ (((P1 ∗ P2 ∗ P3 ∗ P4 ∗ A.pool lim st s0) ∗ Cro) ∗ R) := by
    sep_ac_rfl
  rw [hEq, satisfies_pure_sepConj]
  exact ⟨hClosed0, h⟩

private theorem pre_end5_cro_enforced {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (henf : lim.enforced = true)
    {Cro P1 P2 P3 P4 P5 R : SepProp} {st : M.σ} {s0 : State}
    (hClosed0 : FdsGe3Closed s0.fs)
    (h : s0.mem ⊨ ((P1 ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ A.pool lim st s0) ∗ Cro) ∗ R) :
    s0.mem ⊨ ((P1 ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ (withFds A).pool lim st s0) ∗ Cro) ∗ R := by
  rw [withFds_pool_enforced A henf]
  have hEq :
      ((P1 ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ (⌜FdsGe3Closed s0.fs⌝ ∗ A.pool lim st s0)) ∗ Cro) ∗ R =
      ⌜FdsGe3Closed s0.fs⌝ ∗ (((P1 ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ A.pool lim st s0) ∗ Cro) ∗ R) := by
    sep_ac_rfl
  rw [hEq, satisfies_pure_sepConj]
  exact ⟨hClosed0, h⟩

private theorem post_end3_enforced {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (henf : lim.enforced = true)
    {P1 : List AllocEvent → SepProp} {P2 P3 R : SepProp}
    {st : M.σ} {sf : State}
    (h : sf.mem ⊨ (∃∗ evs : List AllocEvent,
        P1 evs ∗ P2 ∗ P3 ∗ (withFds A).pool lim (M.stepEvents evs st) sf) ∗ R) :
    sf.mem ⊨ (⌜FdsGe3Closed sf.fs⌝ ∗
        (∃∗ evs : List AllocEvent,
          P1 evs ∗ P2 ∗ P3 ∗ A.pool lim (M.stepEvents evs st) sf)) ∗ R := by
  rw [sepExists_sepConj_left, satisfies_sepExists] at h
  rcases h with ⟨evs, h⟩
  rw [withFds_pool_enforced A henf] at h
  have hEq :
      (P1 evs ∗ P2 ∗ P3 ∗ (⌜FdsGe3Closed sf.fs⌝ ∗ A.pool lim (M.stepEvents evs st) sf)) ∗ R =
      ⌜FdsGe3Closed sf.fs⌝ ∗
        ((P1 evs ∗ P2 ∗ P3 ∗ A.pool lim (M.stepEvents evs st) sf) ∗ R) := by
    sep_ac_rfl
  rw [hEq, satisfies_pure_sepConj] at h
  rcases h with ⟨hClosedF, h⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨hClosedF, ?_⟩
  rw [sepExists_sepConj_left, satisfies_sepExists]
  exact ⟨evs, h⟩

private theorem post_end4_enforced {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (henf : lim.enforced = true)
    {P1 : List AllocEvent → SepProp} {P2 P3 P4 R : SepProp}
    {st : M.σ} {sf : State}
    (h : sf.mem ⊨ (∃∗ evs : List AllocEvent,
        P1 evs ∗ P2 ∗ P3 ∗ P4 ∗ (withFds A).pool lim (M.stepEvents evs st) sf) ∗ R) :
    sf.mem ⊨ (⌜FdsGe3Closed sf.fs⌝ ∗
        (∃∗ evs : List AllocEvent,
          P1 evs ∗ P2 ∗ P3 ∗ P4 ∗ A.pool lim (M.stepEvents evs st) sf)) ∗ R := by
  rw [sepExists_sepConj_left, satisfies_sepExists] at h
  rcases h with ⟨evs, h⟩
  rw [withFds_pool_enforced A henf] at h
  have hEq :
      (P1 evs ∗ P2 ∗ P3 ∗ P4 ∗ (⌜FdsGe3Closed sf.fs⌝ ∗ A.pool lim (M.stepEvents evs st) sf)) ∗ R =
      ⌜FdsGe3Closed sf.fs⌝ ∗
        ((P1 evs ∗ P2 ∗ P3 ∗ P4 ∗ A.pool lim (M.stepEvents evs st) sf) ∗ R) := by
    sep_ac_rfl
  rw [hEq, satisfies_pure_sepConj] at h
  rcases h with ⟨hClosedF, h⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨hClosedF, ?_⟩
  rw [sepExists_sepConj_left, satisfies_sepExists]
  exact ⟨evs, h⟩

private theorem post_end5_enforced {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (henf : lim.enforced = true)
    {P1 : List AllocEvent → SepProp} {P2 P3 P4 P5 R : SepProp}
    {st : M.σ} {sf : State}
    (h : sf.mem ⊨ (∃∗ evs : List AllocEvent,
        P1 evs ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ (withFds A).pool lim (M.stepEvents evs st) sf) ∗ R) :
    sf.mem ⊨ (⌜FdsGe3Closed sf.fs⌝ ∗
        (∃∗ evs : List AllocEvent,
          P1 evs ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ A.pool lim (M.stepEvents evs st) sf)) ∗ R := by
  rw [sepExists_sepConj_left, satisfies_sepExists] at h
  rcases h with ⟨evs, h⟩
  rw [withFds_pool_enforced A henf] at h
  have hEq :
      (P1 evs ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗
        (⌜FdsGe3Closed sf.fs⌝ ∗ A.pool lim (M.stepEvents evs st) sf)) ∗ R =
      ⌜FdsGe3Closed sf.fs⌝ ∗
        ((P1 evs ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ A.pool lim (M.stepEvents evs st) sf) ∗ R) := by
    sep_ac_rfl
  rw [hEq, satisfies_pure_sepConj] at h
  rcases h with ⟨hClosedF, h⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨hClosedF, ?_⟩
  rw [sepExists_sepConj_left, satisfies_sepExists]
  exact ⟨evs, h⟩

private theorem pre4_cro_enforced {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (henf : lim.enforced = true)
    {Cro P1 P2 P3 Tail R : SepProp} {st : M.σ} {s0 : State}
    (hClosed0 : FdsGe3Closed s0.fs)
    (h : s0.mem ⊨ ((P1 ∗ P2 ∗ P3 ∗ A.pool lim st s0 ∗ Tail) ∗ Cro) ∗ R) :
    s0.mem ⊨ ((P1 ∗ P2 ∗ P3 ∗ (withFds A).pool lim st s0 ∗ Tail) ∗ Cro) ∗ R := by
  rw [withFds_pool_enforced A henf]
  have hEq :
      ((P1 ∗ P2 ∗ P3 ∗ (⌜FdsGe3Closed s0.fs⌝ ∗ A.pool lim st s0) ∗ Tail) ∗ Cro) ∗ R =
      ⌜FdsGe3Closed s0.fs⌝ ∗ (((P1 ∗ P2 ∗ P3 ∗ A.pool lim st s0 ∗ Tail) ∗ Cro) ∗ R) := by
    sep_ac_rfl
  rw [hEq, satisfies_pure_sepConj]
  exact ⟨hClosed0, h⟩

private theorem pre6_cro_enforced {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (henf : lim.enforced = true)
    {Cro P1 P2 P3 P4 P5 P6 Tail R : SepProp} {st : M.σ} {s0 : State}
    (hClosed0 : FdsGe3Closed s0.fs)
    (h : s0.mem ⊨ ((P1 ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ P6 ∗ A.pool lim st s0 ∗ Tail) ∗ Cro) ∗ R) :
    s0.mem ⊨ ((P1 ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ P6 ∗ (withFds A).pool lim st s0 ∗ Tail) ∗ Cro) ∗ R := by
  rw [withFds_pool_enforced A henf]
  have hEq :
      ((P1 ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ P6 ∗
        (⌜FdsGe3Closed s0.fs⌝ ∗ A.pool lim st s0) ∗ Tail) ∗ Cro) ∗ R =
      ⌜FdsGe3Closed s0.fs⌝ ∗
        (((P1 ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ P6 ∗ A.pool lim st s0 ∗ Tail) ∗ Cro) ∗ R) := by
    sep_ac_rfl
  rw [hEq, satisfies_pure_sepConj]
  exact ⟨hClosed0, h⟩

private theorem post3_enforced {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (henf : lim.enforced = true)
    {P1 : List AllocEvent → SepProp} {P2 P3 Tail R : SepProp}
    {st : M.σ} {sf : State}
    (h : sf.mem ⊨ (∃∗ evs : List AllocEvent,
        P1 evs ∗ P2 ∗ P3 ∗ (withFds A).pool lim (M.stepEvents evs st) sf ∗ Tail) ∗ R) :
    sf.mem ⊨ (⌜FdsGe3Closed sf.fs⌝ ∗
        (∃∗ evs : List AllocEvent,
          P1 evs ∗ P2 ∗ P3 ∗ A.pool lim (M.stepEvents evs st) sf ∗ Tail)) ∗ R := by
  rw [sepExists_sepConj_left, satisfies_sepExists] at h
  rcases h with ⟨evs, h⟩
  rw [withFds_pool_enforced A henf] at h
  have hEq :
      (P1 evs ∗ P2 ∗ P3 ∗
        (⌜FdsGe3Closed sf.fs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗ Tail) ∗ R =
      ⌜FdsGe3Closed sf.fs⌝ ∗
        ((P1 evs ∗ P2 ∗ P3 ∗ A.pool lim (M.stepEvents evs st) sf ∗ Tail) ∗ R) := by
    sep_ac_rfl
  rw [hEq, satisfies_pure_sepConj] at h
  rcases h with ⟨hClosedF, h⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨hClosedF, ?_⟩
  rw [sepExists_sepConj_left, satisfies_sepExists]
  exact ⟨evs, h⟩

private theorem post7_enforced {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (henf : lim.enforced = true)
    {P1 : List AllocEvent → SepProp} {P2 P3 P4 P5 P6 P7 Tail R : SepProp}
    {st : M.σ} {sf : State}
    (h : sf.mem ⊨ (∃∗ evs : List AllocEvent,
        P1 evs ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ P6 ∗ P7 ∗
          (withFds A).pool lim (M.stepEvents evs st) sf ∗ Tail) ∗ R) :
    sf.mem ⊨ (⌜FdsGe3Closed sf.fs⌝ ∗
        (∃∗ evs : List AllocEvent,
          P1 evs ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ P6 ∗ P7 ∗
            A.pool lim (M.stepEvents evs st) sf ∗ Tail)) ∗ R := by
  rw [sepExists_sepConj_left, satisfies_sepExists] at h
  rcases h with ⟨evs, h⟩
  rw [withFds_pool_enforced A henf] at h
  have hEq :
      (P1 evs ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ P6 ∗ P7 ∗
        (⌜FdsGe3Closed sf.fs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗ Tail) ∗ R =
      ⌜FdsGe3Closed sf.fs⌝ ∗
        ((P1 evs ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ P6 ∗ P7 ∗
          A.pool lim (M.stepEvents evs st) sf ∗ Tail) ∗ R) := by
    sep_ac_rfl
  rw [hEq, satisfies_pure_sepConj] at h
  rcases h with ⟨hClosedF, h⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨hClosedF, ?_⟩
  rw [sepExists_sepConj_left, satisfies_sepExists]
  exact ⟨evs, h⟩

/-- Lifts `sessDeserializeSpecPlaced Scope (withFds A) lim DeserEnv`
yields `withFdsGe3Closed (sessDeserializeSpecPlaced Scope A lim DeserEnv)` when
`lim.enforced = true`. -/
theorem subroutine_ok_sessDeserialize_withFdsGe3Closed_of_withFds [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (henf : lim.enforced = true) {P : Program} {entry : BitVec 64}
    (hok : subroutine_ok P entry (sessDeserializeSpecPlaced Scope (withFds A) lim DeserEnv)) :
    subroutine_ok P entry
      (withFdsGe3Closed (sessDeserializeSpecPlaced Scope A lim DeserEnv)) := by
  refine subroutine_ok_of_pre_post (Q := fun _ _ => True) hok rfl rfl rfl ?_ ?_
  · rintro ⟨x, st⟩ R s0 hpre
    obtain ⟨hClosed0, hpreA⟩ := extract_withFdsGe3Closed hpre
    dsimp only [sessDeserializeSpecPlaced,
      CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
      withFds_repAlloc] at hpreA ⊢
    exact ⟨trivial, pre4_cro_enforced henf hClosed0 hpreA⟩
  · rintro ⟨x, st⟩ R s0 sf _ hpost
    dsimp only [withFdsGe3Closed, sessDeserializeSpecPlaced,
      CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
      withFds_repAlloc] at hpost ⊢
    exact post3_enforced henf hpost

/-- Lifts `sessStorePollSpecPlaced (withFds A) lim StoreEnv stk`
yields `withFdsGe3Closed (sessStorePollSpecPlaced A lim StoreEnv stk)` when
`lim.enforced = true`. -/
theorem subroutine_ok_sessStorePoll_withFdsGe3Closed_of_withFds [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {StoreEnv : SessStorePollGhost → List AllocEvent → Prop} {stk : Nat}
    (henf : lim.enforced = true) {P : Program} {entry : BitVec 64}
    (hok : subroutine_ok P entry (sessStorePollSpecPlaced (withFds A) lim StoreEnv stk)) :
    subroutine_ok P entry
      (withFdsGe3Closed (sessStorePollSpecPlaced A lim StoreEnv stk)) := by
  refine subroutine_ok_of_pre_post (Q := fun _ _ => True) hok rfl rfl rfl ?_ ?_
  · rintro ⟨x, st⟩ R s0 hpre
    obtain ⟨hClosed0, hpreA⟩ := extract_withFdsGe3Closed hpre
    dsimp only [sessStorePollSpecPlaced,
      CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
      withFds_repAlloc] at hpreA ⊢
    exact ⟨trivial, pre6_cro_enforced henf hClosed0 hpreA⟩
  · rintro ⟨x, st⟩ R s0 sf _ hpost
    dsimp only [withFdsGe3Closed, sessStorePollSpecPlaced,
      CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
      withFds_repAlloc] at hpost ⊢
    exact post7_enforced henf hpost

/-- Lifts `pathSpecPlaced (withFds A) lim PathEnv stk` yields
`withFdsGe3Closed (pathSpecPlaced A lim PathEnv stk)` when `lim.enforced = true`. -/
theorem subroutine_ok_path_withFdsGe3Closed_of_withFds [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PathEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop} {stk : Nat}
    (henf : lim.enforced = true) {P : Program} {entry : BitVec 64}
    (hok : subroutine_ok P entry (pathSpecPlaced (withFds A) lim PathEnv stk)) :
    subroutine_ok P entry (withFdsGe3Closed (pathSpecPlaced A lim PathEnv stk)) := by
  refine subroutine_ok_of_pre_post (Q := fun _ _ => True) hok rfl rfl rfl ?_ ?_
  · rintro ⟨x, st⟩ R s0 hpre
    obtain ⟨hClosed0, hpreA⟩ := extract_withFdsGe3Closed hpre
    dsimp only [pathSpecPlaced,
      CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
      withFds_repAlloc] at hpreA ⊢
    exact ⟨trivial, pre_end5_cro_enforced henf hClosed0 hpreA⟩
  · rintro ⟨x, st⟩ R s0 sf _ hpost
    dsimp only [withFdsGe3Closed, pathSpecPlaced,
      CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
      withFds_repAlloc] at hpost ⊢
    exact post_end5_enforced henf hpost

/-- Lifts `decimalSpecPlaced (withFds A) lim DecEnv stk` yields
`withFdsGe3Closed (decimalSpecPlaced A lim DecEnv stk)` when `lim.enforced = true`. -/
theorem subroutine_ok_decimal_withFdsGe3Closed_of_withFds [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecEnv : BitVec 32 → List AllocEvent → Prop} {stk : Nat}
    (henf : lim.enforced = true) {P : Program} {entry : BitVec 64}
    (hok : subroutine_ok P entry (decimalSpecPlaced (withFds A) lim DecEnv stk)) :
    subroutine_ok P entry (withFdsGe3Closed (decimalSpecPlaced A lim DecEnv stk)) := by
  refine subroutine_ok_of_pre_post (Q := fun _ _ => True) hok rfl rfl rfl ?_ ?_
  · rintro ⟨x, st⟩ R s0 hpre
    obtain ⟨hClosed0, hpreA⟩ := extract_withFdsGe3Closed hpre
    dsimp only [decimalSpecPlaced,
      CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
      withFds_repAlloc] at hpreA ⊢
    exact ⟨trivial, pre_end3_cro_enforced henf hClosed0 hpreA⟩
  · rintro ⟨x, st⟩ R s0 sf _ hpost
    dsimp only [withFdsGe3Closed, decimalSpecPlaced,
      CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
      withFds_repAlloc] at hpost ⊢
    exact post_end3_enforced henf hpost

/-- Lifts `addrTextSpecPlaced (withFds A) lim AddrEnv stk` yields
`withFdsGe3Closed (addrTextSpecPlaced A lim AddrEnv stk)` when `lim.enforced = true`. -/
theorem subroutine_ok_addrText_withFdsGe3Closed_of_withFds [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {AddrEnv : AddrGhost → List AllocEvent → Prop} {stk : Nat}
    (henf : lim.enforced = true) {P : Program} {entry : BitVec 64}
    (hok : subroutine_ok P entry (addrTextSpecPlaced (withFds A) lim AddrEnv stk)) :
    subroutine_ok P entry (withFdsGe3Closed (addrTextSpecPlaced A lim AddrEnv stk)) := by
  refine subroutine_ok_of_pre_post (Q := fun _ _ => True) hok rfl rfl rfl ?_ ?_
  · rintro ⟨x, st⟩ R s0 hpre
    obtain ⟨hClosed0, hpreA⟩ := extract_withFdsGe3Closed hpre
    dsimp only [addrTextSpecPlaced,
      CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
      withFds_repAlloc] at hpreA ⊢
    exact ⟨trivial, pre_end4_cro_enforced henf hClosed0 hpreA⟩
  · rintro ⟨x, st⟩ R s0 sf _ hpost
    dsimp only [withFdsGe3Closed, addrTextSpecPlaced,
      CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
      withFds_repAlloc] at hpost ⊢
    exact post_end4_enforced henf hpost

/-- Lifts `dirPutSpecPlaced (withFds A) lim PutEnv stk` yields
`withFdsGe3Closed (dirPutSpecPlaced A lim PutEnv stk)` when `lim.enforced = true`. -/
theorem subroutine_ok_dirPut_withFdsGe3Closed_of_withFds [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop} {stk : Nat}
    (henf : lim.enforced = true) {P : Program} {entry : BitVec 64}
    (hok : subroutine_ok P entry (dirPutSpecPlaced (withFds A) lim PutEnv stk)) :
    subroutine_ok P entry (withFdsGe3Closed (dirPutSpecPlaced A lim PutEnv stk)) := by
  refine subroutine_ok_of_pre_post (Q := fun _ _ => True) hok rfl rfl rfl ?_ ?_
  · rintro ⟨x, st⟩ R s0 hpre
    obtain ⟨hClosed0, hpreA⟩ := extract_withFdsGe3Closed hpre
    dsimp only [dirPutSpecPlaced,
      CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
      withFds_repAlloc] at hpreA ⊢
    exact ⟨trivial, pre_end5_cro_enforced henf hClosed0 hpreA⟩
  · rintro ⟨x, st⟩ R s0 sf _ hpost
    dsimp only [withFdsGe3Closed, dirPutSpecPlaced,
      CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
      withFds_repAlloc] at hpost ⊢
    exact post_end5_enforced henf hpost

/-- Lifts `dirPutStrSpecPlaced (withFds A) lim PutStrEnv stk` yields
`withFdsGe3Closed (dirPutStrSpecPlaced A lim PutStrEnv stk)` when `lim.enforced = true`. -/
theorem subroutine_ok_dirPutStr_withFdsGe3Closed_of_withFds [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PutStrEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop} {stk : Nat}
    (henf : lim.enforced = true) {P : Program} {entry : BitVec 64}
    (hok : subroutine_ok P entry (dirPutStrSpecPlaced (withFds A) lim PutStrEnv stk)) :
    subroutine_ok P entry (withFdsGe3Closed (dirPutStrSpecPlaced A lim PutStrEnv stk)) := by
  refine subroutine_ok_of_pre_post (Q := fun _ _ => True) hok rfl rfl rfl ?_ ?_
  · rintro ⟨x, st⟩ R s0 hpre
    obtain ⟨hClosed0, hpreA⟩ := extract_withFdsGe3Closed hpre
    dsimp only [dirPutStrSpecPlaced,
      CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
      withFds_repAlloc] at hpreA ⊢
    exact ⟨trivial, pre_end5_cro_enforced henf hClosed0 hpreA⟩
  · rintro ⟨x, st⟩ R s0 sf _ hpost
    dsimp only [withFdsGe3Closed, dirPutStrSpecPlaced,
      CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
      withFds_repAlloc] at hpost ⊢
    exact post_end5_enforced henf hpost

end LibsignalBinary.Proofs.SignalSession.Cli.Store.SessDeserStoreWithFds
