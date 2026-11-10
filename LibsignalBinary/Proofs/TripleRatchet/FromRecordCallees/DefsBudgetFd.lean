/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.PlacedCallSym
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
public import LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# `FdsGe3Closed`-Threaded `try_decrypt_from_record` Callee Seams

Provides `withFds A` (`lim.enforced = true`) to `withFdsGe3Closed` conversion lemmas and
`withLsCodeLoaded` commutators for `dropSessionStructureLocal2Spec`, `dropSessionStructureLocal1Spec`,
`setSessionStateSpec`, `growOneSpeCondSpec`, and `growOneSpeSpec`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudgetFd

open Arm64 Arm64.Obj ProofLib SepProp
open CryptoVerification (LibsignalPlacement lsmpl withLsCodeLoaded)
open CryptoVerification.LibsignalSession (GrowGhost)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (
  DropSessionStructureGhost SetSessionStateGhost
  dropSessionStructureLocal1Stack dropSessionStructureLocal2Stack
  growOneSpeStack setSessionStateStack
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (
  FdsGe3Closed withFdsGe3Closed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds (
  withFds withFds_live withFds_pool_enforced withFds_repAlloc
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  GrowOneSpeEnv dropSessionStructureLocal1Spec dropSessionStructureLocal2Spec
  growOneSpeCondSpec growOneSpeSpec setSessionStateSpec
)

private theorem subroutine_ok_of_pre_post {α : Type} {P : Program} {entry : BitVec 64}
    {spec1 spec2 : Spec α}
    (hok : subroutine_ok P entry spec1)
    (hpan : spec2.onPanic = spec1.onPanic)
    (hexc : spec2.onExit = spec1.onExit)
    (hoom : spec2.onOom = spec1.onOom)
    (hpre : ∀ x R s0, (s0.mem ⊨ spec2.pre x s0 ∗ R) → (s0.mem ⊨ spec1.pre x s0 ∗ R))
    (hpost : ∀ x R s0 sf, (sf.mem ⊨ spec1.post x s0 sf ∗ R) →
      (sf.mem ⊨ spec2.post x s0 sf ∗ R)) :
    subroutine_ok P entry spec2 := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre2 hsp => ?_
  refine hok.mono_outcome x R s0 hpc hrun (hpre x R s0 hpre2) hsp ?_
  rintro sf (⟨hret, hcc, hp1⟩ | ⟨hp, hpan1⟩ | ⟨c, hc, hexc1⟩ | ⟨ho, hoom1⟩)
  · exact Or.inl ⟨hret, hcc, hpost x R s0 sf hp1⟩
  · exact Or.inr (Or.inl ⟨hp, hpan ▸ hpan1⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hexc ▸ hexc1⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hoom ▸ hoom1⟩))

private structure SpecImp {α : Type} (spec1 spec2 : Spec α) : Prop where
  onPanic_eq : spec2.onPanic = spec1.onPanic
  onExit_eq : spec2.onExit = spec1.onExit
  onOom_eq : spec2.onOom = spec1.onOom
  pre_eq : ∀ x s0, spec2.pre x s0 = spec1.pre x s0
  post_imp : ∀ x R s0 sf,
    (sf.mem ⊨ spec1.post x s0 sf ∗ R) → (sf.mem ⊨ spec2.post x s0 sf ∗ R)

private theorem SpecImp.to_subroutine_ok {α : Type} {P : Program} {entry : BitVec 64}
    {spec1 spec2 : Spec α} (h : SpecImp spec1 spec2)
    (hok : subroutine_ok P entry spec1) :
    subroutine_ok P entry spec2 :=
  subroutine_ok_of_pre_post hok h.onPanic_eq h.onExit_eq h.onOom_eq
    (fun x _ s0 hp => by rwa [← h.pre_eq x s0]) h.post_imp

private theorem SpecImp.withLsCodeLoaded {α : Type} (pl : MultiPlacement)
    {spec1 spec2 : Spec α} (h : SpecImp spec1 spec2) :
    SpecImp (CryptoVerification.withLsCodeLoaded pl spec1)
      (CryptoVerification.withLsCodeLoaded pl spec2) where
  onPanic_eq := h.onPanic_eq
  onExit_eq := h.onExit_eq
  onOom_eq := h.onOom_eq
  pre_eq := fun x s0 => by
    dsimp only [CryptoVerification.withLsCodeLoaded]
    rw [h.pre_eq x s0]
  post_imp := h.post_imp

/-! ## 0. `withLsCodeLoaded` ↔ `withFdsGe3Closed` Commutators -/

/-- Commute `withFdsGe3Closed (withLsCodeLoaded pl spec)` into
`withLsCodeLoaded pl (withFdsGe3Closed spec)`. -/
theorem subroutine_ok_withLsCodeLoaded_withFdsGe3Closed_of_outer {α : Type}
    {P : Program} {entry : BitVec 64} {pl : MultiPlacement} {spec : Spec α}
    (hok : subroutine_ok P entry (withFdsGe3Closed (withLsCodeLoaded pl spec))) :
    subroutine_ok P entry (withLsCodeLoaded pl (withFdsGe3Closed spec)) := by
  refine subroutine_ok_of_pre_post hok rfl rfl rfl (fun _ _ s0 hpre => ?_) (fun _ _ _ _ hpost => hpost)
  dsimp only [withLsCodeLoaded, withFdsGe3Closed] at hpre ⊢
  exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hpre

/-- Commute `withLsCodeLoaded pl (withFdsGe3Closed spec)` into
`withFdsGe3Closed (withLsCodeLoaded pl spec)`. -/
theorem subroutine_ok_withFdsGe3Closed_withLsCodeLoaded_of_inner {α : Type}
    {P : Program} {entry : BitVec 64} {pl : MultiPlacement} {spec : Spec α}
    (hok : subroutine_ok P entry (withLsCodeLoaded pl (withFdsGe3Closed spec))) :
    subroutine_ok P entry (withFdsGe3Closed (withLsCodeLoaded pl spec)) := by
  refine subroutine_ok_of_pre_post hok rfl rfl rfl (fun _ _ s0 hpre => ?_) (fun _ _ _ _ hpost => hpost)
  dsimp only [withLsCodeLoaded, withFdsGe3Closed] at hpre ⊢
  exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hpre

/-! ## 1. `dropSessionStructureLocal2Spec` (Blocks `139`, `442`, `512`) -/

private theorem specImp_dropSessionStructureLocal2 [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (henf : lim.enforced = true) :
    SpecImp (dropSessionStructureLocal2Spec M (withFds A) lim)
      (withFdsGe3Closed (dropSessionStructureLocal2Spec M A lim)) where
  onPanic_eq := rfl
  onExit_eq := rfl
  onOom_eq := rfl
  pre_eq := by
    rintro ⟨x, st⟩ s0
    dsimp only [withFdsGe3Closed, dropSessionStructureLocal2Spec, withFds_repAlloc]
    rw [withFds_pool_enforced A henf]
    sep_ac_rfl
  post_imp := by
    rintro ⟨x, st⟩ R s0 sf hpost
    dsimp only [withFdsGe3Closed, dropSessionStructureLocal2Spec] at hpost ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨evs, hevs⟩
    rw [withFds_pool_enforced A henf] at hevs
    have hpull :
        (⌜sf.trace = s0.trace ∧ FreeOnlyEvs evs⌝ ∗
          memRegion x.ss 344 ∗
          (⌜FdsGe3Closed sf.fs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
          stackAt s0.sp dropSessionStructureLocal2Stack) ∗ R =
        ⌜FdsGe3Closed sf.fs⌝ ∗
          ((⌜sf.trace = s0.trace ∧ FreeOnlyEvs evs⌝ ∗
            memRegion x.ss 344 ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp dropSessionStructureLocal2Stack) ∗ R) := by
      sep_ac_rfl
    rw [hpull, satisfies_pure_sepConj] at hevs
    rcases hevs with ⟨hClosedF, hbody⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hClosedF, ?_⟩
    rw [sepExists_sepConj_left, satisfies_sepExists]
    exact ⟨evs, hbody⟩

theorem subroutine_ok_dropSessionStructureLocal2_withFdsGe3Closed_of_withFds
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {entry : BitVec 64}
    (henf : lim.enforced = true)
    (hok : subroutine_ok P entry (dropSessionStructureLocal2Spec M (withFds A) lim)) :
    subroutine_ok P entry (withFdsGe3Closed (dropSessionStructureLocal2Spec M A lim)) :=
  (specImp_dropSessionStructureLocal2 henf).to_subroutine_ok hok

theorem subroutine_ok_withLsCodeLoaded_dropSessionStructureLocal2_withFdsGe3Closed_of_withFds
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {entry : BitVec 64}
    (henf : lim.enforced = true)
    (hok : subroutine_ok P entry
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M (withFds A) lim))) :
    subroutine_ok P entry
      (withLsCodeLoaded lsmpl (withFdsGe3Closed (dropSessionStructureLocal2Spec M A lim))) :=
  ((specImp_dropSessionStructureLocal2 henf).withLsCodeLoaded lsmpl).to_subroutine_ok hok

/-! ## 2. `dropSessionStructureLocal1Spec` (Block `6`) -/

private theorem specImp_dropSessionStructureLocal1 [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (henf : lim.enforced = true) :
    SpecImp (dropSessionStructureLocal1Spec M (withFds A) lim)
      (withFdsGe3Closed (dropSessionStructureLocal1Spec M A lim)) where
  onPanic_eq := rfl
  onExit_eq := rfl
  onOom_eq := rfl
  pre_eq := by
    rintro ⟨x, st⟩ s0
    dsimp only [withFdsGe3Closed, dropSessionStructureLocal1Spec, withFds_repAlloc]
    rw [withFds_pool_enforced A henf]
    sep_ac_rfl
  post_imp := by
    rintro ⟨x, st⟩ R s0 sf hpost
    dsimp only [withFdsGe3Closed, dropSessionStructureLocal1Spec] at hpost ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨evs, hevs⟩
    rw [withFds_pool_enforced A henf] at hevs
    have hpull :
        (⌜sf.trace = s0.trace ∧ FreeOnlyEvs evs⌝ ∗
          memRegion x.ss 344 ∗
          (⌜FdsGe3Closed sf.fs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
          stackAt s0.sp dropSessionStructureLocal1Stack) ∗ R =
        ⌜FdsGe3Closed sf.fs⌝ ∗
          ((⌜sf.trace = s0.trace ∧ FreeOnlyEvs evs⌝ ∗
            memRegion x.ss 344 ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp dropSessionStructureLocal1Stack) ∗ R) := by
      sep_ac_rfl
    rw [hpull, satisfies_pure_sepConj] at hevs
    rcases hevs with ⟨hClosedF, hbody⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hClosedF, ?_⟩
    rw [sepExists_sepConj_left, satisfies_sepExists]
    exact ⟨evs, hbody⟩

theorem subroutine_ok_dropSessionStructureLocal1_withFdsGe3Closed_of_withFds
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {entry : BitVec 64}
    (henf : lim.enforced = true)
    (hok : subroutine_ok P entry (dropSessionStructureLocal1Spec M (withFds A) lim)) :
    subroutine_ok P entry (withFdsGe3Closed (dropSessionStructureLocal1Spec M A lim)) :=
  (specImp_dropSessionStructureLocal1 henf).to_subroutine_ok hok

theorem subroutine_ok_withLsCodeLoaded_dropSessionStructureLocal1_withFdsGe3Closed_of_withFds
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {entry : BitVec 64}
    (henf : lim.enforced = true)
    (hok : subroutine_ok P entry
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal1Spec M (withFds A) lim))) :
    subroutine_ok P entry
      (withLsCodeLoaded lsmpl (withFdsGe3Closed (dropSessionStructureLocal1Spec M A lim))) :=
  ((specImp_dropSessionStructureLocal1 henf).withLsCodeLoaded lsmpl).to_subroutine_ok hok

/-! ## 3. `setSessionStateSpec` (Block `48`) -/

private theorem specImp_setSessionState
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (henf : lim.enforced = true) :
    SpecImp (setSessionStateSpec M (withFds A) lim)
      (withFdsGe3Closed (setSessionStateSpec M A lim)) where
  onPanic_eq := rfl
  onExit_eq := rfl
  onOom_eq := rfl
  pre_eq := by
    rintro ⟨x, st⟩ s0
    dsimp only [withFdsGe3Closed, setSessionStateSpec, withFds_repAlloc]
    rw [withFds_pool_enforced A henf]
    cases x.cur with
    | none =>
      dsimp only
      sep_ac_rfl
    | some p =>
      rcases p with ⟨G, ss⟩
      dsimp only
      sep_ac_rfl
  post_imp := by
    rintro ⟨x, st⟩ R s0 sf hpost
    dsimp only [withFdsGe3Closed, setSessionStateSpec] at hpost ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨evs, hevs⟩
    rw [withFds_pool_enforced A henf] at hevs
    have hpull :
        (⌜sf.trace = s0.trace ∧ FreeOnlyEvs evs ∧ (x.cur = none → evs = [])⌝ ∗
          ((x.record + 24#64) ↦ₛ x.bs) ∗ (x.src ↦ₛ x.bs) ∗
          (⌜FdsGe3Closed sf.fs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
          stackAt s0.sp setSessionStateStack) ∗ R =
        ⌜FdsGe3Closed sf.fs⌝ ∗
          ((⌜sf.trace = s0.trace ∧ FreeOnlyEvs evs ∧ (x.cur = none → evs = [])⌝ ∗
            ((x.record + 24#64) ↦ₛ x.bs) ∗ (x.src ↦ₛ x.bs) ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp setSessionStateStack) ∗ R) := by
      sep_ac_rfl
    rw [hpull, satisfies_pure_sepConj] at hevs
    rcases hevs with ⟨hClosedF, hbody⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hClosedF, ?_⟩
    rw [sepExists_sepConj_left, satisfies_sepExists]
    exact ⟨evs, hbody⟩

theorem subroutine_ok_setSessionState_withFdsGe3Closed_of_withFds
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {entry : BitVec 64}
    (henf : lim.enforced = true)
    (hok : subroutine_ok P entry (setSessionStateSpec M (withFds A) lim)) :
    subroutine_ok P entry (withFdsGe3Closed (setSessionStateSpec M A lim)) :=
  (specImp_setSessionState henf).to_subroutine_ok hok

theorem subroutine_ok_withLsCodeLoaded_setSessionState_withFdsGe3Closed_of_withFds
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {entry : BitVec 64}
    (henf : lim.enforced = true)
    (hok : subroutine_ok P entry
      (withLsCodeLoaded lsmpl (setSessionStateSpec M (withFds A) lim))) :
    subroutine_ok P entry
      (withLsCodeLoaded lsmpl (withFdsGe3Closed (setSessionStateSpec M A lim))) :=
  ((specImp_setSessionState henf).withLsCodeLoaded lsmpl).to_subroutine_ok hok

/-! ## 4. `growOneSpeCondSpec` & `growOneSpeSpec` (Block `42`) -/

private theorem specImp_growOneSpeCond
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (henf : lim.enforced = true) :
    SpecImp (growOneSpeCondSpec M (withFds A) lim)
      (withFdsGe3Closed (growOneSpeCondSpec M A lim)) where
  onPanic_eq := rfl
  onExit_eq := rfl
  onOom_eq := rfl
  pre_eq := by
    rintro ⟨⟨v, cap, ptr, bs⟩, st⟩ s0
    dsimp only [withFdsGe3Closed, growOneSpeCondSpec, withFds_live]
    rw [withFds_pool_enforced A henf]
    sep_ac_rfl
  post_imp := by
    rintro ⟨⟨v, cap, ptr, bs⟩, st⟩ R s0 sf hpost
    dsimp only [withFdsGe3Closed, growOneSpeCondSpec, withFds_live] at hpost ⊢
    rw [withFds_pool_enforced A henf] at hpost
    exact Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hpost

theorem subroutine_ok_growOneSpeCond_withFdsGe3Closed_of_withFds
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {entry : BitVec 64}
    (henf : lim.enforced = true)
    (hok : subroutine_ok P entry (growOneSpeCondSpec M (withFds A) lim)) :
    subroutine_ok P entry (withFdsGe3Closed (growOneSpeCondSpec M A lim)) :=
  (specImp_growOneSpeCond henf).to_subroutine_ok hok

theorem subroutine_ok_withLsCodeLoaded_growOneSpeCond_withFdsGe3Closed_of_withFds
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {entry : BitVec 64}
    (henf : lim.enforced = true)
    (hok : subroutine_ok P entry
      (withLsCodeLoaded lsmpl (growOneSpeCondSpec M (withFds A) lim))) :
    subroutine_ok P entry
      (withLsCodeLoaded lsmpl (withFdsGe3Closed (growOneSpeCondSpec M A lim))) :=
  ((specImp_growOneSpeCond henf).withLsCodeLoaded lsmpl).to_subroutine_ok hok

private theorem specImp_growOneSpe
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (henf : lim.enforced = true) :
    SpecImp (growOneSpeSpec M (withFds A) lim)
      (withFdsGe3Closed (growOneSpeSpec M A lim)) where
  onPanic_eq := rfl
  onExit_eq := rfl
  onOom_eq := rfl
  pre_eq := by
    rintro ⟨⟨v, cap, ptr, bs⟩, st⟩ s0
    dsimp only [withFdsGe3Closed, growOneSpeSpec, withFds_live]
    rw [withFds_pool_enforced A henf]
    sep_ac_rfl
  post_imp := by
    rintro ⟨⟨v, cap, ptr, bs⟩, st⟩ R s0 sf hpost
    dsimp only [withFdsGe3Closed, growOneSpeSpec, withFds_live] at hpost ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨evs, hevs⟩
    rw [withFds_pool_enforced A henf] at hevs
    let newCap := max (2 * cap.toNat) 4
    let Inner : SepProp :=
      ∃∗ p' : BitVec 64,
        ⌜p' ≠ 0 ∧ p'.toNat % 8 = 0⌝ ∗
        (v ↦₆₄ BitVec.ofNat 64 newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
        A.live p' (newCap * 48) 8 ∗ (p' ↦ₛ bs) ∗
        memRegion (p' + BitVec.ofNat 64 bs.length) ((newCap - cap.toNat) * 48)
    have hpull :
        (⌜sf.trace = s0.trace ∧ GrowOneSpeEnv cap evs⌝ ∗
          Inner ∗
          (⌜FdsGe3Closed sf.fs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
          stackAt s0.sp growOneSpeStack) ∗ R =
        ⌜FdsGe3Closed sf.fs⌝ ∗
          ((⌜sf.trace = s0.trace ∧ GrowOneSpeEnv cap evs⌝ ∗
            Inner ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp growOneSpeStack) ∗ R) := by
      sep_ac_rfl
    change sf.mem ⊨
      (⌜sf.trace = s0.trace ∧ GrowOneSpeEnv cap evs⌝ ∗
        Inner ∗
        (⌜FdsGe3Closed sf.fs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
        stackAt s0.sp growOneSpeStack) ∗ R at hevs
    rw [hpull, satisfies_pure_sepConj] at hevs
    rcases hevs with ⟨hClosedF, hbody⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hClosedF, ?_⟩
    rw [sepExists_sepConj_left, satisfies_sepExists]
    exact ⟨evs, hbody⟩

theorem subroutine_ok_growOneSpe_withFdsGe3Closed_of_withFds
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {entry : BitVec 64}
    (henf : lim.enforced = true)
    (hok : subroutine_ok P entry (growOneSpeSpec M (withFds A) lim)) :
    subroutine_ok P entry (withFdsGe3Closed (growOneSpeSpec M A lim)) :=
  (specImp_growOneSpe henf).to_subroutine_ok hok

theorem subroutine_ok_withLsCodeLoaded_growOneSpe_withFdsGe3Closed_of_withFds
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {entry : BitVec 64}
    (henf : lim.enforced = true)
    (hok : subroutine_ok P entry
      (withLsCodeLoaded lsmpl (growOneSpeSpec M (withFds A) lim))) :
    subroutine_ok P entry
      (withLsCodeLoaded lsmpl (withFdsGe3Closed (growOneSpeSpec M A lim))) :=
  ((specImp_growOneSpe henf).withLsCodeLoaded lsmpl).to_subroutine_ok hok

end LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudgetFd
