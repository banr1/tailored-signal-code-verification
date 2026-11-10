/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
public import LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudgetFd
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.GrowSpeBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# `FdsGe3Closed`-Threaded `RawVec::grow_one` Seams (Blocks `42` & `43`)

Instantiates `GrowSpeBudget` at `withFds A` to lift `growOneSpeSpec` (block `42`) and
`growOne104SpecX` (block `43`) under `withFdsGe3Closed` when `lim.enforced = true`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.GrowSpeBudgetFd

open Arm64 ProofLib SepProp
open CryptoVerification (
  IsLsBlockProg LibsignalPlacement LsBlockBound
  blkPC_42 blkPl_42 blkPC_43 blkPl_43
  lsRustAllocSym lsRustNoAllocShimSym lsRustReallocSym
  ls_subroutine_ok_of_block lsmpl withLsCodeLoaded
)
open CryptoVerification.LibsignalSession (GrowGhost)
open CryptoVerification.LibsignalTripleRatchet (finishGrowStackX)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget
  rustCliAllocBudgetSpec rustCliReallocBudgetSpec
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (
  FdsGe3Closed withFdsGe3Closed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds (
  hookOk_allocBudget_withFds hookOk_reallocBudget_withFds
  withFds withFds_live withFds_pool_enforced
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (noAllocShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (growOneSpeSpec)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudgetFd (
  subroutine_ok_withLsCodeLoaded_growOneSpe_withFdsGe3Closed_of_withFds
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.GrowSpeBudget (
  GrowOne104Env growOne104SpecX grow_one_104_placed_ok_x grow_one_spe_placed_ok
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

private theorem hookSat_allocBudget_withFds [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {zeroed : Bool}
    {H : String → Option (State → State)} {sym : String}
    (hsat : HookSat H sym (rustCliAllocBudgetSpec M A lim zeroed)) :
    HookSat H sym (rustCliAllocBudgetSpec M (withFds A) lim zeroed) :=
  let ⟨f, hf, hok⟩ := hsat
  ⟨f, hf, hookOk_allocBudget_withFds hok⟩

private theorem hookSat_reallocBudget_withFds [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits}
    {H : String → Option (State → State)} {sym : String}
    (hsat : HookSat H sym (rustCliReallocBudgetSpec M A lim)) :
    HookSat H sym (rustCliReallocBudgetSpec M (withFds A) lim) :=
  let ⟨f, hf, hok⟩ := hsat
  ⟨f, hf, hookOk_reallocBudget_withFds hok⟩

/-! ## 1. Spec-Level `withFds` → `withFdsGe3Closed` Conversions for `growOne104SpecX` -/

/-- Convert `subroutine_ok P entry (growOne104SpecX M (withFds A) lim)` into
`subroutine_ok P entry (withFdsGe3Closed (growOne104SpecX M A lim))` when `lim.enforced = true`. -/
theorem subroutine_ok_growOne104SpecX_withFdsGe3Closed_of_withFds
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {entry : BitVec 64}
    (henf : lim.enforced = true)
    (hok : subroutine_ok P entry (growOne104SpecX M (withFds A) lim)) :
    subroutine_ok P entry (withFdsGe3Closed (growOne104SpecX M A lim)) := by
  refine subroutine_ok_of_pre_post hok rfl rfl rfl ?_ ?_
  · rintro ⟨⟨v, cap, ptr, bs⟩, st⟩ R s0 hpre
    dsimp only [withFdsGe3Closed, growOne104SpecX, withFds_live] at hpre ⊢
    rw [withFds_pool_enforced A henf]
    exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hpre
  · rintro ⟨⟨v, cap, ptr, bs⟩, st⟩ R s0 sf hpost
    dsimp only [withFdsGe3Closed, growOne104SpecX, withFds_live] at hpost ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨evs, hevs⟩
    rw [withFds_pool_enforced A henf] at hevs
    let newCap := max (2 * cap.toNat) 4
    let Inner : SepProp :=
      ∃∗ p' : BitVec 64,
        ⌜p' ≠ 0 ∧ p'.toNat % 8 = 0⌝ ∗
        (v ↦₆₄ BitVec.ofNat 64 newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
        A.live p' (newCap * 104) 8 ∗ (p' ↦ₛ bs) ∗
        memRegion (p' + BitVec.ofNat 64 bs.length) ((newCap - cap.toNat) * 104)
    have hpull :
        (⌜sf.trace = s0.trace ∧ GrowOne104Env cap evs⌝ ∗
          Inner ∗
          (⌜FdsGe3Closed sf.fs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
          stackAt s0.sp (464 + finishGrowStackX)) ∗ R =
        ⌜FdsGe3Closed sf.fs⌝ ∗
          ((⌜sf.trace = s0.trace ∧ GrowOne104Env cap evs⌝ ∗
            Inner ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp (464 + finishGrowStackX)) ∗ R) := by
      sep_ac_rfl
    change sf.mem ⊨
      (⌜sf.trace = s0.trace ∧ GrowOne104Env cap evs⌝ ∗
        Inner ∗
        (⌜FdsGe3Closed sf.fs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
        stackAt s0.sp (464 + finishGrowStackX)) ∗ R at hevs
    rw [hpull, satisfies_pure_sepConj] at hevs
    rcases hevs with ⟨hClosedF, hbody⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hClosedF, ?_⟩
    rw [sepExists_sepConj_left, satisfies_sepExists]
    exact ⟨evs, hbody⟩

/-- Convert `subroutine_ok P entry (withLsCodeLoaded lsmpl (growOne104SpecX M (withFds A) lim))`
into `subroutine_ok P entry (withLsCodeLoaded lsmpl (withFdsGe3Closed (growOne104SpecX M A lim)))`
when `lim.enforced = true`. -/
theorem subroutine_ok_withLsCodeLoaded_growOne104SpecX_withFdsGe3Closed_of_withFds
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {entry : BitVec 64}
    (henf : lim.enforced = true)
    (hok : subroutine_ok P entry (withLsCodeLoaded lsmpl (growOne104SpecX M (withFds A) lim))) :
    subroutine_ok P entry
      (withLsCodeLoaded lsmpl (withFdsGe3Closed (growOne104SpecX M A lim))) := by
  refine subroutine_ok_of_pre_post hok rfl rfl rfl ?_ ?_
  · rintro ⟨⟨v, cap, ptr, bs⟩, st⟩ R s0 hpre
    dsimp only [withLsCodeLoaded, withFdsGe3Closed, growOne104SpecX, withFds_live] at hpre ⊢
    rw [withFds_pool_enforced A henf]
    exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hpre
  · rintro ⟨⟨v, cap, ptr, bs⟩, st⟩ R s0 sf hpost
    dsimp only [withLsCodeLoaded, withFdsGe3Closed, growOne104SpecX, withFds_live] at hpost ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨evs, hevs⟩
    rw [withFds_pool_enforced A henf] at hevs
    let newCap := max (2 * cap.toNat) 4
    let Inner : SepProp :=
      ∃∗ p' : BitVec 64,
        ⌜p' ≠ 0 ∧ p'.toNat % 8 = 0⌝ ∗
        (v ↦₆₄ BitVec.ofNat 64 newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
        A.live p' (newCap * 104) 8 ∗ (p' ↦ₛ bs) ∗
        memRegion (p' + BitVec.ofNat 64 bs.length) ((newCap - cap.toNat) * 104)
    have hpull :
        (⌜sf.trace = s0.trace ∧ GrowOne104Env cap evs⌝ ∗
          Inner ∗
          (⌜FdsGe3Closed sf.fs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
          stackAt s0.sp (464 + finishGrowStackX)) ∗ R =
        ⌜FdsGe3Closed sf.fs⌝ ∗
          ((⌜sf.trace = s0.trace ∧ GrowOne104Env cap evs⌝ ∗
            Inner ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp (464 + finishGrowStackX)) ∗ R) := by
      sep_ac_rfl
    change sf.mem ⊨
      (⌜sf.trace = s0.trace ∧ GrowOne104Env cap evs⌝ ∗
        Inner ∗
        (⌜FdsGe3Closed sf.fs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
        stackAt s0.sp (464 + finishGrowStackX)) ∗ R at hevs
    rw [hpull, satisfies_pure_sepConj] at hevs
    rcases hevs with ⟨hClosedF, hbody⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hClosedF, ?_⟩
    rw [sepExists_sepConj_left, satisfies_sepExists]
    exact ⟨evs, hbody⟩

/-! ## 2. Closed Block `42` & Block `43` `subroutine_ok` Wrappers -/

/-- Block `42`: `RawVec<SignalProtocolError>::grow_one` meets
`withLsCodeLoaded lsmpl (withFdsGe3Closed (growOneSpeSpec M A lim))` when `lim.enforced = true`. -/
theorem grow_one_spe_placed_ok_withFdsGe3Closed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (henf : lim.enforced = true)
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_42).rebase (blkPl_42).base H)
      (blkPl_42).base
      (withLsCodeLoaded lsmpl (withFdsGe3Closed (growOneSpeSpec M A lim))) :=
  subroutine_ok_withLsCodeLoaded_growOneSpe_withFdsGe3Closed_of_withFds henf
    (grow_one_spe_placed_ok hshim
      (hookSat_allocBudget_withFds halloc)
      (hookSat_reallocBudget_withFds hrealloc))

/-- Caller-block transfer of `grow_one_spe_placed_ok_withFdsGe3Closed` to any `callerProg` with
`[IsLsBlockProg callerProg i H]`. -/
theorem grow_one_spe_placed_ok_withFdsGe3Closed_at [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {callerProg : Program} {i bi : Nat} [IsLsBlockProg callerProg i H] [LsBlockBound bi]
    (henf : lim.enforced = true)
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hi : i < bi := by decide) :
    subroutine_ok callerProg (lsmpl.base 42)
      (withLsCodeLoaded lsmpl (withFdsGe3Closed (growOneSpeSpec M A lim))) :=
  ls_subroutine_ok_of_block
    (grow_one_spe_placed_ok_withFdsGe3Closed henf hshim halloc hrealloc) hi

/-- Block `43`: `RawVec<Chain>::grow_one` meets
`withLsCodeLoaded lsmpl (withFdsGe3Closed (growOne104SpecX M A lim))` when `lim.enforced = true`. -/
theorem grow_one_104_placed_ok_x_withFdsGe3Closed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (henf : lim.enforced = true)
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_43).rebase (blkPl_43).base H)
      (blkPl_43).base
      (withLsCodeLoaded lsmpl (withFdsGe3Closed (growOne104SpecX M A lim))) :=
  subroutine_ok_withLsCodeLoaded_growOne104SpecX_withFdsGe3Closed_of_withFds henf
    (grow_one_104_placed_ok_x hshim
      (hookSat_allocBudget_withFds halloc)
      (hookSat_reallocBudget_withFds hrealloc))

/-- Caller-block transfer of `grow_one_104_placed_ok_x_withFdsGe3Closed` to any `callerProg` with
`[IsLsBlockProg callerProg i H]`. -/
theorem grow_one_104_placed_ok_x_withFdsGe3Closed_at [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {callerProg : Program} {i bi : Nat} [IsLsBlockProg callerProg i H] [LsBlockBound bi]
    (henf : lim.enforced = true)
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hi : i < bi := by decide) :
    subroutine_ok callerProg (lsmpl.base 43)
      (withLsCodeLoaded lsmpl (withFdsGe3Closed (growOne104SpecX M A lim))) :=
  ls_subroutine_ok_of_block
    (grow_one_104_placed_ok_x_withFdsGe3Closed henf hshim halloc hrealloc) hi

end LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.GrowSpeBudgetFd
