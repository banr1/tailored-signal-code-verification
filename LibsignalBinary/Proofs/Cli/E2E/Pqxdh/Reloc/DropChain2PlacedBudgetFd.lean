/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.DropChain2PlacedBudget
public import LibsignalBinary.Proofs.Placed.PlacedCallSym
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
public import LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# `FdsGe3Closed`-Threaded `drop_glue::<Chain>` Seams (Block `513`)

Conversion seams from `withFds A` (`lim.enforced = true`) to `withFdsGe3Closed` for
`dropChainSpec` and `dropProtoChainSpec`, plus closed Block `513` and caller-block wrappers.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.DropChain2PlacedBudgetFd

open Arm64 Arm64.Obj ProofLib SepProp
open CryptoVerification (
  IsLsBlockProg LibsignalPlacement LsBlockBound
  ls_subroutine_ok_of_block lsmpl
  subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded
)
open CryptoVerification.CliHandshake.Placed (blkPC_513 blkPl_513)
open CryptoVerification.LibsignalTripleRatchet.Getters (
  DropChainGhost dropChainStack dropChainStackX lsRustDeallocSym
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget rustCliDeallocBudgetSpec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.DropChain2PlacedBudget (
  drop_chain_placed_ok drop_proto_chain_placed_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (
  FdsGe3Closed withFdsGe3Closed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds (
  hookOk_deallocBudget_withFds withFds withFds_pool_enforced withFds_repAlloc
)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget (
  dropChainSpec dropChainSpecX dropProtoChainSpec dropProtoChainSpecX
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

private theorem hookSat_deallocBudget_withFds [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits}
    {H : String → Option (State → State)} {sym : String}
    (hsat : HookSat H sym (rustCliDeallocBudgetSpec M A lim)) :
    HookSat H sym (rustCliDeallocBudgetSpec M (withFds A) lim) :=
  let ⟨f, hf, hok⟩ := hsat
  ⟨f, hf, hookOk_deallocBudget_withFds hok⟩

private theorem dropChainPost_imp {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (henf : lim.enforced = true) (stk : Nat)
    (a : BitVec 64) (st : M.σ) (R : SepProp) (s0 sf : State)
    (hpost : sf.mem ⊨
      (⌜sf.trace = s0.trace⌝ ∗
        memRegion a 104 ∗
        (∃∗ evs : List AllocEvent,
          ⌜FreeOnlyEvs evs⌝ ∗ (withFds A).pool lim (M.stepEvents evs st) sf) ∗
        stackAt s0.sp stk) ∗ R) :
    sf.mem ⊨
      (⌜FdsGe3Closed sf.fs⌝ ∗
        (⌜sf.trace = s0.trace⌝ ∗
          memRegion a 104 ∗
          (∃∗ evs : List AllocEvent,
            ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
          stackAt s0.sp stk)) ∗ R := by
  let Rest : SepProp := (⌜sf.trace = s0.trace⌝ ∗ memRegion a 104 ∗ stackAt s0.sp stk) ∗ R
  have h1 : sf.mem ⊨
      (∃∗ evs : List AllocEvent,
        ⌜FreeOnlyEvs evs⌝ ∗ (withFds A).pool lim (M.stepEvents evs st) sf) ∗ Rest :=
    Eq.mp (congrArg (sf.mem ⊨ ·) (by dsimp only [Rest]; sep_ac_rfl)) hpost
  rw [sepExists_sepConj_left, satisfies_sepExists] at h1
  rcases h1 with ⟨evs, hevs⟩
  rw [withFds_pool_enforced A henf] at hevs
  have hpull :
      (⌜FreeOnlyEvs evs⌝ ∗ (⌜FdsGe3Closed sf.fs⌝ ∗ A.pool lim (M.stepEvents evs st) sf)) ∗ Rest =
      ⌜FdsGe3Closed sf.fs⌝ ∗
        ((⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗ Rest) := by
    sep_ac_rfl
  rw [hpull, satisfies_pure_sepConj] at hevs
  rcases hevs with ⟨hClosedF, hbody⟩
  have h2 : sf.mem ⊨
      (∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗ Rest := by
    rw [sepExists_sepConj_left, satisfies_sepExists]
    exact ⟨evs, hbody⟩
  have h3 : sf.mem ⊨
      ⌜FdsGe3Closed sf.fs⌝ ∗
        ((∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
          Rest) :=
    (satisfies_pure_sepConj _ _ _).mpr ⟨hClosedF, h2⟩
  exact Eq.mp (congrArg (sf.mem ⊨ ·) (by dsimp only [Rest]; sep_ac_rfl)) h3

/-! ## 1. Spec-Level `withFds` → `withFdsGe3Closed` Conversions -/

private theorem specImp_dropChain [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (henf : lim.enforced = true) :
    SpecImp (dropChainSpec M (withFds A) lim)
      (withFdsGe3Closed (dropChainSpec M A lim)) where
  onPanic_eq := rfl
  onExit_eq := rfl
  onOom_eq := rfl
  pre_eq := by
    rintro ⟨x, st⟩ s0
    dsimp only [withFdsGe3Closed, dropChainSpec, withFds_repAlloc]
    rw [withFds_pool_enforced A henf]
    sep_ac_rfl
  post_imp := by
    rintro ⟨x, st⟩ R s0 sf hpost
    dsimp only [withFdsGe3Closed, dropChainSpec] at hpost ⊢
    exact dropChainPost_imp henf dropChainStack x.a st R s0 sf hpost

private theorem specImp_dropChainX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (henf : lim.enforced = true) :
    SpecImp (dropChainSpecX M (withFds A) lim)
      (withFdsGe3Closed (dropChainSpecX M A lim)) where
  onPanic_eq := rfl
  onExit_eq := rfl
  onOom_eq := rfl
  pre_eq := by
    rintro ⟨x, st⟩ s0
    dsimp only [withFdsGe3Closed, dropChainSpecX, withFds_repAlloc]
    rw [withFds_pool_enforced A henf]
    sep_ac_rfl
  post_imp := by
    rintro ⟨x, st⟩ R s0 sf hpost
    dsimp only [withFdsGe3Closed, dropChainSpecX] at hpost ⊢
    exact dropChainPost_imp henf dropChainStackX x.a st R s0 sf hpost

private theorem specImp_dropProtoChain [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (henf : lim.enforced = true) :
    SpecImp (dropProtoChainSpec M (withFds A) lim)
      (withFdsGe3Closed (dropProtoChainSpec M A lim)) where
  onPanic_eq := rfl
  onExit_eq := rfl
  onOom_eq := rfl
  pre_eq := by
    rintro ⟨x, st⟩ s0
    dsimp only [withFdsGe3Closed, dropProtoChainSpec, withFds_repAlloc]
    rw [withFds_pool_enforced A henf]
    sep_ac_rfl
  post_imp := by
    rintro ⟨x, st⟩ R s0 sf hpost
    dsimp only [withFdsGe3Closed, dropProtoChainSpec] at hpost ⊢
    exact dropChainPost_imp henf dropChainStack x.a st R s0 sf hpost

private theorem specImp_dropProtoChainX
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (henf : lim.enforced = true) :
    SpecImp (dropProtoChainSpecX M (withFds A) lim)
      (withFdsGe3Closed (dropProtoChainSpecX M A lim)) where
  onPanic_eq := rfl
  onExit_eq := rfl
  onOom_eq := rfl
  pre_eq := by
    rintro ⟨x, st⟩ s0
    dsimp only [withFdsGe3Closed, dropProtoChainSpecX, withFds_repAlloc]
    rw [withFds_pool_enforced A henf]
    sep_ac_rfl
  post_imp := by
    rintro ⟨x, st⟩ R s0 sf hpost
    dsimp only [withFdsGe3Closed, dropProtoChainSpecX] at hpost ⊢
    exact dropChainPost_imp henf dropChainStackX x.a st R s0 sf hpost

theorem subroutine_ok_dropChain_withFdsGe3Closed_of_withFds [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {entry : BitVec 64}
    (henf : lim.enforced = true)
    (hok : subroutine_ok P entry (dropChainSpec M (withFds A) lim)) :
    subroutine_ok P entry (withFdsGe3Closed (dropChainSpec M A lim)) :=
  (specImp_dropChain henf).to_subroutine_ok hok

theorem subroutine_ok_withLsCodeLoaded_dropChain_withFdsGe3Closed_of_withFds [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {entry : BitVec 64}
    (henf : lim.enforced = true)
    (hok : subroutine_ok P entry (withLsCodeLoaded lsmpl (dropChainSpec M (withFds A) lim))) :
    subroutine_ok P entry (withLsCodeLoaded lsmpl (withFdsGe3Closed (dropChainSpec M A lim))) :=
  ((specImp_dropChain henf).withLsCodeLoaded lsmpl).to_subroutine_ok hok

theorem subroutine_ok_dropChainX_withFdsGe3Closed_of_withFds [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {entry : BitVec 64}
    (henf : lim.enforced = true)
    (hok : subroutine_ok P entry (dropChainSpecX M (withFds A) lim)) :
    subroutine_ok P entry (withFdsGe3Closed (dropChainSpecX M A lim)) :=
  (specImp_dropChainX henf).to_subroutine_ok hok

theorem subroutine_ok_withLsCodeLoaded_dropChainX_withFdsGe3Closed_of_withFds [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {entry : BitVec 64}
    (henf : lim.enforced = true)
    (hok : subroutine_ok P entry (withLsCodeLoaded lsmpl (dropChainSpecX M (withFds A) lim))) :
    subroutine_ok P entry (withLsCodeLoaded lsmpl (withFdsGe3Closed (dropChainSpecX M A lim))) :=
  ((specImp_dropChainX henf).withLsCodeLoaded lsmpl).to_subroutine_ok hok

theorem subroutine_ok_dropProtoChain_withFdsGe3Closed_of_withFds [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {entry : BitVec 64}
    (henf : lim.enforced = true)
    (hok : subroutine_ok P entry (dropProtoChainSpec M (withFds A) lim)) :
    subroutine_ok P entry (withFdsGe3Closed (dropProtoChainSpec M A lim)) :=
  (specImp_dropProtoChain henf).to_subroutine_ok hok

theorem subroutine_ok_withLsCodeLoaded_dropProtoChain_withFdsGe3Closed_of_withFds
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {entry : BitVec 64}
    (henf : lim.enforced = true)
    (hok : subroutine_ok P entry
      (withLsCodeLoaded lsmpl (dropProtoChainSpec M (withFds A) lim))) :
    subroutine_ok P entry
      (withLsCodeLoaded lsmpl (withFdsGe3Closed (dropProtoChainSpec M A lim))) :=
  ((specImp_dropProtoChain henf).withLsCodeLoaded lsmpl).to_subroutine_ok hok

theorem subroutine_ok_dropProtoChainX_withFdsGe3Closed_of_withFds
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {entry : BitVec 64}
    (henf : lim.enforced = true)
    (hok : subroutine_ok P entry (dropProtoChainSpecX M (withFds A) lim)) :
    subroutine_ok P entry (withFdsGe3Closed (dropProtoChainSpecX M A lim)) :=
  (specImp_dropProtoChainX henf).to_subroutine_ok hok

theorem subroutine_ok_withLsCodeLoaded_dropProtoChainX_withFdsGe3Closed_of_withFds
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {entry : BitVec 64}
    (henf : lim.enforced = true)
    (hok : subroutine_ok P entry
      (withLsCodeLoaded lsmpl (dropProtoChainSpecX M (withFds A) lim))) :
    subroutine_ok P entry
      (withLsCodeLoaded lsmpl (withFdsGe3Closed (dropProtoChainSpecX M A lim))) :=
  ((specImp_dropProtoChainX henf).withLsCodeLoaded lsmpl).to_subroutine_ok hok

/-! ## 2. Closed Block `513` & Caller-Block `subroutine_ok` Wrappers -/

/-- Block `513` (`core::ptr::drop_glue::<Chain> [local#2]`) meets
`withFdsGe3Closed (dropProtoChainSpec M A lim)` when `lim.enforced = true`. -/
theorem drop_proto_chain_placed_ok_withFdsGe3Closed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (henf : lim.enforced = true)
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_513).rebase (blkPl_513).base H) (blkPl_513).base
      (withFdsGe3Closed (dropProtoChainSpec M A lim)) :=
  subroutine_ok_dropProtoChain_withFdsGe3Closed_of_withFds henf
    (drop_proto_chain_placed_ok (hookSat_deallocBudget_withFds h_dealloc))

/-- Caller-block transfer of `drop_proto_chain_placed_ok_withFdsGe3Closed` to any `callerProg`
with `[IsLsBlockProg callerProg i H]`. -/
theorem drop_proto_chain_placed_ok_withFdsGe3Closed_at [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {callerProg : Program} {i bi : Nat} [IsLsBlockProg callerProg i H] [LsBlockBound bi]
    (henf : lim.enforced = true)
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hi : i < bi := by decide) :
    subroutine_ok callerProg (lsmpl.base 513)
      (withLsCodeLoaded lsmpl (withFdsGe3Closed (dropProtoChainSpec M A lim))) :=
  ls_subroutine_ok_of_block
    (subroutine_ok_withLsCodeLoaded_of_plain
      (drop_proto_chain_placed_ok_withFdsGe3Closed henf h_dealloc)) hi

/-- Block `513` (`core::ptr::drop_glue::<Chain> [local#2]`) meets
`withFdsGe3Closed (dropChainSpec M A lim)` when `lim.enforced = true`. -/
theorem drop_chain_placed_ok_withFdsGe3Closed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (henf : lim.enforced = true)
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_513).rebase (blkPl_513).base H) (blkPl_513).base
      (withFdsGe3Closed (dropChainSpec M A lim)) :=
  subroutine_ok_dropChain_withFdsGe3Closed_of_withFds henf
    (drop_chain_placed_ok (hookSat_deallocBudget_withFds h_dealloc))

/-- Caller-block transfer of `drop_chain_placed_ok_withFdsGe3Closed` to any `callerProg`
with `[IsLsBlockProg callerProg i H]`. -/
theorem drop_chain_placed_ok_withFdsGe3Closed_at [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {callerProg : Program} {i bi : Nat} [IsLsBlockProg callerProg i H] [LsBlockBound bi]
    (henf : lim.enforced = true)
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hi : i < bi := by decide) :
    subroutine_ok callerProg (lsmpl.base 513)
      (withLsCodeLoaded lsmpl (withFdsGe3Closed (dropChainSpec M A lim))) :=
  ls_subroutine_ok_of_block
    (subroutine_ok_withLsCodeLoaded_of_plain
      (drop_chain_placed_ok_withFdsGe3Closed henf h_dealloc)) hi

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.DropChain2PlacedBudgetFd
