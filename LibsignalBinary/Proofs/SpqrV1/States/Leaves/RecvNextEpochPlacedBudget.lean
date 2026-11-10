/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvNextEpochBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvNextEpochPlaced
import ProofLib.SepLogic.WPp

/-!
# `<Ct2Sampled>::recv_next_epoch` (Budget-Threaded Relocatable, Block `355`)

Re-exports the Block `355` budget-threaded contracts from `RecvNextEpochBudget` and provides
envelope-parametric `[LibsignalPlacement]` lifts `ct2_sampled_recv_next_epoch_placed_{ok,cl}_ext_ofEnv`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvNextEpochPlacedBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalPlacement blkPl_355 extract_withLsCodeLoaded lsProg_355 lsmpl withLsCodeLoaded)
open CryptoVerification.SpqrV1.States.Leaves
  (Ct2SampledRecvNextEpochGhost)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget)
open LibsignalBinary.Proofs.SpqrV1.Drop.PolyBudget
  (dropGluePoly16Spec)

/-! ## 1. Re-Exports from `RecvNextEpochBudget` & `DefsPlacedBudget` -/

export LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvNextEpochBudget
  (Ct2SampledRecvNextEpochEnv ct2SampledRecvNextEpochEnv_nonempty
   ct2SampledRecvNextEpochSpec ct2SampledRecvNextEpochSpecOfEnv
   subroutine_ok_ct2SampledRecvNextEpochSpecOfEnv_freeOnly)

export LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvNextEpochBudget
  (Ct2SampledRecvNextEpochPlacedOkX Ct2SampledRecvNextEpochPlacedOkXOfEnv
   call_dropGluePoly16_cl call_dropGluePoly16_budget)

export LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvNextEpochBudget
  (ct2_sampled_recv_next_epoch_placed_ok_ext
   ct2_sampled_recv_next_epoch_placed_cl_ext
   ct2_sampled_recv_next_epoch_placed_ok_x
   ct2_sampled_recv_next_epoch_placed_ok_x_ofEnv)

/-! ## 2. Envelope-Parametric `[LibsignalPlacement]` Lifts for Block `355` -/

/-- Envelope-parametric relocatable `<Ct2Sampled>::recv_next_epoch` (Block `355`) given a plain
    `subroutine_ok` hypothesis for `drop_glue::<[Poly; 16]>` at `lsmpl.base 265`. -/
theorem ct2_sampled_recv_next_epoch_placed_ok_ext_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {Env : Ct2SampledRecvNextEpochGhost F → List AllocEvent → Prop}
    (hsub : ∀ x evs, FreeOnlyEvs evs → Env x evs)
    (hdrop : subroutine_ok (lsProg_355 (Rust.withPanics ext))
      (lsmpl.base 265) (dropGluePoly16Spec M A lim)) :
    subroutine_ok (lsProg_355 (Rust.withPanics ext))
      (blkPl_355).base
      (ct2SampledRecvNextEpochSpecOfEnv M A lim F Env) := by
  have hok := ct2_sampled_recv_next_epoch_placed_ok_ext (F := F) hdrop
  refine subroutine_ok_mono hok (fun ⟨x, st⟩ R s0 hp => ?_) (fun ⟨x, st⟩ R s0 sf hq => ?_)
  · dsimp only [ct2SampledRecvNextEpochSpecOfEnv, ct2SampledRecvNextEpochSpec] at hp ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
    exact ⟨⟨hp.1.1, hp.1.2.1, hp.1.2.2.1, hp.1.2.2.2.1, hp.1.2.2.2.2.2⟩, hp.2⟩
  · dsimp only [ct2SampledRecvNextEpochSpecOfEnv, ct2SampledRecvNextEpochSpec] at hq ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨evs, hq⟩
    refine ⟨evs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    exact ⟨⟨hq.1.1, hsub x evs hq.1.2⟩, hq.2⟩

/-- Envelope-parametric relocatable `<Ct2Sampled>::recv_next_epoch` (Block `355`) given a
    `withLsCodeLoaded` `subroutine_ok` hypothesis for `drop_glue::<[Poly; 16]>` at `lsmpl.base 265`. -/
theorem ct2_sampled_recv_next_epoch_placed_cl_ext_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {Env : Ct2SampledRecvNextEpochGhost F → List AllocEvent → Prop}
    (hsub : ∀ x evs, FreeOnlyEvs evs → Env x evs)
    (hdrop : subroutine_ok (lsProg_355 (Rust.withPanics ext))
      (lsmpl.base 265) (withLsCodeLoaded lsmpl (dropGluePoly16Spec M A lim))) :
    Ct2SampledRecvNextEpochPlacedOkXOfEnv M A lim F ext Env := by
  have hok := ct2_sampled_recv_next_epoch_placed_cl_ext (F := F) hdrop
  refine subroutine_ok_mono hok (fun ⟨x, st⟩ R s0 hp => ?_) (fun ⟨x, st⟩ R s0 sf hq => ?_)
  · obtain ⟨hcl, hpre⟩ := extract_withLsCodeLoaded hp
    dsimp only [ct2SampledRecvNextEpochSpecOfEnv] at hpre
    dsimp only [withLsCodeLoaded, ct2SampledRecvNextEpochSpec]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    exact ⟨⟨hpre.1.1, hpre.1.2.1, hpre.1.2.2.1, hpre.1.2.2.2.1, hpre.1.2.2.2.2.2⟩, hpre.2⟩
  · dsimp only [withLsCodeLoaded, ct2SampledRecvNextEpochSpec,
      ct2SampledRecvNextEpochSpecOfEnv] at hq ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨evs, hq⟩
    refine ⟨evs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    exact ⟨⟨hq.1.1, hsub x evs hq.1.2⟩, hq.2⟩

end LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvNextEpochPlacedBudget
