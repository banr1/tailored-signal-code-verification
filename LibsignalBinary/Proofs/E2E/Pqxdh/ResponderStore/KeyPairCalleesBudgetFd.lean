/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.KeyPairCalleesBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WP.Apply
meta import ProofLib.SepLogic.WP.Apply -- shake: keep

/-!
# File-Descriptor-Preserving Contracts for `kem::KeyPair::from_public_and_private`

Proves `.keepsFs` and `withFdsGe3Closed` relocatable `[LibsignalPlacement]` contracts for
`kem::KeyPair::from_public_and_private` (Block `70`) and its `KeyPairSerde` wrapper (Block `113`)
under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.KeyPairCalleesBudgetFd

open Arm64 Arm64.Obj ProofLib
open CryptoVerification
  (LibsignalHooks LibsignalPlacement blkPC_70 blkPl_70 blkPC_113 blkPl_113
   lsMemcpySym lsRustAllocSym lsRustNoAllocShimSym ls_hook_ok_of_mem ls_subroutine_ok_of_block
   lsmpl lsρ subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded)
open CryptoVerification.E2E.Pqxdh.ResponderStore (bv_sub_add_lit')
open CryptoVerification.LibsignalTripleRatchet (sessionMemcpyRegionSpec sessionShimSpec)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel BudgetLimits FitsEnv FitsEvents PoolPreserved
   RustCliAllocBudget RustLayoutOk VmPreserved fitsEvents_append rustAllocEvents
   rustCliAllocBudgetSpec rustCliAllocNoOomSpec subroutine_ok_allocNoOom_of_budget)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.KeyPairCalleesAuxBudget
  (KemKeyPairFromPubPrivEnv kemKeyPairFromPubPrivEvents kemKeyPairFromPubPrivOkSpec
   stackAt_kemKeyPairFromPubPriv)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
  (subroutine_ok_withFdsGe3Closed_of_keepsFs)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (withFdsGe3Closed)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionMemcpyRegionBudgetSpec sessionShimBudgetSpec)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit bv_sub_add_lit' BitVec.toNat_zero

private theorem setPC_pool_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (pc : BitVec 64) :
    A.pool lim st (s.setPC pc) = A.pool lim st s :=
  A.pool_of_vmPreserved (s0 := s) (sf := s.setPC pc)
    (by delta VmPreserved; cases s; exact ⟨⟨rfl, rfl, rfl⟩, rfl, fun _ => rfl, fun _ _ _ => rfl⟩)

set_option maxHeartbeats 1200000 in
theorem kemKeyPairFromPubPriv_placed_ok_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec.keepsFs)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec.keepsFs) :
    subroutine_ok ((blkPC_70).rebase (blkPl_70).base H) (blkPl_70).base
      (kemKeyPairFromPubPrivOkSpec M A lim).keepsFs := by
  simp only [Spec.keepsFs, kemKeyPairFromPubPrivOkSpec,
    CryptoVerification.E2E.Pqxdh.ResponderStore.kemKeyPairFromPubPrivOkSpec,
    stackAt_kemKeyPairFromPubPriv, RustCliAllocBudget.atState_pool, RustCliAllocBudget.atState_live]
  cells_unfold
  have hshim_ok : subroutine_ok ((blkPC_70).rebase (blkPl_70).base H)
      (lsρ lsRustNoAllocShimSym) sessionShimBudgetSpec.keepsFs :=
    ls_hook_ok_of_mem hshim
  have halloc_ok : subroutine_ok ((blkPC_70).rebase (blkPl_70).base H)
      (lsρ lsRustAllocSym) (rustCliAllocNoOomSpec M A lim false) :=
    subroutine_ok_allocNoOom_of_budget (ls_hook_ok_of_mem halloc)
  have hmemcpy_ok : subroutine_ok ((blkPC_70).rebase (blkPl_70).base H)
      (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec.keepsFs :=
    ls_hook_ok_of_mem hmemcpy
  dsimp only [Spec.keepsFs, sessionShimBudgetSpec, sessionShimSpec] at hshim_ok
  dsimp only [rustCliAllocNoOomSpec, AllocCallPreserved, PoolPreserved,
    Bool.false_eq_true, ↓reduceIte] at halloc_ok
  dsimp only [Spec.keepsFs, sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec,
    memcpyRegionSpec] at hmemcpy_ok
  wp_init xst s0
  obtain ⟨⟨pubPtr, pk, privPtr, sk, outPtr⟩, st⟩ := xst
  dsimp only at *
  simp (config := { maxSteps := 1000000 }) only [
    cells, sepConj_emp, sepExists_sepConj_right, sepExists_sepConj_left,
    bv_sub_add_lit, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub]
  wp_pull_exists
  have hx0_eq : s0.readReg64 .x0 = pubPtr := by assumption
  have hx2_eq : s0.readReg64 .x2 = privPtr := by assumption
  have hx8_eq : s0.readReg64 .x8 = outPtr := by assumption
  subst hx0_eq hx2_eq hx8_eq
  have hfit_all : FitsEnv M lim st KemKeyPairFromPubPrivEnv := by assumption
  have hfit_ev : FitsEvents M lim st kemKeyPairFromPubPrivEvents := hfit_all _ rfl
  rw [kemKeyPairFromPubPrivEvents, fitsEvents_append] at hfit_ev
  rcases hfit_ev with ⟨hfit1, hfit2⟩
  have hfe1 : FitsEvents M lim st [.alloc 1568] := by simpa [rustAllocEvents] using hfit1
  rcases hfe1 with ⟨⟨hwma1, henf1, hram1, hva1⟩, -⟩
  have hfe2 : FitsEvents M lim (M.stepEvents (rustAllocEvents 1568 1) st) [.alloc 3168] := by
    simpa [rustAllocEvents] using hfit2
  rcases hfe2 with ⟨⟨hwma2, henf2, hram2, hva2⟩, -⟩
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay1 : RustLayoutOk 1568 1 := ⟨⟨by decide, hpow2, by decide⟩, by decide⟩
  have hlay2 : RustLayoutOk 3168 1 := ⟨⟨by decide, hpow2, by decide⟩, by decide⟩
  have hpk_len : pk.length = 1568 := by assumption
  have hsk_len : sk.length = 3168 := by assumption
  rw [pointsToBytes_cons (s0.readReg64 (.gpr 0#5)),
    pointsToBytes_cons (s0.readReg64 (.gpr 2#5))]
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  wp_simp_pre [wp_norm]
  wp_apply
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  wp_simp_pre [wp_norm]
  wp_apply with (1568, 1, st)
  wp_steps_sync_pool (lsρ lsMemcpySym)
  wp_simp_pre [wp_norm]
  rw [← hpk_len]
  wp_apply
  simp only [hpk_len] at *
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  wp_simp_pre [wp_norm]
  wp_apply
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  wp_simp_pre [wp_norm]
  wp_apply with (3168, 1, M.stepEvents (rustAllocEvents 1568 1) st)
  wp_steps_sync_pool (lsρ lsMemcpySym)
  wp_simp_pre [wp_norm]
  rw [← hsk_len]
  wp_apply
  simp only [hsk_len] at *
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_pool (s0.readReg64 (.gpr 30#5))
  simp only [kemKeyPairFromPubPrivEvents, AllocCostModel.stepEvents_append]
  wp_done

theorem kemKeyPairSerde_placed_ok_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec.keepsFs)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec.keepsFs) :
    subroutine_ok ((blkPC_113).rebase (blkPl_113).base H) (blkPl_113).base
      (withLsCodeLoaded lsmpl (kemKeyPairFromPubPrivOkSpec M A lim).keepsFs) := by
  have hinner := ls_subroutine_ok_of_block
    (callerProg := (blkPC_113).rebase (blkPl_113).base H)
    (entry := lsmpl.base 70)
    (subroutine_ok_withLsCodeLoaded_of_plain
      (kemKeyPairFromPubPriv_placed_ok_fd hshim halloc hmemcpy))
  exact subroutine_ok_of_b (by simp only [arm64_norm]; rfl)
    (by simp only [arm64_norm])
    rfl (by
      intro x s pc
      dsimp only [withLsCodeLoaded, Spec.keepsFs, kemKeyPairFromPubPrivOkSpec,
        CryptoVerification.E2E.Pqxdh.ResponderStore.kemKeyPairFromPubPrivOkSpec,
        RustCliAllocBudget.atState_pool, RustCliAllocBudget.atState_live]
      rw [setPC_pool_eq A lim x.2 s pc]
      cases s; rfl)
    hinner (by
      intro x s0 sf pc
      dsimp only [withLsCodeLoaded, Spec.keepsFs, kemKeyPairFromPubPrivOkSpec,
        CryptoVerification.E2E.Pqxdh.ResponderStore.kemKeyPairFromPubPrivOkSpec]
      cases s0; rfl)
    (by intros; rfl) (by intros; rfl)

theorem kemKeyPairFromPubPriv_withFdsGe3Closed_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec.keepsFs)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec.keepsFs) :
    subroutine_ok ((blkPC_70).rebase (blkPl_70).base H) (blkPl_70).base
      (withFdsGe3Closed (kemKeyPairFromPubPrivOkSpec M A lim)) :=
  subroutine_ok_withFdsGe3Closed_of_keepsFs
    (kemKeyPairFromPubPriv_placed_ok_fd hshim halloc hmemcpy)

theorem kemKeyPairSerde_withFdsGe3Closed_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec.keepsFs)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec.keepsFs) :
    subroutine_ok ((blkPC_113).rebase (blkPl_113).base H) (blkPl_113).base
      (withFdsGe3Closed (withLsCodeLoaded lsmpl (kemKeyPairFromPubPrivOkSpec M A lim))) := by
  have hk := kemKeyPairSerde_placed_ok_fd hshim halloc hmemcpy
  have h1 : subroutine_ok ((blkPC_113).rebase (blkPl_113).base H) (blkPl_113).base
      (withLsCodeLoaded lsmpl (kemKeyPairFromPubPrivOkSpec M A lim)).keepsFs :=
    subroutine_ok_mono hk (fun _ _ _ hp => hp) fun _ _ _ _ hq => hq
  exact subroutine_ok_withFdsGe3Closed_of_keepsFs h1

theorem kemKeyPairSerde_lsc_withFdsGe3Closed_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec.keepsFs)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec.keepsFs) :
    subroutine_ok ((blkPC_113).rebase (blkPl_113).base H) (blkPl_113).base
      (withLsCodeLoaded lsmpl (withFdsGe3Closed (kemKeyPairFromPubPrivOkSpec M A lim))) :=
  subroutine_ok_mono (kemKeyPairSerde_withFdsGe3Closed_placed_ok hshim halloc hmemcpy)
    (fun _ _ _ hp => by
      dsimp only [withLsCodeLoaded, withFdsGe3Closed] at hp ⊢
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hp)
    (fun _ _ _ _ hq => hq)

end LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.KeyPairCalleesBudgetFd
