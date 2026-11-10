/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.ShimsPlacedBudget
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# `fs`-Preserving and `FdsGe3Closed` `[LibsignalPlacement]` `IdentityFiles` Shims

Lifts the budget-threaded `get_identity_key_pair` (Block `602`) and `get_local_registration_id`
(Block `603`) shim contracts to `Spec.keepsFs` and `withFdsGe3Closed` under `AllocContractsFsPlaced`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.ShimsPlacedBudgetFd

open Arm64 Arm64.Obj ProofLib
open CryptoVerification (IsLsBlockProg LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (LibsignalCodeRoLoaded sepWP_seq_lscro withLsCodeRoLoaded)
open CryptoVerification.SignalSession (CliHooks lsRustAllocSymCli lsRustNoAllocShimSymCli)
open CryptoVerification.SignalSession.Cli (idKeyPairFutVtSym idRegIdFutVtSym)
open CryptoVerification.SignalSession.Cli.Placed
  (blkPC_602 blkPC_603 blkPl_602 blkPl_603 lsProg_602 lsProg_603)
open CryptoVerification.SignalSession.Cli.RunProofs (cliInitiateFrame cliInitiateNeed)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
  (idOwnFutBoxAtPlaced stk_sub_ge_base)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.StoreCalleesProofs
  (memRegion_16_ownBox)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Store.PkShims.Helpers (pkShimStack stackAt_pkShim)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon (ls_transfer_lscro)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget
   RustLayoutOk rustAllocEvents rustCliAllocNoOomExternSpecWithStack)
open LibsignalBinary.Heap.IfaceBudgetLemmas (rustCliAllocNoOomSpecWithStack)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (BoxAllocEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
  (shim_keepsFs_lscro_of_fs subroutine_ok_withFdsGe3Closed_of_keepsFs
   subroutine_ok_withLsCodeRoLoaded_withFdsGe3Closed_of_keepsFs)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
  (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsFsPlaced idOwnShimSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget
  (allocNoOom_lscro_of_cli lift_stk_lscro_budget)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget.AllocContractsFsPlaced
  (toAllocContractsX)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (rustAllocNoOomSpecWithStack)

section Placed

attribute [local irreducible] Program.fetch Program.externAt? FitsEvents
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem keepsFs_withLsCodeRoLoaded_eq {α : Type} (pl : Obj.MultiPlacement) (S : Spec α) :
    (withLsCodeRoLoaded pl S).keepsFs = withLsCodeRoLoaded pl S.keepsFs := rfl

/-! ## 1. Stack Lifting for `(idOwnShimSpecPlaced vtSym A lim stk).keepsFs` -/

theorem idOwnShim_keepsFs_lift_stk_placed [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64}
    {vtSym : String} {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    (hInner : subroutine_ok prog entry (idOwnShimSpecPlaced vtSym A lim pkShimStack).keepsFs)
    (hstk : 32 + extHookStack ≤ stk) :
    subroutine_ok prog entry (idOwnShimSpecPlaced vtSym A lim stk).keepsFs :=
  lift_stk_lscro_budget (pl := lsmpl) (F := fun k => (idOwnShimSpecPlaced vtSym A lim k).keepsFs)
    (P := fun (self, st) s =>
      ⌜s.readReg64 .x0 = self ∧ FitsEnv M lim st (BoxAllocEnv 16)⌝ ∗ A.pool lim st s)
    (Q := fun (self, st) s0 sf =>
      ⌜sf.fs = s0.fs⌝ ∗
      ∃∗ evs : List AllocEvent,
        ⌜sf.readReg64 .x1 = lsρ vtSym ∧ sf.readReg64 .x0 ≠ 0#64 ∧
          (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace ∧
          BoxAllocEnv 16 evs⌝ ∗
          A.live (sf.readReg64 .x0) 16 8 ∗
          idOwnFutBoxAtPlaced (sf.readReg64 .x0) self 0#8 ∗
          A.pool lim (M.stepEvents evs st) sf)
    hInner
    (by dsimp [pkShimStack]; omega)
    (by
      intro ⟨self, st⟩ s k
      dsimp only [Spec.keepsFs, idOwnShimSpecPlaced, withLsCodeRoLoaded]
      sep_ac_rfl)
    (by
      intro ⟨self, st⟩ s0 sf k
      simp only [Spec.keepsFs, idOwnShimSpecPlaced, withLsCodeRoLoaded,
        sepExists_sepConj_left, sepExists_sepConj_right]
      exact sepExists_congr fun _ => by sep_ac_rfl)

/-! ## 2. `get_identity_key_pair` Shim (Block `602`) -/

theorem idKeyPairShim_fixed_keepsFs_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFs : AllocContractsFsPlaced A lim H) :
    subroutine_ok (lsProg_602 H) (lsmpl.base 602)
      (idOwnShimSpecPlaced idKeyPairFutVtSym A lim pkShimStack).keepsFs := by
  unfold idOwnShimSpecPlaced Spec.keepsFs withLsCodeRoLoaded
  simp only [idOwnFutBoxAtPlaced, stackAt_pkShim]
  cells_unfold
  dsimp only [lsProg_602]
  change subroutine_ok ((blkPC_602).rebase (blkPl_602).base H) (blkPl_602).base _
  wp_init xs s0
  obtain ⟨self, st⟩ := xs
  dsimp only
  have hcrl0 : LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  have hfit0 : FitsEnv M lim st (BoxAllocEnv 16) := by assumption
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hlay : RustLayoutOk 16 8 := ⟨⟨by decide, hpow8, by decide⟩, by decide⟩
  have hbev : BoxAllocEnv 16 (rustAllocEvents 16 8) := Or.inr ⟨by decide, rfl⟩
  have hfit : FitsEvents M lim st (rustAllocEvents 16 8) := hfit0 _ hbev
  have halloc := allocNoOom_lscro_of_cli
    (callerProg := (blkPC_602).rebase (blkPl_602).base H) (toAllocContractsX hFs)
  dsimp only [withLsCodeRoLoaded, rustAllocNoOomSpecWithStack,
    rustCliAllocNoOomSpecWithStack] at halloc
  apply sepWP_seq_lscro (mid := lsρ lsRustNoAllocShimSymCli) hcrl0
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSymCli)
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by wp_norm_lhs)
  intro hcrl1
  wp_call_lscro
    (shim_keepsFs_lscro_of_fs (callerProg := (blkPC_602).rebase (blkPl_602).base H) hFs
      (stk := extHookStack))
    hcrl1 ()
  have hfs_shim : sf.fs = s0.fs := by assumption
  refine ProofLib.SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  apply sepWP_seq_lscro (mid := lsρ lsRustAllocSymCli) hcrl_sf
  wp_steps_sync_pool (lsρ lsRustAllocSymCli)
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by wp_norm_lhs)
  intro ⟨hcl2, hro2⟩
  wp_call halloc (16, 8, st)
  have hacp : AllocCallPreserved sf sf_1 := by assumption
  have hfs_alloc : sf_1.fs = s0.fs := hacp.1.trans hfs_shim
  have htr_s0 : sf_1.trace = s0.trace := hacp.2.1.trans (by assumption)
  have hne0 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq0 : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hne0
  simp only [memRegion_16_ownBox, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun b0 => SepWP.exists_elim fun u0 => ?_
  wp_steps_sync_pool (s0.readReg64 Reg.lr)
  wp_done

theorem idKeyPairShim_keepsFs_placed_ok_of_deps [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {stk : Nat}
    (hFs : AllocContractsFsPlaced A lim H)
    (hstk : 32 + extHookStack ≤ stk) :
    subroutine_ok (lsProg_602 H) (lsmpl.base 602)
      (idOwnShimSpecPlaced idKeyPairFutVtSym A lim stk).keepsFs :=
  idOwnShim_keepsFs_lift_stk_placed (idKeyPairShim_fixed_keepsFs_placed_ok hFs) hstk

theorem idKeyPairShim_keepsFs_placed_caller_ok_of_deps [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk H] {stk : Nat}
    (hFs : AllocContractsFsPlaced A lim H)
    (hstk : 32 + extHookStack ≤ stk)
    (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 602)
      (idOwnShimSpecPlaced idKeyPairFutVtSym A lim stk).keepsFs := by
  have h602 := idKeyPairShim_keepsFs_placed_ok_of_deps hFs hstk
  unfold idOwnShimSpecPlaced at h602 ⊢
  rw [keepsFs_withLsCodeRoLoaded_eq] at h602 ⊢
  exact ls_transfer_lscro (callerProg := callerProg) (j := 602) h602 hblk

theorem idKeyPairShim_keepsFs_cli_placed_ok [LibsignalPlacement] {W : CliHooks} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk H]
    (B : RunBudgets) (hh : RunHooksPlaced W A lim H)
    {stk : Nat} (hstk : cliInitiateNeed B ≤ stk)
    (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 602)
      (idOwnShimSpecPlaced idKeyPairFutVtSym A lim (stk - cliInitiateFrame)).keepsFs := by
  have h1 := stk_sub_ge_base hstk
  have he : 32 + extHookStack ≤ 516880 := by decide
  exact idKeyPairShim_keepsFs_placed_caller_ok_of_deps hh.allocFs (by omega) hblk

theorem idKeyPairShim_fds_cli_placed_ok [LibsignalPlacement] {W : CliHooks} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk H]
    (B : RunBudgets) (hh : RunHooksPlaced W A lim H)
    {stk : Nat} (hstk : cliInitiateNeed B ≤ stk)
    (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 602)
      (withFdsGe3Closed
        (idOwnShimSpecPlaced idKeyPairFutVtSym A lim (stk - cliInitiateFrame))) :=
  subroutine_ok_withFdsGe3Closed_of_keepsFs (idKeyPairShim_keepsFs_cli_placed_ok B hh hstk hblk)

/-! ## 3. `get_local_registration_id` Shim (Block `603`) -/

theorem idRegIdShim_fixed_keepsFs_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFs : AllocContractsFsPlaced A lim H) :
    subroutine_ok (lsProg_603 H) (lsmpl.base 603)
      (idOwnShimSpecPlaced idRegIdFutVtSym A lim pkShimStack).keepsFs := by
  unfold idOwnShimSpecPlaced Spec.keepsFs withLsCodeRoLoaded
  simp only [idOwnFutBoxAtPlaced, stackAt_pkShim]
  cells_unfold
  dsimp only [lsProg_603]
  change subroutine_ok ((blkPC_603).rebase (blkPl_603).base H) (blkPl_603).base _
  wp_init xs s0
  obtain ⟨self, st⟩ := xs
  dsimp only
  have hcrl0 : LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  have hfit0 : FitsEnv M lim st (BoxAllocEnv 16) := by assumption
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hlay : RustLayoutOk 16 8 := ⟨⟨by decide, hpow8, by decide⟩, by decide⟩
  have hbev : BoxAllocEnv 16 (rustAllocEvents 16 8) := Or.inr ⟨by decide, rfl⟩
  have hfit : FitsEvents M lim st (rustAllocEvents 16 8) := hfit0 _ hbev
  have halloc := allocNoOom_lscro_of_cli
    (callerProg := (blkPC_603).rebase (blkPl_603).base H) (toAllocContractsX hFs)
  dsimp only [withLsCodeRoLoaded, rustAllocNoOomSpecWithStack,
    rustCliAllocNoOomSpecWithStack] at halloc
  apply sepWP_seq_lscro (mid := lsρ lsRustNoAllocShimSymCli) hcrl0
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSymCli)
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by wp_norm_lhs)
  intro hcrl1
  wp_call_lscro
    (shim_keepsFs_lscro_of_fs (callerProg := (blkPC_603).rebase (blkPl_603).base H) hFs
      (stk := extHookStack))
    hcrl1 ()
  have hfs_shim : sf.fs = s0.fs := by assumption
  refine ProofLib.SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  apply sepWP_seq_lscro (mid := lsρ lsRustAllocSymCli) hcrl_sf
  wp_steps_sync_pool (lsρ lsRustAllocSymCli)
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by wp_norm_lhs)
  intro ⟨hcl2, hro2⟩
  wp_call halloc (16, 8, st)
  have hacp : AllocCallPreserved sf sf_1 := by assumption
  have hfs_alloc : sf_1.fs = s0.fs := hacp.1.trans hfs_shim
  have htr_s0 : sf_1.trace = s0.trace := hacp.2.1.trans (by assumption)
  have hne0 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq0 : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hne0
  simp only [memRegion_16_ownBox, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun b0 => SepWP.exists_elim fun u0 => ?_
  wp_steps_sync_pool (s0.readReg64 Reg.lr)
  wp_done

theorem idRegIdShim_keepsFs_placed_ok_of_deps [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {stk : Nat}
    (hFs : AllocContractsFsPlaced A lim H)
    (hstk : 32 + extHookStack ≤ stk) :
    subroutine_ok (lsProg_603 H) (lsmpl.base 603)
      (idOwnShimSpecPlaced idRegIdFutVtSym A lim stk).keepsFs :=
  idOwnShim_keepsFs_lift_stk_placed (idRegIdShim_fixed_keepsFs_placed_ok hFs) hstk

theorem idRegIdShim_keepsFs_placed_caller_ok_of_deps [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk H] {stk : Nat}
    (hFs : AllocContractsFsPlaced A lim H)
    (hstk : 32 + extHookStack ≤ stk)
    (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 603)
      (idOwnShimSpecPlaced idRegIdFutVtSym A lim stk).keepsFs := by
  have h603 := idRegIdShim_keepsFs_placed_ok_of_deps hFs hstk
  unfold idOwnShimSpecPlaced at h603 ⊢
  rw [keepsFs_withLsCodeRoLoaded_eq] at h603 ⊢
  exact ls_transfer_lscro (callerProg := callerProg) (j := 603) h603 hblk

theorem idRegIdShim_keepsFs_cli_placed_ok [LibsignalPlacement] {W : CliHooks} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk H]
    (B : RunBudgets) (hh : RunHooksPlaced W A lim H)
    {stk : Nat} (hstk : cliInitiateNeed B ≤ stk)
    (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 603)
      (idOwnShimSpecPlaced idRegIdFutVtSym A lim (stk - cliInitiateFrame)).keepsFs := by
  have h1 := stk_sub_ge_base hstk
  have he : 32 + extHookStack ≤ 516880 := by decide
  exact idRegIdShim_keepsFs_placed_caller_ok_of_deps hh.allocFs (by omega) hblk

theorem idRegIdShim_fds_cli_placed_ok [LibsignalPlacement] {W : CliHooks} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk H]
    (B : RunBudgets) (hh : RunHooksPlaced W A lim H)
    {stk : Nat} (hstk : cliInitiateNeed B ≤ stk)
    (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 603)
      (withFdsGe3Closed
        (idOwnShimSpecPlaced idRegIdFutVtSym A lim (stk - cliInitiateFrame))) :=
  subroutine_ok_withFdsGe3Closed_of_keepsFs (idRegIdShim_keepsFs_cli_placed_ok B hh hstk hblk)

end Placed

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.ShimsPlacedBudgetFd
