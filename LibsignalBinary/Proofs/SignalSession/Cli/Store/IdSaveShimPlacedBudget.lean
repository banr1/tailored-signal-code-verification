/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSaveShimPlaced
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable `<IdentityFiles as IdentityKeyStore>::save_identity` Shim

Proves budget-threaded `idSaveShimSpecPlaced` on Block `600` (`lsProg_600 H`) under
`[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSaveShimPlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoVerification (IsLsBlockProg LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.LibsignalTripleRatchet (extHookStack withStack)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (IdentityShimCall LibsignalCodeRoLoaded sepWP_seq_lscro withLsCodeRoLoaded)
open CryptoVerification.SignalSession (lsRustAllocSymCli lsRustNoAllocShimSymCli)
open CryptoVerification.SignalSession.Cli (idSaveBoxAt idSaveFutVtSym)
open CryptoVerification.SignalSession.Cli.Placed (blkPC_600 blkPl_600 lsProg_600)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon (ls_transfer_lscro)
open CryptoVerification.SignalSession.Cli.Store.IdSaveShim (idSaveShimStackPlaced)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget RustLayoutOk
   rustAllocEvents rustCliAllocNoOomExternSpecWithStack)
open LibsignalBinary.Heap.IfaceBudgetLemmas (rustCliAllocNoOomSpecWithStack)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (rustAllocNoOomExternSpecWithStack)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (BoxAllocEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsXCliPlaced idSaveShimSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget
  (allocNoOomExtern_lscro_of_cli lift_stk_lscro_budget shim_lscro_of_cli)

section Placed

attribute [local irreducible] Program.fetch Program.externAt? FitsEvents
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem stackAt_idSaveShim_placed (sp : BitVec 64) :
    stackAt sp idSaveShimStackPlaced =
      stackAt (sp - 48#64) extHookStack ∗ cells (sp - 48#64) 6 :=
  ProofLib.stackAt_split_cells sp extHookStack 6 (by decide)

private theorem memRegion_32_box_placed (p : BitVec 64) :
    memRegion p 32 =
      (∃∗ b0 : BitVec 8, ∃∗ u2 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u0 : BitVec 64,
        (p ↦₆₄ u0) ∗ ((p + 8#64) ↦₆₄ u1) ∗ ((p + 16#64) ↦₆₄ u2) ∗ ((p + 24#64) ↦₈ b0) ∗
        memRegion (p + 25#64) 7) := by
  rw [memRegion_split p 8 24 (by decide),
    memRegion_split (p + 8#64) 8 16 (by decide),
    memRegion_split (p + 8#64 + 8#64) 8 8 (by decide),
    memRegion_split (p + 8#64 + 8#64 + 8#64) 1 7 (by decide),
    memRegion_one, ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem sepWP_pure_mid {prog : Program} {ret : BitVec 64} {s : State}
    {P Q : SepProp} {φ : Prop} {post : State → SepProp → Prop}
    (h : φ → SepWP prog ret s (P ∗ Q) post) :
    SepWP prog ret s (P ∗ ⌜φ⌝ ∗ Q) post := by
  rw [show P ∗ ⌜φ⌝ ∗ Q = ⌜φ⌝ ∗ P ∗ Q by sep_ac_rfl]
  exact SepWP.pure_elim h

theorem idSaveShim_placed_fixed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : AllocContractsXCliPlaced A lim H) :
    subroutine_ok (lsProg_600 H) (lsmpl.base 600)
      (idSaveShimSpecPlaced A lim idSaveShimStackPlaced) := by
  unfold idSaveShimSpecPlaced withLsCodeRoLoaded
  simp only [idSaveBoxAt, stackAt_idSaveShim_placed]
  cells_unfold
  dsimp only [lsProg_600]
  change subroutine_ok ((blkPC_600).rebase (blkPl_600).base H) (blkPl_600).base _
  wp_init xs s0
  obtain ⟨⟨self, addrA, keyA⟩, st⟩ := xs
  dsimp only
  have hcrl0 : LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  have hfit0 : FitsEnv M lim st (BoxAllocEnv 32) := by assumption
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hlay : RustLayoutOk 32 8 := ⟨⟨by decide, hpow8, by decide⟩, by decide⟩
  have hbev : BoxAllocEnv 32 (rustAllocEvents 32 8) := Or.inr ⟨by decide, rfl⟩
  have hfit : FitsEvents M lim st (rustAllocEvents 32 8) := hfit0 _ hbev
  have halloc := allocNoOomExtern_lscro_of_cli
    (callerProg := (blkPC_600).rebase (blkPl_600).base H) hC
  dsimp only [withLsCodeRoLoaded, rustAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomExternSpecWithStack,
    rustCliAllocNoOomExternSpecWithStack, rustCliAllocNoOomSpecWithStack] at halloc
  apply sepWP_seq_lscro (mid := lsρ lsRustNoAllocShimSymCli) hcrl0
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSymCli)
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by wp_norm_lhs)
  intro hcrl1
  wp_call_lscro
    (shim_lscro_of_cli (callerProg := (blkPC_600).rebase (blkPl_600).base H) hC (stk := extHookStack))
    hcrl1 ()
  refine ProofLib.SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  apply sepWP_seq_lscro (mid := lsρ lsRustAllocSymCli) hcrl_sf
  wp_steps_sync_pool (lsρ lsRustAllocSymCli)
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by wp_norm_lhs)
  intro ⟨hcl2, hro2⟩
  wp_call halloc (32, 8, st)
  have hne0 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq0 : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hne0
  simp only [memRegion_32_box_placed, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun b0 => SepWP.exists_elim fun u2 =>
    SepWP.exists_elim fun u1 => SepWP.exists_elim fun u0 => ?_
  wp_steps_sync_pool (s0.readReg64 Reg.lr)
  wp_done

/-- The `save_identity` shim (Block `600`) meets `idSaveShimSpecPlaced A lim stk`. -/
theorem idSaveShim_placed_ok_of_deps [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {stk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (hstk : 0x30 + extHookStack ≤ stk) :
    subroutine_ok (lsProg_600 H) (lsmpl.base 600) (idSaveShimSpecPlaced A lim stk) :=
  lift_stk_lscro_budget (pl := lsmpl) (F := idSaveShimSpecPlaced A lim)
    (P := fun (x, st) s =>
      ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x1 = x.addrA ∧ s.readReg64 .x2 = x.keyA ∧
        FitsEnv M lim st (BoxAllocEnv 32)⌝ ∗ A.pool lim st s)
    (Q := fun (x, st) s0 sf =>
      ∃∗ evs : List AllocEvent,
        ⌜sf.readReg64 .x1 = lsρ idSaveFutVtSym ∧ sf.readReg64 .x0 ≠ 0#64 ∧
          (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace ∧
          BoxAllocEnv 32 evs⌝ ∗
          A.live (sf.readReg64 .x0) 32 8 ∗
          idSaveBoxAt (sf.readReg64 .x0) x.self x.addrA x.keyA 0#8 ∗
          A.pool lim (M.stepEvents evs st) sf)
    (idSaveShim_placed_fixed_ok hC)
    (by dsimp [idSaveShimStackPlaced]; omega)
    (by
      intro ⟨x, st⟩ s k
      dsimp only [idSaveShimSpecPlaced, withLsCodeRoLoaded]
      sep_ac_rfl)
    (by
      intro ⟨x, st⟩ s0 sf k
      simp only [idSaveShimSpecPlaced, withLsCodeRoLoaded, sepExists_sepConj_left]
      exact sepExists_congr fun _ => by sep_ac_rfl)

theorem idSaveShim_placed_caller_ok_of_deps [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk H] {stk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (hstk : 0x30 + extHookStack ≤ stk)
    (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 600) (idSaveShimSpecPlaced A lim stk) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 600)
    (idSaveShim_placed_ok_of_deps hC hstk) hblk

end Placed

end LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSaveShimPlacedBudget
