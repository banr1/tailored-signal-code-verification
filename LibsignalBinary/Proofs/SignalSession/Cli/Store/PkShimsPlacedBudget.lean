/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkShimsPlaced
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable Pre-Key Store Shims

Proves budget-threaded `[LibsignalPlacement]` contracts for the pre-key store `async_trait` shims
in Blocks `606`, `608`, `610`, `611`, and `613`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.PkShimsPlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoVerification (IsLsBlockProg LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (LibsignalCodeRoLoaded sepWP_seq_lscro withLsCodeRoLoaded)
open CryptoVerification.SignalSession (lsRustAllocSymCli lsRustNoAllocShimSymCli)
open CryptoVerification.SignalSession.Cli
  (KpkMarkShimCall PkShimCall kpkGetFutVtSym kpkMarkBoxAt kpkMarkFutVtSym pkBoxAt pkGetFutVtSym
   pkRemoveFutVtSym spkGetFutVtSym)
open CryptoVerification.SignalSession.Cli.Placed
  (blkPC_606 blkPC_608 blkPC_610 blkPC_611 blkPC_613
   blkPl_606 blkPl_608 blkPl_610 blkPl_611 blkPl_613
   lsProg_606 lsProg_608 lsProg_610 lsProg_611 lsProg_613)
open CryptoVerification.SignalSession.Cli.Store.PkShims
  (kpkMarkShimStackPlaced pkShimStackPlaced)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget RustLayoutOk
   rustAllocEvents rustCliAllocNoOomExternSpecWithStack)
open LibsignalBinary.Heap.IfaceBudgetLemmas (rustCliAllocNoOomSpecWithStack)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (rustAllocNoOomExternSpecWithStack)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (BoxAllocEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsXCliPlaced kpkMarkShimSpecPlaced pkShimSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget
  (allocNoOomExtern_lscro_of_cli lift_stk_lscro_budget shim_lscro_of_cli)

section Placed

attribute [local irreducible] Program.fetch Program.externAt? FitsEvents
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem stackAt_pkShim_placed (sp : BitVec 64) :
    stackAt sp pkShimStackPlaced =
      stackAt (sp - 32#64) extHookStack ∗ cells (sp - 32#64) 4 :=
  ProofLib.stackAt_split_cells sp extHookStack 4 (by decide)

private theorem stackAt_kpkMarkShim_placed (sp : BitVec 64) :
    stackAt sp kpkMarkShimStackPlaced =
      stackAt (sp - 48#64) extHookStack ∗ cells (sp - 48#64) 6 :=
  ProofLib.stackAt_split_cells sp extHookStack 6 (by decide)

private theorem memRegion_16_box_placed (p : BitVec 64) :
    memRegion p 16 =
      (∃∗ b0 : BitVec 8, ∃∗ u1 : BitVec 32, ∃∗ u0 : BitVec 64,
        (p ↦₆₄ u0) ∗ ((p + 8#64) ↦₃₂ u1) ∗ ((p + 12#64) ↦₈ b0) ∗
        memRegion (p + 13#64) 3) := by
  rw [memRegion_split p 8 8 (by decide),
    memRegion_split (p + 8#64) 4 4 (by decide),
    memRegion_split (p + 8#64 + 4#64) 1 3 (by decide),
    memRegion_one, ProofLib.memRegion_four, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem memRegion_32_kpkMarkBox_placed (p : BitVec 64) :
    memRegion p 32 =
      (∃∗ b0 : BitVec 8, ∃∗ u3 : BitVec 32, ∃∗ u2 : BitVec 32,
        ∃∗ u1 : BitVec 64, ∃∗ u0 : BitVec 64,
        (p ↦₆₄ u0) ∗ ((p + 8#64) ↦₆₄ u1) ∗ ((p + 16#64) ↦₃₂ u2) ∗
        ((p + 20#64) ↦₃₂ u3) ∗ ((p + 24#64) ↦₈ b0) ∗
        memRegion (p + 25#64) 7) := by
  rw [memRegion_split p 8 24 (by decide),
    memRegion_split (p + 8#64) 8 16 (by decide),
    memRegion_split (p + 8#64 + 8#64) 4 12 (by decide),
    memRegion_split (p + 8#64 + 8#64 + 4#64) 4 8 (by decide),
    memRegion_split (p + 8#64 + 8#64 + 4#64 + 4#64) 1 7 (by decide),
    memRegion_one, ProofLib.memRegion_four, ProofLib.memRegion_four,
    ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem pkShim_lift_stk_placed [LibsignalPlacement] {vtSym : String}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry : BitVec 64} {stk : Nat}
    (hInner : subroutine_ok prog entry (pkShimSpecPlaced vtSym A lim pkShimStackPlaced))
    (hstk : 0x20 + extHookStack ≤ stk) :
    subroutine_ok prog entry (pkShimSpecPlaced vtSym A lim stk) :=
  lift_stk_lscro_budget (pl := lsmpl) (F := pkShimSpecPlaced vtSym A lim)
    (P := fun (x, st) s =>
      ⌜s.readReg64 .x0 = x.self ∧ s.readReg32 .x1 = x.id ∧
        FitsEnv M lim st (BoxAllocEnv 16)⌝ ∗ A.pool lim st s)
    (Q := fun (x, st) s0 sf =>
      ∃∗ evs : List AllocEvent,
        ⌜sf.readReg64 .x1 = lsρ vtSym ∧ sf.readReg64 .x0 ≠ 0#64 ∧
          (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace ∧
          BoxAllocEnv 16 evs⌝ ∗
          A.live (sf.readReg64 .x0) 16 8 ∗ pkBoxAt (sf.readReg64 .x0) x.self x.id 0#8 ∗
          A.pool lim (M.stepEvents evs st) sf)
    hInner
    (by dsimp [pkShimStackPlaced]; omega)
    (by
      intro ⟨x, st⟩ s k
      dsimp only [pkShimSpecPlaced, withLsCodeRoLoaded]
      sep_ac_rfl)
    (by
      intro ⟨x, st⟩ s0 sf k
      simp only [pkShimSpecPlaced, withLsCodeRoLoaded, sepExists_sepConj_left]
      exact sepExists_congr fun _ => by sep_ac_rfl)

theorem spkGetShim_placed_fixed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : AllocContractsXCliPlaced A lim H) :
    subroutine_ok (lsProg_606 H) (lsmpl.base 606)
      (pkShimSpecPlaced spkGetFutVtSym A lim pkShimStackPlaced) := by
  unfold pkShimSpecPlaced withLsCodeRoLoaded
  simp only [pkBoxAt, stackAt_pkShim_placed]
  cells_unfold
  dsimp only [lsProg_606]
  change subroutine_ok ((blkPC_606).rebase (blkPl_606).base H) (blkPl_606).base _
  wp_init xs s0
  obtain ⟨⟨self, id⟩, st⟩ := xs
  dsimp only
  have hcrl0 : LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  have hfit0 : FitsEnv M lim st (BoxAllocEnv 16) := by assumption
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hlay : RustLayoutOk 16 8 := ⟨⟨by decide, hpow8, by decide⟩, by decide⟩
  have hbev : BoxAllocEnv 16 (rustAllocEvents 16 8) := Or.inr ⟨by decide, rfl⟩
  have hfit : FitsEvents M lim st (rustAllocEvents 16 8) := hfit0 _ hbev
  have halloc := allocNoOomExtern_lscro_of_cli
    (callerProg := (blkPC_606).rebase (blkPl_606).base H) hC
  dsimp only [withLsCodeRoLoaded, rustAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomExternSpecWithStack,
    rustCliAllocNoOomExternSpecWithStack, rustCliAllocNoOomSpecWithStack] at halloc
  apply sepWP_seq_lscro (mid := lsρ lsRustNoAllocShimSymCli) hcrl0
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSymCli)
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by wp_norm_lhs)
  intro hcrl1
  wp_call_lscro
    (shim_lscro_of_cli (callerProg := (blkPC_606).rebase (blkPl_606).base H) hC (stk := extHookStack))
    hcrl1 ()
  refine ProofLib.SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  apply sepWP_seq_lscro (mid := lsρ lsRustAllocSymCli) hcrl_sf
  wp_steps_sync_pool (lsρ lsRustAllocSymCli)
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by wp_norm_lhs)
  intro ⟨hcl2, hro2⟩
  wp_call halloc (16, 8, st)
  have hne0 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq0 : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hne0
  simp only [memRegion_16_box_placed, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun b0 => SepWP.exists_elim fun u1 =>
    SepWP.exists_elim fun u0 => ?_
  wp_steps_sync_pool (s0.readReg64 Reg.lr)
  wp_done

theorem pkGetShim_placed_fixed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : AllocContractsXCliPlaced A lim H) :
    subroutine_ok (lsProg_608 H) (lsmpl.base 608)
      (pkShimSpecPlaced pkGetFutVtSym A lim pkShimStackPlaced) := by
  unfold pkShimSpecPlaced withLsCodeRoLoaded
  simp only [pkBoxAt, stackAt_pkShim_placed]
  cells_unfold
  dsimp only [lsProg_608]
  change subroutine_ok ((blkPC_608).rebase (blkPl_608).base H) (blkPl_608).base _
  wp_init xs s0
  obtain ⟨⟨self, id⟩, st⟩ := xs
  dsimp only
  have hcrl0 : LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  have hfit0 : FitsEnv M lim st (BoxAllocEnv 16) := by assumption
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hlay : RustLayoutOk 16 8 := ⟨⟨by decide, hpow8, by decide⟩, by decide⟩
  have hbev : BoxAllocEnv 16 (rustAllocEvents 16 8) := Or.inr ⟨by decide, rfl⟩
  have hfit : FitsEvents M lim st (rustAllocEvents 16 8) := hfit0 _ hbev
  have halloc := allocNoOomExtern_lscro_of_cli
    (callerProg := (blkPC_608).rebase (blkPl_608).base H) hC
  dsimp only [withLsCodeRoLoaded, rustAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomExternSpecWithStack,
    rustCliAllocNoOomExternSpecWithStack, rustCliAllocNoOomSpecWithStack] at halloc
  apply sepWP_seq_lscro (mid := lsρ lsRustNoAllocShimSymCli) hcrl0
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSymCli)
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by wp_norm_lhs)
  intro hcrl1
  wp_call_lscro
    (shim_lscro_of_cli (callerProg := (blkPC_608).rebase (blkPl_608).base H) hC (stk := extHookStack))
    hcrl1 ()
  refine ProofLib.SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  apply sepWP_seq_lscro (mid := lsρ lsRustAllocSymCli) hcrl_sf
  wp_steps_sync_pool (lsρ lsRustAllocSymCli)
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by wp_norm_lhs)
  intro ⟨hcl2, hro2⟩
  wp_call halloc (16, 8, st)
  have hne0 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq0 : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hne0
  simp only [memRegion_16_box_placed, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun b0 => SepWP.exists_elim fun u1 =>
    SepWP.exists_elim fun u0 => ?_
  wp_steps_sync_pool (s0.readReg64 Reg.lr)
  wp_done

theorem pkRemoveShim_placed_fixed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : AllocContractsXCliPlaced A lim H) :
    subroutine_ok (lsProg_610 H) (lsmpl.base 610)
      (pkShimSpecPlaced pkRemoveFutVtSym A lim pkShimStackPlaced) := by
  unfold pkShimSpecPlaced withLsCodeRoLoaded
  simp only [pkBoxAt, stackAt_pkShim_placed]
  cells_unfold
  dsimp only [lsProg_610]
  change subroutine_ok ((blkPC_610).rebase (blkPl_610).base H) (blkPl_610).base _
  wp_init xs s0
  obtain ⟨⟨self, id⟩, st⟩ := xs
  dsimp only
  have hcrl0 : LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  have hfit0 : FitsEnv M lim st (BoxAllocEnv 16) := by assumption
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hlay : RustLayoutOk 16 8 := ⟨⟨by decide, hpow8, by decide⟩, by decide⟩
  have hbev : BoxAllocEnv 16 (rustAllocEvents 16 8) := Or.inr ⟨by decide, rfl⟩
  have hfit : FitsEvents M lim st (rustAllocEvents 16 8) := hfit0 _ hbev
  have halloc := allocNoOomExtern_lscro_of_cli
    (callerProg := (blkPC_610).rebase (blkPl_610).base H) hC
  dsimp only [withLsCodeRoLoaded, rustAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomExternSpecWithStack,
    rustCliAllocNoOomExternSpecWithStack, rustCliAllocNoOomSpecWithStack] at halloc
  apply sepWP_seq_lscro (mid := lsρ lsRustNoAllocShimSymCli) hcrl0
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSymCli)
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by wp_norm_lhs)
  intro hcrl1
  wp_call_lscro
    (shim_lscro_of_cli (callerProg := (blkPC_610).rebase (blkPl_610).base H) hC (stk := extHookStack))
    hcrl1 ()
  refine ProofLib.SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  apply sepWP_seq_lscro (mid := lsρ lsRustAllocSymCli) hcrl_sf
  wp_steps_sync_pool (lsρ lsRustAllocSymCli)
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by wp_norm_lhs)
  intro ⟨hcl2, hro2⟩
  wp_call halloc (16, 8, st)
  have hne0 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq0 : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hne0
  simp only [memRegion_16_box_placed, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun b0 => SepWP.exists_elim fun u1 =>
    SepWP.exists_elim fun u0 => ?_
  wp_steps_sync_pool (s0.readReg64 Reg.lr)
  wp_done

theorem kpkGetShim_placed_fixed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : AllocContractsXCliPlaced A lim H) :
    subroutine_ok (lsProg_611 H) (lsmpl.base 611)
      (pkShimSpecPlaced kpkGetFutVtSym A lim pkShimStackPlaced) := by
  unfold pkShimSpecPlaced withLsCodeRoLoaded
  simp only [pkBoxAt, stackAt_pkShim_placed]
  cells_unfold
  dsimp only [lsProg_611]
  change subroutine_ok ((blkPC_611).rebase (blkPl_611).base H) (blkPl_611).base _
  wp_init xs s0
  obtain ⟨⟨self, id⟩, st⟩ := xs
  dsimp only
  have hcrl0 : LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  have hfit0 : FitsEnv M lim st (BoxAllocEnv 16) := by assumption
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hlay : RustLayoutOk 16 8 := ⟨⟨by decide, hpow8, by decide⟩, by decide⟩
  have hbev : BoxAllocEnv 16 (rustAllocEvents 16 8) := Or.inr ⟨by decide, rfl⟩
  have hfit : FitsEvents M lim st (rustAllocEvents 16 8) := hfit0 _ hbev
  have halloc := allocNoOomExtern_lscro_of_cli
    (callerProg := (blkPC_611).rebase (blkPl_611).base H) hC
  dsimp only [withLsCodeRoLoaded, rustAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomExternSpecWithStack,
    rustCliAllocNoOomExternSpecWithStack, rustCliAllocNoOomSpecWithStack] at halloc
  apply sepWP_seq_lscro (mid := lsρ lsRustNoAllocShimSymCli) hcrl0
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSymCli)
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by wp_norm_lhs)
  intro hcrl1
  wp_call_lscro
    (shim_lscro_of_cli (callerProg := (blkPC_611).rebase (blkPl_611).base H) hC (stk := extHookStack))
    hcrl1 ()
  refine ProofLib.SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  apply sepWP_seq_lscro (mid := lsρ lsRustAllocSymCli) hcrl_sf
  wp_steps_sync_pool (lsρ lsRustAllocSymCli)
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by wp_norm_lhs)
  intro ⟨hcl2, hro2⟩
  wp_call halloc (16, 8, st)
  have hne0 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq0 : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hne0
  simp only [memRegion_16_box_placed, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun b0 => SepWP.exists_elim fun u1 =>
    SepWP.exists_elim fun u0 => ?_
  wp_steps_sync_pool (s0.readReg64 Reg.lr)
  wp_done

theorem kpkMarkShim_placed_fixed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : AllocContractsXCliPlaced A lim H) :
    subroutine_ok (lsProg_613 H) (lsmpl.base 613)
      (kpkMarkShimSpecPlaced A lim kpkMarkShimStackPlaced) := by
  unfold kpkMarkShimSpecPlaced withLsCodeRoLoaded
  simp only [kpkMarkBoxAt, stackAt_kpkMarkShim_placed]
  cells_unfold
  dsimp only [lsProg_613]
  change subroutine_ok ((blkPC_613).rebase (blkPl_613).base H) (blkPl_613).base _
  wp_init xs s0
  obtain ⟨⟨self, id, signedId, baseKeyA⟩, st⟩ := xs
  dsimp only
  have hcrl0 : LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  have hfit0 : FitsEnv M lim st (BoxAllocEnv 32) := by assumption
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hlay : RustLayoutOk 32 8 := ⟨⟨by decide, hpow8, by decide⟩, by decide⟩
  have hbev : BoxAllocEnv 32 (rustAllocEvents 32 8) := Or.inr ⟨by decide, rfl⟩
  have hfit : FitsEvents M lim st (rustAllocEvents 32 8) := hfit0 _ hbev
  have halloc := allocNoOomExtern_lscro_of_cli
    (callerProg := (blkPC_613).rebase (blkPl_613).base H) hC
  dsimp only [withLsCodeRoLoaded, rustAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomExternSpecWithStack,
    rustCliAllocNoOomExternSpecWithStack, rustCliAllocNoOomSpecWithStack] at halloc
  apply sepWP_seq_lscro (mid := lsρ lsRustNoAllocShimSymCli) hcrl0
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSymCli)
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by wp_norm_lhs)
  intro hcrl1
  wp_call_lscro
    (shim_lscro_of_cli (callerProg := (blkPC_613).rebase (blkPl_613).base H) hC (stk := extHookStack))
    hcrl1 ()
  refine ProofLib.SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  apply sepWP_seq_lscro (mid := lsρ lsRustAllocSymCli) hcrl_sf
  wp_steps_sync_pool (lsρ lsRustAllocSymCli)
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by wp_norm_lhs)
  intro ⟨hcl2, hro2⟩
  wp_call halloc (32, 8, st)
  have hne0 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq0 : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hne0
  simp only [memRegion_32_kpkMarkBox_placed, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun b0 => SepWP.exists_elim fun u3 =>
    SepWP.exists_elim fun u2 => SepWP.exists_elim fun u1 =>
    SepWP.exists_elim fun u0 => ?_
  wp_steps_sync_pool (s0.readReg64 Reg.lr)
  wp_done

/-- The `get_signed_pre_key` shim (Block `606`) meets `pkShimSpecPlaced spkGetFutVtSym A lim stk`. -/
theorem spkGetShim_placed_ok_of_deps [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {stk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (hstk : 0x20 + extHookStack ≤ stk) :
    subroutine_ok (lsProg_606 H) (lsmpl.base 606)
      (pkShimSpecPlaced spkGetFutVtSym A lim stk) :=
  pkShim_lift_stk_placed (spkGetShim_placed_fixed_ok hC) hstk

/-- The `get_pre_key` shim (Block `608`) meets `pkShimSpecPlaced pkGetFutVtSym A lim stk`. -/
theorem pkGetShim_placed_ok_of_deps [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {stk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (hstk : 0x20 + extHookStack ≤ stk) :
    subroutine_ok (lsProg_608 H) (lsmpl.base 608)
      (pkShimSpecPlaced pkGetFutVtSym A lim stk) :=
  pkShim_lift_stk_placed (pkGetShim_placed_fixed_ok hC) hstk

/-- The `remove_pre_key` shim (Block `610`) meets `pkShimSpecPlaced pkRemoveFutVtSym A lim stk`. -/
theorem pkRemoveShim_placed_ok_of_deps [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {stk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (hstk : 0x20 + extHookStack ≤ stk) :
    subroutine_ok (lsProg_610 H) (lsmpl.base 610)
      (pkShimSpecPlaced pkRemoveFutVtSym A lim stk) :=
  pkShim_lift_stk_placed (pkRemoveShim_placed_fixed_ok hC) hstk

/-- The `get_kyber_pre_key` shim (Block `611`) meets `pkShimSpecPlaced kpkGetFutVtSym A lim stk`. -/
theorem kpkGetShim_placed_ok_of_deps [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {stk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (hstk : 0x20 + extHookStack ≤ stk) :
    subroutine_ok (lsProg_611 H) (lsmpl.base 611)
      (pkShimSpecPlaced kpkGetFutVtSym A lim stk) :=
  pkShim_lift_stk_placed (kpkGetShim_placed_fixed_ok hC) hstk

/-- The `mark_kyber_pre_key_used` shim (Block `613`) meets `kpkMarkShimSpecPlaced A lim stk`. -/
theorem kpkMarkShim_placed_ok_of_deps [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {stk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (hstk : 0x30 + extHookStack ≤ stk) :
    subroutine_ok (lsProg_613 H) (lsmpl.base 613)
      (kpkMarkShimSpecPlaced A lim stk) :=
  lift_stk_lscro_budget (pl := lsmpl) (F := kpkMarkShimSpecPlaced A lim)
    (P := fun (x, st) s =>
      ⌜s.readReg64 .x0 = x.self ∧ s.readReg32 .x1 = x.id ∧ s.readReg32 .x2 = x.signedId ∧
        s.readReg64 .x3 = x.baseKeyA ∧
        FitsEnv M lim st (BoxAllocEnv 32)⌝ ∗ A.pool lim st s)
    (Q := fun (x, st) s0 sf =>
      ∃∗ evs : List AllocEvent,
        ⌜sf.readReg64 .x1 = lsρ kpkMarkFutVtSym ∧ sf.readReg64 .x0 ≠ 0#64 ∧
          (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace ∧
          BoxAllocEnv 32 evs⌝ ∗
          A.live (sf.readReg64 .x0) 32 8 ∗
          kpkMarkBoxAt (sf.readReg64 .x0) x.self x.baseKeyA x.id x.signedId 0#8 ∗
          A.pool lim (M.stepEvents evs st) sf)
    (kpkMarkShim_placed_fixed_ok hC)
    (by dsimp [kpkMarkShimStackPlaced]; omega)
    (by
      intro ⟨x, st⟩ s k
      dsimp only [kpkMarkShimSpecPlaced, withLsCodeRoLoaded]
      sep_ac_rfl)
    (by
      intro ⟨x, st⟩ s0 sf k
      simp only [kpkMarkShimSpecPlaced, withLsCodeRoLoaded, sepExists_sepConj_left]
      exact sepExists_congr fun _ => by sep_ac_rfl)

end Placed

end LibsignalBinary.Proofs.SignalSession.Cli.Store.PkShimsPlacedBudget
