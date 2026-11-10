/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.PublicApi.StoreKit.FsFds
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitFdsPilotPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.PreKeySpecsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkShimsPlacedBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Placed Budgeted `PreKeyStoreSpec` with Closed-FD Invariant

Establishes `PreKeyStoreKitPlacedOkFds` (`fds = true`) on `cliPreKeyStoreSpecPlaced`
(`OneTimePreKeyFiles`), shim `Spec.keepsFs` contracts on Blocks `608` and `610`,
`withFdsGe3Closed` poll lifting on Blocks `573` and `575`, and `writeFileHook` preservation of
`FdsGe3Closed`.
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.KitInst.PreKeyKitFdsPlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.RecordCodecs (PreKeyRecord)
open CryptoVerification.RecordCodecsBinary (preKeyResultAt)
open CryptoVerification.LibsignalTripleRatchet (extHookStack withStack)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles LibsignalCodeRoLoaded PreKeyPollCall PreKeyShimCall PreKeyStoreSpec TraceFsSound
   extract_withLsCodeRoLoaded ls_subroutine_ok_rocl_of_block preKeyGetPollOutAt
   preKeyRemovePollOutAt sepWP_seq_lscro withEnvPre withLsCodeRoLoaded withLsRoCl)
open LibsignalBinary.Proofs.PublicApi.StoreKit.FsFds (FsAtFds)
open CryptoVerification.SignalSession
  (lsDropOffPlaced lsDropOffPlaced_eq lsRustAllocSymCli lsRustNoAllocShimSymCli writeFileHook)
open CryptoVerification.SignalSession.Cli
  (DirGhost PkNameOk PkPollGhost PkSizeOk ReadRule dirAt keyName pkAnsAt pkAnsOf pkBoxAt
   pkGetAnsAt pkGetFutVtSym pkRemoveFutVtSym pkRemoveOf pkRemoveOutAt)
open CryptoVerification.SignalSession.Cli.Placed
  (blkPC_608 blkPC_610 blkPl_608 blkPl_610 lsProg_573 lsProg_575 lsProg_608 lsProg_610)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon
  (ls_transfer_lscro satisfies_lscro_pre)
open CryptoVerification.SignalSession.Cli.Store.PkShims (pkShimStackPlaced)
open CryptoVerification.SignalSession.Cli.KitInst
  (CliPkInv cliPkStoreAt cliPreKeyStoreSpec cliPreKeyStoreSpecPlaced
   cliPreKeyStoreSpecPlaced_quiet pkGetAnsAt_entails_pollOut_placed
   pkRemoveOutAt_entails_pollOut_placed)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents
   RustCliAllocBudget RustLayoutOk rustAllocEvents)
open LibsignalBinary.Heap.IfaceBudgetLemmas (rustCliAllocNoOomSpecWithStack)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (rustAllocNoOomSpecWithStack)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget
  (BoxAllocEnv PreKeyStoreBudgetEnv kitPreKeyGetPollSpec kitPreKeyGetPollSpecE
   kitPreKeyGetShimSpec kitPreKeyRemovePollSpec kitPreKeyRemovePollSpecE kitPreKeyRemoveShimSpec)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (PreKeyStoreKitPlacedOkFds)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsFsPlaced pkGetPollSpecOfPlaced pkGetPollSpecPlaced pkRemovePollSpecPlaced
   pkShimSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget
  (allocNoOom_lscro_of_cli lift_stk_lscro_budget)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget.AllocContractsFsPlaced
  (toAllocContractsX)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitFdsPilotPlacedBudget
  (cliIdFutDrop_fds_rocl_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed fdsGe3Closed_writeFileHook hookOk_withFdsGe3Closed_writeFileHook withFdsGe3Closed)

@[simp]
theorem cliPreKeyStoreSpecPlaced_fdsOk [LibsignalPlacement] (A : RustAlloc)
    (rd : ReadRule) (F0 : FsFiles) (pathOk : List (BitVec 8) → Prop) (pid : BitVec 32)
    (s1 s2 s3 s4 : Nat) (fs : FsState) :
    (cliPreKeyStoreSpecPlaced A rd F0 pathOk pid s1 s2 s3 s4).fdsOk fs = FdsGe3Closed fs :=
  rfl

/-! ## Shim `keepsFs` and `fds = true` contracts -/

section Shims

attribute [local irreducible] Program.fetch Program.externAt? FitsEvents
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem shim_keepsFs_lscro_of_fs [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i H]
    (hFs : AllocContractsFsPlaced A lim H)
    {stk : Nat} (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsρ lsRustNoAllocShimSymCli)
      (withLsCodeRoLoaded lsmpl (withStack sessionShimBudgetSpec stk).keepsFs) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 617) (hFs.shim stk h1 h2) hi

private theorem stackAt_pkShim_placed (sp : BitVec 64) :
    stackAt sp pkShimStackPlaced =
      stackAt (sp - 32#64) extHookStack ∗ cells (sp - 32#64) 4 :=
  ProofLib.stackAt_split_cells sp extHookStack 4 (by decide)

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

private theorem pkShim_lift_stk_keepsFs_placed [LibsignalPlacement] {vtSym : String}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry : BitVec 64} {stk : Nat}
    (hInner : subroutine_ok prog entry (pkShimSpecPlaced vtSym A lim pkShimStackPlaced).keepsFs)
    (hstk : 0x20 + extHookStack ≤ stk) :
    subroutine_ok prog entry (pkShimSpecPlaced vtSym A lim stk).keepsFs :=
  lift_stk_lscro_budget (pl := lsmpl) (F := fun k => (pkShimSpecPlaced vtSym A lim k).keepsFs)
    (P := fun (x, st) s =>
      ⌜s.readReg64 .x0 = x.self ∧ s.readReg32 .x1 = x.id ∧
        FitsEnv M lim st (BoxAllocEnv 16)⌝ ∗ A.pool lim st s)
    (Q := fun (x, st) s0 sf =>
      ⌜sf.fs = s0.fs⌝ ∗
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
      dsimp only [Spec.keepsFs, pkShimSpecPlaced, withLsCodeRoLoaded]
      sep_ac_rfl)
    (by
      intro ⟨x, st⟩ s0 sf k
      simp only [Spec.keepsFs, pkShimSpecPlaced, withLsCodeRoLoaded,
        sepExists_sepConj_left, sepExists_sepConj_right]
      exact sepExists_congr fun _ => by sep_ac_rfl)

/-- Block `608` (`pkGetShim`) preserves `fs` under `AllocContractsFsPlaced`. -/
theorem pkGetShim_keepsFs_placed_fixed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFs : AllocContractsFsPlaced A lim H) :
    subroutine_ok (lsProg_608 H) (lsmpl.base 608)
      (pkShimSpecPlaced pkGetFutVtSym A lim pkShimStackPlaced).keepsFs := by
  unfold pkShimSpecPlaced Spec.keepsFs withLsCodeRoLoaded
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
  have halloc := allocNoOom_lscro_of_cli
    (callerProg := (blkPC_608).rebase (blkPl_608).base H) (toAllocContractsX hFs)
  dsimp only [withLsCodeRoLoaded, rustAllocNoOomSpecWithStack,
    rustCliAllocNoOomSpecWithStack] at halloc
  apply sepWP_seq_lscro (mid := lsρ lsRustNoAllocShimSymCli) hcrl0
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSymCli)
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by wp_norm_lhs)
  intro hcrl1
  wp_call_lscro
    (shim_keepsFs_lscro_of_fs (callerProg := (blkPC_608).rebase (blkPl_608).base H) hFs
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
  have htr_alloc : sf_1.trace = sf.trace := hacp.2.1
  have htr_s0 : sf_1.trace = s0.trace := hacp.2.1.trans (by assumption)
  have hne0 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq0 : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hne0
  simp only [memRegion_16_box_placed, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun b0 => SepWP.exists_elim fun u1 =>
    SepWP.exists_elim fun u0 => ?_
  wp_steps_sync_pool (s0.readReg64 Reg.lr)
  wp_done

theorem pkGetShim_keepsFs_placed_ok_of_deps [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {stk : Nat}
    (hFs : AllocContractsFsPlaced A lim H)
    (hstk : 0x20 + extHookStack ≤ stk) :
    subroutine_ok (lsProg_608 H) (lsmpl.base 608)
      (pkShimSpecPlaced pkGetFutVtSym A lim stk).keepsFs :=
  pkShim_lift_stk_keepsFs_placed (pkGetShim_keepsFs_placed_fixed_ok hFs) hstk

/-- Block `610` (`pkRemoveShim`) preserves `fs` under `AllocContractsFsPlaced`. -/
theorem pkRemoveShim_keepsFs_placed_fixed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFs : AllocContractsFsPlaced A lim H) :
    subroutine_ok (lsProg_610 H) (lsmpl.base 610)
      (pkShimSpecPlaced pkRemoveFutVtSym A lim pkShimStackPlaced).keepsFs := by
  unfold pkShimSpecPlaced Spec.keepsFs withLsCodeRoLoaded
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
  have halloc := allocNoOom_lscro_of_cli
    (callerProg := (blkPC_610).rebase (blkPl_610).base H) (toAllocContractsX hFs)
  dsimp only [withLsCodeRoLoaded, rustAllocNoOomSpecWithStack,
    rustCliAllocNoOomSpecWithStack] at halloc
  apply sepWP_seq_lscro (mid := lsρ lsRustNoAllocShimSymCli) hcrl0
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSymCli)
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by wp_norm_lhs)
  intro hcrl1
  wp_call_lscro
    (shim_keepsFs_lscro_of_fs (callerProg := (blkPC_610).rebase (blkPl_610).base H) hFs
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
  have htr_alloc : sf_1.trace = sf.trace := hacp.2.1
  have htr_s0 : sf_1.trace = s0.trace := hacp.2.1.trans (by assumption)
  have hne0 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq0 : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hne0
  simp only [memRegion_16_box_placed, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun b0 => SepWP.exists_elim fun u1 =>
    SepWP.exists_elim fun u0 => ?_
  wp_steps_sync_pool (s0.readReg64 Reg.lr)
  wp_done

theorem pkRemoveShim_keepsFs_placed_ok_of_deps [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {stk : Nat}
    (hFs : AllocContractsFsPlaced A lim H)
    (hstk : 0x20 + extHookStack ≤ stk) :
    subroutine_ok (lsProg_610 H) (lsmpl.base 610)
      (pkShimSpecPlaced pkRemoveFutVtSym A lim stk).keepsFs :=
  pkShim_lift_stk_keepsFs_placed (pkRemoveShim_keepsFs_placed_fixed_ok hFs) hstk

end Shims

theorem cliPkGetShim_fds_rocl_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop} {pid : BitVec 32}
    {s1 s2 s3 s4 : Nat}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hFs : AllocContractsFsPlaced A lim H)
    (hs1 : 0x20 + extHookStack ≤ s1) (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg
      (0#64 + (cliPreKeyStoreSpecPlaced A.repAlloc rd F0 pathOk pid s1 s2 s3 s4).getShimOff)
      (withLsRoCl lsmpl
        (kitPreKeyGetShimSpec M A lim
          (cliPreKeyStoreSpecPlaced A.repAlloc rd F0 pathOk pid s1 s2 s3 s4) true)) := by
  have h608 := pkGetShim_keepsFs_placed_ok_of_deps hFs hs1
  have h608_kit : subroutine_ok (lsProg_608 H) (lsmpl.base 608)
      (withLsCodeRoLoaded lsmpl
        (kitPreKeyGetShimSpec M A lim
          (cliPreKeyStoreSpecPlaced A.repAlloc rd F0 pathOk pid s1 s2 s3 s4) true)) := by
    refine subroutine_ok_outcome_intro fun ⟨⟨self, id⟩, st⟩ R s0 hpc hrun hpre hsp => ?_
    obtain ⟨hcrl, hpre0⟩ := extract_withLsCodeRoLoaded hpre
    dsimp only [kitPreKeyGetShimSpec, cliPreKeyStoreSpecPlaced, cliPreKeyStoreSpec] at hpre0
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre0
    rcases hpre0 with ⟨⟨_hb0, hx0, hx1, hfit, hfds0⟩, hrest⟩
    have hpre' :
        s0.mem ⊨ ((pkShimSpecPlaced pkGetFutVtSym A lim s1).keepsFs).pre (⟨self, id⟩, st) s0 ∗ R := by
      dsimp only [Spec.keepsFs]
      refine satisfies_lscro_pre hcrl ?_
      dsimp only [pkShimSpecPlaced, withLsCodeRoLoaded]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hx0, hx1, hfit⟩, by simpa only [sepConj_assoc] using hrest⟩
    refine h608.mono_outcome (⟨self, id⟩, st) R s0 hpc hrun hpre' hsp ?_
    rintro sf (⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩)
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [Spec.keepsFs, pkShimSpecPlaced, withLsCodeRoLoaded, kitPreKeyGetShimSpec,
        cliPreKeyStoreSpecPlaced, cliPreKeyStoreSpec] at hq ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hq
      rcases hq with ⟨hfs_eq, hq⟩
      simp only [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      obtain ⟨evs, hq⟩ := hq
      refine ⟨evs, ?_⟩
      simp only [BitVec.zero_add]
      rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
      rcases hq with ⟨⟨hx1f, hx0f, hal, htr, hbox⟩, hsp_post⟩
      refine ⟨⟨hx1f, hx0f, hal, htr, hbox, hfs_eq ▸ hfds0⟩, ?_⟩
      simpa only [sepConj_assoc] using hsp_post
    · dsimp only [Spec.keepsFs, pkShimSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
    · dsimp only [Spec.keepsFs, pkShimSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
    · dsimp only [Spec.keepsFs, pkShimSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
  change subroutine_ok callerProg (0#64 + lsmpl.base 608) _
  rw [BitVec.zero_add]
  exact ls_subroutine_ok_rocl_of_block (callerProg := callerProg) (j := 608)
    h608_kit hblk (by decide) (by decide)

theorem cliPkRemoveShim_fds_rocl_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop} {pid : BitVec 32}
    {s1 s2 s3 s4 : Nat}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hFs : AllocContractsFsPlaced A lim H)
    (hs3 : 0x20 + extHookStack ≤ s3) (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg
      (0#64 + (cliPreKeyStoreSpecPlaced A.repAlloc rd F0 pathOk pid s1 s2 s3 s4).removeShimOff)
      (withLsRoCl lsmpl
        (kitPreKeyRemoveShimSpec M A lim
          (cliPreKeyStoreSpecPlaced A.repAlloc rd F0 pathOk pid s1 s2 s3 s4) true)) := by
  have h610 := pkRemoveShim_keepsFs_placed_ok_of_deps hFs hs3
  have h610_kit : subroutine_ok (lsProg_610 H) (lsmpl.base 610)
      (withLsCodeRoLoaded lsmpl
        (kitPreKeyRemoveShimSpec M A lim
          (cliPreKeyStoreSpecPlaced A.repAlloc rd F0 pathOk pid s1 s2 s3 s4) true)) := by
    refine subroutine_ok_outcome_intro fun ⟨⟨self, id⟩, st⟩ R s0 hpc hrun hpre hsp => ?_
    obtain ⟨hcrl, hpre0⟩ := extract_withLsCodeRoLoaded hpre
    dsimp only [kitPreKeyRemoveShimSpec, cliPreKeyStoreSpecPlaced, cliPreKeyStoreSpec] at hpre0
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre0
    rcases hpre0 with ⟨⟨_hb0, hx0, hx1, hfit, hfds0⟩, hrest⟩
    have hpre' :
        s0.mem ⊨
          ((pkShimSpecPlaced pkRemoveFutVtSym A lim s3).keepsFs).pre (⟨self, id⟩, st) s0 ∗ R := by
      dsimp only [Spec.keepsFs]
      refine satisfies_lscro_pre hcrl ?_
      dsimp only [pkShimSpecPlaced, withLsCodeRoLoaded]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hx0, hx1, hfit⟩, by simpa only [sepConj_assoc] using hrest⟩
    refine h610.mono_outcome (⟨self, id⟩, st) R s0 hpc hrun hpre' hsp ?_
    rintro sf (⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩)
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [Spec.keepsFs, pkShimSpecPlaced, withLsCodeRoLoaded, kitPreKeyRemoveShimSpec,
        cliPreKeyStoreSpecPlaced, cliPreKeyStoreSpec] at hq ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hq
      rcases hq with ⟨hfs_eq, hq⟩
      simp only [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      obtain ⟨evs, hq⟩ := hq
      refine ⟨evs, ?_⟩
      simp only [BitVec.zero_add]
      rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
      rcases hq with ⟨⟨hx1f, hx0f, hal, htr, hbox⟩, hsp_post⟩
      refine ⟨⟨hx1f, hx0f, hal, htr, hbox, hfs_eq ▸ hfds0⟩, ?_⟩
      simpa only [sepConj_assoc] using hsp_post
    · dsimp only [Spec.keepsFs, pkShimSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
    · dsimp only [Spec.keepsFs, pkShimSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
    · dsimp only [Spec.keepsFs, pkShimSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
  change subroutine_ok callerProg (0#64 + lsmpl.base 610) _
  rw [BitVec.zero_add]
  exact ls_subroutine_ok_rocl_of_block (callerProg := callerProg) (j := 610)
    h610_kit hblk (by decide) (by decide)

/-! ## Poll lifting and `PreKeyStoreKitPlacedOkFds` assembly -/

theorem cliPkGetPoll_fds_rocl_placed_ok_of_poll [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop} {pid : BitVec 32}
    {s1 s2 s3 s4 : Nat}
    {GetPollEnv : FsFiles → PkPollGhost → List AllocEvent → Prop}
    {kitEnv : PreKeyStoreBudgetEnv (cliPreKeyStoreSpecPlaced A.repAlloc rd F0 pathOk pid s1 s2 s3 s4)}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hGetEnv : ∀ fut out self st0 evs,
      GetPollEnv F0 ⟨fut, out, self, pid, st0⟩ evs → kitEnv.getPollEnv st0 pid evs)
    (h573 : subroutine_ok (lsProg_573 H) (lsmpl.base 573)
      (withFdsGe3Closed (pkGetPollSpecPlaced rd pathOk A lim GetPollEnv s2)))
    (hCallerBlk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg
      (0#64 + (cliPreKeyStoreSpecPlaced A.repAlloc rd F0 pathOk pid s1 s2 s3 s4).getPollOff)
      (withLsRoCl lsmpl
        (kitPreKeyGetPollSpecE M A lim
          (cliPreKeyStoreSpecPlaced A.repAlloc rd F0 pathOk pid s1 s2 s3 s4) kitEnv true)) := by
  let pkKit := cliPreKeyStoreSpecPlaced A.repAlloc rd F0 pathOk pid s1 s2 s3 s4
  have h573_kit : subroutine_ok (lsProg_573 H) (lsmpl.base 573)
      (withLsCodeRoLoaded lsmpl (kitPreKeyGetPollSpecE M A lim pkKit kitEnv true)) := by
    refine subroutine_ok.of_codeLoaded
      fun ⟨⟨fut, out, self, id⟩, st0, st⟩ R s0 hpc hrun hpre hsp _ => ?_
    change DirGhost at st0
    obtain ⟨hcrl, hpre1⟩ := extract_withLsCodeRoLoaded hpre
    have hpre2 : s0.mem ⊨ ⌜s0.fs.files = F0 ∧ FdsGe3Closed s0.fs⌝ ∗
        ((kitPreKeyGetPollSpec M A lim pkKit kitEnv true).pre (⟨fut, out, self, id⟩, st0, st) s0 ∗
          R) := by
      change s0.mem ⊨ (⌜s0.fs.files = F0 ∧ FdsGe3Closed s0.fs⌝ ∗
        (kitPreKeyGetPollSpec M A lim pkKit kitEnv true).pre (⟨fut, out, self, id⟩, st0, st) s0) ∗
        R at hpre1
      simpa only [sepConj_assoc] using hpre1
    rw [satisfies_pure_sepConj] at hpre2
    obtain ⟨⟨hfiles, hfds0⟩, hpre3⟩ := hpre2
    change s0.mem ⊨
      (⌜(0#64 &&& 0xfff#64) = 0#64 ∧ s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
          id = pid ∧ FitsEnv M lim st (kitEnv.getPollEnv st0 id)⌝ ∗
        pkBoxAt fut self id 0#8 ∗
        (⌜CliPkInv rd F0 pathOk pid st0⌝ ∗ dirAt A.repAlloc self st0) ∗
        memRegion out 56 ∗ A.pool lim st s0 ∗ stackAt s0.sp s2) ∗ R at hpre3
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre3
    obtain ⟨⟨_, hx0, hx8, hxid, hfit_kit⟩, hpre4⟩ := hpre3
    subst hxid
    have hpre5 : s0.mem ⊨ ⌜CliPkInv rd F0 pathOk id st0⌝ ∗
        (pkBoxAt fut self id 0#8 ∗ dirAt A.repAlloc self st0 ∗ memRegion out 56 ∗
          A.pool lim st s0 ∗ stackAt s0.sp s2 ∗ R) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre4
    rw [satisfies_pure_sepConj] at hpre5
    obtain ⟨hinv, hspatial⟩ := hpre5
    let xg : PkPollGhost := ⟨fut, out, self, id, st0⟩
    have hfit_hop : FitsEnv M lim st (GetPollEnv s0.fs.files xg) := fun evs hm => by
      rw [hfiles] at hm
      exact hfit_kit evs (hGetEnv fut out self st0 evs hm)
    have hpre_hop : s0.mem ⊨
        (withFdsGe3Closed (pkGetPollSpecPlaced rd pathOk A lim GetPollEnv s2)).pre (xg, st) s0 ∗
          R := by
      dsimp only [withFdsGe3Closed, pkGetPollSpecPlaced, pkGetPollSpecOfPlaced, withLsCodeRoLoaded]
      have h1 : s0.mem ⊨
          ⌜FdsGe3Closed s0.fs⌝ ∗
          (⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
          (⌜s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
            PkNameOk pathOk st0 id ∧ PkSizeOk rd s0.fs.files st0 id ∧
            FitsEnv M lim st (GetPollEnv s0.fs.files xg)⌝ ∗
          (pkBoxAt fut self id 0#8 ∗ dirAt A.repAlloc self st0 ∗ memRegion out 56 ∗
            A.pool lim st s0 ∗ stackAt s0.sp s2 ∗ R))) := by
        rw [satisfies_pure_sepConj]; refine ⟨hfds0, ?_⟩
        rw [satisfies_pure_sepConj]; refine ⟨hcrl, ?_⟩
        rw [satisfies_pure_sepConj]
        exact ⟨⟨hx0, hx8, hinv.nameOk, hfiles ▸ hinv.sizeOk, hfit_hop⟩, hspatial⟩
      exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) h1
    refine h573.mono_outcome (xg, st) R s0 hpc hrun hpre_hop hsp fun sf hout => ?_
    rcases hout with ⟨hret, hcc, hpost0⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [withFdsGe3Closed] at hpost0
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpost0
      obtain ⟨hfds_sf, hpost⟩ := hpost0
      refine Satisfies.mono (sepConj_mono_left ?_) hpost
      show (pkGetPollSpecPlaced rd pathOk A lim GetPollEnv s2).post (xg, st) s0 sf ⊢
        (kitPreKeyGetPollSpec M A lim pkKit kitEnv true).post (⟨fut, out, self, id⟩, st0, st) s0 sf
      dsimp only [pkGetPollSpecPlaced, pkGetPollSpecOfPlaced, withLsCodeRoLoaded,
        kitPreKeyGetPollSpec, pkKit, cliPreKeyStoreSpecPlaced, cliPreKeyStoreSpec,
        cliPkStoreAt, xg]
      refine Entails.sepExists_elim fun evs => ?_
      rw [sepExists_sepConj_left]
      refine Entails.sepExists_elim fun pa => ?_
      rw [sepConj_assoc]
      refine Entails.pure_left fun ⟨hpa, htr, hmenv⟩ => ?_
      rw [hfiles] at hpa hmenv
      subst hpa
      have hkenv : kitEnv.getPollEnv st0 id evs := hGetEnv fut out self st0 evs hmenv
      have hent0 := pkGetAnsAt_entails_pollOut_placed A.repAlloc rd F0 pathOk id
        s1 s2 s3 s4 st0 id out
      dsimp only at hent0
      refine Entails.trans (sepConj_mono_left hent0) ?_
      rw [sepExists_sepConj_left]
      refine Entails.sepExists_elim fun ans => ?_
      rw [sepConj_assoc]
      refine Entails.pure_left fun hrel => ?_
      refine Entails.sepExists_right ans (Entails.sepExists_right evs ?_)
      refine Entails.pure_right ⟨hrel, by rw [List.append_nil]; exact htr, hkenv, hfds_sf⟩ ?_
      exact Entails.trans (Entails.pure_right hinv (Entails.refl _))
        (Entails.of_eq (by sep_ac_rfl))
    · dsimp only [withFdsGe3Closed, pkGetPollSpecPlaced, pkGetPollSpecOfPlaced,
        withLsCodeRoLoaded] at hpan
      exact (not_satisfies_false_sepConj hpan).elim
    · dsimp only [withFdsGe3Closed, pkGetPollSpecPlaced, pkGetPollSpecOfPlaced,
        withLsCodeRoLoaded] at hex
      exact (not_satisfies_false_sepConj hex).elim
    · dsimp only [withFdsGe3Closed, pkGetPollSpecPlaced, pkGetPollSpecOfPlaced,
        withLsCodeRoLoaded] at hoom
      exact (not_satisfies_false_sepConj hoom).elim
  change subroutine_ok callerProg (0#64 + lsmpl.base 573) _
  rw [BitVec.zero_add]
  exact ls_subroutine_ok_rocl_of_block (callerProg := callerProg) (j := 573)
    h573_kit hCallerBlk (by decide) (by decide)

theorem cliPkRemovePoll_fds_rocl_placed_ok_of_poll [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop} {pid : BitVec 32}
    {s1 s2 s3 s4 : Nat}
    {RemPollEnv : FsFiles → PkPollGhost → List AllocEvent → Prop}
    {kitEnv : PreKeyStoreBudgetEnv (cliPreKeyStoreSpecPlaced A.repAlloc rd F0 pathOk pid s1 s2 s3 s4)}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hRemEnv : ∀ fut out self st0 evs,
      RemPollEnv F0 ⟨fut, out, self, pid, st0⟩ evs → kitEnv.removePollEnv st0 pid evs)
    (h575 : subroutine_ok (lsProg_575 H) (lsmpl.base 575)
      (withFdsGe3Closed (pkRemovePollSpecPlaced rd pathOk A lim RemPollEnv s4)))
    (hCallerBlk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg
      (0#64 + (cliPreKeyStoreSpecPlaced A.repAlloc rd F0 pathOk pid s1 s2 s3 s4).removePollOff)
      (withLsRoCl lsmpl
        (kitPreKeyRemovePollSpecE M A lim
          (cliPreKeyStoreSpecPlaced A.repAlloc rd F0 pathOk pid s1 s2 s3 s4) kitEnv true)) := by
  let pkKit := cliPreKeyStoreSpecPlaced A.repAlloc rd F0 pathOk pid s1 s2 s3 s4
  have h575_kit : subroutine_ok (lsProg_575 H) (lsmpl.base 575)
      (withLsCodeRoLoaded lsmpl (kitPreKeyRemovePollSpecE M A lim pkKit kitEnv true)) := by
    refine subroutine_ok.of_codeLoaded
      fun ⟨⟨fut, out, self, id⟩, st0, st⟩ R s0 hpc hrun hpre hsp _ => ?_
    change DirGhost at st0
    obtain ⟨hcrl, hpre1⟩ := extract_withLsCodeRoLoaded hpre
    have hpre2 : s0.mem ⊨ ⌜s0.fs.files = F0 ∧ FdsGe3Closed s0.fs⌝ ∗
        ((kitPreKeyRemovePollSpec M A lim pkKit kitEnv true).pre (⟨fut, out, self, id⟩, st0, st) s0 ∗
          R) := by
      change s0.mem ⊨ (⌜s0.fs.files = F0 ∧ FdsGe3Closed s0.fs⌝ ∗
        (kitPreKeyRemovePollSpec M A lim pkKit kitEnv true).pre (⟨fut, out, self, id⟩, st0, st) s0) ∗
        R at hpre1
      simpa only [sepConj_assoc] using hpre1
    rw [satisfies_pure_sepConj] at hpre2
    obtain ⟨⟨hfiles, hfds0⟩, hpre3⟩ := hpre2
    change s0.mem ⊨
      (⌜(0#64 &&& 0xfff#64) = 0#64 ∧ s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
          id = pid ∧ FitsEnv M lim st (kitEnv.removePollEnv st0 id)⌝ ∗
        pkBoxAt fut self id 0#8 ∗
        (⌜CliPkInv rd F0 pathOk pid st0⌝ ∗ dirAt A.repAlloc self st0) ∗
        memRegion out 48 ∗ A.pool lim st s0 ∗ stackAt s0.sp s4) ∗ R at hpre3
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre3
    obtain ⟨⟨_, hx0, hx8, hxid, hfit_kit⟩, hpre4⟩ := hpre3
    subst hxid
    have hpre5 : s0.mem ⊨ ⌜CliPkInv rd F0 pathOk id st0⌝ ∗
        (pkBoxAt fut self id 0#8 ∗ dirAt A.repAlloc self st0 ∗ memRegion out 48 ∗
          A.pool lim st s0 ∗ stackAt s0.sp s4 ∗ R) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre4
    rw [satisfies_pure_sepConj] at hpre5
    obtain ⟨hinv, hspatial⟩ := hpre5
    let xg : PkPollGhost := ⟨fut, out, self, id, st0⟩
    have hfit_hop : FitsEnv M lim st (RemPollEnv s0.fs.files xg) := fun evs hm => by
      rw [hfiles] at hm
      exact hfit_kit evs (hRemEnv fut out self st0 evs hm)
    have hpre_hop : s0.mem ⊨
        (withFdsGe3Closed (pkRemovePollSpecPlaced rd pathOk A lim RemPollEnv s4)).pre (xg, st) s0 ∗
          R := by
      dsimp only [withFdsGe3Closed, pkRemovePollSpecPlaced, withLsCodeRoLoaded]
      have h1 : s0.mem ⊨
          ⌜FdsGe3Closed s0.fs⌝ ∗
          (⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
          (⌜s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
            PkNameOk pathOk st0 id ∧ st0.changed.length < 2 ^ 32 ∧
            FitsEnv M lim st (RemPollEnv s0.fs.files xg)⌝ ∗
          (pkBoxAt fut self id 0#8 ∗ dirAt A.repAlloc self st0 ∗ memRegion out 48 ∗
            A.pool lim st s0 ∗ stackAt s0.sp s4 ∗ R))) := by
        rw [satisfies_pure_sepConj]; refine ⟨hfds0, ?_⟩
        rw [satisfies_pure_sepConj]; refine ⟨hcrl, ?_⟩
        rw [satisfies_pure_sepConj]
        exact ⟨⟨hx0, hx8, hinv.nameOk, hinv.oneLt.1, hfit_hop⟩, hspatial⟩
      exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) h1
    refine h575.mono_outcome (xg, st) R s0 hpc hrun hpre_hop hsp fun sf hout => ?_
    rcases hout with ⟨hret, hcc, hpost0⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [withFdsGe3Closed] at hpost0
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpost0
      obtain ⟨hfds_sf, hpost⟩ := hpost0
      refine Satisfies.mono (sepConj_mono_left ?_) hpost
      show (pkRemovePollSpecPlaced rd pathOk A lim RemPollEnv s4).post (xg, st) s0 sf ⊢
        (kitPreKeyRemovePollSpec M A lim pkKit kitEnv true).post (⟨fut, out, self, id⟩, st0, st)
          s0 sf
      dsimp only [pkRemovePollSpecPlaced, withLsCodeRoLoaded, kitPreKeyRemovePollSpec,
        pkKit, cliPreKeyStoreSpecPlaced, cliPreKeyStoreSpec, cliPkStoreAt, xg]
      refine Entails.sepExists_elim fun evs => ?_
      rw [sepExists_sepConj_left]
      refine Entails.sepExists_elim fun res => ?_
      rw [sepConj_assoc]
      refine Entails.pure_left fun ⟨hres, htr, hmenv⟩ => ?_
      rw [hfiles] at hres hmenv
      subst hres
      have hkenv : kitEnv.removePollEnv st0 id evs := hRemEnv fut out self st0 evs hmenv
      set m := pkRemoveOf st0 (keyName id) (st0.get rd F0 (keyName id))
      have hent0 := pkRemoveOutAt_entails_pollOut_placed A.repAlloc rd F0 pathOk id
        s1 s2 s3 s4 st0 id out
      dsimp only at hent0
      refine Entails.trans (Entails.of_eq (show _ = pkRemoveOutAt A.repAlloc out m.1 ∗
        (dirAt A.repAlloc self m.2 ∗ pkBoxAt fut self id 1#8 ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp s4) by sep_ac_rfl)) ?_
      refine Entails.trans (sepConj_mono_left hent0) ?_
      rw [sepExists_sepConj_left]
      refine Entails.sepExists_elim fun ans => ?_
      rw [sepConj_assoc]
      refine Entails.pure_left fun ⟨hrel, heq2⟩ => ?_
      rw [heq2]
      refine Entails.sepExists_right ans (Entails.sepExists_right evs ?_)
      refine Entails.pure_right ⟨hrel, by rw [List.append_nil]; exact htr, hkenv, hfds_sf⟩ ?_
      exact Entails.trans (Entails.pure_right hinv.removePreKey (Entails.refl _))
        (Entails.of_eq (by sep_ac_rfl))
    · dsimp only [withFdsGe3Closed, pkRemovePollSpecPlaced, withLsCodeRoLoaded] at hpan
      exact (not_satisfies_false_sepConj hpan).elim
    · dsimp only [withFdsGe3Closed, pkRemovePollSpecPlaced, withLsCodeRoLoaded] at hex
      exact (not_satisfies_false_sepConj hex).elim
    · dsimp only [withFdsGe3Closed, pkRemovePollSpecPlaced, withLsCodeRoLoaded] at hoom
      exact (not_satisfies_false_sepConj hoom).elim
  change subroutine_ok callerProg (0#64 + lsmpl.base 575) _
  rw [BitVec.zero_add]
  exact ls_subroutine_ok_rocl_of_block (callerProg := callerProg) (j := 575)
    h575_kit hCallerBlk (by decide) (by decide)

/-- Assemble `PreKeyStoreKitPlacedOkFds` for `cliPreKeyStoreSpecPlaced` from
`AllocContractsFsPlaced` and the Block `573`/`575` poll contracts. -/
theorem cliPkKitPlacedOkFds_of_polls [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop} {pid : BitVec 32}
    {s1 s2 s3 s4 : Nat}
    {GetPollEnv RemPollEnv : FsFiles → PkPollGhost → List AllocEvent → Prop}
    {kitEnv : PreKeyStoreBudgetEnv (cliPreKeyStoreSpecPlaced A.repAlloc rd F0 pathOk pid s1 s2 s3 s4)}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hFs : AllocContractsFsPlaced A lim H)
    (hGetEnv : ∀ fut out self st0 evs,
      GetPollEnv F0 ⟨fut, out, self, pid, st0⟩ evs → kitEnv.getPollEnv st0 pid evs)
    (hRemEnv : ∀ fut out self st0 evs,
      RemPollEnv F0 ⟨fut, out, self, pid, st0⟩ evs → kitEnv.removePollEnv st0 pid evs)
    (h573 : subroutine_ok (lsProg_573 H) (lsmpl.base 573)
      (withFdsGe3Closed (pkGetPollSpecPlaced rd pathOk A lim GetPollEnv s2)))
    (h575 : subroutine_ok (lsProg_575 H) (lsmpl.base 575)
      (withFdsGe3Closed (pkRemovePollSpecPlaced rd pathOk A lim RemPollEnv s4)))
    (hs1 : 0x20 + extHookStack ≤ s1) (hs3 : 0x20 + extHookStack ≤ s3) :
    PreKeyStoreKitPlacedOkFds A lim
      (cliPreKeyStoreSpecPlaced A.repAlloc rd F0 pathOk pid s1 s2 s3 s4)
      kitEnv H where
  getShim := fun hblk => cliPkGetShim_fds_rocl_placed_ok hFs hs1 hblk
  getPoll := fun hblk => cliPkGetPoll_fds_rocl_placed_ok_of_poll hGetEnv h573 hblk
  getFutDrop := fun hblk => by
    change subroutine_ok _ (0#64 + lsDropOffPlaced) _
    rw [lsDropOffPlaced_eq hDropNz]
    exact cliIdFutDrop_fds_rocl_placed_ok hblk
  removeShim := fun hblk => cliPkRemoveShim_fds_rocl_placed_ok hFs hs3 hblk
  removePoll := fun hblk => cliPkRemovePoll_fds_rocl_placed_ok_of_poll hRemEnv h575 hblk
  removeFutDrop := fun hblk => by
    change subroutine_ok _ (0#64 + lsDropOffPlaced) _
    rw [lsDropOffPlaced_eq hDropNz]
    exact cliIdFutDrop_fds_rocl_placed_ok hblk

/-! ## `FsAtFds` and `writeFileHook` preservation -/

theorem fsAt_cliPreKeyKit_of_fdsGe3Closed [LibsignalPlacement] {A : RustAlloc}
    {envOk : FsFiles → Prop} {rd : ReadRule} {F0 : FsFiles}
    {pathOk : List (BitVec 8) → Prop} {pid : BitVec 32}
    {s1 s2 s3 s4 : Nat} {P : Program} {s : State}
    (hP : TraceFsSound P) (henv : envOk F0) (hfiles : s.fs.files = F0) (hfds : FdsGe3Closed s.fs) :
    FsAtFds envOk
      (cliPreKeyStoreSpecPlaced A rd F0 pathOk pid s1 s2 s3 s4).fdsOk
      (cliPreKeyStoreSpecPlaced A rd F0 pathOk pid s1 s2 s3 s4).Quiet P s :=
  .inr ⟨cliPreKeyStoreSpecPlaced_quiet rd F0 pathOk pid s1 s2 s3 s4,
    hP, hfiles.symm ▸ henv, hfds⟩

theorem cliPreKeyStoreSpecPlaced_writeFileHook [LibsignalPlacement] {A : RustAlloc}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop} {pid : BitVec 32}
    {s1 s2 s3 s4 : Nat} {s : State}
    (hfds : (cliPreKeyStoreSpecPlaced A rd F0 pathOk pid s1 s2 s3 s4).fdsOk s.fs) :
    (cliPreKeyStoreSpecPlaced A rd F0 pathOk pid s1 s2 s3 s4).fdsOk (writeFileHook s).fs :=
  fdsGe3Closed_writeFileHook hfds

theorem hookOk_writeFileHook_withFdsGe3Closed_pk {α : Type} {spec : Spec α}
    (hok : HookOk writeFileHook spec) :
    HookOk writeFileHook (withFdsGe3Closed spec) :=
  hookOk_withFdsGe3Closed_writeFileHook hok

end LibsignalBinary.Proofs.SignalSession.Cli.KitInst.PreKeyKitFdsPlacedBudget
