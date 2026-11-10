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
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.KyberMarkFitPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.PreKeySpecsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.KyberKitOkPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkShimsPlacedBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Placed Budgeted `KyberPreKeyStoreSpec` with Closed-FD Invariant

Establishes `KyberPreKeyStoreKitPlacedOkFds` (`fds = true`) on `cliKpkStoreSpecFullPlaced` and
`cliKpkStoreSpecPlaced`, shim `Spec.keepsFs` contracts on Blocks `611` and `613`,
`withFdsGe3Closed` poll lifting on Blocks `576` and `578`, and `writeFileHook` preservation of
`FdsGe3Closed`.
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.KitInst.KyberPreKeyKitFdsPlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSession (PublicKey)
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.RecordCodecs (KyberPreKeyRecord)
open CryptoVerification.LibsignalTripleRatchet (extHookStack withStack)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles KyberMarkPollCall KyberMarkShimCall KyberPreKeyStoreSpec LibsignalCodeRoLoaded
   PreKeyPollCall PreKeyShimCall TraceFsSound extract_withLsCodeRoLoaded kpkGetPollOutAt
   kpkMarkPollOutAt ls_subroutine_ok_rocl_of_block sepWP_seq_lscro unitSpePollOutAt
   withEnvPre withLsCodeRoLoaded withLsRoCl)
open LibsignalBinary.Proofs.PublicApi.StoreKit.FsFds (FsAtFds)
open CryptoVerification.SignalSession
  (lsDropOffPlaced lsDropOffPlaced_eq lsRustAllocSymCli lsRustNoAllocShimSymCli writeFileHook)
open CryptoVerification.SignalSession.Cli
  (KpkBaseKeysOk KpkMarkAns KpkMarkPollGhost KpkMarkShimCall KpkPollGhost KpkSeenOk
   KyberGhost PkAns PkNameOk PkSizeOk ReadRule dirAt keyName kpkAnsAt kpkAnsOf
   kpkGetFutVtSym kpkMarkBoxAt kpkMarkFutVtSym kpkMarkOf kpkMarkOutAt
   pkAnsOf pkBoxAt)
open CryptoVerification.SignalSession.Cli.Placed
  (blkPC_611 blkPC_613 blkPl_611 blkPl_613 lsProg_576 lsProg_578 lsProg_611 lsProg_613)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon
  (ls_transfer_lscro satisfies_lscro_pre)
open CryptoVerification.SignalSession.Cli.Store.PkShims
  (kpkMarkShimStackPlaced pkShimStackPlaced)
open CryptoVerification.SignalSession.Cli.KitInst
  (CliKpkGetSide CliKpkInv CliKpkMarkErr cliKpkGetSide cliKpkMarkErrSpec cliKpkStoreAt
   cliKpkStoreSpec cliKpkStoreSpecPlaced cliKyberPreKeyStoreSpec cliKyberPreKeyStoreSpecPlaced
   kpkAnsAt_entails_pollOut_placed kpkMarkBoxAt_memRegion pkBoxAt_memRegion)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll
  (CliKpkInvFull cliKpkStoreAtFull cliKpkStoreSpecFullPlaced cliKpkStoreSpecFullPlaced_quiet)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents
   RustCliAllocBudget RustLayoutOk rustAllocEvents)
open LibsignalBinary.Heap.IfaceBudgetLemmas (rustCliAllocNoOomSpecWithStack)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (rustAllocNoOomSpecWithStack)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (BoxAllocEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget
  (KyberPreKeyStoreBudgetEnv kitKpkGetPollSpec kitKpkGetPollSpecE kitKpkGetShimSpec
   kitKpkMarkPollSpec kitKpkMarkPollSpecE kitKpkMarkShimSpec)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (KyberPreKeyStoreKitPlacedOkFds)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsFsPlaced kpkGetPollSpecPlaced kpkMarkPollSpecPlaced kpkMarkShimSpecPlaced
   pkShimSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget
  (allocNoOom_lscro_of_cli lift_stk_lscro_budget)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget.AllocContractsFsPlaced
  (toAllocContractsX)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitFdsPilotPlacedBudget
  (cliIdFutDrop_fds_rocl_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.KyberMarkFitPlacedBudget
  (cliKpkMarkOut_entails)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed fdsGe3Closed_writeFileHook hookOk_withFdsGe3Closed_writeFileHook withFdsGe3Closed)

@[simp]
theorem cliKpkStoreSpecPlaced_fdsOk [LibsignalPlacement] (A : RustAlloc)
    (rd : ReadRule) (F0 : FsFiles) (pathOk : List (BitVec 8) → Prop)
    (kid ksid : BitVec 32) (kbk : PublicKey) (G : CliKpkGetSide)
    (s1 s2 s3 s4 : Nat)
    (hGetBox : ∀ box self id st, pkBoxAt box self id st ⊢ memRegion box 16)
    (hMarkBox : ∀ box self baseKeyA id signedId st,
      kpkMarkBoxAt box self baseKeyA id signedId st ⊢ memRegion box 32)
    (fs : FsState) :
    (cliKpkStoreSpecPlaced A rd F0 pathOk kid ksid kbk G s1 s2 s3 s4 hGetBox hMarkBox).fdsOk fs =
      FdsGe3Closed fs :=
  rfl

@[simp]
theorem cliKpkStoreSpecFullPlaced_fdsOk [LibsignalPlacement] (A : RustAlloc)
    (rd : ReadRule) (F0 : FsFiles) (pathOk : List (BitVec 8) → Prop)
    (kid ksid : BitVec 32) (kbk : PublicKey) (s1 s2 s3 s4 : Nat) (fs : FsState) :
    (cliKpkStoreSpecFullPlaced A rd F0 pathOk kid ksid kbk s1 s2 s3 s4).fdsOk fs =
      FdsGe3Closed fs :=
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

private theorem pkShim_lift_stk_keepsFs_placed [LibsignalPlacement] {vtSym : String}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry : BitVec 64} {stk : Nat}
    (hInner : subroutine_ok prog entry (pkShimSpecPlaced vtSym A lim pkShimStackPlaced).keepsFs)
    (hstk : 32 + extHookStack ≤ stk) :
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

/-- Block `611` (`kpkGetShim`) preserves `fs` under `AllocContractsFsPlaced`. -/
theorem kpkGetShim_keepsFs_placed_fixed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFs : AllocContractsFsPlaced A lim H) :
    subroutine_ok (lsProg_611 H) (lsmpl.base 611)
      (pkShimSpecPlaced kpkGetFutVtSym A lim pkShimStackPlaced).keepsFs := by
  unfold Spec.keepsFs pkShimSpecPlaced withLsCodeRoLoaded
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
  have halloc := allocNoOom_lscro_of_cli
    (callerProg := (blkPC_611).rebase (blkPl_611).base H) (toAllocContractsX hFs)
  dsimp only [withLsCodeRoLoaded, rustAllocNoOomSpecWithStack,
    rustCliAllocNoOomSpecWithStack, AllocCallPreserved] at halloc
  apply sepWP_seq_lscro (mid := lsρ lsRustNoAllocShimSymCli) hcrl0
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSymCli)
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by wp_norm_lhs)
  intro hcrl1
  wp_call_lscro
    (shim_keepsFs_lscro_of_fs (callerProg := (blkPC_611).rebase (blkPl_611).base H)
      hFs (stk := extHookStack))
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

theorem kpkGetShim_keepsFs_placed_ok_of_deps [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {stk : Nat}
    (hFs : AllocContractsFsPlaced A lim H)
    (hstk : 32 + extHookStack ≤ stk) :
    subroutine_ok (lsProg_611 H) (lsmpl.base 611)
      (pkShimSpecPlaced kpkGetFutVtSym A lim stk).keepsFs :=
  pkShim_lift_stk_keepsFs_placed (kpkGetShim_keepsFs_placed_fixed_ok hFs) hstk

/-- Block `613` (`kpkMarkShim`) preserves `fs` under `AllocContractsFsPlaced`. -/
theorem kpkMarkShim_keepsFs_placed_fixed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFs : AllocContractsFsPlaced A lim H) :
    subroutine_ok (lsProg_613 H) (lsmpl.base 613)
      (kpkMarkShimSpecPlaced A lim kpkMarkShimStackPlaced).keepsFs := by
  unfold Spec.keepsFs kpkMarkShimSpecPlaced withLsCodeRoLoaded
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
  have halloc := allocNoOom_lscro_of_cli
    (callerProg := (blkPC_613).rebase (blkPl_613).base H) (toAllocContractsX hFs)
  dsimp only [withLsCodeRoLoaded, rustAllocNoOomSpecWithStack,
    rustCliAllocNoOomSpecWithStack, AllocCallPreserved] at halloc
  apply sepWP_seq_lscro (mid := lsρ lsRustNoAllocShimSymCli) hcrl0
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSymCli)
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by wp_norm_lhs)
  intro hcrl1
  wp_call_lscro
    (shim_keepsFs_lscro_of_fs (callerProg := (blkPC_613).rebase (blkPl_613).base H)
      hFs (stk := extHookStack))
    hcrl1 ()
  refine ProofLib.SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  apply sepWP_seq_lscro (mid := lsρ lsRustAllocSymCli) hcrl_sf
  wp_steps_sync_pool (lsρ lsRustAllocSymCli)
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by wp_norm_lhs)
  intro ⟨hcl2, hro2⟩
  wp_call halloc (32, 8, st)
  have hne0 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq0 : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hne0
  simp only [memRegion_32_kpkMarkBox_placed, sepExists_sepConj_left, sepExists_sepConj_right,
    sepConj_assoc]
  refine SepWP.exists_elim fun b0 => SepWP.exists_elim fun u3 =>
    SepWP.exists_elim fun u2 => SepWP.exists_elim fun u1 =>
    SepWP.exists_elim fun u0 => ?_
  wp_steps_sync_pool (s0.readReg64 Reg.lr)
  wp_done

theorem kpkMarkShim_keepsFs_placed_ok_of_deps [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {stk : Nat}
    (hFs : AllocContractsFsPlaced A lim H)
    (hstk : 48 + extHookStack ≤ stk) :
    subroutine_ok (lsProg_613 H) (lsmpl.base 613)
      (kpkMarkShimSpecPlaced A lim stk).keepsFs :=
  lift_stk_lscro_budget (pl := lsmpl) (F := fun k => (kpkMarkShimSpecPlaced A lim k).keepsFs)
    (P := fun (x, st) s =>
      ⌜s.readReg64 .x0 = x.self ∧ s.readReg32 .x1 = x.id ∧ s.readReg32 .x2 = x.signedId ∧
        s.readReg64 .x3 = x.baseKeyA ∧
        FitsEnv M lim st (BoxAllocEnv 32)⌝ ∗ A.pool lim st s)
    (Q := fun (x, st) s0 sf =>
      ⌜sf.fs = s0.fs⌝ ∗
      ∃∗ evs : List AllocEvent,
        ⌜sf.readReg64 .x1 = lsρ kpkMarkFutVtSym ∧ sf.readReg64 .x0 ≠ 0#64 ∧
          (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace ∧
          BoxAllocEnv 32 evs⌝ ∗
          A.live (sf.readReg64 .x0) 32 8 ∗
          kpkMarkBoxAt (sf.readReg64 .x0) x.self x.baseKeyA x.id x.signedId 0#8 ∗
          A.pool lim (M.stepEvents evs st) sf)
    (kpkMarkShim_keepsFs_placed_fixed_ok hFs)
    (by dsimp [kpkMarkShimStackPlaced]; omega)
    (by
      intro ⟨x, st⟩ s k
      dsimp only [Spec.keepsFs, kpkMarkShimSpecPlaced, withLsCodeRoLoaded]
      sep_ac_rfl)
    (by
      intro ⟨x, st⟩ s0 sf k
      simp only [Spec.keepsFs, kpkMarkShimSpecPlaced, withLsCodeRoLoaded,
        sepExists_sepConj_left, sepExists_sepConj_right]
      exact sepExists_congr fun _ => by sep_ac_rfl)

end Shims

theorem cliKpkGetShim_fds_rocl_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop}
    {kid ksid : BitVec 32} {kbk : PublicKey}
    (G : CliKpkGetSide) {s1 s2 s3 s4 : Nat}
    (hGetBox : ∀ box self id st, pkBoxAt box self id st ⊢ memRegion box 16)
    (hMarkBox : ∀ box self baseKeyA id signedId st,
      kpkMarkBoxAt box self baseKeyA id signedId st ⊢ memRegion box 32)
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hFs : AllocContractsFsPlaced A lim H)
    (hs1 : 32 + extHookStack ≤ s1) (hblk : callerBlk < 619 := by decide) :
    let kit :=
      cliKpkStoreSpecPlaced A.repAlloc rd F0 pathOk kid ksid kbk G s1 s2 s3 s4 hGetBox hMarkBox
    subroutine_ok callerProg (0#64 + kit.getShimOff)
      (withLsRoCl lsmpl (kitKpkGetShimSpec M A lim kit true)) := by
  intro kit
  have h611 := kpkGetShim_keepsFs_placed_ok_of_deps hFs hs1
  have h611_kit : subroutine_ok (lsProg_611 H) (lsmpl.base 611)
      (withLsCodeRoLoaded lsmpl (kitKpkGetShimSpec M A lim kit true)) := by
    refine subroutine_ok_outcome_intro fun ⟨⟨self, id⟩, st⟩ R s0 hpc hrun hpre hsp => ?_
    obtain ⟨hcrl, hpre0⟩ := extract_withLsCodeRoLoaded hpre
    dsimp only [kitKpkGetShimSpec, kit, cliKpkStoreSpecPlaced, cliKpkStoreSpec] at hpre0
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre0
    rcases hpre0 with ⟨⟨_hb0, hx0, hx1, hfit, hfds0⟩, hrest⟩
    have hpre' :
        s0.mem ⊨ ((pkShimSpecPlaced kpkGetFutVtSym A lim s1).keepsFs).pre (⟨self, id⟩, st) s0 ∗ R := by
      dsimp only [Spec.keepsFs]
      refine satisfies_lscro_pre hcrl ?_
      dsimp only [pkShimSpecPlaced, withLsCodeRoLoaded]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hx0, hx1, hfit⟩, by simpa only [sepConj_assoc] using hrest⟩
    refine h611.mono_outcome (⟨self, id⟩, st) R s0 hpc hrun hpre' hsp ?_
    rintro sf (⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩)
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [Spec.keepsFs, pkShimSpecPlaced, withLsCodeRoLoaded, kitKpkGetShimSpec,
        kit, cliKpkStoreSpecPlaced, cliKpkStoreSpec] at hq ⊢
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
  change subroutine_ok callerProg (0#64 + lsmpl.base 611) _
  rw [BitVec.zero_add]
  exact ls_subroutine_ok_rocl_of_block (callerProg := callerProg) (j := 611)
    h611_kit hblk (by decide) (by decide)

theorem cliKpkFull_getShim_fds_rocl_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop}
    {kid ksid : BitVec 32} {kbk : PublicKey} {s1 s2 s3 s4 : Nat}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hFs : AllocContractsFsPlaced A lim H)
    (hs1 : 32 + extHookStack ≤ s1) (hblk : callerBlk < 619 := by decide) :
    let kit := cliKpkStoreSpecFullPlaced A.repAlloc rd F0 pathOk kid ksid kbk s1 s2 s3 s4
    subroutine_ok callerProg (0#64 + kit.getShimOff)
      (withLsRoCl lsmpl (kitKpkGetShimSpec M A lim kit true)) :=
  cliKpkGetShim_fds_rocl_placed_ok (rd := rd) (F0 := F0) (pathOk := pathOk)
    (kid := kid) (ksid := ksid) (kbk := kbk)
    (cliKpkGetSide A.repAlloc rd F0 pathOk kid)
    (s1 := s1) (s2 := s2) (s3 := s3) (s4 := s4)
    pkBoxAt_memRegion kpkMarkBoxAt_memRegion hFs hs1 hblk

theorem cliKpkMarkShim_fds_rocl_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop}
    {kid ksid : BitVec 32} {kbk : PublicKey}
    (G : CliKpkGetSide) {s1 s2 s3 s4 : Nat}
    (hGetBox : ∀ box self id st, pkBoxAt box self id st ⊢ memRegion box 16)
    (hMarkBox : ∀ box self baseKeyA id signedId st,
      kpkMarkBoxAt box self baseKeyA id signedId st ⊢ memRegion box 32)
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hFs : AllocContractsFsPlaced A lim H)
    (hs3 : 48 + extHookStack ≤ s3) (hblk : callerBlk < 619 := by decide) :
    let kit :=
      cliKpkStoreSpecPlaced A.repAlloc rd F0 pathOk kid ksid kbk G s1 s2 s3 s4 hGetBox hMarkBox
    subroutine_ok callerProg (0#64 + kit.markShimOff)
      (withLsRoCl lsmpl (kitKpkMarkShimSpec M A lim kit true)) := by
  intro kit
  have h613 := kpkMarkShim_keepsFs_placed_ok_of_deps hFs hs3
  have h613_kit : subroutine_ok (lsProg_613 H) (lsmpl.base 613)
      (withLsCodeRoLoaded lsmpl (kitKpkMarkShimSpec M A lim kit true)) := by
    refine subroutine_ok_outcome_intro
      fun ⟨⟨self, id, signedId, baseKeyA⟩, st⟩ R s0 hpc hrun hpre hsp => ?_
    obtain ⟨hcrl, hpre0⟩ := extract_withLsCodeRoLoaded hpre
    dsimp only [kitKpkMarkShimSpec, kit, cliKpkStoreSpecPlaced, cliKpkStoreSpec] at hpre0
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre0
    rcases hpre0 with ⟨⟨_hb0, hx0, hx1, hx2, hx3, hfit, hfds0⟩, hrest⟩
    have hpre' :
        s0.mem ⊨
          ((kpkMarkShimSpecPlaced A lim s3).keepsFs).pre (⟨self, id, signedId, baseKeyA⟩, st) s0 ∗
            R := by
      dsimp only [Spec.keepsFs]
      refine satisfies_lscro_pre hcrl ?_
      dsimp only [kpkMarkShimSpecPlaced, withLsCodeRoLoaded]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hx0, hx1, hx2, hx3, hfit⟩, by simpa only [sepConj_assoc] using hrest⟩
    refine h613.mono_outcome (⟨self, id, signedId, baseKeyA⟩, st) R s0 hpc hrun hpre' hsp ?_
    rintro sf (⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩)
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [Spec.keepsFs, kpkMarkShimSpecPlaced, withLsCodeRoLoaded, kitKpkMarkShimSpec,
        kit, cliKpkStoreSpecPlaced, cliKpkStoreSpec] at hq ⊢
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
    · dsimp only [Spec.keepsFs, kpkMarkShimSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
    · dsimp only [Spec.keepsFs, kpkMarkShimSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
    · dsimp only [Spec.keepsFs, kpkMarkShimSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
  change subroutine_ok callerProg (0#64 + lsmpl.base 613) _
  rw [BitVec.zero_add]
  exact ls_subroutine_ok_rocl_of_block (callerProg := callerProg) (j := 613)
    h613_kit hblk (by decide) (by decide)

theorem cliKpkFull_markShim_fds_rocl_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop}
    {kid ksid : BitVec 32} {kbk : PublicKey} {s1 s2 s3 s4 : Nat}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hFs : AllocContractsFsPlaced A lim H)
    (hs3 : 48 + extHookStack ≤ s3) (hblk : callerBlk < 619 := by decide) :
    let kit := cliKpkStoreSpecFullPlaced A.repAlloc rd F0 pathOk kid ksid kbk s1 s2 s3 s4
    subroutine_ok callerProg (0#64 + kit.markShimOff)
      (withLsRoCl lsmpl (kitKpkMarkShimSpec M A lim kit true)) :=
  cliKpkMarkShim_fds_rocl_placed_ok (rd := rd) (F0 := F0) (pathOk := pathOk)
    (kid := kid) (ksid := ksid) (kbk := kbk)
    (cliKpkGetSide A.repAlloc rd F0 pathOk kid)
    (s1 := s1) (s2 := s2) (s3 := s3) (s4 := s4)
    pkBoxAt_memRegion kpkMarkBoxAt_memRegion hFs hs3 hblk

/-! ## Poll lifting and `KyberPreKeyStoreKitPlacedOkFds` assembly -/

theorem cliKpkFull_getPoll_fds_rocl_placed_ok_of_poll [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop}
    {kid ksid : BitVec 32} {kbk : PublicKey} {s1 s2 s3 s4 : Nat}
    {GetPollEnv : FsFiles → KpkPollGhost → List AllocEvent → Prop}
    {kitEnv : KyberPreKeyStoreBudgetEnv
      (cliKpkStoreSpecFullPlaced A.repAlloc rd F0 pathOk kid ksid kbk s1 s2 s3 s4)}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hGetEnv : ∀ fut out self st0 evs,
      GetPollEnv F0 ⟨fut, out, self, kid, st0⟩ evs → kitEnv.getPollEnv st0 kid evs)
    (h576 : subroutine_ok (lsProg_576 H) (lsmpl.base 576)
      (withFdsGe3Closed (kpkGetPollSpecPlaced rd pathOk A lim GetPollEnv s2)))
    (hCallerBlk : callerBlk < 619 := by decide) :
    let kit := cliKpkStoreSpecFullPlaced A.repAlloc rd F0 pathOk kid ksid kbk s1 s2 s3 s4
    subroutine_ok callerProg (0#64 + kit.getPollOff)
      (withLsRoCl lsmpl (kitKpkGetPollSpecE M A lim kit kitEnv true)) := by
  intro kit
  have h576_kit : subroutine_ok (lsProg_576 H) (lsmpl.base 576)
      (withLsCodeRoLoaded lsmpl (kitKpkGetPollSpecE M A lim kit kitEnv true)) := by
    refine subroutine_ok.of_codeLoaded
      fun ⟨⟨fut, out, self, id⟩, st0, st⟩ R s0 hpc hrun hpre hsp _ => ?_
    change KyberGhost at st0
    obtain ⟨hcrl, hpre1⟩ := extract_withLsCodeRoLoaded hpre
    have hpre2 : s0.mem ⊨ ⌜s0.fs.files = F0 ∧ FdsGe3Closed s0.fs⌝ ∗
        ((kitKpkGetPollSpec M A lim kit kitEnv true).pre (⟨fut, out, self, id⟩, st0, st) s0 ∗ R) := by
      change s0.mem ⊨ (⌜s0.fs.files = F0 ∧ FdsGe3Closed s0.fs⌝ ∗
        (kitKpkGetPollSpec M A lim kit kitEnv true).pre (⟨fut, out, self, id⟩, st0, st) s0) ∗ R at hpre1
      simpa only [sepConj_assoc] using hpre1
    rw [satisfies_pure_sepConj] at hpre2
    obtain ⟨⟨hfiles, hfds0⟩, hpre3⟩ := hpre2
    change s0.mem ⊨
      (⌜(0#64 &&& 0xfff#64) = 0#64 ∧ s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
          id = kid ∧ FitsEnv M lim st (kitEnv.getPollEnv st0 id)⌝ ∗
        pkBoxAt fut self id 0#8 ∗
        (⌜CliKpkInvFull rd F0 pathOk kid ksid kbk st0⌝ ∗
          (dirAt A.repAlloc self st0.oneTime ∗ dirAt A.repAlloc (self + 40#64) st0.lastResort)) ∗
        memRegion out 88 ∗ A.pool lim st s0 ∗ stackAt s0.sp s2) ∗ R at hpre3
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre3
    obtain ⟨⟨_, hx0, hx8, hxid, hfit_kit⟩, hpre4⟩ := hpre3
    subst hxid
    have hpre5 : s0.mem ⊨ ⌜CliKpkInvFull rd F0 pathOk id ksid kbk st0⌝ ∗
        (pkBoxAt fut self id 0#8 ∗ dirAt A.repAlloc self st0.oneTime ∗
          dirAt A.repAlloc (self + 40#64) st0.lastResort ∗ memRegion out 88 ∗
          A.pool lim st s0 ∗ stackAt s0.sp s2 ∗ R) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre4
    rw [satisfies_pure_sepConj] at hpre5
    obtain ⟨hinv, hspatial⟩ := hpre5
    let xg : KpkPollGhost := ⟨fut, out, self, id, st0⟩
    have hfit_hop : FitsEnv M lim st (GetPollEnv s0.fs.files xg) := fun evs hm => by
      rw [hfiles] at hm
      exact hfit_kit evs (hGetEnv fut out self st0 evs hm)
    have hpre_hop : s0.mem ⊨
        (withFdsGe3Closed (kpkGetPollSpecPlaced rd pathOk A lim GetPollEnv s2)).pre (xg, st) s0 ∗
          R := by
      dsimp only [withFdsGe3Closed, kpkGetPollSpecPlaced, withLsCodeRoLoaded]
      have h1 : s0.mem ⊨
          ⌜FdsGe3Closed s0.fs⌝ ∗
          (⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
          (⌜s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
            PkNameOk pathOk st0.oneTime id ∧ PkNameOk pathOk st0.lastResort id ∧
            PkSizeOk rd s0.fs.files st0.oneTime id ∧ PkSizeOk rd s0.fs.files st0.lastResort id ∧
            FitsEnv M lim st (GetPollEnv s0.fs.files xg)⌝ ∗
          (pkBoxAt fut self id 0#8 ∗ dirAt A.repAlloc self st0.oneTime ∗
            dirAt A.repAlloc (self + 40#64) st0.lastResort ∗ memRegion out 88 ∗
            A.pool lim st s0 ∗ stackAt s0.sp s2 ∗ R))) := by
        rw [satisfies_pure_sepConj]; refine ⟨hfds0, ?_⟩
        rw [satisfies_pure_sepConj]; refine ⟨hcrl, ?_⟩
        rw [satisfies_pure_sepConj]
        exact ⟨⟨hx0, hx8, hinv.markInv.nameOk, hinv.lastNameOk,
          hfiles ▸ hinv.oneSizeOk, hfiles ▸ hinv.lastSizeOk, hfit_hop⟩, hspatial⟩
      exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) h1
    refine h576.mono_outcome (xg, st) R s0 hpc hrun hpre_hop hsp fun sf hout => ?_
    rcases hout with ⟨hret, hcc, hpost0⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [withFdsGe3Closed] at hpost0
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpost0
      obtain ⟨hfds_sf, hpost⟩ := hpost0
      refine Satisfies.mono (sepConj_mono_left ?_) hpost
      show (kpkGetPollSpecPlaced rd pathOk A lim GetPollEnv s2).post (xg, st) s0 sf ⊢
        (kitKpkGetPollSpec M A lim kit kitEnv true).post (⟨fut, out, self, id⟩, st0, st) s0 sf
      dsimp only [kpkGetPollSpecPlaced, withLsCodeRoLoaded, kitKpkGetPollSpec, kit,
        cliKpkStoreSpecFullPlaced,
        CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliKyberPreKeyStoreSpecPlaced,
        cliKyberPreKeyStoreSpecPlaced, cliKyberPreKeyStoreSpec, cliKpkStoreSpec,
        cliKpkStoreAtFull, xg]
      refine Entails.sepExists_elim fun evs => ?_
      rw [sepExists_sepConj_left]
      refine Entails.sepExists_elim fun pa => ?_
      rw [sepConj_assoc]
      refine Entails.pure_left fun ⟨hpa, htr, hmenv⟩ => ?_
      rw [hfiles] at hpa hmenv
      subst hpa
      have hkenv : kitEnv.getPollEnv st0 id evs := hGetEnv fut out self st0 evs hmenv
      have hent0 := kpkAnsAt_entails_pollOut_placed A.repAlloc rd F0 pathOk id ksid kbk
        s1 s2 s3 s4 st0 id out
      dsimp only at hent0
      have hout_eq :
          kpkGetPollOutAt
            (cliKyberPreKeyStoreSpecPlaced A.repAlloc rd F0 pathOk id ksid kbk s1 s2 s3 s4) out =
          kpkGetPollOutAt kit out := by
        funext ans; cases ans <;> rfl
      rw [hout_eq] at hent0
      refine Entails.trans (sepConj_mono_left hent0) ?_
      rw [sepExists_sepConj_left]
      refine Entails.sepExists_elim fun ans => ?_
      rw [sepConj_assoc]
      refine Entails.pure_left fun hrel => ?_
      refine Entails.sepExists_right ans (Entails.sepExists_right evs ?_)
      refine Entails.pure_right ⟨hrel, by rw [List.append_nil]; exact htr, hkenv, hfds_sf⟩ ?_
      exact Entails.trans (Entails.pure_right hinv (Entails.refl _))
        (Entails.of_eq (by sep_ac_rfl))
    · dsimp only [withFdsGe3Closed, kpkGetPollSpecPlaced, withLsCodeRoLoaded] at hpan
      exact (not_satisfies_false_sepConj hpan).elim
    · dsimp only [withFdsGe3Closed, kpkGetPollSpecPlaced, withLsCodeRoLoaded] at hex
      exact (not_satisfies_false_sepConj hex).elim
    · dsimp only [withFdsGe3Closed, kpkGetPollSpecPlaced, withLsCodeRoLoaded] at hoom
      exact (not_satisfies_false_sepConj hoom).elim
  change subroutine_ok callerProg (0#64 + lsmpl.base 576) _
  rw [BitVec.zero_add]
  exact ls_subroutine_ok_rocl_of_block (callerProg := callerProg) (j := 576)
    h576_kit hCallerBlk (by decide) (by decide)

theorem cliKpkStoreSpecPlaced_markPoll_fds_rocl_of_poll [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop}
    {kid ksid : BitVec 32} {kbk : PublicKey}
    (G : CliKpkGetSide) {s1 s2 s3 s4 : Nat}
    (hGetBox : ∀ box self id st, pkBoxAt box self id st ⊢ memRegion box 16)
    (hMarkBox : ∀ box self baseKeyA id signedId st,
      kpkMarkBoxAt box self baseKeyA id signedId st ⊢ memRegion box 32)
    {MarkEnv : FsFiles → KpkMarkPollGhost → List AllocEvent → Prop}
    {kitEnv : KyberPreKeyStoreBudgetEnv
      (cliKpkStoreSpecPlaced A.repAlloc rd F0 pathOk kid ksid kbk G s1 s2 s3 s4 hGetBox hMarkBox)}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hMarkEnv : ∀ fut out self baseKeyA st0 evs,
      MarkEnv F0 ⟨fut, out, self, baseKeyA, kid, ksid, kbk, st0⟩ evs →
        kitEnv.markPollEnv st0 kid ksid kbk evs)
    (h578 : subroutine_ok (lsProg_578 H) (lsmpl.base 578)
      (withFdsGe3Closed (kpkMarkPollSpecPlaced rd pathOk A lim MarkEnv s4)))
    (hCallerBlk : callerBlk < 619 := by decide) :
    let kit :=
      cliKpkStoreSpecPlaced A.repAlloc rd F0 pathOk kid ksid kbk G s1 s2 s3 s4 hGetBox hMarkBox
    subroutine_ok callerProg (0#64 + kit.markPollOff)
      (withLsRoCl lsmpl (kitKpkMarkPollSpecE M A lim kit kitEnv true)) := by
  intro kit
  have h578_kit : subroutine_ok (lsProg_578 H) (lsmpl.base 578)
      (withLsCodeRoLoaded lsmpl (kitKpkMarkPollSpecE M A lim kit kitEnv true)) := by
    refine subroutine_ok.of_codeLoaded
      fun ⟨⟨fut, out, self, baseKeyA, kid', ksid', kbk'⟩, st0, st⟩ R s0 hpc hrun hpre hsp _ => ?_
    change KyberGhost at st0
    obtain ⟨hcrl, hpre1⟩ := extract_withLsCodeRoLoaded hpre
    have hpre2 : s0.mem ⊨ ⌜s0.fs.files = F0 ∧ FdsGe3Closed s0.fs⌝ ∗
        ((kitKpkMarkPollSpec M A lim kit kitEnv true).pre
          (⟨fut, out, self, baseKeyA, kid', ksid', kbk'⟩, st0, st) s0 ∗ R) := by
      change s0.mem ⊨ (⌜s0.fs.files = F0 ∧ FdsGe3Closed s0.fs⌝ ∗
        (kitKpkMarkPollSpec M A lim kit kitEnv true).pre
          (⟨fut, out, self, baseKeyA, kid', ksid', kbk'⟩, st0, st) s0) ∗ R at hpre1
      simpa only [sepConj_assoc] using hpre1
    rw [satisfies_pure_sepConj] at hpre2
    obtain ⟨⟨hfiles, hfds0⟩, hpre3⟩ := hpre2
    change s0.mem ⊨
      (⌜(0#64 &&& 0xfff#64) = 0#64 ∧ s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
          (kid' = kid ∧ ksid' = ksid ∧ kbk' = kbk) ∧
          FitsEnv M lim st (kitEnv.markPollEnv st0 kid' ksid' kbk')⌝ ∗
        kpkMarkBoxAt fut self baseKeyA kid' ksid' 0#8 ∗
        (⌜CliKpkInv rd F0 pathOk kid ksid kbk st0⌝ ∗ dirAt A.repAlloc self st0.oneTime ∗
          dirAt A.repAlloc (self + 40#64) st0.lastResort) ∗
        memRegion out 48 ∗ (baseKeyA ↦ₛ kbk'.bytes.toList) ∗
        A.pool lim st s0 ∗ stackAt s0.sp s4) ∗ R at hpre3
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre3
    obtain ⟨⟨_, hx0, hx8, ⟨hxid, hxsid, hxbk⟩, hfit_kit⟩, hpre4⟩ := hpre3
    rw [hxid, hxsid, hxbk] at hfit_kit hpre4 ⊢
    have hpre5 : s0.mem ⊨ ⌜CliKpkInv rd F0 pathOk kid ksid kbk st0⌝ ∗
        (kpkMarkBoxAt fut self baseKeyA kid ksid 0#8 ∗
          dirAt A.repAlloc self st0.oneTime ∗ dirAt A.repAlloc (self + 40#64) st0.lastResort ∗
          (baseKeyA ↦ₛ kbk.bytes.toList) ∗ memRegion out 48 ∗
          A.pool lim st s0 ∗ stackAt s0.sp s4 ∗ R) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre4
    rw [satisfies_pure_sepConj] at hpre5
    obtain ⟨hinv, hspatial⟩ := hpre5
    let xg : KpkMarkPollGhost := ⟨fut, out, self, baseKeyA, kid, ksid, kbk, st0⟩
    have hfit_hop : FitsEnv M lim st (MarkEnv s0.fs.files xg) := fun evs hm => by
      rw [hfiles] at hm
      exact hfit_kit evs (hMarkEnv fut out self baseKeyA st0 evs hm)
    have hpre_hop : s0.mem ⊨
        (withFdsGe3Closed (kpkMarkPollSpecPlaced rd pathOk A lim MarkEnv s4)).pre (xg, st) s0 ∗
          R := by
      dsimp only [withFdsGe3Closed, kpkMarkPollSpecPlaced, withLsCodeRoLoaded]
      have h1 : s0.mem ⊨
          ⌜FdsGe3Closed s0.fs⌝ ∗
          (⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
          (⌜s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
            PkNameOk pathOk st0.oneTime kid ∧ KpkBaseKeysOk pathOk st0.lastResort kid ∧
            KpkSeenOk rd s0.fs.files st0.lastResort kid ksid kbk ∧
            st0.oneTime.changed.length < 2 ^ 32 ∧ st0.lastResort.changed.length < 2 ^ 32 ∧
            FitsEnv M lim st (MarkEnv s0.fs.files xg)⌝ ∗
          (kpkMarkBoxAt fut self baseKeyA kid ksid 0#8 ∗
            dirAt A.repAlloc self st0.oneTime ∗ dirAt A.repAlloc (self + 40#64) st0.lastResort ∗
            (baseKeyA ↦ₛ kbk.bytes.toList) ∗ memRegion out 48 ∗
            A.pool lim st s0 ∗ stackAt s0.sp s4 ∗ R))) := by
        rw [satisfies_pure_sepConj]; refine ⟨hfds0, ?_⟩
        rw [satisfies_pure_sepConj]; refine ⟨hcrl, ?_⟩
        rw [satisfies_pure_sepConj]
        exact ⟨⟨hx0, hx8, hinv.nameOk, hinv.baseOk, hfiles ▸ hinv.seenOk,
          hinv.oneLt.1, hinv.lastLt.1, hfit_hop⟩, hspatial⟩
      exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) h1
    refine h578.mono_outcome (xg, st) R s0 hpc hrun hpre_hop hsp fun sf hout => ?_
    rcases hout with ⟨hret, hcc, hpost0⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [withFdsGe3Closed] at hpost0
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpost0
      obtain ⟨hfds_sf, hpost⟩ := hpost0
      refine Satisfies.mono (sepConj_mono_left ?_) hpost
      show (kpkMarkPollSpecPlaced rd pathOk A lim MarkEnv s4).post (xg, st) s0 sf ⊢
        (kitKpkMarkPollSpec M A lim kit kitEnv true).post
          (⟨fut, out, self, baseKeyA, kid, ksid, kbk⟩, st0, st) s0 sf
      dsimp only [kpkMarkPollSpecPlaced, withLsCodeRoLoaded, kitKpkMarkPollSpec, kit,
        cliKpkStoreSpecPlaced, cliKpkStoreSpec, cliKpkStoreAt, kpkMarkPollOutAt, xg]
      refine Entails.sepExists_elim fun evs => ?_
      rw [sepExists_sepConj_left]
      refine Entails.sepExists_elim fun res => ?_
      rw [sepConj_assoc]
      refine Entails.pure_left fun ⟨hres, htr, hmenv⟩ => ?_
      rw [hfiles] at hres hmenv
      subst hres
      have hkenv : kitEnv.markPollEnv st0 kid ksid kbk evs :=
        hMarkEnv fut out self baseKeyA st0 evs hmenv
      set m := kpkMarkOf rd F0 st0 kid ksid kbk
      refine Entails.trans
        (Entails.of_eq (show _ =
          kpkMarkOutAt A.repAlloc out m.1 ∗
            (dirAt A.repAlloc self m.2.oneTime ∗ dirAt A.repAlloc (self + 40#64) m.2.lastResort ∗
              kpkMarkBoxAt fut self baseKeyA kid ksid 1#8 ∗
              (baseKeyA ↦ₛ kbk.bytes.toList) ∗ A.pool lim (M.stepEvents evs st) sf ∗
              stackAt s0.sp s4) by sep_ac_rfl)) ?_
      refine Entails.trans (sepConj_mono_left (cliKpkMarkOut_entails A.repAlloc out m.1)) ?_
      rw [sepExists_sepConj_left]
      refine Entails.sepExists_elim fun ans => ?_
      rw [sepConj_assoc]
      refine Entails.pure_left fun hrel => ?_
      refine Entails.sepExists_right ans (Entails.sepExists_right evs ?_)
      refine Entails.pure_right ⟨hrel, by rw [List.append_nil]; exact htr, hkenv, hfds_sf⟩ ?_
      refine Entails.trans ?_
        (Entails.of_eq (show
          ⌜CliKpkInv rd F0 pathOk kid ksid kbk m.2⌝ ∗
            (unitSpePollOutAt (cliKpkMarkErrSpec A.repAlloc) out ans ∗
              (dirAt A.repAlloc self m.2.oneTime ∗ dirAt A.repAlloc (self + 40#64) m.2.lastResort ∗
                kpkMarkBoxAt fut self baseKeyA kid ksid 1#8 ∗
                (baseKeyA ↦ₛ kbk.bytes.toList) ∗ A.pool lim (M.stepEvents evs st) sf ∗
                stackAt s0.sp s4)) = _ by sep_ac_rfl))
      exact Entails.pure_right hinv.mark (Entails.refl _)
    · dsimp only [withFdsGe3Closed, kpkMarkPollSpecPlaced, withLsCodeRoLoaded] at hpan
      exact (not_satisfies_false_sepConj hpan).elim
    · dsimp only [withFdsGe3Closed, kpkMarkPollSpecPlaced, withLsCodeRoLoaded] at hex
      exact (not_satisfies_false_sepConj hex).elim
    · dsimp only [withFdsGe3Closed, kpkMarkPollSpecPlaced, withLsCodeRoLoaded] at hoom
      exact (not_satisfies_false_sepConj hoom).elim
  change subroutine_ok callerProg (0#64 + lsmpl.base 578) _
  rw [BitVec.zero_add]
  exact ls_subroutine_ok_rocl_of_block (callerProg := callerProg) (j := 578)
    h578_kit hCallerBlk (by decide) (by decide)

theorem cliKpkFull_markPoll_fds_rocl_placed_ok_of_poll [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop}
    {kid ksid : BitVec 32} {kbk : PublicKey} {s1 s2 s3 s4 : Nat}
    {MarkEnv : FsFiles → KpkMarkPollGhost → List AllocEvent → Prop}
    {kitEnv : KyberPreKeyStoreBudgetEnv
      (cliKpkStoreSpecFullPlaced A.repAlloc rd F0 pathOk kid ksid kbk s1 s2 s3 s4)}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hMarkEnv : ∀ fut out self baseKeyA st0 evs,
      MarkEnv F0 ⟨fut, out, self, baseKeyA, kid, ksid, kbk, st0⟩ evs →
        kitEnv.markPollEnv st0 kid ksid kbk evs)
    (h578 : subroutine_ok (lsProg_578 H) (lsmpl.base 578)
      (withFdsGe3Closed (kpkMarkPollSpecPlaced rd pathOk A lim MarkEnv s4)))
    (hCallerBlk : callerBlk < 619 := by decide) :
    let kit := cliKpkStoreSpecFullPlaced A.repAlloc rd F0 pathOk kid ksid kbk s1 s2 s3 s4
    subroutine_ok callerProg (0#64 + kit.markPollOff)
      (withLsRoCl lsmpl (kitKpkMarkPollSpecE M A lim kit kitEnv true)) := by
  intro kit
  have h578_kit : subroutine_ok (lsProg_578 H) (lsmpl.base 578)
      (withLsCodeRoLoaded lsmpl (kitKpkMarkPollSpecE M A lim kit kitEnv true)) := by
    refine subroutine_ok.of_codeLoaded
      fun ⟨⟨fut, out, self, baseKeyA, kid', ksid', kbk'⟩, st0, st⟩ R s0 hpc hrun hpre hsp _ => ?_
    change KyberGhost at st0
    obtain ⟨hcrl, hpre1⟩ := extract_withLsCodeRoLoaded hpre
    have hpre2 : s0.mem ⊨ ⌜s0.fs.files = F0 ∧ FdsGe3Closed s0.fs⌝ ∗
        ((kitKpkMarkPollSpec M A lim kit kitEnv true).pre
          (⟨fut, out, self, baseKeyA, kid', ksid', kbk'⟩, st0, st) s0 ∗ R) := by
      change s0.mem ⊨ (⌜s0.fs.files = F0 ∧ FdsGe3Closed s0.fs⌝ ∗
        (kitKpkMarkPollSpec M A lim kit kitEnv true).pre
          (⟨fut, out, self, baseKeyA, kid', ksid', kbk'⟩, st0, st) s0) ∗ R at hpre1
      simpa only [sepConj_assoc] using hpre1
    rw [satisfies_pure_sepConj] at hpre2
    obtain ⟨⟨hfiles, hfds0⟩, hpre3⟩ := hpre2
    change s0.mem ⊨
      (⌜(0#64 &&& 0xfff#64) = 0#64 ∧ s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
          (kid' = kid ∧ ksid' = ksid ∧ kbk' = kbk) ∧
          FitsEnv M lim st (kitEnv.markPollEnv st0 kid' ksid' kbk')⌝ ∗
        kpkMarkBoxAt fut self baseKeyA kid' ksid' 0#8 ∗
        (⌜CliKpkInvFull rd F0 pathOk kid ksid kbk st0⌝ ∗
          (dirAt A.repAlloc self st0.oneTime ∗ dirAt A.repAlloc (self + 40#64) st0.lastResort)) ∗
        memRegion out 48 ∗ (baseKeyA ↦ₛ kbk'.bytes.toList) ∗
        A.pool lim st s0 ∗ stackAt s0.sp s4) ∗ R at hpre3
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre3
    obtain ⟨⟨_, hx0, hx8, ⟨hxid, hxsid, hxbk⟩, hfit_kit⟩, hpre4⟩ := hpre3
    rw [hxid, hxsid, hxbk] at hfit_kit hpre4 ⊢
    have hpre5 : s0.mem ⊨ ⌜CliKpkInvFull rd F0 pathOk kid ksid kbk st0⌝ ∗
        (kpkMarkBoxAt fut self baseKeyA kid ksid 0#8 ∗
          dirAt A.repAlloc self st0.oneTime ∗ dirAt A.repAlloc (self + 40#64) st0.lastResort ∗
          (baseKeyA ↦ₛ kbk.bytes.toList) ∗ memRegion out 48 ∗
          A.pool lim st s0 ∗ stackAt s0.sp s4 ∗ R) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre4
    rw [satisfies_pure_sepConj] at hpre5
    obtain ⟨hinv, hspatial⟩ := hpre5
    let xg : KpkMarkPollGhost := ⟨fut, out, self, baseKeyA, kid, ksid, kbk, st0⟩
    have hfit_hop : FitsEnv M lim st (MarkEnv s0.fs.files xg) := fun evs hm => by
      rw [hfiles] at hm
      exact hfit_kit evs (hMarkEnv fut out self baseKeyA st0 evs hm)
    have hpre_hop : s0.mem ⊨
        (withFdsGe3Closed (kpkMarkPollSpecPlaced rd pathOk A lim MarkEnv s4)).pre (xg, st) s0 ∗
          R := by
      dsimp only [withFdsGe3Closed, kpkMarkPollSpecPlaced, withLsCodeRoLoaded]
      have h1 : s0.mem ⊨
          ⌜FdsGe3Closed s0.fs⌝ ∗
          (⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
          (⌜s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
            PkNameOk pathOk st0.oneTime kid ∧ KpkBaseKeysOk pathOk st0.lastResort kid ∧
            KpkSeenOk rd s0.fs.files st0.lastResort kid ksid kbk ∧
            st0.oneTime.changed.length < 2 ^ 32 ∧ st0.lastResort.changed.length < 2 ^ 32 ∧
            FitsEnv M lim st (MarkEnv s0.fs.files xg)⌝ ∗
          (kpkMarkBoxAt fut self baseKeyA kid ksid 0#8 ∗
            dirAt A.repAlloc self st0.oneTime ∗ dirAt A.repAlloc (self + 40#64) st0.lastResort ∗
            (baseKeyA ↦ₛ kbk.bytes.toList) ∗ memRegion out 48 ∗
            A.pool lim st s0 ∗ stackAt s0.sp s4 ∗ R))) := by
        rw [satisfies_pure_sepConj]; refine ⟨hfds0, ?_⟩
        rw [satisfies_pure_sepConj]; refine ⟨hcrl, ?_⟩
        rw [satisfies_pure_sepConj]
        exact ⟨⟨hx0, hx8, hinv.markInv.nameOk, hinv.markInv.baseOk, hfiles ▸ hinv.markInv.seenOk,
          hinv.markInv.oneLt.1, hinv.markInv.lastLt.1, hfit_hop⟩, hspatial⟩
      exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) h1
    refine h578.mono_outcome (xg, st) R s0 hpc hrun hpre_hop hsp fun sf hout => ?_
    rcases hout with ⟨hret, hcc, hpost0⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [withFdsGe3Closed] at hpost0
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpost0
      obtain ⟨hfds_sf, hpost⟩ := hpost0
      refine Satisfies.mono (sepConj_mono_left ?_) hpost
      show (kpkMarkPollSpecPlaced rd pathOk A lim MarkEnv s4).post (xg, st) s0 sf ⊢
        (kitKpkMarkPollSpec M A lim kit kitEnv true).post
          (⟨fut, out, self, baseKeyA, kid, ksid, kbk⟩, st0, st) s0 sf
      dsimp only [kpkMarkPollSpecPlaced, withLsCodeRoLoaded, kitKpkMarkPollSpec, kit,
        cliKpkStoreSpecFullPlaced,
        CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliKyberPreKeyStoreSpecPlaced,
        cliKyberPreKeyStoreSpecPlaced, cliKyberPreKeyStoreSpec, cliKpkStoreSpec,
        cliKpkStoreAtFull, kpkMarkPollOutAt, xg]
      refine Entails.sepExists_elim fun evs => ?_
      rw [sepExists_sepConj_left]
      refine Entails.sepExists_elim fun res => ?_
      rw [sepConj_assoc]
      refine Entails.pure_left fun ⟨hres, htr, hmenv⟩ => ?_
      rw [hfiles] at hres hmenv
      subst hres
      have hkenv : kitEnv.markPollEnv st0 kid ksid kbk evs :=
        hMarkEnv fut out self baseKeyA st0 evs hmenv
      set m := kpkMarkOf rd F0 st0 kid ksid kbk
      refine Entails.trans
        (Entails.of_eq (show _ =
          kpkMarkOutAt A.repAlloc out m.1 ∗
            (dirAt A.repAlloc self m.2.oneTime ∗ dirAt A.repAlloc (self + 40#64) m.2.lastResort ∗
              kpkMarkBoxAt fut self baseKeyA kid ksid 1#8 ∗
              (baseKeyA ↦ₛ kbk.bytes.toList) ∗ A.pool lim (M.stepEvents evs st) sf ∗
              stackAt s0.sp s4) by sep_ac_rfl)) ?_
      refine Entails.trans (sepConj_mono_left (cliKpkMarkOut_entails A.repAlloc out m.1)) ?_
      rw [sepExists_sepConj_left]
      refine Entails.sepExists_elim fun ans => ?_
      rw [sepConj_assoc]
      refine Entails.pure_left fun hrel => ?_
      refine Entails.sepExists_right ans (Entails.sepExists_right evs ?_)
      refine Entails.pure_right ⟨hrel, by rw [List.append_nil]; exact htr, hkenv, hfds_sf⟩ ?_
      refine Entails.trans ?_
        (Entails.of_eq (show
          ⌜CliKpkInvFull rd F0 pathOk kid ksid kbk m.2⌝ ∗
            (unitSpePollOutAt (cliKpkMarkErrSpec A.repAlloc) out ans ∗
              (dirAt A.repAlloc self m.2.oneTime ∗ dirAt A.repAlloc (self + 40#64) m.2.lastResort ∗
                kpkMarkBoxAt fut self baseKeyA kid ksid 1#8 ∗
                (baseKeyA ↦ₛ kbk.bytes.toList) ∗ A.pool lim (M.stepEvents evs st) sf ∗
                stackAt s0.sp s4)) = _ by sep_ac_rfl))
      exact Entails.pure_right hinv.mark (Entails.refl _)
    · dsimp only [withFdsGe3Closed, kpkMarkPollSpecPlaced, withLsCodeRoLoaded] at hpan
      exact (not_satisfies_false_sepConj hpan).elim
    · dsimp only [withFdsGe3Closed, kpkMarkPollSpecPlaced, withLsCodeRoLoaded] at hex
      exact (not_satisfies_false_sepConj hex).elim
    · dsimp only [withFdsGe3Closed, kpkMarkPollSpecPlaced, withLsCodeRoLoaded] at hoom
      exact (not_satisfies_false_sepConj hoom).elim
  change subroutine_ok callerProg (0#64 + lsmpl.base 578) _
  rw [BitVec.zero_add]
  exact ls_subroutine_ok_rocl_of_block (callerProg := callerProg) (j := 578)
    h578_kit hCallerBlk (by decide) (by decide)

/-- Assemble `KyberPreKeyStoreKitPlacedOkFds` for `cliKpkStoreSpecFullPlaced` from
`AllocContractsFsPlaced` and the Block `576`/`578` poll contracts. -/
theorem cliKpkKitPlacedOkFds_full_of_polls [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop}
    {kid ksid : BitVec 32} {kbk : PublicKey} {s1 s2 s3 s4 : Nat}
    {GetPollEnv : FsFiles → KpkPollGhost → List AllocEvent → Prop}
    {MarkEnv : FsFiles → KpkMarkPollGhost → List AllocEvent → Prop}
    (kitEnv : KyberPreKeyStoreBudgetEnv
      (cliKpkStoreSpecFullPlaced A.repAlloc rd F0 pathOk kid ksid kbk s1 s2 s3 s4))
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hFs : AllocContractsFsPlaced A lim H)
    (hs1 : 32 + extHookStack ≤ s1)
    (hs3 : 48 + extHookStack ≤ s3)
    (hGetEnv : ∀ fut out self st0 evs,
      GetPollEnv F0 ⟨fut, out, self, kid, st0⟩ evs → kitEnv.getPollEnv st0 kid evs)
    (hMarkEnv : ∀ fut out self baseKeyA st0 evs,
      MarkEnv F0 ⟨fut, out, self, baseKeyA, kid, ksid, kbk, st0⟩ evs →
        kitEnv.markPollEnv st0 kid ksid kbk evs)
    (h576 : subroutine_ok (lsProg_576 H) (lsmpl.base 576)
      (withFdsGe3Closed (kpkGetPollSpecPlaced rd pathOk A lim GetPollEnv s2)))
    (h578 : subroutine_ok (lsProg_578 H) (lsmpl.base 578)
      (withFdsGe3Closed (kpkMarkPollSpecPlaced rd pathOk A lim MarkEnv s4))) :
    KyberPreKeyStoreKitPlacedOkFds A lim
      (cliKpkStoreSpecFullPlaced A.repAlloc rd F0 pathOk kid ksid kbk s1 s2 s3 s4)
      kitEnv H where
  getShim hblk := cliKpkFull_getShim_fds_rocl_placed_ok hFs hs1 hblk
  getPoll hblk := cliKpkFull_getPoll_fds_rocl_placed_ok_of_poll hGetEnv h576 hblk
  getFutDrop hblk := by
    change subroutine_ok _ (0#64 + lsDropOffPlaced) _
    rw [lsDropOffPlaced_eq hDropNz]
    exact cliIdFutDrop_fds_rocl_placed_ok hblk
  markShim hblk := cliKpkFull_markShim_fds_rocl_placed_ok hFs hs3 hblk
  markPoll hblk := cliKpkFull_markPoll_fds_rocl_placed_ok_of_poll hMarkEnv h578 hblk
  markFutDrop hblk := by
    change subroutine_ok _ (0#64 + lsDropOffPlaced) _
    rw [lsDropOffPlaced_eq hDropNz]
    exact cliIdFutDrop_fds_rocl_placed_ok hblk

/-- Assemble `KyberPreKeyStoreKitPlacedOkFds` for general-`G` `cliKpkStoreSpecPlaced`. -/
theorem cliKpkStorePlacedOkFds_of_polls [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop}
    {kid ksid : BitVec 32} {kbk : PublicKey}
    (G : CliKpkGetSide) {s1 s2 s3 s4 : Nat}
    (hGetBox : ∀ box self id st, pkBoxAt box self id st ⊢ memRegion box 16)
    (hMarkBox : ∀ box self baseKeyA id signedId st,
      kpkMarkBoxAt box self baseKeyA id signedId st ⊢ memRegion box 32)
    (MarkEnv : FsFiles → KpkMarkPollGhost → List AllocEvent → Prop)
    (kitEnv : KyberPreKeyStoreBudgetEnv
      (cliKpkStoreSpecPlaced A.repAlloc rd F0 pathOk kid ksid kbk G s1 s2 s3 s4 hGetBox hMarkBox))
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hFs : AllocContractsFsPlaced A lim H)
    (hs1 : 32 + extHookStack ≤ s1)
    (hs3 : 48 + extHookStack ≤ s3)
    (hGetPoll : subroutine_ok (lsProg_576 H) (lsmpl.base 576)
      (withLsCodeRoLoaded lsmpl
        (kitKpkGetPollSpecE M A lim
          (cliKpkStoreSpecPlaced A.repAlloc rd F0 pathOk kid ksid kbk G s1 s2 s3 s4
            hGetBox hMarkBox)
          kitEnv true)))
    (hMarkEnv : ∀ fut out self baseKeyA st0 evs,
      MarkEnv F0 ⟨fut, out, self, baseKeyA, kid, ksid, kbk, st0⟩ evs →
        kitEnv.markPollEnv st0 kid ksid kbk evs)
    (hMarkPoll : subroutine_ok (lsProg_578 H) (lsmpl.base 578)
      (withFdsGe3Closed (kpkMarkPollSpecPlaced rd pathOk A lim MarkEnv s4))) :
    KyberPreKeyStoreKitPlacedOkFds A lim
      (cliKpkStoreSpecPlaced A.repAlloc rd F0 pathOk kid ksid kbk G s1 s2 s3 s4 hGetBox hMarkBox)
      kitEnv H where
  getShim hblk := cliKpkGetShim_fds_rocl_placed_ok G hGetBox hMarkBox hFs hs1 hblk
  getPoll {callerProg} {callerBlk} _ hblk := by
    change subroutine_ok callerProg (0#64 + lsmpl.base 576) _
    rw [BitVec.zero_add]
    exact ls_subroutine_ok_rocl_of_block (callerProg := callerProg) (j := 576)
      hGetPoll hblk (by decide) (by decide)
  getFutDrop hblk := by
    change subroutine_ok _ (0#64 + lsDropOffPlaced) _
    rw [lsDropOffPlaced_eq hDropNz]
    exact cliIdFutDrop_fds_rocl_placed_ok hblk
  markShim hblk := cliKpkMarkShim_fds_rocl_placed_ok G hGetBox hMarkBox hFs hs3 hblk
  markPoll hblk :=
    cliKpkStoreSpecPlaced_markPoll_fds_rocl_of_poll G hGetBox hMarkBox hMarkEnv hMarkPoll hblk
  markFutDrop hblk := by
    change subroutine_ok _ (0#64 + lsDropOffPlaced) _
    rw [lsDropOffPlaced_eq hDropNz]
    exact cliIdFutDrop_fds_rocl_placed_ok hblk

/-! ## `FsAtFds` and `writeFileHook` preservation -/

theorem fsAt_cliKpkFullKit_of_fdsGe3Closed [LibsignalPlacement] {A : RustAlloc}
    {envOk : FsFiles → Prop} {rd : ReadRule} {F0 : FsFiles}
    {pathOk : List (BitVec 8) → Prop} {kid ksid : BitVec 32} {kbk : PublicKey}
    {s1 s2 s3 s4 : Nat} {P : Program} {s : State}
    (hP : TraceFsSound P) (henv : envOk F0) (hfiles : s.fs.files = F0) (hfds : FdsGe3Closed s.fs) :
    FsAtFds envOk
      (cliKpkStoreSpecFullPlaced A rd F0 pathOk kid ksid kbk s1 s2 s3 s4).fdsOk
      (cliKpkStoreSpecFullPlaced A rd F0 pathOk kid ksid kbk s1 s2 s3 s4).Quiet P s :=
  .inr ⟨cliKpkStoreSpecFullPlaced_quiet (A := A) rd F0 pathOk kid ksid kbk s1 s2 s3 s4,
    hP, hfiles.symm ▸ henv, hfds⟩

theorem cliKpkStoreSpecFullPlaced_writeFileHook [LibsignalPlacement] {A : RustAlloc}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop}
    {kid ksid : BitVec 32} {kbk : PublicKey} {s1 s2 s3 s4 : Nat} {s : State}
    (hfds : (cliKpkStoreSpecFullPlaced A rd F0 pathOk kid ksid kbk s1 s2 s3 s4).fdsOk s.fs) :
    (cliKpkStoreSpecFullPlaced A rd F0 pathOk kid ksid kbk s1 s2 s3 s4).fdsOk
      (writeFileHook s).fs :=
  fdsGe3Closed_writeFileHook hfds

theorem hookOk_writeFileHook_withFdsGe3Closed_kpk {α : Type} {S : Spec α}
    (h : HookOk writeFileHook S) :
    HookOk writeFileHook (withFdsGe3Closed S) :=
  hookOk_withFdsGe3Closed_writeFileHook h

end LibsignalBinary.Proofs.SignalSession.Cli.KitInst.KyberPreKeyKitFdsPlacedBudget
