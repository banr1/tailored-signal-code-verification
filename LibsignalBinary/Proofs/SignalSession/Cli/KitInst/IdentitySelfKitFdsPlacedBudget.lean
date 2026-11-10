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
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SelfSpecPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.SelfKitOkPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.ShimsPlacedBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Placed Budgeted `IdentitySelfStoreSpec` with Closed-FD Invariant

Establishes `IdentitySelfStoreKitPlacedOkIFds` (`fds = true`) on `cliIdSelfSpecFullPlaced`,
shim `Spec.keepsFs` contracts on Blocks `602` (`get_identity_key_pair`) and `603`
(`get_local_registration_id`), the full-invariant lift `cliIdKitPlacedOkIFds_full` on
`cliIdStoreSpecFullPlaced`, and `writeFileHook` preservation of `FdsGe3Closed`.
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentitySelfKitFdsPlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSession (IdentityKey)
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.RecordCodecs (IdentityKeyPair)
open CryptoVerification.LibsignalTripleRatchet (extHookStack withStack)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles IdentitySelfStoreSpec IdentityStoreSpec LibsignalCodeRoLoaded TraceFsSound
   extract_withLsCodeRoLoaded kpPollOutAt ls_subroutine_ok_rocl_of_block regIdPollOutAt
   sepWP_seq_lscro speErrAt withEnvPre withLsCodeRoLoaded withLsLogOff withLsRoCl)
open LibsignalBinary.Proofs.PublicApi.StoreKit.FsFds (FsAtFds)
open CryptoVerification.SignalSession
  (lsDropOffPlaced lsDropOffPlaced_eq lsRustAllocSymCli lsRustNoAllocShimSymCli
   writeFileHook)
open CryptoVerification.SignalSession.Cli
  (IdGhost ReadRule cliIdentityVtSym dirAt idKeyPairFutVtSym idRegIdFutVtSym pathOf utf8)
open CryptoVerification.SignalSession.Cli.Placed
  (blkPC_602 blkPC_603 blkPl_602 blkPl_603 lsProg_567 lsProg_568 lsProg_602 lsProg_603)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
  (IdOwnPollGhostPlaced idKeyPairOutAt idKeyPairOutAtPlaced idOwnFutBoxAt idOwnFutBoxAtPlaced
   idRegIdOutAt idRegIdOutAtPlaced)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.StoreCalleesProofs
  (memRegion_16_ownBox)
open CryptoVerification.SignalSession.Cli.Store.PkShims.Helpers (pkShimStack stackAt_pkShim)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon
  (ls_transfer_lscro satisfies_lscro_pre)
open CryptoVerification.SignalSession.Cli.KitInst
  (CliIdInv CliSelfSpeErr cliIdStoreAt cliIdentitySelfSpec cliIdentitySelfSpecPlaced
   cliIdentitySelf_kpErr_layout_placed cliIdentitySelf_regIdErr_layout_placed
   cliIdentityStoreSpec cliIdentityStoreSpecPlaced cliSelfSpeErrSpec)
open CryptoVerification.SignalSession.Cli.KitInst.IdKit (cliIdentityKitSpecPlaced)
open CryptoVerification.SignalSession.Cli.KitInst.SelfRel
  (cliKpRel cliKpRel_error_iff cliKpRel_ok_iff cliRegIdRel cliRegIdRel_error_iff cliRegIdRel_ok_iff)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll
  (CliIdOwnInv cliIdSelfSpecFullPlaced cliIdSelfSpecFullPlaced_quiet cliIdStoreAtFull
   cliIdStoreSpecFull cliIdStoreSpecFullPlaced cliIdStoreSpecFullPlaced_quiet)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents
   RustCliAllocBudget RustLayoutOk rustAllocEvents)
open LibsignalBinary.Heap.IfaceBudgetLemmas (rustCliAllocNoOomSpecWithStack)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (rustAllocNoOomSpecWithStack)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (BoxAllocEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (IdentityStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentitySelfStoreKitBudget
  (IdentitySelfStoreBudgetEnv kitKpPollSpec kitKpPollSpecE kitKpShimSpec kitRegIdPollSpec
   kitRegIdPollSpecE kitRegIdShimSpec)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
  (IdentitySelfStoreKitPlacedOkIFds IdentityStoreKitPlacedOkIFds kitKpPollPlacedSpecI
   kitRegIdPollPlacedSpecI kitSavePollPlacedSpec kitSavePollPlacedSpecE kitSavePollPlacedSpecI
   kitTrustPollPlacedSpec kitTrustPollPlacedSpecE kitTrustPollPlacedSpecI)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsFsPlaced idKeyPairPollSpecPlaced idOwnShimSpecPlaced idRegIdPollSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget
  (allocNoOom_lscro_of_cli lift_stk_lscro_budget)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget.AllocContractsFsPlaced
  (toAllocContractsX)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitFdsPilotPlacedBudget
  (cliIdFutDrop_fds_rocl_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed fdsGe3Closed_writeFileHook hookOk_withFdsGe3Closed_writeFileHook withFdsGe3Closed)

@[simp]
theorem cliIdentitySelfSpecPlaced_fdsOk [LibsignalPlacement] (A : RustAlloc)
    (rd : ReadRule) (F0 : FsFiles) (pathOk : List (BitVec 8) → Prop) (peer : AddrGhost)
    {t1 t2 t3 t4 : Nat} (k1 k2 k3 k4 : Nat) (fs : FsState) :
    (cliIdentitySelfSpecPlaced A rd F0 pathOk peer
      (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) k1 k2 k3 k4).fdsOk fs =
      FdsGe3Closed fs :=
  rfl

@[simp]
theorem cliIdStoreSpecFullPlaced_fdsOk [LibsignalPlacement] (A : RustAlloc)
    (rd : ReadRule) (F0 : FsFiles) (pathOk : List (BitVec 8) → Prop) (peer : AddrGhost)
    (t1 t2 t3 t4 : Nat) (fs : FsState) :
    (cliIdStoreSpecFullPlaced A rd F0 pathOk peer t1 t2 t3 t4).fdsOk fs =
      FdsGe3Closed fs :=
  rfl

@[simp]
theorem cliIdSelfSpecFullPlaced_fdsOk [LibsignalPlacement] (A : RustAlloc)
    (rd : ReadRule) (F0 : FsFiles) (pathOk : List (BitVec 8) → Prop) (peer : AddrGhost)
    {t1 t2 t3 t4 : Nat} (k1 k2 k3 k4 : Nat) (fs : FsState) :
    (cliIdSelfSpecFullPlaced A rd F0 pathOk peer
      (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) k1 k2 k3 k4).fdsOk fs =
      FdsGe3Closed fs :=
  rfl

private theorem idKeyPairOutAtPlaced_eq_local (A : RustAlloc) (out : BitVec 64)
    (ans : Except Unit IdentityKeyPair) :
    idKeyPairOutAtPlaced A out ans = idKeyPairOutAt A out ans := by
  cases ans <;> rfl

private theorem idRegIdOutAtPlaced_eq_local (A : RustAlloc) (out : BitVec 64)
    (ans : Except Unit (BitVec 32)) :
    idRegIdOutAtPlaced A out ans = idRegIdOutAt A out ans := by
  cases ans <;> rfl

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

private theorem idOwnShim_lift_stk_keepsFs_placed [LibsignalPlacement] {M : AllocCostModel}
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

/-- Block `602` (`idKeyPairShim`) preserves `fs` under `AllocContractsFsPlaced`. -/
theorem idKeyPairShim_keepsFs_fixed_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFs : AllocContractsFsPlaced A lim H) :
    subroutine_ok (lsProg_602 H) (lsmpl.base 602)
      (idOwnShimSpecPlaced idKeyPairFutVtSym A lim pkShimStack).keepsFs := by
  unfold Spec.keepsFs idOwnShimSpecPlaced withLsCodeRoLoaded
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
    rustCliAllocNoOomSpecWithStack, AllocCallPreserved] at halloc
  apply sepWP_seq_lscro (mid := lsρ lsRustNoAllocShimSymCli) hcrl0
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSymCli)
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by wp_norm_lhs)
  intro hcrl1
  wp_call_lscro
    (shim_keepsFs_lscro_of_fs (callerProg := (blkPC_602).rebase (blkPl_602).base H)
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
  idOwnShim_lift_stk_keepsFs_placed (idKeyPairShim_keepsFs_fixed_placed_ok hFs) hstk

/-- Block `603` (`idRegIdShim`) preserves `fs` under `AllocContractsFsPlaced`. -/
theorem idRegIdShim_keepsFs_fixed_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFs : AllocContractsFsPlaced A lim H) :
    subroutine_ok (lsProg_603 H) (lsmpl.base 603)
      (idOwnShimSpecPlaced idRegIdFutVtSym A lim pkShimStack).keepsFs := by
  unfold Spec.keepsFs idOwnShimSpecPlaced withLsCodeRoLoaded
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
    rustCliAllocNoOomSpecWithStack, AllocCallPreserved] at halloc
  apply sepWP_seq_lscro (mid := lsρ lsRustNoAllocShimSymCli) hcrl0
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSymCli)
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by wp_norm_lhs)
  intro hcrl1
  wp_call_lscro
    (shim_keepsFs_lscro_of_fs (callerProg := (blkPC_603).rebase (blkPl_603).base H)
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
  idOwnShim_lift_stk_keepsFs_placed (idRegIdShim_keepsFs_fixed_placed_ok hFs) hstk

end Shims

theorem cliIdSelfKpShim_fds_rocl_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost}
    {t1 t2 t3 t4 k1 k2 k3 k4 : Nat}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hFs : AllocContractsFsPlaced A lim H)
    (hk1 : 32 + extHookStack ≤ k1) (hblk : callerBlk < 619 := by decide) :
    let skit := cliIdSelfSpecFullPlaced A.repAlloc rd F0 pathOk peer
      (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) k1 k2 k3 k4
    subroutine_ok callerProg (0#64 + skit.kpShimOff)
      (withLsRoCl lsmpl (kitKpShimSpec M A lim skit true)) := by
  intro skit
  have h602 := idKeyPairShim_keepsFs_placed_ok_of_deps hFs hk1
  have h602_kit : subroutine_ok (lsProg_602 H) (lsmpl.base 602)
      (withLsCodeRoLoaded lsmpl (kitKpShimSpec M A lim skit true)) := by
    refine subroutine_ok_outcome_intro fun ⟨self, st⟩ R s0 hpc hrun hpre hsp => ?_
    obtain ⟨hcrl, hpre0⟩ := extract_withLsCodeRoLoaded hpre
    dsimp only [kitKpShimSpec, skit, cliIdSelfSpecFullPlaced] at hpre0
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre0
    rcases hpre0 with ⟨⟨hx0, hfit, hfds0⟩, hrest⟩
    have hpre' :
        s0.mem ⊨
          ((idOwnShimSpecPlaced idKeyPairFutVtSym A lim k1).keepsFs).pre (self, st) s0 ∗ R := by
      dsimp only [Spec.keepsFs]
      refine satisfies_lscro_pre hcrl ?_
      dsimp only [idOwnShimSpecPlaced, withLsCodeRoLoaded]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hx0, hfit⟩, by simpa only [sepConj_assoc] using hrest⟩
    refine h602.mono_outcome (self, st) R s0 hpc hrun hpre' hsp ?_
    rintro sf (⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩)
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [Spec.keepsFs, idOwnShimSpecPlaced, withLsCodeRoLoaded, kitKpShimSpec,
        skit, cliIdSelfSpecFullPlaced, idOwnFutBoxAtPlaced, idOwnFutBoxAt] at hq ⊢
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
    · dsimp only [Spec.keepsFs, idOwnShimSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
    · dsimp only [Spec.keepsFs, idOwnShimSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
    · dsimp only [Spec.keepsFs, idOwnShimSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
  change subroutine_ok callerProg (0#64 + lsmpl.base 602) _
  rw [BitVec.zero_add]
  exact ls_subroutine_ok_rocl_of_block (callerProg := callerProg) (j := 602)
    h602_kit hblk (by decide) (by decide)

theorem cliIdentitySelfKpShim_fds_rocl_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost}
    {t1 t2 t3 t4 k1 k2 k3 k4 : Nat}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hFs : AllocContractsFsPlaced A lim H)
    (hk1 : 32 + extHookStack ≤ k1) (hblk : callerBlk < 619 := by decide) :
    let skit := cliIdentitySelfSpecPlaced A.repAlloc rd F0 pathOk peer
      (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) k1 k2 k3 k4
    subroutine_ok callerProg (0#64 + skit.kpShimOff)
      (withLsRoCl lsmpl (kitKpShimSpec M A lim skit true)) :=
  cliIdSelfKpShim_fds_rocl_placed_ok (rd := rd) (F0 := F0) (pathOk := pathOk) (peer := peer)
    (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) (k1 := k1) (k2 := k2) (k3 := k3) (k4 := k4)
    hFs hk1 hblk

theorem cliIdSelfRegIdShim_fds_rocl_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost}
    {t1 t2 t3 t4 k1 k2 k3 k4 : Nat}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hFs : AllocContractsFsPlaced A lim H)
    (hk3 : 32 + extHookStack ≤ k3) (hblk : callerBlk < 619 := by decide) :
    let skit := cliIdSelfSpecFullPlaced A.repAlloc rd F0 pathOk peer
      (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) k1 k2 k3 k4
    subroutine_ok callerProg (0#64 + skit.regIdShimOff)
      (withLsRoCl lsmpl (kitRegIdShimSpec M A lim skit true)) := by
  intro skit
  have h603 := idRegIdShim_keepsFs_placed_ok_of_deps hFs hk3
  have h603_kit : subroutine_ok (lsProg_603 H) (lsmpl.base 603)
      (withLsCodeRoLoaded lsmpl (kitRegIdShimSpec M A lim skit true)) := by
    refine subroutine_ok_outcome_intro fun ⟨self, st⟩ R s0 hpc hrun hpre hsp => ?_
    obtain ⟨hcrl, hpre0⟩ := extract_withLsCodeRoLoaded hpre
    dsimp only [kitRegIdShimSpec, skit, cliIdSelfSpecFullPlaced] at hpre0
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre0
    rcases hpre0 with ⟨⟨hx0, hfit, hfds0⟩, hrest⟩
    have hpre' :
        s0.mem ⊨
          ((idOwnShimSpecPlaced idRegIdFutVtSym A lim k3).keepsFs).pre (self, st) s0 ∗ R := by
      dsimp only [Spec.keepsFs]
      refine satisfies_lscro_pre hcrl ?_
      dsimp only [idOwnShimSpecPlaced, withLsCodeRoLoaded]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hx0, hfit⟩, by simpa only [sepConj_assoc] using hrest⟩
    refine h603.mono_outcome (self, st) R s0 hpc hrun hpre' hsp ?_
    rintro sf (⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩)
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [Spec.keepsFs, idOwnShimSpecPlaced, withLsCodeRoLoaded, kitRegIdShimSpec,
        skit, cliIdSelfSpecFullPlaced, idOwnFutBoxAtPlaced, idOwnFutBoxAt] at hq ⊢
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
    · dsimp only [Spec.keepsFs, idOwnShimSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
    · dsimp only [Spec.keepsFs, idOwnShimSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
    · dsimp only [Spec.keepsFs, idOwnShimSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
  change subroutine_ok callerProg (0#64 + lsmpl.base 603) _
  rw [BitVec.zero_add]
  exact ls_subroutine_ok_rocl_of_block (callerProg := callerProg) (j := 603)
    h603_kit hblk (by decide) (by decide)

theorem cliIdentitySelfRegIdShim_fds_rocl_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost}
    {t1 t2 t3 t4 k1 k2 k3 k4 : Nat}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hFs : AllocContractsFsPlaced A lim H)
    (hk3 : 32 + extHookStack ≤ k3) (hblk : callerBlk < 619 := by decide) :
    let skit := cliIdentitySelfSpecPlaced A.repAlloc rd F0 pathOk peer
      (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) k1 k2 k3 k4
    subroutine_ok callerProg (0#64 + skit.regIdShimOff)
      (withLsRoCl lsmpl (kitRegIdShimSpec M A lim skit true)) :=
  cliIdSelfRegIdShim_fds_rocl_placed_ok (rd := rd) (F0 := F0) (pathOk := pathOk) (peer := peer)
    (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) (k1 := k1) (k2 := k2) (k3 := k3) (k4 := k4)
    hFs hk3 hblk

/-! ## Poll lifting and `IdentitySelfStoreKitPlacedOkIFds` assembly -/

theorem cliIdSelfKpPoll_fds_rocl_placed_ok_of_poll [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost}
    {t1 t2 t3 t4 k1 k2 k3 k4 : Nat}
    {KpPollEnv : FsFiles → IdOwnPollGhostPlaced → List AllocEvent → Prop}
    {senv : IdentitySelfStoreBudgetEnv
      (cliIdSelfSpecFullPlaced A.repAlloc rd F0 pathOk peer
        (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) k1 k2 k3 k4)}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hKpEnv : ∀ fut out self (g : IdGhost) evs,
      KpPollEnv F0 ⟨fut, out, self, g.own⟩ evs → senv.kpPollEnv g evs)
    (h567 : subroutine_ok (lsProg_567 H) (lsmpl.base 567)
      (withFdsGe3Closed (idKeyPairPollSpecPlaced rd pathOk A lim KpPollEnv k2)))
    (hCallerBlk : callerBlk < 619 := by decide) :
    let skit := cliIdSelfSpecFullPlaced A.repAlloc rd F0 pathOk peer
      (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) k1 k2 k3 k4
    subroutine_ok callerProg (0#64 + skit.kpPollOff)
      (withLsRoCl lsmpl (kitKpPollPlacedSpecI M A lim skit senv true)) := by
  intro skit
  have h567_kit : subroutine_ok (lsProg_567 H) (lsmpl.base 567)
      (withLsCodeRoLoaded lsmpl (kitKpPollPlacedSpecI M A lim skit senv true)) := by
    refine subroutine_ok_outcome_intro fun ⟨fut, out, self, g, st⟩ R s0 hpc hrun hpre hsp => ?_
    change IdGhost at g
    dsimp only [withLsCodeRoLoaded, kitKpPollPlacedSpecI, withLsLogOff,
      kitKpPollSpecE, kitKpPollSpec, withEnvPre,
      skit, cliIdSelfSpecFullPlaced,
      cliIdStoreSpecFullPlaced, cliIdStoreSpecFull, cliIdStoreAtFull,
      cliIdentityStoreSpec, cliIdStoreAt] at hpre
    have hpre' : s0.mem ⊨
        ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
        (⌜s0.fs.files = F0 ∧ FdsGe3Closed s0.fs⌝ ∗
        (⌜s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
          FitsEnv M lim st (senv.kpPollEnv g)⌝ ∗
        (⌜CliIdOwnInv rd F0 pathOk g.own⌝ ∗
        (⌜CliIdInv rd F0 pathOk peer g⌝ ∗
        (idOwnFutBoxAt fut self 0#8 ∗ dirAt A.repAlloc self g.own ∗
          memRegion out 72 ∗ lsLogOff ∗ A.pool lim st s0 ∗
          stackAt s0.sp k2 ∗
          (dirAt A.repAlloc (self + 40#64) g.peers ∗ R)))))) :=
      Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hpre
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hcrl, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨⟨hfiles, hfds0⟩, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨⟨hx0, hx8, hfit⟩, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hown, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hinv, hspatial⟩ := hpre'
    let frameKpCore : SepProp :=
      ⌜CliIdOwnInv rd F0 pathOk g.own⌝ ∗
      ⌜CliIdInv rd F0 pathOk peer g⌝ ∗
      dirAt A.repAlloc (self + 40#64) g.peers
    have hfit_hop :
        FitsEnv M lim st (KpPollEnv s0.fs.files ⟨fut, out, self, g.own⟩) := fun evs hm => by
      rw [hfiles] at hm
      exact hfit evs (hKpEnv fut out self g evs hm)
    have hhop_pure :
        s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
          g.own.path.length < 2 ^ 32 ∧
          pathOk (pathOf g.own.path (utf8 "identity-key-pair")) ∧
          (∀ bs, g.own.get rd s0.fs.files (utf8 "identity-key-pair") = .ok bs →
            bs.length < 2 ^ 32) ∧
          FitsEnv M lim st (KpPollEnv s0.fs.files ⟨fut, out, self, g.own⟩) :=
      ⟨hx0, hx8, hown.ownPathLt, hown.kpPathOk,
        fun bs hbs => hown.kpSizeOk bs (hfiles ▸ hbs), hfit_hop⟩
    have hm_hop :
        s0.mem ⊨
          (withFdsGe3Closed (idKeyPairPollSpecPlaced rd pathOk A lim KpPollEnv k2)).pre
            (⟨fut, out, self, g.own⟩, st) s0 ∗
          (frameKpCore ∗ R) := by
      dsimp only [withFdsGe3Closed, idKeyPairPollSpecPlaced, withLsCodeRoLoaded, frameKpCore,
        idOwnFutBoxAtPlaced, idOwnFutBoxAt] at hspatial ⊢
      have h1 : s0.mem ⊨
          ⌜FdsGe3Closed s0.fs⌝ ∗
          (⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
          (⌜s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
            g.own.path.length < 2 ^ 32 ∧
            pathOk (pathOf g.own.path (utf8 "identity-key-pair")) ∧
            (∀ bs, g.own.get rd s0.fs.files (utf8 "identity-key-pair") = .ok bs →
              bs.length < 2 ^ 32) ∧
            FitsEnv M lim st (KpPollEnv s0.fs.files ⟨fut, out, self, g.own⟩)⌝ ∗
          (⌜CliIdOwnInv rd F0 pathOk g.own⌝ ∗
          (⌜CliIdInv rd F0 pathOk peer g⌝ ∗
          (idOwnFutBoxAt fut self 0#8 ∗ dirAt A.repAlloc self g.own ∗
            memRegion out 72 ∗ lsLogOff ∗ A.pool lim st s0 ∗
            stackAt s0.sp k2 ∗
            (dirAt A.repAlloc (self + 40#64) g.peers ∗ R)))))) := by
        rw [satisfies_pure_sepConj]; refine ⟨hfds0, ?_⟩
        rw [satisfies_pure_sepConj]; refine ⟨hcrl, ?_⟩
        rw [satisfies_pure_sepConj]; refine ⟨hhop_pure, ?_⟩
        rw [satisfies_pure_sepConj]; refine ⟨hown, ?_⟩
        rw [satisfies_pure_sepConj]
        dsimp only [idOwnFutBoxAt]
        exact ⟨hinv, hspatial⟩
      dsimp only [idOwnFutBoxAt, CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff,
        CryptoVerification.LibsignalTripleRatchet.lsLogOff] at h1 ⊢
      exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) h1
    refine h567.mono_outcome (⟨fut, out, self, g.own⟩, st) (frameKpCore ∗ R)
      s0 hpc hrun hm_hop hsp ?_
    rintro sf (⟨hret, hcc, hpost0⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩)
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [withFdsGe3Closed] at hpost0
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpost0
      obtain ⟨hfds_sf, hpost⟩ := hpost0
      dsimp only [idKeyPairPollSpecPlaced, withLsCodeRoLoaded, frameKpCore] at hpost
      simp_rw [idKeyPairOutAtPlaced_eq_local] at hpost
      simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
        satisfies_pure_sepConj] at hpost
      obtain ⟨evs, ans0, ⟨hans0, htr, hevs⟩, hm⟩ := hpost
      rw [hfiles, IdGhost.keyPair_mk_own] at hans0
      rw [hfiles] at hevs
      have hsenv : senv.kpPollEnv g evs := hKpEnv fut out self g evs hevs
      dsimp only [withLsCodeRoLoaded, kitKpPollPlacedSpecI, withLsLogOff,
        kitKpPollSpecE, kitKpPollSpec, withEnvPre,
        skit, cliIdSelfSpecFullPlaced,
        cliIdStoreSpecFullPlaced, cliIdStoreSpecFull, cliIdStoreAtFull,
        cliIdentityStoreSpec, cliIdStoreAt]
      simp only [sepExists_sepConj_left, satisfies_sepExists]
      cases ans0 with
      | ok kp =>
        have hrel : cliKpRel (E := CliSelfSpeErr) rd F0 g (.ok kp) :=
          (cliKpRel_ok_iff (E := CliSelfSpeErr) rd F0 g kp).2 hans0.symm
        refine ⟨.ok kp, evs, ?_⟩
        dsimp only [kpPollOutAt, idKeyPairOutAt, idOwnFutBoxAtPlaced, idOwnFutBoxAt] at hm ⊢
        have hgoal : sf.mem ⊨
            ⌜cliKpRel (E := CliSelfSpeErr) rd F0 g (.ok kp) ∧
              sf.trace = s0.trace ++ [] ∧
              senv.kpPollEnv g evs ∧ FdsGe3Closed sf.fs⌝ ∗
            (idKeyPairOutAt A.repAlloc out (.ok kp) ∗ idOwnFutBoxAt fut self 1#8 ∗
              dirAt A.repAlloc self g.own ∗ lsLogOff ∗ A.pool lim (M.stepEvents evs st) sf ∗
              stackAt s0.sp k2 ∗
              ⌜CliIdOwnInv rd F0 pathOk g.own⌝ ∗
              ⌜CliIdInv rd F0 pathOk peer g⌝ ∗
              dirAt A.repAlloc (self + 40#64) g.peers ∗ R) := by
          dsimp only [idKeyPairOutAt, idOwnFutBoxAt]
          rw [satisfies_pure_sepConj]
          exact ⟨⟨hrel, by rw [List.append_nil]; exact htr, hsenv, hfds_sf⟩, hm⟩
        dsimp only [idKeyPairOutAt, idOwnFutBoxAt] at hgoal
        exact Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hgoal
      | error u =>
        cases u
        have herr_ent :
            idKeyPairOutAt A.repAlloc out (.error ()) ⊢
              ∃∗ e : skit.KpErr, kpPollOutAt skit out (.error e) :=
          (cliIdentitySelf_kpErr_layout_placed A.repAlloc F0
            (peer := peer) (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4)
            (k1 := k1) (k2 := k2) (k3 := k3) (k4 := k4) out).2
        have hm' := Satisfies.mono (sepConj_mono_left herr_ent) hm
        rw [sepExists_sepConj_left, satisfies_sepExists] at hm'
        dsimp only [skit, cliIdSelfSpecFullPlaced, cliIdentitySelfSpecPlaced, cliIdentitySelfSpec,
          kpPollOutAt, idOwnFutBoxAtPlaced, idOwnFutBoxAt] at hm' ⊢
        obtain ⟨e, hme⟩ := hm'
        have hrel : cliKpRel rd F0 g (.error e) :=
          (cliKpRel_error_iff rd F0 g e).2 hans0.symm
        refine ⟨.error e, evs, ?_⟩
        dsimp only [kpPollOutAt, cliIdentitySelfSpecPlaced, cliIdentitySelfSpec]
        have hgoal : sf.mem ⊨
            ⌜cliKpRel rd F0 g (.error e) ∧
              sf.trace = s0.trace ++ [] ∧
              senv.kpPollEnv g evs ∧ FdsGe3Closed sf.fs⌝ ∗
            (((out ↦₈ 1#8) ∗ memRegion (out + 1#64) 7 ∗
                speErrAt (cliSelfSpeErrSpec A.repAlloc) (out + 8#64) e ∗
                memRegion (out + 56#64) 16) ∗
              ((fut ↦₆₄ self) ∗ ((fut + 8#64) ↦₈ 1#8) ∗ memRegion (fut + 9#64) 7) ∗
              dirAt A.repAlloc self g.own ∗ lsLogOff ∗
              A.pool lim (M.stepEvents evs st) sf ∗
              stackAt s0.sp k2 ∗
              ⌜CliIdOwnInv rd F0 pathOk g.own⌝ ∗
              ⌜CliIdInv rd F0 pathOk peer g⌝ ∗
              dirAt A.repAlloc (self + 40#64) g.peers ∗ R) := by
          rw [satisfies_pure_sepConj]
          exact ⟨⟨hrel, by rw [List.append_nil]; exact htr, hsenv, hfds_sf⟩, hme⟩
        exact Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hgoal
    · dsimp only [withFdsGe3Closed, idKeyPairPollSpecPlaced, withLsCodeRoLoaded] at hpan
      exact (not_satisfies_false_sepConj hpan).elim
    · dsimp only [withFdsGe3Closed, idKeyPairPollSpecPlaced, withLsCodeRoLoaded] at hex
      exact (not_satisfies_false_sepConj hex).elim
    · dsimp only [withFdsGe3Closed, idKeyPairPollSpecPlaced, withLsCodeRoLoaded] at hoom
      exact (not_satisfies_false_sepConj hoom).elim
  change subroutine_ok callerProg (0#64 + lsmpl.base 567) _
  rw [BitVec.zero_add]
  exact ls_subroutine_ok_rocl_of_block (callerProg := callerProg) (j := 567)
    h567_kit hCallerBlk (by decide) (by decide)

theorem cliIdSelfRegIdPoll_fds_rocl_placed_ok_of_poll [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost}
    {t1 t2 t3 t4 k1 k2 k3 k4 : Nat}
    {RegPollEnv : FsFiles → IdOwnPollGhostPlaced → List AllocEvent → Prop}
    {senv : IdentitySelfStoreBudgetEnv
      (cliIdSelfSpecFullPlaced A.repAlloc rd F0 pathOk peer
        (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) k1 k2 k3 k4)}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hRegEnv : ∀ fut out self (g : IdGhost) evs,
      RegPollEnv F0 ⟨fut, out, self, g.own⟩ evs → senv.regIdPollEnv g evs)
    (h568 : subroutine_ok (lsProg_568 H) (lsmpl.base 568)
      (withFdsGe3Closed (idRegIdPollSpecPlaced rd pathOk A lim RegPollEnv k4)))
    (hCallerBlk : callerBlk < 619 := by decide) :
    let skit := cliIdSelfSpecFullPlaced A.repAlloc rd F0 pathOk peer
      (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) k1 k2 k3 k4
    subroutine_ok callerProg (0#64 + skit.regIdPollOff)
      (withLsRoCl lsmpl (kitRegIdPollPlacedSpecI M A lim skit senv true)) := by
  intro skit
  have h568_kit : subroutine_ok (lsProg_568 H) (lsmpl.base 568)
      (withLsCodeRoLoaded lsmpl (kitRegIdPollPlacedSpecI M A lim skit senv true)) := by
    refine subroutine_ok_outcome_intro fun ⟨fut, out, self, g, st⟩ R s0 hpc hrun hpre hsp => ?_
    change IdGhost at g
    dsimp only [withLsCodeRoLoaded, kitRegIdPollPlacedSpecI, withLsLogOff,
      kitRegIdPollSpecE, kitRegIdPollSpec, withEnvPre,
      skit, cliIdSelfSpecFullPlaced,
      cliIdStoreSpecFullPlaced, cliIdStoreSpecFull, cliIdStoreAtFull,
      cliIdentityStoreSpec, cliIdStoreAt] at hpre
    have hpre' : s0.mem ⊨
        ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
        (⌜s0.fs.files = F0 ∧ FdsGe3Closed s0.fs⌝ ∗
        (⌜s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
          FitsEnv M lim st (senv.regIdPollEnv g)⌝ ∗
        (⌜CliIdOwnInv rd F0 pathOk g.own⌝ ∗
        (⌜CliIdInv rd F0 pathOk peer g⌝ ∗
        (idOwnFutBoxAt fut self 0#8 ∗ dirAt A.repAlloc self g.own ∗
          memRegion out 48 ∗ A.pool lim st s0 ∗
          stackAt s0.sp k4 ∗
          (dirAt A.repAlloc (self + 40#64) g.peers ∗ lsLogOff ∗ R)))))) :=
      Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hpre
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hcrl, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨⟨hfiles, hfds0⟩, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨⟨hx0, hx8, hfit⟩, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hown, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hinv, hspatial⟩ := hpre'
    let frameRegCore : SepProp :=
      ⌜CliIdOwnInv rd F0 pathOk g.own⌝ ∗
      ⌜CliIdInv rd F0 pathOk peer g⌝ ∗
      dirAt A.repAlloc (self + 40#64) g.peers ∗ lsLogOff
    have hfit_hop :
        FitsEnv M lim st (RegPollEnv s0.fs.files ⟨fut, out, self, g.own⟩) := fun evs hm => by
      rw [hfiles] at hm
      exact hfit evs (hRegEnv fut out self g evs hm)
    have hhop_pure :
        s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
          g.own.path.length < 2 ^ 32 ∧
          pathOk (pathOf g.own.path (utf8 "registration-id")) ∧
          FitsEnv M lim st (RegPollEnv s0.fs.files ⟨fut, out, self, g.own⟩) :=
      ⟨hx0, hx8, hown.ownPathLt, hown.regPathOk, hfit_hop⟩
    have hm_hop :
        s0.mem ⊨
          (withFdsGe3Closed (idRegIdPollSpecPlaced rd pathOk A lim RegPollEnv k4)).pre
            (⟨fut, out, self, g.own⟩, st) s0 ∗
          (frameRegCore ∗ R) := by
      dsimp only [withFdsGe3Closed, idRegIdPollSpecPlaced, withLsCodeRoLoaded, frameRegCore,
        idOwnFutBoxAtPlaced, idOwnFutBoxAt] at hspatial ⊢
      have h1 : s0.mem ⊨
          ⌜FdsGe3Closed s0.fs⌝ ∗
          (⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
          (⌜s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
            g.own.path.length < 2 ^ 32 ∧
            pathOk (pathOf g.own.path (utf8 "registration-id")) ∧
            FitsEnv M lim st (RegPollEnv s0.fs.files ⟨fut, out, self, g.own⟩)⌝ ∗
          (⌜CliIdOwnInv rd F0 pathOk g.own⌝ ∗
          (⌜CliIdInv rd F0 pathOk peer g⌝ ∗
          (idOwnFutBoxAt fut self 0#8 ∗ dirAt A.repAlloc self g.own ∗
            memRegion out 48 ∗ A.pool lim st s0 ∗
            stackAt s0.sp k4 ∗
            (dirAt A.repAlloc (self + 40#64) g.peers ∗ lsLogOff ∗ R)))))) := by
        rw [satisfies_pure_sepConj]; refine ⟨hfds0, ?_⟩
        rw [satisfies_pure_sepConj]; refine ⟨hcrl, ?_⟩
        rw [satisfies_pure_sepConj]; refine ⟨hhop_pure, ?_⟩
        rw [satisfies_pure_sepConj]; refine ⟨hown, ?_⟩
        rw [satisfies_pure_sepConj]
        dsimp only [idOwnFutBoxAt]
        exact ⟨hinv, hspatial⟩
      dsimp only [idOwnFutBoxAt, CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff,
        CryptoVerification.LibsignalTripleRatchet.lsLogOff] at h1 ⊢
      exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) h1
    refine h568.mono_outcome (⟨fut, out, self, g.own⟩, st) (frameRegCore ∗ R)
      s0 hpc hrun hm_hop hsp ?_
    rintro sf (⟨hret, hcc, hpost0⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩)
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [withFdsGe3Closed] at hpost0
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpost0
      obtain ⟨hfds_sf, hpost⟩ := hpost0
      dsimp only [idRegIdPollSpecPlaced, withLsCodeRoLoaded, frameRegCore] at hpost
      simp_rw [idRegIdOutAtPlaced_eq_local] at hpost
      simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
        satisfies_pure_sepConj] at hpost
      obtain ⟨evs, ans0, ⟨hans0, htr, hevs⟩, hm⟩ := hpost
      rw [hfiles, IdGhost.regId_mk_own] at hans0
      rw [hfiles] at hevs
      have hsenv : senv.regIdPollEnv g evs := hRegEnv fut out self g evs hevs
      dsimp only [withLsCodeRoLoaded, kitRegIdPollPlacedSpecI, withLsLogOff,
        kitRegIdPollSpecE, kitRegIdPollSpec, withEnvPre,
        skit, cliIdSelfSpecFullPlaced,
        cliIdStoreSpecFullPlaced, cliIdStoreSpecFull, cliIdStoreAtFull,
        cliIdentityStoreSpec, cliIdStoreAt]
      simp only [sepExists_sepConj_left, satisfies_sepExists]
      cases ans0 with
      | ok reg =>
        have hrel : cliRegIdRel (E := CliSelfSpeErr) rd F0 g (.ok reg) :=
          (cliRegIdRel_ok_iff (E := CliSelfSpeErr) rd F0 g reg).2 hans0.symm
        refine ⟨.ok reg, evs, ?_⟩
        dsimp only [regIdPollOutAt, idRegIdOutAt, idOwnFutBoxAtPlaced, idOwnFutBoxAt] at hm ⊢
        have hgoal : sf.mem ⊨
            ⌜cliRegIdRel (E := CliSelfSpeErr) rd F0 g (.ok reg) ∧
              sf.trace = s0.trace ++ [] ∧
              senv.regIdPollEnv g evs ∧ FdsGe3Closed sf.fs⌝ ∗
            (((out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ ((out + 8#64) ↦₃₂ reg) ∗
                memRegion (out + 12#64) 36) ∗
              idOwnFutBoxAt fut self 1#8 ∗
              dirAt A.repAlloc self g.own ∗ A.pool lim (M.stepEvents evs st) sf ∗
              stackAt s0.sp k4 ∗
              ⌜CliIdOwnInv rd F0 pathOk g.own⌝ ∗
              ⌜CliIdInv rd F0 pathOk peer g⌝ ∗
              dirAt A.repAlloc (self + 40#64) g.peers ∗ lsLogOff ∗ R) := by
          dsimp only [idOwnFutBoxAt]
          rw [satisfies_pure_sepConj]
          exact ⟨⟨hrel, by rw [List.append_nil]; exact htr, hsenv, hfds_sf⟩, hm⟩
        dsimp only [idOwnFutBoxAt] at hgoal
        exact Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hgoal
      | error u =>
        cases u
        have herr_ent :
            idRegIdOutAt A.repAlloc out (.error ()) ⊢
              ∃∗ e : skit.RegIdErr, regIdPollOutAt skit out (.error e) :=
          (cliIdentitySelf_regIdErr_layout_placed A.repAlloc F0
            (peer := peer) (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4)
            (k1 := k1) (k2 := k2) (k3 := k3) (k4 := k4) out).2
        have hm' := Satisfies.mono (sepConj_mono_left herr_ent) hm
        rw [sepExists_sepConj_left, satisfies_sepExists] at hm'
        dsimp only [skit, cliIdSelfSpecFullPlaced, cliIdentitySelfSpecPlaced, cliIdentitySelfSpec,
          regIdPollOutAt, idOwnFutBoxAtPlaced, idOwnFutBoxAt] at hm' ⊢
        obtain ⟨e, hme⟩ := hm'
        have hrel : cliRegIdRel rd F0 g (.error e) :=
          (cliRegIdRel_error_iff rd F0 g e).2 hans0.symm
        refine ⟨.error e, evs, ?_⟩
        dsimp only [regIdPollOutAt, cliIdentitySelfSpecPlaced, cliIdentitySelfSpec]
        have hgoal : sf.mem ⊨
            ⌜cliRegIdRel rd F0 g (.error e) ∧
              sf.trace = s0.trace ++ [] ∧
              senv.regIdPollEnv g evs ∧ FdsGe3Closed sf.fs⌝ ∗
            (speErrAt (cliSelfSpeErrSpec A.repAlloc) out e ∗
              ((fut ↦₆₄ self) ∗ ((fut + 8#64) ↦₈ 1#8) ∗ memRegion (fut + 9#64) 7) ∗
              dirAt A.repAlloc self g.own ∗ A.pool lim (M.stepEvents evs st) sf ∗
              stackAt s0.sp k4 ∗
              ⌜CliIdOwnInv rd F0 pathOk g.own⌝ ∗
              ⌜CliIdInv rd F0 pathOk peer g⌝ ∗
              dirAt A.repAlloc (self + 40#64) g.peers ∗ lsLogOff ∗ R) := by
          rw [satisfies_pure_sepConj]
          exact ⟨⟨hrel, by rw [List.append_nil]; exact htr, hsenv, hfds_sf⟩, hme⟩
        exact Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hgoal
    · dsimp only [withFdsGe3Closed, idRegIdPollSpecPlaced, withLsCodeRoLoaded] at hpan
      exact (not_satisfies_false_sepConj hpan).elim
    · dsimp only [withFdsGe3Closed, idRegIdPollSpecPlaced, withLsCodeRoLoaded] at hex
      exact (not_satisfies_false_sepConj hex).elim
    · dsimp only [withFdsGe3Closed, idRegIdPollSpecPlaced, withLsCodeRoLoaded] at hoom
      exact (not_satisfies_false_sepConj hoom).elim
  change subroutine_ok callerProg (0#64 + lsmpl.base 568) _
  rw [BitVec.zero_add]
  exact ls_subroutine_ok_rocl_of_block (callerProg := callerProg) (j := 568)
    h568_kit hCallerBlk (by decide) (by decide)

/-- Assemble `IdentitySelfStoreKitPlacedOkIFds` for `cliIdSelfSpecFullPlaced` from
`AllocContractsFsPlaced` and the Block `567`/`568` poll contracts. -/
theorem cliIdSelfKitPlacedOkIFds_full_of_polls [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost}
    {t1 t2 t3 t4 k1 k2 k3 k4 : Nat}
    {KpPollEnv : FsFiles → IdOwnPollGhostPlaced → List AllocEvent → Prop}
    {RegPollEnv : FsFiles → IdOwnPollGhostPlaced → List AllocEvent → Prop}
    (senv : IdentitySelfStoreBudgetEnv
      (cliIdSelfSpecFullPlaced A.repAlloc rd F0 pathOk peer
        (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) k1 k2 k3 k4))
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hFs : AllocContractsFsPlaced A lim H)
    (hk1 : 32 + extHookStack ≤ k1)
    (hk3 : 32 + extHookStack ≤ k3)
    (hKpEnv : ∀ fut out self (g : IdGhost) evs,
      KpPollEnv F0 ⟨fut, out, self, g.own⟩ evs → senv.kpPollEnv g evs)
    (hRegEnv : ∀ fut out self (g : IdGhost) evs,
      RegPollEnv F0 ⟨fut, out, self, g.own⟩ evs → senv.regIdPollEnv g evs)
    (h567 : subroutine_ok (lsProg_567 H) (lsmpl.base 567)
      (withFdsGe3Closed (idKeyPairPollSpecPlaced rd pathOk A lim KpPollEnv k2)))
    (h568 : subroutine_ok (lsProg_568 H) (lsmpl.base 568)
      (withFdsGe3Closed (idRegIdPollSpecPlaced rd pathOk A lim RegPollEnv k4))) :
    IdentitySelfStoreKitPlacedOkIFds A lim
      (cliIdStoreSpecFullPlaced A.repAlloc rd F0 pathOk peer t1 t2 t3 t4)
      (cliIdSelfSpecFullPlaced A.repAlloc rd F0 pathOk peer
        (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) k1 k2 k3 k4)
      senv H where
  kpShim hblk := cliIdSelfKpShim_fds_rocl_placed_ok hFs hk1 hblk
  kpPoll hblk := cliIdSelfKpPoll_fds_rocl_placed_ok_of_poll hKpEnv h567 hblk
  kpFutDrop hblk := by
    change subroutine_ok _ (0#64 + lsDropOffPlaced) _
    rw [lsDropOffPlaced_eq hDropNz]
    exact cliIdFutDrop_fds_rocl_placed_ok hblk
  regIdShim hblk := cliIdSelfRegIdShim_fds_rocl_placed_ok hFs hk3 hblk
  regIdPoll hblk := cliIdSelfRegIdPoll_fds_rocl_placed_ok_of_poll hRegEnv h568 hblk
  regIdFutDrop hblk := by
    change subroutine_ok _ (0#64 + lsDropOffPlaced) _
    rw [lsDropOffPlaced_eq hDropNz]
    exact cliIdFutDrop_fds_rocl_placed_ok hblk

/-! ## Full-invariant `IdentityStoreKitPlacedOkIFds` lift -/

def fullIdKitBudgetEnv [LibsignalPlacement] {A : RustAlloc}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop}
    {peer : AddrGhost} {t1 t2 t3 t4 : Nat}
    (baseEnv : IdentityStoreBudgetEnv
      (cliIdentityKitSpecPlaced A rd F0 pathOk peer t1 t2 t3 t4 cliIdentityVtSym)) :
    IdentityStoreBudgetEnv
      (cliIdStoreSpecFullPlaced A rd F0 pathOk peer t1 t2 t3 t4) where
  trustPollEnv := baseEnv.trustPollEnv
  savePollEnv := baseEnv.savePollEnv

private theorem saveUpd_own_placed (rd : ReadRule) (F0 : FsFiles) (g : IdGhost)
    (addr : AddrVal) (key : IdentityKey) :
    (IdGhost.saveUpd rd F0 g addr key).own = g.own := by
  unfold IdGhost.saveUpd; cases IdGhost.peer rd F0 g addr <;> rfl

/-- Lift `IdentityStoreKitPlacedOkIFds` from `cliIdentityKitSpecPlaced` to
`cliIdStoreSpecFullPlaced` by framing `CliIdOwnInv`. -/
theorem cliIdKitPlacedOkIFds_full [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop}
    {peer : AddrGhost} {t1 t2 t3 t4 : Nat}
    {baseEnv : IdentityStoreBudgetEnv
      (cliIdentityKitSpecPlaced A.repAlloc rd F0 pathOk peer t1 t2 t3 t4 cliIdentityVtSym)}
    (hBase : IdentityStoreKitPlacedOkIFds A lim
      (cliIdentityKitSpecPlaced A.repAlloc rd F0 pathOk peer t1 t2 t3 t4 cliIdentityVtSym)
      baseEnv H) :
    IdentityStoreKitPlacedOkIFds A lim
      (cliIdStoreSpecFullPlaced A.repAlloc rd F0 pathOk peer t1 t2 t3 t4)
      (fullIdKitBudgetEnv baseEnv) H where
  trustShim := hBase.trustShim
  trustFutDrop := hBase.trustFutDrop
  saveShim := hBase.saveShim
  saveFutDrop := hBase.saveFutDrop
  trustPoll hblk := by
    refine subroutine_ok_outcome_intro fun ⟨x, d, self, g, st⟩ R s0 hpc hrun hpre hsp => ?_
    change IdGhost at g
    dsimp only [withLsRoCl, kitTrustPollPlacedSpecI, withLsLogOff, kitTrustPollPlacedSpecE,
      kitTrustPollPlacedSpec, withEnvPre, cliIdentityStoreSpec, cliIdStoreSpecFullPlaced,
      cliIdStoreSpecFull, cliIdStoreAtFull, fullIdKitBudgetEnv] at hpre
    have hpre' : s0.mem ⊨ (withLsRoCl lsmpl (kitTrustPollPlacedSpecI M A lim
        (cliIdentityKitSpecPlaced A.repAlloc rd F0 pathOk peer t1 t2 t3 t4 cliIdentityVtSym)
        baseEnv true)).pre (x, d, self, g, st) s0 ∗ (⌜CliIdOwnInv rd F0 pathOk g.own⌝ ∗ R) := by
      dsimp only [withLsRoCl, kitTrustPollPlacedSpecI, withLsLogOff, kitTrustPollPlacedSpecE,
        kitTrustPollPlacedSpec, withEnvPre, cliIdentityKitSpecPlaced, cliIdentityStoreSpec]
      exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hpre
    refine (hBase.trustPoll hblk).mono_outcome (x, d, self, g, st)
      (⌜CliIdOwnInv rd F0 pathOk g.own⌝ ∗ R) s0 hpc hrun hpre' hsp ?_
    rintro sf (⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩)
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [withLsRoCl, kitTrustPollPlacedSpecI, withLsLogOff, kitTrustPollPlacedSpecE,
        kitTrustPollPlacedSpec, withEnvPre, cliIdentityKitSpecPlaced, cliIdentityStoreSpec,
        cliIdStoreSpecFullPlaced, cliIdStoreSpecFull, cliIdStoreAtFull, fullIdKitBudgetEnv] at hpost ⊢
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost ⊢
      obtain ⟨ans, evs, hm⟩ := hpost
      exact ⟨ans, evs, Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hm⟩
    · dsimp only [withLsRoCl, kitTrustPollPlacedSpecI, withLsLogOff, kitTrustPollPlacedSpecE,
        kitTrustPollPlacedSpec, withEnvPre] at hpan
      exact (not_satisfies_false_sepConj hpan).elim
    · dsimp only [withLsRoCl, kitTrustPollPlacedSpecI, withLsLogOff, kitTrustPollPlacedSpecE,
        kitTrustPollPlacedSpec, withEnvPre] at hex
      exact (not_satisfies_false_sepConj hex).elim
    · dsimp only [withLsRoCl, kitTrustPollPlacedSpecI, withLsLogOff, kitTrustPollPlacedSpecE,
        kitTrustPollPlacedSpec, withEnvPre] at hoom
      exact (not_satisfies_false_sepConj hoom).elim
  savePoll hblk := by
    refine subroutine_ok_outcome_intro fun ⟨x, self, g, st⟩ R s0 hpc hrun hpre hsp => ?_
    change IdGhost at g
    dsimp only [withLsRoCl, kitSavePollPlacedSpecI, withLsLogOff, kitSavePollPlacedSpecE,
      kitSavePollPlacedSpec, withEnvPre, cliIdentityStoreSpec, cliIdStoreSpecFullPlaced,
      cliIdStoreSpecFull, cliIdStoreAtFull, fullIdKitBudgetEnv] at hpre
    have hpre' : s0.mem ⊨ (withLsRoCl lsmpl (kitSavePollPlacedSpecI M A lim
        (cliIdentityKitSpecPlaced A.repAlloc rd F0 pathOk peer t1 t2 t3 t4 cliIdentityVtSym)
        baseEnv true)).pre (x, self, g, st) s0 ∗ (⌜CliIdOwnInv rd F0 pathOk g.own⌝ ∗ R) := by
      dsimp only [withLsRoCl, kitSavePollPlacedSpecI, withLsLogOff, kitSavePollPlacedSpecE,
        kitSavePollPlacedSpec, withEnvPre, cliIdentityKitSpecPlaced, cliIdentityStoreSpec]
      exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hpre
    refine (hBase.savePoll hblk).mono_outcome (x, self, g, st)
      (⌜CliIdOwnInv rd F0 pathOk g.own⌝ ∗ R) s0 hpc hrun hpre' hsp ?_
    rintro sf (⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩)
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [withLsRoCl, kitSavePollPlacedSpecI, withLsLogOff, kitSavePollPlacedSpecE,
        kitSavePollPlacedSpec, withEnvPre, cliIdentityKitSpecPlaced, cliIdentityStoreSpec,
        cliIdStoreSpecFullPlaced, cliIdStoreSpecFull, cliIdStoreAtFull, fullIdKitBudgetEnv] at hpost ⊢
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost ⊢
      obtain ⟨ans, evs, hm⟩ := hpost
      rw [saveUpd_own_placed]
      exact ⟨ans, evs, Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hm⟩
    · dsimp only [withLsRoCl, kitSavePollPlacedSpecI, withLsLogOff, kitSavePollPlacedSpecE,
        kitSavePollPlacedSpec, withEnvPre] at hpan
      exact (not_satisfies_false_sepConj hpan).elim
    · dsimp only [withLsRoCl, kitSavePollPlacedSpecI, withLsLogOff, kitSavePollPlacedSpecE,
        kitSavePollPlacedSpec, withEnvPre] at hex
      exact (not_satisfies_false_sepConj hex).elim
    · dsimp only [withLsRoCl, kitSavePollPlacedSpecI, withLsLogOff, kitSavePollPlacedSpecE,
        kitSavePollPlacedSpec, withEnvPre] at hoom
      exact (not_satisfies_false_sepConj hoom).elim

/-! ## `FsAtFds` and `writeFileHook` preservation -/

theorem fsAt_cliIdFullKit_of_fdsGe3Closed [LibsignalPlacement] {A : RustAlloc}
    {envOk : FsFiles → Prop} {rd : ReadRule} {F0 : FsFiles}
    {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost}
    {t1 t2 t3 t4 : Nat} {P : Program} {s : State}
    (hP : TraceFsSound P) (henv : envOk F0) (hfiles : s.fs.files = F0) (hfds : FdsGe3Closed s.fs) :
    FsAtFds envOk
      (cliIdStoreSpecFullPlaced A rd F0 pathOk peer t1 t2 t3 t4).fdsOk
      (cliIdStoreSpecFullPlaced A rd F0 pathOk peer t1 t2 t3 t4).Quiet P s :=
  .inr ⟨cliIdStoreSpecFullPlaced_quiet (A := A) (rd := rd) (F0 := F0) (pathOk := pathOk)
    (peer := peer) (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4),
    hP, hfiles.symm ▸ henv, hfds⟩

theorem cliIdSelfSpecFullPlaced_writeFileHook [LibsignalPlacement] {A : RustAlloc}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost}
    {t1 t2 t3 t4 k1 k2 k3 k4 : Nat} {s : State}
    (hfds : (cliIdSelfSpecFullPlaced A rd F0 pathOk peer
      (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) k1 k2 k3 k4).fdsOk s.fs) :
    (cliIdSelfSpecFullPlaced A rd F0 pathOk peer
      (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) k1 k2 k3 k4).fdsOk (writeFileHook s).fs :=
  fdsGe3Closed_writeFileHook hfds

theorem hookOk_writeFileHook_withFdsGe3Closed_self {α : Type} {S : Spec α}
    (h : HookOk writeFileHook S) :
    HookOk writeFileHook (withFdsGe3Closed S) :=
  hookOk_withFdsGe3Closed_writeFileHook h

end LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentitySelfKitFdsPlacedBudget
