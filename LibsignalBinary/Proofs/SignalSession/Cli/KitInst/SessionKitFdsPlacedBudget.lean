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
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Placed Budgeted `SessionStoreSpec` with Closed-FD Invariant

Establishes `SessionOnlyKitPlacedOkSEFds` (`fds = true`) on `cliSessionKitSpecPlaced`
(`SessionFiles`), shim `Spec.keepsFs` contracts on Blocks `604` and `605`, `withFdsGe3Closed`
poll lifting on Blocks `569` and `570` (both canonical and `SeqFree` envelopes), and
`writeFileHook` preservation of `FdsGe3Closed`.
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitFdsPlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSessionApi (SessionRecord)
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.E2E.InMem.SessionStoreImpl (toRecordGhost)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.E2E.Record.Serialization (CanonRecord)
open CryptoVerification.LibsignalTripleRatchet (extHookStack withStack)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost protocolAddressAt)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal sessionRecordAt)
open CryptoVerification.LibsignalPublicApi.StoreSession (StorePollCall StoreShimCall)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles LibsignalCodeRoLoaded LoadPollCall LoadShimCall SessionStoreSpec TraceFsSound
   extract_withLsCodeRoLoaded loadPollPlacedOutAtS ls_subroutine_ok_rocl_of_block sepWP_seq_lscro
   storePollPlacedOutAt withEnvPre withLsCodeRoLoaded withLsRoCl)
open LibsignalBinary.Proofs.PublicApi.StoreKit.FsFds (FsAtFds)
open CryptoVerification.SignalSession
  (lsDropOffPlaced_eq lsRustAllocSymCli lsRustNoAllocShimSymCli writeFileHook)
open CryptoVerification.SignalSession.Cli
  (DirGhost ReadRule SessFileWf SessLoadAns addressText dirAt pathOf sessLoadBoxAt
   sessLoadFutVtSym sessLoadOutAt sessStoreBoxAt sessStoreFutVtSym)
open CryptoVerification.SignalSession.Cli.Placed
  (blkPC_604 blkPC_605 blkPl_604 blkPl_605 lsProg_569 lsProg_570 lsProg_604 lsProg_605)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon
  (ls_transfer_lscro satisfies_lscro_pre)
open CryptoVerification.SignalSession.Cli.Store.LoadShim (sessLoadShimStackPlaced)
open CryptoVerification.SignalSession.Cli.Store.StoreShim (sessStoreShimStackPlaced)
open CryptoVerification.SignalSession.Cli.Store.StorePoll.Helpers
  (canonRecord_of_satisfies_sessionRecordAt)
open CryptoVerification.SignalSession.Cli.KitInst
  (CliSessInv cliIdentityVtRoSym cliSessStoreAt cliSessionKitSpecPlaced cliSessionStoreSpec
   cliSessionStoreSpec_storeUpdate_inv cliSessionVtRoSym)
open CryptoVerification.SignalSession.Cli.KitInst.SessKit
  (cliSessionKitSpecPlaced_quiet loadShimNeedPlaced storeShimNeedPlaced)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents
   RustCliAllocBudget RustLayoutOk SeqEnv rustAllocEvents)
open LibsignalBinary.Heap.IfaceBudgetLemmas (rustCliAllocNoOomSpecWithStack)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (rustAllocNoOomSpecWithStack)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (BoxAllocEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget
  (SessionStoreBudgetEnv kitLoadShimSpec kitStoreShimSpec)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
  (SessionOnlyKitPlacedOkSEFds kitLoadPollPlacedSpecS kitLoadPollPlacedSpecSE
   kitStorePollPlacedSpec kitStorePollPlacedSpecE)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget (SerializeEnvX)
open LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit (RecordSerializeSeqFreeEnv)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds
  (RecordGhostValid recordGhostValid_of_sessionRecordAt)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsFsPlaced sessLoadPollSpecPlaced sessLoadShimSpecPlaced sessStorePollSpecPlaced
   sessStoreShimSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget
  (allocNoOom_lscro_of_cli lift_stk_lscro_budget)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget.AllocContractsFsPlaced
  (toAllocContractsX)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPoll.LayoutPlacedBudget (CliLoadPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.StorePoll.LayoutBudget (CliStorePollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitFdsPilotPlacedBudget
  (cliIdFutDrop_fds_rocl_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
  (RecordSerializeSeqFreeCellsEnv SerializeCanonEnvX SerializeCanonSeqFreeValidEnv
   cliSessionKitBudgetEnv cliSessionKitLoadPollEnv cliSessionKitStorePollEnv
   serializeEnvX_eq_canon)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed fdsGe3Closed_writeFileHook hookOk_withFdsGe3Closed_writeFileHook withFdsGe3Closed)

@[simp]
theorem cliSessionKitSpecPlaced_fdsOk [LibsignalPlacement] (A : RustAlloc)
    (rd : ReadRule) (F0 : FsFiles) (pathOk : List (BitVec 8) → Prop)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (peer : AddrGhost)
    (s1 s2 s3 s4 : Nat) (vtSym idVtSym : String) (fs : FsState) :
    (cliSessionKitSpecPlaced A rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym idVtSym).fdsOk fs =
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

private theorem stackAt_sessLoadShim_placed (sp : BitVec 64) :
    stackAt sp sessLoadShimStackPlaced =
      stackAt (sp - 32#64) extHookStack ∗ cells (sp - 32#64) 4 :=
  ProofLib.stackAt_split_cells sp extHookStack 4 (by decide)

private theorem memRegion_24_box_placed (p : BitVec 64) :
    memRegion p 24 =
      (∃∗ b0 : BitVec 8, ∃∗ u1 : BitVec 64, ∃∗ u0 : BitVec 64,
        (p ↦₆₄ u0) ∗ ((p + 8#64) ↦₆₄ u1) ∗ ((p + 16#64) ↦₈ b0) ∗
        memRegion (p + 17#64) 7) := by
  rw [memRegion_split p 8 16 (by decide),
    memRegion_split (p + 8#64) 8 8 (by decide),
    memRegion_split (p + 8#64 + 8#64) 1 7 (by decide),
    memRegion_one, ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

/-- Block `604` (`sessLoadShim`) preserves `fs` under `AllocContractsFsPlaced`. -/
theorem sessLoadShim_keepsFs_placed_fixed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFs : AllocContractsFsPlaced A lim H) :
    subroutine_ok (lsProg_604 H) (lsmpl.base 604)
      (sessLoadShimSpecPlaced A lim sessLoadShimStackPlaced).keepsFs := by
  unfold sessLoadShimSpecPlaced Spec.keepsFs withLsCodeRoLoaded
  simp only [sessLoadBoxAt, stackAt_sessLoadShim_placed]
  cells_unfold
  dsimp only [lsProg_604]
  change subroutine_ok ((blkPC_604).rebase (blkPl_604).base H) (blkPl_604).base _
  wp_init xs s0
  obtain ⟨⟨self, addrA⟩, st⟩ := xs
  dsimp only
  have hcrl0 : LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  have hfit0 : FitsEnv M lim st (BoxAllocEnv 24) := by assumption
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hlay : RustLayoutOk 24 8 := ⟨⟨by decide, hpow8, by decide⟩, by decide⟩
  have hbev : BoxAllocEnv 24 (rustAllocEvents 24 8) := Or.inr ⟨by decide, rfl⟩
  have hfit : FitsEvents M lim st (rustAllocEvents 24 8) := hfit0 _ hbev
  have halloc := allocNoOom_lscro_of_cli
    (callerProg := (blkPC_604).rebase (blkPl_604).base H) (toAllocContractsX hFs)
  dsimp only [withLsCodeRoLoaded, rustAllocNoOomSpecWithStack,
    rustCliAllocNoOomSpecWithStack] at halloc
  apply sepWP_seq_lscro (mid := lsρ lsRustNoAllocShimSymCli) hcrl0
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSymCli)
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by wp_norm_lhs)
  intro hcrl1
  wp_call_lscro
    (shim_keepsFs_lscro_of_fs (callerProg := (blkPC_604).rebase (blkPl_604).base H) hFs
      (stk := extHookStack))
    hcrl1 ()
  have hfs_shim : sf.fs = s0.fs := by assumption
  refine ProofLib.SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  apply sepWP_seq_lscro (mid := lsρ lsRustAllocSymCli) hcrl_sf
  wp_steps_sync_pool (lsρ lsRustAllocSymCli)
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by wp_norm_lhs)
  intro ⟨hcl2, hro2⟩
  wp_call halloc (24, 8, st)
  have hacp : AllocCallPreserved sf sf_1 := by assumption
  have hfs_alloc : sf_1.fs = s0.fs := hacp.1.trans hfs_shim
  have htr_alloc : sf_1.trace = sf.trace := hacp.2.1
  have htr_s0 : sf_1.trace = s0.trace := hacp.2.1.trans (by assumption)
  have hne0 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq0 : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hne0
  simp only [memRegion_24_box_placed, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun b0 => SepWP.exists_elim fun u1 =>
    SepWP.exists_elim fun u0 => ?_
  wp_steps_sync_pool (s0.readReg64 Reg.lr)
  wp_done

theorem sessLoadShim_keepsFs_placed_ok_of_deps [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {stk : Nat}
    (hFs : AllocContractsFsPlaced A lim H)
    (hstk : 0x20 + extHookStack ≤ stk) :
    subroutine_ok (lsProg_604 H) (lsmpl.base 604)
      (sessLoadShimSpecPlaced A lim stk).keepsFs :=
  lift_stk_lscro_budget (pl := lsmpl) (F := fun k => (sessLoadShimSpecPlaced A lim k).keepsFs)
    (P := fun (x, st) s =>
      ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x1 = x.addrA ∧
        FitsEnv M lim st (BoxAllocEnv 24)⌝ ∗ A.pool lim st s)
    (Q := fun (x, st) s0 sf =>
      ⌜sf.fs = s0.fs⌝ ∗
      ∃∗ evs : List AllocEvent,
        ⌜sf.readReg64 .x1 = lsρ sessLoadFutVtSym ∧ sf.readReg64 .x0 ≠ 0#64 ∧
          (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace ∧
          BoxAllocEnv 24 evs⌝ ∗
          A.live (sf.readReg64 .x0) 24 8 ∗
          sessLoadBoxAt (sf.readReg64 .x0) x.self x.addrA 0#8 ∗
          A.pool lim (M.stepEvents evs st) sf)
    (sessLoadShim_keepsFs_placed_fixed_ok hFs)
    (by dsimp [sessLoadShimStackPlaced]; omega)
    (by
      intro ⟨x, st⟩ s k
      dsimp only [Spec.keepsFs, sessLoadShimSpecPlaced, withLsCodeRoLoaded]
      sep_ac_rfl)
    (by
      intro ⟨x, st⟩ s0 sf k
      simp only [Spec.keepsFs, sessLoadShimSpecPlaced, withLsCodeRoLoaded,
        sepExists_sepConj_left, sepExists_sepConj_right]
      exact sepExists_congr fun _ => by sep_ac_rfl)

private theorem stackAt_sessStoreShim_placed (sp : BitVec 64) :
    stackAt sp sessStoreShimStackPlaced =
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

/-- Block `605` (`sessStoreShim`) preserves `fs` under `AllocContractsFsPlaced`. -/
theorem sessStoreShim_keepsFs_placed_fixed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFs : AllocContractsFsPlaced A lim H) :
    subroutine_ok (lsProg_605 H) (lsmpl.base 605)
      (sessStoreShimSpecPlaced A lim sessStoreShimStackPlaced).keepsFs := by
  unfold sessStoreShimSpecPlaced Spec.keepsFs withLsCodeRoLoaded
  simp only [sessStoreBoxAt, stackAt_sessStoreShim_placed]
  cells_unfold
  dsimp only [lsProg_605]
  change subroutine_ok ((blkPC_605).rebase (blkPl_605).base H) (blkPl_605).base _
  wp_init xs s0
  obtain ⟨⟨self, addrA, recA⟩, st⟩ := xs
  dsimp only
  have hcrl0 : LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  have hfit0 : FitsEnv M lim st (BoxAllocEnv 32) := by assumption
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hlay : RustLayoutOk 32 8 := ⟨⟨by decide, hpow8, by decide⟩, by decide⟩
  have hbev : BoxAllocEnv 32 (rustAllocEvents 32 8) := Or.inr ⟨by decide, rfl⟩
  have hfit : FitsEvents M lim st (rustAllocEvents 32 8) := hfit0 _ hbev
  have halloc := allocNoOom_lscro_of_cli
    (callerProg := (blkPC_605).rebase (blkPl_605).base H) (toAllocContractsX hFs)
  dsimp only [withLsCodeRoLoaded, rustAllocNoOomSpecWithStack,
    rustCliAllocNoOomSpecWithStack] at halloc
  apply sepWP_seq_lscro (mid := lsρ lsRustNoAllocShimSymCli) hcrl0
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSymCli)
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by wp_norm_lhs)
  intro hcrl1
  wp_call_lscro
    (shim_keepsFs_lscro_of_fs (callerProg := (blkPC_605).rebase (blkPl_605).base H) hFs
      (stk := extHookStack))
    hcrl1 ()
  have hfs_shim : sf.fs = s0.fs := by assumption
  refine ProofLib.SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  apply sepWP_seq_lscro (mid := lsρ lsRustAllocSymCli) hcrl_sf
  wp_steps_sync_pool (lsρ lsRustAllocSymCli)
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by wp_norm_lhs)
  intro ⟨hcl2, hro2⟩
  wp_call halloc (32, 8, st)
  have hacp : AllocCallPreserved sf sf_1 := by assumption
  have hfs_alloc : sf_1.fs = s0.fs := hacp.1.trans hfs_shim
  have htr_alloc : sf_1.trace = sf.trace := hacp.2.1
  have htr_s0 : sf_1.trace = s0.trace := hacp.2.1.trans (by assumption)
  have hne0 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq0 : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hne0
  simp only [memRegion_32_box_placed, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun b0 => SepWP.exists_elim fun u2 =>
    SepWP.exists_elim fun u1 => SepWP.exists_elim fun u0 => ?_
  wp_steps_sync_pool (s0.readReg64 Reg.lr)
  wp_done

theorem sessStoreShim_keepsFs_placed_ok_of_deps [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {stk : Nat}
    (hFs : AllocContractsFsPlaced A lim H)
    (hstk : 0x30 + extHookStack ≤ stk) :
    subroutine_ok (lsProg_605 H) (lsmpl.base 605)
      (sessStoreShimSpecPlaced A lim stk).keepsFs :=
  lift_stk_lscro_budget (pl := lsmpl) (F := fun k => (sessStoreShimSpecPlaced A lim k).keepsFs)
    (P := fun (x, st) s =>
      ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x1 = x.addrA ∧ s.readReg64 .x2 = x.recA ∧
        FitsEnv M lim st (BoxAllocEnv 32)⌝ ∗ A.pool lim st s)
    (Q := fun (x, st) s0 sf =>
      ⌜sf.fs = s0.fs⌝ ∗
      ∃∗ evs : List AllocEvent,
        ⌜sf.readReg64 .x1 = lsρ sessStoreFutVtSym ∧ sf.readReg64 .x0 ≠ 0#64 ∧
          (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace ∧
          BoxAllocEnv 32 evs⌝ ∗
          A.live (sf.readReg64 .x0) 32 8 ∗
          sessStoreBoxAt (sf.readReg64 .x0) x.self x.addrA x.recA 0#8 ∗
          A.pool lim (M.stepEvents evs st) sf)
    (sessStoreShim_keepsFs_placed_fixed_ok hFs)
    (by dsimp [sessStoreShimStackPlaced]; omega)
    (by
      intro ⟨x, st⟩ s k
      dsimp only [Spec.keepsFs, sessStoreShimSpecPlaced, withLsCodeRoLoaded]
      sep_ac_rfl)
    (by
      intro ⟨x, st⟩ s0 sf k
      simp only [Spec.keepsFs, sessStoreShimSpecPlaced, withLsCodeRoLoaded,
        sepExists_sepConj_left, sepExists_sepConj_right]
      exact sepExists_congr fun _ => by sep_ac_rfl)

end Shims

theorem cliSessLoadShim_fds_rocl_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost}
    {s1 s2 s3 s4 : Nat} {vtSym idVtSym : String}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hFs : AllocContractsFsPlaced A lim H)
    (hs1 : loadShimNeedPlaced ≤ s1) (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg
      (0#64 + (cliSessionKitSpecPlaced A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym
        idVtSym).loadShimOff)
      (withLsRoCl lsmpl
        (kitLoadShimSpec M A lim
          (cliSessionKitSpecPlaced A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym
            idVtSym) true)) := by
  have h604 := sessLoadShim_keepsFs_placed_ok_of_deps hFs hs1
  have h604_kit : subroutine_ok (lsProg_604 H) (lsmpl.base 604)
      (withLsCodeRoLoaded lsmpl
        (kitLoadShimSpec M A lim
          (cliSessionKitSpecPlaced A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym
            idVtSym) true)) := by
    refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
    obtain ⟨hcrl, hpre0⟩ := extract_withLsCodeRoLoaded hpre
    dsimp only [kitLoadShimSpec, cliSessionKitSpecPlaced, cliSessionStoreSpec] at hpre0
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre0
    rcases hpre0 with ⟨⟨hx0, hx1, hfit, hfds0⟩, hrest⟩
    have hpre' : s0.mem ⊨ ((sessLoadShimSpecPlaced A lim s1).keepsFs).pre (x, st) s0 ∗ R := by
      dsimp only [Spec.keepsFs]
      refine satisfies_lscro_pre hcrl ?_
      dsimp only [sessLoadShimSpecPlaced, withLsCodeRoLoaded]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hx0, hx1, hfit⟩, by simpa only [sepConj_assoc] using hrest⟩
    refine h604.mono_outcome (x, st) R s0 hpc hrun hpre' hsp ?_
    rintro sf (⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩)
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [Spec.keepsFs, sessLoadShimSpecPlaced, withLsCodeRoLoaded, kitLoadShimSpec,
        cliSessionKitSpecPlaced, cliSessionStoreSpec] at hq ⊢
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
    · dsimp only [Spec.keepsFs, sessLoadShimSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
    · dsimp only [Spec.keepsFs, sessLoadShimSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
    · dsimp only [Spec.keepsFs, sessLoadShimSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
  change subroutine_ok callerProg (0#64 + lsmpl.base 604) _
  rw [BitVec.zero_add]
  exact ls_subroutine_ok_rocl_of_block (callerProg := callerProg) (j := 604)
    h604_kit hblk (by decide) (by decide)

theorem cliSessStoreShim_fds_rocl_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost}
    {s1 s2 s3 s4 : Nat} {vtSym idVtSym : String}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hFs : AllocContractsFsPlaced A lim H)
    (hs3 : storeShimNeedPlaced ≤ s3) (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg
      (0#64 + (cliSessionKitSpecPlaced A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym
        idVtSym).storeShimOff)
      (withLsRoCl lsmpl
        (kitStoreShimSpec M A lim
          (cliSessionKitSpecPlaced A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym
            idVtSym) true)) := by
  have h605 := sessStoreShim_keepsFs_placed_ok_of_deps hFs hs3
  have h605_kit : subroutine_ok (lsProg_605 H) (lsmpl.base 605)
      (withLsCodeRoLoaded lsmpl
        (kitStoreShimSpec M A lim
          (cliSessionKitSpecPlaced A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym
            idVtSym) true)) := by
    refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
    obtain ⟨hcrl, hpre0⟩ := extract_withLsCodeRoLoaded hpre
    dsimp only [kitStoreShimSpec, cliSessionKitSpecPlaced, cliSessionStoreSpec] at hpre0
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre0
    rcases hpre0 with ⟨⟨hx0, hx1, hx2, hfit, hfds0⟩, hrest⟩
    have hpre' : s0.mem ⊨ ((sessStoreShimSpecPlaced A lim s3).keepsFs).pre (x, st) s0 ∗ R := by
      dsimp only [Spec.keepsFs]
      refine satisfies_lscro_pre hcrl ?_
      dsimp only [sessStoreShimSpecPlaced, withLsCodeRoLoaded]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hx0, hx1, hx2, hfit⟩, by simpa only [sepConj_assoc] using hrest⟩
    refine h605.mono_outcome (x, st) R s0 hpc hrun hpre' hsp ?_
    rintro sf (⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩)
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [Spec.keepsFs, sessStoreShimSpecPlaced, withLsCodeRoLoaded, kitStoreShimSpec,
        cliSessionKitSpecPlaced, cliSessionStoreSpec] at hq ⊢
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
    · dsimp only [Spec.keepsFs, sessStoreShimSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
    · dsimp only [Spec.keepsFs, sessStoreShimSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
    · dsimp only [Spec.keepsFs, sessStoreShimSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
  change subroutine_ok callerProg (0#64 + lsmpl.base 605) _
  rw [BitVec.zero_add]
  exact ls_subroutine_ok_rocl_of_block (callerProg := callerProg) (j := 605)
    h605_kit hblk (by decide) (by decide)

/-! ## Poll lifting and `SessionOnlyKitPlacedOkSEFds` assembly -/

theorem cliSessLoadPoll_fds_rocl_placed_ok_of_poll [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost}
    {AddrValEnv : AddrVal → List AllocEvent → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {SerValEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {s1 s2 s3 s4 : Nat} {vtSym idVtSym : String}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (h569 : subroutine_ok (lsProg_569 H) (lsmpl.base 569)
      (withFdsGe3Closed
        (sessLoadPollSpecPlaced rd pathOk Scope A lim
          (CliLoadPollEnv rd Scope (fun g => AddrValEnv g.val) GetEnv DeserEnv) s2)))
    (hCallerBlk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg
      (0#64 + (cliSessionKitSpecPlaced A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym
        idVtSym).loadPollOff)
      (withLsRoCl lsmpl
        (kitLoadPollPlacedSpecSE M A lim
          (cliSessionKitSpecPlaced A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym idVtSym)
          (cliSessionKitBudgetEnv A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4
            AddrValEnv GetEnv DeserEnv SerValEnv PutEnv vtSym idVtSym)
          Scope encodeRecord true)) := by
  have h569_kit : subroutine_ok (lsProg_569 H) (lsmpl.base 569)
      (withLsCodeRoLoaded lsmpl
        (kitLoadPollPlacedSpecSE M A lim
          (cliSessionKitSpecPlaced A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym idVtSym)
          (cliSessionKitBudgetEnv A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4
            AddrValEnv GetEnv DeserEnv SerValEnv PutEnv vtSym idVtSym)
          Scope encodeRecord true)) := by
    refine subroutine_ok_outcome_intro fun ⟨call, self, d, st⟩ R s0 hpc hrun hpre hsp => ?_
    obtain ⟨hcrl, hpre0⟩ := extract_withLsCodeRoLoaded hpre
    dsimp only [kitLoadPollPlacedSpecSE, withEnvPre, kitLoadPollPlacedSpecS,
      cliSessionKitSpecPlaced, cliSessionKitBudgetEnv, cliSessionStoreSpec, cliSessStoreAt] at hpre0
    have hpre' : s0.mem ⊨
        ⌜s0.fs.files = F0 ∧ FdsGe3Closed s0.fs⌝ ∗
        (⌜s0.readReg64 .x0 = call.fut ∧ s0.readReg64 .x8 = call.out ∧
          call.addr.val = peer.val ∧
          FitsEnv M lim st
            (cliSessionKitLoadPollEnv rd Scope AddrValEnv GetEnv DeserEnv F0 d call.addr.val)⌝ ∗
        (⌜CliSessInv rd F0 pathOk Scope peer d⌝ ∗
        (sessLoadBoxAt call.fut self call.addrA 0#8 ∗ dirAt A.repAlloc self d ∗
          memRegion call.out 368 ∗ protocolAddressAt A.repAlloc call.addr call.addrA ∗
          A.pool lim st s0 ∗ stackAt s0.sp s2 ∗ R))) :=
      Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hpre0
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨⟨hfiles, hfds0⟩, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨⟨hx0, hx8, haddr, hfit⟩, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hinv, hspatial⟩ := hpre'
    have hname : call.addr.name.bytes = peer.name.bytes := congrArg AddrVal.name haddr
    have hfit_hop : FitsEnv M lim st
        (CliLoadPollEnv rd Scope (fun g => AddrValEnv g.val) GetEnv DeserEnv
          s0.fs.files ⟨call, self, d⟩) := by
      rw [hfiles]
      exact hfit
    have hhop_pure :
        s0.readReg64 .x0 = call.fut ∧ s0.readReg64 .x8 = call.out ∧
          call.addr.name.bytes.length < 2 ^ 32 ∧
          (addressText call.addr.val).length < 2 ^ 32 ∧ d.path.length < 2 ^ 32 ∧
          pathOk (pathOf d.path (addressText call.addr.val)) ∧
          (∀ bs, d.get rd s0.fs.files (addressText call.addr.val) = .ok bs → SessFileWf Scope bs) ∧
          FitsEnv M lim st
            (CliLoadPollEnv rd Scope (fun g => AddrValEnv g.val) GetEnv DeserEnv
              s0.fs.files ⟨call, self, d⟩) :=
      ⟨hx0, hx8, hname ▸ hinv.nameLt, haddr ▸ hinv.textLt, hinv.pathLt, haddr ▸ hinv.pathOk,
        fun bs hbs => by
          rw [hfiles, haddr] at hbs
          obtain ⟨bs₀, hget₀, hwf₀⟩ := hinv.getOk
          rw [hget₀] at hbs
          cases hbs
          exact hwf₀,
        hfit_hop⟩
    have hm_hop : s0.mem ⊨
        (withFdsGe3Closed
          (sessLoadPollSpecPlaced rd pathOk Scope A lim
            (CliLoadPollEnv rd Scope (fun g => AddrValEnv g.val) GetEnv DeserEnv) s2)).pre
          (⟨call, self, d⟩, st) s0 ∗ R := by
      dsimp only [withFdsGe3Closed, sessLoadPollSpecPlaced, withLsCodeRoLoaded]
      have h1 : s0.mem ⊨
          ⌜FdsGe3Closed s0.fs⌝ ∗
          (⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
          (⌜s0.readReg64 .x0 = call.fut ∧ s0.readReg64 .x8 = call.out ∧
            call.addr.name.bytes.length < 2 ^ 32 ∧
            (addressText call.addr.val).length < 2 ^ 32 ∧ d.path.length < 2 ^ 32 ∧
            pathOk (pathOf d.path (addressText call.addr.val)) ∧
            (∀ bs, d.get rd s0.fs.files (addressText call.addr.val) = .ok bs →
              SessFileWf Scope bs) ∧
            FitsEnv M lim st
              (CliLoadPollEnv rd Scope (fun g => AddrValEnv g.val) GetEnv DeserEnv
                s0.fs.files ⟨call, self, d⟩)⌝ ∗
          (sessLoadBoxAt call.fut self call.addrA 0#8 ∗ dirAt A.repAlloc self d ∗
            memRegion call.out 368 ∗ protocolAddressAt A.repAlloc call.addr call.addrA ∗
            A.pool lim st s0 ∗ stackAt s0.sp s2 ∗ R))) := by
        rw [satisfies_pure_sepConj]; refine ⟨hfds0, ?_⟩
        rw [satisfies_pure_sepConj]; refine ⟨hcrl, ?_⟩
        rw [satisfies_pure_sepConj]; exact ⟨hhop_pure, hspatial⟩
      exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) h1
    refine h569.mono_outcome (⟨call, self, d⟩, st) R s0 hpc hrun hm_hop hsp fun sf hout => ?_
    rcases hout with ⟨hret, hcc, hpost0⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [withFdsGe3Closed, sessLoadPollSpecPlaced, withLsCodeRoLoaded] at hpost0
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpost0
      obtain ⟨hfds_sf, hpost⟩ := hpost0
      simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
        satisfies_pure_sepConj] at hpost
      obtain ⟨evs, gr, ans, ⟨⟨hgr, htr⟩, hans, hevs⟩, hm⟩ := hpost
      have hevs_kit :
          cliSessionKitLoadPollEnv rd Scope AddrValEnv GetEnv DeserEnv F0 d call.addr.val evs := by
        rw [hfiles] at hevs
        exact hevs
      rw [hfiles, haddr] at hgr
      obtain ⟨bs₀, hget₀, _⟩ := hinv.getOk
      rw [hget₀] at hgr
      subst hgr
      have hout_ent : sessLoadOutAt A.repAlloc call.out ans ⊢
          loadPollPlacedOutAtS Scope A.repAlloc call.out ans := by
        cases bs₀ with
        | nil =>
          have hans' : ans = .ok none := hans
          subst hans'
          exact Entails.refl _
        | cons b bs =>
          obtain ⟨r, hans', _, hsc⟩ := hans
          subst hans'
          exact Entails.pure_right hsc (Entails.refl _)
      have hm_out : sf.mem ⊨
          loadPollPlacedOutAtS Scope A.repAlloc call.out ans ∗
            (sessLoadBoxAt call.fut self call.addrA 1#8 ∗ dirAt A.repAlloc self d ∗
              protocolAddressAt A.repAlloc call.addr call.addrA ∗
              A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp s2 ∗ R) :=
        Satisfies.mono (sepConj_mono_left hout_ent) hm
      dsimp only [withLsCodeRoLoaded, kitLoadPollPlacedSpecSE, withEnvPre, kitLoadPollPlacedSpecS,
        cliSessionKitSpecPlaced, cliSessionKitBudgetEnv, cliSessionStoreSpec, cliSessStoreAt]
      simp only [sepExists_sepConj_left, satisfies_sepExists]
      refine ⟨ans, evs, ?_⟩
      have hgoal : sf.mem ⊨
          ⌜((∃ bs, d.get rd F0 (addressText call.addr.val) = .ok bs ∧
                SessLoadAns Scope (.ok bs) ans) ∧
              sf.trace = s0.trace ++ [] ∧
              cliSessionKitLoadPollEnv rd Scope AddrValEnv GetEnv DeserEnv F0 d
                call.addr.val evs) ∧
            FdsGe3Closed sf.fs⌝ ∗
          (⌜CliSessInv rd F0 pathOk Scope peer d⌝ ∗
            (loadPollPlacedOutAtS Scope A.repAlloc call.out ans ∗
              sessLoadBoxAt call.fut self call.addrA 1#8 ∗ dirAt A.repAlloc self d ∗
              protocolAddressAt A.repAlloc call.addr call.addrA ∗
              A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp s2 ∗ R)) := by
        rw [satisfies_pure_sepConj]
        refine ⟨⟨⟨⟨bs₀, haddr.symm ▸ hget₀, hans⟩, by rw [List.append_nil]; exact htr,
          hevs_kit⟩, hfds_sf⟩, ?_⟩
        rw [satisfies_pure_sepConj]
        exact ⟨hinv, hm_out⟩
      exact Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hgoal
    · dsimp only [withFdsGe3Closed, sessLoadPollSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
    · dsimp only [withFdsGe3Closed, sessLoadPollSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
    · dsimp only [withFdsGe3Closed, sessLoadPollSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
  change subroutine_ok callerProg (0#64 + lsmpl.base 569) _
  rw [BitVec.zero_add]
  exact ls_subroutine_ok_rocl_of_block (callerProg := callerProg) (j := 569)
    h569_kit hCallerBlk (by decide) (by decide)

theorem cliSessStorePoll_fds_rocl_placed_ok_of_poll [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost}
    {AddrValEnv : AddrVal → List AllocEvent → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {s1 s2 s3 s4 : Nat} {vtSym idVtSym : String}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (h570 : subroutine_ok (lsProg_570 H) (lsmpl.base 570)
      (withFdsGe3Closed
        (sessStorePollSpecPlaced A lim
          (CliStorePollEnv (fun g => AddrValEnv g.val) SerializeEnvX PutEnv) s4)))
    (hCallerBlk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg
      (0#64 + (cliSessionKitSpecPlaced A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym
        idVtSym).storePollOff)
      (withLsRoCl lsmpl
        (kitStorePollPlacedSpecE M A lim
          (cliSessionKitSpecPlaced A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym idVtSym)
          (cliSessionKitBudgetEnv A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4
            AddrValEnv GetEnv DeserEnv SerializeCanonEnvX PutEnv vtSym idVtSym)
          encodeRecord true)) := by
  have h570_kit : subroutine_ok (lsProg_570 H) (lsmpl.base 570)
      (withLsCodeRoLoaded lsmpl
        (kitStorePollPlacedSpecE M A lim
          (cliSessionKitSpecPlaced A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym idVtSym)
          (cliSessionKitBudgetEnv A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4
            AddrValEnv GetEnv DeserEnv SerializeCanonEnvX PutEnv vtSym idVtSym)
          encodeRecord true)) := by
    refine subroutine_ok_outcome_intro fun ⟨call, self, d, st⟩ R s0 hpc hrun hpre hsp => ?_
    obtain ⟨hcrl, hpre0⟩ := extract_withLsCodeRoLoaded hpre
    dsimp only [kitStorePollPlacedSpecE, withEnvPre, kitStorePollPlacedSpec,
      cliSessionKitSpecPlaced, cliSessionKitBudgetEnv, cliSessionStoreSpec, cliSessStoreAt] at hpre0
    have hpre' : s0.mem ⊨
        ⌜s0.fs.files = F0 ∧ FdsGe3Closed s0.fs⌝ ∗
        (⌜s0.readReg64 .x0 = call.fut ∧ s0.readReg64 .x8 = call.out ∧
          (Scope call.call.record ∧ (encodeRecord call.call.record).length < 2 ^ 32) ∧
          call.call.addr.val = peer.val ∧
          FitsEnv M lim st
            (cliSessionKitStorePollEnv AddrValEnv SerializeCanonEnvX PutEnv
              d call.call.addr.val call.call.record)⌝ ∗
        (⌜CliSessInv rd F0 pathOk Scope peer d⌝ ∗
        (sessStoreBoxAt call.fut self call.call.addrA call.call.recA 0#8 ∗
          dirAt A.repAlloc self d ∗ memRegion call.out 48 ∗
          protocolAddressAt A.repAlloc call.call.addr call.call.addrA ∗
          sessionRecordAt A.repAlloc call.call.recA call.call.g call.call.record ∗
          A.pool lim st s0 ∗ stackAt s0.sp s4 ∗ R))) :=
      Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hpre0
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨⟨_hfiles, hfds0⟩, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨⟨hx0, hx8, hrec, haddr, hfit⟩, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hinv, hspatial⟩ := hpre'
    have hrec_sat : s0.mem ⊨
        sessionRecordAt A.repAlloc call.call.recA call.call.g call.call.record ∗
          (sessStoreBoxAt call.fut self call.call.addrA call.call.recA 0#8 ∗
            dirAt A.repAlloc self d ∗ memRegion call.out 48 ∗
            protocolAddressAt A.repAlloc call.call.addr call.call.addrA ∗
            A.pool lim st s0 ∗ stackAt s0.sp s4 ∗ R) :=
      Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hspatial
    have hcanon : CanonRecord (toRecordGhost call.call.g) call.call.record :=
      canonRecord_of_satisfies_sessionRecordAt A.repAlloc call.call.recA
        call.call.g call.call.record _ s0.mem hrec_sat
    have hfit_hop : FitsEnv M lim st
        (CliStorePollEnv (fun g => AddrValEnv g.val) SerializeEnvX PutEnv ⟨call, self, d⟩) := by
      simpa only [CliStorePollEnv, cliSessionKitStorePollEnv, serializeEnvX_eq_canon hcanon]
        using hfit
    have hname : call.call.addr.name.bytes = peer.name.bytes := congrArg AddrVal.name haddr
    have hm_hop : s0.mem ⊨
        (withFdsGe3Closed
          (sessStorePollSpecPlaced A lim
            (CliStorePollEnv (fun g => AddrValEnv g.val) SerializeEnvX PutEnv) s4)).pre
          (⟨call, self, d⟩, st) s0 ∗ R := by
      dsimp only [withFdsGe3Closed, sessStorePollSpecPlaced, withLsCodeRoLoaded]
      have h1 : s0.mem ⊨
          ⌜FdsGe3Closed s0.fs⌝ ∗
          (⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
          (⌜s0.readReg64 .x0 = call.fut ∧ s0.readReg64 .x8 = call.out ∧
            call.call.addr.name.bytes.length < 2 ^ 32 ∧
            (encodeRecord call.call.record).length < 2 ^ 32 ∧
            d.changed.length < 2 ^ 32 ∧
            FitsEnv M lim st
              (CliStorePollEnv (fun g => AddrValEnv g.val) SerializeEnvX PutEnv
                ⟨call, self, d⟩)⌝ ∗
          (sessStoreBoxAt call.fut self call.call.addrA call.call.recA 0#8 ∗
            dirAt A.repAlloc self d ∗ memRegion call.out 48 ∗
            protocolAddressAt A.repAlloc call.call.addr call.call.addrA ∗
            sessionRecordAt A.repAlloc call.call.recA call.call.g call.call.record ∗
            A.pool lim st s0 ∗ stackAt s0.sp s4 ∗ R))) := by
        rw [satisfies_pure_sepConj]; refine ⟨hfds0, ?_⟩
        rw [satisfies_pure_sepConj]; refine ⟨hcrl, ?_⟩
        rw [satisfies_pure_sepConj]
        exact ⟨⟨hx0, hx8, hname ▸ hinv.nameLt, hrec.2, hinv.changedLt.1, hfit_hop⟩, hspatial⟩
      exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) h1
    refine h570.mono_outcome (⟨call, self, d⟩, st) R s0 hpc hrun hm_hop hsp fun sf hout => ?_
    rcases hout with ⟨hret, hcc, hpost0⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [withFdsGe3Closed, sessStorePollSpecPlaced, withLsCodeRoLoaded] at hpost0
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpost0
      obtain ⟨hfds_sf, hpost⟩ := hpost0
      simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
        satisfies_pure_sepConj] at hpost
      obtain ⟨evs, ⟨htr, hevs⟩, hm⟩ := hpost
      have hevs_kit :
          cliSessionKitStorePollEnv AddrValEnv SerializeCanonEnvX PutEnv
            d call.call.addr.val call.call.record evs := by
        simpa only [CliStorePollEnv, cliSessionKitStorePollEnv, serializeEnvX_eq_canon hcanon]
          using hevs
      have hinv' : CliSessInv rd F0 pathOk Scope peer
          (d.put (addressText call.call.addr.val) (encodeRecord call.call.record)) :=
        cliSessionStoreSpec_storeUpdate_inv (A := A.repAlloc) (b := 0#64)
          (s1 := s1) (s2 := s2) (s3 := s3) (s4 := s4) (ans := .ok ()) hinv haddr hrec
      dsimp only [withLsCodeRoLoaded, kitStorePollPlacedSpecE, withEnvPre, kitStorePollPlacedSpec,
        cliSessionKitSpecPlaced, cliSessionKitBudgetEnv, cliSessionStoreSpec, cliSessStoreAt]
      simp only [sepExists_sepConj_left, satisfies_sepExists]
      refine ⟨.ok (), evs, ?_⟩
      dsimp only [storePollPlacedOutAt]
      have hgoal : sf.mem ⊨
          ⌜((Except.ok () : Except Unit Unit) = .ok () ∧ sf.trace = s0.trace ++ [] ∧
              cliSessionKitStorePollEnv AddrValEnv SerializeCanonEnvX PutEnv
                d call.call.addr.val call.call.record evs) ∧
            FdsGe3Closed sf.fs⌝ ∗
          (⌜CliSessInv rd F0 pathOk Scope peer
              (d.put (addressText call.call.addr.val) (encodeRecord call.call.record))⌝ ∗
            (sessStoreBoxAt call.fut self call.call.addrA call.call.recA 1#8 ∗
              dirAt A.repAlloc self (d.put (addressText call.call.addr.val)
                (encodeRecord call.call.record)) ∗
              (call.out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ memRegion (call.out + 8#64) 40 ∗
              protocolAddressAt A.repAlloc call.call.addr call.call.addrA ∗
              sessionRecordAt A.repAlloc call.call.recA call.call.g call.call.record ∗
              A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp s4 ∗ R)) := by
        rw [satisfies_pure_sepConj]
        refine ⟨⟨⟨rfl, by rw [List.append_nil]; exact htr, hevs_kit⟩, hfds_sf⟩, ?_⟩
        rw [satisfies_pure_sepConj]
        exact ⟨hinv', Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hm⟩
      exact Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hgoal
    · dsimp only [withFdsGe3Closed, sessStorePollSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
    · dsimp only [withFdsGe3Closed, sessStorePollSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
    · dsimp only [withFdsGe3Closed, sessStorePollSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
  change subroutine_ok callerProg (0#64 + lsmpl.base 570) _
  rw [BitVec.zero_add]
  exact ls_subroutine_ok_rocl_of_block (callerProg := callerProg) (j := 570)
    h570_kit hCallerBlk (by decide) (by decide)

private theorem seqEnv_mono {P₁ P₂ Q₁ Q₂ : List AllocEvent → Prop}
    (hP : ∀ e, P₁ e → P₂ e) (hQ : ∀ e, Q₁ e → Q₂ e)
    {evs : List AllocEvent} (h : SeqEnv P₁ Q₁ evs) :
    SeqEnv P₂ Q₂ evs := by
  rcases h with hp | ⟨e₁, e₂, rfl, hp, hq⟩
  · exact Or.inl (hP evs hp)
  · exact Or.inr ⟨e₁, e₂, rfl, hP e₁ hp, hQ e₂ hq⟩

theorem cliSessStorePoll_fds_rocl_seqFree_placed_ok_of_poll [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost}
    {AddrValEnv : AddrVal → List AllocEvent → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {s1 s2 s3 s4 : Nat} {vtSym idVtSym : String}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (h570 : subroutine_ok (lsProg_570 H) (lsmpl.base 570)
      (withFdsGe3Closed
        (sessStorePollSpecPlaced A lim
          (CliStorePollEnv (fun g => AddrValEnv g.val) RecordSerializeSeqFreeCellsEnv PutEnv) s4)))
    (hCallerBlk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg
      (0#64 + (cliSessionKitSpecPlaced A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym
        idVtSym).storePollOff)
      (withLsRoCl lsmpl
        (kitStorePollPlacedSpecE M A lim
          (cliSessionKitSpecPlaced A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym idVtSym)
          (cliSessionKitBudgetEnv A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4
            AddrValEnv GetEnv DeserEnv SerializeCanonSeqFreeValidEnv PutEnv vtSym idVtSym)
          encodeRecord true)) := by
  have h570_kit : subroutine_ok (lsProg_570 H) (lsmpl.base 570)
      (withLsCodeRoLoaded lsmpl
        (kitStorePollPlacedSpecE M A lim
          (cliSessionKitSpecPlaced A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym idVtSym)
          (cliSessionKitBudgetEnv A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4
            AddrValEnv GetEnv DeserEnv SerializeCanonSeqFreeValidEnv PutEnv vtSym idVtSym)
          encodeRecord true)) := by
    refine subroutine_ok_outcome_intro fun ⟨call, self, d, st⟩ R s0 hpc hrun hpre hsp => ?_
    obtain ⟨hcrl, hpre0⟩ := extract_withLsCodeRoLoaded hpre
    dsimp only [kitStorePollPlacedSpecE, withEnvPre, kitStorePollPlacedSpec,
      cliSessionKitSpecPlaced, cliSessionKitBudgetEnv, cliSessionStoreSpec, cliSessStoreAt] at hpre0
    have hpre' : s0.mem ⊨
        ⌜s0.fs.files = F0 ∧ FdsGe3Closed s0.fs⌝ ∗
        (⌜s0.readReg64 .x0 = call.fut ∧ s0.readReg64 .x8 = call.out ∧
          (Scope call.call.record ∧ (encodeRecord call.call.record).length < 2 ^ 32) ∧
          call.call.addr.val = peer.val ∧
          FitsEnv M lim st
            (cliSessionKitStorePollEnv AddrValEnv SerializeCanonSeqFreeValidEnv PutEnv
              d call.call.addr.val call.call.record)⌝ ∗
        (⌜CliSessInv rd F0 pathOk Scope peer d⌝ ∗
        (sessStoreBoxAt call.fut self call.call.addrA call.call.recA 0#8 ∗
          dirAt A.repAlloc self d ∗ memRegion call.out 48 ∗
          protocolAddressAt A.repAlloc call.call.addr call.call.addrA ∗
          sessionRecordAt A.repAlloc call.call.recA call.call.g call.call.record ∗
          A.pool lim st s0 ∗ stackAt s0.sp s4 ∗ R))) :=
      Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hpre0
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨⟨_hfiles, hfds0⟩, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨⟨hx0, hx8, hrec, haddr, hfit⟩, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hinv, hspatial⟩ := hpre'
    have hrec_sat : s0.mem ⊨
        sessionRecordAt A.repAlloc call.call.recA call.call.g call.call.record ∗
          (sessStoreBoxAt call.fut self call.call.addrA call.call.recA 0#8 ∗
            dirAt A.repAlloc self d ∗ memRegion call.out 48 ∗
            protocolAddressAt A.repAlloc call.call.addr call.call.addrA ∗
            A.pool lim st s0 ∗ stackAt s0.sp s4 ∗ R) :=
      Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hspatial
    have hgvalid : RecordGhostValid call.call.g call.call.record :=
      recordGhostValid_of_sessionRecordAt hrec_sat
    have hcells_eq : ∀ evs,
        RecordSerializeSeqFreeCellsEnv (toRecordGhost call.call.g) call.call.record evs =
          RecordSerializeSeqFreeEnv call.call.g call.call.record evs := by
      intro evs; cases call.call.g; rfl
    have hfit_hop : FitsEnv M lim st
        (CliStorePollEnv (fun g => AddrValEnv g.val) RecordSerializeSeqFreeCellsEnv PutEnv
          ⟨call, self, d⟩) := by
      intro evs he
      exact hfit evs
        (seqEnv_mono (fun _ ha => ha)
          (fun _ h2 =>
            seqEnv_mono
              (fun e hs => ⟨call.call.g, hgvalid, (hcells_eq e).mp hs⟩)
              (fun _ hp => hp) h2)
          he)
    have hname : call.call.addr.name.bytes = peer.name.bytes := congrArg AddrVal.name haddr
    have hm_hop : s0.mem ⊨
        (withFdsGe3Closed
          (sessStorePollSpecPlaced A lim
            (CliStorePollEnv (fun g => AddrValEnv g.val) RecordSerializeSeqFreeCellsEnv PutEnv)
            s4)).pre
          (⟨call, self, d⟩, st) s0 ∗ R := by
      dsimp only [withFdsGe3Closed, sessStorePollSpecPlaced, withLsCodeRoLoaded]
      have h1 : s0.mem ⊨
          ⌜FdsGe3Closed s0.fs⌝ ∗
          (⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
          (⌜s0.readReg64 .x0 = call.fut ∧ s0.readReg64 .x8 = call.out ∧
            call.call.addr.name.bytes.length < 2 ^ 32 ∧
            (encodeRecord call.call.record).length < 2 ^ 32 ∧
            d.changed.length < 2 ^ 32 ∧
            FitsEnv M lim st
              (CliStorePollEnv (fun g => AddrValEnv g.val) RecordSerializeSeqFreeCellsEnv PutEnv
                ⟨call, self, d⟩)⌝ ∗
          (sessStoreBoxAt call.fut self call.call.addrA call.call.recA 0#8 ∗
            dirAt A.repAlloc self d ∗ memRegion call.out 48 ∗
            protocolAddressAt A.repAlloc call.call.addr call.call.addrA ∗
            sessionRecordAt A.repAlloc call.call.recA call.call.g call.call.record ∗
            A.pool lim st s0 ∗ stackAt s0.sp s4 ∗ R))) := by
        rw [satisfies_pure_sepConj]; refine ⟨hfds0, ?_⟩
        rw [satisfies_pure_sepConj]; refine ⟨hcrl, ?_⟩
        rw [satisfies_pure_sepConj]
        exact ⟨⟨hx0, hx8, hname ▸ hinv.nameLt, hrec.2, hinv.changedLt.1, hfit_hop⟩, hspatial⟩
      exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) h1
    refine h570.mono_outcome (⟨call, self, d⟩, st) R s0 hpc hrun hm_hop hsp fun sf hout => ?_
    rcases hout with ⟨hret, hcc, hpost0⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [withFdsGe3Closed, sessStorePollSpecPlaced, withLsCodeRoLoaded] at hpost0
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpost0
      obtain ⟨hfds_sf, hpost⟩ := hpost0
      simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
        satisfies_pure_sepConj] at hpost
      obtain ⟨evs, ⟨htr, hevs⟩, hm⟩ := hpost
      have hevs_kit :
          cliSessionKitStorePollEnv AddrValEnv SerializeCanonSeqFreeValidEnv PutEnv
            d call.call.addr.val call.call.record evs :=
        seqEnv_mono (fun _ ha => ha)
          (fun _ h2 =>
            seqEnv_mono
              (fun e hs => ⟨call.call.g, hgvalid, (hcells_eq e).mp hs⟩)
              (fun _ hp => hp) h2)
          hevs
      have hinv' : CliSessInv rd F0 pathOk Scope peer
          (d.put (addressText call.call.addr.val) (encodeRecord call.call.record)) :=
        cliSessionStoreSpec_storeUpdate_inv (A := A.repAlloc) (b := 0#64)
          (s1 := s1) (s2 := s2) (s3 := s3) (s4 := s4) (ans := .ok ()) hinv haddr hrec
      dsimp only [withLsCodeRoLoaded, kitStorePollPlacedSpecE, withEnvPre, kitStorePollPlacedSpec,
        cliSessionKitSpecPlaced, cliSessionKitBudgetEnv, cliSessionStoreSpec, cliSessStoreAt]
      simp only [sepExists_sepConj_left, satisfies_sepExists]
      refine ⟨.ok (), evs, ?_⟩
      dsimp only [storePollPlacedOutAt]
      have hgoal : sf.mem ⊨
          ⌜((Except.ok () : Except Unit Unit) = .ok () ∧ sf.trace = s0.trace ++ [] ∧
              cliSessionKitStorePollEnv AddrValEnv SerializeCanonSeqFreeValidEnv PutEnv
                d call.call.addr.val call.call.record evs) ∧
            FdsGe3Closed sf.fs⌝ ∗
          (⌜CliSessInv rd F0 pathOk Scope peer
              (d.put (addressText call.call.addr.val) (encodeRecord call.call.record))⌝ ∗
            (sessStoreBoxAt call.fut self call.call.addrA call.call.recA 1#8 ∗
              dirAt A.repAlloc self (d.put (addressText call.call.addr.val)
                (encodeRecord call.call.record)) ∗
              (call.out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ memRegion (call.out + 8#64) 40 ∗
              protocolAddressAt A.repAlloc call.call.addr call.call.addrA ∗
              sessionRecordAt A.repAlloc call.call.recA call.call.g call.call.record ∗
              A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp s4 ∗ R)) := by
        rw [satisfies_pure_sepConj]
        refine ⟨⟨⟨rfl, by rw [List.append_nil]; exact htr, hevs_kit⟩, hfds_sf⟩, ?_⟩
        rw [satisfies_pure_sepConj]
        exact ⟨hinv', Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hm⟩
      exact Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hgoal
    · dsimp only [withFdsGe3Closed, sessStorePollSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
    · dsimp only [withFdsGe3Closed, sessStorePollSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
    · dsimp only [withFdsGe3Closed, sessStorePollSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
  change subroutine_ok callerProg (0#64 + lsmpl.base 570) _
  rw [BitVec.zero_add]
  exact ls_subroutine_ok_rocl_of_block (callerProg := callerProg) (j := 570)
    h570_kit hCallerBlk (by decide) (by decide)

/-- Assemble `SessionOnlyKitPlacedOkSEFds` for `cliSessionKitSpecPlaced` (`SerializeCanonEnvX`)
from `AllocContractsFsPlaced` and the Block `569`/`570` poll contracts. -/
theorem cliSessKitOkSE_fds_placed_of_polls [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost}
    {AddrValEnv : AddrVal → List AllocEvent → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {s1 s2 s3 s4 : Nat} {vtSym idVtSym : String}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hFs : AllocContractsFsPlaced A lim H)
    (h569 : subroutine_ok (lsProg_569 H) (lsmpl.base 569)
      (withFdsGe3Closed
        (sessLoadPollSpecPlaced rd pathOk Scope A lim
          (CliLoadPollEnv rd Scope (fun g => AddrValEnv g.val) GetEnv DeserEnv) s2)))
    (h570 : subroutine_ok (lsProg_570 H) (lsmpl.base 570)
      (withFdsGe3Closed
        (sessStorePollSpecPlaced A lim
          (CliStorePollEnv (fun g => AddrValEnv g.val) SerializeEnvX PutEnv) s4)))
    (hs1 : loadShimNeedPlaced ≤ s1) (hs3 : storeShimNeedPlaced ≤ s3) :
    SessionOnlyKitPlacedOkSEFds A lim
      (cliSessionKitSpecPlaced A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym idVtSym)
      (cliSessionKitBudgetEnv A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4
        AddrValEnv GetEnv DeserEnv SerializeCanonEnvX PutEnv vtSym idVtSym)
      Scope encodeRecord H where
  loadShim := fun hblk => cliSessLoadShim_fds_rocl_placed_ok hFs hs1 hblk
  loadPoll := fun hblk => cliSessLoadPoll_fds_rocl_placed_ok_of_poll h569 hblk
  loadFutDrop := fun hblk => by
    dsimp only [cliSessionKitSpecPlaced]
    rw [lsDropOffPlaced_eq hDropNz]
    exact cliIdFutDrop_fds_rocl_placed_ok hblk
  storeShim := fun hblk => cliSessStoreShim_fds_rocl_placed_ok hFs hs3 hblk
  storePoll := fun hblk => cliSessStorePoll_fds_rocl_placed_ok_of_poll h570 hblk
  storeFutDrop := fun hblk => by
    dsimp only [cliSessionKitSpecPlaced]
    rw [lsDropOffPlaced_eq hDropNz]
    exact cliIdFutDrop_fds_rocl_placed_ok hblk

/-- `SeqFree` (`SerializeCanonSeqFreeValidEnv`) variant of `cliSessKitOkSE_fds_placed_of_polls`. -/
theorem cliSessKitOkSE_fds_seqFree_placed_of_polls [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost}
    {AddrValEnv : AddrVal → List AllocEvent → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {s1 s2 s3 s4 : Nat} {vtSym idVtSym : String}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hFs : AllocContractsFsPlaced A lim H)
    (h569 : subroutine_ok (lsProg_569 H) (lsmpl.base 569)
      (withFdsGe3Closed
        (sessLoadPollSpecPlaced rd pathOk Scope A lim
          (CliLoadPollEnv rd Scope (fun g => AddrValEnv g.val) GetEnv DeserEnv) s2)))
    (h570 : subroutine_ok (lsProg_570 H) (lsmpl.base 570)
      (withFdsGe3Closed
        (sessStorePollSpecPlaced A lim
          (CliStorePollEnv (fun g => AddrValEnv g.val) RecordSerializeSeqFreeCellsEnv PutEnv) s4)))
    (hs1 : loadShimNeedPlaced ≤ s1) (hs3 : storeShimNeedPlaced ≤ s3) :
    SessionOnlyKitPlacedOkSEFds A lim
      (cliSessionKitSpecPlaced A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym idVtSym)
      (cliSessionKitBudgetEnv A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4
        AddrValEnv GetEnv DeserEnv SerializeCanonSeqFreeValidEnv PutEnv vtSym idVtSym)
      Scope encodeRecord H where
  loadShim := fun hblk => cliSessLoadShim_fds_rocl_placed_ok hFs hs1 hblk
  loadPoll := fun hblk => cliSessLoadPoll_fds_rocl_placed_ok_of_poll h569 hblk
  loadFutDrop := fun hblk => by
    dsimp only [cliSessionKitSpecPlaced]
    rw [lsDropOffPlaced_eq hDropNz]
    exact cliIdFutDrop_fds_rocl_placed_ok hblk
  storeShim := fun hblk => cliSessStoreShim_fds_rocl_placed_ok hFs hs3 hblk
  storePoll := fun hblk => cliSessStorePoll_fds_rocl_seqFree_placed_ok_of_poll h570 hblk
  storeFutDrop := fun hblk => by
    dsimp only [cliSessionKitSpecPlaced]
    rw [lsDropOffPlaced_eq hDropNz]
    exact cliIdFutDrop_fds_rocl_placed_ok hblk

/-! ## `FsAtFds` and `writeFileHook` preservation -/

theorem fsAt_cliSessionKit_of_fdsGe3Closed [LibsignalPlacement] {A : RustAlloc}
    {envOk : FsFiles → Prop} {rd : ReadRule} {F0 : FsFiles}
    {pathOk : List (BitVec 8) → Prop} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {peer : AddrGhost} {s1 s2 s3 s4 : Nat} {vtSym idVtSym : String} {P : Program} {s : State}
    (hP : TraceFsSound P) (henv : envOk F0) (hfiles : s.fs.files = F0) (hfds : FdsGe3Closed s.fs) :
    FsAtFds envOk
      (cliSessionKitSpecPlaced A rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym idVtSym).fdsOk
      (cliSessionKitSpecPlaced A rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym idVtSym).Quiet P s :=
  .inr ⟨cliSessionKitSpecPlaced_quiet (A := A) (rd := rd) (F0 := F0) (pathOk := pathOk)
    (Scope := Scope) (peer := peer) (s1 := s1) (s2 := s2) (s3 := s3) (s4 := s4)
    (vtSym := vtSym) (idVtSym := idVtSym), hP, hfiles.symm ▸ henv, hfds⟩

theorem cliSessionKitSpecPlaced_writeFileHook [LibsignalPlacement] {A : RustAlloc}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost}
    {s1 s2 s3 s4 : Nat} {vtSym idVtSym : String} {s : State}
    (hfds :
      (cliSessionKitSpecPlaced A rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym idVtSym).fdsOk s.fs) :
    (cliSessionKitSpecPlaced A rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym idVtSym).fdsOk
      (writeFileHook s).fs :=
  fdsGe3Closed_writeFileHook hfds

theorem hookOk_writeFileHook_withFdsGe3Closed_sess {α : Type} {spec : Spec α}
    (hok : HookOk writeFileHook spec) :
    HookOk writeFileHook (withFdsGe3Closed spec) :=
  hookOk_withFdsGe3Closed_writeFileHook hok

end LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitFdsPlacedBudget
