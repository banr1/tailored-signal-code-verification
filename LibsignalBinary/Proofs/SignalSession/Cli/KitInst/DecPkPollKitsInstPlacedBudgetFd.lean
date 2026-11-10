/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.CliCBudget
public import LibsignalBinary.Proofs.RecordCodecs.AssemblyBudget
public import LibsignalBinary.Proofs.RecordCodecs.SignedAssemblyBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
public import LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.DecPkPollKitsFdsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkCliPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkCliPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdKeyPairPollPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdRegIdPollPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KemDeserializeSlotPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.DropSpeWordPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePollPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPollPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPollPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPollPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPollPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePollPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueXCliPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPollPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.StorePollXPlacedBudget
import Arm64.Trusted.Spec.Hoare
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# `CliDecPkPollKitsPlacedOkFds` Instantiation from `CliRunHooksBundleFd`

Discharges `CliDecPkPollKitsPlacedOkFds` from `CliRunHooksBundleFd`, `CliGhostAllocHooks`,
`lsmpl.base 547 ≠ 0#64`, and `lim.enforced = true`, lifting pure-FS allocating callees via
`AllocWithFds.withFds` and assembling `Dir::get` (block 589) with the ten `read_file`-calling polls
via `cliDecPkPollKitsPlacedOkFds_of_polls`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.KitInst.DecPkPollKitsInstPlacedBudgetFd

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSessionApi (SessionRecord)
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement lsmpl withLsCodeLoaded)
open CryptoVerification.E2E.Record.Placed (lsProg_46 lsProg_52)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles subroutine_ok_withLsCodeRoLoaded_of_rocl withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet (doReserveStackX)
open CryptoVerification.RecordCodecs.Placed (lsProg_65 lsProg_84 lsProg_595)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced lsReadFileSym)
open CryptoVerification.SignalSession.Cli.KitInst.IdKit (cliGhostExterns_blackBox)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo cliRunBudgets cliWrOk handleErrorSymCli)
open CryptoVerification.SignalSession.Cli.Placed
  (lsProg_543 lsProg_553 lsProg_565 lsProg_566 lsProg_567 lsProg_568 lsProg_569 lsProg_570
   lsProg_571 lsProg_573 lsProg_575 lsProg_576 lsProg_578 lsProg_589 lsProg_594 lsProg_596
   lsProg_597)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (cliKitStk)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets pathNeed)
open CryptoVerification.SignalSession.Cli.Slots (scopeKit)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.CliCBudget (signedHooksPlaced_of_codecHooks signedPortDepsPlaced_ok)
open LibsignalBinary.Proofs.RecordCodecs.AssemblyBudget
  (identityKeyPair_tryFrom_placed_ok_of_hooks preKeyRecord_deserialize_placed_ok_of_hooks)
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget
  (identityKeyPairTryFromPlacedSpec identityKeyPairTryFromRawSpec preKeyDeserializePlacedSpec
   preKeyDeserializeRawSpec)
open LibsignalBinary.Proofs.RecordCodecs.SignedAssemblyBudget
  (decodeKyberPreKey_placed_ok decodeSignedPreKey_placed_ok)
open LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget
  (decodeKyberPreKeyPlacedSpec decodeKyberPreKeyRawSpec decodeSignedPreKeyPlacedSpec
   decodeSignedPreKeyRawSpec)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget
  (SerializeEnvX serializeCanonSpecX)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux (SessDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget (DecimalEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a (DirGetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetFd (dirGet_placed_ok_of_deps_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget
  (PathEnv path_placed_caller_ok_of_deps)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudgetFd
  (path_placed_caller_ok_of_allocFs_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux (DirPutEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux (DirPutStrEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
  (ls_transfer_withFdsGe3Closed_lscro withLsRetAddr624AndFds)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed extract_withFdsGe3Closed withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds
  (cliGhostAllocHooks_withFds withFds withFds_pool_enforced withFds_repAlloc)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.DecPkPollKitsFdsPlacedBudget
  (CliDecPkPollKitsPlacedOkFds cliDecPkPollKitsPlacedOkFds_of_polls)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkCliPlacedBudget
  (cliDirPutStr_placed_ok_of_sessHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
  (AddrTextValEnv SessKitHooksPlaced cliAddrText_placed_ok_of_sessHooks
   cliDecimal_placed_ok_of_sessHooks cliDirPut_placed_ok_of_sessHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Reserve11PlacedBudget
  (cliDoReserve_placed_ok_at)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudgetFd
  (CliRunHooksBundleFd)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdKeyPairPollPlacedBudgetFd
  (idKeyPairPoll_placed_ok_of_deps_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdRegIdPollPlacedBudgetFd
  (idRegIdPoll_placed_ok_of_deps_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (CliGhostAllocHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KemDeserializeSlotPlacedBudgetFd
  (allocContractsXCliPlaced_withFds_of_runHooks codecHooksPlaced_withFds subroutine_ok_of_pre_post)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (addrTextSpecPlaced decimalSpecPlaced dirPutSpecPlaced dirPutStrSpecPlaced
   dropSpeWordSpecPlaced readFileSpecPlaced sessDeserializeSpecPlaced sessStorePollSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.DropSpeWordPlacedBudget (dropSpeWord_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePollPlacedBudgetFd
  (idSavePoll_placed_ok_of_get_put_bb_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPollPlacedBudgetFd
  (idTrustPoll_placed_ok_of_get_bb_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPollPlacedBudgetFd
  (kpkGetPoll_placed_fs_ok_of_deps_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPollPlacedBudgetFd
  (kpkMarkPoll_placed_ok_of_deps_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollPlacedBudgetFd
  (sessLoadPoll_placed_ok_of_deps_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser
  (sessDeserialize_cli_dcan_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPollPlacedBudgetFd
  (pkGetPoll_placed_fs_ok_of_deps_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePollPlacedBudgetFd
  (pkRemovePoll_placed_ok_of_deps_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueXCliPlacedBudget
  (serializeCanonX_cli_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPollPlacedBudgetFd
  (spkGetPoll_placed_fs_ok_of_deps_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.StorePoll.LayoutBudget (CliStorePollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.StorePollXPlacedBudget
  (sessStorePoll_placed_ok_of_depsX)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommonBudget (doReserveSpecOf)

/-! ## `SessKitHooksPlaced` Lift to `withFds A` and Pool Extraction Helpers -/

theorem sessKitHooksPlaced_withFds_of_runHooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hh : RunHooksPlaced A lim H) :
    SessKitHooksPlaced (withFds A) lim H := by
  have halloc := allocContractsXCliPlaced_withFds_of_runHooks hh
  have hres : ∀ {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i H] {resStack : Nat},
      doReserveStackX ≤ resStack → i < 619 →
      subroutine_ok callerProg (lsmpl.base 561)
        (withLsCodeRoLoaded lsmpl (doReserveSpecOf resStack (withFds A) lim)) := by
    intro callerProg i _ resStack hstk hi
    exact subroutine_ok_withLsCodeRoLoaded_of_rocl
      (cliDoReserve_placed_ok_at (prog := callerProg) (i := i) halloc hstk
        (hh.panics "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error" (by decide)) hi)
  exact
    { alloc := halloc
      panics := hh.panics
      memcpyRO := hh.memcpyRO
      bcmp := hh.bcmp
      fs := hh.fs
      reserve := fun hstk hi => hres hstk hi
      path := fun hstk hi =>
        path_placed_caller_ok_of_deps
          (resProg := lsProg_596 H) (resBlk := 596)
          halloc hh.memcpyRO
          (hres (callerProg := lsProg_596 H) (i := 596) (Nat.le_refl _) (by decide))
          hstk hi (by decide) (by decide) }

private theorem withFds_pool_eq_of_fds {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {s : State} (henf : lim.enforced = true) (hFds : FdsGe3Closed s.fs)
    (st : M.σ) :
    (withFds A).pool lim st s = A.pool lim st s := by
  rw [withFds_pool_enforced A henf]
  have hTrue : FdsGe3Closed s.fs = True := propext ⟨fun _ => trivial, fun _ => hFds⟩
  rw [hTrue, ProofLib.pure_true, Arm64.emp_sepConj]

private theorem fds_of_evs_right4 {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {Q1 : List AllocEvent → SepProp} {P2 P3 R : SepProp}
    {st : M.σ} {sf : State} (henf : lim.enforced = true)
    (h : sf.mem ⊨ (∃∗ evs : List AllocEvent,
      Q1 evs ∗ P2 ∗ P3 ∗ (withFds A).pool lim (M.stepEvents evs st) sf) ∗ R) :
    FdsGe3Closed sf.fs := by
  rw [sepExists_sepConj_left, satisfies_sepExists] at h
  rcases h with ⟨evs, h⟩
  rw [withFds_pool_enforced A henf] at h
  have hEq :
      (Q1 evs ∗ P2 ∗ P3 ∗ (⌜FdsGe3Closed sf.fs⌝ ∗ A.pool lim (M.stepEvents evs st) sf)) ∗ R =
      ⌜FdsGe3Closed sf.fs⌝ ∗ ((Q1 evs ∗ P2 ∗ P3 ∗ A.pool lim (M.stepEvents evs st) sf) ∗ R) := by
    sep_ac_rfl
  rw [hEq, satisfies_pure_sepConj] at h
  exact h.1

private theorem fds_of_evs_right5 {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {Q1 : List AllocEvent → SepProp} {P2 P3 P4 R : SepProp}
    {st : M.σ} {sf : State} (henf : lim.enforced = true)
    (h : sf.mem ⊨ (∃∗ evs : List AllocEvent,
      Q1 evs ∗ P2 ∗ P3 ∗ P4 ∗ (withFds A).pool lim (M.stepEvents evs st) sf) ∗ R) :
    FdsGe3Closed sf.fs := by
  rw [sepExists_sepConj_left, satisfies_sepExists] at h
  rcases h with ⟨evs, h⟩
  rw [withFds_pool_enforced A henf] at h
  have hEq :
      (Q1 evs ∗ P2 ∗ P3 ∗ P4 ∗ (⌜FdsGe3Closed sf.fs⌝ ∗ A.pool lim (M.stepEvents evs st) sf)) ∗ R =
      ⌜FdsGe3Closed sf.fs⌝ ∗ ((Q1 evs ∗ P2 ∗ P3 ∗ P4 ∗ A.pool lim (M.stepEvents evs st) sf) ∗ R) := by
    sep_ac_rfl
  rw [hEq, satisfies_pure_sepConj] at h
  exact h.1

private theorem fds_of_evs_right6 {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {Q1 : List AllocEvent → SepProp} {P2 P3 P4 P5 R : SepProp}
    {st : M.σ} {sf : State} (henf : lim.enforced = true)
    (h : sf.mem ⊨ (∃∗ evs : List AllocEvent,
      Q1 evs ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ (withFds A).pool lim (M.stepEvents evs st) sf) ∗ R) :
    FdsGe3Closed sf.fs := by
  rw [sepExists_sepConj_left, satisfies_sepExists] at h
  rcases h with ⟨evs, h⟩
  rw [withFds_pool_enforced A henf] at h
  have hEq :
      (Q1 evs ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗
        (⌜FdsGe3Closed sf.fs⌝ ∗ A.pool lim (M.stepEvents evs st) sf)) ∗ R =
      ⌜FdsGe3Closed sf.fs⌝ ∗
        ((Q1 evs ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ A.pool lim (M.stepEvents evs st) sf) ∗ R) := by
    sep_ac_rfl
  rw [hEq, satisfies_pure_sepConj] at h
  exact h.1

private theorem fds_of_evs_mid5 {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {Q1 : List AllocEvent → SepProp} {P2 P3 Tail R : SepProp}
    {st : M.σ} {sf : State} (henf : lim.enforced = true)
    (h : sf.mem ⊨ (∃∗ evs : List AllocEvent,
      Q1 evs ∗ P2 ∗ P3 ∗ (withFds A).pool lim (M.stepEvents evs st) sf ∗ Tail) ∗ R) :
    FdsGe3Closed sf.fs := by
  rw [sepExists_sepConj_left, satisfies_sepExists] at h
  rcases h with ⟨evs, h⟩
  rw [withFds_pool_enforced A henf] at h
  have hEq :
      (Q1 evs ∗ P2 ∗ P3 ∗
        (⌜FdsGe3Closed sf.fs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗ Tail) ∗ R =
      ⌜FdsGe3Closed sf.fs⌝ ∗
        ((Q1 evs ∗ P2 ∗ P3 ∗ A.pool lim (M.stepEvents evs st) sf ∗ Tail) ∗ R) := by
    sep_ac_rfl
  rw [hEq, satisfies_pure_sepConj] at h
  exact h.1

private theorem fds_of_evs_mid9 {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {Q1 : List AllocEvent → SepProp} {P2 P3 P4 P5 P6 P7 Tail R : SepProp}
    {st : M.σ} {sf : State} (henf : lim.enforced = true)
    (h : sf.mem ⊨ (∃∗ evs : List AllocEvent,
      Q1 evs ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ P6 ∗ P7 ∗
        (withFds A).pool lim (M.stepEvents evs st) sf ∗ Tail) ∗ R) :
    FdsGe3Closed sf.fs := by
  rw [sepExists_sepConj_left, satisfies_sepExists] at h
  rcases h with ⟨evs, h⟩
  rw [withFds_pool_enforced A henf] at h
  have hEq :
      (Q1 evs ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ P6 ∗ P7 ∗
        (⌜FdsGe3Closed sf.fs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗ Tail) ∗ R =
      ⌜FdsGe3Closed sf.fs⌝ ∗
        ((Q1 evs ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ P6 ∗ P7 ∗
          A.pool lim (M.stepEvents evs st) sf ∗ Tail) ∗ R) := by
    sep_ac_rfl
  rw [hEq, satisfies_pure_sepConj] at h
  exact h.1

private theorem fds_of_codec_post {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {P1 Tail R : SepProp} {Q : List AllocEvent → SepProp}
    {st : M.σ} {sf : State} (henf : lim.enforced = true)
    (h : sf.mem ⊨ (P1 ∗ (∃∗ evs : List AllocEvent,
      Q evs ∗ (withFds A).pool lim (M.stepEvents evs st) sf) ∗ Tail) ∗ R) :
    FdsGe3Closed sf.fs := by
  have hEq1 :
      (P1 ∗ (∃∗ evs : List AllocEvent,
        Q evs ∗ (withFds A).pool lim (M.stepEvents evs st) sf) ∗ Tail) ∗ R =
      (∃∗ evs : List AllocEvent,
        Q evs ∗ (withFds A).pool lim (M.stepEvents evs st) sf) ∗ (P1 ∗ Tail ∗ R) := by
    sep_ac_rfl
  rw [hEq1, sepExists_sepConj_left, satisfies_sepExists] at h
  rcases h with ⟨evs, h⟩
  rw [withFds_pool_enforced A henf] at h
  have hEq2 :
      (Q evs ∗ (⌜FdsGe3Closed sf.fs⌝ ∗ A.pool lim (M.stepEvents evs st) sf)) ∗
        (P1 ∗ Tail ∗ R) =
      ⌜FdsGe3Closed sf.fs⌝ ∗
        ((Q evs ∗ A.pool lim (M.stepEvents evs st) sf) ∗ (P1 ∗ Tail ∗ R)) := by
    sep_ac_rfl
  rw [hEq2, satisfies_pure_sepConj] at h
  exact h.1

private theorem fds_of_dropSpe_post {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {P1 P2 P3 R : SepProp} {st : M.σ} {sf : State}
    (henf : lim.enforced = true)
    (h : sf.mem ⊨ (P1 ∗ P2 ∗ (withFds A).pool lim st sf ∗ P3) ∗ R) :
    FdsGe3Closed sf.fs := by
  rw [withFds_pool_enforced A henf] at h
  have hEq :
      (P1 ∗ P2 ∗ (⌜FdsGe3Closed sf.fs⌝ ∗ A.pool lim st sf) ∗ P3) ∗ R =
      ⌜FdsGe3Closed sf.fs⌝ ∗ ((P1 ∗ P2 ∗ A.pool lim st sf ∗ P3) ∗ R) := by
    sep_ac_rfl
  rw [hEq, satisfies_pure_sepConj] at h
  exact h.1

/-! ## Pure-FS Callee `withFdsGe3Closed` Conversions -/

theorem subroutine_ok_decimal_withFdsGe3Closed_of_withFds [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecEnv : BitVec 32 → List AllocEvent → Prop} {stk : Nat}
    (henf : lim.enforced = true) {P : Program} {entry : BitVec 64}
    (hok : subroutine_ok P entry (decimalSpecPlaced (withFds A) lim DecEnv stk)) :
    subroutine_ok P entry (withFdsGe3Closed (decimalSpecPlaced A lim DecEnv stk)) := by
  refine subroutine_ok_of_pre_post (Q := fun _ _ => True) hok rfl rfl rfl ?_ ?_
  · rintro ⟨x, st⟩ R s0 hpre
    obtain ⟨hClosed0, hpreA⟩ := extract_withFdsGe3Closed hpre
    simp only [decimalSpecPlaced, withLsCodeRoLoaded,
      withFds_pool_eq_of_fds henf hClosed0, withFds_repAlloc] at hpreA ⊢
    exact ⟨trivial, hpreA⟩
  · rintro ⟨x, st⟩ R s0 sf _ hpost
    dsimp only [withFdsGe3Closed, decimalSpecPlaced, withLsCodeRoLoaded] at hpost ⊢
    have hClosedF : FdsGe3Closed sf.fs := fds_of_evs_right4 henf hpost
    simp only [withFds_pool_eq_of_fds henf hClosedF, withFds_repAlloc] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hClosedF, hpost⟩

theorem subroutine_ok_addrText_withFdsGe3Closed_of_withFds [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {AddrEnv : CryptoVerification.LibsignalTripleRatchetRepr.AddrGhost → List AllocEvent → Prop}
    {stk : Nat}
    (henf : lim.enforced = true) {P : Program} {entry : BitVec 64}
    (hok : subroutine_ok P entry (addrTextSpecPlaced (withFds A) lim AddrEnv stk)) :
    subroutine_ok P entry (withFdsGe3Closed (addrTextSpecPlaced A lim AddrEnv stk)) := by
  refine subroutine_ok_of_pre_post (Q := fun _ _ => True) hok rfl rfl rfl ?_ ?_
  · rintro ⟨x, st⟩ R s0 hpre
    obtain ⟨hClosed0, hpreA⟩ := extract_withFdsGe3Closed hpre
    simp only [addrTextSpecPlaced, withLsCodeRoLoaded,
      withFds_pool_eq_of_fds henf hClosed0, withFds_repAlloc] at hpreA ⊢
    exact ⟨trivial, hpreA⟩
  · rintro ⟨x, st⟩ R s0 sf _ hpost
    dsimp only [withFdsGe3Closed, addrTextSpecPlaced, withLsCodeRoLoaded] at hpost ⊢
    have hClosedF : FdsGe3Closed sf.fs := fds_of_evs_right5 henf hpost
    simp only [withFds_pool_eq_of_fds henf hClosedF, withFds_repAlloc] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hClosedF, hpost⟩

theorem subroutine_ok_dirPut_withFdsGe3Closed_of_withFds [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PutEnv : CryptoVerification.SignalSession.Cli.DirGhost → List (BitVec 8) → List (BitVec 8) →
      List AllocEvent → Prop} {stk : Nat}
    (henf : lim.enforced = true) {P : Program} {entry : BitVec 64}
    (hok : subroutine_ok P entry (dirPutSpecPlaced (withFds A) lim PutEnv stk)) :
    subroutine_ok P entry (withFdsGe3Closed (dirPutSpecPlaced A lim PutEnv stk)) := by
  refine subroutine_ok_of_pre_post (Q := fun _ _ => True) hok rfl rfl rfl ?_ ?_
  · rintro ⟨x, st⟩ R s0 hpre
    obtain ⟨hClosed0, hpreA⟩ := extract_withFdsGe3Closed hpre
    simp only [dirPutSpecPlaced, withLsCodeRoLoaded,
      withFds_pool_eq_of_fds henf hClosed0, withFds_repAlloc] at hpreA ⊢
    exact ⟨trivial, hpreA⟩
  · rintro ⟨x, st⟩ R s0 sf _ hpost
    dsimp only [withFdsGe3Closed, dirPutSpecPlaced, withLsCodeRoLoaded] at hpost ⊢
    have hClosedF : FdsGe3Closed sf.fs := fds_of_evs_right6 henf hpost
    simp only [withFds_pool_eq_of_fds henf hClosedF, withFds_repAlloc] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hClosedF, hpost⟩

theorem subroutine_ok_dirPutStr_withFdsGe3Closed_of_withFds [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PutStrEnv : CryptoVerification.SignalSession.Cli.DirGhost → List (BitVec 8) → List (BitVec 8) →
      List AllocEvent → Prop} {stk : Nat}
    (henf : lim.enforced = true) {P : Program} {entry : BitVec 64}
    (hok : subroutine_ok P entry (dirPutStrSpecPlaced (withFds A) lim PutStrEnv stk)) :
    subroutine_ok P entry (withFdsGe3Closed (dirPutStrSpecPlaced A lim PutStrEnv stk)) := by
  refine subroutine_ok_of_pre_post (Q := fun _ _ => True) hok rfl rfl rfl ?_ ?_
  · rintro ⟨x, st⟩ R s0 hpre
    obtain ⟨hClosed0, hpreA⟩ := extract_withFdsGe3Closed hpre
    simp only [dirPutStrSpecPlaced, withLsCodeRoLoaded,
      withFds_pool_eq_of_fds henf hClosed0, withFds_repAlloc] at hpreA ⊢
    exact ⟨trivial, hpreA⟩
  · rintro ⟨x, st⟩ R s0 sf _ hpost
    dsimp only [withFdsGe3Closed, dirPutStrSpecPlaced, withLsCodeRoLoaded] at hpost ⊢
    have hClosedF : FdsGe3Closed sf.fs := fds_of_evs_right6 henf hpost
    simp only [withFds_pool_eq_of_fds henf hClosedF, withFds_repAlloc] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hClosedF, hpost⟩

theorem subroutine_ok_sessDeserialize_withFdsGe3Closed_of_withFds [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (henf : lim.enforced = true) {P : Program} {entry : BitVec 64}
    (hok : subroutine_ok P entry (sessDeserializeSpecPlaced Scope (withFds A) lim DeserEnv)) :
    subroutine_ok P entry
      (withFdsGe3Closed (sessDeserializeSpecPlaced Scope A lim DeserEnv)) := by
  refine subroutine_ok_of_pre_post (Q := fun _ _ => True) hok rfl rfl rfl ?_ ?_
  · rintro ⟨x, st⟩ R s0 hpre
    obtain ⟨hClosed0, hpreA⟩ := extract_withFdsGe3Closed hpre
    simp only [sessDeserializeSpecPlaced, withLsCodeRoLoaded,
      withFds_pool_eq_of_fds henf hClosed0, withFds_repAlloc] at hpreA ⊢
    exact ⟨trivial, hpreA⟩
  · rintro ⟨x, st⟩ R s0 sf _ hpost
    dsimp only [withFdsGe3Closed, sessDeserializeSpecPlaced, withLsCodeRoLoaded] at hpost ⊢
    have hClosedF : FdsGe3Closed sf.fs := fds_of_evs_mid5 henf hpost
    simp only [withFds_pool_eq_of_fds henf hClosedF, withFds_repAlloc] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hClosedF, hpost⟩

theorem subroutine_ok_sessStorePoll_withFdsGe3Closed_of_withFds [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {StoreEnv : CryptoVerification.SignalSession.Cli.SessStorePollGhost → List AllocEvent → Prop}
    {stk : Nat}
    (henf : lim.enforced = true) {P : Program} {entry : BitVec 64}
    (hok : subroutine_ok P entry (sessStorePollSpecPlaced (withFds A) lim StoreEnv stk)) :
    subroutine_ok P entry (withFdsGe3Closed (sessStorePollSpecPlaced A lim StoreEnv stk)) := by
  refine subroutine_ok_of_pre_post (Q := fun _ _ => True) hok rfl rfl rfl ?_ ?_
  · rintro ⟨x, st⟩ R s0 hpre
    obtain ⟨hClosed0, hpreA⟩ := extract_withFdsGe3Closed hpre
    simp only [sessStorePollSpecPlaced, withLsCodeRoLoaded,
      withFds_pool_eq_of_fds henf hClosed0, withFds_repAlloc] at hpreA ⊢
    exact ⟨trivial, hpreA⟩
  · rintro ⟨x, st⟩ R s0 sf _ hpost
    dsimp only [withFdsGe3Closed, sessStorePollSpecPlaced, withLsCodeRoLoaded] at hpost ⊢
    have hClosedF : FdsGe3Closed sf.fs := fds_of_evs_mid9 henf hpost
    simp only [withFds_pool_eq_of_fds henf hClosedF, withFds_repAlloc] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hClosedF, hpost⟩

theorem subroutine_ok_dropSpeWord_withFdsGe3Closed_of_withFds [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (henf : lim.enforced = true) {P : Program} {entry : BitVec 64}
    (hok : subroutine_ok P entry (dropSpeWordSpecPlaced (withFds A) lim)) :
    subroutine_ok P entry (withFdsGe3Closed (dropSpeWordSpecPlaced A lim)) := by
  refine subroutine_ok_of_pre_post (Q := fun _ _ => True) hok rfl rfl rfl ?_ ?_
  · rintro ⟨x, st⟩ R s0 hpre
    obtain ⟨hClosed0, hpreA⟩ := extract_withFdsGe3Closed hpre
    dsimp only [dropSpeWordSpecPlaced, withLsCodeRoLoaded] at hpreA ⊢
    rw [withFds_pool_eq_of_fds henf hClosed0]
    exact ⟨trivial, hpreA⟩
  · rintro ⟨x, st⟩ R s0 sf _ hpost
    dsimp only [withFdsGe3Closed, dropSpeWordSpecPlaced, withLsCodeRoLoaded] at hpost ⊢
    have hClosedF : FdsGe3Closed sf.fs := fds_of_dropSpe_post henf hpost
    rw [withFds_pool_eq_of_fds henf hClosedF] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hClosedF, hpost⟩

theorem subroutine_ok_preKeyDeserialize_withFdsGe3Closed_of_withFds [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (henf : lim.enforced = true) {P : Program} {entry : BitVec 64}
    (hok : subroutine_ok P entry (preKeyDeserializePlacedSpec (withFds A) lim)) :
    subroutine_ok P entry (withFdsGe3Closed (preKeyDeserializePlacedSpec A lim)) := by
  refine subroutine_ok_of_pre_post (Q := fun _ _ => True) hok rfl rfl rfl ?_ ?_
  · rintro ⟨x, st⟩ R s0 hpre
    obtain ⟨hClosed0, hpreA⟩ := extract_withFdsGe3Closed hpre
    dsimp only [preKeyDeserializePlacedSpec, withLsCodeRoLoaded, preKeyDeserializeRawSpec] at hpreA ⊢
    rw [withFds_pool_eq_of_fds henf hClosed0]
    exact ⟨trivial, hpreA⟩
  · rintro ⟨x, st⟩ R s0 sf _ hpost
    dsimp only [withFdsGe3Closed, preKeyDeserializePlacedSpec, withLsCodeRoLoaded,
      preKeyDeserializeRawSpec] at hpost ⊢
    have hClosedF : FdsGe3Closed sf.fs :=
      fds_of_codec_post (Tail := _ ∗ _ ∗ _) henf (by simpa only [sepConj_assoc] using hpost)
    simp only [withFds_pool_eq_of_fds henf hClosedF, withFds_repAlloc] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hClosedF, hpost⟩

theorem subroutine_ok_identityKeyPairTryFrom_withFdsGe3Closed_of_withFds [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (henf : lim.enforced = true) {P : Program} {entry : BitVec 64}
    (hok : subroutine_ok P entry (identityKeyPairTryFromPlacedSpec (withFds A) lim)) :
    subroutine_ok P entry (withFdsGe3Closed (identityKeyPairTryFromPlacedSpec A lim)) := by
  refine subroutine_ok_of_pre_post (Q := fun _ _ => True) hok rfl rfl rfl ?_ ?_
  · rintro ⟨x, st⟩ R s0 hpre
    obtain ⟨hClosed0, hpreA⟩ := extract_withFdsGe3Closed hpre
    dsimp only [identityKeyPairTryFromPlacedSpec, withLsCodeRoLoaded,
      identityKeyPairTryFromRawSpec] at hpreA ⊢
    rw [withFds_pool_eq_of_fds henf hClosed0]
    exact ⟨trivial, hpreA⟩
  · rintro ⟨x, st⟩ R s0 sf _ hpost
    dsimp only [withFdsGe3Closed, identityKeyPairTryFromPlacedSpec, withLsCodeRoLoaded,
      identityKeyPairTryFromRawSpec] at hpost ⊢
    have hClosedF : FdsGe3Closed sf.fs :=
      fds_of_codec_post (Tail := _ ∗ _ ∗ _ ∗ _) henf (by simpa only [sepConj_assoc] using hpost)
    simp only [withFds_pool_eq_of_fds henf hClosedF, withFds_repAlloc] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hClosedF, hpost⟩

theorem subroutine_ok_decodeKyberPreKey_withFdsGe3Closed_of_withFds [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (henf : lim.enforced = true) {P : Program} {entry : BitVec 64}
    (hok : subroutine_ok P entry (decodeKyberPreKeyPlacedSpec (withFds A) lim)) :
    subroutine_ok P entry (withFdsGe3Closed (decodeKyberPreKeyPlacedSpec A lim)) := by
  refine subroutine_ok_of_pre_post (Q := fun _ _ => True) hok rfl rfl rfl ?_ ?_
  · rintro ⟨x, st⟩ R s0 hpre
    obtain ⟨hClosed0, hpreA⟩ := extract_withFdsGe3Closed hpre
    dsimp only [decodeKyberPreKeyPlacedSpec,
      CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded,
      decodeKyberPreKeyRawSpec] at hpreA ⊢
    rw [withFds_pool_eq_of_fds henf hClosed0]
    exact ⟨trivial, hpreA⟩
  · rintro ⟨x, st⟩ R s0 sf _ hpost
    dsimp only [withFdsGe3Closed, decodeKyberPreKeyPlacedSpec,
      CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded,
      decodeKyberPreKeyRawSpec] at hpost ⊢
    have hClosedF : FdsGe3Closed sf.fs :=
      fds_of_codec_post (Tail := _ ∗ _ ∗ _) henf (by simpa only [sepConj_assoc] using hpost)
    simp only [withFds_pool_eq_of_fds henf hClosedF, withFds_repAlloc] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hClosedF, hpost⟩

theorem subroutine_ok_decodeSignedPreKey_withFdsGe3Closed_of_withFds [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (henf : lim.enforced = true) {P : Program} {entry : BitVec 64}
    (hok : subroutine_ok P entry (decodeSignedPreKeyPlacedSpec (withFds A) lim)) :
    subroutine_ok P entry (withFdsGe3Closed (decodeSignedPreKeyPlacedSpec A lim)) := by
  refine subroutine_ok_of_pre_post (Q := fun _ _ => True) hok rfl rfl rfl ?_ ?_
  · rintro ⟨x, st⟩ R s0 hpre
    obtain ⟨hClosed0, hpreA⟩ := extract_withFdsGe3Closed hpre
    dsimp only [decodeSignedPreKeyPlacedSpec,
      CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded,
      decodeSignedPreKeyRawSpec] at hpreA ⊢
    rw [withFds_pool_eq_of_fds henf hClosed0]
    exact ⟨trivial, hpreA⟩
  · rintro ⟨x, st⟩ R s0 sf _ hpost
    dsimp only [withFdsGe3Closed, decodeSignedPreKeyPlacedSpec,
      CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded,
      decodeSignedPreKeyRawSpec] at hpost ⊢
    have hClosedF : FdsGe3Closed sf.fs :=
      fds_of_codec_post (Tail := _ ∗ _ ∗ _) henf (by simpa only [sepConj_assoc] using hpost)
    simp only [withFds_pool_eq_of_fds henf hClosedF, withFds_repAlloc] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hClosedF, hpost⟩

/-! ## Top-Level `CliDecPkPollKitsPlacedOkFds` Dischargers -/

private theorem cliGhostExterns_bcmp_keepsFs_sat (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W))
      CryptoVerification.SignalSession.Cli.cliBcmpName
      (LibsignalBinary.Heap.SpecBudget.withVmPreserved
        CryptoVerification.SignalSession.Cli.cliBcmpSpec).keepsFs := by
  refine CryptoVerification.SignalSession.Cli.Slots.cliGhostExterns_sat_of_cliExternsPlaced
    mmpl g W ?_
  rcases LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget.cliExternsPlaced_bcmp_budget_sat
    mmpl W with ⟨f, hf, hok⟩
  have hbcmp := CryptoVerification.SignalSession.Cli.RunGlue.cliExternsPlaced_bcmp mmpl W
  rw [hbcmp] at hf
  injection hf with hfg
  subst hfg
  exact ⟨_, hbcmp, hok.keepsFs fun _ => rfl⟩

/-- Parametric `B : RunBudgets` and `DeserEnv` discharger for `CliDecPkPollKitsPlacedOkFds` from
`RunHooksPlaced`, `withLsRetAddr624AndFds` `read_file` `HookSat`, `sessDeserialize` (block 46), and
`serializeCanonSpecX` (block 52) at `withFds A`. -/
theorem cliDecPkPollKitsPlacedOkFds_of_deps [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {B : RunBudgets}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {deserProg serProg : Program} {deserBlk serBlk : Nat}
    [IsLsBlockProg deserProg deserBlk (cliGhostExterns g (cliExternsPlaced mmpl W))]
    [IsLsBlockProg serProg serBlk (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (henf : lim.enforced = true)
    (hh : RunHooksPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hReadSat : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsReadFileSym
      (withLsRetAddr624AndFds
        (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv)))
    (hDeser : subroutine_ok deserProg (lsmpl.base 46)
      (withFdsGe3Closed (sessDeserializeSpecPlaced scopeKit A lim DeserEnv)))
    (hSer : subroutine_ok serProg (lsmpl.base 52)
      (withLsCodeLoaded lsmpl (serializeCanonSpecX M (withFds A) lim)))
    (hDeserBlk : deserBlk < 619 := by decide)
    (hDeserUnmut : (deserBlk ∈ CryptoVerification.libsignalMutatedBlocks) = false := by decide)
    (hSerBlk : serBlk < 619 := by decide)
    (hSerUnmut : (serBlk ∈ CryptoVerification.libsignalMutatedBlocks) = false := by decide) :
    CliDecPkPollKitsPlacedOkFds A lim B ReadEnv DeserEnv
      (cliGhostExterns g (cliExternsPlaced mmpl W)) := by
  let H := cliGhostExterns g (cliExternsPlaced mmpl W)
  have hsh := sessKitHooksPlaced_withFds_of_runHooks hh
  have hc := codecHooksPlaced_withFds hh.codecHooks
  have hBcmpFs := cliGhostExterns_bcmp_keepsFs_sat mmpl g W
  have hBb := cliGhostExterns_blackBox mmpl g W
  have hPath596 := path_placed_caller_ok_of_allocFs_fd
    (callerProg := lsProg_596 H) (i := 596) (resStack := doReserveStackX)
    hh.allocFs (by decide) (Nat.le_refl pathNeed)
    (hh.panics handleErrorSymCli (by decide)) (by decide)
  have hGet589 := dirGet_placed_ok_of_deps_fd
    (fun _ hp => hp.2) hh.allocFs hBcmpFs
    (pathProg := lsProg_596 H) (jPath := 596) (by decide) (by decide)
    hPath596 hReadSat (hh.fs (lsProg_589 H) 589) (Nat.le_refl B.dirGetNeed)
    (fun _ _ _ _ hm => hm)
  have hDec597_wf := cliDecimal_placed_ok_of_sessHooks hsh
  have hDec597 := subroutine_ok_decimal_withFdsGe3Closed_of_withFds henf hDec597_wf
  have hAddr594_wf := cliAddrText_placed_ok_of_sessHooks hsh
  have hAddr594 := subroutine_ok_addrText_withFdsGe3Closed_of_withFds henf hAddr594_wf
  have hPut542_wf := cliDirPut_placed_ok_of_sessHooks hsh
  have hPut542 := subroutine_ok_dirPut_withFdsGe3Closed_of_withFds henf hPut542_wf
  have hPutStr543 := subroutine_ok_dirPutStr_withFdsGe3Closed_of_withFds henf
    (cliDirPutStr_placed_ok_of_sessHooks hsh)
  have hDrop553 := subroutine_ok_dropSpeWord_withFdsGe3Closed_of_withFds henf
    (dropSpeWord_placed_ok hsh.alloc)
  have hPkDec65 := subroutine_ok_preKeyDeserialize_withFdsGe3Closed_of_withFds henf
    (preKeyRecord_deserialize_placed_ok_of_hooks hc)
  have hIkp84 := subroutine_ok_identityKeyPairTryFrom_withFdsGe3Closed_of_withFds henf
    (identityKeyPair_tryFrom_placed_ok_of_hooks hc)
  have hSpkDec595 := subroutine_ok_decodeSignedPreKey_withFdsGe3Closed_of_withFds henf
    (decodeSignedPreKey_placed_ok (signedHooksPlaced_of_codecHooks hc) (signedPortDepsPlaced_ok hc))
  have hKpkDec595 := subroutine_ok_decodeKyberPreKey_withFdsGe3Closed_of_withFds henf
    (decodeKyberPreKey_placed_ok (signedHooksPlaced_of_codecHooks hc) (signedPortDepsPlaced_ok hc))
  have h569 := sessLoadPoll_placed_ok_of_deps_fd
    (addrProg := lsProg_594 H) (addrBlk := 594)
    (getProg := lsProg_589 H) (getBlk := 589)
    (deserProg := deserProg) (deserBlk := deserBlk)
    hh.allocFs hAddr594 hGet589 hDeser (hh.fs (lsProg_569 H) 569) (Nat.le_refl _)
    (by decide) (by decide) (by decide) (by decide) hDeserBlk hDeserUnmut
  have h570_wf := sessStorePoll_placed_ok_of_depsX
    (addrProg := lsProg_594 H) (addrBlk := 594)
    (serProg := serProg) (serBlk := serBlk)
    (putProg := lsProg_570 H) (putBlk := 570)
    hsh.alloc hAddr594_wf hSer hPut542_wf (Nat.le_refl _)
    (by decide) (by decide) hSerBlk hSerUnmut (by decide) (by decide)
  have h570 := subroutine_ok_sessStorePoll_withFdsGe3Closed_of_withFds henf h570_wf
  have h566 := idTrustPoll_placed_ok_of_get_bb_fd
    (getProg := lsProg_589 H) (getBlk := 589)
    hh.allocFs hGet589 hBb (Nat.le_refl _) (by decide) (by decide)
  have h565 := idSavePoll_placed_ok_of_get_put_bb_fd
    (getProg := lsProg_589 H) (getBlk := 589)
    (putProg := lsProg_543 H) (putBlk := 543)
    hh.allocFs hGet589 hPutStr543 hBb (Nat.le_refl _)
    (by decide) (by decide) (by decide) (by decide)
  have h567 := idKeyPairPoll_placed_ok_of_deps_fd
    hh.allocFs
    (LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetFd.dirGet_placed_caller_ok_of_deps_fd
      (callerProg := lsProg_567 H) (i := 567)
      (fun _ hp => hp.2) hh.allocFs hBcmpFs
      (pathProg := lsProg_596 H) (jPath := 596) (by decide) (by decide)
      hPath596 hReadSat (hh.fs (lsProg_589 H) 589) (Nat.le_refl B.dirGetNeed)
      (fun _ _ _ _ hm => hm) (by decide))
    (ls_transfer_withFdsGe3Closed_lscro
      (callerProg := lsProg_567 H) (i := 567) (j := 84) hIkp84 (by decide) (by decide) (by decide))
    (Nat.le_refl _)
  have h568 := idRegIdPoll_placed_ok_of_deps_fd
    hh.allocFs
    (LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetFd.dirGet_placed_caller_ok_of_deps_fd
      (callerProg := lsProg_568 H) (i := 568)
      (fun _ hp => hp.2) hh.allocFs hBcmpFs
      (pathProg := lsProg_596 H) (jPath := 596) (by decide) (by decide)
      hPath596 hReadSat (hh.fs (lsProg_589 H) 589) (Nat.le_refl B.dirGetNeed)
      (fun _ _ _ _ hm => hm) (by decide))
    (Nat.le_refl _)
  have h571 := spkGetPoll_placed_fs_ok_of_deps_fd
    (decProg := lsProg_597 H) (decBlk := 597)
    (getProg := lsProg_589 H) (getBlk := 589)
    (spkDecProg := lsProg_595 H) (spkDecBlk := 595)
    (dropProg := lsProg_553 H) (dropBlk := 553)
    hh.allocFs hDec597 hGet589 hSpkDec595 hDrop553 (hh.fs (lsProg_571 H) 571)
    (Nat.le_refl _) (fun _ _ => Or.inl) (fun _ _ => Or.inr)
  have h576 := kpkGetPoll_placed_fs_ok_of_deps_fd
    (decProg := lsProg_597 H) (decBlk := 597)
    (getProg := lsProg_589 H) (getBlk := 589)
    (decodeProg := lsProg_595 H) (decodeBlk := 595)
    hh.allocFs hDec597 hGet589 hKpkDec595 (hh.fs (lsProg_576 H) 576)
    (Nat.le_refl _) (fun _ _ => Or.inl) (fun _ _ => Or.inr)
  have h578 := kpkMarkPoll_placed_ok_of_deps_fd
    (decProg := lsProg_597 H) (decBlk := 597)
    (getProg := lsProg_589 H) (getBlk := 589)
    (putProg := lsProg_570 H) (putBlk := 570)
    hh.allocFs hh.panics hBcmpFs hDec597 hGet589 hPut542 (hh.fs (lsProg_578 H) 578)
    (Nat.le_refl _)
  have h573 := pkGetPoll_placed_fs_ok_of_deps_fd
    (decProg := lsProg_597 H) (decBlk := 597)
    (getProg := lsProg_589 H) (getBlk := 589)
    (pkDecProg := lsProg_65 H) (pkDecBlk := 65)
    (dropProg := lsProg_553 H) (dropBlk := 553)
    hh.allocFs hDec597 hGet589 hPkDec65 hDrop553 (hh.fs (lsProg_573 H) 573)
    (Nat.le_refl _) (fun _ _ => Or.inl) (fun _ _ => Or.inr)
  have h575 := pkRemovePoll_placed_ok_of_deps_fd
    (decProg := lsProg_597 H) (decBlk := 597)
    (getProg := lsProg_589 H) (getBlk := 589)
    (putProg := lsProg_570 H) (putBlk := 570)
    hh.allocFs hDec597 hGet589 hPut542 (hh.fs (lsProg_575 H) 575)
    (Nat.le_refl _)
  exact cliDecPkPollKitsPlacedOkFds_of_polls
    hDropNz hh.allocFs h569 h570 h566 h565 h567 h568 h571 h576 h578 h573 h575

/-- Closed discharger for `CliDecPkPollKitsPlacedOkFds` from `CliRunHooksBundleFd` at
`cliRunBudgets` and `SessDeserializeCancelEnv`. -/
theorem cliDecPkPollKitsPlacedOkFds_of_runHooksBundleFd [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} [HasFineReallocCredit M]
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (henf : lim.enforced = true)
    (hG : CliGhostAllocHooks M A lim g)
    (hHooks : CliRunHooksBundleFd mmpl g W A lim ReadEnv) :
    CliDecPkPollKitsPlacedOkFds A lim cliRunBudgets ReadEnv SessDeserializeCancelEnv
      (cliGhostExterns g (cliExternsPlaced mmpl W)) := by
  have hG_wf := cliGhostAllocHooks_withFds hG
  have hDeser := subroutine_ok_sessDeserialize_withFdsGe3Closed_of_withFds henf
    (sessDeserialize_cli_dcan_placed_ok mmpl g W hG_wf (fun _ hr => hr))
  have hSer := serializeCanonX_cli_placed mmpl g W hG_wf
  exact cliDecPkPollKitsPlacedOkFds_of_deps
    (deserProg := lsProg_46 (cliGhostExterns g (cliExternsPlaced mmpl W))) (deserBlk := 46)
    (serProg := lsProg_52 (cliGhostExterns g (cliExternsPlaced mmpl W))) (serBlk := 52)
    mmpl g W hDropNz henf hHooks.runHooks hHooks.readFileSat hDeser hSer
    (by decide) (by decide) (by decide) (by decide)

end LibsignalBinary.Proofs.SignalSession.Cli.KitInst.DecPkPollKitsInstPlacedBudgetFd
