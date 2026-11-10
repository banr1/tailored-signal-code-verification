/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.W3InitiateEnvBridges
public import LibsignalBinary.Proofs.PeakBudget.W4OuterEnvBridges
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.SessionDeserProfile
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.SessionDeserializeBudget
public import LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeserAux
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# `sessDeserEvents` Bridges for CLI `load_session` & `SessionStore`

Connects the relocatable `SessionRecord::deserialize` contract (`sessDeserialize_budget_placed_ok`
on Block `46`, exact trace `sessDeserEvents x.r` on `DeserializeScopeP_Q NonEmptyV1Q`) into
`SpecsPlacedBudget.sessDeserializeSpecPlaced`, `LoadPollPlacedBudget` (Block `569`),
`SessionOnlyKitPlacedOkSE`, and peak/group credit bounds for `cliSessionKitDefaultBudgetEnv`,
instantiated at `SessDeserializeCancelEnv`, `RecordDeserializeCancelEnv`, `SessDeserSetBEnv`, and
`SessDeserSetAEnv`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser

open Arm64 ProofLib SepProp
open Arm64.Process (bytesOfString)
open CryptoGames.LibsignalSession (IdentityKey)
open CryptoGames.LibsignalSessionApi (Direction SessionRecord)
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement libsignalMutatedBlocks lsmpl lsρ
   withLsCodeLoaded)
open CryptoVerification.E2E (PEParams)
open CryptoVerification.E2E.Record (encodeRecord recDeserializeStack)
open CryptoVerification.E2E.Record.Placed (lsProg_46)
open CryptoVerification.E2E.Record.Serialization (CanonRecord)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles IdentityStoreSpec SessionStoreSpec TraceFsSound extract_withLsCodeRoLoaded
   withLsCodeRoLoaded)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal RecordGhost sessionRecordAt)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost uuidTryParse)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession
  (CliHooks CliPqxdhInputs Inputs cliExternsPlaced lsReadFileSym)
open CryptoVerification.SignalSession.Cli (DirGhost ReadRule StoresGhost addressText pathOf)
open CryptoVerification.SignalSession.Cli.KitInst (cliSessionKitSpecPlaced)
open CryptoVerification.SignalSession.Cli.KitInst.SessKit
  (loadPollNeedPlaced loadShimNeedPlaced storePollNeedXPlaced storeShimNeedPlaced)
open CryptoVerification.SignalSession.Cli.MainHops (AddrV CallV cliIo cliWrOk parseArgs)
open CryptoVerification.SignalSession.Cli.Placed (lsProg_569)
open CryptoVerification.SignalSession.Cli.RunCompose (addrValOf callPeer runFiles)
open CryptoVerification.SignalSession.Cli.RunGlue
  (CliGhostHooks IsFsC allocZeroedHook0_fsT cliExternsPlaced_row cliGhostExterns
   cliGhostExterns_other cliGhostExterns_shim)
open CryptoVerification.SignalSession.Cli.Slots
  (FilesOkPeer cliGhostExterns_panic_handle_alloc_error cliGhostExterns_panic_handle_error
   scopeKit)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon (ls_transfer_lscro)
open Symbolic.Swarm.TRREF.B3Defs (DeserializeScopeP_Q NonEmptyV1Q)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs RustCliAllocBudget SeqEnv)
open LibsignalBinary.Heap.Fine (FineScale fineCostModel)
open LibsignalBinary.Heap.Fine.ClientBounds
  (fineCostModel_largeCost_eq fineCostModel_smallMaxReq_eq)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (StringCloneEnv)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps (DirDomainCaps addressText_length_le)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith (cliBudgetLimits)
open LibsignalBinary.Proofs.PeakBudget.CliGroupBounds (cliSessLoadPollEnv_groupSpec)
open LibsignalBinary.Proofs.PeakBudget.DirPeakSpec (CliAddrTextEnv CliDirGetEnv)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit
  (HasFineGroupCredit PhaseGroupSpec fitsEnv_fineCostModel_of_phaseCredit_groups)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (ModelHyps PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
  (fineCostModel_freeNonInc fineCostModel_modelHyps)
open LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
  (CliSessLoadPollEnv fineReadFileCum fineReadFileLive fineReadFileMaxReq fineReadFilePeak
   optLargeCost optLargeCost_fine_mono optLargeCost_fine_of_gt
   sessLoadPollTightDeltaCum sessLoadPollTightDeltaLive sessLoadPollTightDeltaPeak
   sessLoadPollTightMaxReq sessLoadPoll_phaseCredit_tight)
open LibsignalBinary.Proofs.PeakBudget.W3InitiateEnvBridges (loadStep_phaseCredit)
open LibsignalBinary.Proofs.PeakBudget.W3InitiatePeakSpec
  (w3BoxedStepCum w3BoxedStepLive w3BoxedStepMaxReq w3BoxedStepPeak)
open LibsignalBinary.Proofs.PeakBudget.W4OuterHelpers
  (stringClone_phaseCredit_aff stringClone_phaseCredit_small)
open LibsignalBinary.Proofs.PeakBudget.W4OuterStageHelpers
  (boxedDeallocPred_to_w4BoxedStoreStep loadStepEnv_phaseCredit phaseCreditSpec_seq_freeOnly_exact
   rustDealloc8_freeOnly trustStepEnv_phaseCredit w4BoxedStepCum w4BoxedStepLive w4BoxedStepMaxReq
   w4BoxedStepPeak w4BoxedStoreStep_small_phaseCredit)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget
  (IdentityStoreBudgetEnv TrustStepEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (SessionOnlyKitPlacedOkSE)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget
  (LoadStepEnv SessionStoreBudgetEnv)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.HookLift
  (AllocContractsBudgetPlaced)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.SessionDeserProfile
  (SessDeserSetAEnv SessDeserSetBEnv cliPqxdhInputs_sessGet_empty_or_scopeKit
   filesOkPeer_scopeKit_of_cliPqxdhInputs sessDeserEvents_deserBoundedTotalEvs_of_scope
   sessDeserEvents_deserBoundedTotalEvs_setA_of_scope sessGet_empty_or_scopeKit_of_filesOkPeer)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.SessionDeserializeBudget
  (sessDeserEvents sessDeserializeBudgetPlacedSpec sessDeserializeBudgetRawSpec
   sessDeserialize_budget_placed_ok_of_sub)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget (serializeCanonSpecX)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget
  (RecordDeserializeCancelEnv SessDeserializeCancelEnv deserCancelFineCum deserCancelFineGroups
   deserCancelFineGrpS deserCancelFineLive deserCancelFineMaxReq deserCancelFinePeak
   nil_mem_recordDeserializeCancelEnv recordDeserializeCancelEnv_fine_groupSpec
   recordDeserializeCancelEnv_fine_groupSpec_p16_48 recordDeserializeCancelEnv_fine_groupSpec_p64
   recordDeserializeCancelEnv_fine_groupSpec_p192 recordDeserializeCancelEnv_fine_phaseCreditSpec
   recordDeserializeCancelEnv_fine_phaseCreditSpec_p64
   recordDeserializeCancelEnv_fine_phaseCreditSpec_p192 sessDeserEvents_mem_recordDeserializeCancelEnv
   sessDeserEvents_mem_sessDeserializeCancelEnv sessDeserializeCancelEnv_fine_groupSpec
   sessDeserializeCancelEnv_fine_phaseCreditSpec sessDeserializeCancelEnv_imp_recordDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget (DecimalEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a (DirGetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget (PathEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
  (AddrTextValEnv SessionOnlyKitPlacedRoClOkSE SessKitHooksPlaced cliSessKitOkSE_cli_placed
   cliSessKitOkSE_cli_placed_of_readHook cliSessKitOkSE_placed cliSessKitOkSE_placed_of_sessHooks
   cliSessionKitBudgetEnv cliSessionKitDefaultBudgetEnv cliSessionKitLoadPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliAllocHooks CliGhostAllocHooks bumpGhost cliExternsPlaced_alloc_budget_sat
   cliExternsPlaced_dealloc_budget_sat cliExternsPlaced_realloc_budget_sat
   cliExternsPlaced_sessionMemcpy_budget_sat cliExternsPlaced_shim_budget_sat
   cliGhostAllocHooks_bumpGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsXCliPlaced ReadFileRuleEnv addrTextSpecPlaced dirGetSpecPlaced readFileSpecPlaced
   sessDeserializeSpecPlaced sessLoadPollSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPoll.LayoutPlacedBudget
  (CliLoadPollEnv OptLoadDeserEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollPlacedBudget
  (sessLoadPoll_placed_caller_ok_of_deps sessLoadPoll_placed_ok_of_deps)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeserAux
  (addrTextValEnv_decimal_fine_groupSpec addrTextValEnv_decimal_fine_phaseCredit_tight
   addrTextValEnv_decimal_groupSpec dirGetEnv_path_readFile_fine_phaseCredit_tight
   dirGetEnv_path_readFile_groupSpec seq_freeOnly_phaseCredit)

/-! ## Section 1: `AllocContractsBudgetPlaced` & Block `46` `sessDeserEvents` Subroutine Bridges -/

/-- Lift an event-only predicate `P : List AllocEvent → Prop` to a `SessionRecord`-indexed deserialize envelope. -/
abbrev ofEventPred (P : List AllocEvent → Prop) :
    SessionRecord (List (BitVec 8)) → List AllocEvent → Prop :=
  fun _ evs => P evs

/-- Lift a wire-slice-indexed predicate `DeserByBytesEnv : List (BitVec 8) → List AllocEvent → Prop`
to a `SessionRecord`-indexed deserialize envelope via `encodeRecord`. -/
abbrev ofBytesEnv (DeserByBytesEnv : List (BitVec 8) → List AllocEvent → Prop) :
    SessionRecord (List (BitVec 8)) → List AllocEvent → Prop :=
  fun r evs => DeserByBytesEnv (encodeRecord r) evs

/-- Exact deterministic `SessionRecord::deserialize` event envelope (`evs = sessDeserEvents r`). -/
def SessDeserExactEnv (r : SessionRecord (List (BitVec 8))) (evs : List AllocEvent) : Prop :=
  evs = sessDeserEvents r

/-- `CliGhostAllocHooks M A lim g` discharges `DeserBudget.HookLift.AllocContractsBudgetPlaced` at
`cliGhostExterns g (cliExternsPlaced mmpl W)`. -/
theorem allocContractsBudgetPlaced_cli [LibsignalPlacement] (mmpl : Arm64.Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim g) :
    AllocContractsBudgetPlaced M A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  AllocContractsBudgetPlaced.of_hooks
    (cliExternsPlaced_alloc_budget_sat mmpl g W hG)
    (cliExternsPlaced_dealloc_budget_sat mmpl g W hG)
    (cliExternsPlaced_realloc_budget_sat mmpl g W hG)
    (cliExternsPlaced_shim_budget_sat mmpl g W hG.shim_eq)
    (cliExternsPlaced_sessionMemcpy_budget_sat mmpl g W hG extHookStack)
    (cliGhostExterns_panic_handle_error mmpl g W)
    (cliGhostExterns_panic_handle_alloc_error mmpl g W)

/-- Block `46` (`lsProg_46 H`) satisfies `SpecsPlacedBudget.sessDeserializeSpecPlaced` for any `DeserEnv`
closed under `sessDeserEvents` on `Scope ⊆ DeserializeScopeP_Q NonEmptyV1Q` (`= Slots.scopeKit`). -/
theorem sessDeserialize_of_sessDeserEvents_placed_ok [LibsignalPlacement]
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {M : AllocCostModel} [HasFineReallocCredit M]
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (hA : AllocContractsBudgetPlaced M A lim H)
    (hsub : ∀ r, Scope r → DeserializeScopeP_Q NonEmptyV1Q r)
    (hMem : ∀ r, Scope r → DeserEnv r (sessDeserEvents r)) :
    subroutine_ok (lsProg_46 H) (lsmpl.base 46)
      (sessDeserializeSpecPlaced Scope A lim DeserEnv) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  obtain ⟨hcrl, hrest⟩ := extract_withLsCodeRoLoaded hpre
  dsimp only [sessDeserializeSpecPlaced] at hrest
  rw [sepConj_assoc, satisfies_pure_sepConj] at hrest
  obtain ⟨⟨hx0, hx1, hx8, hsc, hfitEnv⟩, hmem⟩ := hrest
  have hMemEvs : DeserEnv x.r (sessDeserEvents x.r) := hMem x.r hsc
  have hfitEvs : FitsEvents M lim st (sessDeserEvents x.r) := hfitEnv (sessDeserEvents x.r) hMemEvs
  have hpre_b : s0.mem ⊨ (sessDeserializeBudgetPlacedSpec Scope M A lim).pre (x, st) s0 ∗ R := by
    dsimp only [sessDeserializeBudgetPlacedSpec,
      CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded, sessDeserializeBudgetRawSpec]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨⟨hcrl.1, hcrl.2⟩, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx8, hsc, hfitEvs⟩, hmem⟩
  refine (sessDeserialize_budget_placed_ok_of_sub hA hsub).mono_outcome
    (x, st) R s0 hpc hrun hpre_b hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [sessDeserializeBudgetPlacedSpec,
      CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded,
      sessDeserializeBudgetRawSpec] at hpost
    have hpost1 : sf.mem ⊨
        ⌜sf.trace = s0.trace⌝ ∗
        ((∃∗ g : RecordGhost,
            ⌜CanonRecord g x.r ∧
              (∀ G, g.cur = some G →
                (∀ s_sess, x.r.currentSession = some s_sess →
                  LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.Potential.ssStateLargeLive
                    M G s_sess.state =
                  LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.Potential.ssLargeLive M G) ∧
                (33 ≤ HasFineReallocCredit.smallMaxReq M →
                  LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.Potential.ssLargeLive M G =
                  LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.SessionDeserializeBudget.sessDeserLargeLive
                    M x.r))⌝ ∗
            sessionRecordAt A.repAlloc x.out g x.r) ∗
          ((x.p ↦ₛ encodeRecord x.r) ∗
            A.pool lim (M.stepEvents (sessDeserEvents x.r) st) sf ∗
            stackAt s0.sp recDeserializeStack ∗ R)) :=
      Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hpost
    rw [satisfies_pure_sepConj] at hpost1
    obtain ⟨htr, hpost2⟩ := hpost1
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost2
    obtain ⟨g, hg⟩ := hpost2
    rw [sepConj_assoc, satisfies_pure_sepConj] at hg
    obtain ⟨⟨hcanon, _⟩, hspatial⟩ := hg
    dsimp only [sessDeserializeSpecPlaced, withLsCodeRoLoaded]
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨sessDeserEvents x.r, ?_⟩
    have hgoal : sf.mem ⊨
        ⌜sf.trace = s0.trace ∧ DeserEnv x.r (sessDeserEvents x.r)⌝ ∗
        ((∃∗ g' : RecordGhost, ⌜CanonRecord g' x.r⌝ ∗
            CryptoVerification.E2E.Record.sessionRecordAt A.repAlloc x.out g' x.r) ∗
          ((x.p ↦ₛ encodeRecord x.r) ∗
            A.pool lim (M.stepEvents (sessDeserEvents x.r) st) sf ∗
            stackAt s0.sp recDeserializeStack ∗ R)) := by
      rw [satisfies_pure_sepConj]
      refine ⟨⟨htr, hMemEvs⟩, ?_⟩
      rw [sepExists_sepConj_left, satisfies_sepExists]
      refine ⟨g, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hcanon, hspatial⟩
    exact Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hgoal
  · dsimp only [sessDeserializeBudgetPlacedSpec,
      CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [sessDeserializeBudgetPlacedSpec,
      CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [sessDeserializeBudgetPlacedSpec,
      CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded] at hq
    exact (not_satisfies_false_sepConj hq).elim

theorem sessDeserialize_of_sessDeserEvents_caller_ok [LibsignalPlacement]
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {M : AllocCostModel} [HasFineReallocCredit M]
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hA : AllocContractsBudgetPlaced M A lim H)
    (hsub : ∀ r, Scope r → DeserializeScopeP_Q NonEmptyV1Q r)
    (hMem : ∀ r, Scope r → DeserEnv r (sessDeserEvents r))
    (hCallerBlk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 46)
      (sessDeserializeSpecPlaced Scope A lim DeserEnv) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 46)
    (sessDeserialize_of_sessDeserEvents_placed_ok hA hsub hMem) hCallerBlk (by decide) (by decide)

theorem sessDeserialize_cli_of_sessDeserEvents_placed_ok [LibsignalPlacement]
    (mmpl : Arm64.Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {M : AllocCostModel} [HasFineReallocCredit M]
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (hG : CliGhostAllocHooks M A lim g) (hsub : ∀ r, Scope r → scopeKit r)
    (hMem : ∀ r, Scope r → DeserEnv r (sessDeserEvents r)) :
    subroutine_ok (lsProg_46 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced Scope A lim DeserEnv) :=
  sessDeserialize_of_sessDeserEvents_placed_ok (allocContractsBudgetPlaced_cli mmpl g W hG)
    hsub hMem

/-- Exact-trace (`SessDeserExactEnv`) specialization of
`sessDeserialize_of_sessDeserEvents_placed_ok` requiring zero envelope-membership proof. -/
theorem sessDeserialize_exact_placed_ok [LibsignalPlacement]
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {M : AllocCostModel} [HasFineReallocCredit M]
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H) (hsub : ∀ r, Scope r → scopeKit r) :
    subroutine_ok (lsProg_46 H) (lsmpl.base 46)
      (sessDeserializeSpecPlaced Scope A lim SessDeserExactEnv) :=
  sessDeserialize_of_sessDeserEvents_placed_ok hA hsub (fun _ _ => rfl)

theorem sessDeserialize_cli_of_eventPred_placed_ok [LibsignalPlacement]
    (mmpl : Arm64.Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {M : AllocCostModel} [HasFineReallocCredit M]
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {P : List AllocEvent → Prop}
    (hG : CliGhostAllocHooks M A lim g) (hsub : ∀ r, Scope r → scopeKit r)
    (hMem : ∀ r, Scope r → P (sessDeserEvents r)) :
    subroutine_ok (lsProg_46 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced Scope A lim (ofEventPred P)) :=
  sessDeserialize_cli_of_sessDeserEvents_placed_ok mmpl g W hG hsub hMem

theorem sessDeserialize_cli_of_bytesEnv_placed_ok [LibsignalPlacement]
    (mmpl : Arm64.Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {M : AllocCostModel} [HasFineReallocCredit M]
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DeserByBytesEnv : List (BitVec 8) → List AllocEvent → Prop}
    (hG : CliGhostAllocHooks M A lim g) (hsub : ∀ r, Scope r → scopeKit r)
    (hMem : ∀ r, Scope r → DeserByBytesEnv (encodeRecord r) (sessDeserEvents r)) :
    subroutine_ok (lsProg_46 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced Scope A lim (ofBytesEnv DeserByBytesEnv)) :=
  sessDeserialize_cli_of_sessDeserEvents_placed_ok mmpl g W hG hsub hMem

/-! ## Section 2: Block `569` `LoadPoll` & `SessionOnlyKitPlacedOkSE` Assembly Without `hDeser` -/

/-- Block `569` (`load_session::{closure#0}`) meets `sessLoadPollSpecPlaced` with Block `46`
discharged internally from `AllocContractsBudgetPlaced` + `sessDeserEvents` membership. -/
theorem sessLoadPoll_of_sessDeserEvents_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} [HasFineReallocCredit M]
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {AddrEnv : AddrGhost → List AllocEvent → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {addrProg getProg : Program} {addrBlk getBlk : Nat}
    [IsLsBlockProg addrProg addrBlk H] [IsLsBlockProg getProg getBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {addrStk getStk stk : Nat}
    (hC : AllocContractsXCliPlaced A lim H) (hAB : AllocContractsBudgetPlaced M A lim H)
    (hAddr : subroutine_ok addrProg (lsmpl.base 594) (addrTextSpecPlaced A lim AddrEnv addrStk))
    (hGet : subroutine_ok getProg (lsmpl.base 589) (dirGetSpecPlaced rd pathOk A lim GetEnv getStk))
    (hsub : ∀ r, Scope r → scopeKit r) (hMem : ∀ r, Scope r → DeserEnv r (sessDeserEvents r))
    (hFs : TraceFsSound (lsProg_569 H))
    (hstk : 0x350 + max (max addrStk getStk) (max recDeserializeStack extHookStack) ≤ stk)
    (hAddrBlk : addrBlk < 619 := by decide)
    (hAddrUnmut : (addrBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (lsProg_569 H) (lsmpl.base 569)
      (sessLoadPollSpecPlaced rd pathOk Scope A lim
        (CliLoadPollEnv rd Scope AddrEnv GetEnv DeserEnv) stk) :=
  sessLoadPoll_placed_ok_of_deps (deserProg := lsProg_46 H) (deserBlk := 46)
    hC hAddr hGet (sessDeserialize_of_sessDeserEvents_placed_ok hAB hsub hMem)
    hFs hstk hAddrBlk hAddrUnmut hGetBlk hGetUnmut (by decide) (by decide)

theorem sessLoadPoll_of_sessDeserEvents_caller_ok [LibsignalPlacement]
    {M : AllocCostModel} [HasFineReallocCredit M]
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {AddrEnv : AddrGhost → List AllocEvent → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {callerProg addrProg getProg : Program} {callerBlk addrBlk getBlk : Nat}
    [IsLsBlockProg callerProg callerBlk H] [IsLsBlockProg addrProg addrBlk H]
    [IsLsBlockProg getProg getBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {addrStk getStk stk : Nat}
    (hC : AllocContractsXCliPlaced A lim H) (hAB : AllocContractsBudgetPlaced M A lim H)
    (hAddr : subroutine_ok addrProg (lsmpl.base 594) (addrTextSpecPlaced A lim AddrEnv addrStk))
    (hGet : subroutine_ok getProg (lsmpl.base 589) (dirGetSpecPlaced rd pathOk A lim GetEnv getStk))
    (hsub : ∀ r, Scope r → scopeKit r) (hMem : ∀ r, Scope r → DeserEnv r (sessDeserEvents r))
    (hFs : TraceFsSound (lsProg_569 H))
    (hstk : 0x350 + max (max addrStk getStk) (max recDeserializeStack extHookStack) ≤ stk)
    (hCallerBlk : callerBlk < 619 := by decide)
    (hAddrBlk : addrBlk < 619 := by decide)
    (hAddrUnmut : (addrBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsmpl.base 569)
      (sessLoadPollSpecPlaced rd pathOk Scope A lim
        (CliLoadPollEnv rd Scope AddrEnv GetEnv DeserEnv) stk) :=
  sessLoadPoll_placed_caller_ok_of_deps (deserProg := lsProg_46 H) (deserBlk := 46)
    hC hAddr hGet (sessDeserialize_of_sessDeserEvents_placed_ok hAB hsub hMem)
    hFs hstk hCallerBlk hAddrBlk hAddrUnmut hGetBlk hGetUnmut (by decide) (by decide)

section KitAssembly

variable [LibsignalPlacement] {M : AllocCostModel} [HasFineReallocCredit M]
  {A : RustCliAllocBudget M} {lim : BudgetLimits} {F0 : FsFiles}
  {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost}
  {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
  {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
  {readStk s1 s2 s3 s4 : Nat} {vtSym idVtSym : String}

/-- Generic `SessKitHooksPlaced` assembly of `SessionOnlyKitPlacedOkSE` without `hDeser`. -/
theorem cliSessKitOkSE_placed_of_sessDeserEvents_sessHooks
    {H : LibsignalHooks} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {readProg serProg : Program} {jRead serBlk : Nat}
    [IsLsBlockProg readProg jRead H] [IsLsBlockProg serProg serBlk H]
    (hDropNz : lsmpl.base 547 ≠ 0#64) (hpathLen : ∀ p, pathOk p → p.length < 2 ^ 32)
    (hh : SessKitHooksPlaced A lim H) (hAB : AllocContractsBudgetPlaced M A lim H)
    (hRead : subroutine_ok readProg (lsρ lsReadFileSym)
      (withLsCodeRoLoaded lsmpl (readFileSpecPlaced rd pathOk A lim readStk ReadEnv)))
    (hSer : subroutine_ok serProg (lsmpl.base 52)
      (withLsCodeLoaded lsmpl (serializeCanonSpecX M A lim)))
    (hsub : ∀ r, Scope r → scopeKit r) (hMem : ∀ r, Scope r → DeserEnv r (sessDeserEvents r))
    (hs1 : loadShimNeedPlaced ≤ s1) (hs2 : loadPollNeedPlaced readStk ≤ s2)
    (hs3 : storeShimNeedPlaced ≤ s3) (hs4 : storePollNeedXPlaced ≤ s4)
    (hjRead : jRead < 619 := by decide)
    (hjRead_unmut : (jRead ∈ libsignalMutatedBlocks) = false := by decide)
    (hSerBlk : serBlk < 619 := by decide)
    (hSerUnmut : (serBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    SessionOnlyKitPlacedOkSE A lim
      (cliSessionKitSpecPlaced A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym idVtSym)
      (cliSessionKitDefaultBudgetEnv A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4
        DeserEnv vtSym idVtSym ReadEnv)
      Scope encodeRecord H :=
  cliSessKitOkSE_placed_of_sessHooks (deserProg := lsProg_46 H) (deserBlk := 46)
    hDropNz hpathLen hh hRead (sessDeserialize_of_sessDeserEvents_placed_ok hAB hsub hMem)
    hSer hs1 hs2 hs3 hs4 hjRead hjRead_unmut (by decide) (by decide) hSerBlk hSerUnmut

/-- `RunHooksPlaced` assembly of `SessionOnlyKitPlacedOkSE` without `hDeser`. -/
theorem cliSessKitOkSE_placed_of_sessDeserEvents
    {H : LibsignalHooks} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {readProg serProg : Program} {jRead serBlk : Nat}
    [IsLsBlockProg readProg jRead H] [IsLsBlockProg serProg serBlk H]
    (hDropNz : lsmpl.base 547 ≠ 0#64) (hpathLen : ∀ p, pathOk p → p.length < 2 ^ 32)
    (hh : RunHooksPlaced A lim H) (hAB : AllocContractsBudgetPlaced M A lim H)
    (hRead : subroutine_ok readProg (lsρ lsReadFileSym)
      (withLsCodeRoLoaded lsmpl (readFileSpecPlaced rd pathOk A lim readStk ReadEnv)))
    (hSer : subroutine_ok serProg (lsmpl.base 52)
      (withLsCodeLoaded lsmpl (serializeCanonSpecX M A lim)))
    (hsub : ∀ r, Scope r → scopeKit r) (hMem : ∀ r, Scope r → DeserEnv r (sessDeserEvents r))
    (hs1 : loadShimNeedPlaced ≤ s1) (hs2 : loadPollNeedPlaced readStk ≤ s2)
    (hs3 : storeShimNeedPlaced ≤ s3) (hs4 : storePollNeedXPlaced ≤ s4)
    (hjRead : jRead < 619 := by decide)
    (hjRead_unmut : (jRead ∈ libsignalMutatedBlocks) = false := by decide)
    (hSerBlk : serBlk < 619 := by decide)
    (hSerUnmut : (serBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    SessionOnlyKitPlacedOkSE A lim
      (cliSessionKitSpecPlaced A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym idVtSym)
      (cliSessionKitDefaultBudgetEnv A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4
        DeserEnv vtSym idVtSym ReadEnv)
      Scope encodeRecord H :=
  cliSessKitOkSE_placed (deserProg := lsProg_46 H) (deserBlk := 46)
    hDropNz hpathLen hh hRead (sessDeserialize_of_sessDeserEvents_placed_ok hAB hsub hMem)
    hSer hs1 hs2 hs3 hs4 hjRead hjRead_unmut (by decide) (by decide) hSerBlk hSerUnmut

/-- Unconditional CLI `SessionOnlyKitPlacedOkSE` bundle at
`cliGhostExterns g (cliExternsPlaced mmpl W)` with both `hSer` (`lsProg_52`) and `hDeser`
(`lsProg_46`) discharged from `CliGhostAllocHooks M A lim g` + `sessDeserEvents` membership. -/
theorem cliSessKitOkSE_cli_of_sessDeserEvents_placed (mmpl : Arm64.Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks)
    {readProg : Program} {jRead : Nat}
    [IsLsBlockProg readProg jRead (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim g)
    (hAzFsT : HookFsTraced IsFsC g.allocZeroed)
    (hStrFsT : ∀ f, g.stringClone = some f → HookFsTraced IsFsC f)
    (hRead : subroutine_ok readProg (lsρ lsReadFileSym)
      (withLsCodeRoLoaded lsmpl (readFileSpecPlaced cliIo.rd cliWrOk A lim readStk ReadEnv)))
    (hsub : ∀ r, Scope r → scopeKit r) (hMem : ∀ r, Scope r → DeserEnv r (sessDeserEvents r))
    (hs1 : loadShimNeedPlaced ≤ s1) (hs2 : loadPollNeedPlaced readStk ≤ s2)
    (hs3 : storeShimNeedPlaced ≤ s3) (hs4 : storePollNeedXPlaced ≤ s4)
    (hjRead : jRead < 619 := by decide)
    (hjRead_unmut : (jRead ∈ libsignalMutatedBlocks) = false := by decide) :
    SessionOnlyKitPlacedOkSE A lim
      (cliSessionKitSpecPlaced A.repAlloc cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4 vtSym idVtSym)
      (cliSessionKitDefaultBudgetEnv A.repAlloc cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4
        DeserEnv vtSym idVtSym ReadEnv)
      Scope encodeRecord (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  cliSessKitOkSE_cli_placed mmpl g W
    (deserProg := lsProg_46 (cliGhostExterns g (cliExternsPlaced mmpl W))) (deserBlk := 46)
    hDropNz hG hAzFsT hStrFsT hRead
    (sessDeserialize_cli_of_sessDeserEvents_placed_ok mmpl g W hG hsub hMem)
    hs1 hs2 hs3 hs4 hjRead hjRead_unmut (by decide) (by decide)

theorem cliSessKitRoClOkSE_cli_of_sessDeserEvents_placed (mmpl : Arm64.Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks)
    {readProg : Program} {jRead : Nat}
    [IsLsBlockProg readProg jRead (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim g)
    (hAzFsT : HookFsTraced IsFsC g.allocZeroed)
    (hStrFsT : ∀ f, g.stringClone = some f → HookFsTraced IsFsC f)
    (hRead : subroutine_ok readProg (lsρ lsReadFileSym)
      (withLsCodeRoLoaded lsmpl (readFileSpecPlaced cliIo.rd cliWrOk A lim readStk ReadEnv)))
    (hsub : ∀ r, Scope r → scopeKit r) (hMem : ∀ r, Scope r → DeserEnv r (sessDeserEvents r))
    (hs1 : loadShimNeedPlaced ≤ s1) (hs2 : loadPollNeedPlaced readStk ≤ s2)
    (hs3 : storeShimNeedPlaced ≤ s3) (hs4 : storePollNeedXPlaced ≤ s4)
    (hjRead : jRead < 619 := by decide)
    (hjRead_unmut : (jRead ∈ libsignalMutatedBlocks) = false := by decide) :
    SessionOnlyKitPlacedRoClOkSE A lim
      (cliSessionKitSpecPlaced A.repAlloc cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4 vtSym idVtSym)
      (cliSessionKitDefaultBudgetEnv A.repAlloc cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4
        DeserEnv vtSym idVtSym ReadEnv)
      Scope encodeRecord (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  cliSessKitOkSE_cli_of_sessDeserEvents_placed mmpl g W hDropNz hG hAzFsT hStrFsT hRead hsub hMem
    hs1 hs2 hs3 hs4 hjRead hjRead_unmut

theorem cliSessKitOkSE_cli_of_sessDeserEvents_readHook (mmpl : Arm64.Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim g)
    (hAzFsT : HookFsTraced IsFsC g.allocZeroed)
    (hStrFsT : ∀ f, g.stringClone = some f → HookFsTraced IsFsC f)
    (hReadHook : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk A lim readStk ReadEnv))
    (hsub : ∀ r, Scope r → scopeKit r) (hMem : ∀ r, Scope r → DeserEnv r (sessDeserEvents r))
    (hs1 : loadShimNeedPlaced ≤ s1) (hs2 : loadPollNeedPlaced readStk ≤ s2)
    (hs3 : storeShimNeedPlaced ≤ s3) (hs4 : storePollNeedXPlaced ≤ s4) :
    SessionOnlyKitPlacedOkSE A lim
      (cliSessionKitSpecPlaced A.repAlloc cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4 vtSym idVtSym)
      (cliSessionKitDefaultBudgetEnv A.repAlloc cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4
        DeserEnv vtSym idVtSym ReadEnv)
      Scope encodeRecord (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  cliSessKitOkSE_cli_placed_of_readHook mmpl g W
    (deserProg := lsProg_46 (cliGhostExterns g (cliExternsPlaced mmpl W))) (deserBlk := 46)
    hDropNz hG hAzFsT hStrFsT hReadHook
    (sessDeserialize_cli_of_sessDeserEvents_placed_ok mmpl g W hG hsub hMem)
    hs1 hs2 hs3 hs4 (by decide) (by decide)

end KitAssembly

/-! ## Section 3: `cliSessionKitLoadPollEnv_imp_cliSessLoadPollEnv` & W1–W4 `hLoadEq` Dischargers -/

/-- `OptLoadDeserEnv` refines the `2 MiB` wire-slice disjunction inside `CliSessLoadPollEnv`. -/
theorem optLoadDeserEnv_imp_bytesOrNil
    {rd : ReadRule} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DeserByBytesEnv : List (BitVec 8) → List AllocEvent → Prop}
    {F0 : FsFiles} {d : DirGhost} {rem : AddrVal}
    (hCap : ∀ bs, d.get rd F0 (addressText rem) = .ok bs → bs.length ≤ 2097152)
    (hDeser : ∀ r evs, Scope r → DeserEnv r evs → DeserByBytesEnv (encodeRecord r) evs) :
    ∀ evs, OptLoadDeserEnv Scope DeserEnv (d.get rd F0 (addressText rem)) evs →
      (evs = [] ∨ ∃ bs : List (BitVec 8), bs.length ≤ 2097152 ∧ DeserByBytesEnv bs evs) := by
  intro evs hOpt
  unfold OptLoadDeserEnv at hOpt
  cases hget : d.get rd F0 (addressText rem) with
  | error _ => rw [hget] at hOpt; exact Or.inl hOpt
  | ok bs =>
    rw [hget] at hOpt
    cases bs with
    | nil => exact Or.inl hOpt
    | cons b0 bsRest =>
      obtain ⟨r, henc, hsc, hd⟩ := hOpt
      refine Or.inr ⟨b0 :: bsRest, hCap (b0 :: bsRest) hget, ?_⟩
      rw [← henc]; exact hDeser r evs hsc hd

private theorem seqEnv_imp {P₁ P₂ Q₁ Q₂ : List AllocEvent → Prop}
    (hP : ∀ evs, P₁ evs → P₂ evs) (hQ : ∀ evs, Q₁ evs → Q₂ evs) :
    ∀ evs, SeqEnv P₁ Q₁ evs → SeqEnv P₂ Q₂ evs := by
  intro evs h
  rcases h with h1 | ⟨e1, e2, rfl, h1, h2⟩
  · exact Or.inl (hP evs h1)
  · exact Or.inr ⟨e1, e2, rfl, hP e1 h1, hQ e2 h2⟩

/-- `cliSessionKitLoadPollEnv` refines `SerCloneStorePeakSpec.CliSessLoadPollEnv`. -/
theorem cliSessionKitLoadPollEnv_imp_cliSessLoadPollEnv
    {rd : ReadRule} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {AddrValEnv : AddrVal → List AllocEvent → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DeserByBytesEnv : List (BitVec 8) → List AllocEvent → Prop}
    {F0 : FsFiles} {d : DirGhost} {peer : AddrGhost} {rem : AddrVal}
    (hrem : rem = peer.val)
    (hAddr : ∀ evs, AddrValEnv peer.val evs → CliAddrTextEnv peer evs)
    (hGet : ∀ evs, GetEnv F0 d (addressText peer.val) evs →
      CliDirGetEnv (ReadFileRuleEnv rd) F0 d (addressText peer.val) evs)
    (hCap : ∀ bs, d.get rd F0 (addressText peer.val) = .ok bs → bs.length ≤ 2097152)
    (hDeser : ∀ r evs, Scope r → DeserEnv r evs → DeserByBytesEnv (encodeRecord r) evs) :
    ∀ evs, cliSessionKitLoadPollEnv rd Scope AddrValEnv GetEnv DeserEnv F0 d rem evs →
      CliSessLoadPollEnv rd DeserByBytesEnv F0 d peer evs := by
  subst hrem; intro evs h
  unfold cliSessionKitLoadPollEnv at h; unfold CliSessLoadPollEnv
  exact seqEnv_imp hAddr
    (seqEnv_imp hGet
      (seqEnv_imp (optLoadDeserEnv_imp_bytesOrNil hCap hDeser) (fun _ hf => hf))) evs h

section W1ToW4LoadEq

variable [LibsignalPlacement] {A : RustAlloc} {F : FsFiles} {pathOk : List (BitVec 8) → Prop}
  {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost}
  {s1 s2 s3 s4 fileCap : Nat} {vtSym idVtSym : String}
  {AddrValEnv : AddrVal → List AllocEvent → Prop}
  {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
  {DeserEnv SerValEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
  {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
  {DeserByBytesEnv : List (BitVec 8) → List AllocEvent → Prop} {rem : AddrVal}

theorem w1_hLoadEq_of_cliSessionKitBudgetEnv (hrem : rem = peer.val) (hfc : fileCap ≤ 2097152)
    (hSessFileCap : ∀ bs,
      cliIo.rd F (pathOf StoresGhost.opened.sessions.path (addressText peer.val)) = .ok bs →
      bs.length ≤ fileCap)
    (hAddr : ∀ evs, AddrValEnv peer.val evs → CliAddrTextEnv peer evs)
    (hGet : ∀ evs, GetEnv F StoresGhost.opened.sessions (addressText peer.val) evs →
      CliDirGetEnv (ReadFileRuleEnv cliIo.rd) F StoresGhost.opened.sessions (addressText peer.val) evs)
    (hDeser : ∀ r evs, Scope r → DeserEnv r evs → DeserByBytesEnv (encodeRecord r) evs) :
    ∀ evs,
      (cliSessionKitBudgetEnv A cliIo.rd F pathOk Scope peer s1 s2 s3 s4
        AddrValEnv GetEnv DeserEnv SerValEnv PutEnv vtSym idVtSym).loadPollEnv
        StoresGhost.opened.sessions rem evs →
      CliSessLoadPollEnv cliIo.rd DeserByBytesEnv F StoresGhost.opened.sessions peer evs :=
  cliSessionKitLoadPollEnv_imp_cliSessLoadPollEnv hrem hAddr hGet
    (fun bs hbs => Nat.le_trans (hSessFileCap bs hbs) hfc) hDeser

theorem w2_hLoadEq_of_cliSessionKitBudgetEnv (hrem : rem = peer.val) (hfc : fileCap ≤ 2097152)
    (hSessFileCap : ∀ bs,
      cliIo.rd F (pathOf StoresGhost.opened.sessions.path (addressText peer.val)) = .ok bs →
      bs.length ≤ fileCap)
    (hAddr : ∀ evs, AddrValEnv peer.val evs → CliAddrTextEnv peer evs)
    (hGet : ∀ evs, GetEnv F StoresGhost.opened.sessions (addressText peer.val) evs →
      CliDirGetEnv (ReadFileRuleEnv cliIo.rd) F StoresGhost.opened.sessions (addressText peer.val) evs)
    (hDeser : ∀ r evs, Scope r → DeserEnv r evs → DeserByBytesEnv (encodeRecord r) evs) :
    ∀ evs,
      (cliSessionKitBudgetEnv A cliIo.rd F pathOk Scope peer s1 s2 s3 s4
        AddrValEnv GetEnv DeserEnv SerValEnv PutEnv vtSym idVtSym).loadPollEnv
        StoresGhost.opened.sessions rem evs →
      CliSessLoadPollEnv cliIo.rd DeserByBytesEnv F StoresGhost.opened.sessions peer evs :=
  w1_hLoadEq_of_cliSessionKitBudgetEnv hrem hfc hSessFileCap hAddr hGet hDeser

theorem w3_hLoadEq_of_cliSessionKitBudgetEnv (hrem : rem = peer.val) (hfc : fileCap ≤ 2097152)
    (hSessFileCap : ∀ bs,
      cliIo.rd F (pathOf StoresGhost.opened.sessions.path (addressText peer.val)) = .ok bs →
      bs.length ≤ fileCap)
    (hAddr : ∀ evs, AddrValEnv peer.val evs → CliAddrTextEnv peer evs)
    (hGet : ∀ evs, GetEnv F StoresGhost.opened.sessions (addressText peer.val) evs →
      CliDirGetEnv (ReadFileRuleEnv cliIo.rd) F StoresGhost.opened.sessions (addressText peer.val) evs)
    (hDeser : ∀ r evs, Scope r → DeserEnv r evs → DeserByBytesEnv (encodeRecord r) evs) :
    ∀ evs,
      (cliSessionKitBudgetEnv A cliIo.rd F pathOk Scope peer s1 s2 s3 s4
        AddrValEnv GetEnv DeserEnv SerValEnv PutEnv vtSym idVtSym).loadPollEnv
        StoresGhost.opened.sessions rem evs →
      CliSessLoadPollEnv cliIo.rd DeserByBytesEnv F StoresGhost.opened.sessions peer evs :=
  w1_hLoadEq_of_cliSessionKitBudgetEnv hrem hfc hSessFileCap hAddr hGet hDeser

theorem w4_hLoadEq_of_cliSessionKitBudgetEnv (hrem : rem = peer.val) (hfc : fileCap ≤ 2097152)
    (hSessFileCap : ∀ bs,
      cliIo.rd F (pathOf StoresGhost.opened.sessions.path (addressText peer.val)) = .ok bs →
      bs.length ≤ fileCap)
    (hAddr : ∀ evs, AddrValEnv peer.val evs → CliAddrTextEnv peer evs)
    (hGet : ∀ evs, GetEnv F StoresGhost.opened.sessions (addressText peer.val) evs →
      CliDirGetEnv (ReadFileRuleEnv cliIo.rd) F StoresGhost.opened.sessions (addressText peer.val) evs)
    (hDeser : ∀ r evs, Scope r → DeserEnv r evs → DeserByBytesEnv (encodeRecord r) evs) :
    ∀ evs,
      (cliSessionKitBudgetEnv A cliIo.rd F pathOk Scope peer s1 s2 s3 s4
        AddrValEnv GetEnv DeserEnv SerValEnv PutEnv vtSym idVtSym).loadPollEnv
        StoresGhost.opened.sessions rem evs →
      CliSessLoadPollEnv cliIo.rd DeserByBytesEnv F StoresGhost.opened.sessions peer evs :=
  w1_hLoadEq_of_cliSessionKitBudgetEnv hrem hfc hSessFileCap hAddr hGet hDeser

end W1ToW4LoadEq

/-!
## Section 4: `PhaseCreditSpec`, `PhaseGroupSpec`, & Boxed-Step Dischargers for `cliSessionKitDefaultBudgetEnv`
-/

/-- Tight `Δcum` of `cliSessionKitDefaultBudgetEnv`'s `loadPollEnv`:
`11,265` (`AddrTextValEnv DecimalEnv`) `+ 21,185` (`DirGetPathEnv`) `+ max 738 (fineReadFileCum fc) + deserCum`. -/
def defaultLoadPollTightDeltaCum (fc deserCum : Nat) : Nat :=
  32450 + max 738 (fineReadFileCum fc) + deserCum

/-- Tight `fineCostModel` `PhaseCreditSpec` for `cliSessionKitDefaultBudgetEnv`'s `loadPollEnv`
(record-indexed `DeserEnv`, `fc = max maxVal fileCap`). -/
theorem defaultLoadPollEnv_fine_phaseCredit_tight
    {rd : ReadRule} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {F0 : FsFiles} {dir : DirGhost} {rem : AddrVal}
    {maxDir maxEntries maxVal fileCap deserCum deserLive deserPeak deserMaxReq : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir) (hdir : maxDir ≤ 64)
    (hrem : rem.name.length ≤ 40)
    (hcap : ∀ bs, rd F0 (pathOf dir.path (addressText rem)) = .ok bs → bs.length ≤ fileCap)
    (hDeser : ∀ r, Scope r → (encodeRecord r).length ≤ max maxVal fileCap →
      PhaseCreditSpec fineCostModel (DeserEnv r) deserCum deserLive deserPeak deserMaxReq) :
    PhaseCreditSpec fineCostModel
      (cliSessionKitLoadPollEnv rd Scope (AddrTextValEnv DecimalEnv)
        (DirGetEnv PathEnv (ReadFileRuleEnv rd) rd) DeserEnv F0 dir rem)
      (defaultLoadPollTightDeltaCum (max maxVal fileCap) deserCum)
      (fineReadFileLive (max maxVal fileCap) + deserLive)
      (max (fineReadFilePeak (max maxVal fileCap)) (fineReadFileLive (max maxVal fileCap) + deserPeak))
      (max (max 256 (fineReadFileMaxReq (max maxVal fileCap))) deserMaxReq) := by
  have haddrLen : (addressText rem).length ≤ 64 := by
    have h44 := addressText_length_le rem; omega
  have hdc64 : DirDomainCaps 64 maxEntries maxVal dir :=
    hdc.mono hdir (Nat.le_refl _) (Nat.le_refl _)
  have h1 := addrTextValEnv_decimal_fine_phaseCredit_tight rem hrem
  have h2 : PhaseCreditSpec fineCostModel
      (DirGetEnv PathEnv (ReadFileRuleEnv rd) rd F0 dir (addressText rem))
      (21185 + max 738 (fineReadFileCum (max maxVal fileCap)))
      (fineReadFileLive (max maxVal fileCap))
      (fineReadFilePeak (max maxVal fileCap))
      (max 256 (fineReadFileMaxReq (max maxVal fileCap))) :=
    dirGetEnv_path_readFile_fine_phaseCredit_tight rd F0 dir (addressText rem) hdc64 haddrLen hcap
  have hgetCap : ∀ bs, dir.get rd F0 (addressText rem) = .ok bs → bs.length ≤ max maxVal fileCap := by
    unfold DirGhost.get
    cases hfind : dir.changed.find? (fun e => e.1 == addressText rem) with
    | some e =>
      intro bs hbs; cases hbs
      exact Nat.le_trans (hdc.changed_val_le e.1 e.2 (List.mem_of_find?_eq_some hfind))
        (Nat.le_max_left maxVal fileCap)
    | none =>
      intro bs hbs
      exact Nat.le_trans (hcap bs hbs) (Nat.le_max_right maxVal fileCap)
  have h3 : PhaseCreditSpec fineCostModel
      (OptLoadDeserEnv Scope DeserEnv (dir.get rd F0 (addressText rem)))
      deserCum deserLive deserPeak deserMaxReq := by
    unfold OptLoadDeserEnv
    cases hget : dir.get rd F0 (addressText rem) with
    | error _ =>
      exact (PhaseCreditSpec.nil fineCostModel).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    | ok bs =>
      cases bs with
      | nil =>
        exact (PhaseCreditSpec.nil fineCostModel).mono
          (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
      | cons b0 bsRest =>
        have hbs_le : (b0 :: bsRest).length ≤ max maxVal fileCap := hgetCap (b0 :: bsRest) hget
        exact
          { req_align := fun evs ⟨r, henc, hsc, hd⟩ =>
              (hDeser r hsc (henc.symm ▸ hbs_le)).req_align evs hd
            credit_le := fun st0 {_} ⟨r, henc, hsc, hd⟩ =>
              (hDeser r hsc (henc.symm ▸ hbs_le)).credit_le st0 hd }
  have h3f := seq_freeOnly_phaseCredit fineCostModel_freeNonInc h3
  unfold cliSessionKitLoadPollEnv defaultLoadPollTightDeltaCum
  exact (h1.seq (h2.seq h3f)).mono
    (by omega) (by omega)
    (Nat.max_le.mpr ⟨Nat.zero_le _, by omega⟩)
    (Nat.max_le.mpr
      ⟨Nat.le_trans (by decide : 80 ≤ 256)
        (Nat.le_trans (Nat.le_max_left 256 _) (Nat.le_max_left _ _)),
       Nat.le_refl _⟩)

theorem defaultLoadPollEnv_eventPred_fine_phaseCredit_tight
    {rd : ReadRule} {Scope : SessionRecord (List (BitVec 8)) → Prop} {P : List AllocEvent → Prop}
    {F0 : FsFiles} {dir : DirGhost} {rem : AddrVal}
    {maxDir maxEntries maxVal fileCap deserCum deserLive deserPeak deserMaxReq : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir) (hdir : maxDir ≤ 64)
    (hrem : rem.name.length ≤ 40)
    (hcap : ∀ bs, rd F0 (pathOf dir.path (addressText rem)) = .ok bs → bs.length ≤ fileCap)
    (hP : PhaseCreditSpec fineCostModel P deserCum deserLive deserPeak deserMaxReq) :
    PhaseCreditSpec fineCostModel
      (cliSessionKitLoadPollEnv rd Scope (AddrTextValEnv DecimalEnv)
        (DirGetEnv PathEnv (ReadFileRuleEnv rd) rd) (ofEventPred P) F0 dir rem)
      (defaultLoadPollTightDeltaCum (max maxVal fileCap) deserCum)
      (fineReadFileLive (max maxVal fileCap) + deserLive)
      (max (fineReadFilePeak (max maxVal fileCap)) (fineReadFileLive (max maxVal fileCap) + deserPeak))
      (max (max 256 (fineReadFileMaxReq (max maxVal fileCap))) deserMaxReq) :=
  defaultLoadPollEnv_fine_phaseCredit_tight hdc hdir hrem hcap (fun _ _ _ => hP)

theorem defaultLoadPollEnv_byBytes_fine_phaseCredit_tight
    {rd : ReadRule} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {DeserByBytesEnv : List (BitVec 8) → List AllocEvent → Prop}
    {F0 : FsFiles} {dir : DirGhost} {rem : AddrVal}
    {maxDir maxEntries maxVal fileCap deserCum deserLive deserPeak deserMaxReq : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir) (hdir : maxDir ≤ 64)
    (hrem : rem.name.length ≤ 40)
    (hcap : ∀ bs, rd F0 (pathOf dir.path (addressText rem)) = .ok bs → bs.length ≤ fileCap)
    (hDeser : ∀ bs, bs.length ≤ max maxVal fileCap →
      PhaseCreditSpec fineCostModel (DeserByBytesEnv bs) deserCum deserLive deserPeak deserMaxReq) :
    PhaseCreditSpec fineCostModel
      (cliSessionKitLoadPollEnv rd Scope (AddrTextValEnv DecimalEnv)
        (DirGetEnv PathEnv (ReadFileRuleEnv rd) rd) (ofBytesEnv DeserByBytesEnv) F0 dir rem)
      (defaultLoadPollTightDeltaCum (max maxVal fileCap) deserCum)
      (fineReadFileLive (max maxVal fileCap) + deserLive)
      (max (fineReadFilePeak (max maxVal fileCap)) (fineReadFileLive (max maxVal fileCap) + deserPeak))
      (max (max 256 (fineReadFileMaxReq (max maxVal fileCap))) deserMaxReq) :=
  defaultLoadPollEnv_fine_phaseCredit_tight hdc hdir hrem hcap
    (fun r _ hlen => hDeser (encodeRecord r) hlen)

/-- Generic `PhaseGroupSpec M` (`48 * FineScale + g_deser`) for `loadPollEnv`. -/
theorem defaultLoadPollEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    {rd : ReadRule} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {F0 : FsFiles} {dir : DirGhost} {rem : AddrVal} {fc g_deser : Nat}
    (hrem : rem.name.length ≤ 40)
    (hgetCap : ∀ bs, dir.get rd F0 (addressText rem) = .ok bs → bs.length ≤ fc)
    (hDeser : ∀ r, Scope r → (encodeRecord r).length ≤ fc → PhaseGroupSpec M (DeserEnv r) g_deser) :
    PhaseGroupSpec M
      (cliSessionKitLoadPollEnv rd Scope (AddrTextValEnv DecimalEnv)
        (DirGetEnv PathEnv (ReadFileRuleEnv rd) rd) DeserEnv F0 dir rem)
      (48 * FineScale + g_deser) := by
  have h1 := addrTextValEnv_decimal_groupSpec M rem hrem
  have h2 := dirGetEnv_path_readFile_groupSpec M rd F0 dir (addressText rem)
  have h3 : PhaseGroupSpec M
      (OptLoadDeserEnv Scope DeserEnv (dir.get rd F0 (addressText rem))) g_deser := by
    unfold OptLoadDeserEnv
    cases hget : dir.get rd F0 (addressText rem) with
    | error _ => exact (PhaseGroupSpec.nil M).mono (Nat.zero_le _)
    | ok bs =>
      cases bs with
      | nil => exact (PhaseGroupSpec.nil M).mono (Nat.zero_le _)
      | cons b0 bsRest =>
        have hbs_le : (b0 :: bsRest).length ≤ fc := hgetCap (b0 :: bsRest) hget
        exact { groups_le := fun st0 {_} ⟨r, henc, hsc, hd⟩ =>
          (hDeser r hsc (henc.symm ▸ hbs_le)).groups_le st0 hd }
  have h3f := (h3.seq (PhaseGroupSpec.freeOnly M)).mono (Nat.le_of_eq (Nat.add_zero _))
  unfold cliSessionKitLoadPollEnv
  exact (h1.seq (h2.seq h3f)).mono (by omega)

/-- Tight `fineCostModel` `PhaseGroupSpec` (`45 * FineScale + g_deser`) for `cliSessionKitDefaultBudgetEnv`'s `loadPollEnv`. -/
theorem defaultLoadPollEnv_fine_groupSpec
    {rd : ReadRule} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {F0 : FsFiles} {dir : DirGhost} {rem : AddrVal} {fc g_deser : Nat}
    (hrem : rem.name.length ≤ 40)
    (hgetCap : ∀ bs, dir.get rd F0 (addressText rem) = .ok bs → bs.length ≤ fc)
    (hDeser : ∀ r, Scope r → (encodeRecord r).length ≤ fc →
      PhaseGroupSpec fineCostModel (DeserEnv r) g_deser) :
    PhaseGroupSpec fineCostModel
      (cliSessionKitLoadPollEnv rd Scope (AddrTextValEnv DecimalEnv)
        (DirGetEnv PathEnv (ReadFileRuleEnv rd) rd) DeserEnv F0 dir rem)
      (45 * FineScale + g_deser) := by
  have h1 := addrTextValEnv_decimal_fine_groupSpec rem hrem
  have h2 := dirGetEnv_path_readFile_groupSpec fineCostModel rd F0 dir (addressText rem)
  have h3 : PhaseGroupSpec fineCostModel
      (OptLoadDeserEnv Scope DeserEnv (dir.get rd F0 (addressText rem))) g_deser := by
    unfold OptLoadDeserEnv
    cases hget : dir.get rd F0 (addressText rem) with
    | error _ => exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
    | ok bs =>
      cases bs with
      | nil => exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
      | cons b0 bsRest =>
        have hbs_le : (b0 :: bsRest).length ≤ fc := hgetCap (b0 :: bsRest) hget
        exact { groups_le := fun st0 {_} ⟨r, henc, hsc, hd⟩ =>
          (hDeser r hsc (henc.symm ▸ hbs_le)).groups_le st0 hd }
  have h3f := (h3.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono (Nat.le_of_eq (Nat.add_zero _))
  unfold cliSessionKitLoadPollEnv
  exact (h1.seq (h2.seq h3f)).mono (by omega)

/-- Small-regime (`kit.loadBoxSize ≤ smallMaxReq M`) `PhaseCreditSpec M` for
`SessionStoreKitBudget.LoadStepEnv` (`0` live or peak overhead from `Box<dyn Future>`). -/
theorem loadStepEnv_small_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (kitEnv : SessionStoreBudgetEnv kit)
    (st0 : kit.StoreState) (rem : AddrVal) {c l p r : Nat}
    (hsz : kit.loadBoxSize ≤ HasFineReallocCredit.smallMaxReq M)
    (hpoll : PhaseCreditSpec M (kitEnv.loadPollEnv st0 rem) c l p r) :
    PhaseCreditSpec M (LoadStepEnv kit kitEnv st0 rem)
      (w4BoxedStepCum kit.loadBoxSize c) l p (w4BoxedStepMaxReq kit.loadBoxSize r) :=
  PhaseCreditSpec.of_imp
    (fun _ h => boxedDeallocPred_to_w4BoxedStoreStep (fun _ hd => rustDealloc8_freeOnly hd) h)
    (w4BoxedStoreStep_small_phaseCredit hM kit.loadBoxSize hsz hpoll)

/-- W4 boxed `LoadStepEnv` (`loadBoxSize = 24`) cumulative cost on `cliSessionKitSpecPlaced`. -/
abbrev defaultW4LoadCum (fc deserCum : Nat) : Nat :=
  w4BoxedStepCum 24 (defaultLoadPollTightDeltaCum fc deserCum)

/-- W4 boxed `LoadStepEnv` (`loadBoxSize = 24`) regime-uniform live delta on `cliSessionKitSpecPlaced`. -/
abbrev defaultW4LoadLive (fc deserLive : Nat) : Nat :=
  w4BoxedStepLive 24 (fineReadFileLive fc + deserLive)

/-- W4 boxed `LoadStepEnv` (`loadBoxSize = 24`) regime-uniform peak delta on `cliSessionKitSpecPlaced`. -/
abbrev defaultW4LoadPeak (fc deserPeak : Nat) : Nat :=
  w4BoxedStepPeak 24 (max (fineReadFilePeak fc) (fineReadFileLive fc + deserPeak))

/-- W4 boxed `LoadStepEnv` (`loadBoxSize = 24`) max-request bound on `cliSessionKitSpecPlaced`. -/
abbrev defaultW4LoadMaxReq (fc deserMaxReq : Nat) : Nat :=
  w4BoxedStepMaxReq 24 (max (max 256 (fineReadFileMaxReq fc)) deserMaxReq)

section DefaultBoxedSteps

variable [LibsignalPlacement] {A : RustAlloc} {rd : ReadRule} {F0 : FsFiles}
  {pathOk : List (BitVec 8) → Prop} {Scope : SessionRecord (List (BitVec 8)) → Prop}
  {peer : AddrGhost} {s1 s2 s3 s4 : Nat} {vtSym idVtSym : String}
  {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}

local notation "kit₀" => cliSessionKitSpecPlaced A rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym idVtSym
local notation "kitEnv₀" =>
  cliSessionKitDefaultBudgetEnv A rd F0 pathOk Scope peer s1 s2 s3 s4
    DeserEnv vtSym idVtSym (ReadFileRuleEnv rd)

theorem w3_defaultLoadStep_fine_phaseCredit {dir : DirGhost} {rem : AddrVal}
    {maxDir maxEntries maxVal fileCap deserCum deserLive deserPeak deserMaxReq : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir) (hdir : maxDir ≤ 64)
    (hrem : rem.name.length ≤ 40)
    (hcap : ∀ bs, rd F0 (pathOf dir.path (addressText rem)) = .ok bs → bs.length ≤ fileCap)
    (hDeser : ∀ r, Scope r → (encodeRecord r).length ≤ max maxVal fileCap →
      PhaseCreditSpec fineCostModel (DeserEnv r) deserCum deserLive deserPeak deserMaxReq) :
    PhaseCreditSpec fineCostModel (LoadStepEnv kit₀ kitEnv₀ dir rem)
      (w3BoxedStepCum 24 (defaultLoadPollTightDeltaCum (max maxVal fileCap) deserCum))
      (w3BoxedStepLive 24 (fineReadFileLive (max maxVal fileCap) + deserLive))
      (w3BoxedStepPeak 24
        (max (fineReadFilePeak (max maxVal fileCap))
          (fineReadFileLive (max maxVal fileCap) + deserPeak)))
      (w3BoxedStepMaxReq 24
        (max (max 256 (fineReadFileMaxReq (max maxVal fileCap))) deserMaxReq)) :=
  loadStep_phaseCredit fineCostModel_modelHyps kit₀ kitEnv₀ dir rem
    (defaultLoadPollEnv_fine_phaseCredit_tight hdc hdir hrem hcap hDeser)

theorem w4_defaultLoadStep_fine_phaseCredit {dir : DirGhost} {rem : AddrVal}
    {maxDir maxEntries maxVal fileCap deserCum deserLive deserPeak deserMaxReq : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir) (hdir : maxDir ≤ 64)
    (hrem : rem.name.length ≤ 40)
    (hcap : ∀ bs, rd F0 (pathOf dir.path (addressText rem)) = .ok bs → bs.length ≤ fileCap)
    (hDeser : ∀ r, Scope r → (encodeRecord r).length ≤ max maxVal fileCap →
      PhaseCreditSpec fineCostModel (DeserEnv r) deserCum deserLive deserPeak deserMaxReq) :
    PhaseCreditSpec fineCostModel (LoadStepEnv kit₀ kitEnv₀ dir rem)
      (defaultW4LoadCum (max maxVal fileCap) deserCum)
      (defaultW4LoadLive (max maxVal fileCap) deserLive)
      (defaultW4LoadPeak (max maxVal fileCap) deserPeak)
      (defaultW4LoadMaxReq (max maxVal fileCap) deserMaxReq) :=
  loadStepEnv_phaseCredit fineCostModel_modelHyps kit₀ kitEnv₀ dir rem
    (defaultLoadPollEnv_fine_phaseCredit_tight hdc hdir hrem hcap hDeser)

theorem w4_defaultLoadStep_small_fine_phaseCredit {dir : DirGhost} {rem : AddrVal}
    {maxDir maxEntries maxVal fileCap deserCum deserLive deserPeak deserMaxReq : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir) (hdir : maxDir ≤ 64)
    (hrem : rem.name.length ≤ 40)
    (hcap : ∀ bs, rd F0 (pathOf dir.path (addressText rem)) = .ok bs → bs.length ≤ fileCap)
    (hDeser : ∀ r, Scope r → (encodeRecord r).length ≤ max maxVal fileCap →
      PhaseCreditSpec fineCostModel (DeserEnv r) deserCum deserLive deserPeak deserMaxReq) :
    PhaseCreditSpec fineCostModel (LoadStepEnv kit₀ kitEnv₀ dir rem)
      (defaultW4LoadCum (max maxVal fileCap) deserCum)
      (fineReadFileLive (max maxVal fileCap) + deserLive)
      (max (fineReadFilePeak (max maxVal fileCap)) (fineReadFileLive (max maxVal fileCap) + deserPeak))
      (defaultW4LoadMaxReq (max maxVal fileCap) deserMaxReq) :=
  loadStepEnv_small_phaseCredit fineCostModel_modelHyps kit₀ kitEnv₀ dir rem
    (by change 24 ≤ _; rw [fineCostModel_smallMaxReq_eq]; decide)
    (defaultLoadPollEnv_fine_phaseCredit_tight hdc hdir hrem hcap hDeser)

theorem w4_defaultStageP1Ok_fine_phaseCredit {b' : BitVec 64}
    (ikit : IdentityStoreSpec A b') (ikitEnv : IdentityStoreBudgetEnv ikit) (ist : ikit.IdState)
    {dir : DirGhost} {rem : AddrVal} {remoteIdKey : IdentityKey}
    {maxDir maxEntries maxVal fileCap deserCum deserLive deserPeak deserMaxReq c₂ l₂ p₂ r₂ : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir) (hdir : maxDir ≤ 64)
    (hrem : rem.name.length ≤ 40)
    (hcap : ∀ bs, rd F0 (pathOf dir.path (addressText rem)) = .ok bs → bs.length ≤ fileCap)
    (hDeser : ∀ r, Scope r → (encodeRecord r).length ≤ max maxVal fileCap →
      PhaseCreditSpec fineCostModel (DeserEnv r) deserCum deserLive deserPeak deserMaxReq)
    (hTrust : PhaseCreditSpec fineCostModel
      (ikitEnv.trustPollEnv ist rem remoteIdKey .receiving) c₂ l₂ p₂ r₂) :
    PhaseCreditSpec fineCostModel
      (SeqEnv (LoadStepEnv kit₀ kitEnv₀ dir rem)
        (TrustStepEnv ikit ikitEnv ist rem remoteIdKey .receiving))
      (defaultW4LoadCum (max maxVal fileCap) deserCum + w4BoxedStepCum ikit.trustBoxSize c₂)
      (defaultW4LoadLive (max maxVal fileCap) deserLive + w4BoxedStepLive ikit.trustBoxSize l₂)
      (max (defaultW4LoadPeak (max maxVal fileCap) deserPeak)
        (defaultW4LoadLive (max maxVal fileCap) deserLive + w4BoxedStepPeak ikit.trustBoxSize p₂))
      (max (defaultW4LoadMaxReq (max maxVal fileCap) deserMaxReq)
        (w4BoxedStepMaxReq ikit.trustBoxSize r₂)) :=
  (w4_defaultLoadStep_fine_phaseCredit hdc hdir hrem hcap hDeser).seq
    (trustStepEnv_phaseCredit fineCostModel_modelHyps ikit ikitEnv ist rem remoteIdKey
      .receiving hTrust)

theorem w4_defaultStageP1Untrusted_small_fine_phaseCredit {b' : BitVec 64} {targetPeer : AddrGhost}
    (ikit : IdentityStoreSpec A b') (ikitEnv : IdentityStoreBudgetEnv ikit) (ist : ikit.IdState)
    {dir : DirGhost} {remoteIdKey : IdentityKey}
    {maxDir maxEntries maxVal fileCap deserCum deserLive deserPeak deserMaxReq c₂ l₂ p₂ r₂ : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir) (hdir : maxDir ≤ 64)
    (hpeer : targetPeer.name.bytes.length ≤ 40)
    (hcap : ∀ bs, rd F0 (pathOf dir.path (addressText targetPeer.val)) = .ok bs → bs.length ≤ fileCap)
    (hDeser : ∀ r, Scope r → (encodeRecord r).length ≤ max maxVal fileCap →
      PhaseCreditSpec fineCostModel (DeserEnv r) deserCum deserLive deserPeak deserMaxReq)
    (hTrust : PhaseCreditSpec fineCostModel
      (ikitEnv.trustPollEnv ist targetPeer.val remoteIdKey .receiving) c₂ l₂ p₂ r₂) :
    PhaseCreditSpec fineCostModel
      (SeqEnv (LoadStepEnv kit₀ kitEnv₀ dir targetPeer.val)
        (SeqEnv (TrustStepEnv ikit ikitEnv ist targetPeer.val remoteIdKey .receiving)
          (SeqEnv (StringCloneEnv targetPeer.name) FreeOnlyEvs)))
      (defaultW4LoadCum (max maxVal fileCap) deserCum +
        w4BoxedStepCum ikit.trustBoxSize c₂ + (2 * 40 + 9539))
      (defaultW4LoadLive (max maxVal fileCap) deserLive + w4BoxedStepLive ikit.trustBoxSize l₂)
      (max (defaultW4LoadPeak (max maxVal fileCap) deserPeak)
        (defaultW4LoadLive (max maxVal fileCap) deserLive +
          max (w4BoxedStepPeak ikit.trustBoxSize p₂) (w4BoxedStepLive ikit.trustBoxSize l₂)))
      (max (defaultW4LoadMaxReq (max maxVal fileCap) deserMaxReq)
        (max (w4BoxedStepMaxReq ikit.trustBoxSize r₂) 40)) := by
  have hL : PhaseCreditSpec fineCostModel (LoadStepEnv kit₀ kitEnv₀ dir targetPeer.val) _ _ _ _ :=
    w4_defaultLoadStep_fine_phaseCredit hdc hdir hpeer hcap hDeser
  have hT := trustStepEnv_phaseCredit fineCostModel_modelHyps
    ikit ikitEnv ist targetPeer.val remoteIdKey .receiving hTrust
  have hCl := phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps
    (stringClone_phaseCredit_small fineCostModel_modelHyps hpeer
      (by rw [fineCostModel_smallMaxReq_eq]; decide))
  exact (hL.seq (hT.seq hCl)).mono (by omega) (by omega) (by omega) (by omega)

theorem w4_defaultStageP1Untrusted_fine_phaseCredit {b' : BitVec 64} {targetPeer : AddrGhost}
    (ikit : IdentityStoreSpec A b') (ikitEnv : IdentityStoreBudgetEnv ikit) (ist : ikit.IdState)
    {dir : DirGhost} {remoteIdKey : IdentityKey}
    {maxDir maxEntries maxVal fileCap deserCum deserLive deserPeak deserMaxReq c₂ l₂ p₂ r₂ : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir) (hdir : maxDir ≤ 64)
    (hpeer : targetPeer.name.bytes.length ≤ 40)
    (hcap : ∀ bs, rd F0 (pathOf dir.path (addressText targetPeer.val)) = .ok bs → bs.length ≤ fileCap)
    (hDeser : ∀ r, Scope r → (encodeRecord r).length ≤ max maxVal fileCap →
      PhaseCreditSpec fineCostModel (DeserEnv r) deserCum deserLive deserPeak deserMaxReq)
    (hTrust : PhaseCreditSpec fineCostModel
      (ikitEnv.trustPollEnv ist targetPeer.val remoteIdKey .receiving) c₂ l₂ p₂ r₂) :
    PhaseCreditSpec fineCostModel
      (SeqEnv (LoadStepEnv kit₀ kitEnv₀ dir targetPeer.val)
        (SeqEnv (TrustStepEnv ikit ikitEnv ist targetPeer.val remoteIdKey .receiving)
          (SeqEnv (StringCloneEnv targetPeer.name) FreeOnlyEvs)))
      (defaultW4LoadCum (max maxVal fileCap) deserCum +
        w4BoxedStepCum ikit.trustBoxSize c₂ + (2 * 40 + 9539))
      (defaultW4LoadLive (max maxVal fileCap) deserLive +
        w4BoxedStepLive ikit.trustBoxSize l₂ + (40 + 8195))
      (max (defaultW4LoadPeak (max maxVal fileCap) deserPeak)
        (defaultW4LoadLive (max maxVal fileCap) deserLive +
          max (w4BoxedStepPeak ikit.trustBoxSize p₂)
            (w4BoxedStepLive ikit.trustBoxSize l₂ + (40 + 8195))))
      (max (defaultW4LoadMaxReq (max maxVal fileCap) deserMaxReq)
        (max (w4BoxedStepMaxReq ikit.trustBoxSize r₂) 40)) := by
  have hL : PhaseCreditSpec fineCostModel (LoadStepEnv kit₀ kitEnv₀ dir targetPeer.val) _ _ _ _ :=
    w4_defaultLoadStep_fine_phaseCredit hdc hdir hpeer hcap hDeser
  have hT := trustStepEnv_phaseCredit fineCostModel_modelHyps
    ikit ikitEnv ist targetPeer.val remoteIdKey .receiving hTrust
  have hCl := phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps
    (stringClone_phaseCredit_aff fineCostModel_modelHyps hpeer)
  exact (hL.seq (hT.seq hCl)).mono (by omega) (by omega) (by omega) (by omega)

end DefaultBoxedSteps

/-! ## Section 5: `SessDeserializeCancelEnv` & `RecordDeserializeCancelEnv` Specializations -/

/-- Event-predicate (`ofEventPred P`) `PhaseGroupSpec fineCostModel` (`45 * FineScale + g_deser`)
with zero file-cap premise. -/
theorem defaultLoadPollEnv_eventPred_fine_groupSpec
    {rd : ReadRule} {Scope : SessionRecord (List (BitVec 8)) → Prop} {P : List AllocEvent → Prop}
    {F0 : FsFiles} {dir : DirGhost} {rem : AddrVal} {g_deser : Nat}
    (hrem : rem.name.length ≤ 40)
    (hP : PhaseGroupSpec fineCostModel P g_deser) :
    PhaseGroupSpec fineCostModel
      (cliSessionKitLoadPollEnv rd Scope (AddrTextValEnv DecimalEnv)
        (DirGetEnv PathEnv (ReadFileRuleEnv rd) rd) (ofEventPred P) F0 dir rem)
      (45 * FineScale + g_deser) := by
  have h1 := addrTextValEnv_decimal_fine_groupSpec rem hrem
  have h2 := dirGetEnv_path_readFile_groupSpec fineCostModel rd F0 dir (addressText rem)
  have h3 : PhaseGroupSpec fineCostModel
      (OptLoadDeserEnv Scope (ofEventPred P) (dir.get rd F0 (addressText rem))) g_deser := by
    unfold OptLoadDeserEnv
    cases dir.get rd F0 (addressText rem) with
    | error _ => exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
    | ok bs =>
      cases bs with
      | nil => exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
      | cons _ _ => exact { groups_le := fun st0 {_} ⟨_, _, _, hd⟩ => hP.groups_le st0 hd }
  have h3f := (h3.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono (Nat.le_of_eq (Nat.add_zero _))
  unfold cliSessionKitLoadPollEnv
  exact (h1.seq (h2.seq h3f)).mono (by omega)

/-- Placed Block `46` (`cliGhostExterns g (cliExternsPlaced mmpl W)`) contract instantiated at
`SessDeserializeCancelEnv`. -/
theorem sessDeserialize_cli_dcan_placed_ok [LibsignalPlacement]
    (mmpl : Arm64.Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {M : AllocCostModel} [HasFineReallocCredit M]
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim g) (hsub : ∀ r, Scope r → scopeKit r) :
    subroutine_ok (lsProg_46 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced Scope A lim SessDeserializeCancelEnv) :=
  sessDeserialize_cli_of_sessDeserEvents_placed_ok mmpl g W hG hsub
    (fun r hr => sessDeserEvents_mem_sessDeserializeCancelEnv (hsub r hr))

/-- Placed Block `46` (`cliGhostExterns g (cliExternsPlaced mmpl W)`) contract instantiated at
`ofBytesEnv RecordDeserializeCancelEnv`. -/
theorem sessDeserialize_cli_dcan_byBytes_placed_ok [LibsignalPlacement]
    (mmpl : Arm64.Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {M : AllocCostModel} [HasFineReallocCredit M]
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim g) (hsub : ∀ r, Scope r → scopeKit r) :
    subroutine_ok (lsProg_46 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced Scope A lim (ofBytesEnv RecordDeserializeCancelEnv)) :=
  sessDeserialize_cli_of_bytesEnv_placed_ok mmpl g W hG hsub
    (fun r hr => sessDeserEvents_mem_recordDeserializeCancelEnv (hsub r hr))

/-- Placed Block `569` (`load_session::{closure#0}`) contract instantiated at
`SessDeserializeCancelEnv` with zero external deserialize hypotheses. -/
theorem sessLoadPoll_dcan_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} [HasFineReallocCredit M]
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {AddrEnv : AddrGhost → List AllocEvent → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {addrProg getProg : Program} {addrBlk getBlk : Nat}
    [IsLsBlockProg addrProg addrBlk H] [IsLsBlockProg getProg getBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {addrStk getStk stk : Nat}
    (hC : AllocContractsXCliPlaced A lim H) (hAB : AllocContractsBudgetPlaced M A lim H)
    (hAddr : subroutine_ok addrProg (lsmpl.base 594) (addrTextSpecPlaced A lim AddrEnv addrStk))
    (hGet : subroutine_ok getProg (lsmpl.base 589) (dirGetSpecPlaced rd pathOk A lim GetEnv getStk))
    (hsub : ∀ r, Scope r → scopeKit r) (hFs : TraceFsSound (lsProg_569 H))
    (hstk : 0x350 + max (max addrStk getStk) (max recDeserializeStack extHookStack) ≤ stk)
    (hAddrBlk : addrBlk < 619 := by decide)
    (hAddrUnmut : (addrBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (lsProg_569 H) (lsmpl.base 569)
      (sessLoadPollSpecPlaced rd pathOk Scope A lim
        (CliLoadPollEnv rd Scope AddrEnv GetEnv SessDeserializeCancelEnv) stk) :=
  sessLoadPoll_of_sessDeserEvents_placed_ok hC hAB hAddr hGet hsub
    (fun r hr => sessDeserEvents_mem_sessDeserializeCancelEnv (hsub r hr))
    hFs hstk hAddrBlk hAddrUnmut hGetBlk hGetUnmut

/-- Placed Block `569` (`load_session::{closure#0}`) contract instantiated at
`ofBytesEnv RecordDeserializeCancelEnv` with zero external deserialize hypotheses. -/
theorem sessLoadPoll_dcan_byBytes_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} [HasFineReallocCredit M]
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {AddrEnv : AddrGhost → List AllocEvent → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {addrProg getProg : Program} {addrBlk getBlk : Nat}
    [IsLsBlockProg addrProg addrBlk H] [IsLsBlockProg getProg getBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {addrStk getStk stk : Nat}
    (hC : AllocContractsXCliPlaced A lim H) (hAB : AllocContractsBudgetPlaced M A lim H)
    (hAddr : subroutine_ok addrProg (lsmpl.base 594) (addrTextSpecPlaced A lim AddrEnv addrStk))
    (hGet : subroutine_ok getProg (lsmpl.base 589) (dirGetSpecPlaced rd pathOk A lim GetEnv getStk))
    (hsub : ∀ r, Scope r → scopeKit r) (hFs : TraceFsSound (lsProg_569 H))
    (hstk : 0x350 + max (max addrStk getStk) (max recDeserializeStack extHookStack) ≤ stk)
    (hAddrBlk : addrBlk < 619 := by decide)
    (hAddrUnmut : (addrBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (lsProg_569 H) (lsmpl.base 569)
      (sessLoadPollSpecPlaced rd pathOk Scope A lim
        (CliLoadPollEnv rd Scope AddrEnv GetEnv (ofBytesEnv RecordDeserializeCancelEnv)) stk) :=
  sessLoadPoll_of_sessDeserEvents_placed_ok hC hAB hAddr hGet hsub
    (fun r hr => sessDeserEvents_mem_recordDeserializeCancelEnv (hsub r hr))
    hFs hstk hAddrBlk hAddrUnmut hGetBlk hGetUnmut

section DcanKitAssembly

variable [LibsignalPlacement] {M : AllocCostModel} [HasFineReallocCredit M]
  {A : RustCliAllocBudget M} {lim : BudgetLimits} {F0 : FsFiles}
  {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost}
  {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
  {readStk s1 s2 s3 s4 : Nat} {vtSym idVtSym : String}

/-- Unconditional CLI `SessionOnlyKitPlacedOkSE` bundle at `SessDeserializeCancelEnv`. -/
theorem cliSessKitOkSE_cli_dcan_placed (mmpl : Arm64.Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks)
    {readProg : Program} {jRead : Nat}
    [IsLsBlockProg readProg jRead (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim g)
    (hAzFsT : HookFsTraced IsFsC g.allocZeroed)
    (hStrFsT : ∀ f, g.stringClone = some f → HookFsTraced IsFsC f)
    (hRead : subroutine_ok readProg (lsρ lsReadFileSym)
      (withLsCodeRoLoaded lsmpl (readFileSpecPlaced cliIo.rd cliWrOk A lim readStk ReadEnv)))
    (hsub : ∀ r, Scope r → scopeKit r)
    (hs1 : loadShimNeedPlaced ≤ s1) (hs2 : loadPollNeedPlaced readStk ≤ s2)
    (hs3 : storeShimNeedPlaced ≤ s3) (hs4 : storePollNeedXPlaced ≤ s4)
    (hjRead : jRead < 619 := by decide)
    (hjRead_unmut : (jRead ∈ libsignalMutatedBlocks) = false := by decide) :
    SessionOnlyKitPlacedOkSE A lim
      (cliSessionKitSpecPlaced A.repAlloc cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4 vtSym idVtSym)
      (cliSessionKitDefaultBudgetEnv A.repAlloc cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4
        SessDeserializeCancelEnv vtSym idVtSym ReadEnv)
      Scope encodeRecord (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  cliSessKitOkSE_cli_of_sessDeserEvents_placed mmpl g W hDropNz hG hAzFsT hStrFsT hRead hsub
    (fun r hr => sessDeserEvents_mem_sessDeserializeCancelEnv (hsub r hr))
    hs1 hs2 hs3 hs4 hjRead hjRead_unmut

theorem cliSessKitRoClOkSE_cli_dcan_placed (mmpl : Arm64.Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks)
    {readProg : Program} {jRead : Nat}
    [IsLsBlockProg readProg jRead (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim g)
    (hAzFsT : HookFsTraced IsFsC g.allocZeroed)
    (hStrFsT : ∀ f, g.stringClone = some f → HookFsTraced IsFsC f)
    (hRead : subroutine_ok readProg (lsρ lsReadFileSym)
      (withLsCodeRoLoaded lsmpl (readFileSpecPlaced cliIo.rd cliWrOk A lim readStk ReadEnv)))
    (hsub : ∀ r, Scope r → scopeKit r)
    (hs1 : loadShimNeedPlaced ≤ s1) (hs2 : loadPollNeedPlaced readStk ≤ s2)
    (hs3 : storeShimNeedPlaced ≤ s3) (hs4 : storePollNeedXPlaced ≤ s4)
    (hjRead : jRead < 619 := by decide)
    (hjRead_unmut : (jRead ∈ libsignalMutatedBlocks) = false := by decide) :
    SessionOnlyKitPlacedRoClOkSE A lim
      (cliSessionKitSpecPlaced A.repAlloc cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4 vtSym idVtSym)
      (cliSessionKitDefaultBudgetEnv A.repAlloc cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4
        SessDeserializeCancelEnv vtSym idVtSym ReadEnv)
      Scope encodeRecord (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  cliSessKitOkSE_cli_dcan_placed mmpl g W hDropNz hG hAzFsT hStrFsT hRead hsub
    hs1 hs2 hs3 hs4 hjRead hjRead_unmut

theorem cliSessKitOkSE_cli_dcan_readHook (mmpl : Arm64.Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim g)
    (hAzFsT : HookFsTraced IsFsC g.allocZeroed)
    (hStrFsT : ∀ f, g.stringClone = some f → HookFsTraced IsFsC f)
    (hReadHook : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk A lim readStk ReadEnv))
    (hsub : ∀ r, Scope r → scopeKit r)
    (hs1 : loadShimNeedPlaced ≤ s1) (hs2 : loadPollNeedPlaced readStk ≤ s2)
    (hs3 : storeShimNeedPlaced ≤ s3) (hs4 : storePollNeedXPlaced ≤ s4) :
    SessionOnlyKitPlacedOkSE A lim
      (cliSessionKitSpecPlaced A.repAlloc cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4 vtSym idVtSym)
      (cliSessionKitDefaultBudgetEnv A.repAlloc cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4
        SessDeserializeCancelEnv vtSym idVtSym ReadEnv)
      Scope encodeRecord (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  cliSessKitOkSE_cli_of_sessDeserEvents_readHook mmpl g W hDropNz hG hAzFsT hStrFsT hReadHook hsub
    (fun r hr => sessDeserEvents_mem_sessDeserializeCancelEnv (hsub r hr)) hs1 hs2 hs3 hs4

/-- Unconditional CLI `SessionOnlyKitPlacedOkSE` bundle at `ofBytesEnv RecordDeserializeCancelEnv`. -/
theorem cliSessKitOkSE_cli_dcan_byBytes_placed (mmpl : Arm64.Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks)
    {readProg : Program} {jRead : Nat}
    [IsLsBlockProg readProg jRead (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim g)
    (hAzFsT : HookFsTraced IsFsC g.allocZeroed)
    (hStrFsT : ∀ f, g.stringClone = some f → HookFsTraced IsFsC f)
    (hRead : subroutine_ok readProg (lsρ lsReadFileSym)
      (withLsCodeRoLoaded lsmpl (readFileSpecPlaced cliIo.rd cliWrOk A lim readStk ReadEnv)))
    (hsub : ∀ r, Scope r → scopeKit r)
    (hs1 : loadShimNeedPlaced ≤ s1) (hs2 : loadPollNeedPlaced readStk ≤ s2)
    (hs3 : storeShimNeedPlaced ≤ s3) (hs4 : storePollNeedXPlaced ≤ s4)
    (hjRead : jRead < 619 := by decide)
    (hjRead_unmut : (jRead ∈ libsignalMutatedBlocks) = false := by decide) :
    SessionOnlyKitPlacedOkSE A lim
      (cliSessionKitSpecPlaced A.repAlloc cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4 vtSym idVtSym)
      (cliSessionKitDefaultBudgetEnv A.repAlloc cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4
        (ofBytesEnv RecordDeserializeCancelEnv) vtSym idVtSym ReadEnv)
      Scope encodeRecord (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  cliSessKitOkSE_cli_of_sessDeserEvents_placed mmpl g W hDropNz hG hAzFsT hStrFsT hRead hsub
    (fun r hr => sessDeserEvents_mem_recordDeserializeCancelEnv (hsub r hr))
    hs1 hs2 hs3 hs4 hjRead hjRead_unmut

theorem cliSessKitRoClOkSE_cli_dcan_byBytes_placed (mmpl : Arm64.Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks)
    {readProg : Program} {jRead : Nat}
    [IsLsBlockProg readProg jRead (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim g)
    (hAzFsT : HookFsTraced IsFsC g.allocZeroed)
    (hStrFsT : ∀ f, g.stringClone = some f → HookFsTraced IsFsC f)
    (hRead : subroutine_ok readProg (lsρ lsReadFileSym)
      (withLsCodeRoLoaded lsmpl (readFileSpecPlaced cliIo.rd cliWrOk A lim readStk ReadEnv)))
    (hsub : ∀ r, Scope r → scopeKit r)
    (hs1 : loadShimNeedPlaced ≤ s1) (hs2 : loadPollNeedPlaced readStk ≤ s2)
    (hs3 : storeShimNeedPlaced ≤ s3) (hs4 : storePollNeedXPlaced ≤ s4)
    (hjRead : jRead < 619 := by decide)
    (hjRead_unmut : (jRead ∈ libsignalMutatedBlocks) = false := by decide) :
    SessionOnlyKitPlacedRoClOkSE A lim
      (cliSessionKitSpecPlaced A.repAlloc cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4 vtSym idVtSym)
      (cliSessionKitDefaultBudgetEnv A.repAlloc cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4
        (ofBytesEnv RecordDeserializeCancelEnv) vtSym idVtSym ReadEnv)
      Scope encodeRecord (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  cliSessKitOkSE_cli_dcan_byBytes_placed mmpl g W hDropNz hG hAzFsT hStrFsT hRead hsub
    hs1 hs2 hs3 hs4 hjRead hjRead_unmut

theorem cliSessKitOkSE_cli_dcan_byBytes_readHook (mmpl : Arm64.Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim g)
    (hAzFsT : HookFsTraced IsFsC g.allocZeroed)
    (hStrFsT : ∀ f, g.stringClone = some f → HookFsTraced IsFsC f)
    (hReadHook : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk A lim readStk ReadEnv))
    (hsub : ∀ r, Scope r → scopeKit r)
    (hs1 : loadShimNeedPlaced ≤ s1) (hs2 : loadPollNeedPlaced readStk ≤ s2)
    (hs3 : storeShimNeedPlaced ≤ s3) (hs4 : storePollNeedXPlaced ≤ s4) :
    SessionOnlyKitPlacedOkSE A lim
      (cliSessionKitSpecPlaced A.repAlloc cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4 vtSym idVtSym)
      (cliSessionKitDefaultBudgetEnv A.repAlloc cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4
        (ofBytesEnv RecordDeserializeCancelEnv) vtSym idVtSym ReadEnv)
      Scope encodeRecord (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  cliSessKitOkSE_cli_of_sessDeserEvents_readHook mmpl g W hDropNz hG hAzFsT hStrFsT hReadHook hsub
    (fun r hr => sessDeserEvents_mem_recordDeserializeCancelEnv (hsub r hr)) hs1 hs2 hs3 hs4

end DcanKitAssembly

/-- Concrete `LoadPoll` envelope implication at `SessDeserializeCancelEnv` →
`CliSessLoadPollEnv rd RecordDeserializeCancelEnv` (zero `hDeser` premise). -/
theorem cliSessionKitLoadPollEnv_dcan_imp_cliSessLoadPollEnv
    {rd : ReadRule} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {AddrValEnv : AddrVal → List AllocEvent → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {F0 : FsFiles} {d : DirGhost} {peer : AddrGhost} {rem : AddrVal}
    (hrem : rem = peer.val)
    (hAddr : ∀ evs, AddrValEnv peer.val evs → CliAddrTextEnv peer evs)
    (hGet : ∀ evs, GetEnv F0 d (addressText peer.val) evs →
      CliDirGetEnv (ReadFileRuleEnv rd) F0 d (addressText peer.val) evs)
    (hCap : ∀ bs, d.get rd F0 (addressText peer.val) = .ok bs → bs.length ≤ 2097152) :
    ∀ evs, cliSessionKitLoadPollEnv rd Scope AddrValEnv GetEnv SessDeserializeCancelEnv F0 d rem evs →
      CliSessLoadPollEnv rd RecordDeserializeCancelEnv F0 d peer evs :=
  cliSessionKitLoadPollEnv_imp_cliSessLoadPollEnv hrem hAddr hGet hCap
    (fun _ _ _ hd => sessDeserializeCancelEnv_imp_recordDeserializeCancelEnv hd)

/-- Concrete `LoadPoll` envelope implication at `ofBytesEnv RecordDeserializeCancelEnv` →
`CliSessLoadPollEnv rd RecordDeserializeCancelEnv` (zero `hDeser` premise). -/
theorem cliSessionKitLoadPollEnv_dcan_byBytes_imp_cliSessLoadPollEnv
    {rd : ReadRule} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {AddrValEnv : AddrVal → List AllocEvent → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {F0 : FsFiles} {d : DirGhost} {peer : AddrGhost} {rem : AddrVal}
    (hrem : rem = peer.val)
    (hAddr : ∀ evs, AddrValEnv peer.val evs → CliAddrTextEnv peer evs)
    (hGet : ∀ evs, GetEnv F0 d (addressText peer.val) evs →
      CliDirGetEnv (ReadFileRuleEnv rd) F0 d (addressText peer.val) evs)
    (hCap : ∀ bs, d.get rd F0 (addressText peer.val) = .ok bs → bs.length ≤ 2097152) :
    ∀ evs, cliSessionKitLoadPollEnv rd Scope AddrValEnv GetEnv
        (ofBytesEnv RecordDeserializeCancelEnv) F0 d rem evs →
      CliSessLoadPollEnv rd RecordDeserializeCancelEnv F0 d peer evs :=
  cliSessionKitLoadPollEnv_imp_cliSessLoadPollEnv hrem hAddr hGet hCap (fun _ _ _ hd => hd)

section DcanW1ToW4LoadEq

variable [LibsignalPlacement] {A : RustAlloc} {F : FsFiles} {pathOk : List (BitVec 8) → Prop}
  {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost}
  {s1 s2 s3 s4 fileCap : Nat} {vtSym idVtSym : String}
  {AddrValEnv : AddrVal → List AllocEvent → Prop}
  {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
  {SerValEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
  {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
  {rem : AddrVal}

theorem w1_hLoadEq_dcan (hrem : rem = peer.val) (hfc : fileCap ≤ 2097152)
    (hSessFileCap : ∀ bs,
      cliIo.rd F (pathOf StoresGhost.opened.sessions.path (addressText peer.val)) = .ok bs →
      bs.length ≤ fileCap)
    (hAddr : ∀ evs, AddrValEnv peer.val evs → CliAddrTextEnv peer evs)
    (hGet : ∀ evs, GetEnv F StoresGhost.opened.sessions (addressText peer.val) evs →
      CliDirGetEnv (ReadFileRuleEnv cliIo.rd) F StoresGhost.opened.sessions (addressText peer.val) evs) :
    ∀ evs,
      (cliSessionKitBudgetEnv A cliIo.rd F pathOk Scope peer s1 s2 s3 s4
        AddrValEnv GetEnv SessDeserializeCancelEnv SerValEnv PutEnv vtSym idVtSym).loadPollEnv
        StoresGhost.opened.sessions rem evs →
      CliSessLoadPollEnv cliIo.rd RecordDeserializeCancelEnv F StoresGhost.opened.sessions peer evs :=
  w1_hLoadEq_of_cliSessionKitBudgetEnv hrem hfc hSessFileCap hAddr hGet
    (fun _ _ _ hd => sessDeserializeCancelEnv_imp_recordDeserializeCancelEnv hd)

theorem w2_hLoadEq_dcan (hrem : rem = peer.val) (hfc : fileCap ≤ 2097152)
    (hSessFileCap : ∀ bs,
      cliIo.rd F (pathOf StoresGhost.opened.sessions.path (addressText peer.val)) = .ok bs →
      bs.length ≤ fileCap)
    (hAddr : ∀ evs, AddrValEnv peer.val evs → CliAddrTextEnv peer evs)
    (hGet : ∀ evs, GetEnv F StoresGhost.opened.sessions (addressText peer.val) evs →
      CliDirGetEnv (ReadFileRuleEnv cliIo.rd) F StoresGhost.opened.sessions (addressText peer.val) evs) :
    ∀ evs,
      (cliSessionKitBudgetEnv A cliIo.rd F pathOk Scope peer s1 s2 s3 s4
        AddrValEnv GetEnv SessDeserializeCancelEnv SerValEnv PutEnv vtSym idVtSym).loadPollEnv
        StoresGhost.opened.sessions rem evs →
      CliSessLoadPollEnv cliIo.rd RecordDeserializeCancelEnv F StoresGhost.opened.sessions peer evs :=
  w1_hLoadEq_dcan hrem hfc hSessFileCap hAddr hGet

theorem w3_hLoadEq_dcan (hrem : rem = peer.val) (hfc : fileCap ≤ 2097152)
    (hSessFileCap : ∀ bs,
      cliIo.rd F (pathOf StoresGhost.opened.sessions.path (addressText peer.val)) = .ok bs →
      bs.length ≤ fileCap)
    (hAddr : ∀ evs, AddrValEnv peer.val evs → CliAddrTextEnv peer evs)
    (hGet : ∀ evs, GetEnv F StoresGhost.opened.sessions (addressText peer.val) evs →
      CliDirGetEnv (ReadFileRuleEnv cliIo.rd) F StoresGhost.opened.sessions (addressText peer.val) evs) :
    ∀ evs,
      (cliSessionKitBudgetEnv A cliIo.rd F pathOk Scope peer s1 s2 s3 s4
        AddrValEnv GetEnv SessDeserializeCancelEnv SerValEnv PutEnv vtSym idVtSym).loadPollEnv
        StoresGhost.opened.sessions rem evs →
      CliSessLoadPollEnv cliIo.rd RecordDeserializeCancelEnv F StoresGhost.opened.sessions peer evs :=
  w1_hLoadEq_dcan hrem hfc hSessFileCap hAddr hGet

theorem w4_hLoadEq_dcan (hrem : rem = peer.val) (hfc : fileCap ≤ 2097152)
    (hSessFileCap : ∀ bs,
      cliIo.rd F (pathOf StoresGhost.opened.sessions.path (addressText peer.val)) = .ok bs →
      bs.length ≤ fileCap)
    (hAddr : ∀ evs, AddrValEnv peer.val evs → CliAddrTextEnv peer evs)
    (hGet : ∀ evs, GetEnv F StoresGhost.opened.sessions (addressText peer.val) evs →
      CliDirGetEnv (ReadFileRuleEnv cliIo.rd) F StoresGhost.opened.sessions (addressText peer.val) evs) :
    ∀ evs,
      (cliSessionKitBudgetEnv A cliIo.rd F pathOk Scope peer s1 s2 s3 s4
        AddrValEnv GetEnv SessDeserializeCancelEnv SerValEnv PutEnv vtSym idVtSym).loadPollEnv
        StoresGhost.opened.sessions rem evs →
      CliSessLoadPollEnv cliIo.rd RecordDeserializeCancelEnv F StoresGhost.opened.sessions peer evs :=
  w1_hLoadEq_dcan hrem hfc hSessFileCap hAddr hGet

theorem w1_hLoadEq_dcan_byBytes (hrem : rem = peer.val) (hfc : fileCap ≤ 2097152)
    (hSessFileCap : ∀ bs,
      cliIo.rd F (pathOf StoresGhost.opened.sessions.path (addressText peer.val)) = .ok bs →
      bs.length ≤ fileCap)
    (hAddr : ∀ evs, AddrValEnv peer.val evs → CliAddrTextEnv peer evs)
    (hGet : ∀ evs, GetEnv F StoresGhost.opened.sessions (addressText peer.val) evs →
      CliDirGetEnv (ReadFileRuleEnv cliIo.rd) F StoresGhost.opened.sessions (addressText peer.val) evs) :
    ∀ evs,
      (cliSessionKitBudgetEnv A cliIo.rd F pathOk Scope peer s1 s2 s3 s4
        AddrValEnv GetEnv (ofBytesEnv RecordDeserializeCancelEnv) SerValEnv PutEnv vtSym idVtSym).loadPollEnv
        StoresGhost.opened.sessions rem evs →
      CliSessLoadPollEnv cliIo.rd RecordDeserializeCancelEnv F StoresGhost.opened.sessions peer evs :=
  w1_hLoadEq_of_cliSessionKitBudgetEnv hrem hfc hSessFileCap hAddr hGet (fun _ _ _ hd => hd)

theorem w2_hLoadEq_dcan_byBytes (hrem : rem = peer.val) (hfc : fileCap ≤ 2097152)
    (hSessFileCap : ∀ bs,
      cliIo.rd F (pathOf StoresGhost.opened.sessions.path (addressText peer.val)) = .ok bs →
      bs.length ≤ fileCap)
    (hAddr : ∀ evs, AddrValEnv peer.val evs → CliAddrTextEnv peer evs)
    (hGet : ∀ evs, GetEnv F StoresGhost.opened.sessions (addressText peer.val) evs →
      CliDirGetEnv (ReadFileRuleEnv cliIo.rd) F StoresGhost.opened.sessions (addressText peer.val) evs) :
    ∀ evs,
      (cliSessionKitBudgetEnv A cliIo.rd F pathOk Scope peer s1 s2 s3 s4
        AddrValEnv GetEnv (ofBytesEnv RecordDeserializeCancelEnv) SerValEnv PutEnv vtSym idVtSym).loadPollEnv
        StoresGhost.opened.sessions rem evs →
      CliSessLoadPollEnv cliIo.rd RecordDeserializeCancelEnv F StoresGhost.opened.sessions peer evs :=
  w1_hLoadEq_dcan_byBytes hrem hfc hSessFileCap hAddr hGet

theorem w3_hLoadEq_dcan_byBytes (hrem : rem = peer.val) (hfc : fileCap ≤ 2097152)
    (hSessFileCap : ∀ bs,
      cliIo.rd F (pathOf StoresGhost.opened.sessions.path (addressText peer.val)) = .ok bs →
      bs.length ≤ fileCap)
    (hAddr : ∀ evs, AddrValEnv peer.val evs → CliAddrTextEnv peer evs)
    (hGet : ∀ evs, GetEnv F StoresGhost.opened.sessions (addressText peer.val) evs →
      CliDirGetEnv (ReadFileRuleEnv cliIo.rd) F StoresGhost.opened.sessions (addressText peer.val) evs) :
    ∀ evs,
      (cliSessionKitBudgetEnv A cliIo.rd F pathOk Scope peer s1 s2 s3 s4
        AddrValEnv GetEnv (ofBytesEnv RecordDeserializeCancelEnv) SerValEnv PutEnv vtSym idVtSym).loadPollEnv
        StoresGhost.opened.sessions rem evs →
      CliSessLoadPollEnv cliIo.rd RecordDeserializeCancelEnv F StoresGhost.opened.sessions peer evs :=
  w1_hLoadEq_dcan_byBytes hrem hfc hSessFileCap hAddr hGet

theorem w4_hLoadEq_dcan_byBytes (hrem : rem = peer.val) (hfc : fileCap ≤ 2097152)
    (hSessFileCap : ∀ bs,
      cliIo.rd F (pathOf StoresGhost.opened.sessions.path (addressText peer.val)) = .ok bs →
      bs.length ≤ fileCap)
    (hAddr : ∀ evs, AddrValEnv peer.val evs → CliAddrTextEnv peer evs)
    (hGet : ∀ evs, GetEnv F StoresGhost.opened.sessions (addressText peer.val) evs →
      CliDirGetEnv (ReadFileRuleEnv cliIo.rd) F StoresGhost.opened.sessions (addressText peer.val) evs) :
    ∀ evs,
      (cliSessionKitBudgetEnv A cliIo.rd F pathOk Scope peer s1 s2 s3 s4
        AddrValEnv GetEnv (ofBytesEnv RecordDeserializeCancelEnv) SerValEnv PutEnv vtSym idVtSym).loadPollEnv
        StoresGhost.opened.sessions rem evs →
      CliSessLoadPollEnv cliIo.rd RecordDeserializeCancelEnv F StoresGhost.opened.sessions peer evs :=
  w1_hLoadEq_dcan_byBytes hrem hfc hSessFileCap hAddr hGet

end DcanW1ToW4LoadEq

/-! ### Closed `2 MiB` `LoadPoll` Constants & `FitsEnv` Closure -/

private theorem optLargeCost_2MiB_eq : optLargeCost fineCostModel 2097152 = 2105347 := by
  rw [optLargeCost_fine_of_gt (by decide : 135167 < 2097152), fineCostModel_largeCost_eq]

private theorem fineReadFileCum_le_2MiB (fc : Nat) : fineReadFileCum fc ≤ 573818 := by
  unfold fineReadFileCum; split_ifs <;> decide

private theorem max_738_fineReadFileCum_le_2MiB (fc : Nat) :
    max 738 (fineReadFileCum fc) ≤ 573818 := by
  unfold fineReadFileCum; split_ifs <;> decide

theorem fineReadFileLive_le_2MiB {fc : Nat} (hfc : fc ≤ 2097152) :
    fineReadFileLive fc ≤ 2105347 := by
  unfold fineReadFileLive
  split_ifs with hle
  · decide
  · exact Nat.max_le.mpr
      ⟨optLargeCost_2MiB_eq ▸ optLargeCost_fine_mono hfc, Nat.le_refl 2105347⟩

theorem fineReadFilePeak_le_2MiB {fc : Nat} (hfc : fc ≤ 2097152) :
    fineReadFilePeak fc ≤ 3162118 := by
  unfold fineReadFilePeak
  split_ifs with hle
  · decide
  · refine Nat.max_le.mpr ⟨?_, Nat.le_refl 3162118⟩
    exact Nat.le_trans (optLargeCost_2MiB_eq ▸ optLargeCost_fine_mono hfc) (by decide)

theorem fineReadFileMaxReq_le_2MiB {fc : Nat} (hfc : fc ≤ 2097152) :
    fineReadFileMaxReq fc ≤ 2097152 := by
  unfold fineReadFileMaxReq; split_ifs <;> omega

/-- Closed `CliSessLoadPollEnv` `cumSmall` bound on `RecordDeserializeCancelEnv` at `≤ 2 MiB`
(`17,495,245` B). -/
def sessLoadPollCancel2MiBCum : Nat := sessLoadPollTightDeltaCum 2097152 deserCancelFineCum

/-- `P64` `CliSessLoadPollEnv` `cumSmall` bound at `≤ 2 MiB` (`20,022,520` B). -/
def sessLoadPollCancel2MiBCumP64 : Nat := sessLoadPollTightDeltaCum 2097152 19417728

/-- `P192` `CliSessLoadPollEnv` `cumSmall` bound at `≤ 2 MiB` (`21,243,512` B). -/
def sessLoadPollCancel2MiBCumP192 : Nat := sessLoadPollTightDeltaCum 2097152 20638720

/-- Closed `cliSessionKitDefaultBudgetEnv` `loadPollEnv` `cumSmall` bound at `≤ 2 MiB`
(`17,496,721` B). -/
def defaultLoadPollCancel2MiBCum : Nat := defaultLoadPollTightDeltaCum 2097152 deserCancelFineCum

/-- `P64` `cliSessionKitDefaultBudgetEnv` `loadPollEnv` `cumSmall` bound (`20,023,996` B). -/
def defaultLoadPollCancel2MiBCumP64 : Nat := defaultLoadPollTightDeltaCum 2097152 19417728

/-- `P192` `cliSessionKitDefaultBudgetEnv` `loadPollEnv` `cumSmall` bound (`21,244,988` B). -/
def defaultLoadPollCancel2MiBCumP192 : Nat := defaultLoadPollTightDeltaCum 2097152 20638720

/-- Closed `LoadPoll` post-phase `liveLarge` bound on `RecordDeserializeCancelEnv` at `≤ 2 MiB`
(`5,316,629` B). -/
def loadPollCancel2MiBLive : Nat := 2105347 + deserCancelFineLive

/-- Closed `LoadPoll` transient `peakLarge` bound on `RecordDeserializeCancelEnv` at `≤ 2 MiB`
(`7,421,976` B). -/
def loadPollCancel2MiBPeak : Nat := max 3162118 (2105347 + deserCancelFinePeak)

/-- Closed `LoadPoll` `maxReq` cap at `≤ 2 MiB` (`2,097,152` B). -/
def loadPollCancel2MiBMaxReq : Nat := deserCancelFineMaxReq

/-- Closed `CliSessLoadPollEnv` `groupsScaled` bound on `RecordDeserializeCancelEnv`
(`347,214,604`, `5,299` groups). -/
def cliSessLoadPollCancelGrpS : Nat := 42 * FineScale + deserCancelFineGrpS

/-- Ceiling group count of `cliSessLoadPollCancelGrpS` (`5,299` groups). -/
def cliSessLoadPollCancelGroups : Nat := (cliSessLoadPollCancelGrpS + FineScale - 1) / FineScale

def cliSessLoadPollCancelGrpSP16_48 : Nat := 42 * FineScale + 345780512

def cliSessLoadPollCancelGrpSP64 : Nat := 42 * FineScale + 346829088

def cliSessLoadPollCancelGrpSP192 : Nat := 42 * FineScale + 371994912

/-- Closed `cliSessionKitDefaultBudgetEnv` `loadPollEnv` `groupsScaled` bound on
`RecordDeserializeCancelEnv` (`347,411,212`, `5,302` groups). -/
def defaultLoadPollCancelGrpS : Nat := 45 * FineScale + deserCancelFineGrpS

/-- Ceiling group count of `defaultLoadPollCancelGrpS` (`5,302` groups). -/
def defaultLoadPollCancelGroups : Nat := (defaultLoadPollCancelGrpS + FineScale - 1) / FineScale

def defaultLoadPollCancelGrpSP16_48 : Nat := 45 * FineScale + 345780512

def defaultLoadPollCancelGrpSP64 : Nat := 45 * FineScale + 346829088

def defaultLoadPollCancelGrpSP192 : Nat := 45 * FineScale + 371994912

theorem loadPollCancel2MiB_constants_eq :
    sessLoadPollCancel2MiBCum = 17495245 ∧
    sessLoadPollCancel2MiBCumP64 = 20022520 ∧
    sessLoadPollCancel2MiBCumP192 = 21243512 ∧
    defaultLoadPollCancel2MiBCum = 17496721 ∧
    defaultLoadPollCancel2MiBCumP64 = 20023996 ∧
    defaultLoadPollCancel2MiBCumP192 = 21244988 ∧
    loadPollCancel2MiBLive = 5316629 ∧
    loadPollCancel2MiBPeak = 7421976 ∧
    loadPollCancel2MiBMaxReq = 2097152 ∧
    cliSessLoadPollCancelGrpS = 347214604 ∧
    cliSessLoadPollCancelGroups = 5299 ∧
    cliSessLoadPollCancelGrpSP16_48 = 348533024 ∧
    cliSessLoadPollCancelGrpSP64 = 349581600 ∧
    cliSessLoadPollCancelGrpSP192 = 374747424 ∧
    defaultLoadPollCancelGrpS = 347411212 ∧
    defaultLoadPollCancelGroups = 5302 ∧
    defaultLoadPollCancelGrpSP16_48 = 348729632 ∧
    defaultLoadPollCancelGrpSP64 = 349778208 ∧
    defaultLoadPollCancelGrpSP192 = 374944032 := by
  decide

/-- Parametric `fc` `PhaseCreditSpec` for `CliSessLoadPollEnv rd RecordDeserializeCancelEnv`. -/
theorem cliSessLoadPollEnv_dcan_fine_phaseCredit_tight
    {rd : ReadRule} {files : FsFiles} {dir : DirGhost} {peer : AddrGhost}
    {maxDir maxEntries maxVal fileCap : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir) (hdir : maxDir ≤ 64)
    (hpeer : peer.name.bytes.length ≤ 40)
    (hcap : ∀ bs, rd files (pathOf dir.path (addressText peer.val)) = .ok bs → bs.length ≤ fileCap) :
    PhaseCreditSpec fineCostModel
      (CliSessLoadPollEnv rd RecordDeserializeCancelEnv files dir peer)
      (sessLoadPollTightDeltaCum (max maxVal fileCap) deserCancelFineCum)
      (sessLoadPollTightDeltaLive (max maxVal fileCap) deserCancelFineLive)
      (sessLoadPollTightDeltaPeak (max maxVal fileCap) deserCancelFinePeak)
      (sessLoadPollTightMaxReq (max maxVal fileCap) deserCancelFineMaxReq) :=
  sessLoadPoll_phaseCredit_tight hdc hdir hpeer hcap
    (fun _ hbs => recordDeserializeCancelEnv_fine_phaseCreditSpec hbs)

/-- Closed `2 MiB` `PhaseCreditSpec` for `CliSessLoadPollEnv rd RecordDeserializeCancelEnv`:
`(cum, live, peak, maxReq) = (17,495,245, 5,316,629, 7,421,976, 2,097,152)`. -/
theorem cliSessLoadPollEnv_dcan_2MiB_fine_phaseCredit_tight
    {rd : ReadRule} {files : FsFiles} {dir : DirGhost} {peer : AddrGhost}
    {maxDir maxEntries maxVal fileCap : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir) (hdir : maxDir ≤ 64)
    (hpeer : peer.name.bytes.length ≤ 40)
    (hcap : ∀ bs, rd files (pathOf dir.path (addressText peer.val)) = .ok bs → bs.length ≤ fileCap)
    (hfc : max maxVal fileCap ≤ 2097152) :
    PhaseCreditSpec fineCostModel
      (CliSessLoadPollEnv rd RecordDeserializeCancelEnv files dir peer)
      sessLoadPollCancel2MiBCum loadPollCancel2MiBLive
      loadPollCancel2MiBPeak loadPollCancel2MiBMaxReq := by
  have h0 := cliSessLoadPollEnv_dcan_fine_phaseCredit_tight hdc hdir hpeer hcap
  have hrc := fineReadFileCum_le_2MiB (max maxVal fileCap)
  have hrl := fineReadFileLive_le_2MiB hfc
  have hrp := fineReadFilePeak_le_2MiB hfc
  have hrm := fineReadFileMaxReq_le_2MiB hfc
  refine h0.mono ?_ ?_ ?_ ?_
  · unfold sessLoadPollCancel2MiBCum sessLoadPollTightDeltaCum
    rw [show fineReadFileCum 2097152 = 573818 by decide]; omega
  · unfold sessLoadPollTightDeltaLive loadPollCancel2MiBLive; omega
  · unfold sessLoadPollTightDeltaPeak loadPollCancel2MiBPeak
    exact Nat.max_le.mpr
      ⟨Nat.le_trans hrp (Nat.le_max_left _ _),
       Nat.le_trans (Nat.add_le_add_right hrl _) (Nat.le_max_right _ _)⟩
  · unfold sessLoadPollTightMaxReq loadPollCancel2MiBMaxReq deserCancelFineMaxReq
    exact Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨by decide, hrm⟩, Nat.le_refl _⟩

theorem cliSessLoadPollEnv_dcan_2MiB_fine_phaseCredit_p64
    {rd : ReadRule} {files : FsFiles} {dir : DirGhost} {peer : AddrGhost}
    {maxDir maxEntries maxVal fileCap : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir) (hdir : maxDir ≤ 64)
    (hpeer : peer.name.bytes.length ≤ 40)
    (hcap : ∀ bs, rd files (pathOf dir.path (addressText peer.val)) = .ok bs → bs.length ≤ fileCap)
    (hfc : max maxVal fileCap ≤ 2097152) :
    PhaseCreditSpec fineCostModel
      (CliSessLoadPollEnv rd RecordDeserializeCancelEnv files dir peer)
      sessLoadPollCancel2MiBCumP64 loadPollCancel2MiBLive
      loadPollCancel2MiBPeak loadPollCancel2MiBMaxReq :=
  (cliSessLoadPollEnv_dcan_2MiB_fine_phaseCredit_tight hdc hdir hpeer hcap hfc).mono
    (by decide) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)

theorem cliSessLoadPollEnv_dcan_2MiB_fine_phaseCredit_p192
    {rd : ReadRule} {files : FsFiles} {dir : DirGhost} {peer : AddrGhost}
    {maxDir maxEntries maxVal fileCap : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir) (hdir : maxDir ≤ 64)
    (hpeer : peer.name.bytes.length ≤ 40)
    (hcap : ∀ bs, rd files (pathOf dir.path (addressText peer.val)) = .ok bs → bs.length ≤ fileCap)
    (hfc : max maxVal fileCap ≤ 2097152) :
    PhaseCreditSpec fineCostModel
      (CliSessLoadPollEnv rd RecordDeserializeCancelEnv files dir peer)
      sessLoadPollCancel2MiBCumP192 loadPollCancel2MiBLive
      loadPollCancel2MiBPeak loadPollCancel2MiBMaxReq :=
  (cliSessLoadPollEnv_dcan_2MiB_fine_phaseCredit_tight hdc hdir hpeer hcap hfc).mono
    (by decide) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)

/-- Closed unconditional `PhaseGroupSpec` (`347,214,604`, `5,299` groups) for
`CliSessLoadPollEnv rd RecordDeserializeCancelEnv`. -/
theorem cliSessLoadPollEnv_dcan_fine_groupSpec
    {rd : ReadRule} (files : FsFiles) (dir : DirGhost) (peer : AddrGhost) :
    PhaseGroupSpec fineCostModel
      (CliSessLoadPollEnv rd RecordDeserializeCancelEnv files dir peer)
      cliSessLoadPollCancelGrpS :=
  cliSessLoadPollEnv_groupSpec fineCostModel files dir peer
    (fun bs _ => recordDeserializeCancelEnv_fine_groupSpec bs)

theorem cliSessLoadPollEnv_dcan_fine_groupSpec_p16_48
    {rd : ReadRule} (files : FsFiles) (dir : DirGhost) (peer : AddrGhost) :
    PhaseGroupSpec fineCostModel
      (CliSessLoadPollEnv rd RecordDeserializeCancelEnv files dir peer)
      cliSessLoadPollCancelGrpSP16_48 :=
  cliSessLoadPollEnv_groupSpec fineCostModel files dir peer
    (fun bs _ => recordDeserializeCancelEnv_fine_groupSpec_p16_48 bs)

theorem cliSessLoadPollEnv_dcan_fine_groupSpec_p64
    {rd : ReadRule} (files : FsFiles) (dir : DirGhost) (peer : AddrGhost) :
    PhaseGroupSpec fineCostModel
      (CliSessLoadPollEnv rd RecordDeserializeCancelEnv files dir peer)
      cliSessLoadPollCancelGrpSP64 :=
  cliSessLoadPollEnv_groupSpec fineCostModel files dir peer
    (fun bs _ => recordDeserializeCancelEnv_fine_groupSpec_p64 bs)

theorem cliSessLoadPollEnv_dcan_fine_groupSpec_p192
    {rd : ReadRule} (files : FsFiles) (dir : DirGhost) (peer : AddrGhost) :
    PhaseGroupSpec fineCostModel
      (CliSessLoadPollEnv rd RecordDeserializeCancelEnv files dir peer)
      cliSessLoadPollCancelGrpSP192 :=
  cliSessLoadPollEnv_groupSpec fineCostModel files dir peer
    (fun bs _ => recordDeserializeCancelEnv_fine_groupSpec_p192 bs)

/-- Initial-state `FitsEnv` closure on `cliBudgetLimits` (`1 GiB` RAM, `2 ^ 48` VA) for
`CliSessLoadPollEnv rd RecordDeserializeCancelEnv` at `max maxVal fileCap ≤ 2 MiB`. -/
theorem cliSessLoadPollEnv_dcan_fitsEnv_cliBudgetLimits
    {rd : ReadRule} {files : FsFiles} {dir : DirGhost} {peer : AddrGhost}
    {maxDir maxEntries maxVal fileCap : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir) (hdir : maxDir ≤ 64)
    (hpeer : peer.name.bytes.length ≤ 40)
    (hcap : ∀ bs, rd files (pathOf dir.path (addressText peer.val)) = .ok bs → bs.length ≤ fileCap)
    (hfc : max maxVal fileCap ≤ 2097152) :
    FitsEnv fineCostModel cliBudgetLimits fineCostModel.init
      (CliSessLoadPollEnv rd RecordDeserializeCancelEnv files dir peer) :=
  fitsEnv_fineCostModel_of_phaseCredit_groups
    (cliSessLoadPollEnv_dcan_2MiB_fine_phaseCredit_tight hdc hdir hpeer hcap hfc)
    (cliSessLoadPollEnv_dcan_fine_groupSpec files dir peer)
    (by decide)
    (Nat.le_refl cliSessLoadPollCancelGroups)
    rfl
    (by decide)
    (by decide)

/-- Tight `fineCostModel` `PhaseCreditSpec` for `cliSessionKitDefaultBudgetEnv` `loadPollEnv`
at `SessDeserializeCancelEnv` (`max maxVal fileCap ≤ 2 MiB`). -/
theorem defaultLoadPollEnv_dcan_fine_phaseCredit_tight
    {rd : ReadRule} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F0 : FsFiles} {dir : DirGhost} {rem : AddrVal}
    {maxDir maxEntries maxVal fileCap : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir) (hdir : maxDir ≤ 64)
    (hrem : rem.name.length ≤ 40)
    (hcap : ∀ bs, rd F0 (pathOf dir.path (addressText rem)) = .ok bs → bs.length ≤ fileCap)
    (hfc : max maxVal fileCap ≤ 2097152) :
    PhaseCreditSpec fineCostModel
      (cliSessionKitLoadPollEnv rd Scope (AddrTextValEnv DecimalEnv)
        (DirGetEnv PathEnv (ReadFileRuleEnv rd) rd) SessDeserializeCancelEnv F0 dir rem)
      (defaultLoadPollTightDeltaCum (max maxVal fileCap) deserCancelFineCum)
      (fineReadFileLive (max maxVal fileCap) + deserCancelFineLive)
      (max (fineReadFilePeak (max maxVal fileCap))
        (fineReadFileLive (max maxVal fileCap) + deserCancelFinePeak))
      (max (max 256 (fineReadFileMaxReq (max maxVal fileCap))) deserCancelFineMaxReq) :=
  defaultLoadPollEnv_fine_phaseCredit_tight hdc hdir hrem hcap
    (fun _ _ hlen => sessDeserializeCancelEnv_fine_phaseCreditSpec (Nat.le_trans hlen hfc))

/-- Tight `fineCostModel` `PhaseCreditSpec` for `cliSessionKitDefaultBudgetEnv` `loadPollEnv`
at `ofBytesEnv RecordDeserializeCancelEnv` (`max maxVal fileCap ≤ 2 MiB`). -/
theorem defaultLoadPollEnv_dcan_byBytes_fine_phaseCredit_tight
    {rd : ReadRule} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F0 : FsFiles} {dir : DirGhost} {rem : AddrVal}
    {maxDir maxEntries maxVal fileCap : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir) (hdir : maxDir ≤ 64)
    (hrem : rem.name.length ≤ 40)
    (hcap : ∀ bs, rd F0 (pathOf dir.path (addressText rem)) = .ok bs → bs.length ≤ fileCap)
    (hfc : max maxVal fileCap ≤ 2097152) :
    PhaseCreditSpec fineCostModel
      (cliSessionKitLoadPollEnv rd Scope (AddrTextValEnv DecimalEnv)
        (DirGetEnv PathEnv (ReadFileRuleEnv rd) rd)
        (ofBytesEnv RecordDeserializeCancelEnv) F0 dir rem)
      (defaultLoadPollTightDeltaCum (max maxVal fileCap) deserCancelFineCum)
      (fineReadFileLive (max maxVal fileCap) + deserCancelFineLive)
      (max (fineReadFilePeak (max maxVal fileCap))
        (fineReadFileLive (max maxVal fileCap) + deserCancelFinePeak))
      (max (max 256 (fineReadFileMaxReq (max maxVal fileCap))) deserCancelFineMaxReq) :=
  defaultLoadPollEnv_byBytes_fine_phaseCredit_tight hdc hdir hrem hcap
    (fun _ hbs => recordDeserializeCancelEnv_fine_phaseCreditSpec (Nat.le_trans hbs hfc))

/-- Closed `2 MiB` `PhaseCreditSpec` for `cliSessionKitDefaultBudgetEnv` `loadPollEnv` at
`SessDeserializeCancelEnv`: `(17,496,721, 5,316,629, 7,421,976, 2,097,152)`. -/
theorem defaultLoadPollEnv_dcan_2MiB_fine_phaseCredit_tight
    {rd : ReadRule} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F0 : FsFiles} {dir : DirGhost} {rem : AddrVal}
    {maxDir maxEntries maxVal fileCap : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir) (hdir : maxDir ≤ 64)
    (hrem : rem.name.length ≤ 40)
    (hcap : ∀ bs, rd F0 (pathOf dir.path (addressText rem)) = .ok bs → bs.length ≤ fileCap)
    (hfc : max maxVal fileCap ≤ 2097152) :
    PhaseCreditSpec fineCostModel
      (cliSessionKitLoadPollEnv rd Scope (AddrTextValEnv DecimalEnv)
        (DirGetEnv PathEnv (ReadFileRuleEnv rd) rd) SessDeserializeCancelEnv F0 dir rem)
      defaultLoadPollCancel2MiBCum loadPollCancel2MiBLive
      loadPollCancel2MiBPeak loadPollCancel2MiBMaxReq := by
  have h0 := defaultLoadPollEnv_dcan_fine_phaseCredit_tight (Scope := Scope) hdc hdir hrem hcap hfc
  have hrc := max_738_fineReadFileCum_le_2MiB (max maxVal fileCap)
  have hrl := fineReadFileLive_le_2MiB hfc
  have hrp := fineReadFilePeak_le_2MiB hfc
  have hrm := fineReadFileMaxReq_le_2MiB hfc
  refine h0.mono ?_ ?_ ?_ ?_
  · unfold defaultLoadPollCancel2MiBCum defaultLoadPollTightDeltaCum
    rw [show max 738 (fineReadFileCum 2097152) = 573818 by decide]; omega
  · unfold loadPollCancel2MiBLive; omega
  · unfold loadPollCancel2MiBPeak
    exact Nat.max_le.mpr
      ⟨Nat.le_trans hrp (Nat.le_max_left _ _),
       Nat.le_trans (Nat.add_le_add_right hrl _) (Nat.le_max_right _ _)⟩
  · unfold loadPollCancel2MiBMaxReq deserCancelFineMaxReq
    exact Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨by decide, hrm⟩, Nat.le_refl _⟩

/-- Closed `2 MiB` `PhaseCreditSpec` for `cliSessionKitDefaultBudgetEnv` `loadPollEnv` at
`ofBytesEnv RecordDeserializeCancelEnv`: `(17,496,721, 5,316,629, 7,421,976, 2,097,152)`. -/
theorem defaultLoadPollEnv_dcan_byBytes_2MiB_fine_phaseCredit_tight
    {rd : ReadRule} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F0 : FsFiles} {dir : DirGhost} {rem : AddrVal}
    {maxDir maxEntries maxVal fileCap : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir) (hdir : maxDir ≤ 64)
    (hrem : rem.name.length ≤ 40)
    (hcap : ∀ bs, rd F0 (pathOf dir.path (addressText rem)) = .ok bs → bs.length ≤ fileCap)
    (hfc : max maxVal fileCap ≤ 2097152) :
    PhaseCreditSpec fineCostModel
      (cliSessionKitLoadPollEnv rd Scope (AddrTextValEnv DecimalEnv)
        (DirGetEnv PathEnv (ReadFileRuleEnv rd) rd)
        (ofBytesEnv RecordDeserializeCancelEnv) F0 dir rem)
      defaultLoadPollCancel2MiBCum loadPollCancel2MiBLive
      loadPollCancel2MiBPeak loadPollCancel2MiBMaxReq := by
  have h0 := defaultLoadPollEnv_dcan_byBytes_fine_phaseCredit_tight (Scope := Scope)
    hdc hdir hrem hcap hfc
  have hrc := max_738_fineReadFileCum_le_2MiB (max maxVal fileCap)
  have hrl := fineReadFileLive_le_2MiB hfc
  have hrp := fineReadFilePeak_le_2MiB hfc
  have hrm := fineReadFileMaxReq_le_2MiB hfc
  refine h0.mono ?_ ?_ ?_ ?_
  · unfold defaultLoadPollCancel2MiBCum defaultLoadPollTightDeltaCum
    rw [show max 738 (fineReadFileCum 2097152) = 573818 by decide]; omega
  · unfold loadPollCancel2MiBLive; omega
  · unfold loadPollCancel2MiBPeak
    exact Nat.max_le.mpr
      ⟨Nat.le_trans hrp (Nat.le_max_left _ _),
       Nat.le_trans (Nat.add_le_add_right hrl _) (Nat.le_max_right _ _)⟩
  · unfold loadPollCancel2MiBMaxReq deserCancelFineMaxReq
    exact Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨by decide, hrm⟩, Nat.le_refl _⟩

/-- Closed `PhaseGroupSpec` (`347,411,212`, `5,302` groups, zero file-cap premise) for
`cliSessionKitDefaultBudgetEnv` `loadPollEnv` at `SessDeserializeCancelEnv`. -/
theorem defaultLoadPollEnv_dcan_fine_groupSpec
    {rd : ReadRule} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F0 : FsFiles} {dir : DirGhost} {rem : AddrVal} (hrem : rem.name.length ≤ 40) :
    PhaseGroupSpec fineCostModel
      (cliSessionKitLoadPollEnv rd Scope (AddrTextValEnv DecimalEnv)
        (DirGetEnv PathEnv (ReadFileRuleEnv rd) rd) SessDeserializeCancelEnv F0 dir rem)
      defaultLoadPollCancelGrpS := by
  have h1 := addrTextValEnv_decimal_fine_groupSpec rem hrem
  have h2 := dirGetEnv_path_readFile_groupSpec fineCostModel rd F0 dir (addressText rem)
  have h3 : PhaseGroupSpec fineCostModel
      (OptLoadDeserEnv Scope SessDeserializeCancelEnv (dir.get rd F0 (addressText rem)))
      deserCancelFineGrpS := by
    unfold OptLoadDeserEnv
    cases dir.get rd F0 (addressText rem) with
    | error _ => exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
    | ok bs =>
      cases bs with
      | nil => exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
      | cons _ _ =>
        exact { groups_le := fun st0 {_} ⟨r, _, _, hd⟩ =>
          (sessDeserializeCancelEnv_fine_groupSpec r).groups_le st0 hd }
  have h3f := (h3.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono (Nat.le_of_eq (Nat.add_zero _))
  unfold cliSessionKitLoadPollEnv defaultLoadPollCancelGrpS
  exact (h1.seq (h2.seq h3f)).mono (by omega)

/-- Closed `PhaseGroupSpec` (`347,411,212`, `5,302` groups, zero file-cap premise) for
`cliSessionKitDefaultBudgetEnv` `loadPollEnv` at `ofBytesEnv RecordDeserializeCancelEnv`. -/
theorem defaultLoadPollEnv_dcan_byBytes_fine_groupSpec
    {rd : ReadRule} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F0 : FsFiles} {dir : DirGhost} {rem : AddrVal} (hrem : rem.name.length ≤ 40) :
    PhaseGroupSpec fineCostModel
      (cliSessionKitLoadPollEnv rd Scope (AddrTextValEnv DecimalEnv)
        (DirGetEnv PathEnv (ReadFileRuleEnv rd) rd)
        (ofBytesEnv RecordDeserializeCancelEnv) F0 dir rem)
      defaultLoadPollCancelGrpS := by
  have h1 := addrTextValEnv_decimal_fine_groupSpec rem hrem
  have h2 := dirGetEnv_path_readFile_groupSpec fineCostModel rd F0 dir (addressText rem)
  have h3 : PhaseGroupSpec fineCostModel
      (OptLoadDeserEnv Scope (ofBytesEnv RecordDeserializeCancelEnv)
        (dir.get rd F0 (addressText rem)))
      deserCancelFineGrpS := by
    unfold OptLoadDeserEnv
    cases dir.get rd F0 (addressText rem) with
    | error _ => exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
    | ok bs =>
      cases bs with
      | nil => exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
      | cons _ _ =>
        exact { groups_le := fun st0 {_} ⟨r, _, _, hd⟩ =>
          (recordDeserializeCancelEnv_fine_groupSpec (encodeRecord r)).groups_le st0 hd }
  have h3f := (h3.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono (Nat.le_of_eq (Nat.add_zero _))
  unfold cliSessionKitLoadPollEnv defaultLoadPollCancelGrpS
  exact (h1.seq (h2.seq h3f)).mono (by omega)

theorem defaultLoadPollEnv_dcan_byBytes_fine_groupSpec_p16_48
    {rd : ReadRule} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F0 : FsFiles} {dir : DirGhost} {rem : AddrVal} (hrem : rem.name.length ≤ 40) :
    PhaseGroupSpec fineCostModel
      (cliSessionKitLoadPollEnv rd Scope (AddrTextValEnv DecimalEnv)
        (DirGetEnv PathEnv (ReadFileRuleEnv rd) rd)
        (ofBytesEnv RecordDeserializeCancelEnv) F0 dir rem)
      defaultLoadPollCancelGrpSP16_48 :=
  (defaultLoadPollEnv_dcan_byBytes_fine_groupSpec hrem).mono (by decide)

theorem defaultLoadPollEnv_dcan_byBytes_fine_groupSpec_p64
    {rd : ReadRule} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F0 : FsFiles} {dir : DirGhost} {rem : AddrVal} (hrem : rem.name.length ≤ 40) :
    PhaseGroupSpec fineCostModel
      (cliSessionKitLoadPollEnv rd Scope (AddrTextValEnv DecimalEnv)
        (DirGetEnv PathEnv (ReadFileRuleEnv rd) rd)
        (ofBytesEnv RecordDeserializeCancelEnv) F0 dir rem)
      defaultLoadPollCancelGrpSP64 :=
  (defaultLoadPollEnv_dcan_byBytes_fine_groupSpec hrem).mono (by decide)

theorem defaultLoadPollEnv_dcan_byBytes_fine_groupSpec_p192
    {rd : ReadRule} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F0 : FsFiles} {dir : DirGhost} {rem : AddrVal} (hrem : rem.name.length ≤ 40) :
    PhaseGroupSpec fineCostModel
      (cliSessionKitLoadPollEnv rd Scope (AddrTextValEnv DecimalEnv)
        (DirGetEnv PathEnv (ReadFileRuleEnv rd) rd)
        (ofBytesEnv RecordDeserializeCancelEnv) F0 dir rem)
      defaultLoadPollCancelGrpSP192 :=
  (defaultLoadPollEnv_dcan_byBytes_fine_groupSpec hrem).mono (by decide)

/-- Initial-state `FitsEnv` closure on `cliBudgetLimits` (`1 GiB` RAM, `2 ^ 48` VA) for
`cliSessionKitDefaultBudgetEnv` `loadPollEnv` at `SessDeserializeCancelEnv`. -/
theorem defaultLoadPollEnv_dcan_fitsEnv_cliBudgetLimits
    {rd : ReadRule} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F0 : FsFiles} {dir : DirGhost} {rem : AddrVal}
    {maxDir maxEntries maxVal fileCap : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir) (hdir : maxDir ≤ 64)
    (hrem : rem.name.length ≤ 40)
    (hcap : ∀ bs, rd F0 (pathOf dir.path (addressText rem)) = .ok bs → bs.length ≤ fileCap)
    (hfc : max maxVal fileCap ≤ 2097152) :
    FitsEnv fineCostModel cliBudgetLimits fineCostModel.init
      (cliSessionKitLoadPollEnv rd Scope (AddrTextValEnv DecimalEnv)
        (DirGetEnv PathEnv (ReadFileRuleEnv rd) rd) SessDeserializeCancelEnv F0 dir rem) :=
  fitsEnv_fineCostModel_of_phaseCredit_groups
    (defaultLoadPollEnv_dcan_2MiB_fine_phaseCredit_tight hdc hdir hrem hcap hfc)
    (defaultLoadPollEnv_dcan_fine_groupSpec hrem)
    (by decide)
    (Nat.le_refl defaultLoadPollCancelGroups)
    rfl
    (by decide)
    (by decide)

/-- Initial-state `FitsEnv` closure on `cliBudgetLimits` (`1 GiB` RAM, `2 ^ 48` VA) for
`cliSessionKitDefaultBudgetEnv` `loadPollEnv` at `ofBytesEnv RecordDeserializeCancelEnv`. -/
theorem defaultLoadPollEnv_dcan_byBytes_fitsEnv_cliBudgetLimits
    {rd : ReadRule} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F0 : FsFiles} {dir : DirGhost} {rem : AddrVal}
    {maxDir maxEntries maxVal fileCap : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir) (hdir : maxDir ≤ 64)
    (hrem : rem.name.length ≤ 40)
    (hcap : ∀ bs, rd F0 (pathOf dir.path (addressText rem)) = .ok bs → bs.length ≤ fileCap)
    (hfc : max maxVal fileCap ≤ 2097152) :
    FitsEnv fineCostModel cliBudgetLimits fineCostModel.init
      (cliSessionKitLoadPollEnv rd Scope (AddrTextValEnv DecimalEnv)
        (DirGetEnv PathEnv (ReadFileRuleEnv rd) rd)
        (ofBytesEnv RecordDeserializeCancelEnv) F0 dir rem) :=
  fitsEnv_fineCostModel_of_phaseCredit_groups
    (defaultLoadPollEnv_dcan_byBytes_2MiB_fine_phaseCredit_tight hdc hdir hrem hcap hfc)
    (defaultLoadPollEnv_dcan_byBytes_fine_groupSpec hrem)
    (by decide)
    (Nat.le_refl defaultLoadPollCancelGroups)
    rfl
    (by decide)
    (by decide)

section DcanBoxedSteps

variable [LibsignalPlacement] {A : RustAlloc} {rd : ReadRule} {F0 : FsFiles}
  {pathOk : List (BitVec 8) → Prop} {Scope : SessionRecord (List (BitVec 8)) → Prop}
  {peer : AddrGhost} {s1 s2 s3 s4 : Nat} {vtSym idVtSym : String}

local notation "kit_dcan" =>
  cliSessionKitSpecPlaced A rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym idVtSym
local notation "kitEnv_dcan" =>
  cliSessionKitDefaultBudgetEnv A rd F0 pathOk Scope peer s1 s2 s3 s4
    (ofBytesEnv RecordDeserializeCancelEnv) vtSym idVtSym (ReadFileRuleEnv rd)

theorem w3_defaultLoadStep_dcan_byBytes_fine_phaseCredit {dir : DirGhost} {rem : AddrVal}
    {maxDir maxEntries maxVal fileCap : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir) (hdir : maxDir ≤ 64)
    (hrem : rem.name.length ≤ 40)
    (hcap : ∀ bs, rd F0 (pathOf dir.path (addressText rem)) = .ok bs → bs.length ≤ fileCap)
    (hfc : max maxVal fileCap ≤ 2097152) :
    PhaseCreditSpec fineCostModel (LoadStepEnv kit_dcan kitEnv_dcan dir rem)
      (w3BoxedStepCum 24 (defaultLoadPollTightDeltaCum (max maxVal fileCap) deserCancelFineCum))
      (w3BoxedStepLive 24 (fineReadFileLive (max maxVal fileCap) + deserCancelFineLive))
      (w3BoxedStepPeak 24
        (max (fineReadFilePeak (max maxVal fileCap))
          (fineReadFileLive (max maxVal fileCap) + deserCancelFinePeak)))
      (w3BoxedStepMaxReq 24
        (max (max 256 (fineReadFileMaxReq (max maxVal fileCap))) deserCancelFineMaxReq)) :=
  w3_defaultLoadStep_fine_phaseCredit hdc hdir hrem hcap
    (fun r _ hlen =>
      recordDeserializeCancelEnv_fine_phaseCreditSpec (bs := encodeRecord r) (Nat.le_trans hlen hfc))

theorem w4_defaultLoadStep_dcan_byBytes_fine_phaseCredit {dir : DirGhost} {rem : AddrVal}
    {maxDir maxEntries maxVal fileCap : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir) (hdir : maxDir ≤ 64)
    (hrem : rem.name.length ≤ 40)
    (hcap : ∀ bs, rd F0 (pathOf dir.path (addressText rem)) = .ok bs → bs.length ≤ fileCap)
    (hfc : max maxVal fileCap ≤ 2097152) :
    PhaseCreditSpec fineCostModel (LoadStepEnv kit_dcan kitEnv_dcan dir rem)
      (defaultW4LoadCum (max maxVal fileCap) deserCancelFineCum)
      (defaultW4LoadLive (max maxVal fileCap) deserCancelFineLive)
      (defaultW4LoadPeak (max maxVal fileCap) deserCancelFinePeak)
      (defaultW4LoadMaxReq (max maxVal fileCap) deserCancelFineMaxReq) :=
  w4_defaultLoadStep_fine_phaseCredit hdc hdir hrem hcap
    (fun r _ hlen =>
      recordDeserializeCancelEnv_fine_phaseCreditSpec (bs := encodeRecord r) (Nat.le_trans hlen hfc))

theorem w4_defaultLoadStep_small_dcan_byBytes_fine_phaseCredit {dir : DirGhost} {rem : AddrVal}
    {maxDir maxEntries maxVal fileCap : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir) (hdir : maxDir ≤ 64)
    (hrem : rem.name.length ≤ 40)
    (hcap : ∀ bs, rd F0 (pathOf dir.path (addressText rem)) = .ok bs → bs.length ≤ fileCap)
    (hfc : max maxVal fileCap ≤ 2097152) :
    PhaseCreditSpec fineCostModel (LoadStepEnv kit_dcan kitEnv_dcan dir rem)
      (defaultW4LoadCum (max maxVal fileCap) deserCancelFineCum)
      (fineReadFileLive (max maxVal fileCap) + deserCancelFineLive)
      (max (fineReadFilePeak (max maxVal fileCap))
        (fineReadFileLive (max maxVal fileCap) + deserCancelFinePeak))
      (defaultW4LoadMaxReq (max maxVal fileCap) deserCancelFineMaxReq) :=
  w4_defaultLoadStep_small_fine_phaseCredit hdc hdir hrem hcap
    (fun r _ hlen =>
      recordDeserializeCancelEnv_fine_phaseCreditSpec (bs := encodeRecord r) (Nat.le_trans hlen hfc))

theorem w4_defaultStageP1Ok_dcan_byBytes_fine_phaseCredit {b' : BitVec 64}
    (ikit : IdentityStoreSpec A b') (ikitEnv : IdentityStoreBudgetEnv ikit) (ist : ikit.IdState)
    {dir : DirGhost} {rem : AddrVal} {remoteIdKey : IdentityKey}
    {maxDir maxEntries maxVal fileCap c₂ l₂ p₂ r₂ : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir) (hdir : maxDir ≤ 64)
    (hrem : rem.name.length ≤ 40)
    (hcap : ∀ bs, rd F0 (pathOf dir.path (addressText rem)) = .ok bs → bs.length ≤ fileCap)
    (hfc : max maxVal fileCap ≤ 2097152)
    (hTrust : PhaseCreditSpec fineCostModel
      (ikitEnv.trustPollEnv ist rem remoteIdKey .receiving) c₂ l₂ p₂ r₂) :
    PhaseCreditSpec fineCostModel
      (SeqEnv (LoadStepEnv kit_dcan kitEnv_dcan dir rem)
        (TrustStepEnv ikit ikitEnv ist rem remoteIdKey .receiving))
      (defaultW4LoadCum (max maxVal fileCap) deserCancelFineCum +
        w4BoxedStepCum ikit.trustBoxSize c₂)
      (defaultW4LoadLive (max maxVal fileCap) deserCancelFineLive +
        w4BoxedStepLive ikit.trustBoxSize l₂)
      (max (defaultW4LoadPeak (max maxVal fileCap) deserCancelFinePeak)
        (defaultW4LoadLive (max maxVal fileCap) deserCancelFineLive +
          w4BoxedStepPeak ikit.trustBoxSize p₂))
      (max (defaultW4LoadMaxReq (max maxVal fileCap) deserCancelFineMaxReq)
        (w4BoxedStepMaxReq ikit.trustBoxSize r₂)) :=
  w4_defaultStageP1Ok_fine_phaseCredit ikit ikitEnv ist hdc hdir hrem hcap
    (fun r _ hlen =>
      recordDeserializeCancelEnv_fine_phaseCreditSpec (bs := encodeRecord r) (Nat.le_trans hlen hfc))
    hTrust

theorem w4_defaultStageP1Untrusted_small_dcan_byBytes_fine_phaseCredit
    {b' : BitVec 64} {targetPeer : AddrGhost}
    (ikit : IdentityStoreSpec A b') (ikitEnv : IdentityStoreBudgetEnv ikit) (ist : ikit.IdState)
    {dir : DirGhost} {remoteIdKey : IdentityKey}
    {maxDir maxEntries maxVal fileCap c₂ l₂ p₂ r₂ : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir) (hdir : maxDir ≤ 64)
    (hpeer : targetPeer.name.bytes.length ≤ 40)
    (hcap : ∀ bs, rd F0 (pathOf dir.path (addressText targetPeer.val)) = .ok bs → bs.length ≤ fileCap)
    (hfc : max maxVal fileCap ≤ 2097152)
    (hTrust : PhaseCreditSpec fineCostModel
      (ikitEnv.trustPollEnv ist targetPeer.val remoteIdKey .receiving) c₂ l₂ p₂ r₂) :
    PhaseCreditSpec fineCostModel
      (SeqEnv (LoadStepEnv kit_dcan kitEnv_dcan dir targetPeer.val)
        (SeqEnv (TrustStepEnv ikit ikitEnv ist targetPeer.val remoteIdKey .receiving)
          (SeqEnv (StringCloneEnv targetPeer.name) FreeOnlyEvs)))
      (defaultW4LoadCum (max maxVal fileCap) deserCancelFineCum +
        w4BoxedStepCum ikit.trustBoxSize c₂ + (2 * 40 + 9539))
      (defaultW4LoadLive (max maxVal fileCap) deserCancelFineLive +
        w4BoxedStepLive ikit.trustBoxSize l₂)
      (max (defaultW4LoadPeak (max maxVal fileCap) deserCancelFinePeak)
        (defaultW4LoadLive (max maxVal fileCap) deserCancelFineLive +
          max (w4BoxedStepPeak ikit.trustBoxSize p₂) (w4BoxedStepLive ikit.trustBoxSize l₂)))
      (max (defaultW4LoadMaxReq (max maxVal fileCap) deserCancelFineMaxReq)
        (max (w4BoxedStepMaxReq ikit.trustBoxSize r₂) 40)) :=
  w4_defaultStageP1Untrusted_small_fine_phaseCredit ikit ikitEnv ist hdc hdir hpeer hcap
    (fun r _ hlen =>
      recordDeserializeCancelEnv_fine_phaseCreditSpec (bs := encodeRecord r) (Nat.le_trans hlen hfc))
    hTrust

theorem w4_defaultStageP1Untrusted_dcan_byBytes_fine_phaseCredit
    {b' : BitVec 64} {targetPeer : AddrGhost}
    (ikit : IdentityStoreSpec A b') (ikitEnv : IdentityStoreBudgetEnv ikit) (ist : ikit.IdState)
    {dir : DirGhost} {remoteIdKey : IdentityKey}
    {maxDir maxEntries maxVal fileCap c₂ l₂ p₂ r₂ : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir) (hdir : maxDir ≤ 64)
    (hpeer : targetPeer.name.bytes.length ≤ 40)
    (hcap : ∀ bs, rd F0 (pathOf dir.path (addressText targetPeer.val)) = .ok bs → bs.length ≤ fileCap)
    (hfc : max maxVal fileCap ≤ 2097152)
    (hTrust : PhaseCreditSpec fineCostModel
      (ikitEnv.trustPollEnv ist targetPeer.val remoteIdKey .receiving) c₂ l₂ p₂ r₂) :
    PhaseCreditSpec fineCostModel
      (SeqEnv (LoadStepEnv kit_dcan kitEnv_dcan dir targetPeer.val)
        (SeqEnv (TrustStepEnv ikit ikitEnv ist targetPeer.val remoteIdKey .receiving)
          (SeqEnv (StringCloneEnv targetPeer.name) FreeOnlyEvs)))
      (defaultW4LoadCum (max maxVal fileCap) deserCancelFineCum +
        w4BoxedStepCum ikit.trustBoxSize c₂ + (2 * 40 + 9539))
      (defaultW4LoadLive (max maxVal fileCap) deserCancelFineLive +
        w4BoxedStepLive ikit.trustBoxSize l₂ + (40 + 8195))
      (max (defaultW4LoadPeak (max maxVal fileCap) deserCancelFinePeak)
        (defaultW4LoadLive (max maxVal fileCap) deserCancelFineLive +
          max (w4BoxedStepPeak ikit.trustBoxSize p₂)
            (w4BoxedStepLive ikit.trustBoxSize l₂ + (40 + 8195))))
      (max (defaultW4LoadMaxReq (max maxVal fileCap) deserCancelFineMaxReq)
        (max (w4BoxedStepMaxReq ikit.trustBoxSize r₂) 40)) :=
  w4_defaultStageP1Untrusted_fine_phaseCredit ikit ikitEnv ist hdc hdir hpeer hcap
    (fun r _ hlen =>
      recordDeserializeCancelEnv_fine_phaseCreditSpec (bs := encodeRecord r) (Nat.le_trans hlen hfc))
    hTrust

end DcanBoxedSteps

/-!
## Section 6: `SessDeserSetBEnv` / `SessDeserSetAEnv` Wiring & `CliPqxdhInputs` Domain Chain
-/

/-- `SessDeserializeCancelEnv r evs` refines `SessDeserSetBEnv (encodeRecord r) evs`. -/
theorem sessDeserializeCancelEnv_imp_setB {r : SessionRecord (List (BitVec 8))}
    {evs : List AllocEvent} (h : SessDeserializeCancelEnv r evs) :
    SessDeserSetBEnv (encodeRecord r) evs := by
  rcases h with ⟨hr, rfl⟩
  exact sessDeserEvents_deserBoundedTotalEvs_of_scope hr

/-- `SessDeserializeCancelEnv r evs` refines `SessDeserSetAEnv (encodeRecord r) evs`. -/
theorem sessDeserializeCancelEnv_imp_setA {r : SessionRecord (List (BitVec 8))}
    {evs : List AllocEvent} (h : SessDeserializeCancelEnv r evs) :
    SessDeserSetAEnv (encodeRecord r) evs := by
  rcases h with ⟨hr, rfl⟩
  exact sessDeserEvents_deserBoundedTotalEvs_setA_of_scope hr

/-- Placed Block `46` (`cliGhostExterns g (cliExternsPlaced mmpl W)`) contract instantiated at
`ofBytesEnv SessDeserSetBEnv`. -/
theorem sessDeserialize_cli_setB_placed_ok [LibsignalPlacement]
    (mmpl : Arm64.Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {M : AllocCostModel} [HasFineReallocCredit M]
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim g) (hsub : ∀ r, Scope r → scopeKit r) :
    subroutine_ok (lsProg_46 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced Scope A lim (ofBytesEnv SessDeserSetBEnv)) :=
  sessDeserialize_cli_of_bytesEnv_placed_ok mmpl g W hG hsub
    (fun r hr => sessDeserEvents_deserBoundedTotalEvs_of_scope (hsub r hr))

/-- Placed Block `46` (`cliGhostExterns g (cliExternsPlaced mmpl W)`) contract instantiated at
`ofBytesEnv SessDeserSetAEnv`. -/
theorem sessDeserialize_cli_setA_placed_ok [LibsignalPlacement]
    (mmpl : Arm64.Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {M : AllocCostModel} [HasFineReallocCredit M]
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim g) (hsub : ∀ r, Scope r → scopeKit r) :
    subroutine_ok (lsProg_46 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced Scope A lim (ofBytesEnv SessDeserSetAEnv)) :=
  sessDeserialize_cli_of_bytesEnv_placed_ok mmpl g W hG hsub
    (fun r hr => sessDeserEvents_deserBoundedTotalEvs_setA_of_scope (hsub r hr))

section G1KitAssembly

variable [LibsignalPlacement] {M : AllocCostModel} [HasFineReallocCredit M]
  {A : RustCliAllocBudget M} {lim : BudgetLimits} {F0 : FsFiles}
  {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost}
  {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
  {readStk s1 s2 s3 s4 : Nat} {vtSym idVtSym : String}

/-- Unconditional CLI `SessionOnlyKitPlacedOkSE` bundle at `ofBytesEnv SessDeserSetBEnv`. -/
theorem cliSessKitOkSE_cli_setB_placed (mmpl : Arm64.Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks)
    {readProg : Program} {jRead : Nat}
    [IsLsBlockProg readProg jRead (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim g)
    (hAzFsT : HookFsTraced IsFsC g.allocZeroed)
    (hStrFsT : ∀ f, g.stringClone = some f → HookFsTraced IsFsC f)
    (hRead : subroutine_ok readProg (lsρ lsReadFileSym)
      (withLsCodeRoLoaded lsmpl (readFileSpecPlaced cliIo.rd cliWrOk A lim readStk ReadEnv)))
    (hsub : ∀ r, Scope r → scopeKit r)
    (hs1 : loadShimNeedPlaced ≤ s1) (hs2 : loadPollNeedPlaced readStk ≤ s2)
    (hs3 : storeShimNeedPlaced ≤ s3) (hs4 : storePollNeedXPlaced ≤ s4)
    (hjRead : jRead < 619 := by decide)
    (hjRead_unmut : (jRead ∈ libsignalMutatedBlocks) = false := by decide) :
    SessionOnlyKitPlacedOkSE A lim
      (cliSessionKitSpecPlaced A.repAlloc cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4 vtSym idVtSym)
      (cliSessionKitDefaultBudgetEnv A.repAlloc cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4
        (ofBytesEnv SessDeserSetBEnv) vtSym idVtSym ReadEnv)
      Scope encodeRecord (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  cliSessKitOkSE_cli_of_sessDeserEvents_placed mmpl g W hDropNz hG hAzFsT hStrFsT hRead hsub
    (fun r hr => sessDeserEvents_deserBoundedTotalEvs_of_scope (hsub r hr))
    hs1 hs2 hs3 hs4 hjRead hjRead_unmut

theorem cliSessKitOkSE_cli_setB_readHook (mmpl : Arm64.Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim g)
    (hAzFsT : HookFsTraced IsFsC g.allocZeroed)
    (hStrFsT : ∀ f, g.stringClone = some f → HookFsTraced IsFsC f)
    (hReadHook : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk A lim readStk ReadEnv))
    (hsub : ∀ r, Scope r → scopeKit r)
    (hs1 : loadShimNeedPlaced ≤ s1) (hs2 : loadPollNeedPlaced readStk ≤ s2)
    (hs3 : storeShimNeedPlaced ≤ s3) (hs4 : storePollNeedXPlaced ≤ s4) :
    SessionOnlyKitPlacedOkSE A lim
      (cliSessionKitSpecPlaced A.repAlloc cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4 vtSym idVtSym)
      (cliSessionKitDefaultBudgetEnv A.repAlloc cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4
        (ofBytesEnv SessDeserSetBEnv) vtSym idVtSym ReadEnv)
      Scope encodeRecord (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  cliSessKitOkSE_cli_of_sessDeserEvents_readHook mmpl g W hDropNz hG hAzFsT hStrFsT hReadHook hsub
    (fun r hr => sessDeserEvents_deserBoundedTotalEvs_of_scope (hsub r hr)) hs1 hs2 hs3 hs4

/-- Unconditional CLI `SessionOnlyKitPlacedOkSE` bundle at `ofBytesEnv SessDeserSetAEnv`. -/
theorem cliSessKitOkSE_cli_setA_placed (mmpl : Arm64.Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks)
    {readProg : Program} {jRead : Nat}
    [IsLsBlockProg readProg jRead (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim g)
    (hAzFsT : HookFsTraced IsFsC g.allocZeroed)
    (hStrFsT : ∀ f, g.stringClone = some f → HookFsTraced IsFsC f)
    (hRead : subroutine_ok readProg (lsρ lsReadFileSym)
      (withLsCodeRoLoaded lsmpl (readFileSpecPlaced cliIo.rd cliWrOk A lim readStk ReadEnv)))
    (hsub : ∀ r, Scope r → scopeKit r)
    (hs1 : loadShimNeedPlaced ≤ s1) (hs2 : loadPollNeedPlaced readStk ≤ s2)
    (hs3 : storeShimNeedPlaced ≤ s3) (hs4 : storePollNeedXPlaced ≤ s4)
    (hjRead : jRead < 619 := by decide)
    (hjRead_unmut : (jRead ∈ libsignalMutatedBlocks) = false := by decide) :
    SessionOnlyKitPlacedOkSE A lim
      (cliSessionKitSpecPlaced A.repAlloc cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4 vtSym idVtSym)
      (cliSessionKitDefaultBudgetEnv A.repAlloc cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4
        (ofBytesEnv SessDeserSetAEnv) vtSym idVtSym ReadEnv)
      Scope encodeRecord (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  cliSessKitOkSE_cli_of_sessDeserEvents_placed mmpl g W hDropNz hG hAzFsT hStrFsT hRead hsub
    (fun r hr => sessDeserEvents_deserBoundedTotalEvs_setA_of_scope (hsub r hr))
    hs1 hs2 hs3 hs4 hjRead hjRead_unmut

theorem cliSessKitOkSE_cli_setA_readHook (mmpl : Arm64.Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim g)
    (hAzFsT : HookFsTraced IsFsC g.allocZeroed)
    (hStrFsT : ∀ f, g.stringClone = some f → HookFsTraced IsFsC f)
    (hReadHook : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk A lim readStk ReadEnv))
    (hsub : ∀ r, Scope r → scopeKit r)
    (hs1 : loadShimNeedPlaced ≤ s1) (hs2 : loadPollNeedPlaced readStk ≤ s2)
    (hs3 : storeShimNeedPlaced ≤ s3) (hs4 : storePollNeedXPlaced ≤ s4) :
    SessionOnlyKitPlacedOkSE A lim
      (cliSessionKitSpecPlaced A.repAlloc cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4 vtSym idVtSym)
      (cliSessionKitDefaultBudgetEnv A.repAlloc cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4
        (ofBytesEnv SessDeserSetAEnv) vtSym idVtSym ReadEnv)
      Scope encodeRecord (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  cliSessKitOkSE_cli_of_sessDeserEvents_readHook mmpl g W hDropNz hG hAzFsT hStrFsT hReadHook hsub
    (fun r hr => sessDeserEvents_deserBoundedTotalEvs_setA_of_scope (hsub r hr)) hs1 hs2 hs3 hs4

end G1KitAssembly

/-- `cliSessionKitLoadPollEnv` at `SessDeserializeCancelEnv` refines `CliSessLoadPollEnv rd SessDeserSetBEnv`. -/
theorem cliSessionKitLoadPollEnv_dcan_imp_setB
    {rd : ReadRule} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {AddrValEnv : AddrVal → List AllocEvent → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {F0 : FsFiles} {d : DirGhost} {peer : AddrGhost} {rem : AddrVal}
    (hrem : rem = peer.val)
    (hAddr : ∀ evs, AddrValEnv peer.val evs → CliAddrTextEnv peer evs)
    (hGet : ∀ evs, GetEnv F0 d (addressText peer.val) evs →
      CliDirGetEnv (ReadFileRuleEnv rd) F0 d (addressText peer.val) evs)
    (hCap : ∀ bs, d.get rd F0 (addressText peer.val) = .ok bs → bs.length ≤ 2097152) :
    ∀ evs, cliSessionKitLoadPollEnv rd Scope AddrValEnv GetEnv SessDeserializeCancelEnv F0 d rem evs →
      CliSessLoadPollEnv rd SessDeserSetBEnv F0 d peer evs :=
  cliSessionKitLoadPollEnv_imp_cliSessLoadPollEnv hrem hAddr hGet hCap
    (fun _ _ _ hd => sessDeserializeCancelEnv_imp_setB hd)

/-- `cliSessionKitLoadPollEnv` at `SessDeserializeCancelEnv` refines `CliSessLoadPollEnv rd SessDeserSetAEnv`. -/
theorem cliSessionKitLoadPollEnv_dcan_imp_setA
    {rd : ReadRule} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {AddrValEnv : AddrVal → List AllocEvent → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {F0 : FsFiles} {d : DirGhost} {peer : AddrGhost} {rem : AddrVal}
    (hrem : rem = peer.val)
    (hAddr : ∀ evs, AddrValEnv peer.val evs → CliAddrTextEnv peer evs)
    (hGet : ∀ evs, GetEnv F0 d (addressText peer.val) evs →
      CliDirGetEnv (ReadFileRuleEnv rd) F0 d (addressText peer.val) evs)
    (hCap : ∀ bs, d.get rd F0 (addressText peer.val) = .ok bs → bs.length ≤ 2097152) :
    ∀ evs, cliSessionKitLoadPollEnv rd Scope AddrValEnv GetEnv SessDeserializeCancelEnv F0 d rem evs →
      CliSessLoadPollEnv rd SessDeserSetAEnv F0 d peer evs :=
  cliSessionKitLoadPollEnv_imp_cliSessLoadPollEnv hrem hAddr hGet hCap
    (fun _ _ _ hd => sessDeserializeCancelEnv_imp_setA hd)

theorem cliSessionKitLoadPollEnv_setB_imp_cliSessLoadPollEnv
    {rd : ReadRule} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {AddrValEnv : AddrVal → List AllocEvent → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {F0 : FsFiles} {d : DirGhost} {peer : AddrGhost} {rem : AddrVal}
    (hrem : rem = peer.val)
    (hAddr : ∀ evs, AddrValEnv peer.val evs → CliAddrTextEnv peer evs)
    (hGet : ∀ evs, GetEnv F0 d (addressText peer.val) evs →
      CliDirGetEnv (ReadFileRuleEnv rd) F0 d (addressText peer.val) evs)
    (hCap : ∀ bs, d.get rd F0 (addressText peer.val) = .ok bs → bs.length ≤ 2097152) :
    ∀ evs, cliSessionKitLoadPollEnv rd Scope AddrValEnv GetEnv
        (ofBytesEnv SessDeserSetBEnv) F0 d rem evs →
      CliSessLoadPollEnv rd SessDeserSetBEnv F0 d peer evs :=
  cliSessionKitLoadPollEnv_imp_cliSessLoadPollEnv hrem hAddr hGet hCap (fun _ _ _ hd => hd)

theorem cliSessionKitLoadPollEnv_setA_imp_cliSessLoadPollEnv
    {rd : ReadRule} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {AddrValEnv : AddrVal → List AllocEvent → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {F0 : FsFiles} {d : DirGhost} {peer : AddrGhost} {rem : AddrVal}
    (hrem : rem = peer.val)
    (hAddr : ∀ evs, AddrValEnv peer.val evs → CliAddrTextEnv peer evs)
    (hGet : ∀ evs, GetEnv F0 d (addressText peer.val) evs →
      CliDirGetEnv (ReadFileRuleEnv rd) F0 d (addressText peer.val) evs)
    (hCap : ∀ bs, d.get rd F0 (addressText peer.val) = .ok bs → bs.length ≤ 2097152) :
    ∀ evs, cliSessionKitLoadPollEnv rd Scope AddrValEnv GetEnv
        (ofBytesEnv SessDeserSetAEnv) F0 d rem evs →
      CliSessLoadPollEnv rd SessDeserSetAEnv F0 d peer evs :=
  cliSessionKitLoadPollEnv_imp_cliSessLoadPollEnv hrem hAddr hGet hCap (fun _ _ _ hd => hd)

/-- `FilesOkPeer scopeKit` session-read link establishing `RecordDeserializeCancelEnv`,
`SessDeserializeCancelEnv`, `SessDeserSetBEnv`, and `SessDeserSetAEnv`. -/
theorem sessGet_dcan_and_profiles_of_filesOkPeer
    {F : FsFiles} {rem : AddrVal} {bs : List (BitVec 8)}
    (hok : FilesOkPeer scopeKit F rem)
    (hget : StoresGhost.opened.sessions.get cliIo.rd F (addressText rem) = .ok bs) :
    (bs = [] ∧ RecordDeserializeCancelEnv bs []) ∨
      ∃ r : SessionRecord (List (BitVec 8)),
        bs = encodeRecord r ∧
        scopeKit r ∧
        SessDeserializeCancelEnv r (sessDeserEvents r) ∧
        RecordDeserializeCancelEnv bs (sessDeserEvents r) ∧
        SessDeserSetBEnv bs (sessDeserEvents r) ∧
        SessDeserSetAEnv bs (sessDeserEvents r) := by
  rcases sessGet_empty_or_scopeKit_of_filesOkPeer hok hget with rfl | ⟨r, rfl, hr, hB, hA⟩
  · exact Or.inl ⟨rfl, nil_mem_recordDeserializeCancelEnv⟩
  · exact Or.inr ⟨r, rfl, hr,
      sessDeserEvents_mem_sessDeserializeCancelEnv hr,
      sessDeserEvents_mem_recordDeserializeCancelEnv hr, hB, hA⟩

/-- End-to-end `CliPqxdhInputs` domain chain establishing `FilesOkPeer scopeKit`,
`RecordDeserializeCancelEnv`, `SessDeserSetBEnv`, and `SessDeserSetAEnv`. -/
theorem cliPqxdhInputs_sessGet_dcan_and_profiles
    {W : PEParams} {i : Inputs} {c : CallV} {peer : AddrV} {bs : List (BitVec 8)}
    (hi : CliPqxdhInputs W i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some c)
    (hpeer : callPeer c = some peer)
    (hget : StoresGhost.opened.sessions.get cliIo.rd (runFiles i)
      (addressText (addrValOf peer)) = .ok bs) :
    (bs = [] ∧ RecordDeserializeCancelEnv bs []) ∨
      ∃ r : SessionRecord (List (BitVec 8)),
        bs = encodeRecord r ∧
        scopeKit r ∧
        SessDeserializeCancelEnv r (sessDeserEvents r) ∧
        RecordDeserializeCancelEnv bs (sessDeserEvents r) ∧
        SessDeserSetBEnv bs (sessDeserEvents r) ∧
        SessDeserSetAEnv bs (sessDeserEvents r) :=
  sessGet_dcan_and_profiles_of_filesOkPeer
    (filesOkPeer_scopeKit_of_cliPqxdhInputs hi hparse hpeer) hget

/-- `CliPqxdhInputs` implies `FilesOkPeer scopeKit` (`scopeKit = DeserializeScopeP_Q NonEmptyV1Q`). -/
theorem cliPqxdhInputs_filesOkPeer_scopeKit
    {W : PEParams} {i : Inputs} {c : CallV} {peer : AddrV}
    (hi : CliPqxdhInputs W i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some c)
    (hpeer : callPeer c = some peer) :
    FilesOkPeer scopeKit (runFiles i) (addrValOf peer) :=
  filesOkPeer_scopeKit_of_cliPqxdhInputs hi hparse hpeer

end LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser
