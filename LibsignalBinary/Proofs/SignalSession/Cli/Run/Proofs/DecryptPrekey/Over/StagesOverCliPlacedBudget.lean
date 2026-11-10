/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentitySelfStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget
public import LibsignalBinary.Proofs.RecordCodecs.AssemblyBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SelfSpecPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.StagesOverCliPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage1InstPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdKeyPairPollPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdRegIdPollPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.ShimsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Heap.SpecBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStmts
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.InitInv
import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable CLI Poll Self-Kit and Stage P1 Over-Path Adapters

Budget-threaded `[LibsignalPlacement]` self-identity poll envelopes (`cliPollSelfKpPollEnv`,
`cliPollSelfRegIdPollEnv`, `cliPollSelfBudgetEnv`), `IdentitySelfStoreKitPlacedOkI` instantiation
for `cliPollSelfKitPlaced`, and Stage P1 adapters (`OverStageP1OkCliPlacedStmt` and
`OverClosureUntrustedD2cPlacedStmt`) on Block `518`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.StagesOverCliPlacedBudget

open Arm64 Arm64.Process ProofLib
open CryptoGames.LibsignalSession (IdentityKey PublicKey)
open CryptoGames.LibsignalSessionApi (ApiError SessionRecord)
open CryptoVerification (
  IsLsBlockProg LibsignalHooks LibsignalPlacement lsmpl lsρ
)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.RecordCodecs (IdentityKeyPair)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (
  PanicOomProp decryptPrekeyCoroCopyAt decryptPrekeyCoroInitAt
  decryptPrekeySavedRegsAt processPrekeyInnerInitAt
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (
  loadCallStack stageP1CallStack stageP1UntrustedCallStack
)
open CryptoVerification.LibsignalTripleRatchet (extHookStack noAllocShimSpec)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost protocolAddressAt)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal apiDecResultAt preKeyMsgAt)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  FsFiles LibsignalCodeRoLoaded extract_withLsCodeRoLoaded kpPollOutAt
  ls_subroutine_ok_rocl_of_block regIdPollOutAt speErrAt subroutine_ok_rocl_of_withLsCodeRoLoaded
  subroutine_ok_withLsCodeRoLoaded_of_plain withEnvPre withLsCodeRoLoaded withLsLogOff withLsRoCl
)
open CryptoVerification.SignalSession (
  CliHooks cliExternsPlaced lsDropOffPlaced lsDropOffPlaced_eq lsReadFileSym
)
open CryptoVerification.SignalSession.Cli (
  IdGhost StoresGhost dirAt idKeyPairFutVtSym idRegIdFutVtSym pathOf utf8
)
open CryptoVerification.SignalSession.Cli.Placed (lsProg_602 lsProg_603)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo cliWrOk coinsInstalledPlaced storesAt)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.RunCompose (
  DecPkGhost RunSem decResAt dpPollNeed dpSlotArgsPlaced slotOutTr
)
open CryptoVerification.SignalSession.Cli.RunProofs (
  DecPkOkD2c decPkDef decPkDefD2c decPkDefD2c_eq_decPkDef_of_untrusted dpFutDoneAt dpFutStartAt
)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate (
  idKeyPairOutAt idOwnFutBoxAt idOwnFutBoxAtPlaced idRegIdOutAt
)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.IdKeyPairPoll (kpCalleeStk)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.IdRegIdPoll (regCalleeStk)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.PollCommon (
  idKeyPairOutAtPlaced_eq idRegIdOutAtPlaced_eq
)
open CryptoVerification.SignalSession.Cli.Slots (
  EncodeInjOn FilesOkPeer loadRec scopeIn scopeKit
)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon (satisfies_lscro_pre)
open CryptoVerification.SignalSession.Cli.KitInst (
  CliIdInv CliSelfSpeErr cliIdStoreAt cliIdentitySelfSpec cliIdentitySelfSpecPlaced
  cliIdentitySelf_kpErr_layout_placed cliIdentitySelf_regIdErr_layout_placed
  cliIdentityStoreSpec cliKyberPreKeyStoreSpecPlaced cliPreKeyStoreSpecPlaced
  cliSelfSpeErrSpec cliSessionStoreSpec cliSignedPreKeyStoreSpecPlaced
)
open CryptoVerification.SignalSession.Cli.KitInst.SelfRel (
  cliKpRel cliKpRel_error_iff cliKpRel_ok_iff cliRegIdRel cliRegIdRel_error_iff cliRegIdRel_ok_iff
)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (
  CliIdOwnInv DpKitStk LsTokenInit apiDecResultAt_untrusted_entails_decResAt
  cliIdSelfSpecFullPlaced cliIdStoreAtFull cliIdStoreSpecFull cliIdStoreSpecFullPlaced
  cliId_trustRel_eq_of_trusted cliKitStk cliKpkStoreSpecFullPlaced cliPollIdKit cliPollIdKitPlaced
  cliPollId_vtablesPlacedOk cliPollKpkKitPlaced cliPollPkKitPlaced cliPollSelfKitPlaced
  cliPollSessKit cliPollSessKitPlaced cliPollSess_vtablesPlacedOk cliPollSpkKitPlaced
  cliPollStoresKitsAtPlaced cliPollStoresKitsAtPlaced_entails_storesAt cliSess_loadRel_isOk
  closStackUnusedUntrustedAt clos_stack_3280_of_p1_untrusted clos_stack_3280_split_for_p1_untrusted
  closureCalleeSaved_toCalleeSavedPreserved coroUnusedP1At coro_of_p1_untrusted_entails_dpFutDoneAt
  decPkDef_of_trust_err dirGetNeed_eta
  dpClosSubStack dpFutStartAt_split_for_p1_placed dpPollEntryPlaced
  dpPollNeed_eq_frame_add_subStack dpPollProgPlaced
  loadRec_of_cliPollSessPlaced_loadRel pmKyberId pmPreKeyId
  preKeyMsgAt_eq_idKey_sep preKeyMsgRemIdKeyAt slotOutTr_of_err sp_frame_sub_add
  stackAt_poll_entry_split stackAt_subStack_split stageP1UntrustedCallStack_le_subStack
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentitySelfStoreKitBudget (
  IdentitySelfStoreBudgetEnv kitKpPollSpec kitKpPollSpecE kitKpShimSpec kitRegIdPollSpec
  kitRegIdPollSpecE kitRegIdShimSpec
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (
  IdentitySelfStoreKitPlacedOkI kitKpPollPlacedSpecI kitRegIdPollPlacedSpecI
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (futDropBudgetSpec)
open LibsignalBinary.Proofs.RecordCodecs.AssemblyBudget (
  identityKeyPair_tryFrom_placed_ok_of_hooks
)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (
  CliGhostHooks cliGhostExterns cliGhostExterns_other
)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a (DirGetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget (PathEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget (
  cliDirGet_placed_ok cliIdFutDrop_rocl_placed_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudgetAux (
  storesAt_opened_entails_cliPollStoresKitsAtPlaced_d2c
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageDefsPlacedBudget (
  StageP1OkEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget (
  CliDpPollUntrustedEnv StageP1UntrustedMangledPlacedStmt cliPollStageP1_fsAt_placed
  dpPollPost_of_decResAt_placed runHooks_of_stages stageP1_untrusted_mangled_placed_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage1InstPlacedBudget (
  StageP1OkTrapPlacedStmt stageP1OkPostAt stageP1OkPreAt stageP1_ok_trap_placed_inst
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget (
  cliPollIdBudgetEnv cliPollId_kitPlacedOkI cliPollSessBudgetEnv cliPollSess_kitPlacedOkSE
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdKeyPairPollPlacedBudget (
  CliIdKeyPairPollEnv OptIkpTryFromEnv idKeyPairPoll_placed_caller_ok_of_deps
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdRegIdPollPlacedBudget (
  CliIdRegIdPollEnv OptRegIdMalformedEnv idRegIdPoll_placed_caller_ok_of_deps
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.ShimsPlacedBudget (
  idKeyPairShim_placed_ok_of_deps idRegIdShim_placed_ok_of_deps
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (
  cliExternsPlaced_sessionMemcpyRegion_budget_sat
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget (
  DpPollGhostStateBudget dpPollSpecStateBudget dpSlotPollKStatePlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (
  ReadFileRuleEnv idKeyPairPollSpecPlaced idOwnShimSpecPlaced idRegIdPollSpecPlaced
  readFileSpecPlaced sessDeserializeSpecPlaced
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionMemcpyRegionBudgetSpec sessionShimBudgetSpec
)

abbrev RunHooksPlaced :=
  @LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced

/-! ## 1. Self-Identity Poll Envelopes & `cliPollSelf_kitPlacedOk` -/

/-- Tight pre-state-pinned allocation envelope for `IdentityFiles::get_identity_key_pair::{closure#0}`
on `cliPollSelfKitPlaced` (`Dir::get("identity-key-pair")`, `OptIkpTryFromEnv`, and `FreeOnlyEvs`). -/
def cliPollSelfKpPollEnv
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (F0 : FsFiles) (g : IdGhost) : List AllocEvent → Prop :=
  SeqEnv (DirGetEnv PathEnv ReadEnv cliIo.rd F0 g.own (utf8 "identity-key-pair"))
    (SeqEnv (OptIkpTryFromEnv (g.own.get cliIo.rd F0 (utf8 "identity-key-pair"))) FreeOnlyEvs)

/-- Tight pre-state-pinned allocation envelope for
`IdentityFiles::get_local_registration_id::{closure#0}` on `cliPollSelfKitPlaced`
(`Dir::get("registration-id")`, `OptRegIdMalformedEnv`, and `FreeOnlyEvs`). -/
def cliPollSelfRegIdPollEnv
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (F0 : FsFiles) (g : IdGhost) : List AllocEvent → Prop :=
  SeqEnv (DirGetEnv PathEnv ReadEnv cliIo.rd F0 g.own (utf8 "registration-id"))
    (SeqEnv (OptRegIdMalformedEnv (g.own.get cliIo.rd F0 (utf8 "registration-id"))) FreeOnlyEvs)

/-- Canonical `IdentitySelfStoreBudgetEnv` for `cliPollSelfKitPlaced`. -/
def cliPollSelfBudgetEnv [LibsignalPlacement] (A : RustAlloc) (F0 : FsFiles)
    (peer : AddrGhost) (σ : DpKitStk)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop := ReadFileRuleEnv cliIo.rd) :
    IdentitySelfStoreBudgetEnv (cliPollSelfKitPlaced A F0 peer σ) where
  kpPollEnv := cliPollSelfKpPollEnv ReadEnv F0
  regIdPollEnv := cliPollSelfRegIdPollEnv ReadEnv F0

private theorem cliPollSelf_kpShim_rocl [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hblk : callerBlk < 619) :
    let skit := cliPollSelfKitPlaced A.repAlloc F0 peer (cliKitStk B)
    subroutine_ok callerProg (0#64 + skit.kpShimOff)
      (withLsRoCl lsmpl (kitKpShimSpec M A lim skit)) := by
  intro skit
  have h602 := idKeyPairShim_placed_ok_of_deps (H := cliGhostExterns gh (cliExternsPlaced mmpl W))
    (stk := (cliKitStk B).kpShim) hh.alloc (by dsimp [cliKitStk, extHookStack]; omega)
  have h602_kit : subroutine_ok (lsProg_602 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 602)
      (withLsCodeRoLoaded lsmpl (kitKpShimSpec M A lim skit)) := by
    refine subroutine_ok_outcome_intro fun ⟨self, st⟩ R s0 hpc hrun hpre hsp => ?_
    obtain ⟨hcrl, hpre0⟩ := extract_withLsCodeRoLoaded hpre
    have hpre' :
        s0.mem ⊨
          (idOwnShimSpecPlaced idKeyPairFutVtSym A lim (cliKitStk B).kpShim).pre (self, st) s0 ∗ R := by
      refine satisfies_lscro_pre hcrl ?_
      dsimp only [kitKpShimSpec, skit, cliPollSelfKitPlaced, cliIdSelfSpecFullPlaced] at hpre0 ⊢
      exact hpre0
    refine h602.mono_outcome (self, st) R s0 hpc hrun hpre' hsp ?_
    rintro sf (⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩)
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [idOwnShimSpecPlaced, withLsCodeRoLoaded, kitKpShimSpec,
        skit, cliPollSelfKitPlaced, cliIdSelfSpecFullPlaced, idOwnFutBoxAtPlaced,
        idOwnFutBoxAt] at hq ⊢
      simpa only [BitVec.zero_add] using hq
    · dsimp only [idOwnShimSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
    · dsimp only [idOwnShimSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
    · dsimp only [idOwnShimSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
  change subroutine_ok callerProg (0#64 + lsmpl.base 602) _
  rw [BitVec.zero_add]
  exact ls_subroutine_ok_rocl_of_block (callerProg := callerProg) (j := 602)
    h602_kit hblk (by decide) (by decide)

private theorem cliPollSelf_regIdShim_rocl [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hblk : callerBlk < 619) :
    let skit := cliPollSelfKitPlaced A.repAlloc F0 peer (cliKitStk B)
    subroutine_ok callerProg (0#64 + skit.regIdShimOff)
      (withLsRoCl lsmpl (kitRegIdShimSpec M A lim skit)) := by
  intro skit
  have h603 := idRegIdShim_placed_ok_of_deps (H := cliGhostExterns gh (cliExternsPlaced mmpl W))
    (stk := (cliKitStk B).regIdShim) hh.alloc (by dsimp [cliKitStk, extHookStack]; omega)
  have h603_kit : subroutine_ok (lsProg_603 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 603)
      (withLsCodeRoLoaded lsmpl (kitRegIdShimSpec M A lim skit)) := by
    refine subroutine_ok_outcome_intro fun ⟨self, st⟩ R s0 hpc hrun hpre hsp => ?_
    obtain ⟨hcrl, hpre0⟩ := extract_withLsCodeRoLoaded hpre
    have hpre' :
        s0.mem ⊨
          (idOwnShimSpecPlaced idRegIdFutVtSym A lim (cliKitStk B).regIdShim).pre (self, st) s0 ∗ R := by
      refine satisfies_lscro_pre hcrl ?_
      dsimp only [kitRegIdShimSpec, skit, cliPollSelfKitPlaced, cliIdSelfSpecFullPlaced] at hpre0 ⊢
      exact hpre0
    refine h603.mono_outcome (self, st) R s0 hpc hrun hpre' hsp ?_
    rintro sf (⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩)
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [idOwnShimSpecPlaced, withLsCodeRoLoaded, kitRegIdShimSpec,
        skit, cliPollSelfKitPlaced, cliIdSelfSpecFullPlaced, idOwnFutBoxAtPlaced,
        idOwnFutBoxAt] at hq ⊢
      simpa only [BitVec.zero_add] using hq
    · dsimp only [idOwnShimSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
    · dsimp only [idOwnShimSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
    · dsimp only [idOwnShimSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
  change subroutine_ok callerProg (0#64 + lsmpl.base 603) _
  rw [BitVec.zero_add]
  exact ls_subroutine_ok_rocl_of_block (callerProg := callerProg) (j := 603)
    h603_kit hblk (by decide) (by decide)

private theorem cliPollSelf_kpPoll_rocl [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hblk : callerBlk < 619) :
    let skit := cliPollSelfKitPlaced A.repAlloc F0 peer (cliKitStk B)
    let senv := cliPollSelfBudgetEnv A.repAlloc F0 peer (cliKitStk B) ReadEnv
    subroutine_ok callerProg (0#64 + skit.kpPollOff)
      (withLsRoCl lsmpl (kitKpPollPlacedSpecI M A lim skit senv)) := by
  intro skit senv
  have hGet589 := cliDirGet_placed_ok
    (readProg := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (jRead := 518)
    (fun _ hp => hp.2) hh
    (subroutine_ok_withLsCodeRoLoaded_of_plain hRead)
    (by decide) (by decide)
  have hDec84 := identityKeyPair_tryFrom_placed_ok_of_hooks hh.codecHooks
  have hhop := idKeyPairPoll_placed_caller_ok_of_deps
    (callerProg := callerProg) (callerBlk := callerBlk)
    (stk := (cliKitStk B).kpPoll)
    hh.alloc hGet589 hDec84
    (by rw [dirGetNeed_eta B]; dsimp [cliKitStk, kpCalleeStk]; omega)
    hblk (by decide) (by decide) (by decide) (by decide)
  change subroutine_ok callerProg (0#64 + lsmpl.base 567) _
  rw [BitVec.zero_add]
  refine subroutine_ok_rocl_of_withLsCodeRoLoaded ?_
  refine subroutine_ok_outcome_intro fun ⟨fut, out, self, g, st⟩ R s0 hpc hrun hpre hsp => ?_
  change IdGhost at g
  dsimp only [withLsCodeRoLoaded, kitKpPollPlacedSpecI, withLsLogOff,
    kitKpPollSpecE, kitKpPollSpec, withEnvPre,
    skit, senv, cliPollSelfKitPlaced, cliPollSelfBudgetEnv, cliPollSelfKpPollEnv,
    cliIdSelfSpecFullPlaced, cliPollIdKitPlaced,
    cliIdStoreSpecFullPlaced, cliIdStoreSpecFull, cliIdStoreAtFull,
    cliIdentityStoreSpec, cliIdStoreAt] at hpre
  have hpre' : s0.mem ⊨
      ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
      (⌜s0.fs.files = F0⌝ ∗
      (⌜s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
        FitsEnv M lim st
          (SeqEnv (DirGetEnv PathEnv ReadEnv cliIo.rd F0 g.own (utf8 "identity-key-pair"))
            (SeqEnv (OptIkpTryFromEnv (g.own.get cliIo.rd F0 (utf8 "identity-key-pair")))
              FreeOnlyEvs))⌝ ∗
      (⌜CliIdOwnInv cliIo.rd F0 cliWrOk g.own⌝ ∗
      (⌜CliIdInv cliIo.rd F0 cliWrOk peer g⌝ ∗
      (idOwnFutBoxAt fut self 0#8 ∗ dirAt A.repAlloc self g.own ∗
        memRegion out 72 ∗ lsLogOff ∗ A.pool lim st s0 ∗
        stackAt s0.sp (cliKitStk B).kpPoll ∗
        (dirAt A.repAlloc (self + 0x28#64) g.peers ∗ R)))))) :=
    Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hpre
  rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hcrl, hpre'⟩ := hpre'
  rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hfiles, hpre'⟩ := hpre'
  rw [satisfies_pure_sepConj] at hpre'; obtain ⟨⟨hx0, hx8, hfit⟩, hpre'⟩ := hpre'
  rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hown, hpre'⟩ := hpre'
  rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hinv, hspatial⟩ := hpre'
  let frameKpCore : SepProp :=
    ⌜CliIdOwnInv cliIo.rd F0 cliWrOk g.own⌝ ∗
    ⌜CliIdInv cliIo.rd F0 cliWrOk peer g⌝ ∗
    dirAt A.repAlloc (self + 0x28#64) g.peers
  have hfit_hop :
      FitsEnv M lim st
        (CliIdKeyPairPollEnv (DirGetEnv PathEnv ReadEnv cliIo.rd) cliIo.rd
          s0.fs.files ⟨fut, out, self, g.own⟩) := by
    rw [hfiles]; exact hfit
  have hhop_pure :
      s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
        g.own.path.length < 2 ^ 32 ∧
        cliWrOk (pathOf g.own.path (utf8 "identity-key-pair")) ∧
        (∀ bs, g.own.get cliIo.rd s0.fs.files (utf8 "identity-key-pair") = .ok bs →
          bs.length < 2 ^ 32) ∧
        FitsEnv M lim st
          (CliIdKeyPairPollEnv (DirGetEnv PathEnv ReadEnv cliIo.rd) cliIo.rd
            s0.fs.files ⟨fut, out, self, g.own⟩) :=
    ⟨hx0, hx8, hown.ownPathLt, hown.kpPathOk,
      fun bs hbs => hown.kpSizeOk bs (hfiles ▸ hbs), hfit_hop⟩
  have hm_hop :
      s0.mem ⊨
        (idKeyPairPollSpecPlaced cliIo.rd cliWrOk A lim
          (CliIdKeyPairPollEnv (DirGetEnv PathEnv ReadEnv cliIo.rd) cliIo.rd)
          (cliKitStk B).kpPoll).pre (⟨fut, out, self, g.own⟩, st) s0 ∗
        (frameKpCore ∗ R) := by
    dsimp only [idKeyPairPollSpecPlaced, withLsCodeRoLoaded, frameKpCore,
      idOwnFutBoxAtPlaced, idOwnFutBoxAt] at hspatial ⊢
    have h1 : s0.mem ⊨
        ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
        (⌜s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
          g.own.path.length < 2 ^ 32 ∧
          cliWrOk (pathOf g.own.path (utf8 "identity-key-pair")) ∧
          (∀ bs, g.own.get cliIo.rd s0.fs.files (utf8 "identity-key-pair") = .ok bs →
            bs.length < 2 ^ 32) ∧
          FitsEnv M lim st
            (CliIdKeyPairPollEnv (DirGetEnv PathEnv ReadEnv cliIo.rd) cliIo.rd
              s0.fs.files ⟨fut, out, self, g.own⟩)⌝ ∗
        (⌜CliIdOwnInv cliIo.rd F0 cliWrOk g.own⌝ ∗
        (⌜CliIdInv cliIo.rd F0 cliWrOk peer g⌝ ∗
        (idOwnFutBoxAt fut self 0#8 ∗ dirAt A.repAlloc self g.own ∗
          memRegion out 72 ∗ lsLogOff ∗ A.pool lim st s0 ∗
          stackAt s0.sp (cliKitStk B).kpPoll ∗
          (dirAt A.repAlloc (self + 0x28#64) g.peers ∗ R))))) := by
      rw [satisfies_pure_sepConj]; refine ⟨hcrl, ?_⟩
      rw [satisfies_pure_sepConj]; refine ⟨hhop_pure, ?_⟩
      rw [satisfies_pure_sepConj]; refine ⟨hown, ?_⟩
      rw [satisfies_pure_sepConj]
      dsimp only [idOwnFutBoxAt]
      exact ⟨hinv, hspatial⟩
    dsimp only [idOwnFutBoxAt, CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff,
      CryptoVerification.LibsignalTripleRatchet.lsLogOff] at h1 ⊢
    exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) h1
  refine hhop.mono_outcome (⟨fut, out, self, g.own⟩, st) (frameKpCore ∗ R)
    s0 hpc hrun hm_hop hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [idKeyPairPollSpecPlaced, withLsCodeRoLoaded, frameKpCore] at hpost
    simp_rw [idKeyPairOutAtPlaced_eq] at hpost
    simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
      satisfies_pure_sepConj] at hpost
    obtain ⟨evs, ans0, ⟨hans0, htr, hevs⟩, hm⟩ := hpost
    rw [hfiles, IdGhost.keyPair_mk_own] at hans0
    rw [hfiles] at hevs
    dsimp only [withLsCodeRoLoaded, kitKpPollPlacedSpecI, withLsLogOff,
      kitKpPollSpecE, kitKpPollSpec, withEnvPre,
      skit, senv, cliPollSelfKitPlaced, cliPollSelfBudgetEnv, cliPollSelfKpPollEnv,
      cliIdSelfSpecFullPlaced, cliPollIdKitPlaced,
      cliIdStoreSpecFullPlaced, cliIdStoreSpecFull, cliIdStoreAtFull,
      cliIdentityStoreSpec, cliIdStoreAt]
    simp only [sepExists_sepConj_left, satisfies_sepExists]
    cases ans0 with
    | ok kp =>
      have hrel : cliKpRel (E := CliSelfSpeErr) cliIo.rd F0 g (.ok kp) :=
        (cliKpRel_ok_iff (E := CliSelfSpeErr) cliIo.rd F0 g kp).2 hans0.symm
      refine ⟨.ok kp, evs, ?_⟩
      dsimp only [kpPollOutAt, idKeyPairOutAt, idOwnFutBoxAtPlaced, idOwnFutBoxAt] at hm ⊢
      have hgoal : sf.mem ⊨
          ⌜cliKpRel (E := CliSelfSpeErr) cliIo.rd F0 g (.ok kp) ∧
            sf.trace = s0.trace ++ [] ∧
            SeqEnv (DirGetEnv PathEnv ReadEnv cliIo.rd F0 g.own (utf8 "identity-key-pair"))
              (SeqEnv (OptIkpTryFromEnv (g.own.get cliIo.rd F0 (utf8 "identity-key-pair")))
                FreeOnlyEvs) evs⌝ ∗
          (idKeyPairOutAt A.repAlloc out (.ok kp) ∗ idOwnFutBoxAt fut self 1#8 ∗
            dirAt A.repAlloc self g.own ∗ lsLogOff ∗ A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp (cliKitStk B).kpPoll ∗
            ⌜CliIdOwnInv cliIo.rd F0 cliWrOk g.own⌝ ∗
            ⌜CliIdInv cliIo.rd F0 cliWrOk peer g⌝ ∗
            dirAt A.repAlloc (self + 0x28#64) g.peers ∗ R) := by
        dsimp only [idKeyPairOutAt, idOwnFutBoxAt]
        rw [satisfies_pure_sepConj]
        exact ⟨⟨hrel, by rw [List.append_nil]; exact htr, hevs⟩, hm⟩
      dsimp only [idKeyPairOutAt, idOwnFutBoxAt] at hgoal
      exact Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hgoal
    | error u =>
      cases u
      have herr_ent :
          idKeyPairOutAt A.repAlloc out (.error ()) ⊢
            ∃∗ e : skit.KpErr, kpPollOutAt skit out (.error e) :=
        (cliIdentitySelf_kpErr_layout_placed A.repAlloc F0
          (peer := peer) (t1 := (cliKitStk B).idTrustShim) (t2 := (cliKitStk B).idTrustPoll)
          (t3 := (cliKitStk B).idSaveShim) (t4 := (cliKitStk B).idSavePoll)
          (k1 := (cliKitStk B).kpShim) (k2 := (cliKitStk B).kpPoll)
          (k3 := (cliKitStk B).regIdShim) (k4 := (cliKitStk B).regIdPoll) out).2
      have hm' := Satisfies.mono (sepConj_mono_left herr_ent) hm
      rw [sepExists_sepConj_left, satisfies_sepExists] at hm'
      dsimp only [skit, cliPollSelfKitPlaced, cliIdSelfSpecFullPlaced,
        cliIdentitySelfSpecPlaced, cliIdentitySelfSpec,
        kpPollOutAt, idOwnFutBoxAtPlaced, idOwnFutBoxAt] at hm' ⊢
      obtain ⟨e, hme⟩ := hm'
      have hrel : cliKpRel cliIo.rd F0 g (.error e) :=
        (cliKpRel_error_iff cliIo.rd F0 g e).2 hans0.symm
      refine ⟨.error e, evs, ?_⟩
      dsimp only [kpPollOutAt, cliIdentitySelfSpecPlaced, cliIdentitySelfSpec]
      have hgoal : sf.mem ⊨
          ⌜cliKpRel cliIo.rd F0 g (.error e) ∧
            sf.trace = s0.trace ++ [] ∧
            SeqEnv (DirGetEnv PathEnv ReadEnv cliIo.rd F0 g.own (utf8 "identity-key-pair"))
              (SeqEnv (OptIkpTryFromEnv (g.own.get cliIo.rd F0 (utf8 "identity-key-pair")))
                FreeOnlyEvs) evs⌝ ∗
          (((out ↦₈ 1#8) ∗ memRegion (out + 1#64) 7 ∗
              speErrAt (cliSelfSpeErrSpec A.repAlloc) (out + 8#64) e ∗
              memRegion (out + 0x38#64) 16) ∗
            ((fut ↦₆₄ self) ∗ ((fut + 8#64) ↦₈ 1#8) ∗ memRegion (fut + 9#64) 7) ∗
            dirAt A.repAlloc self g.own ∗ lsLogOff ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp (cliKitStk B).kpPoll ∗
            ⌜CliIdOwnInv cliIo.rd F0 cliWrOk g.own⌝ ∗
            ⌜CliIdInv cliIo.rd F0 cliWrOk peer g⌝ ∗
            dirAt A.repAlloc (self + 0x28#64) g.peers ∗ R) := by
        rw [satisfies_pure_sepConj]
        exact ⟨⟨hrel, by rw [List.append_nil]; exact htr, hevs⟩, hme⟩
      exact Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hgoal
  · dsimp only [idKeyPairPollSpecPlaced, withLsCodeRoLoaded] at hpan
    exact (not_satisfies_false_sepConj hpan).elim
  · dsimp only [idKeyPairPollSpecPlaced, withLsCodeRoLoaded] at hex
    exact (not_satisfies_false_sepConj hex).elim
  · dsimp only [idKeyPairPollSpecPlaced, withLsCodeRoLoaded] at hoom
    exact (not_satisfies_false_sepConj hoom).elim

private theorem cliPollSelf_regIdPoll_rocl [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hblk : callerBlk < 619) :
    let skit := cliPollSelfKitPlaced A.repAlloc F0 peer (cliKitStk B)
    let senv := cliPollSelfBudgetEnv A.repAlloc F0 peer (cliKitStk B) ReadEnv
    subroutine_ok callerProg (0#64 + skit.regIdPollOff)
      (withLsRoCl lsmpl (kitRegIdPollPlacedSpecI M A lim skit senv)) := by
  intro skit senv
  have hGet589 := cliDirGet_placed_ok
    (readProg := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (jRead := 518)
    (fun _ hp => hp.2) hh
    (subroutine_ok_withLsCodeRoLoaded_of_plain hRead)
    (by decide) (by decide)
  have hhop := idRegIdPoll_placed_caller_ok_of_deps
    (callerProg := callerProg) (callerBlk := callerBlk)
    (stk := (cliKitStk B).regIdPoll)
    hh.alloc hGet589
    (by rw [dirGetNeed_eta B]; dsimp [cliKitStk, regCalleeStk]; omega)
    hblk (by decide) (by decide)
  change subroutine_ok callerProg (0#64 + lsmpl.base 568) _
  rw [BitVec.zero_add]
  refine subroutine_ok_rocl_of_withLsCodeRoLoaded ?_
  refine subroutine_ok_outcome_intro fun ⟨fut, out, self, g, st⟩ R s0 hpc hrun hpre hsp => ?_
  change IdGhost at g
  dsimp only [withLsCodeRoLoaded, kitRegIdPollPlacedSpecI, withLsLogOff,
    kitRegIdPollSpecE, kitRegIdPollSpec, withEnvPre,
    skit, senv, cliPollSelfKitPlaced, cliPollSelfBudgetEnv, cliPollSelfRegIdPollEnv,
    cliIdSelfSpecFullPlaced, cliPollIdKitPlaced,
    cliIdStoreSpecFullPlaced, cliIdStoreSpecFull, cliIdStoreAtFull,
    cliIdentityStoreSpec, cliIdStoreAt] at hpre
  have hpre' : s0.mem ⊨
      ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
      (⌜s0.fs.files = F0⌝ ∗
      (⌜s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
        FitsEnv M lim st
          (SeqEnv (DirGetEnv PathEnv ReadEnv cliIo.rd F0 g.own (utf8 "registration-id"))
            (SeqEnv (OptRegIdMalformedEnv (g.own.get cliIo.rd F0 (utf8 "registration-id")))
              FreeOnlyEvs))⌝ ∗
      (⌜CliIdOwnInv cliIo.rd F0 cliWrOk g.own⌝ ∗
      (⌜CliIdInv cliIo.rd F0 cliWrOk peer g⌝ ∗
      (idOwnFutBoxAt fut self 0#8 ∗ dirAt A.repAlloc self g.own ∗
        memRegion out 48 ∗ A.pool lim st s0 ∗
        stackAt s0.sp (cliKitStk B).regIdPoll ∗
        (dirAt A.repAlloc (self + 0x28#64) g.peers ∗ lsLogOff ∗ R)))))) :=
    Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hpre
  rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hcrl, hpre'⟩ := hpre'
  rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hfiles, hpre'⟩ := hpre'
  rw [satisfies_pure_sepConj] at hpre'; obtain ⟨⟨hx0, hx8, hfit⟩, hpre'⟩ := hpre'
  rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hown, hpre'⟩ := hpre'
  rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hinv, hspatial⟩ := hpre'
  let frameRegCore : SepProp :=
    ⌜CliIdOwnInv cliIo.rd F0 cliWrOk g.own⌝ ∗
    ⌜CliIdInv cliIo.rd F0 cliWrOk peer g⌝ ∗
    dirAt A.repAlloc (self + 0x28#64) g.peers ∗ lsLogOff
  have hfit_hop :
      FitsEnv M lim st
        (CliIdRegIdPollEnv (DirGetEnv PathEnv ReadEnv cliIo.rd) cliIo.rd
          s0.fs.files ⟨fut, out, self, g.own⟩) := by
    rw [hfiles]; exact hfit
  have hhop_pure :
      s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
        g.own.path.length < 2 ^ 32 ∧
        cliWrOk (pathOf g.own.path (utf8 "registration-id")) ∧
        FitsEnv M lim st
          (CliIdRegIdPollEnv (DirGetEnv PathEnv ReadEnv cliIo.rd) cliIo.rd
            s0.fs.files ⟨fut, out, self, g.own⟩) :=
    ⟨hx0, hx8, hown.ownPathLt, hown.regPathOk, hfit_hop⟩
  have hm_hop :
      s0.mem ⊨
        (idRegIdPollSpecPlaced cliIo.rd cliWrOk A lim
          (CliIdRegIdPollEnv (DirGetEnv PathEnv ReadEnv cliIo.rd) cliIo.rd)
          (cliKitStk B).regIdPoll).pre (⟨fut, out, self, g.own⟩, st) s0 ∗
        (frameRegCore ∗ R) := by
    dsimp only [idRegIdPollSpecPlaced, withLsCodeRoLoaded, frameRegCore,
      idOwnFutBoxAtPlaced, idOwnFutBoxAt] at hspatial ⊢
    have h1 : s0.mem ⊨
        ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
        (⌜s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
          g.own.path.length < 2 ^ 32 ∧
          cliWrOk (pathOf g.own.path (utf8 "registration-id")) ∧
          FitsEnv M lim st
            (CliIdRegIdPollEnv (DirGetEnv PathEnv ReadEnv cliIo.rd) cliIo.rd
              s0.fs.files ⟨fut, out, self, g.own⟩)⌝ ∗
        (⌜CliIdOwnInv cliIo.rd F0 cliWrOk g.own⌝ ∗
        (⌜CliIdInv cliIo.rd F0 cliWrOk peer g⌝ ∗
        (idOwnFutBoxAt fut self 0#8 ∗ dirAt A.repAlloc self g.own ∗
          memRegion out 48 ∗ A.pool lim st s0 ∗
          stackAt s0.sp (cliKitStk B).regIdPoll ∗
          (dirAt A.repAlloc (self + 0x28#64) g.peers ∗ lsLogOff ∗ R))))) := by
      rw [satisfies_pure_sepConj]; refine ⟨hcrl, ?_⟩
      rw [satisfies_pure_sepConj]; refine ⟨hhop_pure, ?_⟩
      rw [satisfies_pure_sepConj]; refine ⟨hown, ?_⟩
      rw [satisfies_pure_sepConj]
      dsimp only [idOwnFutBoxAt]
      exact ⟨hinv, hspatial⟩
    dsimp only [idOwnFutBoxAt, CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff,
      CryptoVerification.LibsignalTripleRatchet.lsLogOff] at h1 ⊢
    exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) h1
  refine hhop.mono_outcome (⟨fut, out, self, g.own⟩, st) (frameRegCore ∗ R)
    s0 hpc hrun hm_hop hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [idRegIdPollSpecPlaced, withLsCodeRoLoaded, frameRegCore] at hpost
    simp_rw [idRegIdOutAtPlaced_eq] at hpost
    simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
      satisfies_pure_sepConj] at hpost
    obtain ⟨evs, ans0, ⟨hans0, htr, hevs⟩, hm⟩ := hpost
    rw [hfiles, IdGhost.regId_mk_own] at hans0
    rw [hfiles] at hevs
    dsimp only [withLsCodeRoLoaded, kitRegIdPollPlacedSpecI, withLsLogOff,
      kitRegIdPollSpecE, kitRegIdPollSpec, withEnvPre,
      skit, senv, cliPollSelfKitPlaced, cliPollSelfBudgetEnv, cliPollSelfRegIdPollEnv,
      cliIdSelfSpecFullPlaced, cliPollIdKitPlaced,
      cliIdStoreSpecFullPlaced, cliIdStoreSpecFull, cliIdStoreAtFull,
      cliIdentityStoreSpec, cliIdStoreAt]
    simp only [sepExists_sepConj_left, satisfies_sepExists]
    cases ans0 with
    | ok reg =>
      have hrel : cliRegIdRel (E := CliSelfSpeErr) cliIo.rd F0 g (.ok reg) :=
        (cliRegIdRel_ok_iff (E := CliSelfSpeErr) cliIo.rd F0 g reg).2 hans0.symm
      refine ⟨.ok reg, evs, ?_⟩
      dsimp only [regIdPollOutAt, idRegIdOutAt, idOwnFutBoxAtPlaced, idOwnFutBoxAt] at hm ⊢
      have hgoal : sf.mem ⊨
          ⌜cliRegIdRel (E := CliSelfSpeErr) cliIo.rd F0 g (.ok reg) ∧
            sf.trace = s0.trace ++ [] ∧
            SeqEnv (DirGetEnv PathEnv ReadEnv cliIo.rd F0 g.own (utf8 "registration-id"))
              (SeqEnv (OptRegIdMalformedEnv (g.own.get cliIo.rd F0 (utf8 "registration-id")))
                FreeOnlyEvs) evs⌝ ∗
          (((out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ ((out + 8#64) ↦₃₂ reg) ∗
              memRegion (out + 12#64) 36) ∗
            idOwnFutBoxAt fut self 1#8 ∗
            dirAt A.repAlloc self g.own ∗ A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp (cliKitStk B).regIdPoll ∗
            ⌜CliIdOwnInv cliIo.rd F0 cliWrOk g.own⌝ ∗
            ⌜CliIdInv cliIo.rd F0 cliWrOk peer g⌝ ∗
            dirAt A.repAlloc (self + 0x28#64) g.peers ∗ lsLogOff ∗ R) := by
        dsimp only [idOwnFutBoxAt]
        rw [satisfies_pure_sepConj]
        exact ⟨⟨hrel, by rw [List.append_nil]; exact htr, hevs⟩, hm⟩
      dsimp only [idOwnFutBoxAt] at hgoal
      exact Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hgoal
    | error u =>
      cases u
      have herr_ent :
          idRegIdOutAt A.repAlloc out (.error ()) ⊢
            ∃∗ e : skit.RegIdErr, regIdPollOutAt skit out (.error e) :=
        (cliIdentitySelf_regIdErr_layout_placed A.repAlloc F0
          (peer := peer) (t1 := (cliKitStk B).idTrustShim) (t2 := (cliKitStk B).idTrustPoll)
          (t3 := (cliKitStk B).idSaveShim) (t4 := (cliKitStk B).idSavePoll)
          (k1 := (cliKitStk B).kpShim) (k2 := (cliKitStk B).kpPoll)
          (k3 := (cliKitStk B).regIdShim) (k4 := (cliKitStk B).regIdPoll) out).2
      have hm' := Satisfies.mono (sepConj_mono_left herr_ent) hm
      rw [sepExists_sepConj_left, satisfies_sepExists] at hm'
      dsimp only [skit, cliPollSelfKitPlaced, cliIdSelfSpecFullPlaced,
        cliIdentitySelfSpecPlaced, cliIdentitySelfSpec,
        regIdPollOutAt, idOwnFutBoxAtPlaced, idOwnFutBoxAt] at hm' ⊢
      obtain ⟨e, hme⟩ := hm'
      have hrel : cliRegIdRel cliIo.rd F0 g (.error e) :=
        (cliRegIdRel_error_iff cliIo.rd F0 g e).2 hans0.symm
      refine ⟨.error e, evs, ?_⟩
      dsimp only [regIdPollOutAt, cliIdentitySelfSpecPlaced, cliIdentitySelfSpec]
      have hgoal : sf.mem ⊨
          ⌜cliRegIdRel cliIo.rd F0 g (.error e) ∧
            sf.trace = s0.trace ++ [] ∧
            SeqEnv (DirGetEnv PathEnv ReadEnv cliIo.rd F0 g.own (utf8 "registration-id"))
              (SeqEnv (OptRegIdMalformedEnv (g.own.get cliIo.rd F0 (utf8 "registration-id")))
                FreeOnlyEvs) evs⌝ ∗
          (speErrAt (cliSelfSpeErrSpec A.repAlloc) out e ∗
            ((fut ↦₆₄ self) ∗ ((fut + 8#64) ↦₈ 1#8) ∗ memRegion (fut + 9#64) 7) ∗
            dirAt A.repAlloc self g.own ∗ A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp (cliKitStk B).regIdPoll ∗
            ⌜CliIdOwnInv cliIo.rd F0 cliWrOk g.own⌝ ∗
            ⌜CliIdInv cliIo.rd F0 cliWrOk peer g⌝ ∗
            dirAt A.repAlloc (self + 0x28#64) g.peers ∗ lsLogOff ∗ R) := by
        rw [satisfies_pure_sepConj]
        exact ⟨⟨hrel, by rw [List.append_nil]; exact htr, hevs⟩, hme⟩
      exact Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hgoal
  · dsimp only [idRegIdPollSpecPlaced, withLsCodeRoLoaded] at hpan
    exact (not_satisfies_false_sepConj hpan).elim
  · dsimp only [idRegIdPollSpecPlaced, withLsCodeRoLoaded] at hex
    exact (not_satisfies_false_sepConj hex).elim
  · dsimp only [idRegIdPollSpecPlaced, withLsCodeRoLoaded] at hoom
    exact (not_satisfies_false_sepConj hoom).elim

/-- Discharges `IdentitySelfStoreKitPlacedOkI` for `cliPollSelfKitPlaced` under
`SkeletonPlacedBudget.RunHooksPlaced` and `hRead`. -/
theorem cliPollSelf_kitPlacedOk [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv)) :
    IdentitySelfStoreKitPlacedOkI A lim
      (cliPollIdKitPlaced A.repAlloc F0 peer (cliKitStk B))
      (cliPollSelfKitPlaced A.repAlloc F0 peer (cliKitStk B))
      (cliPollSelfBudgetEnv A.repAlloc F0 peer (cliKitStk B) ReadEnv)
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) where
  kpShim hblk := cliPollSelf_kpShim_rocl mmpl gh W B F0 peer hh hblk
  kpPoll hblk := cliPollSelf_kpPoll_rocl mmpl gh W B F0 peer hh hRead hblk
  kpFutDrop hblk := by
    change subroutine_ok _ (0#64 + lsDropOffPlaced) _
    rw [lsDropOffPlaced_eq hDropNz]; exact cliIdFutDrop_rocl_placed_ok hblk
  regIdShim hblk := cliPollSelf_regIdShim_rocl mmpl gh W B F0 peer hh hblk
  regIdPoll hblk := cliPollSelf_regIdPoll_rocl mmpl gh W B F0 peer hh hRead hblk
  regIdFutDrop hblk := by
    change subroutine_ok _ (0#64 + lsDropOffPlaced) _
    rw [lsDropOffPlaced_eq hDropNz]; exact cliIdFutDrop_rocl_placed_ok hblk

/-- Convenience wrapper around `cliPollSelf_kitPlacedOk` accepting
`ClosureStagesStmtPlacedBudget.RunHooksPlaced`. -/
theorem cliPollSelf_kitPlacedOk_stagesHooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv)) :
    IdentitySelfStoreKitPlacedOkI A lim
      (cliPollIdKitPlaced A.repAlloc F0 peer (cliKitStk B))
      (cliPollSelfKitPlaced A.repAlloc F0 peer (cliKitStk B))
      (cliPollSelfBudgetEnv A.repAlloc F0 peer (cliKitStk B) ReadEnv)
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  cliPollSelf_kitPlacedOk mmpl gh W B F0 peer hDropNz (runHooks_of_stages hh) hRead

/-! ## 2. Placed Stage P1 CLI Adapters (`OverStageP1OkCliPlacedStmt`, `OverClosureUntrustedD2cPlacedStmt`) -/

/-- Budget-threaded counterpart of `Poll.OverStageP1OkCliPlacedStmt` (`onPanic := PanicOomProp s0`,
fixing `st := StoresGhost.opened.sessions`, `ist := StoresGhost.opened.identity`, and
`s0.fs.files = F0`). -/
def OverStageP1OkCliPlacedStmt [LibsignalPlacement] : Prop :=
  ∀ {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost) (remoteIdKey : IdentityKey),
    let σ := cliKitStk B
    let kit := cliPollSessKitPlaced A.repAlloc F0 scopeKit peer σ
    let ikit := cliPollIdKitPlaced A.repAlloc F0 peer σ
    let kitEnv := cliPollSessBudgetEnv A.repAlloc F0 peer σ DeserEnv ReadEnv
    let ikitEnv := cliPollIdBudgetEnv A.repAlloc F0 peer σ ReadEnv
    ∀ (st_b : M.σ),
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget.RunHooksPlaced
        A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym)
        (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv) →
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsmpl.base 46)
        (sessDeserializeSpecPlaced scopeKit A lim DeserEnv) →
      stageP1CallStack kit ikit ≤ 2 ^ 64 →
      (∀ ans, kit.loadRel StoresGhost.opened.sessions peer.val ans → ans.isOk = true) →
      (∀ ans, ikit.trustRel StoresGhost.opened.identity peer.val remoteIdKey .receiving ans →
        ans = .ok true) →
      FitsEnv M lim st_b
        (StageP1OkEnv kit kitEnv StoresGhost.opened.sessions
          ikit ikitEnv StoresGhost.opened.identity peer.val remoteIdKey) →
      ∀ (s0 : State)
        (sp outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
         sessStorePtr idStorePtr
         preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
         kyberStorePtr kyberStoreVt rngPtr
         v_sp0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 : BitVec 64)
        (b_390 b_4f2 : BitVec 8),
        LibsignalCodeRoLoaded lsmpl s0.mem →
        s0.fs.files = F0 →
        s0.pc = dpPollEntryPlaced →
        s0.status = .Running →
        (s0.sp &&& 15#64 == 0#64) = true →
        s0.sp - 0xcd0#64 = sp →
        s0.readReg64 .x0 = outPtr →
        s0.readReg64 .x1 = coroPtr →
        s0.readReg64 .x2 = ctxPtr →
        SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
          (dpPollEntryPlaced + 0x868#64) s0
          (stageP1OkPreAt A lim st_b kit ikit StoresGhost.opened.sessions
            StoresGhost.opened.identity peer remoteIdKey s0
            sp coroPtr msgPtr remoteAddrPtr localAddrPtr
            sessStorePtr idStorePtr
            preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
            kyberStorePtr kyberStoreVt rngPtr
            v_sp0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 b_390 b_4f2)
          (stageP1OkPostAt A lim st_b scopeKit encodeRecord kit kitEnv ikit ikitEnv
            StoresGhost.opened.sessions StoresGhost.opened.identity
            peer remoteIdKey s0
            sp outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
            sessStorePtr idStorePtr
            preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
            kyberStorePtr kyberStoreVt rngPtr)
          (PanicOomProp s0)

/-- Budget-threaded counterpart of `StagesOverCliPlaced.overStageP1OkCli_of_trap`. -/
theorem overStageP1OkCli_of_trap [LibsignalPlacement]
    (h : StageP1OkTrapPlacedStmt) : OverStageP1OkCliPlacedStmt := by
  intro _M _A _lim _ReadEnv _DeserEnv mmpl gh W B F0 peer remoteIdKey
    _σ _kit _ikit _kitEnv _ikitEnv st_b hh hRead hDeser hp1_64 hload htrust hfits
    s0 sp outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
    sessStorePtr idStorePtr
    preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
    kyberStorePtr kyberStoreVt rngPtr
    v_sp0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0
    b_390 b_4f2
    hro0 hfiles0 hpc hrun hsp_align0 hsp_eq hx0 hx1 hx2
  exact h mmpl gh W B F0 peer remoteIdKey st_b
    StoresGhost.opened.sessions StoresGhost.opened.identity
    hh hRead hDeser hp1_64 rfl rfl hload htrust hfits
    s0 sp outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
    sessStorePtr idStorePtr
    preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
    kyberStorePtr kyberStoreVt rngPtr
    v_sp0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0
    b_390 b_4f2
    hro0 (cliPollStageP1_fsAt_placed (runHooks_of_stages hh) F0 scopeKit peer B hfiles0)
    hpc hrun hsp_align0 hsp_eq hx0 hx1 hx2

/-- Closed CLI instantiation of `OverStageP1OkCliPlacedStmt` from `hDropNz : lsmpl.base 547 ≠ 0#64`. -/
theorem overStageP1OkCli_placed_inst [LibsignalPlacement] (hDropNz : lsmpl.base 547 ≠ 0#64) :
    OverStageP1OkCliPlacedStmt :=
  overStageP1OkCli_of_trap (stageP1_ok_trap_placed_inst hDropNz)

/-- Budget-threaded counterpart of `Poll.OverClosureUntrustedD2cPlacedStmt` (`decPkDefD2c` / `DecPkOkD2c`
untrusted-identity branch on Block `518` under `[LibsignalPlacement]`). -/
def OverClosureUntrustedD2cPlacedStmt [LibsignalPlacement] : Prop :=
  ∀ {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop},
    lsmpl.base 547 ≠ 0#64 →
    ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
      (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
      (Scope : SessionRecord (List (BitVec 8)) → Prop),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym)
        (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv) →
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsmpl.base 46)
        (sessDeserializeSpecPlaced scopeKit A lim DeserEnv) →
      EncodeInjOn scopeKit →
      (∀ r, Scope r → scopeIn r) →
      S.decryptPrekey = decPkDefD2c X ⟨W.C, W.Q⟩ Scope →
      ∀ (stk' : Nat), dpPollNeed B ≤ stk' → stk' ≤ 2 ^ 63 →
      ∀ (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S)),
        FitsEnv M lim y.st (CliDpPollUntrustedEnv (A := A.repAlloc) B ReadEnv DeserEnv y.g) →
        (∀ evs,
          CliDpPollUntrustedEnv (A := A.repAlloc) B ReadEnv DeserEnv y.g evs → DecPkEnv y.g evs) →
        ∀ (R : SepProp) (s0 : State),
          s0.pc = dpPollEntryPlaced →
          s0.status = .Running →
          s0.spAligned = true →
          LibsignalCodeRoLoaded lsmpl s0.mem →
          s0.readReg64 .x0 = y.out →
          s0.readReg64 .x1 = y.fut →
          s0.readReg64 .x2 = y.cx →
          s0.fs.files = y.g.F →
          FilesOkPeer Scope y.g.F y.g.peer.val →
          DecPkOkD2c ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg →
          StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
            y.g.msg.identityKey = .ok false →
          (s0.mem ⊨
            memRegion y.out 48 ∗
            dpFutStartAt y.fut (dpSlotArgsPlaced y.g) ∗
            memRegion y.cx 32 ∗
            storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
            protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
            protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
            coinsInstalledPlaced y.g.coinsP y.g.coins ∗
            LsTokenInit ∗
            lsLogOff ∗
            A.pool lim y.st s0 ∗
            preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
            stackAt s0.sp stk' ∗
            R) →
          let prog := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))
          let K := dpSlotPollKStatePlaced A lim DecPkEnv B S
          ∃ P Fr : SepProp, (s0.mem ⊨ P ∗ Fr) ∧
            SepWPp prog (s0.readReg64 Reg.lr) s0 P
              (fun sf P_f =>
                (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ Fr) →
                  (sf.mem ⊨ (withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')).post y s0 sf ∗ R)) ∧
                  sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
              (fun sf P_f =>
                Steps prog s0 sf → (sf.mem ⊨ P_f ∗ Fr) →
                  (sf.mem ⊨ (withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')).onPanic y s0 sf ∗ R))

private theorem hookSat_sessionMemcpyRegionBudget_of_codec {H : LibsignalHooks}
    (h : HookSat H CryptoVerification.lsMemcpySym
      (LibsignalBinary.Heap.SpecBudget.withVmPreserved
        CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec)) :
    HookSat H CryptoVerification.lsMemcpySym
      LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionMemcpyRegionBudgetSpec :=
  ProofLib.HookSat.mono h fun x R _ hpre => ⟨x, R, hpre, fun _ hpost => hpost⟩

set_option maxHeartbeats 800000 in
/-- Budget-threaded counterpart of `StagesOverCliPlaced.closure_untrusted_d2c_trap_placed_ok`. -/
theorem closure_untrusted_d2c_trap_placed_ok [LibsignalPlacement]
    (hUntrusted : StageP1UntrustedMangledPlacedStmt) :
    OverClosureUntrustedD2cPlacedStmt := by
  intro M A lim ReadEnv DeserEnv DecPkEnv hDropNz mmpl gh W X B S Scope
    hh hRead hDeser hinjK hsub hS stk' hneed hstk63 y hfits_p1 hevs_sub R s0
    hpc hrun hsp hro0 hx0 hx1 hx2 hfiles0 hfPeer hdecOk htrusted hm_base
  dsimp only
  let σ := cliKitStk B
  let pid := pmPreKeyId y.g.msg
  let sid := y.g.msg.signedPreKeyId
  let kid := pmKyberId y.g.msg
  let kbk := y.g.msg.baseKey
  let kit := cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer σ
  let ikit := cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ
  let pkKit := cliPollPkKitPlaced A.repAlloc y.g.F pid σ
  let spkKit := cliPollSpkKitPlaced A.repAlloc y.g.F sid σ
  let kpkKit := cliPollKpkKitPlaced A.repAlloc y.g.F kid sid kbk σ
  let sp := s0.sp - 0xcd0#64
  have hent_stores := storesAt_opened_entails_cliPollStoresKitsAtPlaced_d2c A.repAlloc σ y.g.stores
    hsub hfPeer hdecOk pid sid kid kbk
  have hm_stores : s0.mem ⊨
      memRegion y.out 48 ∗
        dpFutStartAt y.fut (dpSlotArgsPlaced y.g) ∗
        memRegion y.cx 32 ∗
        cliPollStoresKitsAtPlaced A.repAlloc y.g.F scopeKit y.g.peer
          pid sid kid kbk σ y.g.stores StoresGhost.opened ∗
        protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
        protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
        coinsInstalledPlaced y.g.coinsP y.g.coins ∗
        LsTokenInit ∗
        lsLogOff ∗
        A.pool lim y.st s0 ∗
        preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
        stackAt s0.sp stk' ∗
        R :=
    Satisfies.mono (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left hent_stores)))) hm_base
  have hsub64 : dpClosSubStack B ≤ 2 ^ 64 := by
    have := dpPollNeed_eq_frame_add_subStack B; omega
  have hp1_le := stageP1UntrustedCallStack_le_subStack (A := A.repAlloc)
    0#64 y.g.F scopeKit y.g.peer B
  have hp1_64 : stageP1UntrustedCallStack kit ikit ≤ 2 ^ 64 := Nat.le_trans hp1_le hsub64
  rw [dpFutStartAt_split_for_p1_placed y.g y.fut,
      preKeyMsgAt_eq_idKey_sep A.repAlloc y.g.msgG y.g.msgA y.g.msg,
      stackAt_poll_entry_split s0.sp B stk' hneed hstk63,
      stackAt_subStack_split sp B (stageP1UntrustedCallStack kit ikit) hp1_le hsub64,
      clos_stack_3280_split_for_p1_untrusted s0.sp] at hm_stores
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm_stores
  rcases hm_stores with ⟨u_a8, u_b0, u_b8, u_c0, u_c8, u_d0, v_sp0,
    b_4f2, u_3a0, u_398, b_390, coins, hm_flat⟩
  dsimp only [cliPollStoresKitsAtPlaced] at hm_flat
  let P_p1 : SepProp :=
    decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt
      (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
      (y.g.stores + 0x78#64) kpkKit.kpk_vt coins ∗
    cells (y.fut + 0x70#64) 14 ∗
    cells (y.fut + 0xe0#64) 4 ∗
    memRegion (y.fut + 0x100#64) 336 ∗
    cells (y.fut + 0x250#64) 6 ∗
    ((y.fut + 0x2c0#64) ↦₈ 0#8) ∗
    cells (y.fut + 0x2c8#64) 25 ∗
    ((y.fut + 0x390#64) ↦₈ b_390) ∗
    ((y.fut + 0x398#64) ↦₆₄ u_398) ∗
    ((y.fut + 0x3a0#64) ↦₆₄ u_3a0) ∗
    (sp ↦₆₄ v_sp0) ∗
    ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
    ((sp + 0xb0#64) ↦₆₄ u_b0) ∗
    ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
    ((sp + 0xc0#64) ↦₆₄ u_c0) ∗
    ((sp + 0xc8#64) ↦₆₄ u_c8) ∗
    ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
    memRegion (sp + 0xd8#64) 348 ∗
    memRegion (sp + 0x370#64) 36 ∗
    memRegion (sp + 0x3e0#64) 368 ∗
    cells (sp + 0xa90#64) 6 ∗
    cells (s0.sp - 0x60#64) 12 ∗
    memRegion y.out 48 ∗
    lsLogOff ∗
    kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
    ikit.identityAt y.g.stores StoresGhost.opened.identity ∗
    protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
    ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
    A.pool lim y.st s0 ∗
    stackAt sp (stageP1UntrustedCallStack kit ikit)
  let Fr_inner : SepProp :=
    cells (y.fut + 0x428#64) 8 ∗
    cells (y.fut + 0x490#64) 4 ∗
    ((y.fut + 0x4f2#64) ↦₈ b_4f2) ∗
    coroUnusedP1At y.fut ∗
    closStackUnusedUntrustedAt sp ∗
    memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B))
      (dpClosSubStack B - stageP1UntrustedCallStack kit ikit) ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
    memRegion y.cx 32 ∗
    pkKit.storeAt (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
    spkKit.storeAt (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
    kpkKit.storeAt (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
    dirAt A.repAlloc (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
    protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
    preKeyMsgRemIdKeyAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
    coinsInstalledPlaced y.g.coinsP y.g.coins ∗
    LsTokenInit
  have hm_split : s0.mem ⊨ P_p1 ∗ (Fr_inner ∗ R) :=
    Satisfies.mono (by dsimp only [P_p1, Fr_inner, kit, ikit, pkKit, spkKit, kpkKit,
      cliPollSessKitPlaced, cliPollIdKitPlaced, cliPollPkKitPlaced, cliPollSpkKitPlaced,
      cliPollKpkKitPlaced, cliIdStoreSpecFullPlaced, cliPreKeyStoreSpecPlaced,
      cliSignedPreKeyStoreSpecPlaced, cliKpkStoreSpecFullPlaced,
      cliKyberPreKeyStoreSpecPlaced]; sep_frame) hm_flat
  refine ⟨P_p1, Fr_inner ∗ R, hm_split, ?_⟩
  have hwp := hUntrusted
    (M := M) (A := A) (lim := lim) (ext := cliGhostExterns gh (cliExternsPlaced mmpl W))
    (Scope := scopeKit) (encRecord := encodeRecord)
    (kit := kit)
    (kitEnv :=
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget.cliPollSessBudgetEnv
        A.repAlloc y.g.F y.g.peer B ReadEnv DeserEnv)
    (ikit := ikit)
    (ikitEnv :=
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget.cliPollIdBudgetEnv
        A.repAlloc y.g.F y.g.peer B ReadEnv)
    (st := StoresGhost.opened.sessions) (ist := StoresGhost.opened.identity)
    (st_b := y.st)
    y.g.peer y.g.msg.identityKey
    hh.alloc
    hh.codecHooks.dealloc
    ((show withVmPreserved noAllocShimSpec = sessionShimBudgetSpec from rfl) ▸ hh.codecHooks.shim)
    hh.codecHooks.alloc
    (hookSat_sessionMemcpyRegionBudget_of_codec hh.codecHooks.memcpy)
    (cliPollSess_vtablesPlacedOk (A := A.repAlloc) y.g.F scopeKit y.g.peer σ hDropNz)
    (cliPollId_vtablesPlacedOk (A := A.repAlloc) y.g.F y.g.peer σ hDropNz)
    (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget.cliPollSess_kitPlacedOkSE
      mmpl gh W hDropNz hh hRead hDeser)
    (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget.cliPollId_kitPlacedOkI
      mmpl gh W hDropNz hh hRead)
    hp1_64
    (by
      dsimp only [extHookStack, loadCallStack, kit, σ, cliPollSessKitPlaced, cliPollSessKit,
        cliSessionStoreSpec, cliKitStk,
        CryptoVerification.SignalSession.Cli.KitInst.SessKit.loadShimNeed,
        CryptoVerification.SignalSession.Cli.KitInst.SessKit.loadPollNeed,
        CryptoVerification.RustHeap.allocHookStack]
      omega)
    rfl rfl
    (fun _ (h : (cliPollSessKit A.repAlloc 0#64 y.g.F scopeKit y.g.peer σ).loadRel
      StoresGhost.opened.sessions y.g.peer.val _) => cliSess_loadRel_isOk h)
    (fun _ (h : (cliPollIdKit A.repAlloc 0#64 y.g.F y.g.peer σ).trustRel
      StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey .receiving _) =>
      cliId_trustRel_eq_of_trusted htrusted h)
    hfits_p1
    s0 sp y.out y.fut y.cx y.g.msgA y.g.peerA y.g.meA
    (y.g.stores + 0xf0#64) y.g.stores
    (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
    (y.g.stores + 0x78#64) kpkKit.kpk_vt coins
    v_sp0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 b_390
    hro0
    (cliPollStageP1_fsAt_placed hh y.g.F scopeKit y.g.peer B hfiles0)
    hpc hrun (by simpa [State.spAligned] using hsp) rfl hx0 hx1 hx2
  intro R' hm' hL
  obtain ⟨sf, hsteps_run, ⟨hpcf, hrunf, P_f, hmf', hq⟩ | ⟨_, _, _, hfalse⟩ | hoom⟩ := hwp R' hm' hL
  · refine ⟨sf, hsteps_run, Or.inl ⟨hpcf, hrunf, P_f, hmf', ?_⟩⟩
    rcases hq with ⟨⟨opt, evs, hevs_p1, hload, _, htr_evs, hent_f⟩, hspf, hcs, hvregs, _⟩
    refine ⟨?_, hspf, closureCalleeSaved_toCalleeSavedPreserved hcs hvregs⟩
    intro hsteps hmf
    have htr_eq : sf.trace = s0.trace := by
      simpa [kit, ikit, cliPollSessKitPlaced, cliPollIdKitPlaced, cliPollSessKit,
        cliSessionStoreSpec, cliIdStoreSpecFullPlaced, cliIdStoreSpecFull,
        cliIdentityStoreSpec] using htr_evs
    have hloadRec : loadRec Scope y.g.F y.g.peer.val = .ok opt :=
      loadRec_of_cliPollSessPlaced_loadRel hinjK hsub hfPeer hload
    have hans : S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins = some none := by
      rw [hS, decPkDefD2c_eq_decPkDef_of_untrusted X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val
        y.g.msg y.g.coins (by rw [htrusted]; decide)]
      exact decPkDef_of_trust_err X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val
        y.g.msg y.g.coins hloadRec (Or.inr htrusted)
    have hout : slotOutTr (S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins)
        StoresGhost.opened (.error (.untrustedIdentity y.g.peer.val)) s0.trace sf.trace :=
      slotOutTr_of_err StoresGhost.opened s0.trace sf.trace nofun nofun hans
    have hmf1 := Satisfies.mono (sepConj_mono_left hent_f) hmf
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hmf1
    rcases hmf1 with ⟨v_a8, v_b8, v_d0, hmf2⟩
    have hcoro := coro_of_p1_untrusted_entails_dpFutDoneAt y.fut y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt
      (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
      (y.g.stores + 0x78#64) kpkKit.kpk_vt coins b_4f2
    have hstk3280 := clos_stack_3280_of_p1_untrusted s0.sp s0
      0#64 v_a8 (y.fut + 0x390#64) v_b8 y.cx y.out v_d0
    have hres := apiDecResultAt_untrusted_entails_decResAt A.repAlloc y.out y.g.peer.val
    have hstores_back := cliPollStoresKitsAtPlaced_entails_storesAt (A := A.repAlloc)
      (F0 := y.g.F) (Scope := scopeKit) (peer := y.g.peer)
      (pid := pid) (sid := sid) (kid := kid) (kbk := kbk) σ y.g.stores StoresGhost.opened
    let Leftover : SepProp :=
      coinsInstalledPlaced y.g.coinsP y.g.coins ∗
      LsTokenInit
    have hmf_reord : sf.mem ⊨
        (apiDecResultAt A.repAlloc y.out (.error (.untrustedIdentity y.g.peer.val)) ∗
          cliPollStoresKitsAtPlaced A.repAlloc y.g.F scopeKit y.g.peer
            pid sid kid kbk σ y.g.stores StoresGhost.opened ∗
          protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
          protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
          (((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
            preKeyMsgRemIdKeyAt A.repAlloc y.g.msgG y.g.msgA y.g.msg) ∗
          lsLogOff ∗
          A.pool lim (M.stepEvents evs y.st) sf ∗
          Leftover ∗
          (decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
              (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt
              (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
              (y.g.stores + 0x78#64) kpkKit.kpk_vt coins ∗
            decryptPrekeyCoroCopyAt y.fut y.g.msgA y.g.peerA y.g.meA
              (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt
              (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
              (y.g.stores + 0x78#64) kpkKit.kpk_vt coins ∗
            memRegion (y.fut + 0xe0#64) 368 ∗
            cells (y.fut + 0x250#64) 6 ∗
            ((y.fut + 0x2c0#64) ↦₈ 1#8) ∗
            processPrekeyInnerInitAt y.fut y.g.msgA y.g.peerA y.g.meA
              y.g.stores ikit.id_vt (y.g.stores + 0xc8#64) pkKit.pk_vt
              (y.g.stores + 0x50#64) spkKit.spk_vt (y.g.stores + 0x78#64) kpkKit.kpk_vt ∗
            ((y.fut + 0x390#64) ↦₈ 1#8) ∗
            cells (y.fut + 0x398#64) 2 ∗
            cells (y.fut + 0x428#64) 8 ∗
            cells (y.fut + 0x490#64) 4 ∗
            ((y.fut + 0x4f2#64) ↦₈ b_4f2) ∗
            coroUnusedP1At y.fut) ∗
          memRegion y.cx 32 ∗
          (memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
            (memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B))
                (dpClosSubStack B - stageP1UntrustedCallStack kit ikit) ∗
              stackAt sp (stageP1UntrustedCallStack kit ikit)) ∗
            ((sp ↦₆₄ 0#64) ∗
              ((sp + 0xa8#64) ↦₆₄ v_a8) ∗
              ((sp + 0xb0#64) ↦₆₄ (y.fut + 0x390#64)) ∗
              ((sp + 0xb8#64) ↦₆₄ v_b8) ∗
              ((sp + 0xc0#64) ↦₆₄ y.cx) ∗
              ((sp + 0xc8#64) ↦₆₄ y.out) ∗
              ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
              memRegion (sp + 0xd8#64) 348 ∗
              memRegion (sp + 0x370#64) 36 ∗
              memRegion (sp + 0x3e0#64) 368 ∗
              cells (sp + 0xa90#64) 6 ∗
              decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
              closStackUnusedUntrustedAt sp))) ∗ R := by
      have htrust_id : ikit.trustUpdate StoresGhost.opened.identity y.g.peer.val
          y.g.msg.identityKey .receiving (.ok false) = StoresGhost.opened.identity := rfl
      rw [htrust_id] at hmf2
      dsimp only [Fr_inner] at hmf2
      refine Satisfies.mono ?_ hmf2
      dsimp only [Leftover, cliPollStoresKitsAtPlaced]
      sep_frame
    rw [← preKeyMsgAt_eq_idKey_sep A.repAlloc y.g.msgG y.g.msgA y.g.msg,
        ← stackAt_subStack_split sp B (stageP1UntrustedCallStack kit ikit) hp1_le hsub64,
        show sp + 0xcd0#64 = s0.sp from sp_frame_sub_add s0.sp] at hmf_reord
    have hmf_folded : sf.mem ⊨
        (decResAt A.repAlloc y.out (.error (.untrustedIdentity y.g.peer.val)) ∗
          storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
          protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
          protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
          preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
          lsLogOff ∗
          A.pool lim (M.stepEvents evs y.st) sf ∗
          Leftover ∗
          dpFutDoneAt y.fut ∗
          memRegion y.cx 32 ∗
          (memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
            stackAt sp (dpClosSubStack B) ∗
            memRegion sp 3280)) ∗ R :=
      Satisfies.mono (sepConj_mono_left
        (sepConj_mono hres
          (sepConj_mono hstores_back
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono hcoro
                  (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hstk3280)))))))))))))
        hmf_reord
    dsimp only [sp] at hmf_folded
    rw [← stackAt_poll_entry_split s0.sp B stk' hneed hstk63] at hmf_folded
    have hpost := dpPollPost_of_decResAt_placed A lim DecPkEnv B S stk' y s0 sf evs
      StoresGhost.opened (.error (.untrustedIdentity y.g.peer.val)) Leftover
      hh (hevs_sub evs hevs_p1) hsteps htr_eq hout
    exact Satisfies.mono (sepConj_mono_left hpost) hmf_folded
  · exact False.elim hfalse
  · exact ⟨sf, hsteps_run, Or.inr (Or.inr hoom)⟩

/-- Closed `decPkDefD2c` / `DecPkOkD2c` untrusted-identity branch (`trusted =.ok false`) on
Block `518` under `[LibsignalPlacement]`, discharging `StageP1UntrustedMangledPlacedStmt` directly
via `stageP1_untrusted_mangled_placed_ok`. -/
theorem closure_untrusted_d2c_placed_ok [LibsignalPlacement] :
    OverClosureUntrustedD2cPlacedStmt :=
  closure_untrusted_d2c_trap_placed_ok stageP1_untrusted_mangled_placed_ok

/-! ## `LibsignalFrozen` Variants -/

def OverClosureUntrustedD2cFrozenPlacedStmt [LibsignalPlacement] : Prop :=
  ∀ {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop},
    lsmpl.base 547 ≠ 0#64 →
    ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
      (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
      (Scope : SessionRecord (List (BitVec 8)) → Prop),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym)
        (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv) →
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsmpl.base 46)
        (sessDeserializeSpecPlaced scopeKit A lim DeserEnv) →
      EncodeInjOn scopeKit →
      (∀ r, Scope r → scopeIn r) →
      S.decryptPrekey = decPkDefD2c X ⟨W.C, W.Q⟩ Scope →
      ∀ (stk' : Nat), dpPollNeed B ≤ stk' → stk' ≤ 2 ^ 63 →
      ∀ (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S)),
        FitsEnv M lim y.st (CliDpPollUntrustedEnv (A := A.repAlloc) B ReadEnv DeserEnv y.g) →
        (∀ evs,
          CliDpPollUntrustedEnv (A := A.repAlloc) B ReadEnv DeserEnv y.g evs → DecPkEnv y.g evs) →
        ∀ (R : SepProp) (s0 : State),
          s0.pc = dpPollEntryPlaced →
          s0.status = .Running →
          s0.spAligned = true →
          CryptoVerification.LibsignalFrozen lsmpl s0.mem →
          s0.readReg64 .x0 = y.out →
          s0.readReg64 .x1 = y.fut →
          s0.readReg64 .x2 = y.cx →
          s0.fs.files = y.g.F →
          FilesOkPeer Scope y.g.F y.g.peer.val →
          DecPkOkD2c ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg →
          StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
            y.g.msg.identityKey = .ok false →
          (s0.mem ⊨
            memRegion y.out 48 ∗
            dpFutStartAt y.fut (dpSlotArgsPlaced y.g) ∗
            memRegion y.cx 32 ∗
            storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
            protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
            protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
            coinsInstalledPlaced y.g.coinsP y.g.coins ∗
            LsTokenInit ∗
            lsLogOff ∗
            A.pool lim y.st s0 ∗
            preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
            stackAt s0.sp stk' ∗
            R) →
          let prog := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))
          let K := dpSlotPollKStatePlaced A lim DecPkEnv B S
          ∃ P Fr : SepProp, (s0.mem ⊨ P ∗ Fr) ∧
            SepWPp prog (s0.readReg64 Reg.lr) s0 P
              (fun sf P_f =>
                (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ Fr) →
                  (sf.mem ⊨ (CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl (dpPollSpecStateBudget K stk')).post y s0 sf ∗ R)) ∧
                  sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
              (fun sf P_f =>
                Steps prog s0 sf → (sf.mem ⊨ P_f ∗ Fr) →
                  (sf.mem ⊨ (CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl (dpPollSpecStateBudget K stk')).onPanic y s0 sf ∗ R))

theorem closure_untrusted_d2c_trap_frozen_placed_ok [LibsignalPlacement]
    (hUntrusted : StageP1UntrustedMangledPlacedStmt) :
    OverClosureUntrustedD2cFrozenPlacedStmt := by
  intro M A lim ReadEnv DeserEnv DecPkEnv hDropNz mmpl gh W X B S Scope
    hh hRead hDeser hinjK hsub hS stk' hneed hstk63 y hfits_p1 hevs_sub R s0
    hpc hrun hsp hfr0 hx0 hx1 hx2 hfiles0 hfPeer hdecOk htrusted hm_base
  have hro0 : LibsignalCodeRoLoaded lsmpl s0.mem :=
    ⟨CryptoVerification.LibsignalCodeLoaded.of_codeLoaded hfr0.2, hfr0.1⟩
  exact closure_untrusted_d2c_trap_placed_ok hUntrusted A lim hDropNz mmpl gh W X B S Scope
    hh hRead hDeser hinjK hsub hS stk' hneed hstk63 y hfits_p1 hevs_sub R s0
    hpc hrun hsp hro0 hx0 hx1 hx2 hfiles0 hfPeer hdecOk htrusted hm_base

theorem closure_untrusted_d2c_frozen_placed_ok [LibsignalPlacement] :
    OverClosureUntrustedD2cFrozenPlacedStmt :=
  closure_untrusted_d2c_trap_frozen_placed_ok stageP1_untrusted_mangled_placed_ok

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.StagesOverCliPlacedBudget
