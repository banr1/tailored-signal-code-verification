/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonStage2OverPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonStage2V1RegErrPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOneRustAllocPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib
import ProofLib.SepLogic.WPp

/-!
# Fixed-`B` and `regErr` Stage-P2 Over Producers

Fixed-`B` and `regId = .error ()` (`regErr`) Stage-P2 Path C (`Over`,
`dpPollEntryPlaced + 0x0868#64 → +0x1778#64`) producers, together with the Block-`621`
`growOneVecU8` caller contract on `lsProg_51`.
-/

@[expose] public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonStage2OverRegErrPlacedBudgetFd

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option maxRecDepth 200000

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoGames.LibsignalSession (PublicKey ShaCompress SignalMessage)
open CryptoGames.LibsignalSessionApi (ApiError Session SessionRecord)
open CryptoVerification (
  LibsignalFrozen LibsignalFullPlacement LibsignalPlacement libsignalFrozen_of_keepsFrozen
  lsBlackBoxU8Sym lsHandleErrorSym lsProg_51 lsProg_75 lsmpl lsρ withLsCl
)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.RecordCodecs (
  IdentityKeyPair KyberPreKeyRecord PreKeyRecord SignedPreKeyRecord
)
open CryptoVerification.E2E (
  PreKeyMessageFields ResponderPreKeySecrets UnreachedPqxdhPrimitives
  acceptInput keyPairOf modelPrims toU8 vecU8
)
open CryptoVerification.E2E.Pqxdh.Initiator (
  AcceptKeysInput DRKey Primitives bytesToBv8 ofSignalPqxdhAcceptKeysInput ofSignalPqxdhDRKey
)
open CryptoVerification.E2E.Pqxdh.Initiator.Model (acceptKeys acceptKeys_ofSignalPqxdhPrimitives)
open CryptoVerification.E2E.Pqxdh.ResponderStore (clampBv8List_length)
open CryptoVerification.E2E.Pqxdh.ResponderCore (
  bytesToBv8_vecU8 ofSignalPqxdhPrimitives vecU8_length
)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (ClosureCalleeSaved)
open CryptoVerification.E2E.Record (encSession)
open CryptoVerification.E2E.Record.Serialization (CanonSession encSessionMem)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal RecordGhost preKeyMsgAt)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  FsAt FsFiles IdentitySelfStoreSpec KyberPreKeyStoreSpec LibsignalCodeRoLoaded
  PreKeyStoreSpec SignedPreKeyStoreSpec
)
open CryptoVerification.LibsignalTripleRatchet (noAllocShimSpec rootStack)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchetRepr (
  AddrGhost SessionGhost SignalMessageGhost protocolAddressAt signalMessageAt
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (
  OpkOkWitness SessionExtraRel coroOpkIdAtP4 hdrOpkIdBv? mkP2AcceptKeysInput opkOkEvs
  opkOkUpdate p1LoadedRecordAt stageP1ProgPlaced
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (
  clearPending stageP2OverV1CallStack4K stageP3Sub5ExtraPrePrev1
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.OverP2 (clearPendingGhost)
open CryptoVerification.SignalSession (
  CliHooks cliExternsPlaced lsRustAllocSymCli lsRustNoAllocShimSymCli lsRustReallocSymCli
)
open CryptoVerification.SignalSession.Cli (
  CliGhostHooks StoresGhost cliGhostExterns cliIdentityVtSym cliKyberPreKeyVtSym cliPreKeyVtSym
  cliSessionVtSym cliSignedPreKeyVtSym
)
open CryptoVerification.SignalSession.Cli.KitInst (
  cliKpk_getRel_error_iff cliPk_getRel_error_iff cliSpk_getRel_error_iff
)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo cliWrOk coinsInstalledPlaced storesAt)
open CryptoVerification.SignalSession.Cli.RunGlue (cliGhostExterns_other cliGhostExterns_shim)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.RunCompose (DecPkGhost RunSem decResAt)
open CryptoVerification.SignalSession.Cli.RunProofs (
  DecPkOkD2c DecPkOk₀ dpFutDoneAt pkStoreKeys pkToE? pmOfE
)
open CryptoVerification.SignalSession.Cli.RunProofs.DecPkS0 (SessMatchesPm)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (
  LsTokenInit StageP1PostRegs cliKitStk cliModelPrims_structural
  cliPollIdKitPlaced cliPollKpkKitPlaced cliPollKpk_vtablesPlacedOk
  cliPollPkKitPlaced cliPollPk_vtablesPlacedOk cliPollSelfKitPlaced cliPollSelf_kpRel_err_placed
  cliPollSelf_kpRel_ok_placed cliPollSelf_regIdRel_err_placed cliPollSelf_regIdRel_ok_placed
  cliPollSelf_vtablesPlacedOk cliPollSpkKitPlaced cliPollSpk_vtablesPlacedOk
  decPkDefD2c_pathC_accept_none decPkDefD2c_pathC_lookup_err distinctSid_of_decPkOk₀
  dpClosSubStack dpPollEntryPlaced dpPollProgPlaced entails_sepConj_anyHeap hdrOpkIdBv?_mkPathAHdr
  mkPathAHdr p2Over_cliPollKpk_getEvs_placed p2Over_cliPollPk_getEvs_placed
  p2Over_cliPollPk_opkOkEvs_placed p2Over_cliPollPk_opkOkUpdate_placed
  p2Over_cliPollSelf_kpEvs_placed p2Over_cliPollSelf_regIdEvs_placed
  p2Over_cliPollSpk_getEvs_placed pathAInitSession pathAInitState pathA_pm_typed
  pkStoreKeys_eq_none_of_kpk_err pkStoreKeys_eq_none_of_opk_err pkStoreKeys_eq_none_of_spk_err
  pqxdhAcceptErr_entails_decResAt_anyHeap_ext preKeyMsgAt_eq_base_idKey_sep
  preKeyMsgRemBaseIdKeyAt scope_of_loadRec_some sepWPp_conseq_pre sp_sub_576_ne_zero
  stageP2PostP1At stageP3CoroFrameAt stageP3StackFrameAt x29_eq_sp0_sub_60 x29_eq_sp_add_c70
)
open CryptoVerification.SignalSession.Cli.Slots (
  FilesOkPeer cliExternsPlaced_panic_handle_error loadRec scopeIn scopeKit
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (CliGhostAllocHooks)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (growOneVecU8BudgetSpec)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (
  BoxAllocEnv PreKeyStoreBudgetEnv
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKitBudget (
  SignedPreKeyStoreBudgetEnv
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget (
  KyberPreKeyStoreBudgetEnv
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentitySelfStoreKitBudget (
  IdentitySelfStoreBudgetEnv
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (
  IdentitySelfStoreKitPlacedOkI KyberPreKeyStoreKitPlacedOk PreKeyStoreKitPlacedOk
  SignedPreKeyStoreKitPlacedOk
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveAuxBudget (EncodeRawPreallocPlacedOkX)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedABudget (AcceptOptFieldsEnv)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2PurePlacedBudget (
  InitializeBobV1OptFieldsEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2V1PlacedBudget (
  P2Sub6Env P2V1Arm4Env P2V1Arm5EnvOfAcceptErr P2V1Arm6EnvOfBob
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsBudget (
  p2PromoteOverAtSpecWithEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsPlacedBudget (
  PromoteMatchingMissAtPlacedProp PromoteMatchingMissGenPlacedProp
  PromoteOverAtPlacedWithEnvProp PromoteOverGenPlacedWithEnvProp
  promoteMatchingMissAt_placed_of_gen promoteOverAt_placed_of_gen_withEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Mid3PlacedBudget (
  P2OverSub1To4Arm3Env P2OverSub1To4OkEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2V1PlacedBudget (
  P2OverSub6EnvOf P2OverV1Arm4Env P2OverV1Arm5EnvOfAcceptErr P2OverV1Arm6EnvOfBob
)
open LibsignalBinary.Proofs.Cli.E2E.V1.BobTailV1PlacedBudget (InitialStateMemInvPlacedOkOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget (InitialStateEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (
  CliGhostAllocHooks cliExternsPlaced_alloc_budget_sat cliExternsPlaced_realloc_budget_sat
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget (
  DpPollGhostStateBudget dpSlotPollKStatePlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget (
  RunHooksPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1BasePlacedBudget (
  cliPollKpk_getErr_entails_decResAt_anyHeap_placed
  cliPollPk_getErr_entails_decResAt_anyHeap_placed cliPollSelf_kpErr_entails_decResAt_err_placed
  cliPollSelf_regIdErr_entails_decResAt_err_placed
  cliPollSpk_getErr_entails_decResAt_anyHeap_placed cliPollStageP2_fsAt_stages_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1AgreePlacedBudget (
  cliPollKpk_wf_of_preKeysWf_placed cliPollPk_wf_of_preKeysWf_placed
  cliPollSpk_wf_of_preKeysWf_placed pathA_acceptInput_agree_placed sepWPp_with_steps
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1FoldsPlacedBudget (
  p2ErrFrame_fold_pathA_placed_rep
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonStage2OverPlacedBudgetFd (
  stageP2PathCOver_qpan_cli_archive_frozen_of_init75_and_kits
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonStage2PathAPlacedBudgetFd (
  cliInitBobErrOwnedFrozen4K_ok cliInitBobV1FrozenOkPlaced4K_of_init75
  cliStageP2BaseCalleesPlaced4K fitsEnv_step3 p2Sub1To4_opkWord_eq
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonStage2V1RegErrPlacedBudgetFd (
  stageP2OverV1KitsMemInvRegErrAtPlacedOfEnvProp
  stageP2_over_v1_kits_frozen_ext_defs_regErr_placed_ofEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4SpatialPlacedBudget (
  overGenP3Pre_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudgetAux (
  StageP2OverEnv StageP2OverErrPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverFoldsPlacedBudget (
  encSessionMem_clearPending_lt_32 p2Over_not_sessMatchesMsg p2Over_serBytes_len
  pathAInnerFramePlaced stageP2OverV1CallStack4K_le_subStack_placed
  stageP2_entry_unpack_pathCOver_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudget (
  CliPollStageP2Envs P2OverPathCErrEnvOf P2OverPathCOkEnvOf PromoteOverArchiveCanonSessEnv
  PromoteOverArchiveEnv cliPromoteMatchingMissGen_placed_ok cliPromoteOverGen_archive_placed_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudgetAux (
  P2OverPathCErrEnvAux PromoteOverArchiveCanonSessEnvLocal
  StageP2PathCOverQpanCliMemInvPlacedAtStmt cliStageP2ClosureHooksPlaced
  promoteOverArchiveEnv_eq_canon
)

/-! ## 1. Envelope Congruence & `{M} {A}`-Generic `growOneVecU8` Helper -/

private theorem p2OverPathCErrEnvOf_eq_aux [LibsignalPlacement] {A : RustAlloc}
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (B : RunBudgets)
    (BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop)
    (AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop)
    (kitEnvs : ∀ F0 peer spkId kpkId opkWord kbk,
      CliPollStageP2Envs (A := A) B F0 peer spkId kpkId opkWord kbk) :
    P2OverPathCErrEnvOf (A := A) X W B BobV1Env AcceptErrEnv kitEnvs =
      P2OverPathCErrEnvAux (A := A) X W B BobV1Env AcceptErrEnv
        (fun F0 peer spkId kpkId opkWord kbk => (kitEnvs F0 peer spkId kpkId opkWord kbk).selfEnv)
        (fun F0 peer spkId kpkId opkWord kbk => (kitEnvs F0 peer spkId kpkId opkWord kbk).spkEnv)
        (fun F0 peer spkId kpkId opkWord kbk => (kitEnvs F0 peer spkId kpkId opkWord kbk).kpkEnv)
        (fun F0 peer spkId kpkId opkWord kbk => (kitEnvs F0 peer spkId kpkId opkWord kbk).pkEnv) := by
  funext g r evs
  unfold P2OverPathCErrEnvOf P2OverPathCErrEnvAux
  rfl

private theorem promoteOverAtPlacedWithEnv_of_eq [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Env₁ Env₂ : SessionGhost → Session (List (BitVec 8)) → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    {coroPtr : BitVec 64} {g : RecordGhost}
    {recG : SessionGhost} {sess : Session (List (BitVec 8))}
    (hEq : Env₁ recG sess = Env₂ recG sess)
    (h : PromoteOverAtPlacedWithEnvProp M A lim Env₁ ext coroPtr g recG sess) :
    PromoteOverAtPlacedWithEnvProp M A lim Env₂ ext coroPtr g recG sess := by
  unfold PromoteOverAtPlacedWithEnvProp
    LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsBudget.PromoteOverAtPlacedWithEnvProp
    p2PromoteOverAtSpecWithEnv at h ⊢
  rwa [← hEq]

private theorem seqEnv_or_right {E1 A B : List AllocEvent → Prop} {evs : List AllocEvent}
    (h : SeqEnv E1 (fun e => A e ∨ B e) evs) :
    SeqEnv E1 A evs ∨ SeqEnv E1 B evs := by
  rcases h with h1 | ⟨e1, e2, heq, h1, hA | hB⟩
  · exact Or.inl (Or.inl h1)
  · exact Or.inl (Or.inr ⟨e1, e2, heq, h1, hA⟩)
  · exact Or.inr (Or.inr ⟨e1, e2, heq, h1, hB⟩)

private theorem p2OverSub6_or {Bob : List AllocEvent → Prop} {regBox : Nat}
    {regPoll PromTail : List AllocEvent → Prop} {evs : List AllocEvent}
    (h : SeqEnv Bob (P2OverSub6EnvOf regBox regPoll PromTail) evs) :
    SeqEnv Bob (P2Sub6Env regBox regPoll) evs ∨
      SeqEnv Bob (SeqEnv (BoxAllocEnv regBox) (SeqEnv regPoll PromTail)) evs := by
  rcases h with hBob | ⟨eBob, eRest, heq1, hBob, hSub6⟩
  · exact Or.inl (Or.inl hBob)
  · unfold P2OverSub6EnvOf at hSub6
    rcases hSub6 with hBox | ⟨eBox, e2, heq2, hBox, h2⟩
    · exact Or.inl (Or.inr ⟨eBob, eRest, heq1, hBob, Or.inl hBox⟩)
    · rcases seqEnv_or_right h2 with hFree | hProm
      · exact Or.inl (Or.inr ⟨eBob, eRest, heq1, hBob, Or.inr ⟨eBox, e2, heq2, hBox, hFree⟩⟩)
      · exact Or.inr (Or.inr ⟨eBob, eRest, heq1, hBob, Or.inr ⟨eBox, e2, heq2, hBox, hProm⟩⟩)

/-- `{M : AllocCostModel} {A : RustCliAllocBudget M}`-generic Block-`621` `growOneVecU8` caller
contract on `lsProg_51` from `CliGhostAllocHooks`. -/
theorem cliGrowOneVecU8_lsProg51_withLsCl_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim gh) :
    subroutine_ok (lsProg_51 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 621)
      (withLsCl lsmpl (growOneVecU8BudgetSpec M A lim)) :=
  LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOneRustAllocPlacedBudget.growOneVecU8_caller_withLsCl_ok
    (callerProg := lsProg_51 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (i := 51)
    ((show lsHandleErrorSym = CryptoVerification.SpqrV1.Alloc.spqrHandleErrorSym by decide) ▸
      ((cliGhostExterns_other gh (cliExternsPlaced mmpl W)
          (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide)).trans
        (cliExternsPlaced_panic_handle_error mmpl W)))
    ((show lsRustNoAllocShimSymCli =
          CryptoVerification.SpqrV1.Alloc.spqrRustNoAllocShimSym by decide) ▸
      (⟨ProofLib.hookNoop,
        (cliGhostExterns_shim gh _).trans (congrArg some hG.shim_eq),
        LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.noAllocShim_hookOk⟩ :
        HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W))
          lsRustNoAllocShimSymCli
          LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.noAllocShimSpec))
    ((show lsRustAllocSymCli = CryptoVerification.SpqrV1.Alloc.spqrRustAllocSym by decide) ▸
      cliExternsPlaced_alloc_budget_sat mmpl gh W hG)
    ((show lsRustReallocSymCli = CryptoVerification.SpqrV1.Alloc.spqrRustReallocSym by decide) ▸
      cliExternsPlaced_realloc_budget_sat mmpl gh W hG)

/-! ## 2. `regErr` Stage-P2 Path C Statement & Kit-Parametric CPS Producer -/

def StageP2PathCOverQpanCliRegErrMemInvPlacedAtStmt (Φ : Memory → Prop) [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PromEnv : SessionGhost → Session (List (BitVec 8)) → List AllocEvent → Prop)
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (B : RunBudgets)
    (P2OverErrEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop) : Prop :=
  ∀ (S : RunSem)
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S)),
    StoresGhost.opened.identity.regId cliIo.rd y.g.F = .error () →
    ∀ (st_b : M.σ)
    (g1 : StoresGhost)
    (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (s0 s1 : State) (sp rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (Q Qpan : State → SepProp → Prop),
    PromoteMatchingMissGenPlacedProp A.repAlloc (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
    PromoteOverGenPlacedWithEnvProp M A lim PromEnv (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
    RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
    FitsEnv M lim st_b (P2OverErrEnv y.g r) →
    y.g.coins.length < 2 ^ 63 →
    DecPkOk₀ ⟨W.C, W.Q⟩ (fun _ => False) y.g.F y.g.peer.val y.g.me.val y.g.msg →
    (∀ r', Scope r' → scopeIn r') →
    FilesOkPeer Scope y.g.F y.g.peer.val →
    r.currentSession = some sess →
    scopeIn r →
    ¬ SessMatchesPm sess y.g.msg →
    StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val y.g.msg.identityKey = .ok true →
    g1 = StoresGhost.opened →
    FsAt (fun f => f = y.g.F) True (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s1 →
    Φ s1.mem →
    s0.trace <+: s1.trace →
    s1.sp = sp →
    sp + 0xcd0#64 = s0.sp →
    dpClosSubStack B ≤ sp.toNat →
    s1.pc = dpPollEntryPlaced + 0x0868#64 →
    s1.status = .Running →
    (s1.sp &&& 15#64 == 0#64) = true →
    StageP1PostRegs s0 s1 sp y.fut y.g.msgA y.g.peerA y.g.meA
      y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
      (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
      (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) →
    (herr : ∀ sf Pf,
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s1 sf →
      sf.sp = s0.sp →
      ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      (∃ (err : ApiError AddrVal Unit) (evs : List AllocEvent),
        P2OverErrEnv y.g r evs ∧
        err ≠ .panic ∧
        err ≠ .store () ∧
        sf.trace = s1.trace ∧
        (∃ (m : PreKeyMessageFields) (i : SignalMessage),
          pkToE? y.g.msg = some m ∧
          SignalMessage.tryFrom protoSignalCodec m.inner = .ok i ∧
          y.g.msg = pmOfE m i ∧
          ((pkStoreKeys y.g.F m = none ∨
            StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .error () ∨
            StoresGhost.opened.identity.regId cliIo.rd y.g.F = .error ()) ∨
           (∃ (k : ResponderPreKeySecrets) (kp : IdentityKeyPair),
             pkStoreKeys y.g.F m = some k ∧
             StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp ∧
             ∀ reg : BitVec 32,
               SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
                 (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = none))) ∧
        (Pf ⊢
          dpFutDoneAt y.fut ∗
          memRegion sp 3280 ∗
          decResAt A.repAlloc y.out (.error err) ∗
          storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
          preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
          protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
          protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
          lsLogOff ∗
          A.pool lim (M.stepEvents evs st_b) sf ∗
          stackAt sp (dpClosSubStack B) ∗
          anyHeap)) →
      Q sf Pf) →
    SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s1
      (stageP2PostP1At (A.atState lim st_b s1) y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt scopeKit A.repAlloc y.fut (some r) ∗
       preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
       protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
       coinsInstalledPlaced y.g.coinsP y.g.coins ∗
       storesAt A.repAlloc y.g.stores g1 ∗
       LsTokenInit ∗
       lsLogOff ∗
       stackAt sp (dpClosSubStack B))
      Q Qpan

set_option maxHeartbeats 1600000 in
theorem stageP2PathCOver_qpan_cli_regErr_full_placed_at_of_init75_aux [LibsignalFullPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {PromEnv : SessionGhost → Session (List (BitVec 8)) → List AllocEvent → Prop}
    {PromSessEnv : Session (List (BitVec 8)) → List AllocEvent → Prop}
    (hPromEq : ∀ {recG : SessionGhost} {sess : Session (List (BitVec 8))},
      CanonSession recG sess → PromEnv recG sess = PromSessEnv sess)
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (B : RunBudgets)
    {selfEnvOf : ∀ (F0 : FsFiles) (peer : AddrGhost)
      (_spkId _kpkId _opkWord : BitVec 32) (_kbk : PublicKey),
      IdentitySelfStoreBudgetEnv (cliPollSelfKitPlaced A.repAlloc F0 peer (cliKitStk B))}
    {spkEnvOf : ∀ (F0 : FsFiles) (_peer : AddrGhost)
      (spkId _kpkId _opkWord : BitVec 32) (_kbk : PublicKey),
      SignedPreKeyStoreBudgetEnv (cliPollSpkKitPlaced A.repAlloc F0 spkId (cliKitStk B))}
    {kpkEnvOf : ∀ (F0 : FsFiles) (_peer : AddrGhost)
      (spkId kpkId _opkWord : BitVec 32) (kbk : PublicKey),
      KyberPreKeyStoreBudgetEnv (cliPollKpkKitPlaced A.repAlloc F0 kpkId spkId kbk (cliKitStk B))}
    {pkEnvOf : ∀ (F0 : FsFiles) (_peer : AddrGhost)
      (_spkId _kpkId opkWord : BitVec 32) (_kbk : PublicKey),
      PreKeyStoreBudgetEnv (cliPollPkKitPlaced A.repAlloc F0 opkWord (cliKitStk B))}
    {P2OverErrEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (hErrEnv : ∀ g r evs,
      P2OverPathCErrEnvAux X W B
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
        selfEnvOf spkEnvOf kpkEnvOf pkEnvOf g r evs →
      P2OverErrEnv g r evs)
    (hFitsErrOnly : ∀ st_b g r,
      StoresGhost.opened.identity.regId cliIo.rd g.F = .error () →
      FitsEnv M lim st_b (P2OverErrEnv g r) →
      FitsEnv M lim st_b
        (P2OverPathCErrEnvAux X W B
          (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
          (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
          selfEnvOf spkEnvOf kpkEnvOf pkEnvOf g r))
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hInit75 : InitialStateMemInvPlacedOkOfEnv M (LibsignalCodeRoLoaded lsmpl) A lim W.C.F
      (InitialStateEnv W.C.F) (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hSelfKit : ∀ (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      IdentitySelfStoreKitPlacedOkI A lim
        (cliPollIdKitPlaced A.repAlloc F0 peer (cliKitStk B))
        (cliPollSelfKitPlaced A.repAlloc F0 peer (cliKitStk B))
        (selfEnvOf F0 peer spkId kpkId opkWord kbk)
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hSpkKit : ∀ (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      SignedPreKeyStoreKitPlacedOk A lim
        (cliPollSpkKitPlaced A.repAlloc F0 spkId (cliKitStk B))
        (spkEnvOf F0 peer spkId kpkId opkWord kbk)
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hKpkKit : ∀ (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      KyberPreKeyStoreKitPlacedOk A lim
        (cliPollKpkKitPlaced A.repAlloc F0 kpkId spkId kbk (cliKitStk B))
        (kpkEnvOf F0 peer spkId kpkId opkWord kbk)
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hPkKit : ∀ (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      PreKeyStoreKitPlacedOk A lim
        (cliPollPkKitPlaced A.repAlloc F0 opkWord (cliKitStk B))
        (pkEnvOf F0 peer spkId kpkId opkWord kbk)
        (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    StageP2PathCOverQpanCliRegErrMemInvPlacedAtStmt (LibsignalFrozen lsmpl) A lim PromEnv X mmpl gh W B
      P2OverErrEnv := by
  unfold StageP2PathCOverQpanCliRegErrMemInvPlacedAtStmt
  intro S DecPkEnv Scope y hRegErr st_b g1 r sess s0 s1 sp rngPtr v_a8 v_b8 v_d0 Q Qpan
    hPromMiss hPromOver hh hfits hcoins hdec0 hScope hFok hcur hIn hnotMatch _htrust
    hg1 hfs1 hCode1 htr01 hsp1 hsp0 hsub hpc1 hrun1 halign1 hregs1 herr
  subst hg1
  rcases hregs1 with ⟨hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16,
    _, hx19, _, hx22, hx23, hx24, _, _, hx29, hvregs1⟩
  obtain ⟨m, i, _, hi, hpm, hpkToE⟩ := pathA_pm_typed hdec0
  have hfp_reg : s1.readReg64 .x29 = sp + 0xc70#64 := x29_eq_sp_add_c70 hsp0 hx29
  have hsp_align : (sp &&& 15#64 == 0#64) = true := by rw [← hsp1]; exact halign1
  have hfits0 : FitsEnv M lim st_b
      (StageP2OverEnv
        (P2OverPathCErrEnvAux X W B
          (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
          (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
          selfEnvOf spkEnvOf kpkEnvOf pkEnvOf)
        (fun _ _ _ => False) y.g r) :=
    fun evs hq => hFitsErrOnly st_b y.g r hRegErr hfits evs (hq.elim id False.elim)
  refine sepWPp_with_steps ?_
  refine sepWPp_conseq_pre
    (stageP2_entry_unpack_pathCOver_placed y r sess m i s0 sp (sp + 0xc70#64)
      rngPtr v_a8 v_b8 v_d0 hcur hpm rfl hdec0 hFok hScope) ?_
  refine SepWPp.exists_elim fun g => SepWPp.exists_elim fun recG =>
    SepWPp.exists_elim fun w => SepWPp.pure_left fun ⟨_hkit, _hgcur, hcanon, hctBuf_nz, hopkWord⟩ => ?_
  have hPromMissAt : PromoteMatchingMissAtPlacedProp A.repAlloc (cliGhostExterns gh (cliExternsPlaced mmpl W))
      y.fut g recG sess 4#8 (5#8 :: bytesToBv8 (mkPathAHdr m).ekAPk) :=
    promoteMatchingMissAt_placed_of_gen hPromMiss y.fut g recG sess 4#8
      (5#8 :: bytesToBv8 (mkPathAHdr m).ekAPk)
      (p2Over_not_sessMatchesMsg sess y.g.msg m i hpm hnotMatch) (p2Over_serBytes_len m)
  have hPromOverAt0 :=
    promoteOverAt_placed_of_gen_withEnv hPromOver y.fut g recG sess
      (encSessionMem_clearPending_lt_32 hIn hcur hcanon)
  have hPromOverAt : PromoteOverAtPlacedWithEnvProp M A lim
      (fun _ s => PromSessEnv s) (cliGhostExterns gh (cliExternsPlaced mmpl W)) y.fut g recG sess :=
    promoteOverAtPlacedWithEnv_of_eq (hPromEq hcanon) hPromOverAt0
  let opkWord0 : BitVec 32 := m.opkId.getD 0#32
  have ⟨hArm3_eq, hOk14_eq⟩ := p2Sub1To4_opkWord_eq
    (spkBox := (cliPollSpkKitPlaced A.repAlloc y.g.F m.spkId (cliKitStk B)).getBoxSize)
    (spkPoll := (spkEnvOf y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey).getPollEnv
      StoresGhost.opened.signed m.spkId)
    (kpkBox := (cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B)).getBoxSize)
    (kpkPoll := (kpkEnvOf y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey).getPollEnv
      StoresGhost.opened.kyber m.kpkId)
    (pkBox1 := (cliPollPkKitPlaced A.repAlloc y.g.F w.opkWord (cliKitStk B)).getBoxSize)
    (pkBox2 := (cliPollPkKitPlaced A.repAlloc y.g.F opkWord0 (cliKitStk B)).getBoxSize)
    (pkPoll1 := (pkEnvOf y.g.F y.g.peer m.spkId m.kpkId w.opkWord y.g.msg.baseKey).getPollEnv
      StoresGhost.opened.oneTime)
    (pkPoll2 := (pkEnvOf y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey).getPollEnv
      StoresGhost.opened.oneTime)
    (kpBox := (cliPollSelfKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)).kpBoxSize)
    (m := m) (opkWord := w.opkWord) hopkWord (fun hw => by rw [hw]) (fun hw => by rw [hw])
  let ikBSk : SignalPqxdh.Bytes :=
    match StoresGhost.opened.identity.keyPair cliIo.rd y.g.F with
    | .ok kp₀ => vecU8 kp₀.privateKey.bytes | .error _ => List.replicate 32 0
  let ikBPk : SignalPqxdh.Bytes :=
    match StoresGhost.opened.identity.keyPair cliIo.rd y.g.F with
    | .ok kp₀ => vecU8 kp₀.identityKey.publicKey.bytes | .error _ => List.replicate 32 0
  have hikBSk_len : ikBSk.length = 32 := by dsimp only [ikBSk]; split <;> [exact vecU8_length _; simp]
  have hikBPk_len : ikBPk.length = 32 := by dsimp only [ikBPk]; split <;> [exact vecU8_length _; simp]
  have hkp_sk : ∀ kp : IdentityKeyPair,
      (cliPollSelfKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)).kpRel
        StoresGhost.opened.identity (.ok kp) → kp.privateKey.bytes.toList = bytesToBv8 ikBSk := by
    intro kp hrel; dsimp only [ikBSk]; rw [cliPollSelf_kpRel_ok_placed hrel, bytesToBv8_vecU8]
  have hkp_pk : ∀ kp : IdentityKeyPair,
      (cliPollSelfKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)).kpRel
        StoresGhost.opened.identity (.ok kp) →
      kp.identityKey.publicKey.bytes.toList = bytesToBv8 ikBPk := by
    intro kp hrel; dsimp only [ikBPk]; rw [cliPollSelf_kpRel_ok_placed hrel, bytesToBv8_vecU8]
  let err0 : ApiError AddrVal Unit := .protocol .invalidKeyAgreement
  have herr0_p : err0 ≠ .panic := by nofun
  have herr0_s : err0 ≠ .store () := by nofun
  have hStageP2 :
      stageP2OverV1KitsMemInvRegErrAtPlacedOfEnvProp
        (LibsignalFrozen lsmpl)
        (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) A lim W.C.F
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
        (fun _ s => PromSessEnv s)
        (cliGhostExterns gh (cliExternsPlaced mmpl W))
        (cliPollSelfKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
        (selfEnvOf y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey)
        (cliPollSpkKitPlaced A.repAlloc y.g.F m.spkId (cliKitStk B))
        (spkEnvOf y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey)
        (cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
        (kpkEnvOf y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey)
        (cliPollPkKitPlaced A.repAlloc y.g.F w.opkWord (cliKitStk B))
        (pkEnvOf y.g.F y.g.peer m.spkId m.kpkId w.opkWord y.g.msg.baseKey)
        (dpClosSubStack B) :=
    stageP2_over_v1_kits_frozen_ext_defs_regErr_placed_ofEnv
      (M := M)
      (P := ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) (A := A) (lim := lim) (F := W.C.F)
      (BobV1Env := InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
      (AcceptErrEnv := AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
      (PromEnv := fun _ s => PromSessEnv s)
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) (cliModelPrims_structural X W)
      (cliStageP2ClosureHooksPlaced mmpl gh W hh)
      (cliStageP2BaseCalleesPlaced4K mmpl gh W hh)
      (cliInitBobErrOwnedFrozen4K_ok X mmpl gh W hG hh)
      (cliInitBobV1FrozenOkPlaced4K_of_init75 X mmpl gh W hG hh hInit75)
      (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
      (cliPollSelfKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
      (selfEnvOf y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey)
      (cliPollSelf_vtablesPlacedOk y.g.F y.g.peer (cliKitStk B) hDropNz)
      (hSelfKit y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey hh)
      (cliPollSpkKitPlaced A.repAlloc y.g.F m.spkId (cliKitStk B))
      (spkEnvOf y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey)
      (cliPollSpk_vtablesPlacedOk y.g.F m.spkId (cliKitStk B) hDropNz)
      (hSpkKit y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey hh)
      (cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
      (kpkEnvOf y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey)
      (cliPollKpk_vtablesPlacedOk y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B) hDropNz)
      (hKpkKit y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey hh)
      (cliPollPkKitPlaced A.repAlloc y.g.F w.opkWord (cliKitStk B))
      (pkEnvOf y.g.F y.g.peer m.spkId m.kpkId w.opkWord y.g.msg.baseKey)
      (cliPollPk_vtablesPlacedOk y.g.F w.opkWord (cliKitStk B) hDropNz)
      (hPkKit y.g.F y.g.peer m.spkId m.kpkId w.opkWord y.g.msg.baseKey hh)
      (dpClosSubStack B) (stageP2OverV1CallStack4K_le_subStack_placed (A := A.repAlloc)
        y.g.F y.g.peer m.spkId m.kpkId w.opkWord y.g.msg.baseKey B)
  exact hStageP2 (st := st_b)
    (Qp := fun sf Pf => Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s1 sf → Qpan sf Pf)
    s0 s1 (pathAInnerFramePlaced A.repAlloc y m i rngPtr sp)
    (fun sf Pf => Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s1 sf → Q sf Pf)
    sp (sp + 0xc70#64) y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
    y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x50#64) (y.g.stores + 0x78#64)
    y.g.peerA (y.g.msgA + 0xc8#64) w.u_488 w.u_80 w.u_88 w.u_90 v_a8 v_b8 v_d0
    (mkPathAHdr m) ikBSk ikBPk i.messageVersion 0#8 0#8 w.b_4b0 w.b_4f1 0#8
    w.opkWord m.kpkId m.regId m.spkId StoresGhost.opened.signed StoresGhost.opened.kyber
    StoresGhost.opened.oneTime StoresGhost.opened.identity y.g.me y.g.peer g recG sess
    hPromMissAt
    (fun localRegId hrel => by
      have hok_reg := cliPollSelf_regIdRel_ok_placed hrel
      rw [hRegErr] at hok_reg; cases hok_reg)
    hPromOverAt
    (hfits0.mono fun evs hevs => by
      refine Or.inl ?_; unfold P2OverPathCErrEnvAux; rw [hpkToE]
      rcases hevs with h1 | h2 | h3 | hok4
      · exact Or.inl h1
      · exact Or.inr (Or.inl h2)
      · rw [hArm3_eq] at h3; exact Or.inr (Or.inr (Or.inl h3))
      · rw [hOk14_eq] at hok4; exact Or.inr (Or.inr (Or.inr (Or.inl (SeqEnv.inl hok4)))))
    (fun evs14 hevs14 => by
      dsimp only [P2OverSub1To4OkEnv] at hevs14; rw [hOk14_eq] at hevs14
      have hArm4 : FitsEnv M lim st_b (P2OverV1Arm4Env
          (cliPollSpkKitPlaced A.repAlloc y.g.F m.spkId (cliKitStk B)).getBoxSize
          ((spkEnvOf y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey).getPollEnv
            StoresGhost.opened.signed m.spkId)
          (cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B)).getBoxSize
          ((kpkEnvOf y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey).getPollEnv
            StoresGhost.opened.kyber m.kpkId)
          (cliPollPkKitPlaced A.repAlloc y.g.F opkWord0 (cliKitStk B)).getBoxSize
          ((pkEnvOf y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey).getPollEnv
            StoresGhost.opened.oneTime)
          (cliPollSelfKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)).kpBoxSize
          (hdrOpkIdBv? (mkPathAHdr m))
          ((selfEnvOf y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey).kpPollEnv
            StoresGhost.opened.identity)) :=
        hfits0.mono fun evs h4 => by
          refine Or.inl ?_; unfold P2OverPathCErrEnvAux; rw [hpkToE]
          exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
      exact hArm4.seq_right hevs14)
    (fun spkRec _spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes
        wOpk opkPkBytes opkSkBytes kp drKey evs14 evsKp
        hspkRel _ _ _ hspkPubEq hspkPrivEq hkpkRel _ _ _ hkpkPubEq hkpkPrivEq
        hopkOk _ _ hopkBytes hkpRel haccSome hevs14 hevsKp => by
      dsimp only [P2OverSub1To4OkEnv] at hevs14; rw [hOk14_eq] at hevs14
      have hkpOk := cliPollSelf_kpRel_ok_placed hkpRel
      have hikBSk_ok : ikBSk = vecU8 kp.privateKey.bytes := by dsimp only [ikBSk]; rw [hkpOk]
      have hikBPk_ok : ikBPk = vecU8 kp.identityKey.publicKey.bytes := by dsimp only [ikBPk]; rw [hkpOk]
      obtain ⟨k, hk, _, _, hinp⟩ := pathA_acceptInput_agree_placed hdec0 hspkRel hspkPubEq hspkPrivEq
        hkpkRel hkpkPubEq hkpkPrivEq hopkOk hopkBytes hkpOk hikBSk_ok hikBPk_ok
      have hinp0 := hinp 0#32; rw [hinp0] at haccSome ⊢
      refine fitsEnv_step3 (hfits0.mono fun evs hseq => ?_)
        hevs14 hevsKp (FreeOnlyEvs.singleton 8 _)
      rcases hseq with h14 | ⟨e14, er1, heq1, h14, hr1⟩
      · refine Or.inl ?_; unfold P2OverPathCErrEnvAux; rw [hpkToE]
        exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl h14))))
      · rcases hr1 with hkp | ⟨eKp, er2, heq2, hkp, hr2⟩
        · refine Or.inl ?_; unfold P2OverPathCErrEnvAux; rw [hpkToE]
          exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr ⟨e14, er1, heq1, h14, Or.inl hkp⟩))))
        · rcases hr2 with hfr | ⟨eFr, er3, heq3, hfr, hr3⟩
          · refine Or.inl ?_; unfold P2OverPathCErrEnvAux; rw [hpkToE]
            exact Or.inr (Or.inr (Or.inr (Or.inl
              (Or.inr ⟨e14, er1, heq1, h14, Or.inr ⟨eKp, er2, heq2, hkp, hfr⟩⟩))))
          · rcases p2OverSub6_or hr3 with hArm6 | hOk
            · refine Or.inl ?_; unfold P2OverPathCErrEnvAux; rw [hpkToE]; dsimp only
              rw [hk, hkpOk]; dsimp only; rw [haccSome]
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e14, er1, heq1, h14,
                Or.inr ⟨eKp, er2, heq2, hkp, Or.inr ⟨eFr, er3, heq3, hfr, hArm6⟩⟩⟩)))))
            · refine Or.inl ?_; unfold P2OverPathCErrEnvAux; rw [hpkToE]; dsimp only
              rw [hk, hkpOk]; dsimp only; rw [haccSome]
              refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e14, er1, heq1, h14,
                Or.inr ⟨eKp, er2, heq2, hkp, Or.inr ⟨eFr, er3, heq3, hfr, ?_⟩⟩⟩)))))
              rcases hOk with hBob | ⟨eBob, eRest, heq4, hBob, hBox | ⟨eBox, e2, heq5, hBox, hReg | ⟨_, _, _, _, hFalse⟩⟩⟩
              · exact Or.inl hBob
              · exact Or.inr ⟨eBob, eRest, heq4, hBob, Or.inl hBox⟩
              · exact Or.inr ⟨eBob, eRest, heq4, hBob, Or.inr ⟨eBox, e2, heq5, hBox, Or.inl hReg⟩⟩
              · nomatch hFalse)
    (fun spkRec _spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes
        wOpk opkPkBytes opkSkBytes kp evs14 evsKp
        hspkRel _ _ _ hspkPubEq hspkPrivEq hkpkRel _ _ _ hkpkPubEq hkpkPrivEq
        hopkOk _ _ hopkBytes hkpRel _haccNone hevs14 hevsKp => by
      dsimp only [P2OverSub1To4OkEnv] at hevs14; rw [hOk14_eq] at hevs14
      have hkpOk := cliPollSelf_kpRel_ok_placed hkpRel
      have hikBSk_ok : ikBSk = vecU8 kp.privateKey.bytes := by dsimp only [ikBSk]; rw [hkpOk]
      have hikBPk_ok : ikBPk = vecU8 kp.identityKey.publicKey.bytes := by dsimp only [ikBPk]; rw [hkpOk]
      obtain ⟨k, hk, _, _, hinp⟩ := pathA_acceptInput_agree_placed hdec0 hspkRel hspkPubEq hspkPrivEq
        hkpkRel hkpkPubEq hkpkPrivEq hopkOk hopkBytes hkpOk hikBSk_ok hikBPk_ok
      rw [hinp 0#32]
      refine fitsEnv_step3 (hfits0.mono fun evs h5 => ?_) hevs14 hevsKp (FreeOnlyEvs.singleton 8 _)
      refine Or.inl ?_; unfold P2OverPathCErrEnvAux; rw [hpkToE]; dsimp only
      rw [hk, hkpOk]; dsimp only; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5)))))
    hctBuf_nz (sp_sub_576_ne_zero B hsub) hsub hikBSk_len hikBPk_len
    (vecU8_length m.idPub) (vecU8_length m.baseKey) (vecU8_length m.kyberCt) hCode1
    (cliPollStageP2_fsAt_stages_placed hh y.g.F y.g.peer m.spkId m.kpkId w.opkWord y.g.msg.baseKey B hfs1)
    rfl (fun r' hrel _ => cliPollSpk_wf_of_preKeysWf_placed hdec0.preKeysWf r' hrel)
    rfl (fun r' hrel _ => cliPollKpk_wf_of_preKeysWf_placed hdec0.preKeysWf r' hrel)
    (fun id hid => hopkWord id ((hdrOpkIdBv?_mkPathAHdr m).symm.trans hid))
    (fun id hid => hopkWord id ((hdrOpkIdBv?_mkPathAHdr m).symm.trans hid) |>.symm)
    (fun _id r' _ hrel _ => cliPollPk_wf_of_preKeysWf_placed hdec0.preKeysWf r' hrel)
    hkp_sk hkp_pk (Or.inr (distinctSid_of_decPkOk₀ hdec0))
    hpc1 hrun1 hsp1 hsp_align htr01 hvregs1
    hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24 hfp_reg
    (fun e sf Pf evs hspkErr hevs hpc_f hrun_f htr_f hsp_f hcs_f hvregs_f hinv_f hPf hSteps => by
      rw [p2Over_cliPollSpk_getEvs_placed, List.append_nil] at htr_f
      have hspkNone : pkStoreKeys y.g.F m = none := pkStoreKeys_eq_none_of_spk_err
        ((cliSpk_getRel_error_iff (A := A.repAlloc) (b := 0#64) cliIo.rd y.g.F cliWrOk m.spkId
          (cliKitStk B).spkGetShim (cliKitStk B).spkGetPoll
          StoresGhost.opened.signed m.spkId).mp ⟨e, hspkErr⟩)
      have hevs' : P2OverErrEnv y.g r evs := hErrEnv y.g r evs (by
        unfold P2OverPathCErrEnvAux; rw [hpkToE]; exact Or.inl hevs)
      have hpost := Entails.trans hPf (Entails.trans
        (sepConj_mono_left (cliPollSpk_getErr_entails_decResAt_anyHeap_placed A.repAlloc
          y.g.F m.spkId (cliKitStk B) y.out e err0))
        (p2ErrFrame_fold_pathA_placed_rep y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpm rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, evs, hevs', herr0_p, herr0_s, htr_f,
          ⟨m, i, hpkToE, hi, hpm, Or.inl (Or.inl hspkNone)⟩, hpost⟩)
    (fun _spkRec e sf Pf evs _ _ hkpkErr hevs hpc_f hrun_f htr_f hsp_f
        hcs_f hvregs_f hinv_f hPf hSteps => by
      rw [p2Over_cliPollSpk_getEvs_placed, p2Over_cliPollKpk_getEvs_placed,
          List.append_nil, List.append_nil] at htr_f
      have hkpkNone : pkStoreKeys y.g.F m = none := pkStoreKeys_eq_none_of_kpk_err
        ((cliKpk_getRel_error_iff (A := A.repAlloc) cliIo.rd y.g.F cliWrOk m.kpkId
          StoresGhost.opened.kyber m.kpkId).mp ⟨e, hkpkErr⟩)
      have hevs' : P2OverErrEnv y.g r evs := hErrEnv y.g r evs (by
        unfold P2OverPathCErrEnvAux; rw [hpkToE]; exact Or.inr (Or.inl hevs))
      have hpost := Entails.trans hPf (Entails.trans
        (sepConj_mono_left (cliPollKpk_getErr_entails_decResAt_anyHeap_placed A.repAlloc
          y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B) y.out e err0))
        (p2ErrFrame_fold_pathA_placed_rep y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpm rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, evs, hevs', herr0_p, herr0_s, htr_f,
          ⟨m, i, hpkToE, hi, hpm, Or.inl (Or.inl hkpkNone)⟩, hpost⟩)
    (fun _spkRec _kpkRec opkId e sf Pf evs _ _ _ _ hopkHdr hpkErr hevs hpc_f hrun_f htr_f hsp_f
        hcs_f hvregs_f hinv_f hPf hSteps => by
      rw [p2Over_cliPollSpk_getEvs_placed, p2Over_cliPollKpk_getEvs_placed,
          p2Over_cliPollPk_getEvs_placed, List.append_nil, List.append_nil, List.append_nil] at htr_f
      dsimp only [P2OverSub1To4Arm3Env] at hevs; rw [hArm3_eq] at hevs
      have hmOpk : m.opkId = some opkId := (hdrOpkIdBv?_mkPathAHdr m).symm.trans hopkHdr
      have hpkNone : pkStoreKeys y.g.F m = none := pkStoreKeys_eq_none_of_opk_err hmOpk
        ((cliPk_getRel_error_iff (A := A.repAlloc) (b := 0#64) cliIo.rd y.g.F cliWrOk w.opkWord
          (cliKitStk B).pkGetShim (cliKitStk B).pkGetPoll
          (cliKitStk B).pkRemoveShim (cliKitStk B).pkRemovePoll
          StoresGhost.opened.oneTime opkId).mp ⟨e, hpkErr⟩)
      have hevs' : P2OverErrEnv y.g r evs := hErrEnv y.g r evs (by
        unfold P2OverPathCErrEnvAux; rw [hpkToE]; exact Or.inr (Or.inr (Or.inl hevs)))
      have hpost := Entails.trans hPf (Entails.trans
        (sepConj_mono_left (cliPollPk_getErr_entails_decResAt_anyHeap_placed A.repAlloc
          y.g.F w.opkWord (cliKitStk B) y.out e err0))
        (p2ErrFrame_fold_pathA_placed_rep y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpm rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, evs, hevs', herr0_p, herr0_s, htr_f,
          ⟨m, i, hpkToE, hi, hpm, Or.inl (Or.inl hpkNone)⟩, hpost⟩)
    (fun _spkRec _kpkRec wOpk e sf Pf evs _ _ _ _ _ hkpErr hevs hpc_f hrun_f htr_f hsp_f
        hcs_f hvregs_f hinv_f hPf hSteps => by
      rw [p2Over_cliPollSpk_getEvs_placed, p2Over_cliPollKpk_getEvs_placed,
          p2Over_cliPollPk_opkOkEvs_placed, p2Over_cliPollSelf_kpEvs_placed,
          List.append_nil, List.append_nil, List.append_nil, List.append_nil] at htr_f
      have hopkUpd := p2Over_cliPollPk_opkOkUpdate_placed A.repAlloc y.g.F w.opkWord (cliKitStk B)
        (hdrOpkIdBv? (mkPathAHdr m)) wOpk
      rw [hopkUpd] at hPf
      unfold P2OverV1Arm4Env P2V1Arm4Env at hevs; rw [hOk14_eq] at hevs
      have hkpNone := cliPollSelf_kpRel_err_placed hkpErr
      have hevs' : P2OverErrEnv y.g r evs := hErrEnv y.g r evs (by
        unfold P2OverPathCErrEnvAux; rw [hpkToE]; exact Or.inr (Or.inr (Or.inr (Or.inl hevs))))
      have hpost := Entails.trans hPf (Entails.trans
        (sepConj_mono_left (Entails.trans
          (cliPollSelf_kpErr_entails_decResAt_err_placed A.repAlloc
            y.g.F y.g.peer (cliKitStk B) y.out e err0)
          (entails_sepConj_anyHeap _)))
        (p2ErrFrame_fold_pathA_placed_rep y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpm rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, evs, hevs', herr0_p, herr0_s, htr_f,
          ⟨m, i, hpkToE, hi, hpm, Or.inl (Or.inr (Or.inl hkpNone))⟩, hpost⟩)
    (fun spkRec _spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes
        wOpk opkPkBytes opkSkBytes kp errTag w2 w3 w4 w5 w6 sf Pf evs
        hspkRel _ _ _ hspkPubEq hspkPrivEq hkpkRel _ _ _ hkpkPubEq hkpkPrivEq
        hopkOk _ _ hopkBytes hkpRel haccNone hevs _ _
        hpc_f hrun_f htr_f hsp_f hcs_f hvregs_f hinv_f hPf hSteps => by
      rw [p2Over_cliPollSpk_getEvs_placed, p2Over_cliPollKpk_getEvs_placed,
          p2Over_cliPollPk_opkOkEvs_placed, p2Over_cliPollSelf_kpEvs_placed,
          List.append_nil, List.append_nil, List.append_nil, List.append_nil] at htr_f
      have hopkUpd := p2Over_cliPollPk_opkOkUpdate_placed A.repAlloc y.g.F w.opkWord (cliKitStk B)
        (hdrOpkIdBv? (mkPathAHdr m)) wOpk
      rw [hopkUpd] at hPf
      have hkpOk := cliPollSelf_kpRel_ok_placed hkpRel
      have hikBSk_ok : ikBSk = vecU8 kp.privateKey.bytes := by dsimp only [ikBSk]; rw [hkpOk]
      have hikBPk_ok : ikBPk = vecU8 kp.identityKey.publicKey.bytes := by dsimp only [ikBPk]; rw [hkpOk]
      obtain ⟨k, hk, _, _, hinp⟩ := pathA_acceptInput_agree_placed hdec0 hspkRel hspkPubEq hspkPrivEq
        hkpkRel hkpkPubEq hkpkPrivEq hopkOk hopkBytes hkpOk hikBSk_ok hikBPk_ok
      have haccNone0 : ∀ reg : BitVec 32, SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
          (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = none := fun reg =>
        Option.map_eq_none_iff.mp (by
          rw [← acceptKeys_ofSignalPqxdhPrimitives, ← hinp reg]; exact haccNone)
      unfold P2OverV1Arm5EnvOfAcceptErr P2V1Arm5EnvOfAcceptErr at hevs
      rw [hOk14_eq, hinp 0#32] at hevs
      have hevs' : P2OverErrEnv y.g r evs := hErrEnv y.g r evs (by
        unfold P2OverPathCErrEnvAux; rw [hpkToE]; dsimp only; rw [hk, hkpOk]; dsimp only
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hevs)))))
      have hPf' := Entails.trans hPf (by rw [← sepConj_assoc]; exact Entails.refl _)
      have hpost := Entails.trans hPf' (Entails.trans
        (sepConj_mono_left (pqxdhAcceptErr_entails_decResAt_anyHeap_ext A.repAlloc
          y.out errTag w2 w3 w4 w5 w6 err0))
        (p2ErrFrame_fold_pathA_placed_rep y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpm rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, evs, hevs', herr0_p, herr0_s, htr_f,
          ⟨m, i, hpkToE, hi, hpm, Or.inr ⟨k, kp, hk, hkpOk, haccNone0⟩⟩, hpost⟩)
    (fun spkRec _spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes
        wOpk opkPkBytes opkSkBytes kp drKey e sf Pf evs
        hspkRel _ _ _ hspkPubEq hspkPrivEq hkpkRel _ _ _ hkpkPubEq hkpkPrivEq
        hopkOk _ _ hopkBytes hkpRel haccSome hregErr hevs
        hpc_f hrun_f htr_f hsp_f hcs_f hvregs_f hinv_f hPf hSteps => by
      rw [p2Over_cliPollSpk_getEvs_placed, p2Over_cliPollKpk_getEvs_placed,
          p2Over_cliPollPk_opkOkEvs_placed, p2Over_cliPollSelf_kpEvs_placed,
          p2Over_cliPollSelf_regIdEvs_placed,
          List.append_nil, List.append_nil, List.append_nil, List.append_nil, List.append_nil] at htr_f
      have hopkUpd := p2Over_cliPollPk_opkOkUpdate_placed A.repAlloc y.g.F w.opkWord (cliKitStk B)
        (hdrOpkIdBv? (mkPathAHdr m)) wOpk
      rw [hopkUpd] at hPf
      have hkpOk := cliPollSelf_kpRel_ok_placed hkpRel
      have hikBSk_ok : ikBSk = vecU8 kp.privateKey.bytes := by dsimp only [ikBSk]; rw [hkpOk]
      have hikBPk_ok : ikBPk = vecU8 kp.identityKey.publicKey.bytes := by dsimp only [ikBPk]; rw [hkpOk]
      obtain ⟨k, hk, _, _, hinp⟩ := pathA_acceptInput_agree_placed hdec0 hspkRel hspkPubEq hspkPrivEq
        hkpkRel hkpkPubEq hkpkPrivEq hopkOk hopkBytes hkpOk hikBSk_ok hikBPk_ok
      have hinp0 := hinp 0#32; rw [hinp0] at haccSome
      unfold P2OverV1Arm6EnvOfBob P2V1Arm6EnvOfBob at hevs; rw [hOk14_eq, hinp0] at hevs
      have hevs' : P2OverErrEnv y.g r evs := hErrEnv y.g r evs (by
        unfold P2OverPathCErrEnvAux; rw [hpkToE]; dsimp only; rw [hk, hkpOk]; dsimp only
        rw [haccSome]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hevs)))))
      have hregNone := cliPollSelf_regIdRel_err_placed hregErr
      have hpost := Entails.trans hPf (Entails.trans
        (sepConj_mono_left (Entails.trans
          (cliPollSelf_regIdErr_entails_decResAt_err_placed A.repAlloc
            y.g.F y.g.peer (cliKitStk B) y.out e err0)
          (entails_sepConj_anyHeap _)))
        (p2ErrFrame_fold_pathA_placed_rep y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpm rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, evs, hevs', herr0_p, herr0_s, htr_f,
          ⟨m, i, hpkToE, hi, hpm, Or.inl (Or.inr (Or.inr hregNone))⟩, hpost⟩)
    (fun _ _ _ _ _ _
        _ _ _ _ _ _ _ _ _
        _ _ _ _ _ _
        _ _ _ _ _ _
        _ _ _ _ _ _ hregRel _
        _ _ _ _
        _ _ _ _ _ _
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => by
      have hok_reg := cliPollSelf_regIdRel_ok_placed hregRel
      rw [hRegErr] at hok_reg; cases hok_reg)

theorem stageP2PathCOver_qpan_cli_archive_regErr_placed_at_of_init75_and_kits [LibsignalFullPlacement]
    {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (B : RunBudgets)
    {kitEnvs : ∀ (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      CliPollStageP2Envs (A := A.repAlloc) B F0 peer spkId kpkId opkWord kbk}
    {P2OverErrEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (hErrEnv : ∀ g r evs,
      P2OverPathCErrEnvOf (A := A.repAlloc) X W B
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
        kitEnvs g r evs →
      P2OverErrEnv g r evs)
    (hFitsErr : ∀ st_b g r,
      StoresGhost.opened.identity.regId cliIo.rd g.F = .error () →
      FitsEnv M lim st_b (P2OverErrEnv g r) →
      FitsEnv M lim st_b
        (P2OverPathCErrEnvOf (A := A.repAlloc) X W B
          (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
          (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
          kitEnvs g r))
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hInit75 : InitialStateMemInvPlacedOkOfEnv M (LibsignalCodeRoLoaded lsmpl) A lim W.C.F
      (InitialStateEnv W.C.F) (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hSelfKit : ∀ (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      IdentitySelfStoreKitPlacedOkI A lim
        (cliPollIdKitPlaced A.repAlloc F0 peer (cliKitStk B))
        (cliPollSelfKitPlaced A.repAlloc F0 peer (cliKitStk B))
        (kitEnvs F0 peer spkId kpkId opkWord kbk).selfEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hSpkKit : ∀ (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      SignedPreKeyStoreKitPlacedOk A lim
        (cliPollSpkKitPlaced A.repAlloc F0 spkId (cliKitStk B))
        (kitEnvs F0 peer spkId kpkId opkWord kbk).spkEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hKpkKit : ∀ (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      KyberPreKeyStoreKitPlacedOk A lim
        (cliPollKpkKitPlaced A.repAlloc F0 kpkId spkId kbk (cliKitStk B))
        (kitEnvs F0 peer spkId kpkId opkWord kbk).kpkEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hPkKit : ∀ (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      PreKeyStoreKitPlacedOk A lim
        (cliPollPkKitPlaced A.repAlloc F0 opkWord (cliKitStk B))
        (kitEnvs F0 peer spkId kpkId opkWord kbk).pkEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    StageP2PathCOverQpanCliRegErrMemInvPlacedAtStmt (LibsignalFrozen lsmpl) A lim PromoteOverArchiveEnv
      X mmpl gh W B P2OverErrEnv :=
  stageP2PathCOver_qpan_cli_regErr_full_placed_at_of_init75_aux A lim
    (PromEnv := PromoteOverArchiveEnv) (PromSessEnv := PromoteOverArchiveCanonSessEnvLocal)
    promoteOverArchiveEnv_eq_canon X mmpl gh W B
    (selfEnvOf := fun F0 peer spkId kpkId opkWord kbk => (kitEnvs F0 peer spkId kpkId opkWord kbk).selfEnv)
    (spkEnvOf := fun F0 peer spkId kpkId opkWord kbk => (kitEnvs F0 peer spkId kpkId opkWord kbk).spkEnv)
    (kpkEnvOf := fun F0 peer spkId kpkId opkWord kbk => (kitEnvs F0 peer spkId kpkId opkWord kbk).kpkEnv)
    (pkEnvOf := fun F0 peer spkId kpkId opkWord kbk => (kitEnvs F0 peer spkId kpkId opkWord kbk).pkEnv)
    (fun g r evs h => hErrEnv g r evs (p2OverPathCErrEnvOf_eq_aux X W B _ _ _ ▸ h))
    (fun st_b g r hRegErr hf => by
      rw [← p2OverPathCErrEnvOf_eq_aux]
      exact hFitsErr st_b g r hRegErr hf)
    hDropNz hG hInit75 hSelfKit hSpkKit hKpkKit hPkKit

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonStage2OverRegErrPlacedBudgetFd
