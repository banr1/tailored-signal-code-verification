/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2PurePlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevCapPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedABudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonKitsPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonPollPathAPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonPollPathAUntrustedPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonPollPathBPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonPollPathCPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonStage2OverBPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonStage2PathAPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonStage3Prev1PlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.StagesOverCliPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage1InstPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Steps
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureCallees
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureDefs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureDefsPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureEntry
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathATopPlacedBudgetAux
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBMain
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBMainPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmt
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureTrustedP1
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.InitInv
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import ProofLib
import ProofLib.SepLogic.WPp

/-!
# Kit-Parametric D2(c) Top-Level Block-`518` Poll Wrapper

Proves `poll_d2c_canon_gvSeqFree_frozen_of_kits`, assembling the untrusted-identity branch
(`b = false`), trusted Stage P1 (`b = true`), Path A (`opt = none`), Path B (`opt = some r`,
`SessMatchesPm`), and Path C (`opt = some r`, `¬ SessMatchesPm`) from `CanonPollKitsPlacedOk`.
-/

@[expose] public section

open CryptoVerification.SignalSession.Cli.RunProofs (DecPkOk₀)
open LibsignalBinary.Proofs.Placed.Bridge (lsmpl lsρ)

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonPollPathsPlacedBudgetFd

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet


open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open CryptoGames.LibsignalSession (PublicKey SignalMessage)
open CryptoGames.LibsignalSessionApi (Session SessionRecord)
open CryptoVerification (LibsignalFullPlacement LibsignalPlacement lsmpl lsρ)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3 (genP3S5Model)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (
  SessionExtraRel sp_sub_cd0_align_std3 stageP1CallStack
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (clearPending)
open CryptoVerification.E2E (
  PreKeyMessageFields UnreachedPqxdhPrimitives acceptInput modelPrims
)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (decryptPrekeyCoroInitAt)
open CryptoVerification.E2E.Pqxdh.ResponderCore (ofSignalPqxdhPrimitives)
open CryptoVerification.E2E.Record (encSession)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles withLsCodeRoLoaded)
open CryptoVerification.LibsignalPublicApiRepr (preKeyMsgAt)
open CryptoVerification.LibsignalSpqrV1 (spqrV1)
open CryptoVerification.LibsignalTripleRatchet (withLsFrozen)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchet.Record (CloneRel)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost protocolAddressAt uuidTryParse)
open CryptoVerification.RecordCodecs (IdentityKeyPair)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli (
  StoresGhost cliIdentityVtSym cliKyberPreKeyVtSym cliPreKeyVtSym cliSignedPreKeyVtSym dirAt
)
open CryptoVerification.SignalSession.Cli.KitInst (
  cliKyberPreKeyStoreSpecPlaced cliPreKeyStoreSpecPlaced cliSignedPreKeyStoreSpecPlaced
)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo cliRunBudgets coinsInstalledPlaced)
open CryptoVerification.SignalSession.Cli.RunCompose (
  DecPkGhost RunSem dpPollNeed dpSlotArgsPlaced
)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs (
  DecPkOkD2c DecPkOk₀ SessMatchesPm decPkDef decPkDefD2c decPkDefD2c_eq_decPkDef_of_match
  decPkDefD2c_eq_decPkDef_of_noCurrent dpFutStartAt pkStoreKeys pmOfE
)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (
  LsTokenInit StageP1PostRegs cliIdStoreSpecFullPlaced cliId_trustRel_eq_of_trusted
  cliKitStk cliKpkStoreSpecFullPlaced cliPollIdKit cliPollIdKitPlaced cliPollKpkKitPlaced
  cliPollPkKitPlaced cliPollSessKit cliPollSessKitPlaced cliPollSessPrev1KitPlaced
  cliPollSpkKitPlaced cliPollStoresKitsAtPlaced cliSess_loadRel_isOk closStackUnusedP1OkAt
  clos_stack_3280_split_for_p1_ok coroUnusedP1At
  currentSession_some_of_cliPollSessPlaced_loadRel dpClosSubStack
  dpFutStartAt_split_for_p1_placed dpPollEntryPlaced dpPollNeed_eq_frame_add_subStack
  dpPollProgPlaced loadRec_of_cliPollSessPlaced_loadRel pathAInitSession pathAInitState
  pmKyberId pmPreKeyId preKeyMsgAt_eq_idKey_sep preKeyMsgRemIdKeyAt
  sepWPp_conseq_pre sepWPp_sepExists_left stageP1CallStack_le_subStack stageP1Ok_trace_eq_placed
  stackAt_poll_entry_split stackAt_subStack_split subStack_le_sp_of_dpPollNeed
  subroutine_ok_of_sepWPp_steps trusted_ok_of_filesOkPeer
)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (EncodeInjOn FilesOkPeer loadRec scopeIn scopeKit)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget SeqEnv)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2PurePlacedBudget (
  InitializeBobV1OptFieldsEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2TopPlacedBudget (
  StageP2MatchedEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevCapPlacedBudget (
  StageP3ErrM3Env StageP3OkPrefixM3Env
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudget (
  OverVerNe1e04CliAtFrozenPlacedBody
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudgetAux (
  StageP3Prev1Env StageP3VerNePrev1Env
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedABudget (AcceptOptFieldsEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudget (
  overPollTryDecryptPlacedSpecTPTight
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudgetAux (
  CliStageP4Prev1Envs StageP2OverEnv StageP4Prev1Env
  storesAt_opened_entails_cliPollStoresKitsAtPlaced_d2c
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverUntrustedPlacedBudget (
  dpPollPre_unpack_d2c_frozen_placed sepWPp_pollGoal_of_decPk_eq_frozen_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudget (
  P2OverPathCErrEnvOf P2OverPathCOkEnvOf PromoteOverArchiveCanonSessEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.StagesOverCliPlacedBudget (
  cliPollSelfBudgetEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureEntryPlacedBudget (
  dpPollEntrySpatialPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathATopPlacedBudgetAux (
  p1Ok_recombine_entails_stageP2_placed_budget sepWPp_bind_p1_noPanic
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget (
  StageP3Env StageP3ErrEnv StageP3OkPrefixEnv StageP3VerNeEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget (
  StageP2PathAEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureTrustedP1PlacedBudget (
  CliStageP1OkEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget (
  cliPollStageP1_fsAt_placed runHooks_to_stages
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage1InstPlacedBudget (
  stageP1_ok_placed_of_kits
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux (
  cliP2PathAOptFieldsErrEnv cliP2PathAOptFieldsOkEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget (
  cliPollIdBudgetEnv cliPollKpkBudgetEnv cliPollPkBudgetEnv cliPollSessBudgetEnv
  cliPollSessSeqFreeBudgetEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (
  CliGhostAllocHooks
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget (
  DpPollGhostStateBudget dpPollSpecStateBudget dpSlotPollKStatePlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (sessDeserializeSpecPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonKitsPlacedBudgetFd (
  CanonPollKitsPlacedOk
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonStage2OverBPlacedBudgetFd (
  StageP2OverQpanCliMemInvPlacedAtXBStmt StageP2OverQpanCliRegErrPlacedAtBStmt
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonStage2PathAPlacedBudgetFd (
  StageP2PathAQpanCliNoReadFrozenPlacedAtStmt
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonStage3Prev1PlacedBudgetFd (
  DecPkD2cCanonPollGvSeqFreeEnv PathCP3Envs cliP2KitEnvsFixed cliPollStageP4Prev1SeqFreeEnvsAt
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonPollPathAUntrustedPlacedBudgetFd (
  closure_untrusted_d2c_frozen_placed_ok_of_kits
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonPollPathAPlacedBudgetFd (
  closure_pathA_frozen_placed_ok_at_gv_of_kits
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonPollPathBPlacedBudgetFd (
  closure_pathB_frozen_placed_ok_at_gv_of_kits
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonPollPathCPlacedBudgetFd (
  closure_pathC_frozen_placed_ok_at_gv_of_kits
)

local elab "erase_hkdf_arm64_norm" : command => Lean.Elab.Command.liftCoreM do
  for n in [``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp,
            ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp,
            ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592,
            ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592] do
    Lean.Attribute.erase n `arm64_norm
erase_hkdf_arm64_norm

set_option maxHeartbeats 1000000 in
/-- Kit-parametric `{M} (A : RustCliAllocBudget M)`-generic Block-`518` D2(c) poll producer
at `DecPkD2cCanonPollGvSeqFreeEnv` (`0` `lsReadFileSym` hypotheses). -/
theorem poll_d2c_canon_gvSeqFree_frozen_of_kits [CryptoVerification.LibsignalFullPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {PrevEncOK : List (BitVec 8) → Prop}
    {verNeDecEnv : List (BitVec 8) → List AllocEvent → Prop}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    {p3c : CliHooks → PathCP3Envs}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (hG : CliGhostAllocHooks M A lim gh)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (S : RunSem)
    (hh_skel : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hDeser : subroutine_ok
      (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46) (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hKits : CanonPollKitsPlacedOk A lim cliRunBudgets ReadEnv DeserEnv
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hP2A : StageP2PathAQpanCliNoReadFrozenPlacedAtStmt A lim X mmpl gh W cliRunBudgets
      (cliP2PathAOptFieldsErrEnv A.repAlloc ReadEnv X W cliRunBudgets
        (fun F0 peer => cliPollSelfBudgetEnv A.repAlloc F0 peer (cliKitStk cliRunBudgets) ReadEnv))
      (cliP2PathAOptFieldsOkEnv A.repAlloc ReadEnv X W cliRunBudgets
        (fun F0 peer => cliPollSelfBudgetEnv A.repAlloc F0 peer (cliKitStk cliRunBudgets) ReadEnv)))
    (hP2Over_raw : StageP2OverQpanCliMemInvPlacedAtXBStmt
      (CryptoVerification.LibsignalFrozen lsmpl) A lim X mmpl gh W cliRunBudgets
      (P2OverPathCErrEnvOf (A := A.repAlloc) X W cliRunBudgets
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
        (cliP2KitEnvsFixed A.repAlloc ReadEnv))
      (P2OverPathCOkEnvOf (A := A.repAlloc) X W cliRunBudgets
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        PromoteOverArchiveCanonSessEnv
        (cliP2KitEnvsFixed A.repAlloc ReadEnv)))
    (hP2Over_regErr : StageP2OverQpanCliRegErrPlacedAtBStmt
      (CryptoVerification.LibsignalFrozen lsmpl) A lim X mmpl gh W cliRunBudgets
      (P2OverPathCErrEnvOf (A := A.repAlloc) X W cliRunBudgets
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
        (cliP2KitEnvsFixed A.repAlloc ReadEnv)))
    (hTry0 : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (overPollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (spqrV1 W.C.F W.Q.K) (tdEnv W))))
    (hPrevEnc : ∀ r s_old, scopeIn r → r.currentSession = some s_old →
      s_old.state.sessionVersion = 4#32 → PrevEncOK (encSession (clearPending s_old)))
    (hVerNeAt : OverVerNe1e04CliAtFrozenPlacedBody A lim PrevEncOK verNeDecEnv
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hp3Err : ∀ recG G₁ st rem loc msgG msg rest evs,
      StageP3ErrM3Env (tdEnv W) recG G₁ st rem loc msgG msg rest evs →
      (p3c W).errEnv recG G₁ st rem loc msgG msg rest evs)
    (hp3VerNe : ∀ recG st enc evs,
      StageP3VerNePrev1Env verNeDecEnv recG st enc evs →
      (p3c W).verNeEnv recG st enc evs)
    (hp3Ok : ∀ recG G₁ st rem loc msgG msg rest evs,
      StageP3OkPrefixM3Env (tdEnv W) recG G₁ st rem loc msgG msg rest evs →
      (p3c W).okPrefixEnv recG G₁ st rem loc msgG msg rest evs)
    (hp3Fits : ∀ st_b recG st rem loc msgG msg msgVer enc rest,
      FitsEnv M lim st_b
        (fun evs =>
          (∃ G₁, CloneRel recG G₁ ∧ (p3c W).errEnv recG G₁ st rem loc msgG msg rest evs) ∨
          (p3c W).verNeEnv recG st enc evs ∨
          ∃ G₁, CloneRel recG G₁ ∧ (p3c W).okPrefixEnv recG G₁ st rem loc msgG msg rest evs) →
      FitsEnv M lim st_b
        (StageP3Prev1Env (tdEnv W) verNeDecEnv recG st rem loc msgG msg msgVer enc rest))
    (hErrEnv : ∀ g r evs,
      P2OverPathCErrEnvOf (A := A.repAlloc) X W cliRunBudgets
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
        (cliP2KitEnvsFixed A.repAlloc ReadEnv) g r evs →
      P2OverErrEnv g r evs)
    (hOkEnv : ∀ g r evs,
      P2OverPathCOkEnvOf (A := A.repAlloc) X W cliRunBudgets
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        PromoteOverArchiveCanonSessEnv
        (cliP2KitEnvsFixed A.repAlloc ReadEnv) g r evs →
      P2OverOkEnv g r evs)
    (hFitsSplit : ∀ st_b g r,
      FitsEnv M lim st_b (StageP2OverEnv P2OverErrEnv P2OverOkEnv g r) →
      FitsEnv M lim st_b
        (StageP2OverEnv
          (P2OverPathCErrEnvOf (A := A.repAlloc) X W cliRunBudgets
            (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
            (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
            (cliP2KitEnvsFixed A.repAlloc ReadEnv))
          (P2OverPathCOkEnvOf (A := A.repAlloc) X W cliRunBudgets
            (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
            PromoteOverArchiveCanonSessEnv
            (cliP2KitEnvsFixed A.repAlloc ReadEnv))
          g r))
    (hinjK : EncodeInjOn scopeKit)
    (hS : S.decryptPrekey = decPkDefD2c X ⟨W.C, W.Q⟩ scopeIn)
    (hSemOk : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      FilesOkPeer scopeIn F peer ∧ DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn F peer me pm)
    (stk' : Nat) (hneed : dpPollNeed cliRunBudgets ≤ stk') (hstk63 : stk' ≤ 2 ^ 63) :
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      dpPollEntryPlaced
      (withLsFrozen lsmpl
        (dpPollSpecStateBudget
          (dpSlotPollKStatePlaced A lim
            (DecPkD2cCanonPollGvSeqFreeEnv A.repAlloc W X ReadEnv DeserEnv
              P2OverErrEnv P2OverOkEnv tdEnv p3c)
            cliRunBudgets S)
          stk')) := by
  let _ := hDeser
  let _ := hp3Fits
  let B := cliRunBudgets
  let P2PathAErrEnv := cliP2PathAOptFieldsErrEnv A.repAlloc ReadEnv X W cliRunBudgets
    (fun F0 peer => cliPollSelfBudgetEnv A.repAlloc F0 peer (cliKitStk cliRunBudgets) ReadEnv)
  let P2PathAOkEnv := cliP2PathAOptFieldsOkEnv A.repAlloc ReadEnv X W cliRunBudgets
    (fun F0 peer => cliPollSelfBudgetEnv A.repAlloc F0 peer (cliKitStk cliRunBudgets) ReadEnv)
  let Scope := scopeIn
  have hsub : ∀ r, Scope r → scopeIn r := fun _ h => h
  let DecPkEnv := DecPkD2cCanonPollGvSeqFreeEnv A.repAlloc W X ReadEnv DeserEnv
    P2OverErrEnv P2OverOkEnv tdEnv p3c
  let p4Envs := fun B' F0 peer pid kpkId spkId kbk =>
    cliPollStageP4Prev1SeqFreeEnvsAt A.repAlloc B' F0 peer pid kpkId spkId kbk ReadEnv
  have hp4Envs : p4Envs = fun B' F0 peer pid kpkId spkId kbk =>
      cliPollStageP4Prev1SeqFreeEnvsAt A.repAlloc B' F0 peer pid kpkId spkId kbk ReadEnv := rfl
  have hEnv : ∀ g evs, DecPkEnv g evs → DecPkEnv g evs := fun _ _ h => h
  have hneed' : dpPollNeed B ≤ stk' := hneed
  apply subroutine_ok_of_sepWPp_steps
  intro y R s0 hpc hrun hpre hsp
  obtain ⟨hpure, hm_base⟩ :=
    dpPollPre_unpack_d2c_frozen_placed (W := W) (B := B) (S := S) (Scope := Scope)
      hSemOk stk' y R s0 hpre
  have hfits_all := hpure.fits
  obtain ⟨b, htrusted⟩ :=
    trusted_ok_of_filesOkPeer (peer := y.g.peer) hpure.filesOkPeer y.g.msg.identityKey
  cases b with
  | false =>
    dsimp only [dpPollEntrySpatialPlaced] at hm_base
    exact closure_untrusted_d2c_frozen_placed_ok_of_kits A lim hDropNz mmpl gh W X B S Scope
      hh_skel hKits hinjK hsub hS stk' hneed' hstk63 y
      (hfits_all.mono fun _ h => Or.inl (Or.inl h))
      (fun evs h => hEnv y.g evs (Or.inl (Or.inl h)))
      R s0 hpc hrun hsp hpure.fr hpure.x0 hpure.x1 hpure.x2 hpure.files_eq hpure.filesOkPeer
      hpure.decPkOk htrusted hm_base
  | true =>
    dsimp only
    dsimp only [dpPollEntrySpatialPlaced] at hm_base
    have hh := runHooks_to_stages hh_skel
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
    let kitEnv := cliPollSessSeqFreeBudgetEnv A.repAlloc y.g.F y.g.peer σ DeserEnv ReadEnv
    let ikitEnv := cliPollIdBudgetEnv A.repAlloc y.g.F y.g.peer σ ReadEnv
    let pkKitEnv := cliPollPkBudgetEnv A.repAlloc y.g.F pid σ ReadEnv
    let kpkKitEnv := fun kpkId spkId =>
      cliPollKpkBudgetEnv A.repAlloc y.g.F kpkId spkId kbk σ ReadEnv
    let sp := s0.sp - 0xcd0#64
    have hsp_align0 : (s0.sp &&& 15#64 == 0#64) = true := by
      simpa [State.spAligned] using hsp
    have hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat :=
      (subStack_le_sp_of_dpPollNeed hneed' hpure.stk_le_sp).1
    have hent_stores := storesAt_opened_entails_cliPollStoresKitsAtPlaced_d2c A.repAlloc σ
      y.g.stores hsub hpure.filesOkPeer hpure.decPkOk pid sid kid kbk
    have hm_stores : s0.mem ⊨
        memRegion y.out 48 ∗
          dpFutStartAt y.fut (dpSlotArgsPlaced y.g) ∗
          memRegion y.cx 32 ∗
          cliPollStoresKitsAtPlaced A.repAlloc y.g.F scopeKit y.g.peer
            pid sid kid kbk σ y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗
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
    have hp1_le := stageP1CallStack_le_subStack (A := A.repAlloc)
      0#64 y.g.F scopeKit y.g.peer B
    have hp1_64 : stageP1CallStack kit ikit ≤ 2 ^ 64 := Nat.le_trans hp1_le hsub64
    rw [dpFutStartAt_split_for_p1_placed y.g y.fut,
        preKeyMsgAt_eq_idKey_sep A.repAlloc y.g.msgG y.g.msgA y.g.msg,
        stackAt_poll_entry_split s0.sp B stk' hneed' hstk63,
        stackAt_subStack_split sp B (stageP1CallStack kit ikit) hp1_le hsub64,
        clos_stack_3280_split_for_p1_ok s0.sp] at hm_stores
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm_stores
    rcases hm_stores with ⟨u_98, u_a0, u_a8, u_b0, u_b8, u_c0, u_c8, u_d0, v_sp0,
      b_4f2, u_3a0, u_398, b_390, coins, hm_flat⟩
    rw [← ProofLib.memRegion_cells (y.fut + 0x250#64) 6 (by decide)] at hm_flat
    simp only [Nat.reduceMul] at hm_flat
    dsimp only [cliPollStoresKitsAtPlaced] at hm_flat
    let P_p1 : SepProp :=
      decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt
        (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
        (y.g.stores + 0x78#64) kpkKit.kpk_vt coins ∗
      cells (y.fut + 0x70#64) 14 ∗
      cells (y.fut + 0xe0#64) 4 ∗
      memRegion (y.fut + 0x100#64) 336 ∗
      ((y.fut + 0x2c0#64) ↦₈ 0#8) ∗
      cells (y.fut + 0x2c8#64) 25 ∗
      ((y.fut + 0x390#64) ↦₈ b_390) ∗
      ((y.fut + 0x398#64) ↦₆₄ u_398) ∗
      ((y.fut + 0x3a0#64) ↦₆₄ u_3a0) ∗
      cells (y.fut + 0x428#64) 8 ∗
      cells (y.fut + 0x490#64) 4 ∗
      ((y.fut + 0x4f2#64) ↦₈ b_4f2) ∗
      (sp ↦₆₄ v_sp0) ∗
      ((sp + 0x98#64) ↦₆₄ u_98) ∗
      ((sp + 0xa0#64) ↦₆₄ u_a0) ∗
      ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
      ((sp + 0xb0#64) ↦₆₄ u_b0) ∗
      ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
      ((sp + 0xc0#64) ↦₆₄ u_c0) ∗
      ((sp + 0xc8#64) ↦₆₄ u_c8) ∗
      ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
      memRegion (sp + 0xd8#64) 348 ∗
      memRegion (sp + 0x3e0#64) 368 ∗
      cells (s0.sp - 0x60#64) 12 ∗
      lsLogOff ∗
      kit.storeAt (y.g.stores + 0xf0#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions ∗
      ikit.identityAt y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity ∗
      protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
      ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
      A.pool lim y.st s0 ∗
      stackAt sp (stageP1CallStack kit ikit)
    let Fr_inner : SepProp :=
      memRegion (y.fut + 0x250#64) 48 ∗
      coroUnusedP1At y.fut ∗
      closStackUnusedP1OkAt sp ∗
      memRegion y.out 48 ∗
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B))
        (dpClosSubStack B - stageP1CallStack kit ikit) ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
      memRegion y.cx 32 ∗
      pkKit.storeAt (y.g.stores + 0xc8#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.oneTime ∗
      spkKit.storeAt (y.g.stores + 0x50#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.signed ∗
      kpkKit.storeAt (y.g.stores + 0x78#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.kyber ∗
      dirAt A.repAlloc (y.g.stores + 0x118#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.pub ∗
      protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
      preKeyMsgRemIdKeyAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
      coinsInstalledPlaced y.g.coinsP y.g.coins ∗
      LsTokenInit
    have hm_split : s0.mem ⊨ (P_p1 ∗ Fr_inner) ∗ R :=
      Satisfies.mono (by dsimp only [P_p1, Fr_inner, kit, ikit, pkKit, spkKit, kpkKit,
        cliPollSessKitPlaced, cliPollIdKitPlaced, cliPollPkKitPlaced, cliPollSpkKitPlaced,
        cliPollKpkKitPlaced, cliIdStoreSpecFullPlaced, cliPreKeyStoreSpecPlaced,
        cliSignedPreKeyStoreSpecPlaced, cliKpkStoreSpecFullPlaced,
        cliKyberPreKeyStoreSpecPlaced]; sep_frame) hm_flat
    refine ⟨P_p1 ∗ Fr_inner, R, hm_split, ?_⟩
    have hfits_p1 : FitsEnv M lim y.st (CliStageP1OkEnv (A := A.repAlloc) B ReadEnv DeserEnv y.g) :=
      hfits_all.mono fun _ h => Or.inl (Or.inr (Or.inl h))
    have hwp := stageP1_ok_placed_of_kits (Qp := fun _ _ => False)
      mmpl gh W B y.g.F y.g.peer y.g.msg.identityKey hDropNz
      hh (hKits.sessOk y.g.F y.g.peer) (hKits.idOk y.g.F y.g.peer)
      y.st CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity
      hp1_64 rfl rfl
      (fun _ (h : (cliPollSessKit A.repAlloc 0#64 y.g.F scopeKit y.g.peer σ).loadRel
        CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions y.g.peer.val _) => cliSess_loadRel_isOk h)
      (fun _ (h : (cliPollIdKit A.repAlloc 0#64 y.g.F y.g.peer σ).trustRel
        CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey .receiving _) =>
        cliId_trustRel_eq_of_trusted htrusted h)
      hfits_p1
      s0 sp y.out y.fut y.cx y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) y.g.stores
      (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
      (y.g.stores + 0x78#64) kpkKit.kpk_vt coins
      v_sp0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0
      b_390 b_4f2
      hpure.ro
      (cliPollStageP1_fsAt_placed hh_skel y.g.F scopeKit y.g.peer B hpure.files_eq)
      hpc hrun hsp_align0 rfl hpure.x0 hpure.x1 hpure.x2
    refine sepWPp_bind_p1_noPanic hwp rfl ?_
    intro s1 P_1 hsteps01 hpc1 hrun1 hq1
    rcases hq1 with ⟨⟨opt, evs_p1, hevs_p1, hload_rel, _htrust_rel, htr_evs, hent_1⟩,
      hs1_sp, hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16, hx17,
      hx19, hx20, hx22, hx23, hx24, hx25, hx28, hx29, hvregs1, _hro1⟩
    have hfr1 : CryptoVerification.LibsignalFrozen lsmpl s1.mem :=
      CryptoVerification.libsignalFrozen_of_keepsFrozen hpure.fr hsteps01.keepsFrozen
    have htr1 : s1.trace = s0.trace := stageP1Ok_trace_eq_placed htr_evs
    have hsp_align1 : (s1.sp &&& 15#64 == 0#64) = true :=
      hs1_sp ▸ sp_sub_cd0_align_std3 hsp_align0
    have hregs1 : StageP1PostRegs s0 s1 sp y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 0x78#64)
        (lsρ cliKyberPreKeyVtSym) :=
      ⟨hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16, hx17,
       hx19, hx20, hx22, hx23, hx24, hx25, hx28, hx29, hvregs1⟩
    refine sepWPp_conseq_pre (sepConj_mono_left hent_1) ?_
    simp only [sepExists_sepConj_left]
    refine sepWPp_sepExists_left fun v_a8 =>
      sepWPp_sepExists_left fun v_b8 =>
      sepWPp_sepExists_left fun v_d0 => ?_
    have hrecomb := p1Ok_recombine_entails_stageP2_placed_budget stk' hneed' hstk63 y
      (M.stepEvents evs_p1 y.st) s0 s1 coins v_a8 v_b8 v_d0 opt
    dsimp only at hrecomb
    refine sepWPp_conseq_pre hrecomb ?_
    let S0 : RunSem := { S with decryptPrekey := decPkDef X ⟨W.C, W.Q⟩ Scope }
    let y0 : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S0) :=
      ⟨y.out, y.fut, y.cx, y.g, y.st⟩
    cases opt with
    | none =>
      have hloadNone : loadRec Scope y.g.F y.g.peer.val = .ok none :=
        loadRec_of_cliPollSessPlaced_loadRel hinjK hsub hpure.filesOkPeer hload_rel
      have hnone : ∀ r', loadRec Scope y.g.F y.g.peer.val = .ok (some r') →
          r'.currentSession = none := by
        intro r' hr'; rw [hloadNone] at hr'; cases hr'
      have hdecOk0 : DecPkOk₀ ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg :=
        hpure.decPkOk.toDecPkOk₀_of_noCurrent hnone
      have hEq : S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins =
          S0.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins := by
        dsimp only [S0]
        rw [hS]
        exact decPkDefD2c_eq_decPkDef_of_noCurrent X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val
          y.g.me.val y.g.msg y.g.coins hnone
      refine sepWPp_pollGoal_of_decPk_eq_frozen_placed stk' y s0 s1 _ R hEq ?_
      have hfits_p2 :
          FitsEnv M lim (M.stepEvents evs_p1 y.st)
            (StageP2PathAEnv P2PathAErrEnv P2PathAOkEnv y.g) :=
        (hfits_all.mono fun _ h =>
          Or.inl (Or.inr (Or.inr (Or.inl ⟨hload_rel, Or.inl h⟩)))).seq_right hevs_p1
      have hevs_p2_err : ∀ evs_p2, P2PathAErrEnv y.g evs_p2 → DecPkEnv y.g (evs_p1 ++ evs_p2) :=
        fun evs_p2 he2 =>
          hEnv y.g _ (Or.inl (Or.inr (Or.inr (Or.inl
            ⟨hload_rel, Or.inl (LibsignalBinary.Heap.SeqEnv.append hevs_p1 (Or.inl he2))⟩))))
      refine closure_pathA_frozen_placed_ok_at_gv_of_kits mmpl gh W X B S0 Scope
        hP2A hDropNz hG hh hKits hTry0
        hinjK hsub rfl stk' hneed' hstk63 y0 kitEnv ikitEnv pkKitEnv kpkKitEnv
        rfl rfl rfl (fun _ _ => rfl) evs_p1 s0 s1 coins
        v_a8 v_b8 v_d0 R hpure.files_eq hpure.filesOkPeer hdecOk0 hpure.coins_lt htrusted
        hload_rel hfits_p2 hevs_p2_err
        ?_ ?_ ?_ ?_ ?_ ?_
        hsteps01 htr1 hfr1 hs1_sp hsp_sub hpc1 hrun1 hsp_align1 hregs1
      · intro evs_p2 m i k kp reg dk recG he2 hpm hi hk hkp hreg hacc hex
        exact (hfits_all.mono fun _ h =>
          Or.inl (Or.inr (Or.inr (Or.inl ⟨hload_rel, Or.inr ⟨m, i, k, kp, reg, dk, recG,
            hpm, hi, hk, hkp, hreg, hacc, hex, Or.inl h⟩⟩)))).seq_right
          (LibsignalBinary.Heap.SeqEnv.append hevs_p1 he2)
      · intro evs_p2 m i k kp reg dk recG G₁ G' evs_p3 pt he2 hpm hi hk hkp hreg hacc hex
          hver hcl hdec he3 hok
        exact (hfits_all.mono fun _ h =>
          Or.inl (Or.inr (Or.inr (Or.inl ⟨hload_rel, Or.inr ⟨m, i, k, kp, reg, dk, recG,
            hpm, hi, hk, hkp, hreg, hacc, hex,
            Or.inr ⟨G₁, G', pt, hver, hcl, hdec, hok, h⟩⟩⟩)))).seq_right
          (LibsignalBinary.Heap.SeqEnv.append (LibsignalBinary.Heap.SeqEnv.append hevs_p1 he2) he3)
      · intro evs_p2 m i k kp reg dk recG G₁ G' evs_p3 pt evs_p4 he2 hpm hi hk hkp hreg hacc hex
          hver hcl hdec he3 hok he4
        exact hEnv y.g _ (Or.inl (Or.inr (Or.inr (Or.inl ⟨hload_rel, Or.inr ⟨m, i, k, kp, reg, dk,
          recG, hpm, hi, hk, hkp, hreg, hacc, hex,
          Or.inr ⟨G₁, G', pt, hver, hcl, hdec, hok,
            LibsignalBinary.Heap.SeqEnv.append (LibsignalBinary.Heap.SeqEnv.append (LibsignalBinary.Heap.SeqEnv.append hevs_p1 he2) he3)
              (Or.inr (Or.inr (Or.inr he4)))⟩⟩⟩))))
      · intro evs_p2 m i k kp reg dk recG G₁ G' evs_p3 pt evs_p4 he2 hpm hi hk hkp hreg hacc hex
          hver hcl hdec he3 hok he4
        exact hEnv y.g _ (Or.inl (Or.inr (Or.inr (Or.inl ⟨hload_rel, Or.inr ⟨m, i, k, kp, reg, dk,
          recG, hpm, hi, hk, hkp, hreg, hacc, hex,
          Or.inr ⟨G₁, G', pt, hver, hcl, hdec, hok,
            LibsignalBinary.Heap.SeqEnv.append (LibsignalBinary.Heap.SeqEnv.append (LibsignalBinary.Heap.SeqEnv.append hevs_p1 he2) he3)
              (Or.inr (Or.inl he4))⟩⟩⟩))))
      · intro evs_p2 m i k kp reg dk recG G₁ _G' evs_p3 _e he2 hpm hi hk hkp hreg hacc hex
          hver hcl _hdec he3 _herr _hne
        have he3_env : StageP3Env (tdEnv W) recG
            (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
            y.g.peer y.g.me y.g.msgG.msg y.g.msg.message
            (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins evs_p3 := by
          dsimp only [y0, dpSlotPollKStatePlaced] at hver
          unfold StageP3Env
          simp only [hver, ↓reduceIte]
          exact ⟨G₁, hcl, he3⟩
        exact hEnv y.g _ (Or.inl (Or.inr (Or.inr (Or.inl ⟨hload_rel, Or.inr ⟨m, i, k, kp, reg, dk,
          recG, hpm, hi, hk, hkp, hreg, hacc, hex,
          Or.inl (LibsignalBinary.Heap.SeqEnv.append (LibsignalBinary.Heap.SeqEnv.append hevs_p1 he2) he3_env)⟩⟩))))
      · intro evs_p2 m i k kp reg dk recG evs_p3 he2 hpm hi hk hkp hreg hacc hex hver_ne he3
        have he3_env : StageP3Env (tdEnv W) recG
            (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
            y.g.peer y.g.me y.g.msgG.msg y.g.msg.message
            (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins evs_p3 := by
          dsimp only [y0, dpSlotPollKStatePlaced] at hver_ne
          unfold StageP3Env
          simp only [hver_ne, ↓reduceIte]
          exact he3
        exact hEnv y.g _ (Or.inl (Or.inr (Or.inr (Or.inl ⟨hload_rel, Or.inr ⟨m, i, k, kp, reg, dk,
          recG, hpm, hi, hk, hkp, hreg, hacc, hex,
          Or.inl (LibsignalBinary.Heap.SeqEnv.append (LibsignalBinary.Heap.SeqEnv.append hevs_p1 he2) he3_env)⟩⟩))))
    | some r =>
      obtain ⟨sess, hcur⟩ := currentSession_some_of_cliPollSessPlaced_loadRel hload_rel
      have hloadSome : loadRec Scope y.g.F y.g.peer.val = .ok (some r) :=
        loadRec_of_cliPollSessPlaced_loadRel hinjK hsub hpure.filesOkPeer hload_rel
      rcases Classical.em (SessMatchesPm sess y.g.msg) with hmatch | hnot_match
      · have hdecOk0 : DecPkOk₀ ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg :=
          hpure.decPkOk.toDecPkOk₀_of_match hloadSome hcur hmatch
        have hEq : S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins =
            S0.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins := by
          dsimp only [S0]
          rw [hS]
          exact decPkDefD2c_eq_decPkDef_of_match X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val
            y.g.me.val y.g.msg y.g.coins hloadSome hcur hmatch
        refine sepWPp_pollGoal_of_decPk_eq_frozen_placed stk' y s0 s1 _ R hEq ?_
        have hfits_p2 :
            FitsEnv M lim (M.stepEvents evs_p1 y.st)
              (StageP2MatchedEnv sess y.g.msg.identityKey) :=
          (hfits_all.mono fun _ h =>
            Or.inl (Or.inr (Or.inr (Or.inr ⟨r, sess, hload_rel, hcur, Or.inl h⟩)))).seq_right
            hevs_p1
        refine closure_pathB_frozen_placed_ok_at_gv_of_kits
          mmpl gh W hDropNz hG X B S0 Scope hh hKits hTry0 hinjK hsub rfl
          stk' hneed' hstk63 y0 kitEnv ikitEnv rfl rfl evs_p1 r sess s0 s1 coins v_a8 v_b8 v_d0 R
          hpure.files_eq hpure.filesOkPeer hdecOk0 hpure.coins_lt htrusted hload_rel hcur hfits_p2
          ?_ ?_ ?_ ?_ ?_ ?_
          hsteps01 htr1 hfr1 hs1_sp hsp_sub hpc1 hrun1 hsp_align1 hregs1
        · intro hne evs_p2 he2
          have he2_env : StageP2MatchedEnv sess y.g.msg.identityKey evs_p2 := by
            dsimp only [y0, dpSlotPollKStatePlaced] at hne
            unfold StageP2MatchedEnv
            simp only [hne, ↓reduceIte]
            exact he2
          exact hEnv y.g _ (Or.inl (Or.inr (Or.inr (Or.inr
            ⟨r, sess, hload_rel, hcur, Or.inl (LibsignalBinary.Heap.SeqEnv.append hevs_p1 he2_env)⟩))))
        · intro hrem evs_p2 recG he2 hex
          exact (hfits_all.mono fun _ h =>
            Or.inl (Or.inr (Or.inr (Or.inr ⟨r, sess, hload_rel, hcur,
              Or.inr ⟨hrem, recG, hex, Or.inl h⟩⟩)))).seq_right (LibsignalBinary.Heap.SeqEnv.append hevs_p1 he2)
        · intro hrem hver evs_p2 recG G₁ G' evs_p3 pt he2 hex hcl hdec he3 hok
          exact (hfits_all.mono fun _ h =>
            Or.inl (Or.inr (Or.inr (Or.inr ⟨r, sess, hload_rel, hcur,
              Or.inr ⟨hrem, recG, hex, Or.inr ⟨hver, G₁, G', pt, hcl, hdec, hok, h⟩⟩⟩)))).seq_right
            (LibsignalBinary.Heap.SeqEnv.append (LibsignalBinary.Heap.SeqEnv.append hevs_p1 he2) he3)
        · intro hrem hver evs_p2 recG G₁ G' evs_p3 pt evs_p4 he2 hex hcl hdec he3 hok he4
          exact hEnv y.g _ (Or.inl (Or.inr (Or.inr (Or.inr ⟨r, sess, hload_rel, hcur,
            Or.inr ⟨hrem, recG, hex, Or.inr ⟨hver, G₁, G', pt, hcl, hdec, hok,
              LibsignalBinary.Heap.SeqEnv.append (LibsignalBinary.Heap.SeqEnv.append (LibsignalBinary.Heap.SeqEnv.append hevs_p1 he2) he3) (Or.inr he4)⟩⟩⟩))))
        · intro hrem hver evs_p2 recG G₁ _G' evs_p3 _e he2 hex hcl _hdec he3 _herr _hne
          have he3_env : StageP3Env (tdEnv W) recG sess.state y.g.peer y.g.me y.g.msgG.msg
              y.g.msg.message (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins evs_p3 := by
            dsimp only [y0, dpSlotPollKStatePlaced] at hver
            unfold StageP3Env
            simp only [hver, ↓reduceIte]
            exact ⟨G₁, hcl, he3⟩
          exact hEnv y.g _ (Or.inl (Or.inr (Or.inr (Or.inr ⟨r, sess, hload_rel, hcur,
            Or.inr ⟨hrem, recG, hex,
              Or.inl (LibsignalBinary.Heap.SeqEnv.append (LibsignalBinary.Heap.SeqEnv.append hevs_p1 he2) he3_env)⟩⟩))))
        · intro hrem hver_ne evs_p2 recG evs_p3 he2 hex he3
          have he3_env : StageP3Env (tdEnv W) recG sess.state y.g.peer y.g.me y.g.msgG.msg
              y.g.msg.message (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins evs_p3 := by
            dsimp only [y0, dpSlotPollKStatePlaced] at hver_ne
            unfold StageP3Env
            simp only [hver_ne, ↓reduceIte]
            exact he3
          exact hEnv y.g _ (Or.inl (Or.inr (Or.inr (Or.inr ⟨r, sess, hload_rel, hcur,
            Or.inr ⟨hrem, recG, hex,
              Or.inl (LibsignalBinary.Heap.SeqEnv.append (LibsignalBinary.Heap.SeqEnv.append hevs_p1 he2) he3_env)⟩⟩))))
      · have hFits2_over_abs :
            FitsEnv M lim (M.stepEvents evs_p1 y.st) (StageP2OverEnv P2OverErrEnv P2OverOkEnv y.g r) :=
          (hfits_all.mono fun _ h =>
            Or.inr ⟨r, sess, hloadSome, hcur, hnot_match, htrusted, Or.inl h⟩).seq_right hevs_p1
        have hFits2_raw_both := hFitsSplit _ y.g r hFits2_over_abs
        have hFits2_err_raw :
            FitsEnv M lim (M.stepEvents evs_p1 y.st)
              (P2OverPathCErrEnvOf (A := A.repAlloc) X W cliRunBudgets
                (InitializeBobV1OptFieldsEnv
                  (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
                (AcceptOptFieldsEnv
                  (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
                (cliP2KitEnvsFixed A.repAlloc ReadEnv) y.g r) :=
          hFits2_raw_both.mono fun _ h => Or.inl h
        have hFits2_ok_raw :
            ∀ reg0, CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg0 →
              FitsEnv M lim (M.stepEvents evs_p1 y.st)
                (StageP2OverEnv
                  (P2OverPathCErrEnvOf (A := A.repAlloc) X W cliRunBudgets
                    (InitializeBobV1OptFieldsEnv
                      (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
                    (AcceptOptFieldsEnv
                      (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
                    (cliP2KitEnvsFixed A.repAlloc ReadEnv))
                  (P2OverPathCOkEnvOf (A := A.repAlloc) X W cliRunBudgets
                    (InitializeBobV1OptFieldsEnv
                      (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
                    PromoteOverArchiveCanonSessEnv
                    (cliP2KitEnvsFixed A.repAlloc ReadEnv))
                  y.g r) :=
          fun _ _ => hFits2_raw_both
        refine closure_pathC_frozen_placed_ok_at_gv_of_kits A lim DecPkEnv
          (PrevEncOK := PrevEncOK) (verNeDecEnv := verNeDecEnv)
          (ReadEnv := ReadEnv) (DeserEnv := DeserEnv) (p4Envs := p4Envs)
          hDropNz hp4Envs
          mmpl gh W hG X B S Scope hP2Over_raw hP2Over_regErr hPrevEnc hVerNeAt
          hh_skel hKits hTry0 hinjK hsub hS stk' hneed' hstk63 y evs_p1 r sess
          s0 s1 coins v_a8 v_b8 v_d0 R
          hFits2_err_raw hFits2_ok_raw
          (fun evs2 he2 =>
            Or.inr ⟨r, sess, hloadSome, hcur, hnot_match, htrusted,
              Or.inl (LibsignalBinary.Heap.SeqEnv.append hevs_p1 (Or.inl (hErrEnv y.g r evs2 he2)))⟩)
          ?_ ?_ ?_ ?_ ?_
          hpure.files_eq hpure.filesOkPeer hpure.decPkOk hpure.coins_lt htrusted
          hload_rel hcur hnot_match
          hsteps01 htr1 hfr1 hs1_sp hsp_sub hpc1 hrun1 hsp_align1 hregs1
        · intro evs2 m i k kp reg dk recG whisperG he2_raw hpm hi hk hkp hreg hacc hex
          have he2 := hOkEnv y.g r evs2 he2_raw
          intro evs3 he3_prev1
          unfold StageP3Prev1Env at he3_prev1
          split at he3_prev1
          · rcases he3_prev1 with ⟨G₁, hcl, he3_err⟩
            exact ((hfits_all.mono fun _ h =>
              Or.inr ⟨r, sess, hloadSome, hcur, hnot_match, htrusted,
                Or.inr ⟨m, i, k, kp, reg, dk, recG, whisperG,
                  hpm, hi, hk, hkp, hreg, hacc, hex,
                  Or.inl ⟨G₁, hcl, h⟩⟩⟩).seq_right (LibsignalBinary.Heap.SeqEnv.append hevs_p1 he2))
              evs3 (hp3Err _ _ _ _ _ _ _ _ _ he3_err)
          · exact ((hfits_all.mono fun _ h =>
              Or.inr ⟨r, sess, hloadSome, hcur, hnot_match, htrusted,
                Or.inr ⟨m, i, k, kp, reg, dk, recG, whisperG,
                  hpm, hi, hk, hkp, hreg, hacc, hex,
                  Or.inr (Or.inl h)⟩⟩).seq_right (LibsignalBinary.Heap.SeqEnv.append hevs_p1 he2))
              evs3 (hp3VerNe _ _ _ _ he3_prev1)
        · intro evs2 evs3 m i k kp reg dk recG G₁ whisperG he2_raw hpm hi hk hkp hreg hacc hex hcl he3
          exact Or.inr ⟨r, sess, hloadSome, hcur, hnot_match, htrusted,
            Or.inr ⟨m, i, k, kp, reg, dk, recG, whisperG, hpm, hi, hk, hkp, hreg, hacc, hex,
              Or.inl ⟨G₁, hcl,
                LibsignalBinary.Heap.SeqEnv.append (LibsignalBinary.Heap.SeqEnv.append hevs_p1 (hOkEnv y.g r evs2 he2_raw))
                  (hp3Err _ _ _ _ _ _ _ _ _ he3)⟩⟩⟩
        · intro evs2 evs3 m i k kp reg dk recG whisperG he2_raw hpm hi hk hkp hreg hacc hex he3
          exact Or.inr ⟨r, sess, hloadSome, hcur, hnot_match, htrusted,
            Or.inr ⟨m, i, k, kp, reg, dk, recG, whisperG, hpm, hi, hk, hkp, hreg, hacc, hex,
              Or.inr (Or.inl
                (LibsignalBinary.Heap.SeqEnv.append (LibsignalBinary.Heap.SeqEnv.append hevs_p1 (hOkEnv y.g r evs2 he2_raw))
                  (hp3VerNe _ _ _ _ he3)))⟩⟩
        · intro evs2 evs3 m i k kp reg dk recG G₁ G' pt whisperG
            he2_raw hpm hi hk hkp hreg hacc hex hcl hdec he3 hok _σ _pid _envs _st0 _ses' hgv'
          exact (hfits_all.mono fun _ h =>
            Or.inr ⟨r, sess, hloadSome, hcur, hnot_match, htrusted,
              Or.inr ⟨m, i, k, kp, reg, dk, recG, whisperG,
                hpm, hi, hk, hkp, hreg, hacc, hex,
                Or.inr (Or.inr ⟨G₁, G', pt, hcl, hdec, hok, hgv', h⟩)⟩⟩).seq_right
            (LibsignalBinary.Heap.SeqEnv.append (LibsignalBinary.Heap.SeqEnv.append hevs_p1 (hOkEnv y.g r evs2 he2_raw))
              (hp3Ok _ _ _ _ _ _ _ _ _ he3))
        · intro evs2 evs3 evs4 m i k kp reg dk recG G₁ G' pt whisperG
            he2_raw hpm hi hk hkp hreg hacc hex hcl hdec he3 hok _σ _pid _envs _st0 _ses' hgv' he4
          exact Or.inr ⟨r, sess, hloadSome, hcur, hnot_match, htrusted,
            Or.inr ⟨m, i, k, kp, reg, dk, recG, whisperG,
              hpm, hi, hk, hkp, hreg, hacc, hex,
              Or.inr (Or.inr ⟨G₁, G', pt, hcl, hdec, hok, hgv',
                LibsignalBinary.Heap.SeqEnv.append
                  (LibsignalBinary.Heap.SeqEnv.append (LibsignalBinary.Heap.SeqEnv.append hevs_p1 (hOkEnv y.g r evs2 he2_raw))
                    (hp3Ok _ _ _ _ _ _ _ _ _ he3))
                  he4⟩)⟩⟩

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonPollPathsPlacedBudgetFd
