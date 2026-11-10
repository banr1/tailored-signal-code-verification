/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.AgreePathACore
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureEntryPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathATopPlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBMainPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBTopPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureTrustedP1Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrusted
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage1InstPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1InstPlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.PollStmtPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureSpeOwned
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStmts
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.InitInv
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Auxiliary Lemmas for Budget-Threaded Relocatable `[LibsignalPlacement]` Poll Trusted Join

Defines reducible mirrors `CliStageP1OkEnv` and `CliDpPollTrustedEnv` and proves
`closure_trusted_branch_placed_ok_at` and `closure_trusted_placed_ok_at` accepting pointwise
`StageP2PathAQpanCliPlacedAtStmt`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.dupNamespace false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureTrustedP1PlacedBudgetAux

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  lsLogOff withLsCodeRoLoaded LibsignalCodeRoLoaded
  subroutine_ok_withLsCodeRoLoaded_of_plain
  subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalSpqrV1 hiding Bytes
open CryptoVerification.E2E
open CryptoVerification.E2E.Bin hiding encodeRecord
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.ResponderCore hiding Bytes
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding
  PanicOomProp Bytes eq_of_sep_emp outPtr48_split_eq decryptPrekeySavedRegsAt_add_cd0
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton hiding RunHooksPlaced
open CryptoVerification.SignalSession.Cli.RunCompose hiding
  Bytes dpSlotPollKStatePlaced slotFramePlaced decPkSlotSpecPlaced
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.KitInst hiding
  cliPreKeyStoreSpecPlaced cliSignedPreKeyStoreSpecPlaced cliKyberPreKeyStoreSpecPlaced
open CryptoVerification.SignalSession.Coins
open CryptoVerification.SignalSession.Coins.Placed
open CryptoVerification.SignalSession.Cli.RunProofs.Poll hiding
  dpPollEntrySpatialPlaced
  StageP2PathAQpanCliPlacedStmt
  stageP3_exit_pathA_to_pollPost_placed
  closure_pathA_placed_ok
  StageP2MatchedFramedCliPlacedStmt
  storesAt_opened_entails_cliPollStoresKitsAtPlaced
  sepWPp_pollGoal_frame_placed
  stageP3_exit_prevEmpty_to_pollPost_placed
  sepWPp_genP3_to_tailQpan_placed
  closure_pathB_placed_ok
  cliFiles_eq_of_trace_eq_placed
  cliPollStageP1_fsAt_placed
  cliPollStageP4Stack_placed_le_subStack
  cliPollStageP4MatchedStack_placed_le_subStack
  cliPollStageP4_fsAt_placed
  closure_pathA_p4_cont_placed
  stageP3ErrPathA_entails_exit_placed
  stageP3ErrPrevEmpty_entails_exit_placed
  pathAP4RemAtPlaced
  pathBP4RemAtPlaced
  stageP3MidPathA_eq_p4_placed
  stageP3MidPrevEmpty_eq_p4_placed
  stageP4PathAExit_entails_exit_placed
  stageP4MatchedExit_entails_exit_placed
  exit_entails_dpPollPost_placed
  sepWPp_genP3_to_pollGoal_placed
  closure_pathB_p4_cont_placed
  genP3Pre_placed genP3CallFrame_placed genP3S5PostFrame_placed
  stageP3DispatchOkMid_placed stageP3ErrPost_placed
  stageP3DispatchOkMidPrevEmpty_placed stageP3ErrPostPrevEmpty_placed
  stageP4SharedPlaced stageP4RawPrePlaced stageP4PrePlaced stageP4ExitAtPlaced
  StageP4RawBranchPlaced StageP4BranchPlaced StageP4PathAPlacedStmt
  stageP4MatchedSharedPlaced stageP4MatchedPrePlaced stageP4MatchedExitAtPlaced
  StageP4MatchedBranchPlaced StageP4MatchedPlacedStmt
  StageP2PathAErrPlaced StageP2PathACliPlacedStmt
  StageP3PrevEmptyVRegsPlacedStmt StageP3GenStepsVRegsPlacedStmt CliTryDecryptPqV1PlacedStmt
  closure_untrusted_placed_ok closure_trusted_placed_ok
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget SeqEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2BridgePlacedBudget (
  StageP2MatchedBridgeEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2TopPlacedBudget (
  StageP2MatchedEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (
  CliGhostHooks cliGhostExterns cliGhostExterns_other
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureEntryPlacedBudget (
  dpPollEntrySpatialPlaced dpPollPre_unpack_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathATopPlacedBudgetAux (
  closure_pathA_placed_ok_at p1Ok_recombine_entails_stageP2_placed_budget sepWPp_bind_p1_noPanic
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBMainPlacedBudget (
  StageP2MatchedFramedCliPlacedStmt closure_pathB_placed_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageDefsPlacedBudget (
  StageP1OkEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget (
  StageP3Env StageP3GenStepsVRegsPlacedStmt StageP3OkPrefixEnv pollTryDecryptPlacedSpecTPTight
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget (
  RunHooksPlaced StageP2PathAEnv StageP3PrevEmptyVRegsPlacedStmt StageP4MatchedEnv
  StageP4MatchedPlacedStmt StageP4PathAEnv StageP4PathAPlacedStmt
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget (
  CliDpPollUntrustedEnv cliPollStageP1_fsAt_placed closure_untrusted_placed_ok runHooks_to_stages
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage1InstPlacedBudget (
  stageP1_ok_placed_inst
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1InstPlacedBudgetAux (
  StageP2PathAQpanCliPlacedAtStmt
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget (
  cliPollIdBudgetEnv cliPollKpkBudgetEnv cliPollPkBudgetEnv cliPollSessBudgetEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.PollStmtPlacedBudget (
  CliDpPollOkStatePlacedAt
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget (
  DpPollGhostStateBudget dpPollSpecStateBudget dpSlotPollKStatePlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (
  readFileSpecPlaced sessDeserializeSpecPlaced
)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## 1. Concrete CLI Stage-P1 & Trusted Poll Allocation Envelopes (Reducible Mirrors) -/

/-- Concrete CLI Stage-P1 (`is_trusted_identity =.ok true`) allocation envelope at
`StoresGhost.opened` (definitionally identical to `ClosureTrustedP1PlacedBudget.CliStageP1OkEnv`). -/
@[reducible] def CliStageP1OkEnv [LibsignalPlacement] {A : RustAlloc}
    (B : RunBudgets)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (g : DecPkGhost) : List AllocEvent → Prop :=
  let σ := cliKitStk B
  StageP1OkEnv
    (cliPollSessKitPlaced A g.F Slots.scopeKit g.peer σ)
    (cliPollSessBudgetEnv A g.F g.peer σ DeserEnv ReadEnv)
    StoresGhost.opened.sessions
    (cliPollIdKitPlaced A g.F g.peer σ)
    (cliPollIdBudgetEnv A g.F g.peer σ ReadEnv)
    StoresGhost.opened.identity
    g.peer.val g.msg.identityKey

/-- Complete allocation-event envelope for `closure_trusted_placed_ok_at`, definitionally identical
to `ClosureTrustedP1PlacedBudget.CliDpPollTrustedEnv`. -/
@[reducible] def CliDpPollTrustedEnv [LibsignalPlacement] {A : RustAlloc}
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (P2PathAErrEnv P2PathAOkEnv : DecPkGhost → List AllocEvent → Prop)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (g : DecPkGhost) (evs : List AllocEvent) : Prop :=
  let σ := cliKitStk B
  let sessKit := cliPollSessKitPlaced A g.F Slots.scopeKit g.peer σ
  let kitEnv := cliPollSessBudgetEnv A g.F g.peer σ DeserEnv ReadEnv
  let idKit := cliPollIdKitPlaced A g.F g.peer σ
  let ikitEnv := cliPollIdBudgetEnv A g.F g.peer σ ReadEnv
  let P1 := CliStageP1OkEnv (A := A) B ReadEnv DeserEnv g
  CliDpPollUntrustedEnv (A := A) B ReadEnv DeserEnv g evs ∨
  P1 evs ∨
  (sessKit.loadRel StoresGhost.opened.sessions g.peer.val (.ok none) ∧
    (SeqEnv P1 (StageP2PathAEnv P2PathAErrEnv P2PathAOkEnv g) evs ∨
     ∃ m i k kp reg dk recG,
       g.msg = pmOfE m i ∧
       SignalMessage.tryFrom CryptoVerification.LibsignalProtoCodec.protoSignalCodec m.inner = .ok i ∧
       pkStoreKeys g.F m = some k ∧
       StoresGhost.opened.identity.keyPair cliIo.rd g.F = .ok kp ∧
       StoresGhost.opened.identity.regId cliIo.rd g.F = .ok reg ∧
       SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
         (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk ∧
       SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) ∧
       (SeqEnv (SeqEnv P1 (P2PathAOkEnv g))
          (StageP3Env tdEnv recG (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
            g.peer g.me g.msgG.msg g.msg.message
            (g.msg.message.messageVersion.zeroExtend 32) g.coins) evs ∨
        ∃ G₁ G' pt,
          (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk).version =
            g.msg.message.messageVersion.zeroExtend 32 ∧
          CryptoVerification.LibsignalTripleRatchet.Record.CloneRel recG G₁ ∧
          G₁.AfterTryDecrypt true G' ∧
          (genP3S5Model W.C W.Q.K g.peer g.me g.msg.message g.coins
            (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)).1 = .ok pt ∧
          SeqEnv
            (SeqEnv (SeqEnv P1 (P2PathAOkEnv g))
              (StageP3OkPrefixEnv tdEnv recG G₁
                (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
                g.peer g.me g.msgG.msg g.msg.message g.coins))
            (StageP4PathAEnv
              sessKit kitEnv idKit ikitEnv
              (cliPollPkKitPlaced A g.F (pmPreKeyId g.msg) σ)
              (cliPollPkBudgetEnv A g.F (pmPreKeyId g.msg) σ ReadEnv)
              (cliPollKpkKitPlaced A g.F m.kpkId m.spkId g.msg.baseKey σ)
              (cliPollKpkBudgetEnv A g.F m.kpkId m.spkId g.msg.baseKey σ ReadEnv)
              StoresGhost.opened.sessions StoresGhost.opened.identity
              StoresGhost.opened.oneTime StoresGhost.opened.kyber
              g.peer.val g.msg.identityKey m.opkId m.kpkId m.spkId g.msg.baseKey
              { pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk with
                state := (genP3S5Model W.C W.Q.K g.peer g.me g.msg.message g.coins
                  (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)).2
                pendingPreKey := none
                pendingKyberPreKey := none }) evs))) ∨
  (∃ (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8))),
    sessKit.loadRel StoresGhost.opened.sessions g.peer.val (.ok (some r)) ∧
    r.currentSession = some sess ∧
    (SeqEnv P1 (StageP2MatchedEnv sess g.msg.identityKey) evs ∨
     (sess.state.remoteIdentity = some g.msg.identityKey ∧
      ∃ recG, SessionExtraRel recG sess ∧
        (SeqEnv (SeqEnv P1 StageP2MatchedBridgeEnv)
           (StageP3Env tdEnv recG sess.state g.peer g.me g.msgG.msg g.msg.message
             (g.msg.message.messageVersion.zeroExtend 32) g.coins) evs ∨
         (sess.state.version = g.msg.message.messageVersion.zeroExtend 32 ∧
          ∃ G₁ G' pt,
            CryptoVerification.LibsignalTripleRatchet.Record.CloneRel recG G₁ ∧
            G₁.AfterTryDecrypt true G' ∧
            (genP3S5Model W.C W.Q.K g.peer g.me g.msg.message g.coins sess.state).1 = .ok pt ∧
            SeqEnv
              (SeqEnv (SeqEnv P1 StageP2MatchedBridgeEnv)
                (StageP3OkPrefixEnv tdEnv recG G₁ sess.state g.peer g.me g.msgG.msg
                  g.msg.message g.coins))
              (StageP4MatchedEnv sessKit kitEnv idKit ikitEnv
                StoresGhost.opened.sessions StoresGhost.opened.identity
                g.peer.val g.msg.identityKey
                { sess with
                  state := (genP3S5Model W.C W.Q.K g.peer g.me g.msg.message g.coins sess.state).2
                  pendingPreKey := none
                  pendingKyberPreKey := none }) evs)))))

/-! ## 2. Trusted-Identity Branch & Full Poll Closure (`closure_trusted_placed_ok_at`) -/

set_option maxHeartbeats 1200000 in
/-- Trusted-identity branch (`trusted =.ok true`) of `subroutine_ok_of_sepWPp_steps` for
Block `518` under `[LibsignalPlacement]`: runs `Stage1InstPlacedBudget.stageP1_ok_placed_inst`,
reassembles `stageP2PostP1At`, and dispatches on `opt` to `closure_pathA_placed_ok_at` (`opt = none`)
or `closure_pathB_placed_ok` (`opt = some r`). -/
theorem closure_trusted_branch_placed_ok_at [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv P2PathAErrEnv P2PathAOkEnv : DecPkGhost → List AllocEvent → Prop}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hP2A : StageP2PathAQpanCliPlacedAtStmt A lim ReadEnv X mmpl gh W B P2PathAErrEnv P2PathAOkEnv)
    (hP3A : StageP3GenStepsVRegsPlacedStmt)
    (hP4A : StageP4PathAPlacedStmt)
    (hP2M : StageP2MatchedFramedCliPlacedStmt)
    (hP3M : StageP3PrevEmptyVRegsPlacedStmt)
    (hP4M : StageP4MatchedPlacedStmt)
    (hh_skel : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hReadFile : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced Slots.scopeKit A lim DeserEnv))
    (hTryDec : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (StoreKit.withLsCodeRoLoaded lsmpl
        (pollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse (spqrV1 W.C.F W.Q.K) tdEnv)))
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (hfits_all : FitsEnv M lim y.st
      (CliDpPollTrustedEnv (A := A.repAlloc) W X B ReadEnv DeserEnv
        P2PathAErrEnv P2PathAOkEnv tdEnv y.g))
    (hEnv : ∀ evs,
      CliDpPollTrustedEnv (A := A.repAlloc) W X B ReadEnv DeserEnv
        P2PathAErrEnv P2PathAOkEnv tdEnv y.g evs →
      DecPkEnv y.g evs)
    (R : SepProp) (s0 : State)
    (hpc : s0.pc = dpPollEntryPlaced)
    (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true)
    (hstk_sp : stk' ≤ s0.sp.toNat)
    (hro0 : StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem)
    (hx0 : s0.readReg64 .x0 = y.out)
    (hx1 : s0.readReg64 .x1 = y.fut)
    (hx2 : s0.readReg64 .x2 = y.cx)
    (hfiles0 : s0.fs.files = y.g.F)
    (hfPeer : Slots.FilesOkPeer Scope y.g.F y.g.peer.val)
    (hdecOk : DecPkOk₀ ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (hcoins : y.g.coins.length < 2 ^ 63)
    (htrusted : StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
      y.g.msg.identityKey = .ok true)
    (hm_base : s0.mem ⊨ dpPollEntrySpatialPlaced stk' y s0 R) :
    let prog := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))
    let K := dpSlotPollKStatePlaced A lim DecPkEnv B S
    ∃ P Fr : SepProp, (s0.mem ⊨ P ∗ Fr) ∧
      SepWPp prog (s0.readReg64 Reg.lr) s0 P
        (fun sf P_f =>
          (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (StoreKit.withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')).post y s0 sf ∗ R)) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f =>
          Steps prog s0 sf → (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (StoreKit.withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')).onPanic y s0 sf ∗ R)) := by
  dsimp only
  dsimp only [dpPollEntrySpatialPlaced] at hm_base
  have hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
    runHooks_to_stages hh_skel
  let σ := cliKitStk B
  let pid := pmPreKeyId y.g.msg
  let sid := y.g.msg.signedPreKeyId
  let kid := pmKyberId y.g.msg
  let kbk := y.g.msg.baseKey
  let kit := cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer σ
  let ikit := cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ
  let pkKit := cliPollPkKitPlaced A.repAlloc y.g.F pid σ
  let spkKit := cliPollSpkKitPlaced A.repAlloc y.g.F sid σ
  let kpkKit := cliPollKpkKitPlaced A.repAlloc y.g.F kid sid kbk σ
  let kitEnv := cliPollSessBudgetEnv A.repAlloc y.g.F y.g.peer σ DeserEnv ReadEnv
  let ikitEnv := cliPollIdBudgetEnv A.repAlloc y.g.F y.g.peer σ ReadEnv
  let pkKitEnv := cliPollPkBudgetEnv A.repAlloc y.g.F pid σ ReadEnv
  let kpkKitEnv := fun kpkId spkId =>
    cliPollKpkBudgetEnv A.repAlloc y.g.F kpkId spkId kbk σ ReadEnv
  let sp := s0.sp - 0xcd0#64
  have hsp_align0 : (s0.sp &&& 15#64 == 0#64) = true := by
    simpa [State.spAligned] using hsp
  have hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat :=
    (subStack_le_sp_of_dpPollNeed hneed hstk_sp).1
  have hent_stores := storesAt_entails_cliPollStoresKitsAtPlaced (A := A.repAlloc)
    (F0 := y.g.F) (Scope := Slots.scopeKit) (peer := y.g.peer)
    (pid := pid) (sid := sid) (kid := kid) (kbk := kbk) σ
    y.g.stores StoresGhost.opened
    (cliSessInv_opened_scopeKit hsub hfPeer)
    (cliIdOwnInv_opened hdecOk)
    (cliIdInv_opened_peer hfPeer)
    (cliPkInv_opened hdecOk pid)
    (cliSpkInv_opened hdecOk sid)
    (cliKpkInvFull_opened hdecOk kid sid kbk)
  have hm_stores : s0.mem ⊨
      memRegion y.out 48 ∗
        dpFutStartAt y.fut (dpSlotArgsPlaced y.g) ∗
        memRegion y.cx 32 ∗
        cliPollStoresKitsAtPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer
          pid sid kid kbk σ y.g.stores StoresGhost.opened ∗
        protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
        protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
        coinsInstalledPlaced y.g.coinsP y.g.coins ∗
        LsTokenInit ∗
        FromRecordCallees.lsLogOff ∗
        A.pool lim y.st s0 ∗
        preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
        stackAt s0.sp stk' ∗
        R :=
    Satisfies.mono (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left hent_stores)))) hm_base
  have hsub64 : dpClosSubStack B ≤ 2 ^ 64 := by
    have := dpPollNeed_eq_frame_add_subStack B; omega
  have hp1_le := stageP1CallStack_le_subStack (A := A.repAlloc)
    0#64 y.g.F Slots.scopeKit y.g.peer B
  have hp1_64 : stageP1CallStack kit ikit ≤ 2 ^ 64 := Nat.le_trans hp1_le hsub64
  rw [dpFutStartAt_split_for_p1_placed y.g y.fut,
      preKeyMsgAt_eq_idKey_sep A.repAlloc y.g.msgG y.g.msgA y.g.msg,
      stackAt_poll_entry_split s0.sp B stk' hneed hstk63,
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
    FromRecordCallees.lsLogOff ∗
    kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
    ikit.identityAt y.g.stores StoresGhost.opened.identity ∗
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
    pkKit.storeAt (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
    spkKit.storeAt (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
    kpkKit.storeAt (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
    dirAt A.repAlloc (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
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
    hfits_all.mono fun _ h => Or.inr (Or.inl h)
  have hwp := stageP1_ok_placed_inst hDropNz mmpl gh W B y.g.F y.g.peer y.g.msg.identityKey
    hh hReadFile hDeser y.st StoresGhost.opened.sessions StoresGhost.opened.identity
    hp1_64 rfl rfl
    (fun _ (h : (cliPollSessKit A.repAlloc 0#64 y.g.F Slots.scopeKit y.g.peer σ).loadRel
      StoresGhost.opened.sessions y.g.peer.val _) => cliSess_loadRel_isOk h)
    (fun _ (h : (cliPollIdKit A.repAlloc 0#64 y.g.F y.g.peer σ).trustRel
      StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey .receiving _) =>
      cliId_trustRel_eq_of_trusted htrusted h)
    hfits_p1
    s0 sp y.out y.fut y.cx y.g.msgA y.g.peerA y.g.meA
    (y.g.stores + 0xf0#64) y.g.stores
    (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
    (y.g.stores + 0x78#64) kpkKit.kpk_vt coins
    v_sp0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0
    b_390 b_4f2
    hro0
    (cliPollStageP1_fsAt_placed hh_skel y.g.F Slots.scopeKit y.g.peer B hfiles0)
    hpc hrun hsp_align0 rfl hx0 hx1 hx2
  refine sepWPp_bind_p1_noPanic hwp rfl ?_
  intro s1 P_1 hsteps01 hpc1 hrun1 hq1
  rcases hq1 with ⟨⟨opt, evs_p1, hevs_p1, hload_rel, _htrust_rel, htr_evs, hent_1⟩,
    hs1_sp, hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16, hx17,
    hx19, hx20, hx22, hx23, hx24, hx25, hx28, hx29, hvregs1, hro1⟩
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
  have hrecomb := p1Ok_recombine_entails_stageP2_placed_budget stk' hneed hstk63 y
    (M.stepEvents evs_p1 y.st) s0 s1 coins v_a8 v_b8 v_d0 opt
  dsimp only at hrecomb
  refine sepWPp_conseq_pre hrecomb ?_
  cases opt with
  | none =>
    have hfits_p2 :
        FitsEnv M lim (M.stepEvents evs_p1 y.st)
          (StageP2PathAEnv P2PathAErrEnv P2PathAOkEnv y.g) :=
      (hfits_all.mono fun _ h =>
        Or.inr (Or.inr (Or.inl ⟨hload_rel, Or.inl h⟩))).seq_right hevs_p1
    have hevs_p2_err : ∀ evs_p2, P2PathAErrEnv y.g evs_p2 → DecPkEnv y.g (evs_p1 ++ evs_p2) :=
      fun evs_p2 he2 =>
        hEnv _ (Or.inr (Or.inr (Or.inl
          ⟨hload_rel, Or.inl (SeqEnv.append hevs_p1 (Or.inl he2))⟩)))
    refine closure_pathA_placed_ok_at mmpl gh W X B S Scope hP2A hP3A hP4A hh hReadFile hDeser hTryDec
      hinjK hsub hS stk' hneed hstk63 y kitEnv ikitEnv pkKitEnv kpkKitEnv evs_p1 s0 s1 coins
      v_a8 v_b8 v_d0 R hfiles0 hfPeer hdecOk hcoins htrusted hload_rel hfits_p2 hevs_p2_err
      ?_ ?_ ?_ ?_ ?_ ?_
      hsteps01 htr1 hro1 hs1_sp hsp_sub hpc1 hrun1 hsp_align1 hregs1
    · intro evs_p2 m i k kp reg dk recG he2 hpm hi hk hkp hreg hacc hex
      exact (hfits_all.mono fun _ h =>
        Or.inr (Or.inr (Or.inl ⟨hload_rel, Or.inr ⟨m, i, k, kp, reg, dk, recG,
          hpm, hi, hk, hkp, hreg, hacc, hex, Or.inl h⟩⟩))).seq_right
        (SeqEnv.append hevs_p1 he2)
    · intro evs_p2 m i k kp reg dk recG G₁ G' evs_p3 pt he2 hpm hi hk hkp hreg hacc hex
        hver hcl hdec he3 hok
      exact (hfits_all.mono fun _ h =>
        Or.inr (Or.inr (Or.inl ⟨hload_rel, Or.inr ⟨m, i, k, kp, reg, dk, recG,
          hpm, hi, hk, hkp, hreg, hacc, hex,
          Or.inr ⟨G₁, G', pt, hver, hcl, hdec, hok, h⟩⟩⟩))).seq_right
        (SeqEnv.append (SeqEnv.append hevs_p1 he2) he3)
    · intro evs_p2 m i k kp reg dk recG G₁ G' evs_p3 pt evs_p4 he2 hpm hi hk hkp hreg hacc hex
        hver hcl hdec he3 hok he4
      exact hEnv _ (Or.inr (Or.inr (Or.inl ⟨hload_rel, Or.inr ⟨m, i, k, kp, reg, dk, recG,
        hpm, hi, hk, hkp, hreg, hacc, hex,
        Or.inr ⟨G₁, G', pt, hver, hcl, hdec, hok,
          SeqEnv.append (SeqEnv.append (SeqEnv.append hevs_p1 he2) he3)
            (Or.inr (Or.inr (Or.inr he4)))⟩⟩⟩)))
    · intro evs_p2 m i k kp reg dk recG G₁ G' evs_p3 pt evs_p4 he2 hpm hi hk hkp hreg hacc hex
        hver hcl hdec he3 hok he4
      exact hEnv _ (Or.inr (Or.inr (Or.inl ⟨hload_rel, Or.inr ⟨m, i, k, kp, reg, dk, recG,
        hpm, hi, hk, hkp, hreg, hacc, hex,
        Or.inr ⟨G₁, G', pt, hver, hcl, hdec, hok,
          SeqEnv.append (SeqEnv.append (SeqEnv.append hevs_p1 he2) he3)
            (Or.inr (Or.inl he4))⟩⟩⟩)))
    · intro evs_p2 m i k kp reg dk recG G₁ G' evs_p3 e he2 hpm hi hk hkp hreg hacc hex
        hver hcl _hdec he3 _herr _hne
      have he3_env : StageP3Env tdEnv recG (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
          y.g.peer y.g.me y.g.msgG.msg y.g.msg.message
          (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins evs_p3 := by
        unfold StageP3Env
        simp only [hver, ↓reduceIte]
        exact ⟨G₁, hcl, he3⟩
      exact hEnv _ (Or.inr (Or.inr (Or.inl ⟨hload_rel, Or.inr ⟨m, i, k, kp, reg, dk, recG,
        hpm, hi, hk, hkp, hreg, hacc, hex,
        Or.inl (SeqEnv.append (SeqEnv.append hevs_p1 he2) he3_env)⟩⟩)))
    · intro evs_p2 m i k kp reg dk recG evs_p3 he2 hpm hi hk hkp hreg hacc hex hver_ne he3
      have he3_env : StageP3Env tdEnv recG (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
          y.g.peer y.g.me y.g.msgG.msg y.g.msg.message
          (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins evs_p3 := by
        unfold StageP3Env
        simp only [hver_ne, ↓reduceIte]
        exact he3
      exact hEnv _ (Or.inr (Or.inr (Or.inl ⟨hload_rel, Or.inr ⟨m, i, k, kp, reg, dk, recG,
        hpm, hi, hk, hkp, hreg, hacc, hex,
        Or.inl (SeqEnv.append (SeqEnv.append hevs_p1 he2) he3_env)⟩⟩)))
  | some r =>
    obtain ⟨sess, hcur⟩ := currentSession_some_of_cliPollSessPlaced_loadRel hload_rel
    have hfits_p2 :
        FitsEnv M lim (M.stepEvents evs_p1 y.st)
          (StageP2MatchedEnv sess y.g.msg.identityKey) :=
      (hfits_all.mono fun _ h =>
        Or.inr (Or.inr (Or.inr ⟨r, sess, hload_rel, hcur, Or.inl h⟩))).seq_right hevs_p1
    refine closure_pathB_placed_ok hP2M hP3M hP4M mmpl gh W X B S Scope hh hReadFile hDeser hTryDec
      hinjK hsub hS stk' hneed hstk63 y kitEnv ikitEnv evs_p1 r sess s0 s1 coins v_a8 v_b8 v_d0 R
      hfiles0 hfPeer hdecOk hcoins htrusted hload_rel hcur hfits_p2
      ?_ ?_ ?_ ?_ ?_ ?_
      hsteps01 htr1 hro1 hs1_sp hsp_sub hpc1 hrun1 hsp_align1 hregs1
    · intro hne evs_p2 he2
      have he2_env : StageP2MatchedEnv sess y.g.msg.identityKey evs_p2 := by
        unfold StageP2MatchedEnv
        simp only [hne, ↓reduceIte]
        exact he2
      exact hEnv _ (Or.inr (Or.inr (Or.inr
        ⟨r, sess, hload_rel, hcur, Or.inl (SeqEnv.append hevs_p1 he2_env)⟩)))
    · intro hrem evs_p2 recG he2 hex
      exact (hfits_all.mono fun _ h =>
        Or.inr (Or.inr (Or.inr ⟨r, sess, hload_rel, hcur,
          Or.inr ⟨hrem, recG, hex, Or.inl h⟩⟩))).seq_right (SeqEnv.append hevs_p1 he2)
    · intro hrem hver evs_p2 recG G₁ G' evs_p3 pt he2 hex hcl hdec he3 hok
      exact (hfits_all.mono fun _ h =>
        Or.inr (Or.inr (Or.inr ⟨r, sess, hload_rel, hcur,
          Or.inr ⟨hrem, recG, hex, Or.inr ⟨hver, G₁, G', pt, hcl, hdec, hok, h⟩⟩⟩))).seq_right
        (SeqEnv.append (SeqEnv.append hevs_p1 he2) he3)
    · intro hrem hver evs_p2 recG G₁ G' evs_p3 pt evs_p4 he2 hex hcl hdec he3 hok he4
      exact hEnv _ (Or.inr (Or.inr (Or.inr ⟨r, sess, hload_rel, hcur,
        Or.inr ⟨hrem, recG, hex, Or.inr ⟨hver, G₁, G', pt, hcl, hdec, hok,
          SeqEnv.append (SeqEnv.append (SeqEnv.append hevs_p1 he2) he3) (Or.inr he4)⟩⟩⟩)))
    · intro hrem hver evs_p2 recG G₁ G' evs_p3 e he2 hex hcl _hdec he3 _herr _hne
      have he3_env : StageP3Env tdEnv recG sess.state y.g.peer y.g.me y.g.msgG.msg y.g.msg.message
          (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins evs_p3 := by
        unfold StageP3Env
        simp only [hver, ↓reduceIte]
        exact ⟨G₁, hcl, he3⟩
      exact hEnv _ (Or.inr (Or.inr (Or.inr ⟨r, sess, hload_rel, hcur,
        Or.inr ⟨hrem, recG, hex,
          Or.inl (SeqEnv.append (SeqEnv.append hevs_p1 he2) he3_env)⟩⟩)))
    · intro hrem hver_ne evs_p2 recG evs_p3 he2 hex he3
      have he3_env : StageP3Env tdEnv recG sess.state y.g.peer y.g.me y.g.msgG.msg y.g.msg.message
          (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins evs_p3 := by
        unfold StageP3Env
        simp only [hver_ne, ↓reduceIte]
        exact he3
      exact hEnv _ (Or.inr (Or.inr (Or.inr ⟨r, sess, hload_rel, hcur,
        Or.inr ⟨hrem, recG, hex,
          Or.inl (SeqEnv.append (SeqEnv.append hevs_p1 he2) he3_env)⟩⟩)))

private theorem withPanics_cliGhostExterns_eq (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks) :
    Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W)) =
      cliGhostExterns gh (cliExternsPlaced mmpl W) := by
  funext s
  by_cases hp : Rust.isPanicSymbol s = true
  · have hother : cliGhostExterns gh (cliExternsPlaced mmpl W) s = cliExternsPlaced mmpl W s :=
      cliGhostExterns_other gh (cliExternsPlaced mmpl W)
        (fun h => by subst h; simp [Rust.isPanicSymbol, CryptoVerification.SignalSession.lsRustAllocSymCli, CryptoVerification.SignalSession.lsRustDeallocSymCli, CryptoVerification.SignalSession.lsRustReallocSymCli, CryptoVerification.SignalSession.lsRustAllocZeroedSymCli, CryptoVerification.SignalSession.lsRustNoAllocShimSymCli, CryptoVerification.SignalSession.lsStringCloneSym] at hp)
        (fun h => by subst h; simp [Rust.isPanicSymbol, CryptoVerification.SignalSession.lsRustAllocSymCli, CryptoVerification.SignalSession.lsRustDeallocSymCli, CryptoVerification.SignalSession.lsRustReallocSymCli, CryptoVerification.SignalSession.lsRustAllocZeroedSymCli, CryptoVerification.SignalSession.lsRustNoAllocShimSymCli, CryptoVerification.SignalSession.lsStringCloneSym] at hp)
        (fun h => by subst h; simp [Rust.isPanicSymbol, CryptoVerification.SignalSession.lsRustAllocSymCli, CryptoVerification.SignalSession.lsRustDeallocSymCli, CryptoVerification.SignalSession.lsRustReallocSymCli, CryptoVerification.SignalSession.lsRustAllocZeroedSymCli, CryptoVerification.SignalSession.lsRustNoAllocShimSymCli, CryptoVerification.SignalSession.lsStringCloneSym] at hp)
        (fun h => by subst h; simp [Rust.isPanicSymbol, CryptoVerification.SignalSession.lsRustAllocSymCli, CryptoVerification.SignalSession.lsRustDeallocSymCli, CryptoVerification.SignalSession.lsRustReallocSymCli, CryptoVerification.SignalSession.lsRustAllocZeroedSymCli, CryptoVerification.SignalSession.lsRustNoAllocShimSymCli, CryptoVerification.SignalSession.lsStringCloneSym] at hp)
        (fun h => by subst h; simp [Rust.isPanicSymbol, CryptoVerification.SignalSession.lsRustAllocSymCli, CryptoVerification.SignalSession.lsRustDeallocSymCli, CryptoVerification.SignalSession.lsRustReallocSymCli, CryptoVerification.SignalSession.lsRustAllocZeroedSymCli, CryptoVerification.SignalSession.lsRustNoAllocShimSymCli, CryptoVerification.SignalSession.lsStringCloneSym] at hp)
        (fun h => by subst h; simp [Rust.isPanicSymbol, CryptoVerification.SignalSession.lsRustAllocSymCli, CryptoVerification.SignalSession.lsRustDeallocSymCli, CryptoVerification.SignalSession.lsRustReallocSymCli, CryptoVerification.SignalSession.lsRustAllocZeroedSymCli, CryptoVerification.SignalSession.lsRustNoAllocShimSymCli, CryptoVerification.SignalSession.lsStringCloneSym] at hp)
        (fun h => by subst h; simp [Rust.isPanicSymbol, CryptoVerification.SignalSession.lsReadFileSym] at hp)
        (fun h => by subst h; simp [Rust.isPanicSymbol, CryptoVerification.SignalSession.lsReadStdinSym] at hp)
        (fun h => by subst h; simp [Rust.isPanicSymbol, CryptoVerification.SignalSession.lsMemsetSym] at hp)
        (fun h => by subst h; simp [Rust.isPanicSymbol, CryptoVerification.SignalSession.lsMemcpySym] at hp)
    unfold Rust.withPanics
    rw [hother]
    unfold cliExternsPlaced isCliPanicSymbolPlaced
    simp [hp]
  · simp [Rust.withPanics, hp]

/-- Full budget-threaded `[LibsignalPlacement]` `decrypt_prekey` poll closure (`dpPollEntryPlaced`)
at fixed `(mmpl, gh, W, X, B, S, Scope)` accepting pointwise `StageP2PathAQpanCliPlacedAtStmt`. -/
theorem closure_trusted_placed_ok_at [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv P2PathAErrEnv P2PathAOkEnv : DecPkGhost → List AllocEvent → Prop}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hP2A : StageP2PathAQpanCliPlacedAtStmt A lim ReadEnv X mmpl gh W B P2PathAErrEnv P2PathAOkEnv)
    (hP3A : StageP3GenStepsVRegsPlacedStmt)
    (hP4A : StageP4PathAPlacedStmt)
    (hP2B : StageP2MatchedFramedCliPlacedStmt)
    (hP3B : StageP3PrevEmptyVRegsPlacedStmt)
    (hP4B : StageP4MatchedPlacedStmt)
    (hTryDec : subroutine_ok (DecryptPrekeyHelpers.dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (StoreKit.withLsCodeRoLoaded lsmpl
        (pollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse (spqrV1 W.C.F W.Q.K) tdEnv)))
    (hEnv : ∀ g evs,
      CliDpPollTrustedEnv (A := A.repAlloc) W X B ReadEnv DeserEnv
        P2PathAErrEnv P2PathAOkEnv tdEnv g evs →
      DecPkEnv g evs) :
    CliDpPollOkStatePlacedAt A lim ReadEnv DeserEnv DecPkEnv mmpl gh W X B S Scope := by
  intro hh hReadFile hDeser hinjK hsub hS hSemOk stk' hneed hstk63
  have hProg : DecryptPrekeyHelpers.dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)) =
      dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)) := by
    dsimp only [DecryptPrekeyHelpers.dpPollProgPlaced, dpPollProgPlaced, stageP1ProgPlaced]
    rw [withPanics_cliGhostExterns_eq mmpl gh W]
  have hEntry : DecryptPrekeyHelpers.dpPollEntryPlaced = dpPollEntryPlaced := rfl
  rw [hProg] at hReadFile hDeser hTryDec ⊢
  rw [hEntry]
  have hneed' : dpPollNeed B ≤ stk' := hneed
  apply subroutine_ok_of_sepWPp_steps
  intro y R s0 hpc hrun hpre hsp
  obtain ⟨hpure, hm_base⟩ :=
    dpPollPre_unpack_placed (W := W) (X := X) (B := B) (S := S) (Scope := Scope)
      hSemOk stk' y R s0 hpre
  have hfits_all : FitsEnv M lim y.st
      (CliDpPollTrustedEnv (A := A.repAlloc) W X B ReadEnv DeserEnv
        P2PathAErrEnv P2PathAOkEnv tdEnv y.g) :=
    hpure.fits.mono (hEnv y.g)
  obtain ⟨b, htrusted⟩ :=
    trusted_ok_of_filesOkPeer (peer := y.g.peer) hpure.filesOkPeer y.g.msg.identityKey
  cases b with
  | false =>
    dsimp only [dpPollEntrySpatialPlaced] at hm_base
    exact closure_untrusted_placed_ok A lim hDropNz mmpl gh W X B S Scope hh hReadFile hDeser
      hinjK hsub hS stk' hneed' hstk63 y
      (hfits_all.mono fun _ h => Or.inl h)
      (fun evs h => hEnv y.g evs (Or.inl h))
      R s0 hpc hrun hsp
      hpure.ro hpure.x0 hpure.x1 hpure.x2 hpure.files_eq hpure.filesOkPeer hpure.decPkOk
      htrusted hm_base
  | true =>
    exact closure_trusted_branch_placed_ok_at hDropNz mmpl gh W X B S Scope
      hP2A hP3A hP4A hP2B hP3B hP4B hh hReadFile hDeser hTryDec hinjK hsub hS
      stk' hneed' hstk63 y hfits_all (hEnv y.g) R s0 hpc hrun hsp hpure.stk_le_sp
      hpure.ro hpure.x0 hpure.x1 hpure.x2 hpure.files_eq hpure.filesOkPeer hpure.decPkOk
      hpure.coins_lt htrusted hm_base

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureTrustedP1PlacedBudgetAux
