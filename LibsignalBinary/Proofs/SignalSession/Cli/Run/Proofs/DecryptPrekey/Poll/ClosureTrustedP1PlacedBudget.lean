/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.AgreePathACore
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureEntryPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathATopPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBMainPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBTopPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureTrustedP1Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrusted
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage1InstPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.PollStmtPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureTrustedP1PlacedBudgetAux

/-!
# Budget-Threaded Relocatable `[LibsignalPlacement]` Poll Trusted Entry and Path A/B Join

Joins `ClosureUntrustedPlacedBudget.closure_untrusted_placed_ok`,
`Stage1InstPlacedBudget.stageP1_ok_placed_inst`, `ClosurePathATopPlacedBudget.closure_pathA_placed_ok`,
and `ClosurePathBMainPlacedBudget.closure_pathB_placed_ok` under `[LibsignalPlacement]` and the
allocation envelope `CliDpPollTrustedEnv`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.dupNamespace false
set_option warningAsError false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureTrustedP1PlacedBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (SignalMessage)
open CryptoGames.LibsignalSessionApi (Session SessionRecord)
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3 (genP3S5Model)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (SessionExtraRel)
open CryptoVerification.E2E (
  PreKeyMessageFields UnreachedPqxdhPrimitives acceptInput modelPrims
)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles withLsCodeRoLoaded)
open CryptoVerification.LibsignalSpqrV1 (spqrV1)
open CryptoVerification.LibsignalTripleRatchet.Record (CloneRel)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli (StoresGhost)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo)
open CryptoVerification.SignalSession.Cli.RunCompose (DecPkGhost RunSem)
open CryptoVerification.SignalSession.Cli.RunProofs (pkStoreKeys pmOfE)
open CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers (dpPollProgPlaced)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (
  cliKitStk cliPollIdKitPlaced cliPollKpkKitPlaced cliPollPkKitPlaced cliPollSessKitPlaced
  pathAInitSession pathAInitState pmPreKeyId
)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (scopeKit)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget SeqEnv)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2BridgePlacedBudget (
  StageP2MatchedBridgeEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2TopPlacedBudget (
  StageP2MatchedEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (
  CliGhostHooks cliGhostExterns
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathATopPlacedBudget (
  StageP2PathAQpanCliPlacedStmt
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBMainPlacedBudget (
  StageP2MatchedFramedCliPlacedStmt
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageDefsPlacedBudget (
  StageP1OkEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget (
  StageP3Env StageP3GenStepsVRegsPlacedStmt StageP3OkPrefixEnv pollTryDecryptPlacedSpecTPTight
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget (
  StageP2PathAEnv StageP3PrevEmptyVRegsPlacedStmt StageP4MatchedEnv StageP4MatchedPlacedStmt
  StageP4PathAEnv StageP4PathAPlacedStmt
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget (
  CliDpPollUntrustedEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget (
  cliPollIdBudgetEnv cliPollKpkBudgetEnv cliPollPkBudgetEnv cliPollSessBudgetEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.PollStmtPlacedBudget (
  CliDpPollOkStatePlacedAt CliDpPollOkStatePlacedStmt
)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)

/-- Bundle of Path A and Path B stage statements consumed by `closure_trusted_placed_ok`
(Stage P1 is discharged directly via `Stage1InstPlacedBudget.stageP1_ok_placed_inst`). -/
structure PollBaseStagesPlacedStmt [LibsignalPlacement] : Prop where
  stageP2PathA : StageP2PathAQpanCliPlacedStmt
  stageP3PathA : StageP3GenStepsVRegsPlacedStmt
  stageP4PathA : StageP4PathAPlacedStmt
  stageP2PathB : StageP2MatchedFramedCliPlacedStmt
  stageP3PathB : StageP3PrevEmptyVRegsPlacedStmt
  stageP4PathB : StageP4MatchedPlacedStmt

/-- Concrete CLI Stage-P1 (`is_trusted_identity =.ok true`) allocation envelope at `StoresGhost.opened`. -/
def CliStageP1OkEnv [LibsignalPlacement] {A : RustAlloc}
    (B : RunBudgets)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (g : DecPkGhost) : List AllocEvent → Prop :=
  let σ := cliKitStk B
  StageP1OkEnv
    (cliPollSessKitPlaced A g.F scopeKit g.peer σ)
    (cliPollSessBudgetEnv A g.F g.peer σ DeserEnv ReadEnv)
    StoresGhost.opened.sessions
    (cliPollIdKitPlaced A g.F g.peer σ)
    (cliPollIdBudgetEnv A g.F g.peer σ ReadEnv)
    StoresGhost.opened.identity
    g.peer.val g.msg.identityKey

/-- Complete allocation-event envelope for `closure_trusted_placed_ok`, covering untrusted rejection,
Stage P1 (`CliStageP1OkEnv`), Path A (`opt = none`, Stages P2–P4), and Path B (`opt = some r`,
`previousSessions = []`, Stages P2–P4). -/
def CliDpPollTrustedEnv [LibsignalPlacement] {A : RustAlloc}
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (P2PathAErrEnv P2PathAOkEnv : DecPkGhost → List AllocEvent → Prop)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (g : DecPkGhost) (evs : List AllocEvent) : Prop :=
  let σ := cliKitStk B
  let sessKit := cliPollSessKitPlaced A g.F scopeKit g.peer σ
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
       SignalMessage.tryFrom protoSignalCodec m.inner = .ok i ∧
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
          CloneRel recG G₁ ∧
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
            CloneRel recG G₁ ∧
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

/-- Budget-threaded `[LibsignalPlacement]` `decrypt_prekey` poll closure (`dpPollEntryPlaced`)
combining `ClosureUntrustedPlacedBudget`, `Stage1InstPlacedBudget`, `ClosurePathATopPlacedBudget`,
and `ClosurePathBMainPlacedBudget` at fixed `(mmpl, gh, W, X, B, S, Scope)`. -/
theorem closure_trusted_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv P2PathAErrEnv P2PathAOkEnv : DecPkGhost → List AllocEvent → Prop}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hStages : PollBaseStagesPlacedStmt)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hTryDec : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (pollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse (spqrV1 W.C.F W.Q.K) tdEnv)))
    (hEnv : ∀ g evs,
      CliDpPollTrustedEnv (A := A.repAlloc) W X B ReadEnv DeserEnv
        P2PathAErrEnv P2PathAOkEnv tdEnv g evs →
      DecPkEnv g evs) :
    CliDpPollOkStatePlacedAt A lim ReadEnv DeserEnv DecPkEnv mmpl gh W X B S Scope :=
  ClosureTrustedP1PlacedBudgetAux.closure_trusted_placed_ok_at hDropNz mmpl gh W X B S Scope
    (fun {_DecPkEnv _DeserEnv _st_b} =>
      hStages.stageP2PathA (ReadEnv := ReadEnv) mmpl gh X W B)
    hStages.stageP3PathA hStages.stageP4PathA
    hStages.stageP2PathB hStages.stageP3PathB hStages.stageP4PathB
    hTryDec hEnv

theorem cliDpPollOk_placed_of_stages [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv : CliHooks → UnreachedPqxdhPrimitives → RunBudgets →
      (SessionRecord (List (BitVec 8)) → Prop) → DecPkGhost → List AllocEvent → Prop}
    {P2PathAErrEnv P2PathAOkEnv : CliHooks → UnreachedPqxdhPrimitives → RunBudgets →
      (SessionRecord (List (BitVec 8)) → Prop) → DecPkGhost → List AllocEvent → Prop}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hStages : PollBaseStagesPlacedStmt)
    (hTryDec : ∀ mmpl gh W,
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsmpl.base 508)
        (withLsCodeRoLoaded lsmpl
          (pollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse (spqrV1 W.C.F W.Q.K)
            (tdEnv W))))
    (hEnv : ∀ W X B Scope g evs,
      CliDpPollTrustedEnv (A := A.repAlloc) W X B ReadEnv DeserEnv
        (P2PathAErrEnv W X B Scope) (P2PathAOkEnv W X B Scope) (tdEnv W) g evs →
      DecPkEnv W X B Scope g evs) :
    CliDpPollOkStatePlacedStmt A lim ReadEnv DeserEnv DecPkEnv :=
  fun mmpl gh W X B S Scope =>
    closure_trusted_placed_ok hDropNz hStages mmpl gh W X B S Scope
      (hTryDec mmpl gh W) (hEnv W X B Scope)

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureTrustedP1PlacedBudget
