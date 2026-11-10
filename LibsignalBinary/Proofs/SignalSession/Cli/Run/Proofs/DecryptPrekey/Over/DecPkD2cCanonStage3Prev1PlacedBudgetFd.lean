/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ChainClone3ExtPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2BridgePlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2TopPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevCapPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudgetAux
public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.TryDecryptPV1TrapPlacedBudget
public import LibsignalBinary.Proofs.PeakBudget.RealCliDecPkSlotOk
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3StageP3Prev1PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cSlotOkAtPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4ContPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4SpatialPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.StagesOverCliPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.TryDecryptStmtOfSpqrPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureTrustedP1PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib
import ProofLib.SepLogic.WPp

/-!
# `SessionGhostValid` Envelopes and Generic Stage-P3 `Prev1` Wrapper

Defines `CliDpPollTrustedGvSeqFreeEnv` and `DecPkD2cCanonPollGvSeqFreeEnv` and proves the
`{M} {A}`-generic Stage-P3 `Prev1` wrapper `stageP3_prev1_custom_frozen_placed_ok` from
`Over/StageP3PlacedBudget.stageP3Gen_prev1_vregs_at_full_placed_ok`.
-/

@[expose] public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonStage3Prev1PlacedBudgetFd

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open CryptoGames.LibsignalSession (Crypto PublicKey SessionState SignalMessage SignalProtocolError)
open CryptoGames.LibsignalSessionApi (Session SessionRecord)
open CryptoVerification (
  LibsignalFrozen LibsignalFullPlacement LibsignalPlacement lsMemcpySym lsRustAllocSym
  lsRustDeallocSym lsRustNoAllocShimSym ls_hook_ok_ultra_of_mem lsmpl lsρ withLsCodeLoaded
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3 (genP3S5Model genP3S5ModelPanicProp)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched (LsTokenInitM3)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (
  clearPending overScratch stageP3Sub5ExtraPrePrev1
)
open CryptoVerification.CliHandshake.RespClosurePlaced (instIsLsBlockProg_518 lsProg_518)
open CryptoVerification.E2E (
  PreKeyMessageFields ResponderPreKeySecrets UnreachedPqxdhPrimitives acceptInput
  aesDecHookMallocng modelPrims
)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (ClosureCalleeSaved)
open CryptoVerification.E2E.Pqxdh.WireEntries (DistinctSid)
open CryptoVerification.E2E.Record (encSession)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalPublicApi.MessageDecrypt (sessionModelRel)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  FsFiles LibsignalCodeRoLoaded withLsCodeRoLoaded
)
open CryptoVerification.LibsignalSpqrV1 (spqrV1)
open CryptoVerification.LibsignalTripleRatchet (SeedsLen32 SendCall SpqrModel rootStack)
open CryptoVerification.LibsignalTripleRatchet.Record (CloneRel)
open CryptoVerification.LibsignalTripleRatchetRepr (
  AddrGhost SessionGhost SignalMessageGhost UuidParser decryptDraws sessionStateAt uuidTryParse
)
open CryptoVerification.RecordCodecs (IdentityKeyPair)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession (
  CliHooks cliExternsPlaced lsRustAllocSymCli lsRustDeallocSymCli lsRustNoAllocShimSymCli
)
open CryptoVerification.SignalSession.Cli (StoresGhost)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo cliRunBudgets)
open CryptoVerification.SignalSession.Cli.RunCompose (DecPkGhost)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs (SessMatchesPm pkStoreKeys pmOfE)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (
  LsTokenInit cliKitStk cliPollIdKitPlaced cliPollKpkKitPlaced cliPollPkKitPlaced
  cliPollSessKitPlaced cliPollSessPrev1KitPlaced dpPollEntryPlaced dpPollProgPlaced
  pathAInitSession pathAInitState pmPreKeyId
)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (
  cliGhostExterns_sat_of_cliExternsPlaced loadRec scopeIn scopeKit
)
open CryptoVerification.SignalSession.Coins (coinsAfterPlaced coinsAtPlaced)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget SeqEnv
  rustCliAllocBudgetSpec rustCliDeallocBudgetSpec
)
open LibsignalBinary.Heap.SpecBudget (FmtWriteEnv FormatInnerEnv aesDecBudgetSpec)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ChainClone3ExtPlacedBudget (
  ChainClone3OkPlaced SenderChainClone3OkPlaced
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2BridgePlacedBudget (
  StageP2MatchedBridgeEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2TopPlacedBudget (
  StageP2MatchedEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevCapPlacedBudget (
  StageP3ErrM3Env StageP3OkPrefixM3Env pollTryDecryptM3PlacedSpecP
  pollTryDecryptM3PlacedSpecTPTight
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudget (
  OverVerNe1e04CliAtFrozenPlacedBody stageP3Gen_prev1_vregs_at_full_placed_ok
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudgetAux (
  StageP3Prev1Env StageP3VerNePrev1Env
)
open LibsignalBinary.Proofs.Cli.SpqrV1.M4.TryDecryptPV1TrapPlacedBudget (TryDecryptCliEnvOf)
open LibsignalBinary.Proofs.PeakBudget.RealCliDecPkSlotOk (
  cliFmtWrite_budget_sat cliFormatInner_budget_sat
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3StageP3Prev1PlacedBudget (
  cliGrowOneSpe_518_placed_ok cliSetSessionState_518_placed_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cSlotOkAtPlacedBudget (
  cliP2KitEnvsAt
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4ContPlacedBudget (
  cliPollStageP4Prev1SeqFreeEnvs
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4SpatialPlacedBudget (
  overGenP3Pre_placed overGenP3S5PostFrame_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudget (
  overPollTryDecryptPlacedSpecTPTight
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudgetAux (
  CliStageP4Prev1Envs StageP2OverEnv StageP4Prev1Env overStageP3ErrPostPrevEmptyAt_placed
  stageP3DispatchOkMidPrev1At_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudget (
  CliPollStageP2Envs
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.StagesOverCliPlacedBudget (
  cliPollSelfBudgetEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.TryDecryptStmtOfSpqrPlacedBudget (
  overPollTryDecrypt_placed_at_of_tdEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget (
  StageP3Env StageP3ErrEnv StageP3OkPrefixEnv pollTryDecryptPlacedSpecP
  pollTryDecryptPlacedSpecTPTight
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget (
  StageP2PathAEnv StageP4MatchedEnv StageP4PathAEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureTrustedP1PlacedBudget (
  CliStageP1OkEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget (
  CliDpPollUntrustedEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux (
  cliP2PathAOptFieldsErrEnv cliP2PathAOptFieldsOkEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget (
  cliPollIdBudgetEnv cliPollKpkBudgetEnv cliPollPkBudgetEnv cliPollSessSeqFreeBudgetEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (CliGhostAllocHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (AllocContractsXCliPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget (SpqrV1PlacedSeamsOfEnv)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  dropSessionStructureLocal2Spec
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionMemcpyRegionBudgetSpec sessionShimBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)

/-! ## 1. Fixed-`cliRunBudgets` Kit & Path-C Stage-P3 Envelope Bundles -/

def cliP2KitEnvsFixed [LibsignalPlacement] (A : RustAlloc)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (F0 : FsFiles) (peer : AddrGhost) (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey) :
    CliPollStageP2Envs (A := A) cliRunBudgets F0 peer spkId kpkId opkWord kbk :=
  cliP2KitEnvsAt A ReadEnv cliRunBudgets F0 peer spkId kpkId opkWord kbk

abbrev cliPollStageP4Prev1SeqFreeEnvsAt [LibsignalPlacement] (A : RustAlloc)
    (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
    (pid kpkId spkId : BitVec 32) (kbk : PublicKey)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop) :
    CliStageP4Prev1Envs (A := A) B F0 peer pid kpkId spkId kbk :=
  let e := cliPollStageP4Prev1SeqFreeEnvs A B F0 peer pid kpkId spkId kbk ReadEnv
  ⟨⟨e.opsEnv.storePollPrev1Env⟩, e.ikitEnv, e.pkKitEnv, e.kpkKitEnv⟩

structure PathCP3Envs where
  errEnv : SessionGhost → SessionGhost → SessionState (List (BitVec 8)) → AddrGhost → AddrGhost →
    SignalMessageGhost → SignalMessage → List (BitVec 8) → List AllocEvent → Prop
  verNeEnv : SessionGhost → SessionState (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop
  okPrefixEnv : SessionGhost → SessionGhost → SessionState (List (BitVec 8)) → AddrGhost → AddrGhost →
    SignalMessageGhost → SignalMessage → List (BitVec 8) → List AllocEvent → Prop

def tightPathCP3Envs (tdEnvW : TryDecryptEnvArgs → List AllocEvent → Prop)
    (verNeDecEnv : List (BitVec 8) → List AllocEvent → Prop) : PathCP3Envs where
  errEnv := StageP3ErrEnv tdEnvW
  verNeEnv := StageP3VerNePrev1Env verNeDecEnv
  okPrefixEnv := StageP3OkPrefixEnv tdEnvW

def wideM3PathCP3Envs (tdEnvW : TryDecryptEnvArgs → List AllocEvent → Prop)
    (verNeDecEnv : List (BitVec 8) → List AllocEvent → Prop) : PathCP3Envs where
  errEnv := StageP3ErrM3Env tdEnvW
  verNeEnv := StageP3VerNePrev1Env verNeDecEnv
  okPrefixEnv := StageP3OkPrefixM3Env tdEnvW

/-! ## 2. `CanonSessionGhostValid` & `SeqFree` Stage-P4 Poll Envelopes -/

@[reducible] def CanonSessionGhostValid (G : SessionGhost) (ses : Session (List (BitVec 8))) : Prop :=
  sessionModelRel G ses ∧
  ∃ (A : RustAlloc) (ss : BitVec 64) (m : Arm64.Memory) (R : SepProp),
    Satisfies (sepConj (sessionStateAt A ss G ses.state) R) m

theorem ex_frame_genP3 {m : Arm64.Memory} {P1 Pp S P2 P3 R : SepProp}
    (hm : Satisfies (sepConj (sepConj P1 (sepConj (sepConj Pp (sepConj S P2)) P3)) R) m) :
    ∃ R', Satisfies (sepConj S R') m :=
  ⟨sepConj P1 (sepConj Pp (sepConj P2 (sepConj P3 R))),
   Arm64.Satisfies.mono (Arm64.Entails.of_eq (by sep_ac_rfl)) hm⟩

def CliDpPollTrustedGvSeqFreeEnv [LibsignalPlacement] {A : RustAlloc}
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (P2PathAErrEnv P2PathAOkEnv : DecPkGhost → List AllocEvent → Prop)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (g : DecPkGhost) (evs : List AllocEvent) : Prop :=
  let σ := cliKitStk B
  let sessKit := cliPollSessKitPlaced A g.F scopeKit g.peer σ
  let kitEnv := cliPollSessSeqFreeBudgetEnv A g.F g.peer σ DeserEnv ReadEnv
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
       CanonSessionGhostValid recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) ∧
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
          let pid := pmPreKeyId g.msg
          let pkKit := cliPollPkKitPlaced A g.F pid σ
          let pkKitEnv := cliPollPkBudgetEnv A g.F pid σ ReadEnv
          let kpkKit := cliPollKpkKitPlaced A g.F m.kpkId m.spkId g.msg.baseKey σ
          let kpkKitEnv := cliPollKpkBudgetEnv A g.F m.kpkId m.spkId g.msg.baseKey σ ReadEnv
          let st0 := pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk
          SeqEnv
            (SeqEnv (SeqEnv P1 (P2PathAOkEnv g))
              (StageP3OkPrefixEnv tdEnv recG G₁ st0
                g.peer g.me g.msgG.msg g.msg.message g.coins))
            (StageP4PathAEnv sessKit kitEnv idKit ikitEnv pkKit pkKitEnv kpkKit kpkKitEnv
              StoresGhost.opened.sessions StoresGhost.opened.identity
              StoresGhost.opened.oneTime StoresGhost.opened.kyber
              g.peer.val g.msg.identityKey m.opkId m.kpkId m.spkId g.msg.baseKey
              { pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk with
                state := (genP3S5Model W.C W.Q.K g.peer g.me g.msg.message g.coins st0).2
                pendingPreKey := none
                pendingKyberPreKey := none }) evs))) ∨
  (∃ (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8))),
    sessKit.loadRel StoresGhost.opened.sessions g.peer.val (.ok (some r)) ∧
    r.currentSession = some sess ∧
    (SeqEnv P1 (StageP2MatchedEnv sess g.msg.identityKey) evs ∨
     (sess.state.remoteIdentity = some g.msg.identityKey ∧
      ∃ recG, CanonSessionGhostValid recG sess ∧
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
                (StageP3OkPrefixEnv tdEnv recG G₁ sess.state
                  g.peer g.me g.msgG.msg g.msg.message g.coins))
              (StageP4MatchedEnv sessKit kitEnv idKit ikitEnv
                StoresGhost.opened.sessions StoresGhost.opened.identity
                g.peer.val g.msg.identityKey
                { sess with
                  state := (genP3S5Model W.C W.Q.K g.peer g.me g.msg.message g.coins sess.state).2
                  pendingPreKey := none
                  pendingKyberPreKey := none })
              evs)))))

def DecPkD2cCanonPollGvSeqFreeEnv [LibsignalPlacement] (A : RustAlloc)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop)
    (p3c : CliHooks → PathCP3Envs)
    (g : DecPkGhost) (evs : List AllocEvent) : Prop :=
  let σ := cliKitStk cliRunBudgets
  let pid := pmPreKeyId g.msg
  let kbk := g.msg.baseKey
  let P1 := CliStageP1OkEnv (A := A) cliRunBudgets ReadEnv DeserEnv g
  let P2AErr := cliP2PathAOptFieldsErrEnv A ReadEnv X W cliRunBudgets
    (fun F0 peer => cliPollSelfBudgetEnv A F0 peer σ ReadEnv)
  let P2AOk := cliP2PathAOptFieldsOkEnv A ReadEnv X W cliRunBudgets
    (fun F0 peer => cliPollSelfBudgetEnv A F0 peer σ ReadEnv)
  CliDpPollTrustedGvSeqFreeEnv (A := A) W X cliRunBudgets ReadEnv DeserEnv P2AErr P2AOk (tdEnv W) g evs ∨
  ∃ (r : SessionRecord (List (BitVec 8))) (s_old : Session (List (BitVec 8))),
    loadRec scopeIn g.F g.peer.val = .ok (some r) ∧
    r.currentSession = some s_old ∧
    ¬ SessMatchesPm s_old g.msg ∧
    StoresGhost.opened.identity.trusted cliIo.rd g.F g.peer.val g.msg.identityKey = .ok true ∧
    (SeqEnv P1 (StageP2OverEnv P2OverErrEnv P2OverOkEnv g r) evs ∨
     ∃ (m : PreKeyMessageFields) (i : SignalMessage) (k : ResponderPreKeySecrets)
       (kp : IdentityKeyPair) (reg : BitVec 32) (dk : SignalPqxdh.DRKey)
       (recG : SessionGhost) (whisperG : SignalMessageGhost),
       g.msg = pmOfE m i ∧
       SignalMessage.tryFrom protoSignalCodec m.inner = .ok i ∧
       pkStoreKeys g.F m = some k ∧
       StoresGhost.opened.identity.keyPair cliIo.rd g.F = .ok kp ∧
       StoresGhost.opened.identity.regId cliIo.rd g.F = .ok reg ∧
       SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
         (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk ∧
       CanonSessionGhostValid recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) ∧
       let st0 := pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk
       let enc_old := encSession (clearPending s_old)
       ((∃ G₁, CloneRel recG G₁ ∧
           SeqEnv (SeqEnv P1 (P2OverOkEnv g r))
             ((p3c W).errEnv recG G₁ st0 g.peer g.me whisperG g.msg.message g.coins) evs) ∨
        SeqEnv (SeqEnv P1 (P2OverOkEnv g r))
          ((p3c W).verNeEnv recG st0 enc_old) evs ∨
        ∃ G₁ G' pt,
          CloneRel recG G₁ ∧
          G₁.AfterTryDecrypt true G' ∧
          (genP3S5Model W.C W.Q.K g.peer g.me g.msg.message g.coins st0).1 = .ok pt ∧
          let envs := cliPollStageP4Prev1SeqFreeEnvsAt A cliRunBudgets g.F g.peer pid
            m.kpkId m.spkId kbk ReadEnv
          let ses' : Session (List (BitVec 8)) :=
            { pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk with
              state := (genP3S5Model W.C W.Q.K g.peer g.me g.msg.message g.coins st0).2
              pendingPreKey := none
              pendingKyberPreKey := none }
          CanonSessionGhostValid G' ses' ∧
          SeqEnv
            (SeqEnv (SeqEnv P1 (P2OverOkEnv g r))
              ((p3c W).okPrefixEnv recG G₁ st0 g.peer g.me whisperG g.msg.message g.coins))
            (StageP4Prev1Env
              (cliPollSessPrev1KitPlaced A g.F g.peer σ) envs.opsEnv
              (cliPollIdKitPlaced A g.F g.peer σ) envs.ikitEnv
              (cliPollPkKitPlaced A g.F pid σ) envs.pkKitEnv
              (cliPollKpkKitPlaced A g.F m.kpkId m.spkId kbk σ) envs.kpkKitEnv
              StoresGhost.opened.sessions StoresGhost.opened.identity
              StoresGhost.opened.oneTime StoresGhost.opened.kyber
              g.peer.val g.msg.identityKey m.kpkId m.spkId kbk m.opkId G' ses' enc_old)
            evs))

def DecPkD2cCanonPollGvSeqFreeEnvFns [LibsignalPlacement] (A : RustAlloc)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop)
    (p3ErrEnv : CliHooks → SessionGhost → SessionGhost → SessionState (List (BitVec 8)) →
      AddrGhost → AddrGhost → SignalMessageGhost → SignalMessage → List (BitVec 8) →
      List AllocEvent → Prop)
    (p3VerNeEnv : CliHooks → SessionGhost → SessionState (List (BitVec 8)) → List (BitVec 8) →
      List AllocEvent → Prop)
    (p3OkPrefixEnv : CliHooks → SessionGhost → SessionGhost → SessionState (List (BitVec 8)) →
      AddrGhost → AddrGhost → SignalMessageGhost → SignalMessage → List (BitVec 8) →
      List AllocEvent → Prop)
    (g : DecPkGhost) (evs : List AllocEvent) : Prop :=
  DecPkD2cCanonPollGvSeqFreeEnv A W X ReadEnv DeserEnv P2OverErrEnv P2OverOkEnv tdEnv
    (fun W' => ⟨p3ErrEnv W', p3VerNeEnv W', p3OkPrefixEnv W'⟩) g evs

/-! ## 3. `{M}{A}`-Generic Block-`507` `try_decrypt_with_state` & Stage-P3 `Prev1` Wrapper -/

private theorem fmtWriteEnv_nonempty : ∃ evs, FmtWriteEnv evs := ⟨[], rfl⟩

private theorem formatInnerEnv_nonempty : ∃ evs, FormatInnerEnv evs := ⟨[], rfl⟩

theorem try507_of_tdEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (ctl : BitVec 64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (hSpqrTd : SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W InitEnv
      (fun st msg => RecvBytesEnv st.bytes msg.bytes) SendEnv)
    (hRecv_ne : ∀ stBs msgBs, ∃ evs, RecvBytesEnv stBs msgBs evs)
    (htd : ∀ a evs,
      TryDecryptCliEnvOf W.C (spqrV1 W.C.F W.Q.K) FmtWriteEnv RecvBytesEnv FormatInnerEnv a evs →
      tdEnv W a evs) :
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (overPollTryDecryptPlacedSpecTPTight W.C A lim ctl uuidTryParse
          (spqrV1 W.C.F W.Q.K) (tdEnv W))) :=
  overPollTryDecrypt_placed_at_of_tdEnv mmpl gh W ctl hG hAesDec hSpqrTd
    (cliFmtWrite_budget_sat mmpl gh W) (cliFormatInner_budget_sat mmpl gh W)
    hRecv_ne fmtWriteEnv_nonempty formatInnerEnv_nonempty htd

private theorem pollTryDecryptM3PlacedSpecTPTight_eq_over [LibsignalPlacement]
    {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    pollTryDecryptM3PlacedSpecTPTight C A lim ctl uuidParse S tdEnv =
      overPollTryDecryptPlacedSpecTPTight C A lim ctl uuidParse S tdEnv := by
  dsimp only [pollTryDecryptM3PlacedSpecTPTight, overPollTryDecryptPlacedSpecTPTight,
    pollTryDecryptPlacedSpecTPTight, pollTryDecryptM3PlacedSpecP, pollTryDecryptPlacedSpecP,
    LsTokenInitM3, LsTokenInit]
  rfl

theorem stageP3_prev1_custom_frozen_placed_ok [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    {PrevEncOK : List (BitVec 8) → Prop}
    {verNeDecEnv : List (BitVec 8) → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (st_b : M.σ)
    (hG : CliGhostAllocHooks M A lim gh)
    (_hAllocX : AllocContractsXCliPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hcc : ChainClone3OkPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hscc : SenderChainClone3OkPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hroot : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (overPollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (spqrV1 W.C.F W.Q.K) (tdEnv W))))
    (hDropSS3 : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hVerNeAt : OverVerNe1e04CliAtFrozenPlacedBody A lim PrevEncOK verNeDecEnv
      (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    ∀ (s0 s : State)
      (coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr
        remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
      (msgVer : BitVec 32) (b_2c0 : BitVec 8)
      (enc rest : List (BitVec 8))
      (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
      (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
      (F_frame : SepProp) (Q : State → SepProp → Prop),
      FitsEnv M lim st_b
        (StageP3Prev1Env (tdEnv W) verNeDecEnv recG st rem loc msgG msg msgVer enc rest) →
      initErrsPtr ≠ 0#64 →
      prevCap ≠ 0#64 →
      PrevEncOK enc →
      st.version = 4#32 →
      (st.remoteIdentity ≠ some st.localIdentity ∨
        DistinctSid uuidTryParse loc.name.bytes rem.name.bytes) →
      SeedsLen32 st →
      st.receiverChains.length < 2 ^ 32 →
      st.pqRatchetState.length < 2 ^ 32 →
      LibsignalFrozen lsmpl s.mem →
      s.pc = dpPollEntryPlaced + 0x1778#64 →
      s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true →
      rootStack ≤ s.sp.toNat →
      s.readReg64 .x29 = s.sp + 0xc70#64 →
      s.trace = s0.trace →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      (∀ (G₁ G' : SessionGhost) (evs_p3 : List AllocEvent)
          (pt : List (BitVec 8)) (ptCap ptPtr : BitVec 64)
          (s' : State) (P_s' : SepProp),
        st.version = msgVer →
        CloneRel recG G₁ →
        G₁.AfterTryDecrypt true G' →
        StageP3OkPrefixM3Env (tdEnv W) recG G₁ st rem loc msgG msg rest evs_p3 →
        (genP3S5Model W.C W.Q.K rem loc msg rest st).1 = .ok pt →
        pt.length ≤ ptCap.toNat →
        ptCap.toNat < 2 ^ 63 →
        ptPtr ≠ 0#64 →
        Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s s' →
        s'.pc = dpPollEntryPlaced + 0x34dc#64 →
        s'.status = .Running →
        s'.sp = s.sp →
        s'.trace = s0.trace →
        calleeSavedVRegs s' = calleeSavedVRegs s0 →
        s'.readReg64 .x19 = coroPtr →
        s'.readReg64 .x24 = s.sp + 0x370#64 →
        s'.readReg64 .x25 = s.sp + 0x210#64 →
        s'.readReg64 .x26 = outPtr →
        s'.readReg64 .x27 = ctxPtr →
        s'.readReg64 .x28 = 0xfffffffffffffffe#64 →
        LibsignalCodeRoLoaded lsmpl s'.mem →
        (P_s' ⊢
          stageP3DispatchOkMidPrev1At_placed A lim (M.stepEvents evs_p3 st_b) s0 s s'
            coroPtr outPtr initErrsPtr prevCap prevPtr ptCap ptPtr enc pt b_2c0 G'
            (genP3S5Model W.C W.Q.K rem loc msg rest st).2 ∗
          overGenP3S5PostFrame_placed A.repAlloc s.sp coroPtr ctxPtr remAddrPtr locAddrPtr
            whisperMsgPtr msgVer rem loc msgG msg
            (coinsAfterPlaced cur rest
              (decryptDraws W.C st msg.senderRatchetKey rest)) ∗
          overScratch s.sp) →
        SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
          (s0.readReg64 .x30) s' (P_s' ∗ F_frame) Q
          (genP3S5ModelPanicProp W.C W.Q.K rem loc st msg msgVer rest s0)) →
      (∀ (G₁ G' : SessionGhost) (evs_p3 : List AllocEvent)
          (e : SignalProtocolError) (sf : State) (P_f : SepProp),
        st.version = msgVer →
        CloneRel recG G₁ →
        G₁.AfterTryDecrypt false G' →
        StageP3ErrM3Env (tdEnv W) recG G₁ st rem loc msgG msg rest evs_p3 →
        (genP3S5Model W.C W.Q.K rem loc msg rest st).1 = .error e →
        e ≠ .panic →
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
          memRegion (s.sp + 0x3e0#64) 344 ∗
          overStageP3ErrPostPrevEmptyAt_placed A lim (M.stepEvents evs_p3 st_b) s0 s sf
            coroPtr outPtr e ∗
          overGenP3S5PostFrame_placed A.repAlloc s.sp coroPtr ctxPtr remAddrPtr locAddrPtr
            whisperMsgPtr msgVer rem loc msgG msg
            (coinsAfterPlaced cur rest
              (decryptDraws W.C st msg.senderRatchetKey rest)) ∗
          overScratch s.sp) →
        sf.sp = s.sp + 0xcd0#64 →
        sf.trace = s0.trace →
        ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 →
        LibsignalCodeRoLoaded lsmpl sf.mem →
        Q sf (P_f ∗ F_frame)) →
      (∀ (evs_p3 : List AllocEvent) (sf : State) (P_f : SepProp),
        st.version ≠ msgVer →
        StageP3VerNePrev1Env verNeDecEnv recG st enc evs_p3 →
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
          memRegion (s.sp + 0x3e0#64) 344 ∗
          overStageP3ErrPostPrevEmptyAt_placed A lim (M.stepEvents evs_p3 st_b) s0 s sf coroPtr
            outPtr (.invalidMessage .preKey .decryptionFailed) ∗
          overGenP3S5PostFrame_placed A.repAlloc s.sp coroPtr ctxPtr remAddrPtr locAddrPtr
            whisperMsgPtr msgVer rem loc msgG msg (coinsAtPlaced cur rest) ∗
          overScratch s.sp ∗
          anyHeap) →
        sf.sp = s.sp + 0xcd0#64 →
        sf.trace = s0.trace →
        ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 →
        LibsignalCodeRoLoaded lsmpl sf.mem →
        Q sf (P_f ∗ F_frame)) →
      SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (s0.readReg64 .x30) s
        (LsTokenInit ∗
          overGenP3Pre_placed A lim st_b s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr
            locAddrPtr whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗
          stageP3Sub5ExtraPrePrev1 A.repAlloc s0 s coroPtr outPtr initErrsPtr prevCap prevPtr
            enc b_2c0 ∗
          overScratch s.sp ∗
          F_frame)
        Q
        (genP3S5ModelPanicProp W.C W.Q.K rem loc st msg msgVer rest s0) := by
  intro s0 s coroPtr ctxPtr outPtr initErrsPtr
    prevCap prevPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer b_2c0 enc rest recG st rem loc
    msgG msg F_frame Q hfits hinit hcap hprev hv4 hns hsd hrc hpq hfr hpc hrun hsp hroot_sp hfp
    htr hvregs hOk hErr hVerNe
  let ext := cliGhostExterns gh (cliExternsPlaced mmpl W)
  have hshim : subroutine_ok (lsProg_518 ext) (lsρ lsRustNoAllocShimSym)
      sessionShimBudgetSpec :=
    ls_hook_ok_ultra_of_mem
      ((show lsRustNoAllocShimSymCli = lsRustNoAllocShimSym by decide) ▸
        LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget.cliExternsPlaced_shim_budget_sat
          mmpl gh W hG.shim_eq)
      (by decide)
  have halloc : subroutine_ok (lsProg_518 ext) (lsρ lsRustAllocSym)
      (rustCliAllocBudgetSpec M A lim false) :=
    ls_hook_ok_ultra_of_mem
      ((show lsRustAllocSymCli = lsRustAllocSym by decide) ▸
        LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget.cliExternsPlaced_alloc_budget_sat
          mmpl gh W hG)
      (by decide)
  have hdealloc : subroutine_ok (lsProg_518 ext) (lsρ lsRustDeallocSym)
      (rustCliDeallocBudgetSpec M A lim) :=
    ls_hook_ok_ultra_of_mem
      ((show lsRustDeallocSymCli = lsRustDeallocSym by decide) ▸
        LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget.cliExternsPlaced_dealloc_budget_sat
          mmpl gh W hG)
      (by decide)
  have hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym)
      sessionMemcpyRegionBudgetSpec :=
    ls_hook_ok_ultra_of_mem
      ((show ("memcpy" : String) = lsMemcpySym by decide) ▸
        LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget.cliExternsPlaced_sessionMemcpyRegion_budget_sat
          mmpl gh W hG)
      (by decide)
  have hrootM3 : subroutine_ok (lsProg_518 ext) (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (pollTryDecryptM3PlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (spqrV1 W.C.F W.Q.K) (tdEnv W))) := by
    rw [pollTryDecryptM3PlacedSpecTPTight_eq_over]
    exact hroot
  exact stageP3Gen_prev1_vregs_at_full_placed_ok ext W.C 0#64 W.Q.K
    hshim halloc hdealloc hmemcpy
    (cliGrowOneSpe_518_placed_ok mmpl gh W hG)
    (cliSetSessionState_518_placed_ok mmpl gh W hG)
    hDropSS3 hcc hscc hrootM3 hVerNeAt
    st_b s0 s coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr remAddrPtr locAddrPtr whisperMsgPtr
    cur msgVer b_2c0 enc rest recG st rem loc msgG msg F_frame Q
    hfits hinit hcap hprev hv4 hns hsd hrc hpq hfr hpc hrun hsp hroot_sp hfp htr hvregs
    (fun G₁ G' pt ptCap ptPtr evs_ok s' P_s' => hOk G₁ G' evs_ok pt ptCap ptPtr s' P_s')
    (fun G₁ G' e evs_err sf P_f => hErr G₁ G' evs_err e sf P_f)
    (fun evs_vn sf P_f hver hevs hPf => hVerNe evs_vn sf P_f hver hevs
      (Entails.trans hPf (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (Entails.trans (Entails.of_eq (sepConj_emp _).symm)
          (sepConj_mono_right (entails_anyHeap emp)))))))))

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonStage3Prev1PlacedBudgetFd
