/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import Arm64.Trusted.Spec.SepLogic
public import LibsignalBinary.Heap.Fine.CostModel
public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2PurePlacedBudget
public import LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedABudget
public import LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith
public import LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
public import LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinkedAux
public import LibsignalBinary.Proofs.PeakBudget.RealCliDecPkGuardedDefs
public import LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.W4PathCVerNeWideDefs
public import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkSlot
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4ContPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.StagesOverCliPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# Guarded wide `W4` (`decrypt_prekey`) poll-to-binary-kit bridge (`CliDpPollTrustedWideBridge`)

Connects `[LibsignalFullPlacement]` D2(c) `decrypt_prekey` poll producers to
`realCliDecPkBinaryWideSlotEnvGuardedFixed` and `realCliDecPkBinaryWideSlotEnvCmkWithP3CGuardedFixedOf`:
1. Unsatisfiability of `FitsEnv M lim st (fun _ => True)` (`not_fitsEnv_top`);
2. Path-C C3/C4-tied and `SeqFree` D2(c) linked poll envelopes parameterized by `verNeEnv`
   (defaulting to `VerNeTightTopEnv`);
3. Parametric `PeerSpqrStateTight640` split-on-guard `DecPkD2cSlotOk` slot wrappers;
4. Consumer `hRunSub` guard eliminators and `Cmk + VerNe-prev1` slot envelopes.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.PeakBudget.CliDpPollTrustedWideBridge

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open CryptoGames.LibsignalSession (PublicKey SignalMessage)
open CryptoGames.LibsignalSessionApi (ApiError Session SessionRecord)
open CryptoVerification
  (LibsignalFrozen LibsignalFullPlacement LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (clearPending)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3 (genP3S5Model)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (SessionExtraRel)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives acceptInput modelPrims)
open CryptoVerification.E2E.Pqxdh.ResponderCore (ofSignalPqxdhPrimitives)
open CryptoVerification.E2E.Record (encSession)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles withLsCodeRoLoaded)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal)
open CryptoVerification.LibsignalTripleRatchet (SendCall)
open CryptoVerification.LibsignalTripleRatchet.Record (CloneRel)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost uuidTryParse)
open CryptoVerification.RecordCodecs (IdentityKeyPair)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession
  (CliHooks CliPqxdhInputs Inputs cliExternsPlaced lsReadFileSym)
open CryptoVerification.SignalSession.Cli (CliGhostHooks StoresGhost cliGhostExterns)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddrV cliIo cliRunBudgets cliWrOk parseArgs)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (DecPkGhost RunNeeds RunSem addrValOf mkSlot runFiles slotOut slotTrace)
open CryptoVerification.SignalSession.Cli.RunProofs
  (DecPkOkD2c SessMatchesPm cliDecryptPrekeyNeed decPkDefD2c pkStoreKeys pmOfE)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll
  (cliKitStk cliPollIdKitPlaced cliPollKpkKitPlaced cliPollPkKitPlaced cliPollSessKitPlaced
   cliPollSessPrev1KitPlaced pathAInitSession pathAInitState pmPreKeyId)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (filesOk₀ scopeIn scopeKit)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open VerifiedLibraries.Mallocng (MallocngMaxAllocSize)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget SeqEnv)
open LibsignalBinary.Heap.Fine (fineCostModel)
open LibsignalBinary.Heap.SpecBudget (aesDecBudgetSpec)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2PurePlacedBudget
  (InitializeBobV1OptFieldsEnv)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2BridgePlacedBudget
  (StageP2MatchedBridgeEnv)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2TopPlacedBudget
  (StageP2MatchedEnv)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevCapPlacedBudget
  (StageP3ErrM3Env StageP3OkPrefixM3Env)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudgetAux
  (StageP3Prev1Env StageP3VerNePrev1Env)
open LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget
  (CmkLoopAdvanceEvs)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedABudget (AcceptOptFieldsEnv)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith (cliBudgetLimits)
open LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs (W4CloneACDomEnv)
open LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked
  (SpqrRecvC07C09aBytesEnv TryDecryptCliLinkedEnv)
open LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinkedAux
  (StageP3Prev1WideVRegsPlacedStmt)
open LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinkedBase
  (DecPkD2cSlotOkFrozenPlaced DecPkD2cSlotOkFrozenPlacedAt DecPkD2cSlotOkPlacedAtOf
   StageP2OverQpanCliMemInvPlacedStmt StageP2PathAQpanCliMemInvAtStmt decPkSlotSpecBasePlaced
   decPkSlotSpecPlacedOf extract_withMemInv slotsOfDecPkPlacedOf withMemInv)
open LibsignalBinary.Proofs.PeakBudget.RealCliDecPkGuardedDefs
  (realCliDecPkBinaryWideSlotEnvGuardedFixed)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
  (realCliDecPkBinaryWideSlotEnvFixed)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift
  (PeerSpqrStateTight640 peerSpqrStateTight640_of_cliPqInputs_recv)
open LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec (OptStageEnv)
open LibsignalBinary.Proofs.PeakBudget.W4PathCVerNeWideDefs
  (VerNeTightTopEnv W4StageP3Prev1WideEnvOf w4StageP3Prev1WideEnvOf_of_wide)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkSlot
  (W4BinaryRecvPrekeyParamsCmk W4LoopAdvEnv W4RecvPrekeyTryDecACCmkEnvOf
   realCliDecPkBinaryWideSlotEnvCmkFixedOf realCliDecPkBinaryWideSlotEnvCmkWithP3CFixedOf
   realCliDecPkBinaryWideSlotEnvCmkWithP3CFixedOf_mono
   realCliDecPkBinaryWideSlotEnvCmkWithP3CGuardedFixedOf
   realCliDecPkBinaryWideSlotEnvCmkWithP3CGuardedFixedOf_ghost_congr
   w4c_defaultDecodeMaxOps w4c_loopAdvSub_refl)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget
  (RecordDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (ReadFileRuleEnvFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4ContPlacedBudget
  (cliPollSessPrev1SeqFreeStorePollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudgetAux
  (CliStageP4Prev1Envs StageP2OverEnv StageP4Prev1Env StageP4Prev1VRegsPlacedStmt)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudget
  (P2OverPathCErrEnvOf P2OverPathCOkEnvOf PromoteOverArchiveCanonSessEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.StagesOverCliPlacedBudget
  (cliPollSelfBudgetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBMainPlacedBudget
  (StageP2MatchedFramedCliPlacedStmt)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget
  (StageP3Env StageP3GenStepsVRegsPlacedStmt StageP3OkPrefixEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget
  (StageP2PathAEnv StageP3PrevEmptyVRegsPlacedStmt StageP4MatchedEnv StageP4PathAEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureTrustedP1PlacedBudget
  (CliDpPollTrustedEnv CliStageP1OkEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget
  (CliDpPollUntrustedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux
  (cliP2PathAOptFieldsErrEnv cliP2PathAOptFieldsOkEnv cliStageP2KitEnvs)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget
  (StageP4MatchedSeqFreeCliPlacedStmt StageP4PathASeqFreeCliPlacedStmt
   cliPollIdBudgetEnv cliPollKpkBudgetEnv cliPollPkBudgetEnv cliPollSessSeqFreeBudgetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget
  (decPkSlotSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (readFileSpecPlaced sessDeserializeSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget
  (SpqrV1PlacedSeamsOfEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser (ofBytesEnv)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)

/-! ## Top-envelope `FitsEnv` impossibility -/

/-- No cost-model state satisfies `FitsEnv M lim st (fun _ => True)` because the single-allocation
trace `[.alloc (MallocngMaxAllocSize + 1)]` violates `AllocEvent.withinMaxAlloc`. -/
theorem not_fitsEnv_top (M : AllocCostModel) (lim : BudgetLimits) (st : M.σ) :
    ¬ FitsEnv M lim st (fun _ => True) := by
  intro h
  have hev := (h [.alloc (MallocngMaxAllocSize + 1)] trivial).1.1
  unfold AllocEvent.withinMaxAlloc at hev
  omega

theorem not_fitsEnv_top_cliBudgetLimits (st : fineCostModel.σ) :
    ¬ FitsEnv fineCostModel cliBudgetLimits st (fun _ => True) :=
  not_fitsEnv_top fineCostModel cliBudgetLimits st

/-! ## C3/C4-tied and `SeqFree` D2(c) linked poll envelopes -/

/-- `PollOverPathCPlacedBudgetAux.CliStageP4Prev1Envs` bundle at `cliPollSessPrev1SeqFreeStorePollEnv`. -/
def cliPollStageP4Prev1SeqFreeEnvsAux [LibsignalPlacement] (A : RustAlloc)
    (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
    (pid kpkId spkId : BitVec 32) (kbk : PublicKey)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop) :
    CliStageP4Prev1Envs (A := A) B F0 peer pid kpkId spkId kbk where
  opsEnv := { storePrev1PollEnv := cliPollSessPrev1SeqFreeStorePollEnv }
  ikitEnv := cliPollIdBudgetEnv A F0 peer (cliKitStk B) ReadEnv
  pkKitEnv := cliPollPkBudgetEnv A F0 pid (cliKitStk B) ReadEnv
  kpkKitEnv := cliPollKpkBudgetEnv A F0 kpkId spkId kbk (cliKitStk B) ReadEnv

/-- `SeqFree` counterpart of `ClosureTrustedP1PlacedBudget.CliDpPollTrustedEnv`, replacing
`cliPollSessBudgetEnv` (`SerializeCanonEnvX`) with `cliPollSessSeqFreeBudgetEnv`
(`RecordSerializeSeqFreeValidEnv`) on Stage P4 of Paths A and B so Stage-P4 `store_session` traces
land in `W4BinaryStageP4{Matched,PathA}WideEnvAllFixed`. -/
def CliDpPollTrustedSeqFreeEnv [LibsignalPlacement] {A : RustAlloc}
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
                (StageP3OkPrefixEnv tdEnv recG G₁ sess.state
                  g.peer g.me g.msgG.msg g.msg.message g.coins))
              (StageP4MatchedEnv sessKit kitEnv idKit ikitEnv
                StoresGhost.opened.sessions StoresGhost.opened.identity
                g.peer.val g.msg.identityKey
                { sess with
                  state := (genP3S5Model W.C W.Q.K g.peer g.me g.msg.message g.coins sess.state).2 })
              evs)))))

/-- Shared Path-C D2(c) tail over `(P1, P2OverErrEnv, P2OverOkEnv, tdEnv, verNeEnv, p4Envs)` with
C3 (`StageP3ErrM3Env`) and C4 (`StageP3VerNePrev1Env verNeEnv`) explicitly tied to `g` via
`g.msg = pmOfE m i`, `pkStoreKeys`, `keyPair`, `regId`, `acceptKeys`, and
`SessionExtraRel recG (pathAInitSession ...)`. -/
def CliDpPollPathCTiedEnvOf [LibsignalPlacement] {A : RustAlloc}
    (verNeEnv : List (BitVec 8) → List AllocEvent → Prop)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (p4Envs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
      CliStageP4Prev1Envs (A := A) B F0 peer pid kpkId spkId kbk)
    (g : DecPkGhost) (evs : List AllocEvent) : Prop :=
  let σ := cliKitStk B
  let P1 := CliStageP1OkEnv (A := A) B ReadEnv DeserEnv g
  ∃ (r : SessionRecord (List (BitVec 8))) (s_old : Session (List (BitVec 8))),
    (cliPollSessKitPlaced A g.F scopeKit g.peer σ).loadRel
      StoresGhost.opened.sessions g.peer.val (.ok (some r)) ∧
    r.currentSession = some s_old ∧
    ¬ SessMatchesPm s_old g.msg ∧
    (SeqEnv P1 (StageP2OverEnv P2OverErrEnv P2OverOkEnv g r) evs ∨
     (∃ m i k, ∃ kp : IdentityKeyPair, ∃ reg dk recG whisperG,
       g.msg = pmOfE m i ∧
       SignalMessage.tryFrom protoSignalCodec m.inner = .ok i ∧
       pkStoreKeys g.F m = some k ∧
       StoresGhost.opened.identity.keyPair cliIo.rd g.F = .ok kp ∧
       StoresGhost.opened.identity.regId cliIo.rd g.F = .ok reg ∧
       SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
         (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk ∧
       SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) ∧
       SeqEnv (SeqEnv P1 (P2OverOkEnv g r))
         (StageP3Prev1Env tdEnv verNeEnv recG
           (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
           g.peer g.me whisperG g.msg.message
           (g.msg.message.messageVersion.zeroExtend 32)
           (encSession (clearPending s_old)) g.coins) evs) ∨
     (∃ m i k, ∃ kp : IdentityKeyPair, ∃ reg dk recG G₁ whisperG,
       g.msg = pmOfE m i ∧
       SignalMessage.tryFrom protoSignalCodec m.inner = .ok i ∧
       pkStoreKeys g.F m = some k ∧
       StoresGhost.opened.identity.keyPair cliIo.rd g.F = .ok kp ∧
       StoresGhost.opened.identity.regId cliIo.rd g.F = .ok reg ∧
       SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
         (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk ∧
       SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) ∧
       CloneRel recG G₁ ∧
       SeqEnv (SeqEnv P1 (P2OverOkEnv g r))
         (StageP3ErrM3Env tdEnv recG G₁
           (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
           g.peer g.me whisperG g.msg.message g.coins) evs) ∨
     (∃ m i k, ∃ kp : IdentityKeyPair, ∃ reg dk recG,
       g.msg = pmOfE m i ∧
       SignalMessage.tryFrom protoSignalCodec m.inner = .ok i ∧
       pkStoreKeys g.F m = some k ∧
       StoresGhost.opened.identity.keyPair cliIo.rd g.F = .ok kp ∧
       StoresGhost.opened.identity.regId cliIo.rd g.F = .ok reg ∧
       SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
         (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk ∧
       SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) ∧
       (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk).version ≠
         g.msg.message.messageVersion.zeroExtend 32 ∧
       SeqEnv (SeqEnv P1 (P2OverOkEnv g r))
         (StageP3VerNePrev1Env verNeEnv recG
           (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
           (encSession (clearPending s_old))) evs) ∨
     (∃ m i k, ∃ kp : IdentityKeyPair, ∃ reg dk recG G₁ G' pt whisperG,
       g.msg = pmOfE m i ∧
       SignalMessage.tryFrom protoSignalCodec m.inner = .ok i ∧
       pkStoreKeys g.F m = some k ∧
       StoresGhost.opened.identity.keyPair cliIo.rd g.F = .ok kp ∧
       StoresGhost.opened.identity.regId cliIo.rd g.F = .ok reg ∧
       SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
         (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk ∧
       SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) ∧
       CloneRel recG G₁ ∧
       G₁.AfterTryDecrypt true G' ∧
       (genP3S5Model W.C W.Q.K g.peer g.me g.msg.message g.coins
         (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)).1 = .ok pt ∧
       let pid := pmPreKeyId g.msg
       let envs := p4Envs B g.F g.peer pid m.kpkId m.spkId g.msg.baseKey
       let st0 := pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk
       let ses' : Session (List (BitVec 8)) :=
         { pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk with
           state := (genP3S5Model W.C W.Q.K g.peer g.me g.msg.message g.coins st0).2
           pendingPreKey := none
           pendingKyberPreKey := none }
       SeqEnv
         (SeqEnv (SeqEnv P1 (P2OverOkEnv g r))
           (StageP3OkPrefixM3Env tdEnv recG G₁ st0
             g.peer g.me whisperG g.msg.message g.coins))
         (StageP4Prev1Env
           (cliPollSessPrev1KitPlaced A g.F g.peer σ) envs.opsEnv
           (cliPollIdKitPlaced A g.F g.peer σ) envs.ikitEnv
           (cliPollPkKitPlaced A g.F pid σ) envs.pkKitEnv
           (cliPollKpkKitPlaced A g.F m.kpkId m.spkId g.msg.baseKey σ) envs.kpkKitEnv
           StoresGhost.opened.sessions StoresGhost.opened.identity
           StoresGhost.opened.oneTime StoresGhost.opened.kyber
           g.peer.val g.msg.identityKey m.kpkId m.spkId g.msg.baseKey m.opkId G' ses'
           (encSession (clearPending s_old))) evs))

/-- C3/C4-tied counterpart of `DecPkD2cSlotOkLinkedAux.CliDpPollD2cWideEnv` parametric in
`verNeEnv`. -/
def CliDpPollD2cTiedWideEnvOf [LibsignalPlacement] {A : RustAlloc}
    (verNeEnv : List (BitVec 8) → List AllocEvent → Prop)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (P2PathAErrEnv P2PathAOkEnv : DecPkGhost → List AllocEvent → Prop)
    (P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop)
    (p4Envs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
      CliStageP4Prev1Envs (A := A) B F0 peer pid kpkId spkId kbk)
    (g : DecPkGhost) (evs : List AllocEvent) : Prop :=
  CliDpPollTrustedEnv (A := A) W X B ReadEnv DeserEnv
    P2PathAErrEnv P2PathAOkEnv (tdEnv W) g evs ∨
  CliDpPollPathCTiedEnvOf (A := A) verNeEnv W X B ReadEnv DeserEnv
    P2OverErrEnv P2OverOkEnv (tdEnv W) p4Envs g evs

abbrev CliDpPollD2cTiedLinkedEnvOf [LibsignalPlacement] {A : RustAlloc}
    (verNeEnv : List (BitVec 8) → List AllocEvent → Prop)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (P2PathAErrEnv P2PathAOkEnv : DecPkGhost → List AllocEvent → Prop)
    (P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (p4Envs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
      CliStageP4Prev1Envs (A := A) B F0 peer pid kpkId spkId kbk)
    (g : DecPkGhost) (evs : List AllocEvent) : Prop :=
  CliDpPollD2cTiedWideEnvOf (A := A) verNeEnv W X B ReadEnv DeserEnv
    P2PathAErrEnv P2PathAOkEnv P2OverErrEnv P2OverOkEnv
    (fun W => TryDecryptCliLinkedEnv W.C W.Q.K) p4Envs g evs

abbrev CliDpPollD2cTiedLinkedEnv [LibsignalPlacement] {A : RustAlloc}
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (P2PathAErrEnv P2PathAOkEnv : DecPkGhost → List AllocEvent → Prop)
    (P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (p4Envs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
      CliStageP4Prev1Envs (A := A) B F0 peer pid kpkId spkId kbk)
    (g : DecPkGhost) (evs : List AllocEvent) : Prop :=
  CliDpPollD2cTiedLinkedEnvOf (A := A) VerNeTightTopEnv W X B ReadEnv DeserEnv
    P2PathAErrEnv P2PathAOkEnv P2OverErrEnv P2OverOkEnv p4Envs g evs

/-- `verNeEnv`-parametric `SeqFree` D2(c) linked poll envelope (`TryDecryptCliLinkedEnv W.C W.Q.K`
+ `SeqFree` Stage P4 across Paths A, B, and C, with C3 and C4 tied to `g`). -/
def CliDpPollD2cSeqFreeLinkedEnvOf [LibsignalPlacement] {A : RustAlloc}
    (verNeEnv : List (BitVec 8) → List AllocEvent → Prop)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (P2PathAErrEnv P2PathAOkEnv : DecPkGhost → List AllocEvent → Prop)
    (P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (p4Envs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
      CliStageP4Prev1Envs (A := A) B F0 peer pid kpkId spkId kbk)
    (g : DecPkGhost) (evs : List AllocEvent) : Prop :=
  let tdEnv := TryDecryptCliLinkedEnv W.C W.Q.K
  CliDpPollTrustedSeqFreeEnv (A := A) W X B ReadEnv DeserEnv
    P2PathAErrEnv P2PathAOkEnv tdEnv g evs ∨
  CliDpPollPathCTiedEnvOf (A := A) verNeEnv W X B ReadEnv DeserEnv
    P2OverErrEnv P2OverOkEnv tdEnv p4Envs g evs

/-- `SeqFree` D2(c) linked poll envelope specialized to `VerNeTightTopEnv`. -/
abbrev CliDpPollD2cSeqFreeLinkedEnv [LibsignalPlacement] {A : RustAlloc}
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (P2PathAErrEnv P2PathAOkEnv : DecPkGhost → List AllocEvent → Prop)
    (P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (p4Envs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
      CliStageP4Prev1Envs (A := A) B F0 peer pid kpkId spkId kbk)
    (g : DecPkGhost) (evs : List AllocEvent) : Prop :=
  CliDpPollD2cSeqFreeLinkedEnvOf (A := A) VerNeTightTopEnv W X B ReadEnv DeserEnv
    P2PathAErrEnv P2PathAOkEnv P2OverErrEnv P2OverOkEnv p4Envs g evs

abbrev CliDpPollD2cSeqFreeConcreteEnvOf [LibsignalPlacement]
    (verNeEnv : List (BitVec 8) → List AllocEvent → Prop)
    (A : RustAlloc) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (g : DecPkGhost) (evs : List AllocEvent) : Prop :=
  let ReadEnv := ReadFileRuleEnvFixed cliIo.rd
  let selfEnv := fun F0 peer => cliPollSelfBudgetEnv A F0 peer (cliKitStk cliRunBudgets) ReadEnv
  let kitEnvs := cliStageP2KitEnvs (A := A) ReadEnv cliRunBudgets selfEnv
  CliDpPollD2cSeqFreeLinkedEnvOf (A := A) verNeEnv W X cliRunBudgets
    ReadEnv
    (ofBytesEnv RecordDeserializeCancelEnv)
    (cliP2PathAOptFieldsErrEnv A ReadEnv X W cliRunBudgets selfEnv)
    (cliP2PathAOptFieldsOkEnv A ReadEnv X W cliRunBudgets selfEnv)
    (P2OverPathCErrEnvOf (A := A) X W cliRunBudgets
      (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
      (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
      kitEnvs)
    (P2OverPathCOkEnvOf (A := A) X W cliRunBudgets
      (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
      PromoteOverArchiveCanonSessEnv
      kitEnvs)
    (fun B F0 peer pid kpkId spkId kbk =>
      cliPollStageP4Prev1SeqFreeEnvsAux A B F0 peer pid kpkId spkId kbk ReadEnv)
    g evs

abbrev CliDpPollD2cSeqFreeConcreteEnv [LibsignalPlacement]
    (A : RustAlloc) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (g : DecPkGhost) (evs : List AllocEvent) : Prop :=
  CliDpPollD2cSeqFreeConcreteEnvOf VerNeTightTopEnv A X W g evs

/-! ## Parametric guarded `DecPkD2cSlotOk` slot wrappers -/

/-- Generic `CodeOk`-parameterized split-on-guard slot adapter (`not_fitsEnv_top` closes the false-guard `⊤` branch). -/
theorem decPkD2cSlotOkPlacedAtOf_targetGuarded_of_unguarded [LibsignalPlacement]
    (CodeOk : Memory → Prop) {M : AllocCostModel}
    {H : LibsignalHooks} {X : UnreachedPqxdhPrimitives} {W : CliHooks}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {TargetEnv DecPkEnv₀ DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (hSlot : ∀ g e, DecPkEnv g e ↔
      (PeerSpqrStateTight640 W.C.F W.Q.K g.F g.peer.val → TargetEnv g e))
    (hUnguarded : DecPkD2cSlotOkPlacedAtOf CodeOk H X W A lim DecPkEnv₀)
    (hBridge : ∀ g evs,
      filesOk₀ scopeIn (fun _ => True) g.F g.peer.val g.me.val →
      DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn g.F g.peer.val g.me.val g.msg →
      PeerSpqrStateTight640 W.C.F W.Q.K g.F g.peer.val →
      DecPkEnv₀ g evs →
      TargetEnv g evs) :
    DecPkD2cSlotOkPlacedAtOf CodeOk H X W A lim DecPkEnv := by
  intro S needs sEnvs hsEnv hFilesEq hDecDefEq hDecOkEq hNeedEq stk hstk1 hstk2
  have hSub0 : subroutine_ok (lsProg_579 H) (lsmpl.base 520)
      (decPkSlotSpecPlacedOf CodeOk A lim DecPkEnv₀ S stk) :=
    hUnguarded S needs { sEnvs with decryptPrekey := DecPkEnv₀ }
      rfl hFilesEq hDecDefEq hDecOkEq hNeedEq stk hstk1 hstk2
  dsimp only [slotsOfDecPkPlacedOf, mkSlot]
  rw [hsEnv]
  refine subroutine_ok.of_codeLoaded fun (x, st) R s0 hpc hrun hpre hsp _ => ?_
  obtain ⟨hcode, hpre0⟩ := extract_withMemInv hpre
  dsimp only [decPkSlotSpecBasePlaced] at hpre0
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre0
  obtain ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8, hF0, hfOk, hdOk, hsp_le, hfit⟩,
    hspatial⟩ := hpre0
  by_cases hTight : PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val
  · have hfOk0 : filesOk₀ scopeIn (fun _ => True) x.F x.peer.val x.me.val := hFilesEq ▸ hfOk
    have hdOk0 : DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn x.F x.peer.val x.me.val x.msg := hDecOkEq ▸ hdOk
    have hImp : ∀ evs, DecPkEnv₀ x evs → DecPkEnv x evs :=
      fun evs hevs0 => (hSlot x evs).mpr (fun _ => hBridge x evs hfOk0 hdOk0 hTight hevs0)
    have hfit0 : FitsEnv M lim st (DecPkEnv₀ x) :=
      fun evs hevs0 => hfit evs (hImp evs hevs0)
    have hpre_base0 :
        s0.mem ⊨ (decPkSlotSpecBasePlaced A lim DecPkEnv₀ S stk).pre (x, st) s0 ∗ R := by
      dsimp only [decPkSlotSpecBasePlaced]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8, hF0, hfOk, hdOk, hsp_le, hfit0⟩,
        hspatial⟩
    have hpre1 :
        s0.mem ⊨ (decPkSlotSpecPlacedOf CodeOk A lim DecPkEnv₀ S stk).pre (x, st) s0 ∗ R := by
      dsimp only [decPkSlotSpecPlacedOf, withMemInv]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      exact ⟨hcode, by simpa only [sepConj_comm, sepConj_left_comm, sepConj_assoc] using hpre_base0⟩
    refine hSub0.mono_outcome (x, st) R s0 hpc hrun hpre1 hsp fun sf hout => ?_
    rcases hout with ⟨hret, hcc, hpost⟩ | hp | hex | ho
    · refine Or.inl ⟨hret, hcc, Satisfies.mono (sepConj_mono_left ?_) hpost⟩
      dsimp only [decPkSlotSpecPlacedOf, withMemInv, decPkSlotSpecBasePlaced,
        decPkSlotSpecPlaced, withLsCodeRoLoaded]
      refine Entails.sepExists_elim fun evs => Entails.sepExists_right evs ?_
      refine Entails.sepExists_elim fun g' => Entails.sepExists_right g' ?_
      refine Entails.sepExists_elim fun e => Entails.sepExists_right e ?_
      refine Entails.pure_left fun ⟨hevs0, htr, hout_e⟩ => ?_
      have hPure : (DecPkEnv x evs ∧ slotTrace s0 sf ∧
          slotOut (S.decryptPrekey x.F x.peer.val x.me.val x.msg x.coins) g' e s0 sf) = True :=
        propext ⟨fun _ => trivial, fun _ => ⟨hImp evs hevs0, htr, hout_e⟩⟩
      rw [hPure, pure_true, emp_sepConj]
      exact Entails.refl _
    · exact Or.inr (Or.inl hp)
    · exact Or.inr (Or.inr (Or.inl hex))
    · exact Or.inr (Or.inr (Or.inr ho))
  · exfalso
    refine not_fitsEnv_top M lim st (fun evs _ => ?_)
    exact hfit evs ((hSlot x evs).mpr (fun h => False.elim (hTight h)))

/-- Specialization of `decPkD2cSlotOkPlacedAtOf_targetGuarded_of_unguarded` to `realCliDecPkBinaryWideSlotEnvGuardedFixed X W`. -/
theorem decPkD2cSlotOkPlacedAtOf_guarded_of_unguarded [LibsignalPlacement]
    (CodeOk : Memory → Prop) {M : AllocCostModel}
    {H : LibsignalHooks} {X : UnreachedPqxdhPrimitives} {W : CliHooks}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv₀ DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (hSlot : ∀ g e, DecPkEnv g e ↔ realCliDecPkBinaryWideSlotEnvGuardedFixed X W g e)
    (hUnguarded : DecPkD2cSlotOkPlacedAtOf CodeOk H X W A lim DecPkEnv₀)
    (hBridge : ∀ g evs,
      filesOk₀ scopeIn (fun _ => True) g.F g.peer.val g.me.val →
      DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn g.F g.peer.val g.me.val g.msg →
      PeerSpqrStateTight640 W.C.F W.Q.K g.F g.peer.val →
      DecPkEnv₀ g evs →
      realCliDecPkBinaryWideSlotEnvFixed X W g evs) :
    DecPkD2cSlotOkPlacedAtOf CodeOk H X W A lim DecPkEnv :=
  decPkD2cSlotOkPlacedAtOf_targetGuarded_of_unguarded CodeOk hSlot hUnguarded hBridge

theorem decPkD2cSlotOkFrozenPlacedAt_guarded_of_unguarded [LibsignalPlacement]
    {M : AllocCostModel}
    {H : LibsignalHooks} {X : UnreachedPqxdhPrimitives} {W : CliHooks}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv₀ DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (hSlot : ∀ g e, DecPkEnv g e ↔ realCliDecPkBinaryWideSlotEnvGuardedFixed X W g e)
    (hUnguarded : DecPkD2cSlotOkFrozenPlacedAt H X W A lim DecPkEnv₀)
    (hBridge : ∀ g evs,
      filesOk₀ scopeIn (fun _ => True) g.F g.peer.val g.me.val →
      DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn g.F g.peer.val g.me.val g.msg →
      PeerSpqrStateTight640 W.C.F W.Q.K g.F g.peer.val →
      DecPkEnv₀ g evs →
      realCliDecPkBinaryWideSlotEnvFixed X W g evs) :
    DecPkD2cSlotOkFrozenPlacedAt H X W A lim DecPkEnv :=
  decPkD2cSlotOkPlacedAtOf_guarded_of_unguarded (LibsignalFrozen lsmpl) hSlot hUnguarded hBridge

theorem decPkD2cSlotOkFrozenPlaced_guarded_of_unguarded [LibsignalPlacement]
    {M : AllocCostModel}
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv₀ : UnreachedPqxdhPrimitives → DecPkGhost → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (X : UnreachedPqxdhPrimitives)
    (hSlot : ∀ g e, DecPkEnv g e ↔ realCliDecPkBinaryWideSlotEnvGuardedFixed X W g e)
    (hUnguarded : ∀ X',
      DecPkD2cSlotOkFrozenPlacedAt (cliGhostExterns gh (cliExternsPlaced mmpl W)) X' W A lim
        (DecPkEnv₀ X'))
    (hBridge : ∀ X' g evs,
      filesOk₀ scopeIn (fun _ => True) g.F g.peer.val g.me.val →
      DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn g.F g.peer.val g.me.val g.msg →
      PeerSpqrStateTight640 W.C.F W.Q.K g.F g.peer.val →
      DecPkEnv₀ X' g evs →
      realCliDecPkBinaryWideSlotEnvFixed X' W g evs) :
    DecPkD2cSlotOkFrozenPlaced mmpl gh W A lim DecPkEnv := by
  intro X'
  have hSlot' : ∀ g e, DecPkEnv g e ↔ realCliDecPkBinaryWideSlotEnvGuardedFixed X' W g e := by
    intro g e
    rw [hSlot g e]
  exact decPkD2cSlotOkPlacedAtOf_guarded_of_unguarded (LibsignalFrozen lsmpl)
    hSlot' (hUnguarded X') (hBridge X')

/-! ## Consumer `hRunSub` guard eliminators -/

/-- Generic `PeerSpqrStateTight640`-guarded eliminator for any `TargetEnv`. -/
theorem targetEnv_of_guarded_tight
    {W : CliHooks} {TargetEnv DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {x : DecPkGhost} {evs : List AllocEvent}
    (hSlot : ∀ g e, DecPkEnv g e ↔
      (PeerSpqrStateTight640 W.C.F W.Q.K g.F g.peer.val → TargetEnv g e))
    (hTight : PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val)
    (hevs : DecPkEnv x evs) :
    TargetEnv x evs :=
  ((hSlot x evs).mp hevs) hTight

/-- Generic `.recv peer` `CliPqxdhInputs` guard eliminator for any `TargetEnv`. -/
theorem targetEnv_of_guarded_cliPqInputs_recv
    {W : CliHooks} {i : Inputs} {peer : AddrV}
    {TargetEnv DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {x : DecPkGhost} {evs : List AllocEvent}
    (hSlot : ∀ g e, DecPkEnv g e ↔
      (PeerSpqrStateTight640 W.C.F W.Q.K g.F g.peer.val → TargetEnv g e))
    (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peer))
    (hF : x.F = runFiles i) (hpeer : x.peer.val = addrValOf peer)
    (hevs : DecPkEnv x evs) :
    TargetEnv x evs := by
  apply targetEnv_of_guarded_tight hSlot _ hevs
  rw [hF, hpeer]
  exact peerSpqrStateTight640_of_cliPqInputs_recv hi hparse

/-- Discharges a `PeerSpqrStateTight640`-guarded `DecPkEnv` back to unguarded
`realCliDecPkBinaryWideSlotEnvFixed X W x evs` from any `PeerSpqrStateTight640` witness. -/
theorem realCliDecPkBinaryWideSlotEnvFixed_of_guarded_tight [LibsignalPlacement]
    {X : UnreachedPqxdhPrimitives} {W : CliHooks}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {x : DecPkGhost} {evs : List AllocEvent}
    (hSlot : ∀ g e, DecPkEnv g e ↔ realCliDecPkBinaryWideSlotEnvGuardedFixed X W g e)
    (hTight : PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val)
    (hevs : DecPkEnv x evs) :
    realCliDecPkBinaryWideSlotEnvFixed X W x evs :=
  targetEnv_of_guarded_tight hSlot hTight hevs

/-- Discharges the `PeerSpqrStateTight640` guard on `realCliDecPkBinaryWideSlotEnvGuardedFixed` under `CliPqxdhInputs` at `.recv peer`. -/
theorem realCliDecPkBinaryWideSlotEnvFixed_of_guarded_cliPqInputs_recv [LibsignalPlacement]
    {X : UnreachedPqxdhPrimitives} {W : CliHooks} {i : Inputs} {peer : AddrV}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {x : DecPkGhost} {evs : List AllocEvent}
    (hSlot : ∀ g e, DecPkEnv g e ↔ realCliDecPkBinaryWideSlotEnvGuardedFixed X W g e)
    (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peer))
    (hF : x.F = runFiles i) (hpeer : x.peer.val = addrValOf peer)
    (hevs : DecPkEnv x evs) :
    realCliDecPkBinaryWideSlotEnvFixed X W x evs :=
  targetEnv_of_guarded_cliPqInputs_recv hSlot hi hparse hF hpeer hevs

/-! ## `W4RecvPrekeyCmkSlot` and `VerNe-prev1` slot envelopes, wrappers, and eliminators -/

/-- Path-C Stage-P3 step envelope for `W4RecvPrekeyCmkSlot`, combining `W4StageP3Prev1WideEnvOf verNeEnv`
with `W4RecvPrekeyTryDecACCmkEnvOf LoopAdvEnv maxOps w.base`. -/
def w4c_verNePrev1P3PathCEnvOf
    (verNeEnv : List (BitVec 8) → List AllocEvent → Prop)
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (w : W4BinaryRecvPrekeyParamsCmk) : List AllocEvent → Prop :=
  OptStageEnv
    (W4StageP3Prev1WideEnvOf verNeEnv W4CloneACDomEnv
      (W4RecvPrekeyTryDecACCmkEnvOf LoopAdvEnv maxOps w.base) w.base.enc_prev1)

/-- Canonical `VerNeTightTopEnv` Path-C Stage-P3 step envelope for `W4RecvPrekeyCmkSlot`. -/
abbrev w4c_verNePrev1P3PathCEnv
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (w : W4BinaryRecvPrekeyParamsCmk) : List AllocEvent → Prop :=
  w4c_verNePrev1P3PathCEnvOf VerNeTightTopEnv LoopAdvEnv maxOps w

/-- `(verNeEnv, LoopAdvEnv, maxOps)`-parametric unguarded `Cmk + VerNe-prev1` binary-kit W4 slot
envelope. -/
abbrev realCliDecPkBinaryWideSlotEnvCmkVerNeFixedOf [LibsignalPlacement]
    (verNeEnv : List (BitVec 8) → List AllocEvent → Prop)
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x : DecPkGhost) (evs : List AllocEvent) : Prop :=
  realCliDecPkBinaryWideSlotEnvCmkWithP3CFixedOf LoopAdvEnv maxOps
    (w4c_verNePrev1P3PathCEnvOf verNeEnv LoopAdvEnv maxOps) X W x evs

/-- Default `(VerNeTightTopEnv, CmkLoopAdvanceEvs, 109)` unguarded `Cmk + VerNe-prev1` W4 slot
envelope. -/
abbrev realCliDecPkBinaryWideSlotEnvCmkVerNeFixed [LibsignalPlacement]
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x : DecPkGhost) (evs : List AllocEvent) : Prop :=
  realCliDecPkBinaryWideSlotEnvCmkVerNeFixedOf
    VerNeTightTopEnv CmkLoopAdvanceEvs w4c_defaultDecodeMaxOps X W x evs

theorem realCliDecPkBinaryWideSlotEnvCmkFixedOf_sub_verNeOf [LibsignalPlacement]
    {verNeEnv : List (BitVec 8) → List AllocEvent → Prop}
    {LoopAdvEnv : W4LoopAdvEnv} {maxOps : Nat}
    {X : UnreachedPqxdhPrimitives} {W : CliHooks} {x : DecPkGhost} {evs : List AllocEvent}
    (h : realCliDecPkBinaryWideSlotEnvCmkFixedOf LoopAdvEnv maxOps X W x evs) :
    realCliDecPkBinaryWideSlotEnvCmkVerNeFixedOf verNeEnv LoopAdvEnv maxOps X W x evs :=
  realCliDecPkBinaryWideSlotEnvCmkWithP3CFixedOf_mono
    (w4c_loopAdvSub_refl LoopAdvEnv) (Nat.le_refl maxOps)
    (fun _ _ hp3 => hp3.elim Or.inl fun hw => Or.inr (w4StageP3Prev1WideEnvOf_of_wide hw))
    h

/-- `(verNeEnv, LoopAdvEnv, maxOps)`-parametric `PeerSpqrStateTight640`-guarded `Cmk + VerNe-prev1` W4 slot envelope. -/
abbrev realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixedOf [LibsignalPlacement]
    (verNeEnv : List (BitVec 8) → List AllocEvent → Prop)
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x : DecPkGhost) (evs : List AllocEvent) : Prop :=
  realCliDecPkBinaryWideSlotEnvCmkWithP3CGuardedFixedOf LoopAdvEnv maxOps
    (w4c_verNePrev1P3PathCEnvOf verNeEnv LoopAdvEnv maxOps) X W x evs

/-- Default `(VerNeTightTopEnv, CmkLoopAdvanceEvs, 109)` `PeerSpqrStateTight640`-guarded `Cmk + VerNe-prev1` W4 slot envelope. -/
abbrev realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixed [LibsignalPlacement]
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x : DecPkGhost) (evs : List AllocEvent) : Prop :=
  realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixedOf
    VerNeTightTopEnv CmkLoopAdvanceEvs w4c_defaultDecodeMaxOps X W x evs

theorem realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixedOf_ghost_congr [LibsignalPlacement]
    (verNeEnv : List (BitVec 8) → List AllocEvent → Prop)
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x y : DecPkGhost)
    (hp : x.peer.val = y.peer.val) (hm : x.me.val = y.me.val)
    (hs : x.stores = y.stores) (hcp : x.coinsP = y.coinsP)
    (hf : x.F = y.F) (hc : x.coins = y.coins) (hmsg : x.msg = y.msg) :
    realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixedOf verNeEnv LoopAdvEnv maxOps X W x =
      realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixedOf verNeEnv LoopAdvEnv maxOps X W y :=
  realCliDecPkBinaryWideSlotEnvCmkWithP3CGuardedFixedOf_ghost_congr
    LoopAdvEnv maxOps (w4c_verNePrev1P3PathCEnvOf verNeEnv LoopAdvEnv maxOps)
    X W x y hp hm hs hcp hf hc hmsg

theorem realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixed_ghost_congr [LibsignalPlacement]
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x y : DecPkGhost)
    (hp : x.peer.val = y.peer.val) (hm : x.me.val = y.me.val)
    (hs : x.stores = y.stores) (hcp : x.coinsP = y.coinsP)
    (hf : x.F = y.F) (hc : x.coins = y.coins) (hmsg : x.msg = y.msg) :
    realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixed X W x =
      realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixed X W y :=
  realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixedOf_ghost_congr
    VerNeTightTopEnv CmkLoopAdvanceEvs w4c_defaultDecodeMaxOps X W x y hp hm hs hcp hf hc hmsg

/-- `(LoopAdvEnv, maxOps, P3PathCEnv)`-parametric `CodeOk` guarded-slot wrapper at
`realCliDecPkBinaryWideSlotEnvCmkWithP3CGuardedFixedOf`. -/
theorem decPkD2cSlotOkPlacedAtOf_cmkWithP3CGuarded_of_unguarded [LibsignalPlacement]
    (CodeOk : Memory → Prop) {M : AllocCostModel}
    {LoopAdvEnv : W4LoopAdvEnv} {maxOps : Nat}
    {P3PathCEnv : W4BinaryRecvPrekeyParamsCmk → List AllocEvent → Prop}
    {H : LibsignalHooks} {X : UnreachedPqxdhPrimitives} {W : CliHooks}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv₀ DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (hSlot : ∀ g e, DecPkEnv g e ↔
      realCliDecPkBinaryWideSlotEnvCmkWithP3CGuardedFixedOf LoopAdvEnv maxOps P3PathCEnv X W g e)
    (hUnguarded : DecPkD2cSlotOkPlacedAtOf CodeOk H X W A lim DecPkEnv₀)
    (hBridge : ∀ g evs,
      filesOk₀ scopeIn (fun _ => True) g.F g.peer.val g.me.val →
      DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn g.F g.peer.val g.me.val g.msg →
      PeerSpqrStateTight640 W.C.F W.Q.K g.F g.peer.val →
      DecPkEnv₀ g evs →
      realCliDecPkBinaryWideSlotEnvCmkWithP3CFixedOf LoopAdvEnv maxOps P3PathCEnv X W g evs) :
    DecPkD2cSlotOkPlacedAtOf CodeOk H X W A lim DecPkEnv :=
  decPkD2cSlotOkPlacedAtOf_targetGuarded_of_unguarded CodeOk hSlot hUnguarded hBridge

theorem decPkD2cSlotOkFrozenPlacedAt_cmkWithP3CGuarded_of_unguarded [LibsignalPlacement]
    {M : AllocCostModel}
    {LoopAdvEnv : W4LoopAdvEnv} {maxOps : Nat}
    {P3PathCEnv : W4BinaryRecvPrekeyParamsCmk → List AllocEvent → Prop}
    {H : LibsignalHooks} {X : UnreachedPqxdhPrimitives} {W : CliHooks}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv₀ DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (hSlot : ∀ g e, DecPkEnv g e ↔
      realCliDecPkBinaryWideSlotEnvCmkWithP3CGuardedFixedOf LoopAdvEnv maxOps P3PathCEnv X W g e)
    (hUnguarded : DecPkD2cSlotOkFrozenPlacedAt H X W A lim DecPkEnv₀)
    (hBridge : ∀ g evs,
      filesOk₀ scopeIn (fun _ => True) g.F g.peer.val g.me.val →
      DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn g.F g.peer.val g.me.val g.msg →
      PeerSpqrStateTight640 W.C.F W.Q.K g.F g.peer.val →
      DecPkEnv₀ g evs →
      realCliDecPkBinaryWideSlotEnvCmkWithP3CFixedOf LoopAdvEnv maxOps P3PathCEnv X W g evs) :
    DecPkD2cSlotOkFrozenPlacedAt H X W A lim DecPkEnv :=
  decPkD2cSlotOkPlacedAtOf_cmkWithP3CGuarded_of_unguarded
    (LibsignalFrozen lsmpl) hSlot hUnguarded hBridge

theorem decPkD2cSlotOkFrozenPlaced_cmkWithP3CGuarded_of_unguarded [LibsignalPlacement]
    {M : AllocCostModel}
    {LoopAdvEnv : W4LoopAdvEnv} {maxOps : Nat}
    {P3PathCEnv : W4BinaryRecvPrekeyParamsCmk → List AllocEvent → Prop}
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv₀ : UnreachedPqxdhPrimitives → DecPkGhost → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (X : UnreachedPqxdhPrimitives)
    (hSlot : ∀ g e, DecPkEnv g e ↔
      realCliDecPkBinaryWideSlotEnvCmkWithP3CGuardedFixedOf LoopAdvEnv maxOps P3PathCEnv X W g e)
    (hUnguarded : ∀ X',
      DecPkD2cSlotOkFrozenPlacedAt (cliGhostExterns gh (cliExternsPlaced mmpl W)) X' W A lim
        (DecPkEnv₀ X'))
    (hBridge : ∀ X' g evs,
      filesOk₀ scopeIn (fun _ => True) g.F g.peer.val g.me.val →
      DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn g.F g.peer.val g.me.val g.msg →
      PeerSpqrStateTight640 W.C.F W.Q.K g.F g.peer.val →
      DecPkEnv₀ X' g evs →
      realCliDecPkBinaryWideSlotEnvCmkWithP3CFixedOf LoopAdvEnv maxOps P3PathCEnv X' W g evs) :
    DecPkD2cSlotOkFrozenPlaced mmpl gh W A lim DecPkEnv := by
  intro X'
  have hSlot' : ∀ g e, DecPkEnv g e ↔
      realCliDecPkBinaryWideSlotEnvCmkWithP3CGuardedFixedOf LoopAdvEnv maxOps P3PathCEnv X' W g e := by
    intro g e
    rw [hSlot g e]
  exact decPkD2cSlotOkPlacedAtOf_cmkWithP3CGuarded_of_unguarded
    (LibsignalFrozen lsmpl) hSlot' (hUnguarded X') (hBridge X')

/-- `(verNeEnv, LoopAdvEnv, maxOps)`-specialized `CodeOk` guarded-slot wrapper at
`realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixedOf`. -/
theorem decPkD2cSlotOkPlacedAtOf_cmkVerNeGuardedOf_of_unguarded [LibsignalPlacement]
    (CodeOk : Memory → Prop) {M : AllocCostModel}
    {verNeEnv : List (BitVec 8) → List AllocEvent → Prop}
    {LoopAdvEnv : W4LoopAdvEnv} {maxOps : Nat}
    {H : LibsignalHooks} {X : UnreachedPqxdhPrimitives} {W : CliHooks}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv₀ DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (hSlot : ∀ g e, DecPkEnv g e ↔
      realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixedOf verNeEnv LoopAdvEnv maxOps X W g e)
    (hUnguarded : DecPkD2cSlotOkPlacedAtOf CodeOk H X W A lim DecPkEnv₀)
    (hBridge : ∀ g evs,
      filesOk₀ scopeIn (fun _ => True) g.F g.peer.val g.me.val →
      DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn g.F g.peer.val g.me.val g.msg →
      PeerSpqrStateTight640 W.C.F W.Q.K g.F g.peer.val →
      DecPkEnv₀ g evs →
      realCliDecPkBinaryWideSlotEnvCmkVerNeFixedOf verNeEnv LoopAdvEnv maxOps X W g evs) :
    DecPkD2cSlotOkPlacedAtOf CodeOk H X W A lim DecPkEnv :=
  decPkD2cSlotOkPlacedAtOf_cmkWithP3CGuarded_of_unguarded CodeOk hSlot hUnguarded hBridge

theorem decPkD2cSlotOkPlacedAtOf_cmkVerNeGuarded_of_unguarded [LibsignalPlacement]
    (CodeOk : Memory → Prop) {M : AllocCostModel}
    {H : LibsignalHooks} {X : UnreachedPqxdhPrimitives} {W : CliHooks}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv₀ DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (hSlot : ∀ g e, DecPkEnv g e ↔ realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixed X W g e)
    (hUnguarded : DecPkD2cSlotOkPlacedAtOf CodeOk H X W A lim DecPkEnv₀)
    (hBridge : ∀ g evs,
      filesOk₀ scopeIn (fun _ => True) g.F g.peer.val g.me.val →
      DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn g.F g.peer.val g.me.val g.msg →
      PeerSpqrStateTight640 W.C.F W.Q.K g.F g.peer.val →
      DecPkEnv₀ g evs →
      realCliDecPkBinaryWideSlotEnvCmkVerNeFixed X W g evs) :
    DecPkD2cSlotOkPlacedAtOf CodeOk H X W A lim DecPkEnv :=
  decPkD2cSlotOkPlacedAtOf_cmkVerNeGuardedOf_of_unguarded CodeOk hSlot hUnguarded hBridge

theorem decPkD2cSlotOkFrozenPlacedAt_cmkVerNeGuardedOf_of_unguarded [LibsignalPlacement]
    {M : AllocCostModel}
    {verNeEnv : List (BitVec 8) → List AllocEvent → Prop}
    {LoopAdvEnv : W4LoopAdvEnv} {maxOps : Nat}
    {H : LibsignalHooks} {X : UnreachedPqxdhPrimitives} {W : CliHooks}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv₀ DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (hSlot : ∀ g e, DecPkEnv g e ↔
      realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixedOf verNeEnv LoopAdvEnv maxOps X W g e)
    (hUnguarded : DecPkD2cSlotOkFrozenPlacedAt H X W A lim DecPkEnv₀)
    (hBridge : ∀ g evs,
      filesOk₀ scopeIn (fun _ => True) g.F g.peer.val g.me.val →
      DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn g.F g.peer.val g.me.val g.msg →
      PeerSpqrStateTight640 W.C.F W.Q.K g.F g.peer.val →
      DecPkEnv₀ g evs →
      realCliDecPkBinaryWideSlotEnvCmkVerNeFixedOf verNeEnv LoopAdvEnv maxOps X W g evs) :
    DecPkD2cSlotOkFrozenPlacedAt H X W A lim DecPkEnv :=
  decPkD2cSlotOkFrozenPlacedAt_cmkWithP3CGuarded_of_unguarded hSlot hUnguarded hBridge

theorem decPkD2cSlotOkFrozenPlacedAt_cmkVerNeGuarded_of_unguarded [LibsignalPlacement]
    {M : AllocCostModel}
    {H : LibsignalHooks} {X : UnreachedPqxdhPrimitives} {W : CliHooks}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv₀ DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (hSlot : ∀ g e, DecPkEnv g e ↔ realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixed X W g e)
    (hUnguarded : DecPkD2cSlotOkFrozenPlacedAt H X W A lim DecPkEnv₀)
    (hBridge : ∀ g evs,
      filesOk₀ scopeIn (fun _ => True) g.F g.peer.val g.me.val →
      DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn g.F g.peer.val g.me.val g.msg →
      PeerSpqrStateTight640 W.C.F W.Q.K g.F g.peer.val →
      DecPkEnv₀ g evs →
      realCliDecPkBinaryWideSlotEnvCmkVerNeFixed X W g evs) :
    DecPkD2cSlotOkFrozenPlacedAt H X W A lim DecPkEnv :=
  decPkD2cSlotOkFrozenPlacedAt_cmkVerNeGuardedOf_of_unguarded hSlot hUnguarded hBridge

theorem decPkD2cSlotOkFrozenPlaced_cmkVerNeGuardedOf_of_unguarded [LibsignalPlacement]
    {M : AllocCostModel}
    {verNeEnv : List (BitVec 8) → List AllocEvent → Prop}
    {LoopAdvEnv : W4LoopAdvEnv} {maxOps : Nat}
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv₀ : UnreachedPqxdhPrimitives → DecPkGhost → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (X : UnreachedPqxdhPrimitives)
    (hSlot : ∀ g e, DecPkEnv g e ↔
      realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixedOf verNeEnv LoopAdvEnv maxOps X W g e)
    (hUnguarded : ∀ X',
      DecPkD2cSlotOkFrozenPlacedAt (cliGhostExterns gh (cliExternsPlaced mmpl W)) X' W A lim
        (DecPkEnv₀ X'))
    (hBridge : ∀ X' g evs,
      filesOk₀ scopeIn (fun _ => True) g.F g.peer.val g.me.val →
      DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn g.F g.peer.val g.me.val g.msg →
      PeerSpqrStateTight640 W.C.F W.Q.K g.F g.peer.val →
      DecPkEnv₀ X' g evs →
      realCliDecPkBinaryWideSlotEnvCmkVerNeFixedOf verNeEnv LoopAdvEnv maxOps X' W g evs) :
    DecPkD2cSlotOkFrozenPlaced mmpl gh W A lim DecPkEnv :=
  decPkD2cSlotOkFrozenPlaced_cmkWithP3CGuarded_of_unguarded X hSlot hUnguarded hBridge

/-- Default `(VerNeTightTopEnv, CmkLoopAdvanceEvs, 109)` universal-`X` `DecPkD2cSlotOkFrozenPlaced` guarded-slot wrapper. -/
theorem decPkD2cSlotOkFrozenPlaced_cmkVerNeGuarded_of_unguarded [LibsignalPlacement]
    {M : AllocCostModel}
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv₀ : UnreachedPqxdhPrimitives → DecPkGhost → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (X : UnreachedPqxdhPrimitives)
    (hSlot : ∀ g e, DecPkEnv g e ↔ realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixed X W g e)
    (hUnguarded : ∀ X',
      DecPkD2cSlotOkFrozenPlacedAt (cliGhostExterns gh (cliExternsPlaced mmpl W)) X' W A lim
        (DecPkEnv₀ X'))
    (hBridge : ∀ X' g evs,
      filesOk₀ scopeIn (fun _ => True) g.F g.peer.val g.me.val →
      DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn g.F g.peer.val g.me.val g.msg →
      PeerSpqrStateTight640 W.C.F W.Q.K g.F g.peer.val →
      DecPkEnv₀ X' g evs →
      realCliDecPkBinaryWideSlotEnvCmkVerNeFixed X' W g evs) :
    DecPkD2cSlotOkFrozenPlaced mmpl gh W A lim DecPkEnv :=
  decPkD2cSlotOkFrozenPlaced_cmkVerNeGuardedOf_of_unguarded X hSlot hUnguarded hBridge

/-- `(LoopAdvEnv, maxOps, P3PathCEnv)`-parametric `hRunSub` eliminator from `PeerSpqrStateTight640`. -/
theorem realCliDecPkBinaryWideSlotEnvCmkWithP3CFixedOf_of_guarded_tight [LibsignalPlacement]
    {LoopAdvEnv : W4LoopAdvEnv} {maxOps : Nat}
    {P3PathCEnv : W4BinaryRecvPrekeyParamsCmk → List AllocEvent → Prop}
    {X : UnreachedPqxdhPrimitives} {W : CliHooks}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {x : DecPkGhost} {evs : List AllocEvent}
    (hSlot : ∀ g e, DecPkEnv g e ↔
      realCliDecPkBinaryWideSlotEnvCmkWithP3CGuardedFixedOf LoopAdvEnv maxOps P3PathCEnv X W g e)
    (hTight : PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val)
    (hevs : DecPkEnv x evs) :
    realCliDecPkBinaryWideSlotEnvCmkWithP3CFixedOf LoopAdvEnv maxOps P3PathCEnv X W x evs :=
  targetEnv_of_guarded_tight hSlot hTight hevs

/-- `(LoopAdvEnv, maxOps, P3PathCEnv)`-parametric `hRunSub` eliminator at `.recv peer` under `CliPqxdhInputs ⟨W.C, W.Q⟩ i`. -/
theorem realCliDecPkBinaryWideSlotEnvCmkWithP3CFixedOf_of_guarded_cliPqInputs_recv [LibsignalPlacement]
    {LoopAdvEnv : W4LoopAdvEnv} {maxOps : Nat}
    {P3PathCEnv : W4BinaryRecvPrekeyParamsCmk → List AllocEvent → Prop}
    {X : UnreachedPqxdhPrimitives} {W : CliHooks} {i : Inputs} {peer : AddrV}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {x : DecPkGhost} {evs : List AllocEvent}
    (hSlot : ∀ g e, DecPkEnv g e ↔
      realCliDecPkBinaryWideSlotEnvCmkWithP3CGuardedFixedOf LoopAdvEnv maxOps P3PathCEnv X W g e)
    (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peer))
    (hF : x.F = runFiles i) (hpeer : x.peer.val = addrValOf peer)
    (hevs : DecPkEnv x evs) :
    realCliDecPkBinaryWideSlotEnvCmkWithP3CFixedOf LoopAdvEnv maxOps P3PathCEnv X W x evs :=
  targetEnv_of_guarded_cliPqInputs_recv hSlot hi hparse hF hpeer hevs

theorem realCliDecPkBinaryWideSlotEnvCmkVerNeFixedOf_of_guarded_tight [LibsignalPlacement]
    {verNeEnv : List (BitVec 8) → List AllocEvent → Prop}
    {LoopAdvEnv : W4LoopAdvEnv} {maxOps : Nat}
    {X : UnreachedPqxdhPrimitives} {W : CliHooks}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {x : DecPkGhost} {evs : List AllocEvent}
    (hSlot : ∀ g e, DecPkEnv g e ↔
      realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixedOf verNeEnv LoopAdvEnv maxOps X W g e)
    (hTight : PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val)
    (hevs : DecPkEnv x evs) :
    realCliDecPkBinaryWideSlotEnvCmkVerNeFixedOf verNeEnv LoopAdvEnv maxOps X W x evs :=
  realCliDecPkBinaryWideSlotEnvCmkWithP3CFixedOf_of_guarded_tight hSlot hTight hevs

theorem realCliDecPkBinaryWideSlotEnvCmkVerNeFixed_of_guarded_tight [LibsignalPlacement]
    {X : UnreachedPqxdhPrimitives} {W : CliHooks}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {x : DecPkGhost} {evs : List AllocEvent}
    (hSlot : ∀ g e, DecPkEnv g e ↔ realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixed X W g e)
    (hTight : PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val)
    (hevs : DecPkEnv x evs) :
    realCliDecPkBinaryWideSlotEnvCmkVerNeFixed X W x evs :=
  realCliDecPkBinaryWideSlotEnvCmkVerNeFixedOf_of_guarded_tight hSlot hTight hevs

theorem realCliDecPkBinaryWideSlotEnvCmkVerNeFixedOf_of_guarded_cliPqInputs_recv [LibsignalPlacement]
    {verNeEnv : List (BitVec 8) → List AllocEvent → Prop}
    {LoopAdvEnv : W4LoopAdvEnv} {maxOps : Nat}
    {X : UnreachedPqxdhPrimitives} {W : CliHooks} {i : Inputs} {peer : AddrV}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {x : DecPkGhost} {evs : List AllocEvent}
    (hSlot : ∀ g e, DecPkEnv g e ↔
      realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixedOf verNeEnv LoopAdvEnv maxOps X W g e)
    (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peer))
    (hF : x.F = runFiles i) (hpeer : x.peer.val = addrValOf peer)
    (hevs : DecPkEnv x evs) :
    realCliDecPkBinaryWideSlotEnvCmkVerNeFixedOf verNeEnv LoopAdvEnv maxOps X W x evs :=
  realCliDecPkBinaryWideSlotEnvCmkWithP3CFixedOf_of_guarded_cliPqInputs_recv
    hSlot hi hparse hF hpeer hevs

/-- Default `(VerNeTightTopEnv, CmkLoopAdvanceEvs, 109)` `hRunSub` eliminator at `.recv peer` under `CliPqxdhInputs ⟨W.C, W.Q⟩ i`. -/
theorem realCliDecPkBinaryWideSlotEnvCmkVerNeFixed_of_guarded_cliPqInputs_recv [LibsignalPlacement]
    {X : UnreachedPqxdhPrimitives} {W : CliHooks} {i : Inputs} {peer : AddrV}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {x : DecPkGhost} {evs : List AllocEvent}
    (hSlot : ∀ g e, DecPkEnv g e ↔ realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixed X W g e)
    (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peer))
    (hF : x.F = runFiles i) (hpeer : x.peer.val = addrValOf peer)
    (hevs : DecPkEnv x evs) :
    realCliDecPkBinaryWideSlotEnvCmkVerNeFixed X W x evs :=
  realCliDecPkBinaryWideSlotEnvCmkVerNeFixedOf_of_guarded_cliPqInputs_recv
    hSlot hi hparse hF hpeer hevs

end LibsignalBinary.Proofs.PeakBudget.CliDpPollTrustedWideBridge
