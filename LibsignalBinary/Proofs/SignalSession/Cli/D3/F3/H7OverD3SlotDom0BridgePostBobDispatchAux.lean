/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2PurePlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevCapPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudgetAux
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1DefsPlacedBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedABudget
public import LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
public import LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
public import LibsignalBinary.Proofs.PeakBudget.RealMainBinaryEnvAdapterD3
public import LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux
public import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux
public import LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds
public import LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.W4PathCVerNeWideDefs
public import LibsignalBinary.Proofs.PeakBudget.W4PostBobPrev1Derive
public import LibsignalBinary.Proofs.PeakBudget.W4PostBobPrev1Dom
public import LibsignalBinary.Proofs.PeakBudget.W4PostBobPrev1DomIdle
public import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0
public import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0TdAux
public import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkSlot
public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget
public import LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverEnvPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPollPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotDom0LeafL23
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotDom0LeafL45R
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotWideWitness
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4ContPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.StagesOverCliPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget

/-!
# `OverD3` Slot-to-`Dom0'` Bridge Dispatch Helpers

Auxiliary 6-arm dispatch proof for
`H7OverD3SlotDom0BridgePostBob.h7w_decPkValidOverTight_sub_zbDom0'FixedOf` mapping
`DecPkD3ValidOverTightConcreteEnv'` traces into `W4BinaryRecvPrekeyDomCmk0'` and
`W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrFixedOf`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotDom0BridgePostBobDispatchAux

open Arm64.Process (bytesOfString)
open CryptoGames.LibsignalSession (Crypto PublicKey SignalMessage)
open CryptoGames.LibsignalSessionApi (Session SessionRecord)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3 (genP3S5Model)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (SessionExtraRel)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (clearPending)
open CryptoVerification.E2E (
  LocalIdentity PEParams PreKeyMessageFields ResponderPreKeySecrets UnreachedPqxdhPrimitives
  acceptInput modelPrims
)
open CryptoVerification.E2E.Pqxdh.ResponderCore (ofSignalPqxdhPrimitives)
open CryptoVerification.E2E.Record (encSession encodeRecord)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.LibsignalTripleRatchet.Record (CloneRel)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost SessionGhost uuidTryParse)
open CryptoVerification.RecordCodecs (IdentityKeyPair)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession (CliHooks Inputs)
open CryptoVerification.SignalSession.Cli (StoresGhost)
open CryptoVerification.SignalSession.Cli.MainHops (AddrV CallV RunCall cliIo cliRunBudgets parseArgs)
open CryptoVerification.SignalSession.Cli.RunCompose (DecPkGhost addrValOf runFiles)
open CryptoVerification.SignalSession.Cli.RunProofs (SessMatchesPm pkStoreKeys pkToE?)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (
  cliKitStk cliPollIdKitPlaced cliPollKpkKitPlaced cliPollPkKitPlaced cliPollSessKitPlaced
  cliPollSessPrev1KitPlaced pathAInitSession pathAInitState pmPreKeyId
)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (scopeKit)
open LibsignalBinary.Heap (AllocEvent SeqEnv)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2PurePlacedBudget (
  InitializeBobV1OptFieldsEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevCapPlacedBudget (
  StageP3ErrM3Env StageP3OkPrefixM3Env
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudgetAux (
  StageP3Prev1Env StageP3VerNePrev1Env
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1DefsPlacedBudget (
  StageP4Prev1ExitEnv
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedABudget (AcceptOptFieldsEnv)
open LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs (
  W4BinaryStageP2MatchedWideEnv W4CloneACDomEnv W4CloneBDomEnv
)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed (
  W4BinaryStageP1OkEnvAllFixed W4BinaryStageP2PathAWideEnvAllFixed
  W4BinaryStageP4MatchedWideEnvAllFixed W4BinaryStageP4PathAWideEnvAllFixed
)
open LibsignalBinary.Proofs.PeakBudget.RealMainBinaryEnvAdapterD3 (CliPqOrD3RecvDom)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (msgCapBytes sessionCapBytes)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux (TopStateTight)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds (FreshBobCloneDom SessionCloneDom)
open LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec (OptStageEnv W4StageP3WideEnv)
open LibsignalBinary.Proofs.PeakBudget.W4PostBobPrev1DomIdle (postBobPrev1Dom_idle_exists)
open LibsignalBinary.Proofs.PeakBudget.W4PathCVerNeWideDefs (VerNeTightTopRawEnv)
open LibsignalBinary.Proofs.PeakBudget.W4PostBobPrev1Derive (
  postBobPrev1Dom_of_arm4 postBobPrev1Dom_of_leaves
)
open LibsignalBinary.Proofs.PeakBudget.W4PostBobPrev1Dom (
  PostBobPrev1Dom W4BinaryCallSiteDomCmk' W4BinaryCallSiteDomCmk0' W4BinaryRecvPrekeyDomCmk0'
  W4RecvPrekeyCmkDom0Of' postBobTotalPrev1Cap286K w4PostBobPqCap
)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0 (
  W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrAllFixedOf W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrFixedOf
  W4RecvPrekeyTryDecACCmkSrEnvOf W4TrialRunWideCmkSrEnvOf mkW4RecvPrekeyWideCmkSrSlotParamsOf
  w4c_wideSlotEnvCmkVerNeSrAllFixed_eq_fixed_of_cliPqOrD3RecvDom
)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0TdAux (
  W4FailedTdCancelCmkSrEnvOf W4StatesRecvEnv w4c_TryDecryptCliLinkedSrEnvOf
)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkSlot (
  W4BinaryRecvPrekeyParamsCmk W4LoopAdvEnv W4RecvPrekeyRealParamsCmk
)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget (SessionGhostValid)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux (SessDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.D3 (ScopeOverIn)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPollPlacedBudget (
  CliStageP1OkEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotDom0LeafL23 (
  h7l23_encSession_clearPending_le_encodeRecord h7l23_encodeRecord_clearPending_le_cap
  h7l23_loadRel_encodeRecord_le_sessionCap
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotDom0LeafL45R (
  h7l45r_pathAInit_freshBobCloneDom h7l45r_pathAInit_receiverChains_nil
  h7l45r_pathAInit_topStateTight
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotWideWitness (
  H7wCallSiteDomOut1 H7wOverSlotEnvAllFixedOf h7w_overSlotEnv_to_fourArmAllFixed
  h7w_witness_p1Ok h7w_witness_p2Over h7w_witness_p3ErrM3 h7w_witness_p3Prev1
  h7w_witness_p3VerNe h7w_witness_p4Prev1Exit h7w_witness_untrusted
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (ReadFileRuleEnvFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4ContPlacedBudget (
  CliStageP4Prev1Envs cliPollSessPrev1SeqFreeBudgetEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudgetAux (
  StageP2OverEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudget (
  P2OverPathCErrEnvOf P2OverPathCOkEnvOf PromoteOverArchiveCanonSessEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.StagesOverCliPlacedBudget (
  cliPollSelfBudgetEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget (
  CliDpPollUntrustedEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux (
  cliStageP2KitEnvs
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget (
  cliPollIdBudgetEnv cliPollKpkBudgetEnv cliPollPkBudgetEnv
)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)

/-! ## 1. `rfl`-Compatible Mirror of `DecPkD3ValidOverTightConcreteEnv'` (Cycle-Free) -/

/-- Cycle-free mirror of `H7OverD3SlotDom0BridgePostBob.h7pb_cliStageP4Prev1SeqFreeEnvs` (`rfl`). -/
def H7pbCliStageP4Prev1SeqFreeEnvs [LibsignalPlacement] (A : RustAlloc)
    (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
    (pid kpkId spkId : BitVec 32) (kbk : PublicKey)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop) :
    CliStageP4Prev1Envs (A := A) B F0 peer pid kpkId spkId kbk where
  opsEnv := cliPollSessPrev1SeqFreeBudgetEnv A F0 peer (cliKitStk B)
  ikitEnv := cliPollIdBudgetEnv A F0 peer (cliKitStk B) ReadEnv
  pkKitEnv := cliPollPkBudgetEnv A F0 pid (cliKitStk B) ReadEnv
  kpkKitEnv := cliPollKpkBudgetEnv A F0 kpkId spkId kbk (cliKitStk B) ReadEnv

/-- Cycle-free mirror of `H7OverD3SlotDom0BridgePostBob.DecPkD3ValidOverOfEnv'` (`rfl`). -/
def H7pbDecPkD3ValidOverOfEnv' [LibsignalPlacement] (A : RustAlloc)
    (verNeEnv : List (BitVec 8) → List AllocEvent → Prop)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop)
    (p4Envs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
      CliStageP4Prev1Envs (A := A) B F0 peer pid kpkId spkId kbk)
    (g : DecPkGhost) (evs : List AllocEvent) : Prop :=
  let σ := cliKitStk B
  let P1 := CliStageP1OkEnv (A := A) B ReadEnv DeserEnv g
  CliDpPollUntrustedEnv (A := A) B ReadEnv DeserEnv g evs ∨
  P1 evs ∨
  ∃ (r : SessionRecord (List (BitVec 8))) (s_old : Session (List (BitVec 8))),
    (cliPollSessKitPlaced A g.F scopeKit g.peer σ).loadRel
      StoresGhost.opened.sessions g.peer.val (.ok (some r)) ∧
    r.currentSession = some s_old ∧
    ScopeOverIn r ∧
    ¬ SessMatchesPm s_old g.msg ∧
    (SeqEnv P1 (StageP2OverEnv P2OverErrEnv P2OverOkEnv g r) evs ∨
     (∃ m i k kp reg dk recG whisperG,
       pkToE? g.msg = some m ∧
       g.msg.message = i ∧
       SignalMessage.tryFrom protoSignalCodec m.inner = .ok i ∧
       pkStoreKeys g.F m = some k ∧
       StoresGhost.opened.identity.keyPair cliIo.rd g.F = .ok kp ∧
       StoresGhost.opened.identity.regId cliIo.rd g.F = .ok reg ∧
       SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
         (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk ∧
       SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) ∧
       SessionGhostValid recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) ∧
       SeqEnv (SeqEnv P1 (P2OverOkEnv g r))
         (StageP3Prev1Env (tdEnv W) verNeEnv recG
           (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
           g.peer g.me whisperG g.msg.message
           (g.msg.message.messageVersion.zeroExtend 32)
           (encSession (clearPending s_old)) g.coins) evs) ∨
     (∃ m i k, ∃ kp : IdentityKeyPair, ∃ reg dk recG G₁ whisperG,
       pkToE? g.msg = some m ∧
       g.msg.message = i ∧
       SignalMessage.tryFrom protoSignalCodec m.inner = .ok i ∧
       pkStoreKeys g.F m = some k ∧
       StoresGhost.opened.identity.keyPair cliIo.rd g.F = .ok kp ∧
       StoresGhost.opened.identity.regId cliIo.rd g.F = .ok reg ∧
       SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
         (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk ∧
       SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) ∧
       SessionGhostValid recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) ∧
       CloneRel recG G₁ ∧
       SeqEnv (SeqEnv P1 (P2OverOkEnv g r))
         (StageP3ErrM3Env (tdEnv W) recG G₁
           (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
           g.peer g.me whisperG g.msg.message g.coins) evs) ∨
     (∃ m i k, ∃ kp : IdentityKeyPair, ∃ reg dk recG,
       pkToE? g.msg = some m ∧
       g.msg.message = i ∧
       SignalMessage.tryFrom protoSignalCodec m.inner = .ok i ∧
       pkStoreKeys g.F m = some k ∧
       StoresGhost.opened.identity.keyPair cliIo.rd g.F = .ok kp ∧
       StoresGhost.opened.identity.regId cliIo.rd g.F = .ok reg ∧
       SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
         (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk ∧
       SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) ∧
       SessionGhostValid recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) ∧
       SeqEnv (SeqEnv P1 (P2OverOkEnv g r))
         (StageP3VerNePrev1Env verNeEnv recG
           (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
           (encSession (clearPending s_old))) evs) ∨
     (∃ m i k kp reg dk recG G₁ G' pt whisperG,
       pkToE? g.msg = some m ∧
       g.msg.message = i ∧
       SignalMessage.tryFrom protoSignalCodec m.inner = .ok i ∧
       pkStoreKeys g.F m = some k ∧
       StoresGhost.opened.identity.keyPair cliIo.rd g.F = .ok kp ∧
       StoresGhost.opened.identity.regId cliIo.rd g.F = .ok reg ∧
       SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
         (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk ∧
       SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) ∧
       SessionGhostValid recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) ∧
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
       SessionGhostValid G' ses' ∧
       SeqEnv
         (SeqEnv (SeqEnv P1 (P2OverOkEnv g r))
           (StageP3OkPrefixM3Env (tdEnv W) recG G₁ st0
             g.peer g.me whisperG g.msg.message g.coins))
         (StageP4Prev1ExitEnv
           (cliPollSessPrev1KitPlaced A g.F g.peer σ) envs.opsEnv
           (cliPollIdKitPlaced A g.F g.peer σ) envs.ikitEnv
           (cliPollPkKitPlaced A g.F pid σ) envs.pkKitEnv
           (cliPollKpkKitPlaced A g.F m.kpkId m.spkId g.msg.baseKey σ) envs.kpkKitEnv
           StoresGhost.opened.sessions StoresGhost.opened.identity
           StoresGhost.opened.oneTime StoresGhost.opened.kyber
           m.opkId g.peer.val g.msg.identityKey m.kpkId m.spkId g.msg.baseKey G' ses'
           (encSession (clearPending s_old))) evs))

/-- Cycle-free mirror of `H7OverD3SlotDom0BridgePostBob.DecPkD3ValidOverTightConcreteEnv'` (`rfl`). -/
abbrev H7pbDecPkD3ValidOverTightConcreteEnv' [LibsignalPlacement]
    (A : RustAlloc) (W : CliHooks) (X : UnreachedPqxdhPrimitives)
    (tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop)
    (g : DecPkGhost) (evs : List AllocEvent) : Prop :=
  let ReadEnv := ReadFileRuleEnvFixed cliIo.rd
  let selfEnv := fun F0 peer => cliPollSelfBudgetEnv A F0 peer (cliKitStk cliRunBudgets) ReadEnv
  let kitEnvs := cliStageP2KitEnvs (A := A) ReadEnv cliRunBudgets selfEnv
  H7pbDecPkD3ValidOverOfEnv' A VerNeTightTopRawEnv W X cliRunBudgets
    ReadEnv
    SessDeserializeCancelEnv
    (P2OverPathCErrEnvOf (A := A) X W cliRunBudgets
      (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
      (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
      kitEnvs)
    (P2OverPathCOkEnvOf (A := A) X W cliRunBudgets
      (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
      PromoteOverArchiveCanonSessEnv
      kitEnvs)
    tdEnv
    (fun B F0 peer pid kpkId spkId kbk =>
      H7pbCliStageP4Prev1SeqFreeEnvs A B F0 peer pid kpkId spkId kbk ReadEnv)
    g evs

/-! ## 2. `toCallSiteDomCmk0'` Conversion & Witness Helpers -/

/-- Converts `H7wCallSiteDomOut1 (PostBobPrev1Dom ...)` into `W4BinaryCallSiteDomCmk0'`. -/
theorem h7pb_toCallSiteDomCmk0'
    {C : Crypto} {K : MlKem} {maxCt : Nat} {peerVal : AddrVal} {files : FsFiles}
    {R : W4RecvPrekeyRealParamsCmk}
    (h : H7wCallSiteDomOut1
      (PostBobPrev1Dom w4PostBobPqCap 2097152 postBobTotalPrev1Cap286K)
      C K maxCt peerVal files R) :
    W4BinaryCallSiteDomCmk0' C K maxCt peerVal files R :=
  ⟨{ eq_C := h.eq_C
     eq_K := h.eq_K
     eq_rd := h.eq_rd
     eq_files := h.eq_files
     eq_peerVal := h.eq_peerVal
     kpk_dir := h.kpk_dir
     ownKey_len := h.ownKey_len
     ownReg_len := h.ownReg_len
     kpkMark_len := h.kpkMark_len
     res_old := h.res_old
     res_new := h.res_new
     spqr_key := h.spqr_key
     cur_dom := h.cur_dom
     arch_valid := h.arch_valid
     arch_enc := h.arch_enc
     out0_valid := h.out0_valid
     out0_enc := h.out0_enc
     out1_postBob := h.out1_dom
     trials_len4 := h.trials_len4
     cur_fail_dom := h.cur_fail_dom
     trials_dom := h.trials_dom
     tdB_dom := h.tdB_dom
     tdAC_dom := h.tdAC_dom },
   h.archivedTrials_nil⟩

private theorem e2ar_overSlotEnv_to_allFixed
    {SR : W4StatesRecvEnv} {LoopAdvEnv : W4LoopAdvEnv} {maxOps : Nat}
    {w : W4BinaryRecvPrekeyParamsCmk} {evs : List AllocEvent}
    (h : H7wOverSlotEnvAllFixedOf
      (W4FailedTdCancelCmkSrEnvOf SR LoopAdvEnv maxOps)
      (W4TrialRunWideCmkSrEnvOf SR LoopAdvEnv maxOps)
      (w4c_TryDecryptCliLinkedSrEnvOf SR LoopAdvEnv maxOps) w evs) :
    W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrAllFixedOf SR LoopAdvEnv maxOps w evs := by
  let P := mkW4RecvPrekeyWideCmkSrSlotParamsOf SR LoopAdvEnv maxOps w.base
  exact h7w_overSlotEnv_to_fourArmAllFixed
    (fun e =>
      SeqEnv (W4BinaryStageP1OkEnvAllFixed w.base.rd w.base.files w.base.peer w.remoteIdKey)
        (SeqEnv
          (OptStageEnv
            (W4BinaryStageP2MatchedWideEnv P.DecEnv P.TrialEnv P.DropEnv P.archivedTrials
              w.base.g_arch w.base.r_arch))
          (SeqEnv (OptStageEnv (W4StageP3WideEnv W4CloneBDomEnv P.TryDecEnv))
            (OptStageEnv
              (W4BinaryStageP4MatchedWideEnvAllFixed w.base.rd w.base.files w.base.peer
                w.remoteIdKey w.base.g_out0 w.base.r_out0)))) e)
    (fun e =>
      SeqEnv (W4BinaryStageP1OkEnvAllFixed w.base.rd w.base.files w.base.peer w.remoteIdKey)
        (SeqEnv
          (OptStageEnv
            (W4BinaryStageP2PathAWideEnvAllFixed w.base.hasOpk w.base.rd w.base.files
              w.base.spkId w.base.kpkId w.base.opkId w.base.C.F w.base.x_res w.base.x_spqr))
          (SeqEnv
            (OptStageEnv
              (W4StageP3WideEnv W4CloneACDomEnv
                (W4RecvPrekeyTryDecACCmkSrEnvOf SR LoopAdvEnv maxOps w.base)))
            (OptStageEnv
              (W4BinaryStageP4PathAWideEnvAllFixed w.base.hasOpk w.base.rd w.base.files w.base.peer
                w.remoteIdKey w.base.kpkId w.base.spkId w.base.opkId w.baseKey
                w.base.g_out0 w.base.r_out0)))) e)
    h

private theorem e2ar_finish_witness
    {SR : W4StatesRecvEnv} {LoopAdvEnv : W4LoopAdvEnv} {maxOps : Nat}
    {W : CliHooks} {g : RunCall} {peerV : AddrV} {x : DecPkGhost} {evs : List AllocEvent}
    (hi : CliPqOrD3RecvDom ⟨W.C, W.Q⟩ g.i)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV))
    (hfiles : x.F = runFiles g.i)
    (hpeer : x.peer.val = addrValOf peerV)
    (hw : ∃ w4 : W4BinaryRecvPrekeyParamsCmk,
      H7wCallSiteDomOut1
        (PostBobPrev1Dom w4PostBobPqCap 2097152 postBobTotalPrev1Cap286K)
        W.C W.Q.K msgCapBytes x.peer.val x.F w4.base ∧
      w4.remoteIdKey = x.msg.identityKey ∧
      w4.baseKey = x.msg.baseKey ∧
      H7wOverSlotEnvAllFixedOf
        (W4FailedTdCancelCmkSrEnvOf SR LoopAdvEnv maxOps)
        (W4TrialRunWideCmkSrEnvOf SR LoopAdvEnv maxOps)
        (w4c_TryDecryptCliLinkedSrEnvOf SR LoopAdvEnv maxOps) w4 evs) :
    ∃ w4 : W4BinaryRecvPrekeyParamsCmk,
      W4BinaryRecvPrekeyDomCmk0' SR LoopAdvEnv maxOps (.recv peerV) g.i w4 ∧
      w4.remoteIdKey = x.msg.identityKey ∧
      w4.baseKey = x.msg.baseKey ∧
      W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrFixedOf SR LoopAdvEnv maxOps w4 evs := by
  obtain ⟨w4, hdom, hrem, hbk, hall⟩ := hw
  have hdom' : H7wCallSiteDomOut1
      (PostBobPrev1Dom w4PostBobPqCap 2097152 postBobTotalPrev1Cap286K)
      W.C W.Q.K msgCapBytes (addrValOf peerV) (runFiles g.i) w4.base := by
    rwa [hpeer, hfiles] at hdom
  have hcs0 : W4BinaryCallSiteDomCmk0' W.C W.Q.K msgCapBytes
      (addrValOf peerV) (runFiles g.i) w4.base :=
    h7pb_toCallSiteDomCmk0' hdom'
  have hcmk0 : W4RecvPrekeyCmkDom0Of' SR LoopAdvEnv maxOps sessionCapBytes msgCapBytes w4.base :=
    W4BinaryCallSiteDomCmk0'.toCmkDom0Of' SR LoopAdvEnv maxOps hcs0 hparse (Nat.le_refl msgCapBytes)
  have hrecvDom : W4BinaryRecvPrekeyDomCmk0' SR LoopAdvEnv maxOps (.recv peerV) g.i w4 := by
    intro peerAddr hcall
    cases hcall
    exact ⟨hcs0.1.eq_peerVal, hcmk0.1.outer_dom.peer_len, hcs0.1.eq_files, hcs0.1.eq_rd, hcmk0⟩
  have hfixed : W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrFixedOf SR LoopAdvEnv maxOps w4 evs := by
    have hall4 := e2ar_overSlotEnv_to_allFixed hall
    rwa [w4c_wideSlotEnvCmkVerNeSrAllFixed_eq_fixed_of_cliPqOrD3RecvDom
      hi hcs0.1.eq_files hcs0.1.eq_rd] at hall4
  exact ⟨w4, hrecvDom, hrem, hbk, hfixed⟩

private theorem e2ar_sessionCloneDom_16K_to_postBob {s : Session (List (BitVec 8))}
    (hdom : SessionCloneDom 16384 s) :
    SessionCloneDom w4PostBobPqCap s where
  rc_len := hdom.rc_len
  seeds32 := hdom.seeds32
  alice_len := hdom.alice_len
  kyber_cap := hdom.kyber_cap
  pq_len := Nat.le_trans hdom.pq_len (by decide)

private theorem e2ar_freshBob_postBobPrev1Dom
    (P : PEParams) (me : LocalIdentity) (k : ResponderPreKeySecrets)
    (m : PreKeyMessageFields) (dk : SignalPqxdh.DRKey)
    (recG : SessionGhost) {enc : List (BitVec 8)}
    (hgv : SessionGhostValid recG (pathAInitSession P me k m dk))
    (hprev : enc.length ≤ 2097152) :
    PostBobPrev1Dom w4PostBobPqCap 2097152 postBobTotalPrev1Cap286K
      recG (pathAInitSession P me k m dk) enc := by
  have hClone := h7l45r_pathAInit_freshBobCloneDom P me k m dk recG hgv
  have hrc1 : (pathAInitSession P me k m dk).state.receiverChains.length ≤ 1 := by
    have hnil : (pathAInitState P me k m dk).receiverChains = [] :=
      h7l45r_pathAInit_receiverChains_nil P me k m dk
    change (pathAInitState P me k m dk).receiverChains.length ≤ 1
    rw [hnil]
    decide
  exact postBobPrev1Dom_of_leaves hrc1 hgv (e2ar_sessionCloneDom_16K_to_postBob hClone.dom) hprev

/-! ## 3. Six-Arm `OverD3` Slot-to-`Dom0'` Dispatch -/

/-- Dispatches all 6 arms of `DecPkD3ValidOverTightConcreteEnv'` into
`W4BinaryRecvPrekeyDomCmk0'` and `W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrFixedOf` given an
idle `PostBobPrev1Dom` witness `hIdle`. -/
theorem h7pb_decPkValidOverTight_sub_zbDom0'FixedOf_of_idle [LibsignalPlacement]
    (hIdle : ∃ G_idle ses_idle,
      PostBobPrev1Dom w4PostBobPqCap 2097152 postBobTotalPrev1Cap286K G_idle ses_idle [])
    {SR : W4StatesRecvEnv} {LoopAdvEnv : W4LoopAdvEnv} {maxOps : Nat}
    (A : RustAlloc) (W : CliHooks) (X : UnreachedPqxdhPrimitives)
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    (htdSub : ∀ a e,
      TopStateTight W.C.F W.Q.K a.st.pqRatchetState →
      a.msg.ciphertext.length ≤ msgCapBytes →
      tdEnv W a e →
      w4c_TryDecryptCliLinkedSrEnvOf SR LoopAdvEnv maxOps W.C W.Q.K a e)
    {g : RunCall} {peerV : AddrV} {x : DecPkGhost}
    (hi : CliPqOrD3RecvDom ⟨W.C, W.Q⟩ g.i)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV))
    (hfiles : x.F = runFiles g.i)
    (hpeer : x.peer.val = addrValOf peerV)
    (hct : x.msg.message.ciphertext.length ≤ msgCapBytes)
    (evs : List AllocEvent)
    (hevs : H7pbDecPkD3ValidOverTightConcreteEnv' A W X tdEnv x evs) :
    ∃ w4 : W4BinaryRecvPrekeyParamsCmk,
      W4BinaryRecvPrekeyDomCmk0' SR LoopAdvEnv maxOps (.recv peerV) g.i w4 ∧
      w4.remoteIdKey = x.msg.identityKey ∧
      w4.baseKey = x.msg.baseKey ∧
      W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrFixedOf SR LoopAdvEnv maxOps w4 evs := by
  obtain ⟨G_idle, ses_idle, hOut1Idle0⟩ := hIdle
  refine e2ar_finish_witness hi hparse hfiles hpeer ?_
  rcases hevs with h0 | h1 | ⟨r, s_old, hload, hcur, _hScope, _hNotMatch, hRest⟩
  · exact h7w_witness_untrusted A W x G_idle ses_idle hOut1Idle0 h0
  · exact h7w_witness_p1Ok A W x G_idle ses_idle hOut1Idle0 h1
  · have hCap : (encodeRecord ⟨some (clearPending s_old)⟩).length ≤ 2097152 :=
      h7l23_encodeRecord_clearPending_le_cap A ⟨W.C, W.Q⟩ cliRunBudgets hi hfiles hload hcur
    have hprevEnc : (encSession (clearPending s_old)).length ≤ 2097152 :=
      Nat.le_trans (h7l23_encSession_clearPending_le_encodeRecord r s_old hcur)
        (h7l23_loadRel_encodeRecord_le_sessionCap hi hfiles hload)
    rcases hRest with h2 | h3 | h4 | h5 | h6
    · exact h7w_witness_p2Over A X W x r s_old G_idle ses_idle hcur hCap hOut1Idle0 h2
    · obtain ⟨m, _i, k, kp, reg, dk, recG, whisperG, _hm, _hi_eq, _htry, _hk, _hkp, _hreg,
        _hacc, _hex, hgv, hp3⟩ := h3
      let P_pe : PEParams := ⟨W.C, W.Q⟩
      let me_id : LocalIdentity := ⟨kp.privateKey.bytes, reg⟩
      exact h7w_witness_p3Prev1 A X W htdSub x r s_old recG
        (pathAInitSession P_pe me_id k m dk) whisperG
        recG (pathAInitSession P_pe me_id k m dk)
        hcur hCap
        (h7l45r_pathAInit_freshBobCloneDom P_pe me_id k m dk recG hgv)
        (h7l45r_pathAInit_topStateTight P_pe me_id k m dk)
        hct
        (e2ar_freshBob_postBobPrev1Dom P_pe me_id k m dk recG hgv (Nat.zero_le _))
        (e2ar_freshBob_postBobPrev1Dom P_pe me_id k m dk recG hgv hprevEnc)
        hp3
    · obtain ⟨m, _i, k, kp, reg, dk, recG, G₁, whisperG, _hm, _hi_eq, _htry, _hk, _hkp, _hreg,
        _hacc, _hex, hgv, _hcl, hp3⟩ := h4
      let P_pe : PEParams := ⟨W.C, W.Q⟩
      let me_id : LocalIdentity := ⟨kp.privateKey.bytes, reg⟩
      exact h7w_witness_p3ErrM3 A X W htdSub x r s_old recG G₁
        (pathAInitSession P_pe me_id k m dk) whisperG
        recG (pathAInitSession P_pe me_id k m dk)
        hcur hCap
        (h7l45r_pathAInit_freshBobCloneDom P_pe me_id k m dk recG hgv)
        (h7l45r_pathAInit_topStateTight P_pe me_id k m dk)
        hct
        (e2ar_freshBob_postBobPrev1Dom P_pe me_id k m dk recG hgv (Nat.zero_le _))
        (e2ar_freshBob_postBobPrev1Dom P_pe me_id k m dk recG hgv hprevEnc)
        hp3
    · obtain ⟨m, _i, k, kp, reg, dk, recG, _hm, _hi_eq, _htry, _hk, _hkp, _hreg,
        _hacc, _hex, hgv, hp3⟩ := h5
      let P_pe : PEParams := ⟨W.C, W.Q⟩
      let me_id : LocalIdentity := ⟨kp.privateKey.bytes, reg⟩
      exact h7w_witness_p3VerNe (tdEnv := tdEnv) A X W x r s_old recG
        (pathAInitSession P_pe me_id k m dk)
        recG (pathAInitSession P_pe me_id k m dk)
        hcur hCap
        (h7l45r_pathAInit_freshBobCloneDom P_pe me_id k m dk recG hgv)
        (e2ar_freshBob_postBobPrev1Dom P_pe me_id k m dk recG hgv (Nat.zero_le _))
        (e2ar_freshBob_postBobPrev1Dom P_pe me_id k m dk recG hgv hprevEnc)
        hp3
    · obtain ⟨m, _i, k, kp, reg, dk, recG, G₁, G', pt, whisperG, hm, _hi_eq, _htry, _hk, _hkp,
        _hreg, _hacc, _hex, hgv, _hcl, _haft, hok, hgv', hp4⟩ := h6
      let P_pe : PEParams := ⟨W.C, W.Q⟩
      let me_id : LocalIdentity := ⟨kp.privateKey.bytes, reg⟩
      have hOut1Post :=
        postBobPrev1Dom_of_arm4 P_pe me_id k m dk x.peer x.me x.msg.message x.coins
          hok hgv' hprevEnc
      exact h7w_witness_p4Prev1Exit A X W htdSub x r s_old m recG G₁ G'
        (pathAInitSession P_pe me_id k m dk)
        { pathAInitSession P_pe me_id k m dk with
          state := (genP3S5Model W.C W.Q.K x.peer x.me x.msg.message x.coins
            (pathAInitState P_pe me_id k m dk)).2
          pendingPreKey := none
          pendingKyberPreKey := none }
        whisperG
        hcur hm hCap
        (h7l45r_pathAInit_freshBobCloneDom P_pe me_id k m dk recG hgv)
        (h7l45r_pathAInit_topStateTight P_pe me_id k m dk)
        hct hOut1Post hp4

theorem h7pb_decPkValidOverTight_sub_zbDom0'FixedOf [LibsignalPlacement]
    {SR : W4StatesRecvEnv} {LoopAdvEnv : W4LoopAdvEnv} {maxOps : Nat}
    (A : RustAlloc) (W : CliHooks) (X : UnreachedPqxdhPrimitives)
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    (htdSub : ∀ a e,
      TopStateTight W.C.F W.Q.K a.st.pqRatchetState →
      a.msg.ciphertext.length ≤ msgCapBytes →
      tdEnv W a e →
      w4c_TryDecryptCliLinkedSrEnvOf SR LoopAdvEnv maxOps W.C W.Q.K a e)
    {g : RunCall} {peerV : AddrV} {x : DecPkGhost}
    (hi : CliPqOrD3RecvDom ⟨W.C, W.Q⟩ g.i)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV))
    (hfiles : x.F = runFiles g.i)
    (hpeer : x.peer.val = addrValOf peerV)
    (hct : x.msg.message.ciphertext.length ≤ msgCapBytes)
    (evs : List AllocEvent)
    (hevs : H7pbDecPkD3ValidOverTightConcreteEnv' A W X tdEnv x evs) :
    ∃ w4 : W4BinaryRecvPrekeyParamsCmk,
      W4BinaryRecvPrekeyDomCmk0' SR LoopAdvEnv maxOps (.recv peerV) g.i w4 ∧
      w4.remoteIdKey = x.msg.identityKey ∧
      w4.baseKey = x.msg.baseKey ∧
      W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrFixedOf SR LoopAdvEnv maxOps w4 evs :=
  h7pb_decPkValidOverTight_sub_zbDom0'FixedOf_of_idle postBobPrev1Dom_idle_exists
    A W X htdSub hi hparse hfiles hpeer hct evs hevs

end LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotDom0BridgePostBobDispatchAux
