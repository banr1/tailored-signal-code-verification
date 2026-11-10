/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2PurePlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2V1PlacedBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedABudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobCutPlacedBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobErrOwnedPlacedBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.RecvWireSameAccountPlaced
public import LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentitySelfStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveAuxBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveDefsBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchivePromoteBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Over.MatchCalleeBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKitBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkCliPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.PreKeySpecsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SelfSpecPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.UuidFsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverFoldsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1AgreePlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1BasePlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueXCliPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable CLI Poll Stage P2 Over-Path (`Path C`) Instantiation

Budget-threaded `[LibsignalPlacement]` instantiation of Stage P2 on overwrite path `Path C` under
`RustCliAllocBudget M`, defining deterministic pre-state-pinned envelopes
(`PromoteOverCanonSessEnv`, `P2OverPathCErrEnvOf`, `P2OverPathCOkEnvOf`) and instantiating
`StageP2PathCOverQpanCliPlacedStmt` and its `LibsignalFrozen` and pointwise companions.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudget

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudgetAux (
  P2OverPathCErrEnvAux P2OverPathCOkEnvAux P2OverPathCOkEnvAuxOf
  PromoteOverArchiveCanonSessEnvLocal PromoteOverArchiveEnvLocal PromoteOverCanonSessEnvLocal
  StageP2PathCOverQpanCliFrozenPlacedAtStmt StageP2PathCOverQpanCliMemInvPlacedAtStmt
  promoteOverArchiveEnv_eq_canon promoteOverEnv_eq_canon_pub
  stageP2PathCOver_qpan_cli_full_placed_at_of_seams_aux
  stageP2PathCOver_qpan_cli_full_placed_of_seams_aux stageP2PathCOver_qpan_cli_placed_of_seams_aux
)

open Arm64 Arm64.Process ProofLib
open CryptoGames.LibsignalSession (
  PublicKey ShaCompress SignalMessage
)
open CryptoGames.LibsignalSessionApi (ApiError Session SessionRecord)
open CryptoVerification (
  LibsignalFrozen LibsignalFullPlacement LibsignalPlacement lsBlackBoxU8Sym lsProg_51 lsProg_75
  lsmpl lsρ withLsCl
)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.RecordCodecs (
  IdentityKeyPair KyberPreKeyRecord PreKeyRecord SignedPreKeyRecord
)
open CryptoVerification.E2E (
  PreKeyMessageFields ResponderPreKeySecrets UnreachedPqxdhPrimitives
  acceptInput modelPrims
)
open CryptoVerification.E2E.Pqxdh.Initiator (
  AcceptKeysInput DRKey Primitives StructuralPrims ofSignalPqxdhAcceptKeysInput
)
open CryptoVerification.E2E.Pqxdh.Initiator.Model (acceptKeys)
open CryptoVerification.E2E.Pqxdh.ResponderCore (ofSignalPqxdhPrimitives)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (ClosureCalleeSaved)
open CryptoVerification.E2E.Record (encSession)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal preKeyMsgAt)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  FsAt FsFiles IdentitySelfStoreSpec IdentitySelfVtablesPlacedOk IdentityStoreSpec
  KyberPreKeyStoreSpec KyberPreKeyVtablesPlacedOk LibsignalCodeRoLoaded
  PreKeyStoreSpec PreKeyVtablesPlacedOk
  SignedPreKeyStoreSpec SignedPreKeyVtablesPlacedOk
)
open CryptoVerification.LibsignalTripleRatchet (noAllocShimSpec rootStack)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchetRepr (
  AddrGhost SessionGhost SignalMessageGhost protocolAddressAt signalMessageAt
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (
  OpkOkWitness SessionExtraRel coroOpkIdAtP4 hdrOpkIdBv? opkOkEvs opkOkUpdate p1LoadedRecordAt
  stageP1ProgPlaced
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (
  clearPending stageP2OverV1CallStack4K stageP3Sub5ExtraPrePrev1
)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli (
  CliGhostHooks StoresGhost cliGhostExterns cliIdentityVtSym cliKyberPreKeyVtSym cliPreKeyVtSym
  cliSessionVtSym cliSignedPreKeyVtSym
)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo coinsInstalledPlaced storesAt)
open CryptoVerification.SignalSession.Cli.RunGlue (cliExternsPlaced_row cliGhostExterns_other)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.RunCompose (DecPkGhost RunSem decResAt)
open CryptoVerification.SignalSession.Cli.RunProofs (
  DecPkOk₀ dpFutDoneAt pkStoreKeys pkToE? pmOfE
)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (
  DpKitStk LsTokenInit StageP1PostRegs cliKitStk cliPollIdKitPlaced cliPollKpkKitPlaced
  cliPollPkKitPlaced cliPollSelfKitPlaced cliPollSpkKitPlaced dpClosSubStack
  dpPollEntryPlaced dpPollProgPlaced mkPathAHdr pathAInitSession pathAInitState
  stageP2PostP1At stageP3CoroFrameAt stageP3StackFrameAt
)
open CryptoVerification.SignalSession.Cli.Slots (
  FilesOkPeer blackBox_row_placed cliGhostExterns_sat_of_cliExternsPlaced scopeIn scopeKit
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs
  RustCliAllocBudget SeqEnv rustAllocEvents rustDeallocEvents
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (growOneVecU8BudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionShimBudgetSpec)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (
  PreKeyStoreBudgetEnv
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
open LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveDefsBudget (ArchiveCoreEnv)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget (SerContractsXPlaced)
open LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget (BoundedRustEvs)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptBudget (pqxdhAcceptOptFieldsPlacedSpec)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedABudget (AcceptOptFieldsEnv)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobCutPlacedBudget (AcceptSuccessEnv)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobErrOwnedPlacedBudget (
  pqxdhAcceptErrOwnedPlacedSpec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1PlacedBudget (
  p2Sub1Events
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget (
  InitializeBobV1Env StageP2ClosureHooksPlaced StageP2PureCalleesPlaced4K
  StageP2PureCalleesPlaced4KOfEnv initializeBobSessionErrOwned4KPlacedSpec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2PurePlacedBudget (
  InitializeBobV1OptFieldsEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsPlacedBudget (
  PromoteMatchingMissGenPlacedProp PromoteOverEnv PromoteOverGenPlacedProp
  PromoteOverGenPlacedWithEnvProp
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Mid2PlacedBudget (
  P2OverSub1To3Arm1Env P2OverSub1To3Arm2Env
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Mid3PlacedBudget (
  P2OverSub1To4Arm3Env
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2V1PlacedBudget (
  P2OverV1Arm4Env P2OverV1Arm5EnvOfAcceptErr P2OverV1Arm6EnvOfBob P2OverV1OkEnvOfBobAndProm
  stageP2OverV1KitsAtPlacedOfEnvProp stageP2OverV1KitsAtPlacedProp
  stageP2_over_v1_kits_ext_placed stageP2_over_v1_kits_ext_placed_ofEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget (SpqrV1PlacedSeams)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (CliGhostAllocHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget (
  DpPollGhostStateBudget dpSlotPollKStatePlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget (
  RunHooksPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4SpatialPlacedBudget (
  overGenP3Pre_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudgetAux (
  StageP2OverEnv StageP2OverErrPlaced StageP2OverQpanCliPlacedStmt
)

/-! ## 1. Placed Stage P2 Over-Path (`Path C`) Model Rejection & Error Postcondition -/

/-- Pure model-rejection witness discharged on all 6 Stage P2 error arms on Path C (`Over`)
under `[LibsignalPlacement]`. -/
def StageP2PathCOverModelRejPlaced [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    {B : RunBudgets} {S : RunSem}
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S)) : Prop :=
  ∃ (m : PreKeyMessageFields) (i : SignalMessage),
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
           (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = none))

/-- Budget-threaded exit postcondition of all 6 Stage P2 store-error and PQXDH-rejection arms on
Path C (`Over`) under `[LibsignalPlacement]`, carrying `evs : List AllocEvent` in `P2OverErrEnv`. -/
def StageP2PathCOverErrPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st_b : M.σ)
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (P2OverErrEnv : DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (B : RunBudgets) (S : RunSem)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (r : SessionRecord (List (BitVec 8)))
    (s1 sf : State) (sp : BitVec 64) (Pf : SepProp) : Prop :=
  ∃ (err : ApiError AddrVal Unit) (evs : List AllocEvent),
    P2OverErrEnv y.g r evs ∧
    err ≠ .panic ∧
    err ≠ .store () ∧
    sf.trace = s1.trace ∧
    StageP2PathCOverModelRejPlaced X W y ∧
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
      anyHeap)

/-! ## 2. Placed Kit Event Simplifications (`cliPoll*KitPlaced`) -/

theorem p2Over_cliPollSpk_getEvs_placed [LibsignalPlacement] {A : RustAlloc} {F : FsFiles}
    {sid id : BitVec 32} {σ : DpKitStk}
    (ans : Except (cliPollSpkKitPlaced A F sid σ).GetErr SignedPreKeyRecord) :
    (cliPollSpkKitPlaced A F sid σ).getEvs id ans = [] := rfl

theorem p2Over_cliPollKpk_getEvs_placed [LibsignalPlacement] {A : RustAlloc} {F : FsFiles}
    {kid sid id : BitVec 32} {kbk : PublicKey} {σ : DpKitStk}
    (ans : Except (cliPollKpkKitPlaced A F kid sid kbk σ).GetErr KyberPreKeyRecord) :
    (cliPollKpkKitPlaced A F kid sid kbk σ).getEvs id ans = [] := rfl

theorem p2Over_cliPollPk_getEvs_placed [LibsignalPlacement] {A : RustAlloc} {F : FsFiles}
    {pid id : BitVec 32} {σ : DpKitStk}
    (ans : Except (cliPollPkKitPlaced A F pid σ).GetErr PreKeyRecord) :
    (cliPollPkKitPlaced A F pid σ).getEvs id ans = [] := rfl

theorem p2Over_cliPollPk_opkOkEvs_placed [LibsignalPlacement] {A : RustAlloc} {F : FsFiles}
    {pid : BitVec 32} {σ : DpKitStk}
    (opt : Option (BitVec 32)) (wOpk : OpkOkWitness opt) :
    opkOkEvs (cliPollPkKitPlaced A F pid σ) opt wOpk = [] := by
  cases opt <;> rfl

theorem p2Over_cliPollPk_opkOkUpdate_placed [LibsignalPlacement] (A : RustAlloc) (F : FsFiles)
    (pid : BitVec 32) (σ : DpKitStk)
    (opt : Option (BitVec 32)) (wOpk : OpkOkWitness opt) :
    opkOkUpdate (cliPollPkKitPlaced A F pid σ) StoresGhost.opened.oneTime opt wOpk =
      StoresGhost.opened.oneTime := by
  cases opt <;> rfl

theorem p2Over_cliPollSelf_kpEvs_placed [LibsignalPlacement] {A : RustAlloc} {F : FsFiles}
    {peer : AddrGhost} {σ : DpKitStk}
    (ans : Except (cliPollSelfKitPlaced A F peer σ).KpErr IdentityKeyPair) :
    (cliPollSelfKitPlaced A F peer σ).kpEvs ans = [] := rfl

theorem p2Over_cliPollSelf_regIdEvs_placed [LibsignalPlacement] {A : RustAlloc} {F : FsFiles}
    {peer : AddrGhost} {σ : DpKitStk}
    (ans : Except (cliPollSelfKitPlaced A F peer σ).RegIdErr (BitVec 32)) :
    (cliPollSelfKitPlaced A F peer σ).regIdEvs ans = [] := rfl

/-! ## 3. Deterministic Pre-State-Pinned CLI Poll Stage P2 Envelopes -/

/-- Bundle of budget envelopes for the 4 CLI Poll store kits at `(B, F0, peer, spkId, kpkId,
opkWord, kbk)`. -/
structure CliPollStageP2Envs [LibsignalPlacement] {A : RustAlloc}
    (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
    (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey) where
  selfEnv : IdentitySelfStoreBudgetEnv (cliPollSelfKitPlaced A F0 peer (cliKitStk B))
  spkEnv : SignedPreKeyStoreBudgetEnv (cliPollSpkKitPlaced A F0 spkId (cliKitStk B))
  kpkEnv : KyberPreKeyStoreBudgetEnv (cliPollKpkKitPlaced A F0 kpkId spkId kbk (cliKitStk B))
  pkEnv : PreKeyStoreBudgetEnv (cliPollPkKitPlaced A F0 opkWord (cliKitStk B))

/-- Canonical-session specialization of `PromoteOverEnv` eliminating `SessionGhost`:
under `CanonSession recG sess`, `encSessionMem_clearPending_eq` identifies
`(encSessionMem (clearPendingGhost recG) (clearPending sess)).length` with
`(encSession (clearPending sess)).length`. -/
def PromoteOverCanonSessEnv (sess : Session (List (BitVec 8))) : List AllocEvent → Prop :=
  let n := (encSession (clearPending sess)).length
  SeqEnv FreeOnlyEvs (SeqEnv (BoundedRustEvs (4 * n + 34) (2 * n + 96)) FreeOnlyEvs)

example (sess : Session (List (BitVec 8))) : PromoteOverCanonSessEnv sess [] :=
  Or.inl (by simp [FreeOnlyEvs])

/-- Deterministic pre-state-pinned union of the six Stage P2 error envelopes for CLI Poll Path C Stage P2,
keyed by `(g : DecPkGhost)` with zero unpinned existential witnesses. -/
def P2OverPathCErrEnvOf [LibsignalPlacement] {A : RustAlloc}
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (B : RunBudgets)
    (BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop)
    (AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop)
    (kitEnvs : ∀ (F0 : FsFiles) (peer : AddrGhost) (spkId kpkId opkWord : BitVec 32)
      (kbk : PublicKey), CliPollStageP2Envs (A := A) B F0 peer spkId kpkId opkWord kbk)
    (g : DecPkGhost) (_r : SessionRecord (List (BitVec 8))) (evs : List AllocEvent) : Prop :=
  match pkToE? g.msg with
  | none => False
  | some m =>
      let opkWord := m.opkId.getD 0#32
      let ke := kitEnvs g.F g.peer m.spkId m.kpkId opkWord g.msg.baseKey
      let spkBox := (cliPollSpkKitPlaced A g.F m.spkId (cliKitStk B)).getBoxSize
      let spkPoll := ke.spkEnv.getPollEnv StoresGhost.opened.signed m.spkId
      let kpkBox := (cliPollKpkKitPlaced A g.F m.kpkId m.spkId g.msg.baseKey (cliKitStk B)).getBoxSize
      let kpkPoll := ke.kpkEnv.getPollEnv StoresGhost.opened.kyber m.kpkId
      let pkBox := (cliPollPkKitPlaced A g.F opkWord (cliKitStk B)).getBoxSize
      let pkPoll := ke.pkEnv.getPollEnv StoresGhost.opened.oneTime
      let kpBox := (cliPollSelfKitPlaced A g.F g.peer (cliKitStk B)).kpBoxSize
      let kpPoll := ke.selfEnv.kpPollEnv StoresGhost.opened.identity
      let regBox := (cliPollSelfKitPlaced A g.F g.peer (cliKitStk B)).regIdBoxSize
      let regPoll := ke.selfEnv.regIdPollEnv StoresGhost.opened.identity
      let opkId? := hdrOpkIdBv? (mkPathAHdr m)
      P2OverSub1To3Arm1Env spkBox spkPoll evs ∨
      P2OverSub1To3Arm2Env spkBox spkPoll kpkBox kpkPoll evs ∨
      P2OverSub1To4Arm3Env spkBox spkPoll kpkBox kpkPoll pkBox pkPoll opkId? evs ∨
      P2OverV1Arm4Env spkBox spkPoll kpkBox kpkPoll pkBox pkPoll kpBox opkId? kpPoll evs ∨
      (match pkStoreKeys g.F m, StoresGhost.opened.identity.keyPair cliIo.rd g.F with
       | some k, .ok kp =>
           let inp := ofSignalPqxdhAcceptKeysInput
             (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ k m)
           P2OverV1Arm5EnvOfAcceptErr spkBox spkPoll kpkBox kpkPoll pkBox pkPoll kpBox opkId?
             kpPoll (AcceptErrEnv inp) evs ∨
           (match acceptKeys (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) inp with
            | none => False
            | some drKey =>
                P2OverV1Arm6EnvOfBob spkBox spkPoll kpkBox kpkPoll pkBox pkPoll kpBox opkId?
                  kpPoll (BobV1Env inp drKey) regBox regPoll evs)
       | _, _ => False)

example [LibsignalPlacement] {A : RustAlloc}
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (B : RunBudgets)
    (kitEnvs : ∀ F0 peer spkId kpkId opkWord kbk,
      CliPollStageP2Envs (A := A) B F0 peer spkId kpkId opkWord kbk)
    (g : DecPkGhost) (r : SessionRecord (List (BitVec 8))) (m : PreKeyMessageFields)
    (hm : pkToE? g.msg = some m) :
    P2OverPathCErrEnvOf X W B (InitializeBobV1Env W.C.F) (fun _ => (· = [])) kitEnvs g r
      (p2Sub1Events (cliPollSpkKitPlaced A g.F m.spkId (cliKitStk B)).getBoxSize) := by
  unfold P2OverPathCErrEnvOf
  rw [hm]
  exact Or.inl (Or.inl rfl)

/-- Deterministic pre-state-pinned normal-exit (`+0x1778`) envelope for CLI Poll Path C Stage P2,
keyed by `(g : DecPkGhost)` and `(r : SessionRecord (List (BitVec 8)))` with zero unpinned
existential witnesses. -/
def P2OverPathCOkEnvOf [LibsignalPlacement] {A : RustAlloc}
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (B : RunBudgets)
    (BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop)
    (PromSessEnv : Session (List (BitVec 8)) → List AllocEvent → Prop)
    (kitEnvs : ∀ (F0 : FsFiles) (peer : AddrGhost) (spkId kpkId opkWord : BitVec 32)
      (kbk : PublicKey), CliPollStageP2Envs (A := A) B F0 peer spkId kpkId opkWord kbk)
    (g : DecPkGhost) (r : SessionRecord (List (BitVec 8))) (evs : List AllocEvent) : Prop :=
  match pkToE? g.msg, r.currentSession with
  | some m, some sess =>
      match pkStoreKeys g.F m, StoresGhost.opened.identity.keyPair cliIo.rd g.F with
      | some k, .ok kp =>
          let inp := ofSignalPqxdhAcceptKeysInput
            (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ k m)
          match acceptKeys (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) inp with
          | none => False
          | some drKey =>
              let opkWord := m.opkId.getD 0#32
              let ke := kitEnvs g.F g.peer m.spkId m.kpkId opkWord g.msg.baseKey
              let spkBox := (cliPollSpkKitPlaced A g.F m.spkId (cliKitStk B)).getBoxSize
              let spkPoll := ke.spkEnv.getPollEnv StoresGhost.opened.signed m.spkId
              let kpkBox := (cliPollKpkKitPlaced A g.F m.kpkId m.spkId g.msg.baseKey (cliKitStk B)).getBoxSize
              let kpkPoll := ke.kpkEnv.getPollEnv StoresGhost.opened.kyber m.kpkId
              let pkBox := (cliPollPkKitPlaced A g.F opkWord (cliKitStk B)).getBoxSize
              let pkPoll := ke.pkEnv.getPollEnv StoresGhost.opened.oneTime
              let kpBox := (cliPollSelfKitPlaced A g.F g.peer (cliKitStk B)).kpBoxSize
              let kpPoll := ke.selfEnv.kpPollEnv StoresGhost.opened.identity
              let regBox := (cliPollSelfKitPlaced A g.F g.peer (cliKitStk B)).regIdBoxSize
              let regPoll := ke.selfEnv.regIdPollEnv StoresGhost.opened.identity
              let opkId? := hdrOpkIdBv? (mkPathAHdr m)
              let promTail := SeqEnv (fun e => e = rustDeallocEvents regBox 8)
                (SeqEnv (PromSessEnv sess)
                  (fun e => e = rustDeallocEvents 1568 1 ++ rustDeallocEvents 3168 1))
              P2OverV1OkEnvOfBobAndProm spkBox spkPoll kpkBox kpkPoll pkBox pkPoll kpBox opkId?
                kpPoll (BobV1Env inp drKey) regBox regPoll promTail evs
      | _, _ => False
  | _, _ => False

example [LibsignalPlacement] {A : RustAlloc}
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (B : RunBudgets)
    (kitEnvs : ∀ F0 peer spkId kpkId opkWord kbk,
      CliPollStageP2Envs (A := A) B F0 peer spkId kpkId opkWord kbk)
    (g : DecPkGhost) (r : SessionRecord (List (BitVec 8)))
    (m : PreKeyMessageFields) (sess : Session (List (BitVec 8)))
    (k : ResponderPreKeySecrets) (kp : IdentityKeyPair) (drKey : DRKey)
    (hm : pkToE? g.msg = some m) (hcur : r.currentSession = some sess)
    (hk : pkStoreKeys g.F m = some k)
    (hkp : StoresGhost.opened.identity.keyPair cliIo.rd g.F = .ok kp)
    (hacc : acceptKeys (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩))
      (ofSignalPqxdhAcceptKeysInput
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ k m)) = some drKey) :
    P2OverPathCOkEnvOf X W B (InitializeBobV1Env W.C.F) PromoteOverCanonSessEnv kitEnvs g r
      (p2Sub1Events (cliPollSpkKitPlaced A g.F m.spkId (cliKitStk B)).getBoxSize) := by
  simp only [P2OverPathCOkEnvOf, hm, hcur, hk, hkp, hacc]
  exact Or.inl (Or.inl (Or.inl rfl))

/-! ## 4. Budget-Threaded `StageP2PathCOverQpanCliPlacedStmt` & Callee Instantiations -/

/-- Budget-threaded Placed Stage P2 Path C (`Over`) CPS contract statement at
`dpPollEntryPlaced + 0x0868#64`, parameterized over `PromoteMatchingMissGenPlacedProp` and
`PromoteOverGenPlacedWithEnvProp`. -/
def StageP2PathCOverQpanCliPlacedStmt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PromEnv : SessionGhost → Session (List (BitVec 8)) → List AllocEvent → Prop)
    (P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop) : Prop :=
  ∀ (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (B : RunBudgets) (S : RunSem)
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (st_b : M.σ)
    (g1 : StoresGhost)
    (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (s0 s1 : State) (sp rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (Q Qpan : State → SepProp → Prop),
    PromoteMatchingMissGenPlacedProp A.repAlloc (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
    PromoteOverGenPlacedWithEnvProp M A lim PromEnv (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
    RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
    FitsEnv M lim st_b (StageP2OverEnv P2OverErrEnv P2OverOkEnv y.g r) →
    y.g.coins.length < 2 ^ 63 →
    DecPkOk₀ ⟨W.C, W.Q⟩ (fun _ => False) y.g.F y.g.peer.val y.g.me.val y.g.msg →
    (∀ r', Scope r' → scopeIn r') →
    FilesOkPeer Scope y.g.F y.g.peer.val →
    r.currentSession = some sess →
    scopeIn r →
    ¬ CryptoVerification.SignalSession.Cli.RunProofs.DecPkS0.SessMatchesPm sess y.g.msg →
    StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val y.g.msg.identityKey = .ok true →
    g1 = StoresGhost.opened →
    FsAt (fun f => f = y.g.F) True (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s1 →
    LibsignalCodeRoLoaded lsmpl s1.mem →
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
      StageP2PathCOverErrPlaced A lim st_b P2OverErrEnv X W B S y r s1 sf sp Pf →
      Q sf Pf) →
    (hok : ∀ (s2 : State) (evs_p2 : List AllocEvent)
      (m : PreKeyMessageFields) (i : SignalMessage)
      (k : ResponderPreKeySecrets)
      (kp : IdentityKeyPair) (reg : BitVec 32)
      (dk : SignalPqxdh.DRKey)
      (G_bob : SessionGhost)
      (prevCap' prevPtr' : BitVec 64)
      (whisperMsgPtr : BitVec 64) (whisperG : SignalMessageGhost)
      (preKeyMsgRem : SepProp),
      P2OverOkEnv y.g r evs_p2 →
      prevCap' ≠ 0#64 →
      y.g.msg = pmOfE m i →
      SignalMessage.tryFrom protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel G_bob
        (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) →
      (signalMessageAt A.repAlloc whisperG whisperMsgPtr y.g.msg.message ∗
        ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem ⊢
        preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg) →
      Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s1 s2 →
      s2.trace = s1.trace →
      s2.pc = dpPollEntryPlaced + 0x1778#64 →
      s2.status = .Running →
      s2.sp = sp →
      (s2.sp &&& 15#64 == 0#64) = true →
      s2.readReg64 .x19 = y.fut →
      s2.readReg64 .x27 = sp + 0x370#64 →
      s2.readReg64 .x29 = s0.sp - 0x60#64 →
      calleeSavedVRegs s2 = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl s2.mem →
      SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s2
        (LsTokenInit ∗
         overGenP3Pre_placed A lim (M.stepEvents evs_p2 st_b) s2.sp (s2.readReg64 .x29) y.fut
           y.cx y.g.peerA y.g.meA whisperMsgPtr y.g.coinsP
           (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
           G_bob (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
           y.g.peer y.g.me whisperG y.g.msg.message s2 ∗
         stageP3Sub5ExtraPrePrev1 A.repAlloc s0 s2 y.fut y.out 8#64 prevCap' prevPtr'
           (encSession (clearPending sess)) 0#8 ∗
         stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
           (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
           (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
           (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
           (coroOpkIdAtP4 y.fut m.opkId)
           (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗
            ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
         stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
         ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
         ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
         preKeyMsgRem ∗
         storesAt A.repAlloc y.g.stores g1 ∗
         memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack))
        Q Qpan) →
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

private theorem subroutine_ok_withLsCl_of_spec_map [LibsignalPlacement] {α β : Type}
    {prog : Program} {entry : BitVec 64} {specA : Spec α} {specB : Spec β}
    (f : β → α)
    (hpre : ∀ x s, specB.pre x s = specA.pre (f x) s)
    (hpost : ∀ x s0 sf, specA.post (f x) s0 sf = specB.post x s0 sf)
    (hpan : ∀ x s0 sf, specA.onPanic (f x) s0 sf = specB.onPanic x s0 sf)
    (hexit : ∀ x code s0 sf, specA.onExit (f x) code s0 sf = specB.onExit x code s0 sf)
    (hoom : ∀ x s0 sf, specA.onOom (f x) s0 sf = specB.onOom x s0 sf)
    (hok : subroutine_ok prog entry (CryptoVerification.withLsCl lsmpl specA)) :
    subroutine_ok prog entry (CryptoVerification.withLsCl lsmpl specB) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hp halign => ?_
  have hp' : s0.mem ⊨ (CryptoVerification.withLsCl lsmpl specA).pre (f x) s0 ∗ R := by
    dsimp only [CryptoVerification.withLsCl] at hp ⊢
    rwa [← hpre x s0]
  refine hok.mono_outcome (f x) R s0 hpc hrun hp' halign ?_
  rintro sf (⟨hret, hcs, hq⟩ | ⟨hp1, hpa⟩ | ⟨code, he1, he2⟩ | ⟨ho1, hoo⟩)
  · refine Or.inl ⟨hret, hcs, ?_⟩
    dsimp only [CryptoVerification.withLsCl] at hq ⊢
    rwa [← hpost x s0 sf]
  · refine Or.inr (Or.inl ⟨hp1, ?_⟩)
    dsimp only [CryptoVerification.withLsCl] at hpa ⊢; rwa [← hpan x s0 sf]
  · refine Or.inr (Or.inr (Or.inl ⟨code, he1, ?_⟩))
    dsimp only [CryptoVerification.withLsCl] at he2 ⊢; rwa [← hexit x code s0 sf]
  · refine Or.inr (Or.inr (Or.inr ⟨ho1, ?_⟩))
    dsimp only [CryptoVerification.withLsCl] at hoo ⊢; rwa [← hoom x s0 sf]

/-- Relocatable `VmPreserved` `PromoteMatchingMissGenPlacedProp` (`lsmpl.base 50`) from `h_bb`. -/
theorem promoteMatchingMissGen_placed_of_blackBox [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h_bb : ext lsBlackBoxU8Sym = some CryptoVerification.LibsignalSession.blackBoxHook) :
    PromoteMatchingMissGenPlacedProp A ext := by
  have h50' : subroutine_ok (CryptoVerification.CliHandshake.RespClosurePlaced.lsProg_518 ext)
      (lsmpl.base 50)
      (CryptoVerification.withLsCl lsmpl
        (LibsignalBinary.Proofs.PublicApi.StoreKit.Over.MatchDefsBudget.promoteMatchingSessionMissSpec A)) :=
    CryptoVerification.LibsignalTripleRatchet.ls_subroutine_ok_cl_of_callee
      (callerProg := CryptoVerification.CliHandshake.RespClosurePlaced.lsProg_518 ext)
      (LibsignalBinary.Proofs.PublicApi.StoreKit.Over.MatchCalleeBudget.promote_matching_session_miss_placed_ok h_bb)
  exact subroutine_ok_withLsCl_of_spec_map
    (fun x : CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.P2PromoteMissGhost =>
      (⟨x.recPtr, x.msgVer, x.serPtr, x.serBytes, x.outPtr, x.g, x.r, x.s⟩ :
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.PromoteMissGhost))
    (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ _ _ => rfl) (fun _ _ _ => rfl) h50'

/-- Relocatable `VmPreserved` `PromoteMatchingMissGenPlacedProp` (`lsmpl.base 50`) at
`cliGhostExterns gh (cliExternsPlaced mmpl W)`. -/
theorem cliPromoteMatchingMissGen_placed_ok [LibsignalPlacement] (A : RustAlloc)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) :
    PromoteMatchingMissGenPlacedProp A (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  promoteMatchingMissGen_placed_of_blackBox
    ((cliGhostExterns_other gh _ (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)).trans
      (cliExternsPlaced_row mmpl W (blackBox_row_placed mmpl W)))

private theorem boundedRustEvs_rustAlloc_one (n : Nat) (hn : n < 2 ^ 32) :
    BoundedRustEvs 1 (max n 16) (LibsignalBinary.Heap.rustAllocEvents n 1) := by
  unfold LibsignalBinary.Heap.rustAllocEvents
  by_cases h1 : 1 ≤ n
  · have hcond : 1 ≤ 16 ∧ 1 ≤ n := ⟨by decide, h1⟩
    rw [ite_eq_left hcond]
    refine ⟨Nat.le_refl 1, fun ev hev => ?_⟩
    simp only [List.mem_singleton] at hev
    subst hev
    exact ⟨Nat.le_trans (Nat.le_of_lt hn) (by decide), Nat.le_max_left n 16,
      (fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩
  · have hn0 : n = 0 := by omega
    subst hn0
    have hcond : ¬ (1 ≤ 16 ∧ 1 ≤ 0) := by decide
    rw [ite_eq_right hcond]
    refine ⟨by decide, fun ev hev => ?_⟩
    simp only [List.mem_singleton] at hev
    subst hev
    exact ⟨by decide, by decide,
      (fun al _ h => by cases h; decide), (fun _ _ _ h => nomatch h)⟩

private theorem boundedRustEvs_grow96 :
    BoundedRustEvs 1 96 (LibsignalBinary.Heap.rustAllocEvents 96 8) := by
  change BoundedRustEvs 1 96 [.alloc 96]
  refine ⟨by decide, fun ev hev => ?_⟩
  simp only [List.mem_singleton] at hev
  subst hev
  exact ⟨by decide, by decide, (fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩

private theorem archiveCoreEnv_imp_promoteOverEnv
    {prevCap : BitVec 64} {G : SessionGhost} {sess : Session (List (BitVec 8))}
    (hlen :
      (CryptoVerification.E2E.Record.Serialization.encSessionMem
        (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.clearPendingGhost G)
        (clearPending sess)).length < 2 ^ 32)
    {evs : List AllocEvent}
    (h : LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveDefsBudget.ArchiveCoreEnv
      prevCap G sess evs) :
    PromoteOverEnv G sess evs := by
  dsimp only [LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveDefsBudget.ArchiveCoreEnv,
    PromoteOverEnv,
    LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsBudget.PromoteOverAllocMidEnv]
    at h ⊢
  set n :=
    (CryptoVerification.E2E.Record.Serialization.encSessionMem
      (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.clearPendingGhost G)
      (clearPending sess)).length
  have hn_eq :
      (CryptoVerification.E2E.Record.Serialization.encSessionMem
        (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.OverP2.clearPendingGhost G)
        (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.OverP2.clearPending sess)).length = n := rfl
  rw [hn_eq]
  have hlen1 : BoundedRustEvs 1 (max n 16) (LibsignalBinary.Heap.rustAllocEvents n 1) :=
    boundedRustEvs_rustAlloc_one n hlen
  have hgrow_b : ∀ e3 : List AllocEvent,
      (if prevCap = 0#64 then e3 = LibsignalBinary.Heap.rustAllocEvents 96 8 else e3 = []) →
      BoundedRustEvs 1 96 e3 := by
    intro e3 hg
    split at hg
    · subst hg; exact boundedRustEvs_grow96
    · subst hg; exact BoundedRustEvs.nil 1 96
  rcases h with hf1 | ⟨e1, e23, rfl, hf1, h23⟩
  · exact Or.inl hf1
  · refine Or.inr ⟨e1, e23, rfl, hf1, ?_⟩
    rcases h23 with rfl | ⟨e2, e34, rfl, rfl, h34⟩
    · exact Or.inl (hlen1.mono (by omega) (by omega))
    · rcases h34 with hgrow | ⟨e3, e4, rfl, hgrow, hf4⟩
      · exact Or.inl ((hlen1.append (hgrow_b e34 hgrow)).mono (by omega) (by omega))
      · rw [← List.append_assoc]
        exact Or.inr ⟨LibsignalBinary.Heap.rustAllocEvents n 1 ++ e3, e4, rfl,
          (hlen1.append (hgrow_b e3 hgrow)).mono (by omega) (by omega), hf4⟩

/-- Relocatable budget-threaded `PromoteOverGenPlacedProp` (`lsmpl.base 47`) from
`SerContractsXPlaced`, a Block `51`→`621` `grow_one` budget contract, and
`EncodeRawPreallocPlacedOkX`. -/
theorem promoteOverGen_placed_of_contracts [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hC : SerContractsXPlaced M A lim ext)
    (hGrow : subroutine_ok (lsProg_51 ext) (lsmpl.base 621)
      (withLsCl lsmpl (growOneVecU8BudgetSpec M A lim)))
    (hRaw : EncodeRawPreallocPlacedOkX A.repAlloc ext) :
    PromoteOverGenPlacedProp M A lim ext := by
  have h47 :=
    LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchivePromoteBudget.promote_state_over_gen_placed_cl_of_contracts
      (callerProg := CryptoVerification.CliHandshake.RespClosurePlaced.lsProg_518 ext)
      (callerBlk := 518) hC hGrow hRaw
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre halign => ?_
  let y : CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.PromoteOverGenGhost :=
    { recPtr := x.recPtr, src := x.src, prevCap := x.prevCap, prevPtr := x.prevPtr,
      G := x.G, sess := x.sess, newBs := x.newBs }
  have hlen :
      (CryptoVerification.E2E.Record.Serialization.encSessionMem
        (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.clearPendingGhost x.G)
        (clearPending x.sess)).length < 2 ^ 32 := by
    have hp := hpre
    dsimp only [CryptoVerification.withLsCl,
      LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsBudget.p2PromoteOverGenSpec,
      LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsBudget.p2PromoteOverGenSpecWithEnv]
      at hp
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hp
    rcases hp with ⟨⟨_, _, _, hlen, _⟩, _⟩
    exact hlen
  have hpre' : s0.mem ⊨
      (CryptoVerification.withLsCl lsmpl
        (LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveDefsBudget.promoteOverGenSpec
          M A lim)).pre (y, st) s0 ∗ R := by
    refine Satisfies.mono (sepConj_mono_left (sepConj_mono_left ?_)) hpre
    rw [LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveAuxBudget.promoteOverGenSpec_pre_eq]
    dsimp only [
      LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsBudget.p2PromoteOverGenSpec,
      LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsBudget.p2PromoteOverGenSpecWithEnv,
      LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveDefsBudget.PromoteOverGenEnv, y]
    refine Entails.pure_left fun ⟨h0, h1, hnb, hlen', hfit⟩ => ?_
    exact Entails.pure_right
      (hfit.mono fun evs hevs => archiveCoreEnv_imp_promoteOverEnv hlen' hevs)
      (Entails.pure_right ⟨h0, h1, hnb, hlen'⟩ (Entails.of_eq (by ac_rfl)))
  refine h47.mono_outcome (y, st) R s0 hpc hrun hpre' halign ?_
  rintro sf (⟨hret, hcs, hpost⟩ | hpan | hexit | hoom)
  · refine Or.inl ⟨hret, hcs, ?_⟩
    refine Satisfies.mono (sepConj_mono_left (sepConj_mono_right ?_)) hpost
    rw [LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveAuxBudget.promoteOverGenSpec_post_eq]
    dsimp only [
      LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsBudget.p2PromoteOverGenSpec,
      LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsBudget.p2PromoteOverGenSpecWithEnv,
      LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveDefsBudget.PromoteOverGenEnv, y]
    refine Entails.sepExists_elim fun evs => Entails.pure_left fun hevs => ?_
    have hpool :
        A.pool lim (M.stepEvents evs st) sf ⊢
          ∃∗ evs' : List AllocEvent,
            ⌜PromoteOverEnv x.G x.sess evs'⌝ ∗ A.pool lim (M.stepEvents evs' st) sf :=
      Entails.sepExists_right evs
        (Entails.pure_right (archiveCoreEnv_imp_promoteOverEnv hlen hevs) (Entails.refl _))
    exact sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hpool))))
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl hexit))
  · exact Or.inr (Or.inr (Or.inr hoom))

private theorem hookSat_sessionMemcpyBudget_of_codec
    {H : String → Option (Arm64.State → Arm64.State)} (stk : Nat)
    (h : HookSat H CryptoVerification.lsMemcpySym
      (LibsignalBinary.Heap.SpecBudget.withVmPreserved
        CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec)) :
    HookSat H CryptoVerification.lsMemcpySym
      (LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionMemcpyBudgetSpec stk) := by
  refine ProofLib.HookSat.mono h fun ⟨dst, src, bs⟩ R s0 hpre =>
    ⟨(dst, src, bs), ProofLib.stackAt s0.sp stk ∗ R, ?_, fun sf hpost => ?_⟩
  · dsimp only [LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionMemcpyBudgetSpec,
      CryptoVerification.LibsignalTripleRatchet.sessionMemcpySpec,
      ProofLib.libcMemcpySpec,
      LibsignalBinary.Heap.SpecBudget.withVmPreserved,
      CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec] at hpre ⊢
    exact ProofLib.Satisfies.mono (ProofLib.Entails.of_eq (by ac_rfl)) hpre
  · dsimp only [LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionMemcpyBudgetSpec,
      CryptoVerification.LibsignalTripleRatchet.sessionMemcpySpec,
      LibsignalBinary.Heap.SpecBudget.withVmPreserved,
      CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec] at hpost ⊢
    exact ProofLib.Satisfies.mono (ProofLib.Entails.of_eq (by ac_rfl)) hpost

/-- Relocatable budget-threaded `PromoteOverGenPlacedProp` (`lsmpl.base 47`) at
`cliGhostExterns gh (cliExternsPlaced mmpl W)`. -/
theorem cliPromoteOverGen_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hGrow : subroutine_ok (lsProg_51 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 621)
      (withLsCl lsmpl (growOneVecU8BudgetSpec M A lim)))
    (hRaw : EncodeRawPreallocPlacedOkX A.repAlloc (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    PromoteOverGenPlacedProp M A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  promoteOverGen_placed_of_contracts
    (SerContractsXPlaced.of_hooks
      hh.codecHooks.alloc
      hh.codecHooks.dealloc
      hh.codecHooks.realloc
      ((show withVmPreserved noAllocShimSpec = sessionShimBudgetSpec from rfl) ▸ hh.codecHooks.shim)
      (cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
        (LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget.cliExternsPlaced_sessionMemmove_budget_sat
          mmpl W CryptoVerification.LibsignalTripleRatchet.extHookStack))
      (hookSat_sessionMemcpyBudget_of_codec
        CryptoVerification.LibsignalTripleRatchet.extHookStack hh.codecHooks.memcpy))
    hGrow hRaw

/-- Envelope-parametric statement of `stageP2_over_v1_kits_ext_placed_ofEnv`. -/
def StageP2OverV1KitsExtPlacedOfEnvStmt [LibsignalPlacement] : Prop :=
  ∀ {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    {PromEnv : SessionGhost → Session (List (BitVec 8)) → List AllocEvent → Prop}
    (ext : String → Option (State → State)),
    StructuralPrims P →
    StageP2ClosureHooksPlaced A lim ext →
    StageP2PureCalleesPlaced4KOfEnv P A lim F BobV1Env AcceptErrEnv ext →
    subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 75)
      (initializeBobSessionErrOwned4KPlacedSpec P A lim AcceptErrEnv) →
    ∀ (ikit : IdentityStoreSpec A.repAlloc 0#64) (skit : IdentitySelfStoreSpec ikit)
      (senv : IdentitySelfStoreBudgetEnv skit),
      IdentitySelfVtablesPlacedOk ikit skit →
      IdentitySelfStoreKitPlacedOkI A lim ikit skit senv ext →
    ∀ (spkKit : SignedPreKeyStoreSpec A.repAlloc 0#64)
      (spkEnv : SignedPreKeyStoreBudgetEnv spkKit),
      SignedPreKeyVtablesPlacedOk spkKit →
      SignedPreKeyStoreKitPlacedOk A lim spkKit spkEnv ext →
    ∀ (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64)
      (kpkEnv : KyberPreKeyStoreBudgetEnv kpkKit),
      KyberPreKeyVtablesPlacedOk kpkKit →
      KyberPreKeyStoreKitPlacedOk A lim kpkKit kpkEnv ext →
    ∀ (pkKit : PreKeyStoreSpec A.repAlloc 0#64)
      (pkEnv : PreKeyStoreBudgetEnv pkKit),
      PreKeyVtablesPlacedOk pkKit →
      PreKeyStoreKitPlacedOk A lim pkKit pkEnv ext →
    ∀ (stk : Nat), stageP2OverV1CallStack4K spkKit kpkKit pkKit skit ≤ stk →
    stageP2OverV1KitsAtPlacedOfEnvProp P A lim F BobV1Env AcceptErrEnv PromEnv ext
      skit senv spkKit spkEnv kpkKit kpkEnv pkKit pkEnv stk

/-- Default-envelope statement of `stageP2_over_v1_kits_ext_placed`. -/
def StageP2OverV1KitsExtPlacedStmt [LibsignalPlacement] : Prop :=
  ∀ {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (ext : String → Option (State → State)),
    StructuralPrims P →
    StageP2ClosureHooksPlaced A lim ext →
    StageP2PureCalleesPlaced4K P A lim F AcceptErrEnv ext →
    subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 75)
      (initializeBobSessionErrOwned4KPlacedSpec P A lim AcceptErrEnv) →
    ∀ (ikit : IdentityStoreSpec A.repAlloc 0#64) (skit : IdentitySelfStoreSpec ikit)
      (senv : IdentitySelfStoreBudgetEnv skit),
      IdentitySelfVtablesPlacedOk ikit skit →
      IdentitySelfStoreKitPlacedOkI A lim ikit skit senv ext →
    ∀ (spkKit : SignedPreKeyStoreSpec A.repAlloc 0#64)
      (spkEnv : SignedPreKeyStoreBudgetEnv spkKit),
      SignedPreKeyVtablesPlacedOk spkKit →
      SignedPreKeyStoreKitPlacedOk A lim spkKit spkEnv ext →
    ∀ (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64)
      (kpkEnv : KyberPreKeyStoreBudgetEnv kpkKit),
      KyberPreKeyVtablesPlacedOk kpkKit →
      KyberPreKeyStoreKitPlacedOk A lim kpkKit kpkEnv ext →
    ∀ (pkKit : PreKeyStoreSpec A.repAlloc 0#64)
      (pkEnv : PreKeyStoreBudgetEnv pkKit),
      PreKeyVtablesPlacedOk pkKit →
      PreKeyStoreKitPlacedOk A lim pkKit pkEnv ext →
    ∀ (stk : Nat), stageP2OverV1CallStack4K spkKit kpkKit pkKit skit ≤ stk →
    stageP2OverV1KitsAtPlacedProp P A lim F AcceptErrEnv ext
      skit senv spkKit spkEnv kpkKit kpkEnv pkKit pkEnv stk

theorem stageP2OverV1Kits_ext_placed_ofEnv_inst [LibsignalPlacement] :
    StageP2OverV1KitsExtPlacedOfEnvStmt :=
  fun {_ _ _ _ _ _ _ _} => stageP2_over_v1_kits_ext_placed_ofEnv

theorem stageP2OverV1Kits_ext_placed_inst [LibsignalPlacement] :
    StageP2OverV1KitsExtPlacedStmt :=
  fun {_ _ _ _ _ _} => stageP2_over_v1_kits_ext_placed

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

private theorem p2OverPathCOkEnvOf_eq_aux [LibsignalPlacement] {A : RustAlloc}
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (B : RunBudgets)
    (BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop)
    (kitEnvs : ∀ F0 peer spkId kpkId opkWord kbk,
      CliPollStageP2Envs (A := A) B F0 peer spkId kpkId opkWord kbk) :
    P2OverPathCOkEnvOf (A := A) X W B BobV1Env PromoteOverCanonSessEnv kitEnvs =
      P2OverPathCOkEnvAux (A := A) X W B BobV1Env
        (fun F0 peer spkId kpkId opkWord kbk => (kitEnvs F0 peer spkId kpkId opkWord kbk).selfEnv)
        (fun F0 peer spkId kpkId opkWord kbk => (kitEnvs F0 peer spkId kpkId opkWord kbk).spkEnv)
        (fun F0 peer spkId kpkId opkWord kbk => (kitEnvs F0 peer spkId kpkId opkWord kbk).kpkEnv)
        (fun F0 peer spkId kpkId opkWord kbk => (kitEnvs F0 peer spkId kpkId opkWord kbk).pkEnv) := by
  funext g r evs
  unfold P2OverPathCOkEnvOf P2OverPathCOkEnvAux
    PromoteOverCanonSessEnv PromoteOverCanonSessEnvLocal
  rfl

/-- Budget-Threaded Path C Over Stage P2 V1 Instantiation (`StageP2PathCOverQpanCliPlacedStmt`)
from `(hDropNz : lsmpl.base 547 ≠ 0#64)`, `SpqrV1PlacedSeams`, the Block `79` `Pqxdh::accept`
seams, and the 4 placed CLI store-kit `subroutine_ok` bundles. -/
theorem stageP2PathCOver_qpan_cli_placed_of_seams [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {AcceptErrEnv : UnreachedPqxdhPrimitives → CliHooks → AcceptKeysInput → List AllocEvent → Prop}
    {kitEnvs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      CliPollStageP2Envs (A := A.repAlloc) B F0 peer spkId kpkId opkWord kbk}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (hErrEnv : ∀ X W B g r evs,
      P2OverPathCErrEnvOf (A := A.repAlloc) X W B (InitializeBobV1Env W.C.F)
        (AcceptErrEnv X W) (kitEnvs B) g r evs →
      P2OverErrEnv g r evs)
    (hOkEnv : ∀ X W B g r evs,
      P2OverPathCOkEnvOf (A := A.repAlloc) X W B (InitializeBobV1Env W.C.F)
        PromoteOverCanonSessEnv (kitEnvs B) g r evs →
      P2OverOkEnv g r evs)
    (hFitsSplit : ∀ X W B st_b g r,
      FitsEnv M lim st_b (StageP2OverEnv P2OverErrEnv P2OverOkEnv g r) →
      FitsEnv M lim st_b
        (StageP2OverEnv
          (P2OverPathCErrEnvOf (A := A.repAlloc) X W B (InitializeBobV1Env W.C.F)
            (AcceptErrEnv X W) (kitEnvs B))
          (P2OverPathCOkEnvOf (A := A.repAlloc) X W B (InitializeBobV1Env W.C.F)
            PromoteOverCanonSessEnv (kitEnvs B))
          g r))
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hSpqr : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks),
      SpqrV1PlacedSeams M A lim mmpl gh W)
    (h_accept_ok : ∀ (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement)
      (gh : CliGhostHooks) (W : CliHooks),
      subroutine_ok (lsProg_75 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 79)
        (pqxdhAcceptOptFieldsPlacedSpec
          (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) A lim AcceptSuccessEnv))
    (h_accept_err : ∀ (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement)
      (gh : CliGhostHooks) (W : CliHooks),
      subroutine_ok (lsProg_75 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 79)
        (pqxdhAcceptOptFieldsPlacedSpec
          (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) A lim (AcceptErrEnv X W)))
    (h_accept_err_owned : ∀ (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement)
      (gh : CliGhostHooks) (W : CliHooks),
      subroutine_ok (lsProg_75 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 79)
        (pqxdhAcceptErrOwnedPlacedSpec
          (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) A lim (AcceptErrEnv X W)))
    (hSelfKit : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
      (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      IdentitySelfStoreKitPlacedOkI A lim
        (cliPollIdKitPlaced A.repAlloc F0 peer (cliKitStk B))
        (cliPollSelfKitPlaced A.repAlloc F0 peer (cliKitStk B))
        (kitEnvs B F0 peer spkId kpkId opkWord kbk).selfEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hSpkKit : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
      (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      SignedPreKeyStoreKitPlacedOk A lim
        (cliPollSpkKitPlaced A.repAlloc F0 spkId (cliKitStk B))
        (kitEnvs B F0 peer spkId kpkId opkWord kbk).spkEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hKpkKit : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
      (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      KyberPreKeyStoreKitPlacedOk A lim
        (cliPollKpkKitPlaced A.repAlloc F0 kpkId spkId kbk (cliKitStk B))
        (kitEnvs B F0 peer spkId kpkId opkWord kbk).kpkEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hPkKit : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
      (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      PreKeyStoreKitPlacedOk A lim
        (cliPollPkKitPlaced A.repAlloc F0 opkWord (cliKitStk B))
        (kitEnvs B F0 peer spkId kpkId opkWord kbk).pkEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    StageP2PathCOverQpanCliPlacedStmt A lim PromoteOverEnv P2OverErrEnv P2OverOkEnv := by
  exact stageP2PathCOver_qpan_cli_placed_of_seams_aux A lim
    (selfEnvOf := fun B F0 peer spkId kpkId opkWord kbk => (kitEnvs B F0 peer spkId kpkId opkWord kbk).selfEnv)
    (spkEnvOf := fun B F0 peer spkId kpkId opkWord kbk => (kitEnvs B F0 peer spkId kpkId opkWord kbk).spkEnv)
    (kpkEnvOf := fun B F0 peer spkId kpkId opkWord kbk => (kitEnvs B F0 peer spkId kpkId opkWord kbk).kpkEnv)
    (pkEnvOf := fun B F0 peer spkId kpkId opkWord kbk => (kitEnvs B F0 peer spkId kpkId opkWord kbk).pkEnv)
    (fun X W B g r evs h => hErrEnv X W B g r evs (p2OverPathCErrEnvOf_eq_aux X W B _ _ _ ▸ h))
    (fun X W B g r evs h => hOkEnv X W B g r evs (p2OverPathCOkEnvOf_eq_aux X W B _ _ ▸ h))
    (fun X W B st_b g r hf => by
      rw [← p2OverPathCErrEnvOf_eq_aux, ← p2OverPathCOkEnvOf_eq_aux]
      exact hFitsSplit X W B st_b g r hf)
    hDropNz hSpqr h_accept_ok h_accept_err h_accept_err_owned
    hSelfKit hSpkKit hKpkKit hPkKit

/-- Lift `StageP2PathCOverQpanCliPlacedStmt` + `PromoteMatchingMissGenPlacedProp` +
`PromoteOverGenPlacedWithEnvProp` to `PollOverPathCPlacedBudgetAux.StageP2OverQpanCliPlacedStmt`,
feeding `PollOverPathCPlacedBudget.closure_pathC_placed_ok`. -/
theorem stageP2Over_qpan_cli_placed_of_pathC [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PromEnv : SessionGhost → Session (List (BitVec 8)) → List AllocEvent → Prop}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (hPathC : StageP2PathCOverQpanCliPlacedStmt A lim PromEnv P2OverErrEnv P2OverOkEnv)
    (hPromMiss : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks),
      PromoteMatchingMissGenPlacedProp A.repAlloc (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hPromOver : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      PromoteOverGenPlacedWithEnvProp M A lim PromEnv (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    StageP2OverQpanCliPlacedStmt A lim P2OverErrEnv P2OverOkEnv := by
  intro X mmpl gh W B S DecPkEnv Scope y st_b r s_old g1 s0 s1 sp rngPtr v_a8 v_b8 v_d0 Q Qpan
    hh hfits hcoins hdecOk hsub hfPeer hload hcur hnot htrust hg1
    hfs hCode1 htr01 hsp1 hsp0 hsp_sub hpc1 hrun1 halign1 hregs1 herr hok
  have hh' : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
    ⟨hh.alloc, hh.allocFs, hh.panics, hh.memcpyRO, hh.bcmp, hh.fs, hh.utf8, hh.memrchr,
      hh.codecHooks, hh.allocZeroed, hh.stringClone, hh.formatInner⟩
  have hr_scope : scopeIn r :=
    hsub r (CryptoVerification.SignalSession.Cli.RunProofs.Poll.scope_of_loadRec_some hfPeer hload)
  exact hPathC X mmpl gh W B S Scope y st_b g1 r s_old s0 s1 sp rngPtr v_a8 v_b8 v_d0 Q Qpan
    (hPromMiss mmpl gh W) (hPromOver mmpl gh W hh') hh' hfits hcoins hdecOk.toDecPkOk₀_emptyScope
    hsub hfPeer hcur hr_scope hnot htrust hg1
    hfs hCode1 htr01 hsp1 hsp0 hsp_sub hpc1 hrun1 halign1 hregs1
    (fun sf Pf hpcf hrunf hstepsf hspf hcsf hvregsf hinvf
        ⟨err, evs, hevs, hne_p, hne_s, htrf, hrej, hpostf⟩ => by
      refine herr sf Pf hpcf hrunf hstepsf hspf hcsf hvregsf hinvf
        ⟨err, evs, hevs, hne_p, hne_s, htrf, ?_, hpostf⟩
      rcases hrej with ⟨m, i, hpm, hi, _hpm_eq, hlookup | ⟨k, kp, hk, hkp, haccAll⟩⟩
      · exact CryptoVerification.SignalSession.Cli.RunProofs.Poll.decPkDefD2c_pathC_lookup_err
          X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val
          y.g.msg y.g.coins hload hcur htrust hnot hpm hlookup
      · cases hreg : StoresGhost.opened.identity.regId cliIo.rd y.g.F with
        | error u =>
          cases u
          exact CryptoVerification.SignalSession.Cli.RunProofs.Poll.decPkDefD2c_pathC_lookup_err
            X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val
            y.g.msg y.g.coins hload hcur htrust hnot hpm (Or.inr (Or.inr hreg))
        | ok reg =>
          exact CryptoVerification.SignalSession.Cli.RunProofs.Poll.decPkDefD2c_pathC_accept_none
            X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val
            y.g.msg y.g.coins hload hcur htrust hnot hpm hi hk hkp hreg (haccAll reg))
    hok

/-- Direct seam-to-`PollOverPathCPlacedBudgetAux.StageP2OverQpanCliPlacedStmt` corollary feeding
`PollOverPathCPlacedBudget.closure_pathC_placed_ok`. -/
theorem stageP2Over_qpan_cli_placed_of_seams [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {AcceptErrEnv : UnreachedPqxdhPrimitives → CliHooks → AcceptKeysInput → List AllocEvent → Prop}
    {kitEnvs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      CliPollStageP2Envs (A := A.repAlloc) B F0 peer spkId kpkId opkWord kbk}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (hErrEnv : ∀ X W B g r evs,
      P2OverPathCErrEnvOf (A := A.repAlloc) X W B (InitializeBobV1Env W.C.F)
        (AcceptErrEnv X W) (kitEnvs B) g r evs →
      P2OverErrEnv g r evs)
    (hOkEnv : ∀ X W B g r evs,
      P2OverPathCOkEnvOf (A := A.repAlloc) X W B (InitializeBobV1Env W.C.F)
        PromoteOverCanonSessEnv (kitEnvs B) g r evs →
      P2OverOkEnv g r evs)
    (hFitsSplit : ∀ X W B st_b g r,
      FitsEnv M lim st_b (StageP2OverEnv P2OverErrEnv P2OverOkEnv g r) →
      FitsEnv M lim st_b
        (StageP2OverEnv
          (P2OverPathCErrEnvOf (A := A.repAlloc) X W B (InitializeBobV1Env W.C.F)
            (AcceptErrEnv X W) (kitEnvs B))
          (P2OverPathCOkEnvOf (A := A.repAlloc) X W B (InitializeBobV1Env W.C.F)
            PromoteOverCanonSessEnv (kitEnvs B))
          g r))
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hSpqr : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks),
      SpqrV1PlacedSeams M A lim mmpl gh W)
    (hRaw : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks),
      EncodeRawPreallocPlacedOkX A.repAlloc (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hGrow : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks),
      subroutine_ok (lsProg_51 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 621)
        (withLsCl lsmpl (growOneVecU8BudgetSpec M A lim)))
    (h_accept_ok : ∀ (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement)
      (gh : CliGhostHooks) (W : CliHooks),
      subroutine_ok (lsProg_75 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 79)
        (pqxdhAcceptOptFieldsPlacedSpec
          (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) A lim AcceptSuccessEnv))
    (h_accept_err : ∀ (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement)
      (gh : CliGhostHooks) (W : CliHooks),
      subroutine_ok (lsProg_75 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 79)
        (pqxdhAcceptOptFieldsPlacedSpec
          (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) A lim (AcceptErrEnv X W)))
    (h_accept_err_owned : ∀ (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement)
      (gh : CliGhostHooks) (W : CliHooks),
      subroutine_ok (lsProg_75 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 79)
        (pqxdhAcceptErrOwnedPlacedSpec
          (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) A lim (AcceptErrEnv X W)))
    (hSelfKit : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
      (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      IdentitySelfStoreKitPlacedOkI A lim
        (cliPollIdKitPlaced A.repAlloc F0 peer (cliKitStk B))
        (cliPollSelfKitPlaced A.repAlloc F0 peer (cliKitStk B))
        (kitEnvs B F0 peer spkId kpkId opkWord kbk).selfEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hSpkKit : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
      (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      SignedPreKeyStoreKitPlacedOk A lim
        (cliPollSpkKitPlaced A.repAlloc F0 spkId (cliKitStk B))
        (kitEnvs B F0 peer spkId kpkId opkWord kbk).spkEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hKpkKit : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
      (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      KyberPreKeyStoreKitPlacedOk A lim
        (cliPollKpkKitPlaced A.repAlloc F0 kpkId spkId kbk (cliKitStk B))
        (kitEnvs B F0 peer spkId kpkId opkWord kbk).kpkEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hPkKit : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
      (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      PreKeyStoreKitPlacedOk A lim
        (cliPollPkKitPlaced A.repAlloc F0 opkWord (cliKitStk B))
        (kitEnvs B F0 peer spkId kpkId opkWord kbk).pkEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    StageP2OverQpanCliPlacedStmt A lim P2OverErrEnv P2OverOkEnv :=
  stageP2Over_qpan_cli_placed_of_pathC
    (stageP2PathCOver_qpan_cli_placed_of_seams A lim hErrEnv hOkEnv hFitsSplit hDropNz hSpqr
      h_accept_ok h_accept_err h_accept_err_owned hSelfKit hSpkKit hKpkKit hPkKit)
    (cliPromoteMatchingMissGen_placed_ok A.repAlloc)
    (fun mmpl gh W hh => cliPromoteOverGen_placed_ok mmpl gh W hh (hGrow mmpl gh W) (hRaw mmpl gh W))

/-! ## 5. Tight `ArchiveCoreEnv` Envelopes & `[LibsignalFullPlacement]` `withLsFrozen` Variants -/

/-- Tight `ArchiveCoreEnv` (`prevCap = 0#64 ∨ prevCap ≠ 0#64`) envelope for `promote_state`
(`lsmpl.base 47`) on D2(c) empty-`previous_sessions` records. -/
abbrev PromoteOverArchiveEnv := PromoteOverArchiveEnvLocal

/-- Canonical-session specialization of `PromoteOverArchiveEnv` eliminating `SessionGhost`
(`O(n)` single pre-reserved `Vec::with_capacity(n)` allocation + optional `96`-byte `grow_one`). -/
def PromoteOverArchiveCanonSessEnv (sess : Session (List (BitVec 8)))
    (evs : List AllocEvent) : Prop :=
  let n := (encSession (clearPending sess)).length
  SeqEnv FreeOnlyEvs
    (SeqEnv (fun e => e = rustAllocEvents n 1)
      (SeqEnv (fun e => e = rustAllocEvents 96 8) FreeOnlyEvs)) evs ∨
  SeqEnv FreeOnlyEvs
    (SeqEnv (fun e => e = rustAllocEvents n 1)
      (SeqEnv (fun e => e = []) FreeOnlyEvs)) evs

example (sess : Session (List (BitVec 8))) : PromoteOverArchiveCanonSessEnv sess [] :=
  Or.inl (Or.inl (by simp [FreeOnlyEvs]))

theorem archiveCoreEnv_imp_promoteOverArchiveEnv
    {prevCap : BitVec 64} {G : SessionGhost} {sess : Session (List (BitVec 8))}
    {evs : List AllocEvent}
    (h : ArchiveCoreEnv prevCap G sess evs) :
    PromoteOverArchiveEnv G sess evs := by
  by_cases hp : prevCap = 0#64
  · subst hp; exact Or.inl h
  · refine Or.inr ?_
    unfold ArchiveCoreEnv at h ⊢
    have h10 : (1#64 : BitVec 64) ≠ 0#64 := by decide
    simpa only [hp, h10, ↓reduceIte] using h

/-- Relocatable budget-threaded `PromoteOverGenPlacedWithEnvProp` at tight `PromoteOverArchiveEnv`
from `SerContractsXPlaced`, Block `51`→`621` `grow_one`, and `EncodeRawPreallocPlacedOkX`. -/
theorem promoteOverGen_archive_placed_of_contracts [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hC : SerContractsXPlaced M A lim ext)
    (hGrow : subroutine_ok (lsProg_51 ext) (lsmpl.base 621)
      (withLsCl lsmpl (growOneVecU8BudgetSpec M A lim)))
    (hRaw : EncodeRawPreallocPlacedOkX A.repAlloc ext) :
    PromoteOverGenPlacedWithEnvProp M A lim PromoteOverArchiveEnv ext := by
  have h47 :=
    LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchivePromoteBudget.promote_state_over_gen_placed_cl_of_contracts
      (callerProg := CryptoVerification.CliHandshake.RespClosurePlaced.lsProg_518 ext)
      (callerBlk := 518) hC hGrow hRaw
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre halign => ?_
  let y : CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.PromoteOverGenGhost :=
    { recPtr := x.recPtr, src := x.src, prevCap := x.prevCap, prevPtr := x.prevPtr,
      G := x.G, sess := x.sess, newBs := x.newBs }
  have hpre' : s0.mem ⊨
      (CryptoVerification.withLsCl lsmpl
        (LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveDefsBudget.promoteOverGenSpec
          M A lim)).pre (y, st) s0 ∗ R := by
    refine Satisfies.mono (sepConj_mono_left (sepConj_mono_left ?_)) hpre
    rw [LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveAuxBudget.promoteOverGenSpec_pre_eq]
    dsimp only [
      LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsBudget.p2PromoteOverGenSpecWithEnv,
      LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveDefsBudget.PromoteOverGenEnv, y]
    refine Entails.pure_left fun ⟨h0, h1, hnb, hlen', hfit⟩ => ?_
    exact Entails.pure_right
      (hfit.mono fun _evs hevs => archiveCoreEnv_imp_promoteOverArchiveEnv hevs)
      (Entails.pure_right ⟨h0, h1, hnb, hlen'⟩ (Entails.of_eq (by ac_rfl)))
  refine h47.mono_outcome (y, st) R s0 hpc hrun hpre' halign ?_
  rintro sf (⟨hret, hcs, hpost⟩ | hpan | hexit | hoom)
  · refine Or.inl ⟨hret, hcs, ?_⟩
    refine Satisfies.mono (sepConj_mono_left (sepConj_mono_right ?_)) hpost
    rw [LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveAuxBudget.promoteOverGenSpec_post_eq]
    dsimp only [
      LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsBudget.p2PromoteOverGenSpecWithEnv,
      LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveDefsBudget.PromoteOverGenEnv, y]
    refine Entails.sepExists_elim fun evs => Entails.pure_left fun hevs => ?_
    have hpool :
        A.pool lim (M.stepEvents evs st) sf ⊢
          ∃∗ evs' : List AllocEvent,
            ⌜PromoteOverArchiveEnv x.G x.sess evs'⌝ ∗ A.pool lim (M.stepEvents evs' st) sf :=
      Entails.sepExists_right evs
        (Entails.pure_right (archiveCoreEnv_imp_promoteOverArchiveEnv hevs) (Entails.refl _))
    exact sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hpool))))
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl hexit))
  · exact Or.inr (Or.inr (Or.inr hoom))

/-- Relocatable budget-threaded `PromoteOverGenPlacedWithEnvProp` at tight `PromoteOverArchiveEnv`
and `cliGhostExterns gh (cliExternsPlaced mmpl W)`. -/
theorem cliPromoteOverGen_archive_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hGrow : subroutine_ok (lsProg_51 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 621)
      (withLsCl lsmpl (growOneVecU8BudgetSpec M A lim)))
    (hRaw : EncodeRawPreallocPlacedOkX A.repAlloc (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    PromoteOverGenPlacedWithEnvProp M A lim PromoteOverArchiveEnv
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  promoteOverGen_archive_placed_of_contracts
    (SerContractsXPlaced.of_hooks
      hh.codecHooks.alloc
      hh.codecHooks.dealloc
      hh.codecHooks.realloc
      ((show withVmPreserved noAllocShimSpec = sessionShimBudgetSpec from rfl) ▸ hh.codecHooks.shim)
      (cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
        (LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget.cliExternsPlaced_sessionMemmove_budget_sat
          mmpl W CryptoVerification.LibsignalTripleRatchet.extHookStack))
      (hookSat_sessionMemcpyBudget_of_codec
        CryptoVerification.LibsignalTripleRatchet.extHookStack hh.codecHooks.memcpy))
    hGrow hRaw

/-- Memory-invariant-parameterized (`Φ : Memory → Prop`) Placed Stage P2 Path C (`Over`) CPS
contract statement at `dpPollEntryPlaced + 0x0868#64` under `RustCliAllocBudget M`. -/
def StageP2PathCOverQpanCliMemInvPlacedStmt (Φ : Memory → Prop) [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PromEnv : SessionGhost → Session (List (BitVec 8)) → List AllocEvent → Prop)
    (P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop) : Prop :=
  ∀ (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (B : RunBudgets) (S : RunSem)
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (st_b : M.σ)
    (g1 : StoresGhost)
    (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (s0 s1 : State) (sp rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (Q Qpan : State → SepProp → Prop),
    PromoteMatchingMissGenPlacedProp A.repAlloc (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
    PromoteOverGenPlacedWithEnvProp M A lim PromEnv (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
    RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
    FitsEnv M lim st_b (StageP2OverEnv P2OverErrEnv P2OverOkEnv y.g r) →
    y.g.coins.length < 2 ^ 63 →
    DecPkOk₀ ⟨W.C, W.Q⟩ (fun _ => False) y.g.F y.g.peer.val y.g.me.val y.g.msg →
    (∀ r', Scope r' → scopeIn r') →
    FilesOkPeer Scope y.g.F y.g.peer.val →
    r.currentSession = some sess →
    scopeIn r →
    ¬ CryptoVerification.SignalSession.Cli.RunProofs.DecPkS0.SessMatchesPm sess y.g.msg →
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
      StageP2PathCOverErrPlaced A lim st_b P2OverErrEnv X W B S y r s1 sf sp Pf →
      Q sf Pf) →
    (hok : ∀ (s2 : State) (evs_p2 : List AllocEvent)
      (m : PreKeyMessageFields) (i : SignalMessage)
      (k : ResponderPreKeySecrets)
      (kp : IdentityKeyPair) (reg : BitVec 32)
      (dk : SignalPqxdh.DRKey)
      (G_bob : SessionGhost)
      (prevCap' prevPtr' : BitVec 64)
      (whisperMsgPtr : BitVec 64) (whisperG : SignalMessageGhost)
      (preKeyMsgRem : SepProp),
      P2OverOkEnv y.g r evs_p2 →
      prevCap' ≠ 0#64 →
      y.g.msg = pmOfE m i →
      SignalMessage.tryFrom protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel G_bob
        (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) →
      (signalMessageAt A.repAlloc whisperG whisperMsgPtr y.g.msg.message ∗
        ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem ⊢
        preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg) →
      Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s1 s2 →
      s2.trace = s1.trace →
      s2.pc = dpPollEntryPlaced + 0x1778#64 →
      s2.status = .Running →
      s2.sp = sp →
      (s2.sp &&& 15#64 == 0#64) = true →
      s2.readReg64 .x19 = y.fut →
      s2.readReg64 .x27 = sp + 0x370#64 →
      s2.readReg64 .x29 = s0.sp - 0x60#64 →
      calleeSavedVRegs s2 = calleeSavedVRegs s0 →
      Φ s2.mem →
      SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s2
        (LsTokenInit ∗
         overGenP3Pre_placed A lim (M.stepEvents evs_p2 st_b) s2.sp (s2.readReg64 .x29) y.fut
           y.cx y.g.peerA y.g.meA whisperMsgPtr y.g.coinsP
           (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
           G_bob (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
           y.g.peer y.g.me whisperG y.g.msg.message s2 ∗
         stageP3Sub5ExtraPrePrev1 A.repAlloc s0 s2 y.fut y.out 8#64 prevCap' prevPtr'
           (encSession (clearPending sess)) 0#8 ∗
         stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
           (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
           (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
           (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
           (coroOpkIdAtP4 y.fut m.opkId)
           (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗
            ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
         stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
         ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
         ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
         preKeyMsgRem ∗
         storesAt A.repAlloc y.g.stores g1 ∗
         memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack))
        Q Qpan) →
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

/-- `LibsignalFrozen`-guarded Stage P2 Path C (`Over`) CPS contract statement at
`dpPollEntryPlaced + 0x0868#64`. -/
abbrev StageP2PathCOverQpanCliFrozenPlacedStmt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PromEnv : SessionGhost → Session (List (BitVec 8)) → List AllocEvent → Prop)
    (P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop) : Prop :=
  StageP2PathCOverQpanCliMemInvPlacedStmt (LibsignalFrozen lsmpl) A lim PromEnv P2OverErrEnv P2OverOkEnv

/-- Memory-invariant-parameterized (`Φ : Memory → Prop`) general-`Qpan` CPS Stage P2
(`+0x0868 → +0x1778`) statement for Path C (`Over`), matching
`PollOverPathCPlacedBudgetAux.StageP2OverQpanCliPlacedStmt` with `Φ s1.mem` and `Φ s2.mem`. -/
def StageP2OverQpanCliMemInvPlacedStmt (Φ : Memory → Prop) [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop) : Prop :=
  ∀ (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (S : RunSem)
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (st_b : M.σ)
    (r : SessionRecord (List (BitVec 8))) (s_old : Session (List (BitVec 8)))
    (g1 : StoresGhost)
    (s0 s1 : State) (sp rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (Q Qpan : State → SepProp → Prop),
    RunHooksPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) →
    FitsEnv M lim st_b (StageP2OverEnv P2OverErrEnv P2OverOkEnv y.g r) →
    y.g.coins.length < 2 ^ 63 →
    CryptoVerification.SignalSession.Cli.RunProofs.DecPkOkD2c ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val
      y.g.me.val y.g.msg →
    (∀ r', Scope r' → scopeIn r') →
    FilesOkPeer Scope y.g.F y.g.peer.val →
    CryptoVerification.SignalSession.Cli.Slots.loadRec Scope y.g.F y.g.peer.val = .ok (some r) →
    r.currentSession = some s_old →
    ¬ CryptoVerification.SignalSession.Cli.RunProofs.DecPkS0.SessMatchesPm s_old y.g.msg →
    StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val y.g.msg.identityKey = .ok true →
    g1 = StoresGhost.opened →
    FsAt (fun f => f = y.g.F) True (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) s1 →
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
      Steps (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) s1 sf →
      sf.sp = s0.sp →
      ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      StageP2OverErrPlaced A lim st_b P2OverErrEnv X W B S Scope y r s0 s1 sf sp Pf →
      Q sf Pf) →
    (hok : ∀ (s2 : State) (evs_p2 : List AllocEvent)
      (m : PreKeyMessageFields) (i : SignalMessage) (k : ResponderPreKeySecrets)
      (kp : IdentityKeyPair) (reg : BitVec 32)
      (dk : SignalPqxdh.DRKey) (recG : SessionGhost)
      (prevCap prevPtr whisperMsgPtr : BitVec 64) (whisperG : SignalMessageGhost)
      (preKeyMsgRem : SepProp),
      P2OverOkEnv y.g r evs_p2 →
      prevCap ≠ 0#64 →
      y.g.msg = pmOfE m i →
      SignalMessage.tryFrom protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) →
      (signalMessageAt A.repAlloc whisperG whisperMsgPtr y.g.msg.message ∗
        ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem ⊢
        preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg) →
      Steps (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) s1 s2 →
      s2.trace = s1.trace →
      s2.pc = dpPollEntryPlaced + 0x1778#64 →
      s2.status = .Running →
      s2.sp = sp →
      (s2.sp &&& 15#64 == 0#64) = true →
      s2.readReg64 .x19 = y.fut →
      s2.readReg64 .x27 = sp + 0x370#64 →
      s2.readReg64 .x29 = s0.sp - 0x60#64 →
      calleeSavedVRegs s2 = calleeSavedVRegs s0 →
      Φ s2.mem →
      SepWPp (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s2
        (LsTokenInit ∗
         overGenP3Pre_placed A lim (M.stepEvents evs_p2 st_b) s2.sp (s2.readReg64 .x29) y.fut
           y.cx y.g.peerA y.g.meA whisperMsgPtr y.g.coinsP
           (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
           recG (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
           y.g.peer y.g.me whisperG y.g.msg.message s2 ∗
         stageP3Sub5ExtraPrePrev1 A.repAlloc s0 s2 y.fut y.out 8#64 prevCap prevPtr
           (encSession (clearPending s_old)) 0#8 ∗
         stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
           (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
           (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
           (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
           (coroOpkIdAtP4 y.fut m.opkId)
           (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗
            ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
         stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
         ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
         ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
         preKeyMsgRem ∗
         storesAt A.repAlloc y.g.stores g1 ∗
         memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack))
        Q Qpan) →
    SepWPp (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s1
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

/-- `LibsignalFrozen`-guarded Stage P2 Path C (`Over`) CPS contract statement feeding
`PollOverPathCPlacedBudget`'s `LibsignalFrozen` variant. -/
abbrev StageP2OverQpanCliFrozenPlacedStmt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop) : Prop :=
  StageP2OverQpanCliMemInvPlacedStmt (LibsignalFrozen lsmpl) A lim P2OverErrEnv P2OverOkEnv

private theorem p2OverPathCOkEnvOf_eq_auxOf [LibsignalPlacement] {A : RustAlloc}
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (B : RunBudgets)
    (BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop)
    (PromSessEnv : Session (List (BitVec 8)) → List AllocEvent → Prop)
    (kitEnvs : ∀ F0 peer spkId kpkId opkWord kbk,
      CliPollStageP2Envs (A := A) B F0 peer spkId kpkId opkWord kbk) :
    P2OverPathCOkEnvOf (A := A) X W B BobV1Env PromSessEnv kitEnvs =
      P2OverPathCOkEnvAuxOf (A := A) X W B BobV1Env PromSessEnv
        (fun F0 peer spkId kpkId opkWord kbk => (kitEnvs F0 peer spkId kpkId opkWord kbk).selfEnv)
        (fun F0 peer spkId kpkId opkWord kbk => (kitEnvs F0 peer spkId kpkId opkWord kbk).spkEnv)
        (fun F0 peer spkId kpkId opkWord kbk => (kitEnvs F0 peer spkId kpkId opkWord kbk).kpkEnv)
        (fun F0 peer spkId kpkId opkWord kbk => (kitEnvs F0 peer spkId kpkId opkWord kbk).pkEnv) := by
  funext g r evs
  unfold P2OverPathCOkEnvOf P2OverPathCOkEnvAuxOf
  rfl

/-- Lift `StageP2PathCOverQpanCliMemInvPlacedStmt Φ` + `PromoteMatchingMissGenPlacedProp` +
`PromoteOverGenPlacedWithEnvProp` to `StageP2OverQpanCliMemInvPlacedStmt Φ`. -/
theorem stageP2Over_qpan_cli_memInv_placed_of_pathC {Φ : Memory → Prop} [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PromEnv : SessionGhost → Session (List (BitVec 8)) → List AllocEvent → Prop}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (hPathC : StageP2PathCOverQpanCliMemInvPlacedStmt Φ A lim PromEnv P2OverErrEnv P2OverOkEnv)
    (hPromMiss : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks),
      PromoteMatchingMissGenPlacedProp A.repAlloc (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hPromOver : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      PromoteOverGenPlacedWithEnvProp M A lim PromEnv (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    StageP2OverQpanCliMemInvPlacedStmt Φ A lim P2OverErrEnv P2OverOkEnv := by
  intro X mmpl gh W B S DecPkEnv Scope y st_b r s_old g1 s0 s1 sp rngPtr v_a8 v_b8 v_d0 Q Qpan
    hh hfits hcoins hdecOk hsub hfPeer hload hcur hnot htrust hg1
    hfs hCode1 htr01 hsp1 hsp0 hsp_sub hpc1 hrun1 halign1 hregs1 herr hok
  have hh' : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
    ⟨hh.alloc, hh.allocFs, hh.panics, hh.memcpyRO, hh.bcmp, hh.fs, hh.utf8, hh.memrchr,
      hh.codecHooks, hh.allocZeroed, hh.stringClone, hh.formatInner⟩
  have hr_scope : scopeIn r :=
    hsub r (CryptoVerification.SignalSession.Cli.RunProofs.Poll.scope_of_loadRec_some hfPeer hload)
  exact hPathC X mmpl gh W B S Scope y st_b g1 r s_old s0 s1 sp rngPtr v_a8 v_b8 v_d0 Q Qpan
    (hPromMiss mmpl gh W) (hPromOver mmpl gh W hh') hh' hfits hcoins hdecOk.toDecPkOk₀_emptyScope
    hsub hfPeer hcur hr_scope hnot htrust hg1
    hfs hCode1 htr01 hsp1 hsp0 hsp_sub hpc1 hrun1 halign1 hregs1
    (fun sf Pf hpcf hrunf hstepsf hspf hcsf hvregsf hinvf
        ⟨err, evs, hevs, hne_p, hne_s, htrf, hrej, hpostf⟩ => by
      refine herr sf Pf hpcf hrunf hstepsf hspf hcsf hvregsf hinvf
        ⟨err, evs, hevs, hne_p, hne_s, htrf, ?_, hpostf⟩
      rcases hrej with ⟨m, i, hpm, hi, _hpm_eq, hlookup | ⟨k, kp, hk, hkp, haccAll⟩⟩
      · exact CryptoVerification.SignalSession.Cli.RunProofs.Poll.decPkDefD2c_pathC_lookup_err
          X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val
          y.g.msg y.g.coins hload hcur htrust hnot hpm hlookup
      · cases hreg : StoresGhost.opened.identity.regId cliIo.rd y.g.F with
        | error u =>
          cases u
          exact CryptoVerification.SignalSession.Cli.RunProofs.Poll.decPkDefD2c_pathC_lookup_err
            X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val
            y.g.msg y.g.coins hload hcur htrust hnot hpm (Or.inr (Or.inr hreg))
        | ok reg =>
          exact CryptoVerification.SignalSession.Cli.RunProofs.Poll.decPkDefD2c_pathC_accept_none
            X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val
            y.g.msg y.g.coins hload hcur htrust hnot hpm hi hk hkp hreg (haccAll reg))
    hok

/-- `LibsignalFrozen` specialization of `stageP2Over_qpan_cli_memInv_placed_of_pathC`. -/
theorem stageP2Over_qpan_cli_full_placed_of_pathC [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PromEnv : SessionGhost → Session (List (BitVec 8)) → List AllocEvent → Prop}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (hPathC : StageP2PathCOverQpanCliFrozenPlacedStmt A lim PromEnv P2OverErrEnv P2OverOkEnv)
    (hPromMiss : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks),
      PromoteMatchingMissGenPlacedProp A.repAlloc (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hPromOver : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      PromoteOverGenPlacedWithEnvProp M A lim PromEnv (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    StageP2OverQpanCliFrozenPlacedStmt A lim P2OverErrEnv P2OverOkEnv :=
  stageP2Over_qpan_cli_memInv_placed_of_pathC hPathC hPromMiss hPromOver

/-- Closed `[LibsignalFullPlacement]` Budget-Threaded Path C Over Stage P2 V1 Instantiation
(`StageP2PathCOverQpanCliFrozenPlacedStmt`) at `PromoteOverEnv` / `PromoteOverCanonSessEnv`,
discharging Block `79` (`Pqxdh::accept`) internally via `withLsFrozen` at
`InitializeBobV1OptFieldsEnv` / `AcceptOptFieldsEnv` with zero `h_accept*` seams. -/
theorem stageP2PathCOver_qpan_cli_full_placed_of_seams [LibsignalFullPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {kitEnvs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      CliPollStageP2Envs (A := A.repAlloc) B F0 peer spkId kpkId opkWord kbk}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (hErrEnv : ∀ X W B g r evs,
      P2OverPathCErrEnvOf (A := A.repAlloc) X W B
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
        (kitEnvs B) g r evs →
      P2OverErrEnv g r evs)
    (hOkEnv : ∀ X W B g r evs,
      P2OverPathCOkEnvOf (A := A.repAlloc) X W B
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        PromoteOverCanonSessEnv (kitEnvs B) g r evs →
      P2OverOkEnv g r evs)
    (hFitsSplit : ∀ X W B st_b g r,
      FitsEnv M lim st_b (StageP2OverEnv P2OverErrEnv P2OverOkEnv g r) →
      FitsEnv M lim st_b
        (StageP2OverEnv
          (P2OverPathCErrEnvOf (A := A.repAlloc) X W B
            (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
            (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
            (kitEnvs B))
          (P2OverPathCOkEnvOf (A := A.repAlloc) X W B
            (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
            PromoteOverCanonSessEnv (kitEnvs B))
          g r))
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : ∀ (gh : CliGhostHooks), CliGhostAllocHooks M A lim gh)
    (hSpqr : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks),
      SpqrV1PlacedSeams M A lim mmpl gh W)
    (hSelfKit : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
      (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      IdentitySelfStoreKitPlacedOkI A lim
        (cliPollIdKitPlaced A.repAlloc F0 peer (cliKitStk B))
        (cliPollSelfKitPlaced A.repAlloc F0 peer (cliKitStk B))
        (kitEnvs B F0 peer spkId kpkId opkWord kbk).selfEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hSpkKit : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
      (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      SignedPreKeyStoreKitPlacedOk A lim
        (cliPollSpkKitPlaced A.repAlloc F0 spkId (cliKitStk B))
        (kitEnvs B F0 peer spkId kpkId opkWord kbk).spkEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hKpkKit : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
      (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      KyberPreKeyStoreKitPlacedOk A lim
        (cliPollKpkKitPlaced A.repAlloc F0 kpkId spkId kbk (cliKitStk B))
        (kitEnvs B F0 peer spkId kpkId opkWord kbk).kpkEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hPkKit : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
      (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      PreKeyStoreKitPlacedOk A lim
        (cliPollPkKitPlaced A.repAlloc F0 opkWord (cliKitStk B))
        (kitEnvs B F0 peer spkId kpkId opkWord kbk).pkEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    StageP2PathCOverQpanCliFrozenPlacedStmt A lim PromoteOverEnv P2OverErrEnv P2OverOkEnv := by
  exact stageP2PathCOver_qpan_cli_full_placed_of_seams_aux A lim
    (PromEnv := PromoteOverEnv) (PromSessEnv := PromoteOverCanonSessEnvLocal)
    promoteOverEnv_eq_canon_pub
    (selfEnvOf := fun B F0 peer spkId kpkId opkWord kbk => (kitEnvs B F0 peer spkId kpkId opkWord kbk).selfEnv)
    (spkEnvOf := fun B F0 peer spkId kpkId opkWord kbk => (kitEnvs B F0 peer spkId kpkId opkWord kbk).spkEnv)
    (kpkEnvOf := fun B F0 peer spkId kpkId opkWord kbk => (kitEnvs B F0 peer spkId kpkId opkWord kbk).kpkEnv)
    (pkEnvOf := fun B F0 peer spkId kpkId opkWord kbk => (kitEnvs B F0 peer spkId kpkId opkWord kbk).pkEnv)
    (fun X W B g r evs h => hErrEnv X W B g r evs (p2OverPathCErrEnvOf_eq_aux X W B _ _ _ ▸ h))
    (fun X W B g r evs h => hOkEnv X W B g r evs (by
      have heq : PromoteOverCanonSessEnv = PromoteOverCanonSessEnvLocal := rfl
      rw [heq]; exact p2OverPathCOkEnvOf_eq_auxOf X W B _ _ _ ▸ h))
    (fun X W B st_b g r hf => by
      have heq : PromoteOverCanonSessEnv = PromoteOverCanonSessEnvLocal := rfl
      rw [← p2OverPathCErrEnvOf_eq_aux, ← p2OverPathCOkEnvOf_eq_auxOf, ← heq]
      exact hFitsSplit X W B st_b g r hf)
    hDropNz hG hSpqr hSelfKit hSpkKit hKpkKit hPkKit

/-- Tight-`ArchiveCoreEnv` `[LibsignalFullPlacement]` Path C Over Stage P2 V1 Instantiation
(`StageP2PathCOverQpanCliFrozenPlacedStmt`) at `PromoteOverArchiveEnv` /
`PromoteOverArchiveCanonSessEnv`, discharging Block `79` (`Pqxdh::accept`) internally via
`withLsFrozen` with zero `h_accept*` seams. -/
theorem stageP2PathCOver_qpan_cli_archive_full_placed_of_seams [LibsignalFullPlacement]
    {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {kitEnvs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      CliPollStageP2Envs (A := A.repAlloc) B F0 peer spkId kpkId opkWord kbk}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (hErrEnv : ∀ X W B g r evs,
      P2OverPathCErrEnvOf (A := A.repAlloc) X W B
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
        (kitEnvs B) g r evs →
      P2OverErrEnv g r evs)
    (hOkEnv : ∀ X W B g r evs,
      P2OverPathCOkEnvOf (A := A.repAlloc) X W B
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        PromoteOverArchiveCanonSessEnv (kitEnvs B) g r evs →
      P2OverOkEnv g r evs)
    (hFitsSplit : ∀ X W B st_b g r,
      FitsEnv M lim st_b (StageP2OverEnv P2OverErrEnv P2OverOkEnv g r) →
      FitsEnv M lim st_b
        (StageP2OverEnv
          (P2OverPathCErrEnvOf (A := A.repAlloc) X W B
            (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
            (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
            (kitEnvs B))
          (P2OverPathCOkEnvOf (A := A.repAlloc) X W B
            (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
            PromoteOverArchiveCanonSessEnv (kitEnvs B))
          g r))
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : ∀ (gh : CliGhostHooks), CliGhostAllocHooks M A lim gh)
    (hSpqr : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks),
      SpqrV1PlacedSeams M A lim mmpl gh W)
    (hSelfKit : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
      (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      IdentitySelfStoreKitPlacedOkI A lim
        (cliPollIdKitPlaced A.repAlloc F0 peer (cliKitStk B))
        (cliPollSelfKitPlaced A.repAlloc F0 peer (cliKitStk B))
        (kitEnvs B F0 peer spkId kpkId opkWord kbk).selfEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hSpkKit : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
      (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      SignedPreKeyStoreKitPlacedOk A lim
        (cliPollSpkKitPlaced A.repAlloc F0 spkId (cliKitStk B))
        (kitEnvs B F0 peer spkId kpkId opkWord kbk).spkEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hKpkKit : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
      (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      KyberPreKeyStoreKitPlacedOk A lim
        (cliPollKpkKitPlaced A.repAlloc F0 kpkId spkId kbk (cliKitStk B))
        (kitEnvs B F0 peer spkId kpkId opkWord kbk).kpkEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hPkKit : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
      (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      PreKeyStoreKitPlacedOk A lim
        (cliPollPkKitPlaced A.repAlloc F0 opkWord (cliKitStk B))
        (kitEnvs B F0 peer spkId kpkId opkWord kbk).pkEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    StageP2PathCOverQpanCliFrozenPlacedStmt A lim PromoteOverArchiveEnv
      P2OverErrEnv P2OverOkEnv := by
  exact stageP2PathCOver_qpan_cli_full_placed_of_seams_aux A lim
    (PromEnv := PromoteOverArchiveEnv) (PromSessEnv := PromoteOverArchiveCanonSessEnvLocal)
    promoteOverArchiveEnv_eq_canon
    (selfEnvOf := fun B F0 peer spkId kpkId opkWord kbk => (kitEnvs B F0 peer spkId kpkId opkWord kbk).selfEnv)
    (spkEnvOf := fun B F0 peer spkId kpkId opkWord kbk => (kitEnvs B F0 peer spkId kpkId opkWord kbk).spkEnv)
    (kpkEnvOf := fun B F0 peer spkId kpkId opkWord kbk => (kitEnvs B F0 peer spkId kpkId opkWord kbk).kpkEnv)
    (pkEnvOf := fun B F0 peer spkId kpkId opkWord kbk => (kitEnvs B F0 peer spkId kpkId opkWord kbk).pkEnv)
    (fun X W B g r evs h => hErrEnv X W B g r evs (p2OverPathCErrEnvOf_eq_aux X W B _ _ _ ▸ h))
    (fun X W B g r evs h => hOkEnv X W B g r evs (by
      have heq : PromoteOverArchiveCanonSessEnv = PromoteOverArchiveCanonSessEnvLocal := rfl
      rw [heq]; exact p2OverPathCOkEnvOf_eq_auxOf X W B _ _ _ ▸ h))
    (fun X W B st_b g r hf => by
      have heq : PromoteOverArchiveCanonSessEnv = PromoteOverArchiveCanonSessEnvLocal := rfl
      rw [← p2OverPathCErrEnvOf_eq_aux, ← p2OverPathCOkEnvOf_eq_auxOf, ← heq]
      exact hFitsSplit X W B st_b g r hf)
    hDropNz hG hSpqr hSelfKit hSpkKit hKpkKit hPkKit

/-- Direct seam-to-`StageP2OverQpanCliFrozenPlacedStmt` corollary at `PromoteOverCanonSessEnv`
with zero `h_accept*` seams. -/
theorem stageP2Over_qpan_cli_full_placed_of_seams [LibsignalFullPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {kitEnvs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      CliPollStageP2Envs (A := A.repAlloc) B F0 peer spkId kpkId opkWord kbk}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (hErrEnv : ∀ X W B g r evs,
      P2OverPathCErrEnvOf (A := A.repAlloc) X W B
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
        (kitEnvs B) g r evs →
      P2OverErrEnv g r evs)
    (hOkEnv : ∀ X W B g r evs,
      P2OverPathCOkEnvOf (A := A.repAlloc) X W B
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        PromoteOverCanonSessEnv (kitEnvs B) g r evs →
      P2OverOkEnv g r evs)
    (hFitsSplit : ∀ X W B st_b g r,
      FitsEnv M lim st_b (StageP2OverEnv P2OverErrEnv P2OverOkEnv g r) →
      FitsEnv M lim st_b
        (StageP2OverEnv
          (P2OverPathCErrEnvOf (A := A.repAlloc) X W B
            (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
            (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
            (kitEnvs B))
          (P2OverPathCOkEnvOf (A := A.repAlloc) X W B
            (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
            PromoteOverCanonSessEnv (kitEnvs B))
          g r))
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : ∀ (gh : CliGhostHooks), CliGhostAllocHooks M A lim gh)
    (hSpqr : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks),
      SpqrV1PlacedSeams M A lim mmpl gh W)
    (hRaw : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks),
      EncodeRawPreallocPlacedOkX A.repAlloc (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hGrow : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks),
      subroutine_ok (lsProg_51 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 621)
        (withLsCl lsmpl (growOneVecU8BudgetSpec M A lim)))
    (hSelfKit : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
      (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      IdentitySelfStoreKitPlacedOkI A lim
        (cliPollIdKitPlaced A.repAlloc F0 peer (cliKitStk B))
        (cliPollSelfKitPlaced A.repAlloc F0 peer (cliKitStk B))
        (kitEnvs B F0 peer spkId kpkId opkWord kbk).selfEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hSpkKit : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
      (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      SignedPreKeyStoreKitPlacedOk A lim
        (cliPollSpkKitPlaced A.repAlloc F0 spkId (cliKitStk B))
        (kitEnvs B F0 peer spkId kpkId opkWord kbk).spkEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hKpkKit : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
      (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      KyberPreKeyStoreKitPlacedOk A lim
        (cliPollKpkKitPlaced A.repAlloc F0 kpkId spkId kbk (cliKitStk B))
        (kitEnvs B F0 peer spkId kpkId opkWord kbk).kpkEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hPkKit : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
      (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      PreKeyStoreKitPlacedOk A lim
        (cliPollPkKitPlaced A.repAlloc F0 opkWord (cliKitStk B))
        (kitEnvs B F0 peer spkId kpkId opkWord kbk).pkEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    StageP2OverQpanCliFrozenPlacedStmt A lim P2OverErrEnv P2OverOkEnv :=
  stageP2Over_qpan_cli_full_placed_of_pathC
    (stageP2PathCOver_qpan_cli_full_placed_of_seams A lim hErrEnv hOkEnv hFitsSplit hDropNz hG hSpqr
      hSelfKit hSpkKit hKpkKit hPkKit)
    (cliPromoteMatchingMissGen_placed_ok A.repAlloc)
    (fun mmpl gh W hh => cliPromoteOverGen_placed_ok mmpl gh W hh (hGrow mmpl gh W) (hRaw mmpl gh W))

/-- Direct seam-to-`StageP2OverQpanCliFrozenPlacedStmt` corollary at tight
`PromoteOverArchiveCanonSessEnv` (`ArchiveCoreEnv`) with zero `h_accept*` seams. -/
theorem stageP2Over_qpan_cli_archive_full_placed_of_seams [LibsignalFullPlacement]
    {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {kitEnvs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      CliPollStageP2Envs (A := A.repAlloc) B F0 peer spkId kpkId opkWord kbk}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (hErrEnv : ∀ X W B g r evs,
      P2OverPathCErrEnvOf (A := A.repAlloc) X W B
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
        (kitEnvs B) g r evs →
      P2OverErrEnv g r evs)
    (hOkEnv : ∀ X W B g r evs,
      P2OverPathCOkEnvOf (A := A.repAlloc) X W B
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        PromoteOverArchiveCanonSessEnv (kitEnvs B) g r evs →
      P2OverOkEnv g r evs)
    (hFitsSplit : ∀ X W B st_b g r,
      FitsEnv M lim st_b (StageP2OverEnv P2OverErrEnv P2OverOkEnv g r) →
      FitsEnv M lim st_b
        (StageP2OverEnv
          (P2OverPathCErrEnvOf (A := A.repAlloc) X W B
            (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
            (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
            (kitEnvs B))
          (P2OverPathCOkEnvOf (A := A.repAlloc) X W B
            (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
            PromoteOverArchiveCanonSessEnv (kitEnvs B))
          g r))
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : ∀ (gh : CliGhostHooks), CliGhostAllocHooks M A lim gh)
    (hSpqr : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks),
      SpqrV1PlacedSeams M A lim mmpl gh W)
    (hRaw : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks),
      EncodeRawPreallocPlacedOkX A.repAlloc (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hGrow : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks),
      subroutine_ok (lsProg_51 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 621)
        (withLsCl lsmpl (growOneVecU8BudgetSpec M A lim)))
    (hSelfKit : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
      (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      IdentitySelfStoreKitPlacedOkI A lim
        (cliPollIdKitPlaced A.repAlloc F0 peer (cliKitStk B))
        (cliPollSelfKitPlaced A.repAlloc F0 peer (cliKitStk B))
        (kitEnvs B F0 peer spkId kpkId opkWord kbk).selfEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hSpkKit : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
      (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      SignedPreKeyStoreKitPlacedOk A lim
        (cliPollSpkKitPlaced A.repAlloc F0 spkId (cliKitStk B))
        (kitEnvs B F0 peer spkId kpkId opkWord kbk).spkEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hKpkKit : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
      (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      KyberPreKeyStoreKitPlacedOk A lim
        (cliPollKpkKitPlaced A.repAlloc F0 kpkId spkId kbk (cliKitStk B))
        (kitEnvs B F0 peer spkId kpkId opkWord kbk).kpkEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hPkKit : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
      (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      PreKeyStoreKitPlacedOk A lim
        (cliPollPkKitPlaced A.repAlloc F0 opkWord (cliKitStk B))
        (kitEnvs B F0 peer spkId kpkId opkWord kbk).pkEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    StageP2OverQpanCliFrozenPlacedStmt A lim P2OverErrEnv P2OverOkEnv :=
  stageP2Over_qpan_cli_full_placed_of_pathC
    (stageP2PathCOver_qpan_cli_archive_full_placed_of_seams A lim hErrEnv hOkEnv hFitsSplit
      hDropNz hG hSpqr hSelfKit hSpkKit hKpkKit hPkKit)
    (cliPromoteMatchingMissGen_placed_ok A.repAlloc)
    (fun mmpl gh W hh =>
      cliPromoteOverGen_archive_placed_ok mmpl gh W hh (hGrow mmpl gh W) (hRaw mmpl gh W))

/-! ## 6. Pointwise `*At` Companions at Fixed `(mmpl, gh, W)` -/

/-- Pointwise per-`(X, mmpl, g, W)` general-`Qpan` CPS Stage P2 (`+0x0868 → +0x1778`) body
parameterized by memory invariant `Φ : Memory → Prop`, matching the exact body of
`PollOverPathCPlacedBudgetAux.StageP2OverQpanCliPlacedStmt` /
`PollOverPathCPlacedBudgetAux.StageP2OverQpanCliFrozenPlacedStmt` (`SkeletonPlacedBudget.RunHooksPlaced`)
by `rfl`. -/
abbrev StageP2OverQpanCliMemInvPlacedAtXStmt (Φ : Memory → Prop) [LibsignalPlacement]
    {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop) : Prop :=
  ∀ (B : RunBudgets) (S : RunSem)
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (st_b : M.σ)
    (r : SessionRecord (List (BitVec 8))) (s_old : Session (List (BitVec 8)))
    (g1 : StoresGhost)
    (s0 s1 : State) (sp rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (Q Qpan : State → SepProp → Prop),
    LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) →
    FitsEnv M lim st_b (StageP2OverEnv P2OverErrEnv P2OverOkEnv y.g r) →
    y.g.coins.length < 2 ^ 63 →
    CryptoVerification.SignalSession.Cli.RunProofs.DecPkOkD2c ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val
      y.g.me.val y.g.msg →
    (∀ r', Scope r' → scopeIn r') →
    FilesOkPeer Scope y.g.F y.g.peer.val →
    CryptoVerification.SignalSession.Cli.Slots.loadRec Scope y.g.F y.g.peer.val = .ok (some r) →
    r.currentSession = some s_old →
    ¬ CryptoVerification.SignalSession.Cli.RunProofs.DecPkS0.SessMatchesPm s_old y.g.msg →
    StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val y.g.msg.identityKey = .ok true →
    g1 = StoresGhost.opened →
    FsAt (fun f => f = y.g.F) True (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) s1 →
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
      Steps (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) s1 sf →
      sf.sp = s0.sp →
      ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      StageP2OverErrPlaced A lim st_b P2OverErrEnv X W B S Scope y r s0 s1 sf sp Pf →
      Q sf Pf) →
    (hok : ∀ (s2 : State) (evs_p2 : List AllocEvent)
      (m : PreKeyMessageFields) (i : SignalMessage) (k : ResponderPreKeySecrets)
      (kp : IdentityKeyPair) (reg : BitVec 32)
      (dk : SignalPqxdh.DRKey) (recG : SessionGhost)
      (prevCap prevPtr whisperMsgPtr : BitVec 64) (whisperG : SignalMessageGhost)
      (preKeyMsgRem : SepProp),
      P2OverOkEnv y.g r evs_p2 →
      prevCap ≠ 0#64 →
      y.g.msg = pmOfE m i →
      SignalMessage.tryFrom protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) →
      (signalMessageAt A.repAlloc whisperG whisperMsgPtr y.g.msg.message ∗
        ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem ⊢
        preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg) →
      Steps (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) s1 s2 →
      s2.trace = s1.trace →
      s2.pc = dpPollEntryPlaced + 0x1778#64 →
      s2.status = .Running →
      s2.sp = sp →
      (s2.sp &&& 15#64 == 0#64) = true →
      s2.readReg64 .x19 = y.fut →
      s2.readReg64 .x27 = sp + 0x370#64 →
      s2.readReg64 .x29 = s0.sp - 0x60#64 →
      calleeSavedVRegs s2 = calleeSavedVRegs s0 →
      Φ s2.mem →
      SepWPp (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s2
        (LsTokenInit ∗
         overGenP3Pre_placed A lim (M.stepEvents evs_p2 st_b) s2.sp (s2.readReg64 .x29) y.fut
           y.cx y.g.peerA y.g.meA whisperMsgPtr y.g.coinsP
           (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
           recG (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
           y.g.peer y.g.me whisperG y.g.msg.message s2 ∗
         stageP3Sub5ExtraPrePrev1 A.repAlloc s0 s2 y.fut y.out 8#64 prevCap prevPtr
           (encSession (clearPending s_old)) 0#8 ∗
         stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
           (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
           (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
           (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
           (coroOpkIdAtP4 y.fut m.opkId)
           (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗
            ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
         stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
         ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
         ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
         preKeyMsgRem ∗
         storesAt A.repAlloc y.g.stores g1 ∗
         memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack))
        Q Qpan) →
    SepWPp (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s1
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

private example [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop) :
    StageP2OverQpanCliPlacedStmt A lim P2OverErrEnv P2OverOkEnv =
      (∀ (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
        (W : CliHooks),
        StageP2OverQpanCliMemInvPlacedAtXStmt (LibsignalCodeRoLoaded lsmpl) A lim X mmpl g W
          P2OverErrEnv P2OverOkEnv) := rfl

/-- Pointwise per-`(mmpl, g, W)` general-`Qpan` CPS Stage P2 (`+0x0868 → +0x1778`) statement
parameterized by `Φ : Memory → Prop`, keeping `∀ (X : UnreachedPqxdhPrimitives) (B : RunBudgets)
(S : RunSem) …` inside. -/
abbrev StageP2OverQpanCliMemInvPlacedAtStmt (Φ : Memory → Prop) [LibsignalPlacement]
    {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop) : Prop :=
  ∀ (X : UnreachedPqxdhPrimitives),
    StageP2OverQpanCliMemInvPlacedAtXStmt Φ A lim X mmpl g W P2OverErrEnv P2OverOkEnv

/-- `LibsignalFrozen`-guarded pointwise per-`(mmpl, g, W)` Stage P2 Path C (`Over`) CPS contract
statement (`rfl`-identical to the pointwise body of
`PollOverPathCPlacedBudgetAux.StageP2OverQpanCliFrozenPlacedStmt` at `(mmpl, g, W)`). -/
abbrev StageP2OverQpanCliFrozenPlacedAtStmt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop) : Prop :=
  StageP2OverQpanCliMemInvPlacedAtStmt (LibsignalFrozen lsmpl) A lim mmpl g W
    P2OverErrEnv P2OverOkEnv

/-- Pointwise lift of `StageP2PathCOverQpanCliMemInvPlacedAtStmt Φ` + `PromoteMatchingMissGenPlacedProp`
+ `PromoteOverGenPlacedWithEnvProp` at fixed `(X, mmpl, gh, W, B)` to
`StageP2OverQpanCliMemInvPlacedAtXStmt Φ`. -/
theorem stageP2Over_qpan_cli_memInv_placed_at_of_pathC {Φ : Memory → Prop} [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PromEnv : SessionGhost → Session (List (BitVec 8)) → List AllocEvent → Prop}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {X : UnreachedPqxdhPrimitives} {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    (hPathC : ∀ B : RunBudgets,
      StageP2PathCOverQpanCliMemInvPlacedAtStmt Φ A lim PromEnv X mmpl gh W B
        P2OverErrEnv P2OverOkEnv)
    (hPromMiss : PromoteMatchingMissGenPlacedProp A.repAlloc
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hPromOver :
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      PromoteOverGenPlacedWithEnvProp M A lim PromEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    StageP2OverQpanCliMemInvPlacedAtXStmt Φ A lim X mmpl gh W P2OverErrEnv P2OverOkEnv := by
  intro B S DecPkEnv Scope y st_b r s_old g1 s0 s1 sp rngPtr v_a8 v_b8 v_d0 Q Qpan
    hh hfits hcoins hdecOk hsub hfPeer hload hcur hnot htrust hg1
    hfs hCode1 htr01 hsp1 hsp0 hsp_sub hpc1 hrun1 halign1 hregs1 herr hok
  have hh' : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
    ⟨hh.alloc, hh.allocFs, hh.panics, hh.memcpyRO, hh.bcmp, hh.fs, hh.utf8, hh.memrchr,
      hh.codecHooks, hh.allocZeroed, hh.stringClone, hh.formatInner⟩
  have hr_scope : scopeIn r :=
    hsub r (CryptoVerification.SignalSession.Cli.RunProofs.Poll.scope_of_loadRec_some hfPeer hload)
  exact hPathC B S Scope y st_b g1 r s_old s0 s1 sp rngPtr v_a8 v_b8 v_d0 Q Qpan
    hPromMiss (hPromOver hh') hh' hfits hcoins hdecOk.toDecPkOk₀_emptyScope
    hsub hfPeer hcur hr_scope hnot htrust hg1
    hfs hCode1 htr01 hsp1 hsp0 hsp_sub hpc1 hrun1 halign1 hregs1
    (fun sf Pf hpcf hrunf hstepsf hspf hcsf hvregsf hinvf
        ⟨err, evs, hevs, hne_p, hne_s, htrf, hrej, hpostf⟩ => by
      refine herr sf Pf hpcf hrunf hstepsf hspf hcsf hvregsf hinvf
        ⟨err, evs, hevs, hne_p, hne_s, htrf, ?_, hpostf⟩
      rcases hrej with ⟨m, i, hpm, hi, _hpm_eq, hlookup | ⟨k, kp, hk, hkp, haccAll⟩⟩
      · exact CryptoVerification.SignalSession.Cli.RunProofs.Poll.decPkDefD2c_pathC_lookup_err
          X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val
          y.g.msg y.g.coins hload hcur htrust hnot hpm hlookup
      · cases hreg : StoresGhost.opened.identity.regId cliIo.rd y.g.F with
        | error u =>
          cases u
          exact CryptoVerification.SignalSession.Cli.RunProofs.Poll.decPkDefD2c_pathC_lookup_err
            X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val
            y.g.msg y.g.coins hload hcur htrust hnot hpm (Or.inr (Or.inr hreg))
        | ok reg =>
          exact CryptoVerification.SignalSession.Cli.RunProofs.Poll.decPkDefD2c_pathC_accept_none
            X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val
            y.g.msg y.g.coins hload hcur htrust hnot hpm hi hk hkp hreg (haccAll reg))
    hok

/-- `LibsignalFrozen` specialization of `stageP2Over_qpan_cli_memInv_placed_at_of_pathC`. -/
theorem stageP2Over_qpan_cli_full_placed_at_of_pathC [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PromEnv : SessionGhost → Session (List (BitVec 8)) → List AllocEvent → Prop}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {X : UnreachedPqxdhPrimitives} {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    (hPathC : ∀ B : RunBudgets,
      StageP2PathCOverQpanCliFrozenPlacedAtStmt A lim PromEnv X mmpl gh W B
        P2OverErrEnv P2OverOkEnv)
    (hPromMiss : PromoteMatchingMissGenPlacedProp A.repAlloc
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hPromOver :
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      PromoteOverGenPlacedWithEnvProp M A lim PromEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    StageP2OverQpanCliMemInvPlacedAtXStmt (LibsignalFrozen lsmpl) A lim X mmpl gh W
      P2OverErrEnv P2OverOkEnv :=
  stageP2Over_qpan_cli_memInv_placed_at_of_pathC hPathC hPromMiss hPromOver

/-- Pointwise per-`(X, mmpl, gh, W, B)` `[LibsignalFullPlacement]` Path C Over Stage P2 V1
instantiation at `PromoteOverEnv` / `PromoteOverCanonSessEnv` with zero `h_accept*` seams and zero
universal-`mmpl` premises. -/
theorem stageP2PathCOver_qpan_cli_full_placed_at_of_seams [LibsignalFullPlacement]
    {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (B : RunBudgets)
    {kitEnvs : ∀ (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      CliPollStageP2Envs (A := A.repAlloc) B F0 peer spkId kpkId opkWord kbk}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (hErrEnv : ∀ g r evs,
      P2OverPathCErrEnvOf (A := A.repAlloc) X W B
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
        kitEnvs g r evs →
      P2OverErrEnv g r evs)
    (hOkEnv : ∀ g r evs,
      P2OverPathCOkEnvOf (A := A.repAlloc) X W B
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        PromoteOverCanonSessEnv kitEnvs g r evs →
      P2OverOkEnv g r evs)
    (hFitsSplit : ∀ st_b g r,
      FitsEnv M lim st_b (StageP2OverEnv P2OverErrEnv P2OverOkEnv g r) →
      FitsEnv M lim st_b
        (StageP2OverEnv
          (P2OverPathCErrEnvOf (A := A.repAlloc) X W B
            (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
            (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
            kitEnvs)
          (P2OverPathCOkEnvOf (A := A.repAlloc) X W B
            (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
            PromoteOverCanonSessEnv kitEnvs)
          g r))
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hSpqr : SpqrV1PlacedSeams M A lim mmpl gh W)
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
    StageP2PathCOverQpanCliFrozenPlacedAtStmt A lim PromoteOverEnv X mmpl gh W B
      P2OverErrEnv P2OverOkEnv :=
  stageP2PathCOver_qpan_cli_full_placed_at_of_seams_aux A lim
    (PromEnv := PromoteOverEnv) (PromSessEnv := PromoteOverCanonSessEnvLocal)
    promoteOverEnv_eq_canon_pub X mmpl gh W B
    (selfEnvOf := fun F0 peer spkId kpkId opkWord kbk => (kitEnvs F0 peer spkId kpkId opkWord kbk).selfEnv)
    (spkEnvOf := fun F0 peer spkId kpkId opkWord kbk => (kitEnvs F0 peer spkId kpkId opkWord kbk).spkEnv)
    (kpkEnvOf := fun F0 peer spkId kpkId opkWord kbk => (kitEnvs F0 peer spkId kpkId opkWord kbk).kpkEnv)
    (pkEnvOf := fun F0 peer spkId kpkId opkWord kbk => (kitEnvs F0 peer spkId kpkId opkWord kbk).pkEnv)
    (fun g r evs h => hErrEnv g r evs (p2OverPathCErrEnvOf_eq_aux X W B _ _ _ ▸ h))
    (fun g r evs h => hOkEnv g r evs (by
      have heq : PromoteOverCanonSessEnv = PromoteOverCanonSessEnvLocal := rfl
      rw [heq]; exact p2OverPathCOkEnvOf_eq_auxOf X W B _ _ _ ▸ h))
    (fun st_b g r hf => by
      have heq : PromoteOverCanonSessEnv = PromoteOverCanonSessEnvLocal := rfl
      rw [← p2OverPathCErrEnvOf_eq_aux, ← p2OverPathCOkEnvOf_eq_auxOf, ← heq]
      exact hFitsSplit st_b g r hf)
    hDropNz hG hSpqr hSelfKit hSpkKit hKpkKit hPkKit

/-- Pointwise per-`(X, mmpl, gh, W, B)` tight-`ArchiveCoreEnv` `[LibsignalFullPlacement]` Path C
Over Stage P2 V1 instantiation at `PromoteOverArchiveEnv` / `PromoteOverArchiveCanonSessEnv` with
zero `h_accept*` seams and zero universal-`mmpl` premises. -/
theorem stageP2PathCOver_qpan_cli_archive_full_placed_at_of_seams [LibsignalFullPlacement]
    {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (B : RunBudgets)
    {kitEnvs : ∀ (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      CliPollStageP2Envs (A := A.repAlloc) B F0 peer spkId kpkId opkWord kbk}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (hErrEnv : ∀ g r evs,
      P2OverPathCErrEnvOf (A := A.repAlloc) X W B
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
        kitEnvs g r evs →
      P2OverErrEnv g r evs)
    (hOkEnv : ∀ g r evs,
      P2OverPathCOkEnvOf (A := A.repAlloc) X W B
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        PromoteOverArchiveCanonSessEnv kitEnvs g r evs →
      P2OverOkEnv g r evs)
    (hFitsSplit : ∀ st_b g r,
      FitsEnv M lim st_b (StageP2OverEnv P2OverErrEnv P2OverOkEnv g r) →
      FitsEnv M lim st_b
        (StageP2OverEnv
          (P2OverPathCErrEnvOf (A := A.repAlloc) X W B
            (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
            (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
            kitEnvs)
          (P2OverPathCOkEnvOf (A := A.repAlloc) X W B
            (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
            PromoteOverArchiveCanonSessEnv kitEnvs)
          g r))
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hSpqr : SpqrV1PlacedSeams M A lim mmpl gh W)
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
    StageP2PathCOverQpanCliFrozenPlacedAtStmt A lim PromoteOverArchiveEnv X mmpl gh W B
      P2OverErrEnv P2OverOkEnv :=
  stageP2PathCOver_qpan_cli_full_placed_at_of_seams_aux A lim
    (PromEnv := PromoteOverArchiveEnv) (PromSessEnv := PromoteOverArchiveCanonSessEnvLocal)
    promoteOverArchiveEnv_eq_canon X mmpl gh W B
    (selfEnvOf := fun F0 peer spkId kpkId opkWord kbk => (kitEnvs F0 peer spkId kpkId opkWord kbk).selfEnv)
    (spkEnvOf := fun F0 peer spkId kpkId opkWord kbk => (kitEnvs F0 peer spkId kpkId opkWord kbk).spkEnv)
    (kpkEnvOf := fun F0 peer spkId kpkId opkWord kbk => (kitEnvs F0 peer spkId kpkId opkWord kbk).kpkEnv)
    (pkEnvOf := fun F0 peer spkId kpkId opkWord kbk => (kitEnvs F0 peer spkId kpkId opkWord kbk).pkEnv)
    (fun g r evs h => hErrEnv g r evs (p2OverPathCErrEnvOf_eq_aux X W B _ _ _ ▸ h))
    (fun g r evs h => hOkEnv g r evs (by
      have heq : PromoteOverArchiveCanonSessEnv = PromoteOverArchiveCanonSessEnvLocal := rfl
      rw [heq]; exact p2OverPathCOkEnvOf_eq_auxOf X W B _ _ _ ▸ h))
    (fun st_b g r hf => by
      have heq : PromoteOverArchiveCanonSessEnv = PromoteOverArchiveCanonSessEnvLocal := rfl
      rw [← p2OverPathCErrEnvOf_eq_aux, ← p2OverPathCOkEnvOf_eq_auxOf, ← heq]
      exact hFitsSplit st_b g r hf)
    hDropNz hG hSpqr hSelfKit hSpkKit hKpkKit hPkKit

/-- Pointwise per-`(mmpl, gh, W)` seam-to-`StageP2OverQpanCliFrozenPlacedAtStmt` corollary at
`PromoteOverCanonSessEnv`, with zero `h_accept*` seams and zero universal-`mmpl`
premises. -/
theorem stageP2Over_qpan_cli_full_placed_at_of_seams [LibsignalFullPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {kitEnvs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      CliPollStageP2Envs (A := A.repAlloc) B F0 peer spkId kpkId opkWord kbk}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (hErrEnv : ∀ X B g r evs,
      P2OverPathCErrEnvOf (A := A.repAlloc) X W B
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
        (kitEnvs B) g r evs →
      P2OverErrEnv g r evs)
    (hOkEnv : ∀ X B g r evs,
      P2OverPathCOkEnvOf (A := A.repAlloc) X W B
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        PromoteOverCanonSessEnv (kitEnvs B) g r evs →
      P2OverOkEnv g r evs)
    (hFitsSplit : ∀ X B st_b g r,
      FitsEnv M lim st_b (StageP2OverEnv P2OverErrEnv P2OverOkEnv g r) →
      FitsEnv M lim st_b
        (StageP2OverEnv
          (P2OverPathCErrEnvOf (A := A.repAlloc) X W B
            (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
            (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
            (kitEnvs B))
          (P2OverPathCOkEnvOf (A := A.repAlloc) X W B
            (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
            PromoteOverCanonSessEnv (kitEnvs B))
          g r))
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hSpqr : SpqrV1PlacedSeams M A lim mmpl gh W)
    (hRaw : EncodeRawPreallocPlacedOkX A.repAlloc (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hGrow : subroutine_ok (lsProg_51 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 621)
      (withLsCl lsmpl (growOneVecU8BudgetSpec M A lim)))
    (hSelfKit : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      IdentitySelfStoreKitPlacedOkI A lim
        (cliPollIdKitPlaced A.repAlloc F0 peer (cliKitStk B))
        (cliPollSelfKitPlaced A.repAlloc F0 peer (cliKitStk B))
        (kitEnvs B F0 peer spkId kpkId opkWord kbk).selfEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hSpkKit : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      SignedPreKeyStoreKitPlacedOk A lim
        (cliPollSpkKitPlaced A.repAlloc F0 spkId (cliKitStk B))
        (kitEnvs B F0 peer spkId kpkId opkWord kbk).spkEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hKpkKit : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      KyberPreKeyStoreKitPlacedOk A lim
        (cliPollKpkKitPlaced A.repAlloc F0 kpkId spkId kbk (cliKitStk B))
        (kitEnvs B F0 peer spkId kpkId opkWord kbk).kpkEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hPkKit : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      PreKeyStoreKitPlacedOk A lim
        (cliPollPkKitPlaced A.repAlloc F0 opkWord (cliKitStk B))
        (kitEnvs B F0 peer spkId kpkId opkWord kbk).pkEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    StageP2OverQpanCliFrozenPlacedAtStmt A lim mmpl gh W P2OverErrEnv P2OverOkEnv :=
  fun X =>
    stageP2Over_qpan_cli_full_placed_at_of_pathC
      (fun B =>
        stageP2PathCOver_qpan_cli_full_placed_at_of_seams A lim X mmpl gh W B
          (hErrEnv X B) (hOkEnv X B) (hFitsSplit X B) hDropNz hG hSpqr
          (hSelfKit B) (hSpkKit B) (hKpkKit B) (hPkKit B))
      (cliPromoteMatchingMissGen_placed_ok A.repAlloc mmpl gh W)
      (fun hh => cliPromoteOverGen_placed_ok mmpl gh W hh hGrow hRaw)

/-- Pointwise per-`(mmpl, gh, W)` seam-to-`StageP2OverQpanCliFrozenPlacedAtStmt` corollary at tight
`PromoteOverArchiveCanonSessEnv` (`ArchiveCoreEnv`), with zero `h_accept*` seams and zero
universal-`mmpl` premises. -/
theorem stageP2Over_qpan_cli_archive_full_placed_at_of_seams [LibsignalFullPlacement]
    {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {kitEnvs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      CliPollStageP2Envs (A := A.repAlloc) B F0 peer spkId kpkId opkWord kbk}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (hErrEnv : ∀ X B g r evs,
      P2OverPathCErrEnvOf (A := A.repAlloc) X W B
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
        (kitEnvs B) g r evs →
      P2OverErrEnv g r evs)
    (hOkEnv : ∀ X B g r evs,
      P2OverPathCOkEnvOf (A := A.repAlloc) X W B
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        PromoteOverArchiveCanonSessEnv (kitEnvs B) g r evs →
      P2OverOkEnv g r evs)
    (hFitsSplit : ∀ X B st_b g r,
      FitsEnv M lim st_b (StageP2OverEnv P2OverErrEnv P2OverOkEnv g r) →
      FitsEnv M lim st_b
        (StageP2OverEnv
          (P2OverPathCErrEnvOf (A := A.repAlloc) X W B
            (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
            (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
            (kitEnvs B))
          (P2OverPathCOkEnvOf (A := A.repAlloc) X W B
            (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
            PromoteOverArchiveCanonSessEnv (kitEnvs B))
          g r))
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hSpqr : SpqrV1PlacedSeams M A lim mmpl gh W)
    (hRaw : EncodeRawPreallocPlacedOkX A.repAlloc (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hGrow : subroutine_ok (lsProg_51 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 621)
      (withLsCl lsmpl (growOneVecU8BudgetSpec M A lim)))
    (hSelfKit : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      IdentitySelfStoreKitPlacedOkI A lim
        (cliPollIdKitPlaced A.repAlloc F0 peer (cliKitStk B))
        (cliPollSelfKitPlaced A.repAlloc F0 peer (cliKitStk B))
        (kitEnvs B F0 peer spkId kpkId opkWord kbk).selfEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hSpkKit : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      SignedPreKeyStoreKitPlacedOk A lim
        (cliPollSpkKitPlaced A.repAlloc F0 spkId (cliKitStk B))
        (kitEnvs B F0 peer spkId kpkId opkWord kbk).spkEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hKpkKit : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      KyberPreKeyStoreKitPlacedOk A lim
        (cliPollKpkKitPlaced A.repAlloc F0 kpkId spkId kbk (cliKitStk B))
        (kitEnvs B F0 peer spkId kpkId opkWord kbk).kpkEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hPkKit : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      PreKeyStoreKitPlacedOk A lim
        (cliPollPkKitPlaced A.repAlloc F0 opkWord (cliKitStk B))
        (kitEnvs B F0 peer spkId kpkId opkWord kbk).pkEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    StageP2OverQpanCliFrozenPlacedAtStmt A lim mmpl gh W P2OverErrEnv P2OverOkEnv :=
  fun X =>
    stageP2Over_qpan_cli_full_placed_at_of_pathC
      (fun B =>
        stageP2PathCOver_qpan_cli_archive_full_placed_at_of_seams A lim X mmpl gh W B
          (hErrEnv X B) (hOkEnv X B) (hFitsSplit X B) hDropNz hG hSpqr
          (hSelfKit B) (hSpkKit B) (hKpkKit B) (hPkKit B))
      (cliPromoteMatchingMissGen_placed_ok A.repAlloc mmpl gh W)
      (fun hh => cliPromoteOverGen_archive_placed_ok mmpl gh W hh hGrow hRaw)

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudget
