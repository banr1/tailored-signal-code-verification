/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.KeyPairCalleesAuxBudget
public import LibsignalBinary.Proofs.PeakBudget.CliRealExistentialCalleeEnvs
public import LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
public import LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit
public import LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit
public import LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux
public import LibsignalBinary.Proofs.PeakBudget.SpqrSendPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.W1SendRealSlot
public import LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds
public import LibsignalBinary.Proofs.PeakBudget.W2RecvWhisperRealSlot
public import LibsignalBinary.Proofs.PeakBudget.W3InitiatePeakSpec
public import LibsignalBinary.Proofs.PeakBudget.W3InitiateStagesPeak
public import LibsignalBinary.Proofs.PeakBudget.W3InitiateTightSpec
public import LibsignalBinary.Proofs.PeakBudget.W4ArchiveCancelPeak
public import LibsignalBinary.Proofs.PeakBudget.W4InitBobPeak
public import LibsignalBinary.Proofs.PeakBudget.W4OuterHelpers
public import LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.W4OuterStageHelpers
public import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot
public import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot1MiB
public import LibsignalBinary.Proofs.PeakBudget.WirePksmTightCredit
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget
public import LibsignalBinary.Proofs.RecordCodecs.DepsBudget
public import LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget
public import LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdKeyPairPollPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdRegIdPollPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.TopPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlotOfInnerPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LayoutBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.SymPlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.LayoutBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePoll.LayoutPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesBudget

/-!
# Binary-Kit Real CLI Callee Envelopes

Defines the binary store-kit poll envelopes (`AddrTextValEnv DecimalEnv`,
`DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd`, `ofBytesEnv RecordDeserializeCancelEnv`,
`RecordSerializeSeqFreeValidEnv`, `DirPutEnv`, `cliIdentityKitDefaultBudgetEnv`), the W1–W4
slot envelopes, and the whole-`run` and whole-`main` trace predicates `mkBinaryKitRealCalleeEnvs`,
`realCliRunBinaryKitEnvOf`, and `realCliMainBinaryKitEnvOf`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs

open CryptoGames.LibsignalSession (IdentityKey PublicKey SessionState ShaCompress)
open CryptoGames.LibsignalSessionApi (Session SessionRecord)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (encodeRecordPrev1Mem)
open CryptoVerification.E2E (PEParams UnreachedPqxdhPrimitives pqxdhSpqrModel)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity (IdentityStoreSpec)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.LibsignalTripleRatchet (DoReserveCall)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost SessionGhost uuidTryParse)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession (CliHooks Inputs)
open CryptoVerification.SignalSession.Cli (DirGhost ReadRule StoresGhost addressText keyName utf8)
open CryptoVerification.SignalSession.Cli.KitInst (cliIdentityVtRoSym cliSessionVtRoSym)
open CryptoVerification.SignalSession.Cli.KitInst.IdKit
  (savePollNeed saveShimNeed trustPollNeed trustShimNeed)
open CryptoVerification.SignalSession.Cli.KitInst.SessKit
  (loadPollNeed loadShimNeed storePollNeedX storeShimNeed)
open CryptoVerification.SignalSession.Cli.MainHops (AddrV CallV RunCall cliIo cliWrOk)
open CryptoVerification.SignalSession.Cli.RunCompose
  (DecSigGhost EncGhost InitGhost RunSem addrValOf runFiles)
open CryptoVerification.SignalSession.Cli.RunProofs.DecryptLemmas (toDecryptGhost)
open CryptoVerification.SignalSession.Cli.RunProofs.EncryptLemmas (w1EncGhost)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (scopeKit)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open LibsignalBinary.Heap (AllocEvent FreeOnlyEvs SeqEnv rustAllocEvents)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (StringCloneEnv)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefsBudgetAux
  (toTempTwinsIkitEnv toTempTwinsKitEnv)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins
  (WithStoresEncEnv)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.KeyPairCalleesAuxBudget
  (KemKeyPairFromPubPrivEnv)
open LibsignalBinary.Proofs.PeakBudget.CliRunArmsPeak (CliRunCalleeEnvs)
open LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge
  (CliRunBinaryEnv RealCliMainBinaryEnvOf)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (IterSeqEnv)
open LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit (dropClonedSessionEvents)
open LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit
  (RecordSerializeSeqFreeEnv SerializePrev1SeqFreeEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (msgCapBytes sessionCapBytes)
open LibsignalBinary.Proofs.PeakBudget.SpqrSendPeakSpec (SpqrSendTightCapEnv)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds
  (FreshBobCloneDom RecordGhostValid SessionCloneDom)
open LibsignalBinary.Proofs.PeakBudget.W2RecvWhisperRealSlot (W2RealTdEnv)
open LibsignalBinary.Proofs.PeakBudget.W3InitiatePeakSpec (W3BoxedStoreStepEnv)
open LibsignalBinary.Proofs.PeakBudget.W3InitiateStagesPeak
  (W3InitiateFullEnv W3InitiateFullEnvWide)
open LibsignalBinary.Proofs.PeakBudget.W3InitiateTightSpec (RecordAliceInitiatedAnyCkBounds)
open LibsignalBinary.Proofs.PeakBudget.W4ArchiveCancelPeak
  (ArchivedTrialIterEnv PromoteStateArchiveEnv)
open LibsignalBinary.Proofs.PeakBudget.W4InitBobPeak
  (W4BobSessionBuildEnv W4BoundedEvs W4PqxdhAcceptEnv)
open LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec
  (OptStageEnv W4DecryptPrekeySlotParams W4DecryptPrekeySplitWideSlotEnv W4ErrTailWideEnv
   W4StageP2MatchedCheckEnv W4StageP3WideEnv W4TryDecryptCloneFailWideEnv)
open LibsignalBinary.Proofs.PeakBudget.W4OuterStageHelpers (W4BoxedStoreStepEnv)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot
  (W4ArchivedTrial W4FailedTdCancelEnv W4RecvPrekeyRealParams
   W4RecvPrekeyTryDecACEnv mkW4RecvPrekeySlotParams)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot1MiB (W4RecvPrekeyRealDomOf)
open LibsignalBinary.Proofs.PeakBudget.WirePksmTightCredit (PksmCanonSliceEnv)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget
  (SessionGhostValid WithStoresDecEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (IdentityStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (BoxAllocEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (SessionStoreBudgetEnv)
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget (PreKeyDeserializeEnv RecordCodecLoopEnv)
open LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget (KyberDecodeEnv SpkLoopEnv)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget (RecordDeserializeCancelEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget (InitialStateEnv)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (SegCloneEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget (DecimalEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a (DirGetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget (PathEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux (DirPutEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux (DirPutStrEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
  (cliIdentityKitDefaultBudgetEnv cliIdentityKitSavePollEnv cliIdentityKitTrustPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
  (AddrTextValEnv cliSessionKitBudgetEnv cliSessionKitLoadPollEnv cliSessionKitStorePollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdKeyPairPollPlacedBudget
  (OptIkpTryFromEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdRegIdPollPlacedBudget
  (OptRegIdMalformedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget
  (decIdKitPlaced decSessKitPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlotOfInnerPlacedBudget
  (w1IdKitPlaced w1SessKitPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (ReadFileRuleEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LayoutBudget (CliKpkGetPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.SymPlacedBudgetAux
  (CliKpkMarkPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser (ofBytesEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.LayoutBudget (CliPkGetPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePoll.LayoutPlacedBudget
  (CliPkRemovePollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesBudget (CliSpkGetPollEnv)

/-! ## Binary Store-Kit Poll and Budget Envelopes -/

/-- Value-indexed `SessionRecord::serialize` (`lsProg_52`) spare-capacity envelope guarded by
`RecordGhostValid g r` (supplied at Block `570` by `sessionRecordAt`). -/
def RecordSerializeSeqFreeValidEnv
    (r : SessionRecord (List (BitVec 8))) (evs : List AllocEvent) : Prop :=
  ∃ g : RecordGhost, RecordGhostValid g r ∧ RecordSerializeSeqFreeEnv g r evs

/-- Binary-kit `SessionStoreBudgetEnv` for `w1SessKitPlaced A B F0 peer` at the true binary
kit polls (`AddrTextValEnv DecimalEnv`, `DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd`,
`ofBytesEnv RecordDeserializeCancelEnv`, `RecordSerializeSeqFreeValidEnv`, `DirPutEnv`). -/
noncomputable abbrev w1BinarySessKitPlacedBudget [LibsignalPlacement]
    (A : RustAlloc) (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost) :
    SessionStoreBudgetEnv (w1SessKitPlaced A B F0 peer) :=
  cliSessionKitBudgetEnv A cliIo.rd F0 cliWrOk scopeKit peer
    loadShimNeed (loadPollNeed B.readFile)
    storeShimNeed storePollNeedX
    (AddrTextValEnv DecimalEnv)
    (DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd)
    (ofBytesEnv RecordDeserializeCancelEnv)
    RecordSerializeSeqFreeValidEnv
    DirPutEnv
    cliSessionVtRoSym cliIdentityVtRoSym

/-- Binary-kit `IdentityStoreBudgetEnv` for `w1IdKitPlaced A B F0 peer` at the true binary
identity polls (`DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd`, `DirPutStrEnv`). -/
noncomputable abbrev w1BinaryIdKitPlacedBudget [LibsignalPlacement]
    (A : RustAlloc) (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost) :
    IdentityStoreBudgetEnv (w1IdKitPlaced A B F0 peer) :=
  cliIdentityKitDefaultBudgetEnv A cliIo.rd F0 cliWrOk peer
    trustShimNeed (trustPollNeed B.readFile)
    saveShimNeed (savePollNeed B.readFile)
    cliIdentityVtRoSym (ReadFileRuleEnv cliIo.rd)

noncomputable abbrev decBinarySessKitPlacedBudget [LibsignalPlacement]
    (A : RustAlloc) (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost) :
    SessionStoreBudgetEnv (decSessKitPlaced A F0 peer B) :=
  w1BinarySessKitPlacedBudget A B F0 peer

noncomputable abbrev decBinaryIdKitPlacedBudget [LibsignalPlacement]
    (A : RustAlloc) (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost) :
    IdentityStoreBudgetEnv (decIdKitPlaced A F0 peer B) :=
  w1BinaryIdKitPlacedBudget A B F0 peer

/-! ## Binary-Kit W3 (`init`), W1 (`send`), and W2 (`recv` Whisper) Slot Envelopes -/

/-- Parameter bundle for the binary-kit W3 (`init`) slot envelope. -/
structure W3BinaryInitParams where
  x : InitGhost
  F : ShaCompress
  peerKey : IdentityKey
  x_spqr : InitialStateGhost
  g_rec : RecordGhost
  r_rec : SessionRecord (List (BitVec 8))

/-- Call-site alignment, `peer.name ≤ 40`, `runFiles` binding, SPQR key bound, and
Alice-initiated `SessionRecord` bounds (`RecordAliceInitiatedAnyCkBounds`) for `W3BinaryInitParams`
on `.init peerAddr dir` (vacuously satisfied on `.keygen`, `.send`, `.recv`). -/
def W3BinaryInitDom (c : CallV) (i : Inputs) (w : W3BinaryInitParams) : Prop :=
  ∀ (peerAddr : AddrV) (dir : List (BitVec 8)), c = .init peerAddr dir →
    w.x.peer.val = addrValOf peerAddr ∧
    w.x.peer.name.bytes.length ≤ 40 ∧
    w.x.F = runFiles i ∧
    w.x_spqr.p.authKey.length ≤ 32 ∧
    RecordGhostValid w.g_rec w.r_rec ∧
    RecordAliceInitiatedAnyCkBounds w.g_rec w.r_rec

/-- Binary-kit W3 (`init`) slot envelope (`W3InitiateFullEnvWide` across the 6 true binary
store-kit / self-store polls at `AddrTextValEnv DecimalEnv`,
`DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd`,
`ofBytesEnv RecordDeserializeCancelEnv`, `OptIkpTryFromEnv`, `OptRegIdMalformedEnv`,
`RecordSerializeSeqFreeEnv w.g_rec`, `DirPutStrEnv`, `DirPutEnv`, and `InitialStateEnv`). -/
def W3InitBinaryKitSlotEnv (w : W3BinaryInitParams) (evs : List AllocEvent) : Prop :=
  W3InitiateFullEnvWide
    (W3BoxedStoreStepEnv 32
      (cliIdentityKitTrustPollEnv
        (DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd)
        w.x.F StoresGhost.opened.identity w.x.peer.val w.peerKey .sending))
    (W3BoxedStoreStepEnv 24
      (cliSessionKitLoadPollEnv cliIo.rd scopeKit
        (AddrTextValEnv DecimalEnv)
        (DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd)
        (ofBytesEnv RecordDeserializeCancelEnv)
        w.x.F StoresGhost.opened.sessions w.x.peer.val))
    (W3BoxedStoreStepEnv 16
      (SeqEnv
        (DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd
          w.x.F StoresGhost.opened.identity.own (utf8 "identity-key-pair"))
        (SeqEnv
          (OptIkpTryFromEnv
            (StoresGhost.opened.identity.own.get cliIo.rd w.x.F (utf8 "identity-key-pair")))
          FreeOnlyEvs)))
    (InitialStateEnv w.F w.x_spqr)
    (W3BoxedStoreStepEnv 16
      (SeqEnv
        (DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd
          w.x.F StoresGhost.opened.identity.own (utf8 "registration-id"))
        (SeqEnv
          (OptRegIdMalformedEnv
            (StoresGhost.opened.identity.own.get cliIo.rd w.x.F (utf8 "registration-id")))
          FreeOnlyEvs)))
    (W3BoxedStoreStepEnv 32
      (cliIdentityKitSavePollEnv cliIo.rd
        (DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd)
        DirPutStrEnv w.x.F StoresGhost.opened.identity w.x.peer.val w.peerKey))
    (W3BoxedStoreStepEnv 32
      (cliSessionKitStorePollEnv
        (AddrTextValEnv DecimalEnv)
        (RecordSerializeSeqFreeEnv w.g_rec)
        DirPutEnv StoresGhost.opened.sessions w.x.peer.val w.r_rec))
    w.x.peer.name.bytes.length
    evs

/-- Parameter bundle for the binary-kit W1 (`send`) slot envelope. -/
structure W1BinarySendParams where
  repAlloc : RustAlloc
  B : RunBudgets
  peer : AddrGhost
  x : EncGhost

/-- Call-site alignment & `1 MiB` plaintext bound for `W1BinarySendParams` on `.send peerAddr`
(vacuously satisfied on `.keygen`, `.init`, `.recv`). -/
def W1BinarySendDom (c : CallV) (i : Inputs) (R : W1BinarySendParams) : Prop :=
  ∀ peerAddr, c = .send peerAddr →
    R.peer.val = addrValOf peerAddr ∧
    R.x.peer = R.peer ∧
    (w1EncGhost R.x).rem.val = R.peer.val ∧
    (w1EncGhost R.x).ptext.length ≤ msgCapBytes ∧
    R.x.F = runFiles i

/-- Binary-kit W1 (`send`) slot envelope (`WithStoresEncEnv` at `w1BinarySessKitPlacedBudget`,
`w1BinaryIdKitPlacedBudget`, and `SpqrSendTightCapEnv`; definitionally equal to
`CliEncryptSlotEnv P A R.B SpqrSendTightCapEnv (w1BinarySessKitPlacedBudget A.repAlloc R.B)
(w1BinaryIdKitPlacedBudget A.repAlloc R.B) R.x` when `R.repAlloc = A.repAlloc`). -/
def W1SendBinaryKitSlotEnv [LibsignalPlacement]
    (P : PEParams) (R : W1BinarySendParams) (evs : List AllocEvent) : Prop :=
  WithStoresEncEnv
    (w1SessKitPlaced R.repAlloc R.B R.x.F R.x.peer)
    (toTempTwinsKitEnv (w1BinarySessKitPlacedBudget R.repAlloc R.B R.x.F R.x.peer))
    StoresGhost.opened.sessions
    (w1IdKitPlaced R.repAlloc R.B R.x.F R.x.peer)
    (toTempTwinsIkitEnv (w1BinaryIdKitPlacedBudget R.repAlloc R.B R.x.F R.x.peer))
    StoresGhost.opened.identity
    scopeKit P.C (pqxdhSpqrModel P) SpqrSendTightCapEnv uuidTryParse (w1EncGhost R.x) evs

/-- Parameter bundle for the binary-kit W2 (`recv` whisper) slot envelope. -/
structure W2BinaryWhisperParams where
  repAlloc : RustAlloc
  B : RunBudgets
  peer : AddrGhost
  x : DecSigGhost

/-- Call-site alignment & `1 MiB` ciphertext bound for `W2BinaryWhisperParams` on `.recv peerAddr`
(vacuously satisfied on `.keygen`, `.init`, `.send`). -/
def W2BinaryWhisperDom (c : CallV) (i : Inputs) (R : W2BinaryWhisperParams) : Prop :=
  ∀ peerAddr, c = .recv peerAddr →
    R.peer.val = addrValOf peerAddr ∧
    R.x.peer = R.peer ∧
    (toDecryptGhost R.x).rem.val = R.peer.val ∧
    (toDecryptGhost R.x).msg.ciphertext.length ≤ msgCapBytes ∧
    R.x.F = runFiles i

/-- Binary-kit W2 (`recv` whisper) slot envelope (`WithStoresDecEnv` at
`decBinarySessKitPlacedBudget`, `decBinaryIdKitPlacedBudget`, and `W2RealTdEnv P.C.F P.Q.K`;
definitionally equal to `CliDecryptSignalSlotEnv P A R.B (W2RealTdEnv P.C.F P.Q.K)
(decBinarySessKitPlacedBudget A.repAlloc R.B) (decBinaryIdKitPlacedBudget A.repAlloc R.B) R.x`
when `R.repAlloc = A.repAlloc`). -/
def W2RecvWhisperBinaryKitSlotEnv [LibsignalPlacement]
    (P : PEParams) (R : W2BinaryWhisperParams) (evs : List AllocEvent) : Prop :=
  WithStoresDecEnv
    (decSessKitPlaced R.repAlloc R.x.F R.x.peer R.B)
    (decBinarySessKitPlacedBudget R.repAlloc R.B R.x.F R.x.peer)
    StoresGhost.opened.sessions
    (decIdKitPlaced R.repAlloc R.x.F R.x.peer R.B)
    (decBinaryIdKitPlacedBudget R.repAlloc R.B R.x.F R.x.peer)
    StoresGhost.opened.identity
    P.C (pqxdhSpqrModel P) uuidTryParse (W2RealTdEnv P.C.F P.Q.K) scopeKit
    (toDecryptGhost R.x) evs

/-! ## Binary-Kit W4 (`recv-prekey`) Slot Envelopes -/

abbrev W4CloneBDomEnv (evs : List AllocEvent) : Prop :=
  ∃ (G : SessionGhost) (ses : Session (List (BitVec 8))),
    SessionGhostValid G ses ∧ SessionCloneDom 286196 ses ∧ SegCloneEnv G ses.state evs

abbrev W4CloneACDomEnv (evs : List AllocEvent) : Prop :=
  ∃ (G : SessionGhost) (ses : Session (List (BitVec 8))),
    FreshBobCloneDom 16384 G ses ∧ SegCloneEnv G ses.state evs

abbrev W4TrialRunWideEnv (F : ShaCompress) (K : MlKem) (x : W4ArchivedTrial F)
    (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨
    W4TryDecryptCloneFailWideEnv (SegCloneEnv x.G_tr x.ses_tr.state)
      (W4FailedTdCancelEnv F K x.fc_tr)
      (· = dropClonedSessionEvents x.G_tr x.ses_tr.state) evs

abbrev mkW4RecvPrekeyWideSlotParams (R : W4RecvPrekeyRealParams) :
    W4DecryptPrekeySlotParams (W4ArchivedTrial R.F) :=
  { mkW4RecvPrekeySlotParams R with TrialEnv := W4TrialRunWideEnv R.F R.K }

/-- Disjunction envelope for `decode_signed_pre_key` / `decode_kyber_pre_key` (Block `595`),
`rfl`-identical to `Stage2V1KitsPlacedBudgetAux.CliSpkDecodeEnv`. -/
def CliSpkDecodeEnv (bs : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  SpkLoopEnv (2 * bs.length + 3) bs.length evs ∨ KyberDecodeEnv bs.length evs

/-- Disjunction envelope for `PreKeyRecord::deserialize` (Block `65`),
`rfl`-identical to `Stage2V1KitsPlacedBudgetAux.CliPkDecodeEnv`. -/
def CliPkDecodeEnv (bs : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  RecordCodecLoopEnv (2 * bs.length + 3) bs.length evs ∨ PreKeyDeserializeEnv bs.length evs

/-- Binary-kit `load_session` boxed step (`24` B box + `cliSessionKitLoadPollEnv` at
`RecordDeserializeCancelEnv`). -/
def W4BinarySessLoadStepEnv (rd : ReadRule) (files : FsFiles) (peer : AddrGhost) :
    List AllocEvent → Prop :=
  W4BoxedStoreStepEnv 24
    (cliSessionKitLoadPollEnv rd scopeKit (AddrTextValEnv DecimalEnv)
      (DirGetEnv PathEnv (ReadFileRuleEnv rd) rd) (ofBytesEnv RecordDeserializeCancelEnv)
      files StoresGhost.opened.sessions peer.val)

/-- Binary-kit `is_trusted_identity` boxed step (`32` B box + `cliIdentityKitTrustPollEnv` at
`.receiving`). -/
def W4BinaryIdTrustStepEnv (rd : ReadRule) (files : FsFiles) (peer : AddrGhost)
    (remoteIdKey : IdentityKey) : List AllocEvent → Prop :=
  W4BoxedStoreStepEnv 32
    (cliIdentityKitTrustPollEnv (DirGetEnv PathEnv (ReadFileRuleEnv rd) rd)
      files StoresGhost.opened.identity peer.val remoteIdKey .receiving)

/-- Binary-kit `save_identity` boxed step (`32` B box + `cliIdentityKitSavePollEnv`). -/
def W4BinaryIdSaveStepEnv (rd : ReadRule) (files : FsFiles) (peer : AddrGhost)
    (remoteIdKey : IdentityKey) : List AllocEvent → Prop :=
  W4BoxedStoreStepEnv 32
    (cliIdentityKitSavePollEnv rd (DirGetEnv PathEnv (ReadFileRuleEnv rd) rd)
      DirPutStrEnv files StoresGhost.opened.identity peer.val remoteIdKey)

/-- Binary-kit `0`-prev `store_session` boxed step (`32` B box + `cliSessionKitStorePollEnv`). -/
def W4BinarySessStoreStepEnv (peer : AddrGhost) (g_rec : RecordGhost)
    (r_rec : SessionRecord (List (BitVec 8))) : List AllocEvent → Prop :=
  W4BoxedStoreStepEnv 32
    (cliSessionKitStorePollEnv (AddrTextValEnv DecimalEnv)
      (RecordSerializeSeqFreeEnv g_rec) DirPutEnv StoresGhost.opened.sessions peer.val r_rec)

/-- Binary-kit `prev1` `store_session` boxed step (`32` B box + `AddrTextValEnv` →
`SerializePrev1SeqFreeEnv` → `DirPutEnv`). -/
def W4BinarySessStorePrev1StepEnv (peer : AddrGhost) (G : SessionGhost)
    (sess : Session (List (BitVec 8))) (enc : List (BitVec 8)) : List AllocEvent → Prop :=
  W4BoxedStoreStepEnv 32
    (SeqEnv (AddrTextValEnv DecimalEnv peer.val)
      (SeqEnv (SerializePrev1SeqFreeEnv G sess enc)
        (DirPutEnv StoresGhost.opened.sessions (addressText peer.val)
          (encodeRecordPrev1Mem G sess enc))))

/-- Binary-kit `get_signed_pre_key` boxed step (`16` B box + `CliSpkGetPollEnv`). -/
def W4BinarySpkGetStepEnv (rd : ReadRule) (files : FsFiles) (spkId : BitVec 32) :
    List AllocEvent → Prop :=
  W4BoxedStoreStepEnv 16
    (CliSpkGetPollEnv DecimalEnv
      (fun d k => DirGetEnv PathEnv (ReadFileRuleEnv rd) rd files d (keyName k))
      CliSpkDecodeEnv rd files ⟨0#64, 0#64, 0#64, spkId, StoresGhost.opened.signed⟩)

/-- Binary-kit `get_kyber_pre_key` boxed step (`16` B box + `CliKpkGetPollEnv` over `oneTime` and
fallback `lastResort`). -/
def W4BinaryKpkGetStepEnv (rd : ReadRule) (files : FsFiles) (kpkId : BitVec 32) :
    List AllocEvent → Prop :=
  W4BoxedStoreStepEnv 16
    (CliKpkGetPollEnv DecimalEnv
      (fun d k => DirGetEnv PathEnv (ReadFileRuleEnv rd) rd files d (keyName k))
      CliSpkDecodeEnv rd files ⟨0#64, 0#64, 0#64, kpkId, StoresGhost.opened.kyber⟩)

/-- Binary-kit `get_pre_key` boxed step (`16` B box + `CliPkGetPollEnv`). -/
def W4BinaryPkGetStepEnv (rd : ReadRule) (files : FsFiles) (opkId : BitVec 32) :
    List AllocEvent → Prop :=
  W4BoxedStoreStepEnv 16
    (CliPkGetPollEnv DecimalEnv (DirGetEnv PathEnv (ReadFileRuleEnv rd) rd files)
      CliPkDecodeEnv rd files ⟨0#64, 0#64, 0#64, opkId, StoresGhost.opened.oneTime⟩)

/-- Optional-box store-step combinator (`OptStageEnv (BoxAllocEnv boxBytes)` → `inner`), matching
left-nested Stage-P2 `SeqEnv` splits where `BoxAllocEnv 16` precedes an earlier `OptStageEnv`
cut at `+0` B across all `PhaseCreditSpec` columns. -/
def W4OptBoxedStoreStepEnv (boxBytes : Nat) (inner : List AllocEvent → Prop) :
    List AllocEvent → Prop :=
  SeqEnv (OptStageEnv (BoxAllocEnv boxBytes)) inner

/-- Binary-kit `get_identity_key_pair` boxed step (`OptStageEnv (BoxAllocEnv 16)` + `DirGetEnv` +
`OptIkpTryFromEnv` + `FreeOnlyEvs`). -/
def W4BinarySelfKpStepEnv (rd : ReadRule) (files : FsFiles) : List AllocEvent → Prop :=
  W4OptBoxedStoreStepEnv 16
    (SeqEnv (DirGetEnv PathEnv (ReadFileRuleEnv rd) rd files
        StoresGhost.opened.identity.own (utf8 "identity-key-pair"))
      (SeqEnv
        (OptIkpTryFromEnv (StoresGhost.opened.identity.own.get rd files (utf8 "identity-key-pair")))
        FreeOnlyEvs))

abbrev W4BinarySelfKpStepOptEnv := W4BinarySelfKpStepEnv

/-- Binary-kit `get_local_registration_id` boxed step (`16` B box + `DirGetEnv` +
`OptRegIdMalformedEnv`). -/
def W4BinarySelfRegIdStepEnv (rd : ReadRule) (files : FsFiles) : List AllocEvent → Prop :=
  W4BoxedStoreStepEnv 16
    (SeqEnv (DirGetEnv PathEnv (ReadFileRuleEnv rd) rd files
        StoresGhost.opened.identity.own (utf8 "registration-id"))
      (SeqEnv
        (OptRegIdMalformedEnv (StoresGhost.opened.identity.own.get rd files (utf8 "registration-id")))
        FreeOnlyEvs))

/-- Binary-kit `mark_kyber_pre_key_used` boxed step (`32` B box + `CliKpkMarkPollEnv`). -/
def W4BinaryKpkMarkStepEnv (rd : ReadRule) (files : FsFiles)
    (kpkId spkId : BitVec 32) (baseKey : PublicKey) : List AllocEvent → Prop :=
  W4BoxedStoreStepEnv 32
    (CliKpkMarkPollEnv rd DecimalEnv (DirGetEnv PathEnv (ReadFileRuleEnv rd) rd) DirPutEnv
      files ⟨0#64, 0#64, 0#64, 0#64, kpkId, spkId, baseKey, StoresGhost.opened.kyber⟩)

/-- Binary-kit `remove_pre_key` boxed step (`16` B box + `CliPkRemovePollEnv`). -/
def W4BinaryPkRemoveStepEnv (rd : ReadRule) (files : FsFiles) (opkId : BitVec 32) :
    List AllocEvent → Prop :=
  W4BoxedStoreStepEnv 16
    (CliPkRemovePollEnv rd DecimalEnv (DirGetEnv PathEnv (ReadFileRuleEnv rd) rd) DirPutEnv
      files ⟨0#64, 0#64, 0#64, opkId, StoresGhost.opened.oneTime⟩)

/-- Binary-kit Stage P1 trusted-path (`is_trusted_identity = .ok true` or early error) envelope. -/
def W4BinaryStageP1OkEnv (rd : ReadRule) (files : FsFiles) (peer : AddrGhost)
    (remoteIdKey : IdentityKey) (evs : List AllocEvent) : Prop :=
  SeqEnv (W4BinarySessLoadStepEnv rd files peer)
    (OptStageEnv (W4BinaryIdTrustStepEnv rd files peer remoteIdKey)) evs

/-- Binary-kit Stage P1 untrusted-rejection (`is_trusted_identity = .ok false`) envelope,
including `StringCloneEnv peer.name` (`peer.name.bytes.length` allocation when non-empty). -/
def W4BinaryStageP1UntrustedEnv (rd : ReadRule) (files : FsFiles) (peer : AddrGhost)
    (remoteIdKey : IdentityKey) (evs : List AllocEvent) : Prop :=
  SeqEnv (W4BinarySessLoadStepEnv rd files peer)
    (SeqEnv (W4BinaryIdTrustStepEnv rd files peer remoteIdKey)
      (SeqEnv (StringCloneEnv peer.name) FreeOnlyEvs)) evs

/-- Binary-kit `Pqxdh::accept` envelope covering both `W4PqxdhAcceptEnv` and Block-`79`
`AcceptOptFieldsEnv` (`≤ 6` small allocations `≤ 192` B including the `32`-byte `dhCycle` boxes). -/
def W4BinaryAcceptWideEnv (x_res : DoReserveCall) (hasOpk : Bool)
    (evs : List AllocEvent) : Prop :=
  W4PqxdhAcceptEnv x_res hasOpk evs ∨ SeqEnv (W4BoundedEvs 6 192) FreeOnlyEvs evs

/-- Binary-kit `initialize_bob_session` envelope (`W4BinaryAcceptWideEnv` → `InitialStateEnv` →
`W4BobSessionBuildEnv9`). -/
def W4BinaryInitBobWideEnv (F : ShaCompress) (x_res : DoReserveCall) (hasOpk : Bool)
    (x_spqr : InitialStateGhost) (evs : List AllocEvent) : Prop :=
  SeqEnv (W4BinaryAcceptWideEnv x_res hasOpk)
    (OptStageEnv
      (SeqEnv (InitialStateEnv F x_spqr) (OptStageEnv W4OuterPeakSpec.W4BobSessionBuildEnv9))) evs

/-- Direct single-allocation `ArchiveCoreEnv` envelope (`encLen ≤ maxEncLen` + optional `96` B
`Vec` buffer + `FreeOnlyEvs` drops). -/
def W4BinaryArchiveDirectEnv (maxEncLen : Nat) (evs : List AllocEvent) : Prop :=
  SeqEnv FreeOnlyEvs
    (SeqEnv (fun e => ∃ n ≤ maxEncLen, e = rustAllocEvents n 1)
      (SeqEnv (W4BoundedEvs 1 192) FreeOnlyEvs)) evs

/-- Binary-kit session-archive envelope covering `RecordSerializeSeqFreeEnv` promotion and
direct `ArchiveCoreEnv` promotion bounded by `(encodeRecord r_arch).length`. -/
def W4BinaryPromoteArchiveEnv (g_arch : RecordGhost) (r_arch : SessionRecord (List (BitVec 8)))
    (evs : List AllocEvent) : Prop :=
  PromoteStateArchiveEnv (RecordSerializeSeqFreeEnv g_arch r_arch) (W4BoundedEvs 1 192) evs ∨
    W4BinaryArchiveDirectEnv (encodeRecord r_arch).length evs

/-- Binary-kit Stage P2 Path B (`Matched`) envelope. -/
def W4BinaryStageP2MatchedWideEnv {α : Type}
    (DecEnv TrialEnv DropEnv : α → List AllocEvent → Prop) (xs : List α)
    (g_arch : RecordGhost) (r_arch : SessionRecord (List (BitVec 8)))
    (evs : List AllocEvent) : Prop :=
  SeqEnv W4StageP2MatchedCheckEnv
    (OptStageEnv
      (fun evs2 => FreeOnlyEvs evs2 ∨
        SeqEnv (IterSeqEnv (ArchivedTrialIterEnv DecEnv TrialEnv DropEnv) xs)
          (fun evs3 => FreeOnlyEvs evs3 ∨
            SeqEnv (W4BinaryPromoteArchiveEnv g_arch r_arch) FreeOnlyEvs evs3) evs2)) evs

/-- Binary-kit Stage P2 Path A (`0`-prev) envelope across Substages P2.1–P2.6
(`PublicKey::serialize` → `spkGet` → `kpkGet` → `KemKeyPairFromPubPrivEnv` → `P2Sub3TailAllocEnv` →
optional `pkGet` → `selfKp` → `W4BinaryInitBobWideEnv` → `selfRegId` → `W4ErrTailWideEnv`). -/
def W4BinaryStageP2PathAWideEnv (hasOpk : Bool) (rd : ReadRule) (files : FsFiles)
    (spkId kpkId opkId : BitVec 32)
    (F : ShaCompress) (x_res : DoReserveCall) (x_spqr : InitialStateGhost)
    (evs : List AllocEvent) : Prop :=
  SeqEnv (OptStageEnv (SeqEnv (W4BoundedEvs 1 33) FreeOnlyEvs))
    (SeqEnv (OptStageEnv (W4BinarySpkGetStepEnv rd files spkId))
      (SeqEnv (OptStageEnv (W4BinaryKpkGetStepEnv rd files kpkId))
        (SeqEnv (OptStageEnv (SeqEnv KemKeyPairFromPubPrivEnv FreeOnlyEvs))
          (SeqEnv (OptStageEnv (SeqEnv (W4BoundedEvs 1 21) FreeOnlyEvs))
            (SeqEnv (OptStageEnv (if hasOpk then W4BinaryPkGetStepEnv rd files opkId else (· = [])))
              (SeqEnv (OptStageEnv (W4BinarySelfKpStepEnv rd files))
                (SeqEnv (OptStageEnv (W4BinaryInitBobWideEnv F x_res hasOpk x_spqr))
                  (SeqEnv (OptStageEnv (W4BinarySelfRegIdStepEnv rd files))
                    W4ErrTailWideEnv)))))))) evs

/-- Binary-kit Stage P2 Path C (`prev1`) envelope across failed trials and Substages P2.1–P2.6
(`selfRegId` → `W4BinaryPromoteArchiveEnv` → `W4ErrTailWideEnv`). -/
def W4BinaryStageP2PathCWideEnv {α : Type}
    (G_cur : SessionGhost) (st_cur : SessionState (List (BitVec 8)))
    (CurTrialFailEnv : List AllocEvent → Prop)
    (DecEnv TrialEnv DropEnv : α → List AllocEvent → Prop) (xs : List α)
    (g_arch : RecordGhost) (r_arch : SessionRecord (List (BitVec 8)))
    (hasOpk : Bool) (rd : ReadRule) (files : FsFiles)
    (spkId kpkId opkId : BitVec 32)
    (F : ShaCompress) (x_res : DoReserveCall) (x_spqr : InitialStateGhost)
    (evs : List AllocEvent) : Prop :=
  SeqEnv
    (OptStageEnv
      (W4TryDecryptCloneFailWideEnv (SegCloneEnv G_cur st_cur) CurTrialFailEnv
        (· = dropClonedSessionEvents G_cur st_cur)))
    (SeqEnv (OptStageEnv (IterSeqEnv (ArchivedTrialIterEnv DecEnv TrialEnv DropEnv) xs))
      (SeqEnv (OptStageEnv (SeqEnv (W4BoundedEvs 1 33) FreeOnlyEvs))
        (SeqEnv (OptStageEnv (W4BinarySpkGetStepEnv rd files spkId))
          (SeqEnv (OptStageEnv (W4BinaryKpkGetStepEnv rd files kpkId))
            (SeqEnv (OptStageEnv (SeqEnv KemKeyPairFromPubPrivEnv FreeOnlyEvs))
              (SeqEnv (OptStageEnv (SeqEnv (W4BoundedEvs 1 21) FreeOnlyEvs))
                (SeqEnv (OptStageEnv (if hasOpk then W4BinaryPkGetStepEnv rd files opkId else (· = [])))
                  (SeqEnv (OptStageEnv (W4BinarySelfKpStepEnv rd files))
                    (SeqEnv (OptStageEnv (W4BinaryInitBobWideEnv F x_res hasOpk x_spqr))
                      (SeqEnv (OptStageEnv (W4BinarySelfRegIdStepEnv rd files))
                        (SeqEnv (OptStageEnv (W4BinaryPromoteArchiveEnv g_arch r_arch))
                          W4ErrTailWideEnv))))))))))) evs

/-- Binary-kit Stage P4 Path B (`Matched`) envelope (`idSave` → `sessStore`). -/
def W4BinaryStageP4MatchedWideEnv (rd : ReadRule) (files : FsFiles) (peer : AddrGhost)
    (remoteIdKey : IdentityKey) (g_out0 : RecordGhost) (r_out0 : SessionRecord (List (BitVec 8)))
    (evs : List AllocEvent) : Prop :=
  SeqEnv (OptStageEnv (W4BinaryIdSaveStepEnv rd files peer remoteIdKey))
    (SeqEnv (OptStageEnv (W4BinarySessStoreStepEnv peer g_out0 r_out0)) FreeOnlyEvs) evs

/-- Binary-kit Stage P4 Path A (`0`-prev) envelope (`idSave` → `kpkMark` → optional `pkRemove` → `sessStore`). -/
def W4BinaryStageP4PathAWideEnv (hasOpk : Bool) (rd : ReadRule) (files : FsFiles)
    (peer : AddrGhost) (remoteIdKey : IdentityKey)
    (kpkId spkId opkId : BitVec 32) (baseKey : PublicKey)
    (g_out0 : RecordGhost) (r_out0 : SessionRecord (List (BitVec 8)))
    (evs : List AllocEvent) : Prop :=
  SeqEnv (OptStageEnv (W4BinaryIdSaveStepEnv rd files peer remoteIdKey))
    (SeqEnv (OptStageEnv (W4BinaryKpkMarkStepEnv rd files kpkId spkId baseKey))
      (SeqEnv (OptStageEnv (if hasOpk then W4BinaryPkRemoveStepEnv rd files opkId else (· = [])))
        (SeqEnv (OptStageEnv (W4BinarySessStoreStepEnv peer g_out0 r_out0)) FreeOnlyEvs))) evs

/-- Binary-kit Stage P4 Path C (`prev1`) envelope (`idSave` → `kpkMark` → optional `pkRemove` →
`sessStorePrev1` at K2 `SerializePrev1SeqFreeEnv`). -/
def W4BinaryStageP4PathCWideEnv (hasOpk : Bool) (rd : ReadRule) (files : FsFiles)
    (peer : AddrGhost) (remoteIdKey : IdentityKey)
    (kpkId spkId opkId : BitVec 32) (baseKey : PublicKey)
    (G_out1 : SessionGhost) (sess_out1 : Session (List (BitVec 8))) (enc_prev1 : List (BitVec 8))
    (evs : List AllocEvent) : Prop :=
  SeqEnv (OptStageEnv (W4BinaryIdSaveStepEnv rd files peer remoteIdKey))
    (SeqEnv (OptStageEnv (W4BinaryKpkMarkStepEnv rd files kpkId spkId baseKey))
      (SeqEnv (OptStageEnv (if hasOpk then W4BinaryPkRemoveStepEnv rd files opkId else (· = [])))
        (SeqEnv (OptStageEnv (W4BinarySessStorePrev1StepEnv peer G_out1 sess_out1 enc_prev1))
          FreeOnlyEvs))) evs

/-- Parameter bundle for the binary-kit W4 (`recv-prekey`) slot envelope. -/
structure W4BinaryRecvPrekeyParams where
  base : W4RecvPrekeyRealParams
  remoteIdKey : IdentityKey
  baseKey : PublicKey

/-- Call-site alignment, `peer.name.bytes.length ≤ 40`, `runFiles` / `cliIo.rd` binding, and
`1 MiB` pure domain bounds for `W4BinaryRecvPrekeyParams` on `.recv peerAddr`
(vacuously satisfied on `.keygen`, `.init`, `.send`). -/
def W4BinaryRecvPrekeyDom (c : CallV) (i : Inputs) (w : W4BinaryRecvPrekeyParams) : Prop :=
  ∀ peerAddr, c = .recv peerAddr →
    w.base.peer.val = addrValOf peerAddr ∧
    w.base.peer.name.bytes.length ≤ 40 ∧
    w.base.files = runFiles i ∧
    w.base.rd = cliIo.rd ∧
    W4RecvPrekeyRealDomOf sessionCapBytes msgCapBytes w.base

/-- Binary-kit Path B (`Matched` session) Stages P1 → P2 → P3 → P4 envelope. -/
def W4BinaryRecvPrekeyPathBWideEnv (w : W4BinaryRecvPrekeyParams)
    (evs : List AllocEvent) : Prop :=
  let P := mkW4RecvPrekeyWideSlotParams w.base
  SeqEnv (W4BinaryStageP1OkEnv w.base.rd w.base.files w.base.peer w.remoteIdKey)
    (SeqEnv
      (OptStageEnv
        (W4BinaryStageP2MatchedWideEnv P.DecEnv P.TrialEnv P.DropEnv P.archivedTrials
          w.base.g_arch w.base.r_arch))
      (SeqEnv (OptStageEnv (W4StageP3WideEnv W4CloneBDomEnv P.TryDecEnv))
        (OptStageEnv
          (W4BinaryStageP4MatchedWideEnv w.base.rd w.base.files w.base.peer w.remoteIdKey
            w.base.g_out0 w.base.r_out0)))) evs

/-- Binary-kit Path A (`0`-prev) Stages P1 → P2 → P3 → P4 envelope. -/
def W4BinaryRecvPrekeyPathAWideEnv (w : W4BinaryRecvPrekeyParams)
    (evs : List AllocEvent) : Prop :=
  SeqEnv (W4BinaryStageP1OkEnv w.base.rd w.base.files w.base.peer w.remoteIdKey)
    (SeqEnv
      (OptStageEnv
        (W4BinaryStageP2PathAWideEnv w.base.hasOpk w.base.rd w.base.files
          w.base.spkId w.base.kpkId w.base.opkId w.base.F w.base.x_res w.base.x_spqr))
      (SeqEnv (OptStageEnv (W4StageP3WideEnv W4CloneACDomEnv (W4RecvPrekeyTryDecACEnv w.base)))
        (OptStageEnv
          (W4BinaryStageP4PathAWideEnv w.base.hasOpk w.base.rd w.base.files w.base.peer
            w.remoteIdKey w.base.kpkId w.base.spkId w.base.opkId w.baseKey
            w.base.g_out0 w.base.r_out0)))) evs

/-- Binary-kit Path C (`Over` / `prev1`) Stages P1 → P2 → P3 → P4 envelope. -/
def W4BinaryRecvPrekeyPathCWideEnv (w : W4BinaryRecvPrekeyParams)
    (evs : List AllocEvent) : Prop :=
  let P := mkW4RecvPrekeyWideSlotParams w.base
  SeqEnv (W4BinaryStageP1OkEnv w.base.rd w.base.files w.base.peer w.remoteIdKey)
    (SeqEnv
      (OptStageEnv
        (W4BinaryStageP2PathCWideEnv w.base.G_cur w.base.st_cur P.CurTrialFailEnv
          P.DecEnv P.TrialEnv P.DropEnv P.archivedTrials w.base.g_arch w.base.r_arch
          w.base.hasOpk w.base.rd w.base.files w.base.spkId w.base.kpkId w.base.opkId
          w.base.F w.base.x_res w.base.x_spqr))
      (SeqEnv (OptStageEnv (W4StageP3WideEnv W4CloneACDomEnv (W4RecvPrekeyTryDecACEnv w.base)))
        (OptStageEnv
          (W4BinaryStageP4PathCWideEnv w.base.hasOpk w.base.rd w.base.files w.base.peer
            w.remoteIdKey w.base.kpkId w.base.spkId w.base.opkId w.baseKey
            w.base.G_out1 w.base.sess_out1 w.base.enc_prev1)))) evs

/-- 4-arm binary-kit W4 (`recv-prekey`) slot envelope
(`FreeOnlyEvs | Untrusted | PathBWide | PathAWide | PathCWide` + trailing `FreeOnlyEvs`). -/
def W4BinaryRecvPrekeyWideSlotEnv (w : W4BinaryRecvPrekeyParams)
    (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨
  SeqEnv
    (fun e =>
      W4BinaryStageP1UntrustedEnv w.base.rd w.base.files w.base.peer w.remoteIdKey e ∨
      W4BinaryRecvPrekeyPathBWideEnv w e ∨
      W4BinaryRecvPrekeyPathAWideEnv w e ∨
      W4BinaryRecvPrekeyPathCWideEnv w e)
    FreeOnlyEvs evs

/-! ## Whole-`run` and Whole-`main` Binary-Kit Callee and Trace Envelopes -/

/-- Mode-dispatched `CliRunCalleeEnvs` bundle at the true binary store-kit polls (`W3`, `W1`, `W2`,
and `W4`) plus `PksmCanonSliceEnv`. -/
def mkBinaryKitRealCalleeEnvs [LibsignalPlacement]
    (_img : Arm64.Obj.Image) (_S : RunSem) (_X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (g : RunCall) : CliRunCalleeEnvs where
  initEnv := match g.c with
    | .init _ _ => fun evs =>
      ∃ w : W3BinaryInitParams, W3BinaryInitDom g.c g.i w ∧ W3InitBinaryKitSlotEnv w evs
    | _ => fun _ => False
  encEnv := match g.c with
    | .send _ => fun evs =>
      ∃ w1R : W1BinarySendParams,
        W1BinarySendDom g.c g.i w1R ∧ W1SendBinaryKitSlotEnv ⟨W.C, W.Q⟩ w1R evs
    | _ => fun _ => False
  decSigEnv := match g.c with
    | .recv _ => fun evs =>
      ∃ w2R : W2BinaryWhisperParams,
        W2BinaryWhisperDom g.c g.i w2R ∧ W2RecvWhisperBinaryKitSlotEnv ⟨W.C, W.Q⟩ w2R evs
    | _ => fun _ => False
  pksmEnv := PksmCanonSliceEnv
  decPkEnv := match g.c with
    | .recv _ => fun evs =>
      ∃ w4 : W4BinaryRecvPrekeyParams,
        W4BinaryRecvPrekeyDom g.c g.i w4 ∧ W4BinaryRecvPrekeyWideSlotEnv w4 evs
    | _ => fun _ => False

/-- Whole-`signal_session::run` binary-kit allocator trace predicate on `g : RunCall`. -/
abbrev realCliRunBinaryKitEnvOf [LibsignalPlacement]
    (img : Arm64.Obj.Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (g : RunCall) : List AllocEvent → Prop :=
  CliRunBinaryEnv cliIo.rd (mkBinaryKitRealCalleeEnvs img S X W g) sessionCapBytes g

/-- Whole-`main` binary-kit allocator trace predicate on `i : Inputs`. -/
abbrev realCliMainBinaryKitEnvOf [LibsignalPlacement]
    (img : Arm64.Obj.Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (i : Inputs) : List AllocEvent → Prop :=
  RealCliMainBinaryEnvOf (mkBinaryKitRealCalleeEnvs img S X W) i

end LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
