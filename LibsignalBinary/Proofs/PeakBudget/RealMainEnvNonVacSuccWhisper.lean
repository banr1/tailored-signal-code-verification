/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Process.Semantics
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget
public import LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
public import LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith
public import LibsignalBinary.Proofs.PeakBudget.CliGroupBounds
public import LibsignalBinary.Proofs.PeakBudget.CliMainPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
public import LibsignalBinary.Proofs.PeakBudget.CliRunArmsPeak
public import LibsignalBinary.Proofs.PeakBudget.CliRunPeakHelpers
public import LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge
public import LibsignalBinary.Proofs.PeakBudget.DirPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.RealMainEnvAdapter
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit
public import LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit
public import LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedEnv
public import LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds
public import LibsignalBinary.Proofs.PeakBudget.W2DecryptPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.W2DecryptPhasePeak
public import LibsignalBinary.Proofs.PeakBudget.W2DecryptTrialPeak
public import LibsignalBinary.Proofs.PeakBudget.W2RecvWhisperRealSlot
public import LibsignalBinary.Proofs.PeakBudget.WireMsgPeakSpec
public import LibsignalBinary.Proofs.ProtoCodecRoundTrip
public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Defs
public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.SessionDeserializeBudget
public import LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget
public import LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.AddressText.PlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.CalleesBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R0ProofPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.TopPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.FilesOk
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ScopeIn
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPoll.LayoutPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser
public import LibsignalBinary.Proofs.SignalSession.NonVacuityPq
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget
public import LibsignalBinary.Specifications.CryptoGames.AEAD.HKDFDefs
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.CreateChainDefs
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSessionApi
public import LibsignalBinary.Specifications.LibsignalE2E.StateXModel
public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
public import LibsignalBinary.Specifications.SignalSession.PqDir
public import LibsignalBinary.Proofs.ConsumeMessageKey.NonVacProofs.StateWitness
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Plumbing
import ProofLib.VCGen

/-!
# `recvWhisper`-Arm Binary-Kit Success-Path Non-Vacuity Witness

Proves that the `recv` Whisper (`2#8`) CLI arm's binary-kit success path is inhabited in
`RealCliMainBinaryEnvOf (mkBinaryKitRealCalleeEnvs img S X W₀)` (`= realCliMainBinaryKitEnvOf img S X W₀`)
for all `img`, `S`, `X` at the concrete witness `W₀ = w0CliHooks` (`⟨W₀.C, W₀.Q⟩ = NonVacuityPq.W0`):
1. Defines `RecvWhisperSuccMainEnv` via strict `ConcatEnv` / `IterConcatEnv` composition across
   `M1..M3`, `R0BinarySuccEnv`, `SigTryFromOkEnv`, `W2LoadStepSuccEnv` (with Block 594 `address_text`
   on `Bob.1` and `.ok` cache-miss Block 589 `Dir::get` reads), `RecordDecryptSuccEnv`,
   `W2TrustStepSuccEnv`, `W2SaveStepSuccEnv`, `W2StoreStepSuccEnv`, `RecvWhisperM5SuccEnv`, and
   `RecvWhisperSuccM6Env`, tied to `decryptRecord = .ok (pt, rec')` and
   `pqRecvWhisperModel P₀ st rest rc = some (some (st₁, pt))`.
2. Proves `RecvWhisperSuccMainEnv img ⟨W.C, W.Q⟩ i₀ ⊆ realCliMainBinaryKitEnvOf img S X W i₀`.
3. Exhibits concrete `(W₀, i₀, evs)` satisfying `CliPqxdhInputs ⟨W₀.C, W₀.Q⟩ i₀` (file-read witnesses
   use the hook-model disjunct of `ReadFileEnv` / `ReadStdinEnv`, `M6` uses `CliWriteStdoutEnv`'s
   `alloc 1024` over-approximation disjunct, and bounded-cost inner stages carry functional success
   via `decryptRecord` and `pqRecvWhisperModel`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 8192

namespace LibsignalBinary.Proofs.PeakBudget.RealMainEnvNonVacSuccWhisper

open Arm64 ProofLib SepProp
open Arm64.Process (bytesOfString initFsState)
open CryptoGames (Party)
open CryptoGames.HKDF (bytesToKey32)
open CryptoGames.HMAC (hmacSha256Trunc8 hmacWith keyToBytes32 sha256IV sha256With toBEBytes)
open CryptoGames.LibsignalAead (addressCheckPasses)
open CryptoGames.LibsignalSession
  (ChainKey Crypto GhostState IdentityKey KeyPair MessageKeys Mut ProtoSignalMessage PublicKey
   RatchetState ReceiverChain SenderChain SessionState ShaCompress SignalMessage
   SignalProtocolError Spqr TripleRatchet aesCbcDecrypt aesCbcEncrypt computeMac currentVersion
   initializeInitiatorSession liftE macLength maxMessageKeys preKyberVersion serializeContent
   versionByte zoom)
open CryptoGames.LibsignalSessionApi
  (PendingKyberPreKey PendingPreKey Session SessionRecord)
open CryptoGames.Ratchet (chainHmac chainKeySeed clampScalar rootKdf)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.E2E
  (PEParams PreKeyBundleFields RecordExtras UnreachedPqxdhPrimitives blockLevelPrims
   encodeRecordUnderExtras fitVec initiateInput initiateKemCoins initiateState initiateTapeLen
   initiatorRecordExtras keyPairOf modelPrims ofU8 partyAddressName pqxdhSessionParams
   pqxdhSpqrModel pqxdhSpqrSession toU8 u32 u8Vec vecU8 wireWhisper)
open CryptoVerification.E2E.Record (encodeRecord lenField toRecord)
open CryptoVerification.E2E.Record.Serialization (encSessionMem)
open CryptoVerification.E2E.RecordX (encodeRecordX_eq_toRecord extrasOf)
open CryptoVerification.LibsignalProtoCodec
  (LengthsFit WireType encode encodeBytesField encodeKey encodeUint32Field encodeVarint
   encodeVarintAux protoSignalCodec protoSignalCodec_roundTrip)
open CryptoVerification.LibsignalPublicApi (DecryptGhost)
open CryptoVerification.LibsignalPublicApi.MessageDecrypt (decryptRecord recGhostOf sessionModelRel)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal KyberRel OptU32Rel PendingRel RecordGhost serializeAddrVals)
open CryptoVerification.LibsignalSession.NonVacuityWitness
  (A₀ bytesOf32 bytesOf64 pk0 pointsTo64_eq_pointsToBytes split_arena_region)
open CryptoVerification.LibsignalSessionRepr
  (VecGhost VecPin chainAt leBytes messageKeyAt optChainKeyAt vecGhostAt)
open CryptoVerification.LibsignalSpqrV1
  (Authenticator Chain ChainEpochDirection ChainPB ChainParams ChainResult Direction HkdfFn
   KeyHistory Message MlKem PqRatchetState PqRatchetStatePB SpqrApiDeps SpqrApiResult States
   V1Recv V1State Version VersionNegotiationPB chainFrom decodeState msgPreamble recv
   recvKeyToSalt? recvPanicsB recvPanicsSaltB spqrAuthApi spqrDeps spqrHkdfWith spqrPolyApi
   spqrV1 spqrV1_eq stateVersion toSpqrModel)
open CryptoVerification.LibsignalTripleRatchet (RecordDecryptGhost SpqrModel reserveCap)
open CryptoVerification.LibsignalTripleRatchet.Record (CloneRel)
open CryptoVerification.LibsignalTripleRatchetRepr
  (AddrGhost SenderChainGhost SessionGhost SignalMessageGhost TailVecGhost addrBytes coinsOf
   noneCap optSenderChainAt optTailVecAt serviceIdParse sessionStateAt uuidTryParse)
open CryptoVerification.RustHeap (RustAlloc arrayAt vecAt vecBuf vecHeader vecU8At)
open CryptoVerification.SignalSession
  (Address CliHooks CliPqxdhInputs Cmd Inputs PqParty PqxdhPartyInSpecDomain emptyParty encodeDir
   fileCapBytes partyAddress pqInitModel pqInputs pqRecvInputs pqRecvWhisperModel textBytes)
open CryptoVerification.SignalSession.Cli
  (DirGhost StoresGhost addressText cliInputs decimalText pathOf utf8)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddressCall AddrV CallV RunCall addrParse cliIo cliWrOk parseArgs)
open CryptoVerification.SignalSession.Cli.RunCompose
  (DecSigGhost RunSem SlotCtx addrValOf runFiles)
open CryptoVerification.SignalSession.Cli.RunProofs.DecryptLemmas (toDecryptGhost)
open CryptoVerification.SignalSession.Cli.RunRefine
  (addrParse_textBytes ownAddr_pqRecv parseArgs_recv)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots
  (partyAddr pqIdBytes pqIdGet_recv pqSessBytes pqSessBytes_le_fileCapBytes pqSessGet_recv
   scopeIn scopeKit scopeKit_of_scopeIn)
open CryptoVerification.SignalSession.CliExt (blockingAncestorF pathStr readFileResult readViewF)
open CryptoVerification.SignalSession.NonVacuityPq
  (C0 K0 Q0 W0 X0 b0 nzVec32 pqInitModel_W0_creates_wfSession t0)
open CryptoVerification.SpqrV1.ChainProofs
  (ChainAddEpochGhost ChainIntoPbCall ChainNewGhost ChainRecvKeyGhost)
open CryptoVerification.SpqrV1.States.IntoPb (StatesIntoPbGhost)
open CryptoVerification.SpqrV1.Top.InitInner (InitInnerGhost)
open LibsignalBinary.Heap
  (AllocEvent FreeOnlyEvs rustAllocEvents rustDeallocEvents rustReallocEvents)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rawVecGrowEvents)
open LibsignalBinary.Heap.SpecBudget
  (ReadFileEnv ReadStdinEnv allocBytes1Events cliIoCapsEvents cliIoReadScheduleCaps)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
  (addressText_length_le opened_peers_path_len opened_sess_path_len)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith
  (cliMaxAddrTextBytes cliMaxDirPathBytes cliMaxDirtyEntries)
open LibsignalBinary.Proofs.PeakBudget.CliGroupBounds (W2TryDecryptTightEnv)
open LibsignalBinary.Proofs.PeakBudget.CliMainPeakSpec
  (CliMainSetupEnv M2CollectStepEnv M5LoopAEntryEnv M5WriteStepEnv M6Env)
open LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
  (RecordSerializeSeqFreeValidEnv W2BinaryWhisperDom W2BinaryWhisperParams
   W2RecvWhisperBinaryKitSlotEnv decBinaryIdKitPlacedBudget decBinarySessKitPlacedBudget
   mkBinaryKitRealCalleeEnvs realCliMainBinaryKitEnvOf realCliRunBinaryKitEnvOf)
open LibsignalBinary.Proofs.PeakBudget.CliRunArmsPeak
  (JoinEnv SigTryFromSliceEnv)
open LibsignalBinary.Proofs.PeakBudget.CliRunPeakHelpers (deallocBytes1OfLen)
open LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge
  (CliRunBinaryEnv R0BinaryEnv RealCliMainBinaryEnvOf)
open LibsignalBinary.Proofs.PeakBudget.RealMainEnvAdapter
  (CliMainBoundedSetupEnv ValidPostSetupWitness cliMainBoundedSetupEnv_of_setup_any)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (ConcatEnv IterConcatEnv IterSeqEnv)
open LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit (dropClonedSessionEvents)
open LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit
  (RecordSerializeSeqFreeEnv SerializeSomeCancelEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (msgCapBytes sessionCapBytes)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedEnv
  (SpqrRecvC07C09aTightLinkedEnv spqrRecvC07TightLinkedEnv_nil_exists)
open LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpec (StatesRecvProtoEnv)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds (RecordGhostValid)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptPhasePeak
  (BoundedLenEvs BoundedNonFreeEvs)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptTrialPeak (s7CoreEvs)
open LibsignalBinary.Proofs.PeakBudget.W2RecvWhisperRealSlot
  (W2RealTdEnv peer_and_rem_name_le_40_of_recv)
open LibsignalBinary.Proofs.PeakBudget.WireMsgPeakSpec
  (IntoBoxedBoundedEnv IntoBoxedOptBoundedEnv SigTryFromCaps SigTryFromErrTailEnv
   SigTryFromLoopBoundedEnv SigTryFromPostEnv SigTryFromPostOkAllocEnv SigTryFromPostOutPreEnv
   TryCloneBytesEnv intoBoxedCapEvents)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget
  (FromKeyReadyEnv FromLoadPolledEnv FromPostSomeEnv FromRegionSomeEnv FromStoreCallEnv
   FromTrustedTrueEnv LoadPollStepEnv SessionGhostValid)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (SaveStepEnv TrustStepEnv)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.SessionDeserializeBudget
  (sessDeserEvents)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget (RecordDeserializeCancelEnv)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux
  (sessDeserEvents_mem_recordDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.AddressText.PlacedBudgetAux
  (addrDecReserveEvents addrDotReserveEvents addrToOwnedEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget
  (DecimalEnv decimalEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a
  (DirGetAfterReadEnv DirGetEnv DirGetErrAllocEnv DirGetMissEnv DirGetPathEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget
  (PathEnv pathEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux
  (DirPutEnv DirPutTailEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux (DirPutStrEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
  (cliIdentityKitSavePollEnv cliIdentityKitSaveTailEnv cliIdentityKitTrustPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
  (AddrTextValEnv cliSessionKitLoadPollEnv cliSessionKitStorePollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.CalleesBudget (AddressEnv addressEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R0ProofPlacedBudget (PreAfterGetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget
  (decIdKitPlaced decSessKitPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (ReadFileRuleEnv readFileRuleEnv_eq_readFileEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPoll.LayoutPlacedBudget (OptLoadDeserEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser (ofBytesEnv)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (PublicKeySerializeEnv publicKeySerializeEvents)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget
  (RecordDecryptEnv SegCloneEnv TryDecryptEnvArgs recordTryDecryptEnvArgs segCloneEvents)

/-! ## 1. `RecvWhisperSucc*` Sub-Envelopes -/

/-- `ReadFileRuleEnv` / `ReadFileEnv` pinned to `.ok bs` with `bs.length ≤ 2097152`. -/
def ReadFileOkEnv (rd : CryptoVerification.SignalSession.Cli.ReadRule) (files : FsFiles)
    (path : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  ∃ bs : List (BitVec 8),
    rd files path = .ok bs ∧
    bs.length ≤ 2097152 ∧
    (evs = allocBytes1Events bs ∨
      evs = cliIoCapsEvents 0 (cliIoReadScheduleCaps 9 bs.length))

/-- `ReadStdinEnv` pinned to `bs.length ≤ 1048576` (excluding over-cap `1048576 < bs.length`). -/
def ReadStdinSuccEnv (bs : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  bs.length ≤ 1048576 ∧
  (evs = allocBytes1Events bs ∨
    evs = cliIoCapsEvents 0 (cliIoReadScheduleCaps 8 bs.length))

/-- `M2CollectEnv` with `IterConcatEnv` at every step. -/
def M2CollectSuccEnv (argvLen : Nat) (evs : List AllocEvent) : Prop :=
  IterConcatEnv M2CollectStepEnv (List.range argvLen) evs

/-- `CliMainSetupEnv uuidTryParse i₀ addrOpt true` with `ConcatEnv` / `IterConcatEnv` at every seam,
`M1` pinned to `rustAllocEvents (16 * i₀.argv.length) 8`, and `ReadFileOkEnv` pinning `"coins"`. -/
def CliMainSetupSuccEnv (i₀ : Inputs) (addrOpt : Option AddressCall)
    (evs : List AllocEvent) : Prop :=
  ConcatEnv (· = rustAllocEvents (16 * i₀.argv.length) 8)
    (ConcatEnv (M2CollectSuccEnv i₀.argv.length)
      (ConcatEnv
        (match addrOpt with
         | none => (· = [])
         | some ag => AddressEnv uuidTryParse ag)
        (ConcatEnv (ReadStdinSuccEnv i₀.stdin)
          (ConcatEnv
            (ReadFileOkEnv readFileResult (initFsState (cliInputs i₀)).files (utf8 "coins"))
            FreeOnlyEvs))))
    evs

/-- Binary Block `594` `address_text(&ProtocolAddress)` success envelope with `ConcatEnv` across
`addrToOwnedEvents`, `addrDotReserveEvents`, `DecimalEnv`, `addrDecReserveEvents`, and `FreeOnlyEvs`. -/
def AddrTextValSuccEnv (rem : AddrVal) (evs : List AllocEvent) : Prop :=
  ConcatEnv (· = addrToOwnedEvents rem.name)
    (ConcatEnv (· = addrDotReserveEvents rem.name)
      (ConcatEnv (DecimalEnv (rem.device.zeroExtend 32))
        (ConcatEnv (· = addrDecReserveEvents rem.name rem.device) FreeOnlyEvs)))
    evs

/-- Binary Block `589` `Dir::get` cache-miss `.ok bs` envelope: `d.changed = []`,
`cliIo.rd F0 (pathOf d.path name) = .ok bs` (`DirGetErrAllocEnv` reduces to `(· = [])`), and
`ConcatEnv` at every seam. -/
def DirGetCacheMissOkBinEnv (F0 : FsFiles) (d : DirGhost) (name : List (BitVec 8))
    (evs : List AllocEvent) : Prop :=
  d.changed = [] ∧
  ∃ bs : List (BitVec 8),
    cliIo.rd F0 (pathOf d.path name) = .ok bs ∧
    bs.length ≤ 2097152 ∧
    ConcatEnv (DirGetPathEnv PathEnv d.path name)
      (ConcatEnv (ReadFileOkEnv cliIo.rd F0 (pathOf d.path name))
        (ConcatEnv (· = []) FreeOnlyEvs))
      evs

/-- Binary Arm `R0` (`R0BinaryEnv cliIo.rd g` `Or.inr`) pinned to `.ok ownB` and
`addrParse uuidTryParse ownB = some ownAddr` (`ConcatEnv` throughout). -/
def R0BinarySuccEnv (g : RunCall) (evs : List AllocEvent) : Prop :=
  ∃ (ownB : List (BitVec 8)) (ownAddr : AddrV),
    StoresGhost.opened.identity.own.get cliIo.rd (runFiles g.i) (utf8 "address") = .ok ownB ∧
    addrParse uuidTryParse ownB = some ownAddr ∧
    ConcatEnv (DirGetCacheMissOkBinEnv (runFiles g.i) StoresGhost.opened.identity.own (utf8 "address"))
      (ConcatEnv (· = rustAllocEvents ownAddr.name.length 1) FreeOnlyEvs)
      evs

/-- `SigTryFromSliceEnv rest` pinned to `.ok msg` (`ConcatEnv` throughout). -/
def SigTryFromOkEnv (rest : List (BitVec 8)) (msg : SignalMessage)
    (evs : List AllocEvent) : Prop :=
  SignalMessage.tryFrom protoSignalCodec rest = .ok msg ∧
  ConcatEnv (SigTryFromLoopBoundedEnv rest.length SigTryFromCaps.zero)
    (ConcatEnv
      (ConcatEnv FreeOnlyEvs
        (ConcatEnv (IntoBoxedBoundedEnv msg.ciphertext)
          (ConcatEnv (IntoBoxedOptBoundedEnv msg.addresses)
            (TryCloneBytesEnv msg.serialized))))
      FreeOnlyEvs)
    evs

/-- Binary `load_session` step + `loadBox` dealloc (`W2LoadStepSuccEnv` on `W2BinaryWhisperParams`,
using `AddrTextValSuccEnv` and `DirGetCacheMissOkBinEnv`). -/
def W2LoadStepSuccEnv [LibsignalPlacement]
    (w2R : W2BinaryWhisperParams)
    (rec : SessionRecord (List (BitVec 8))) (evs : List AllocEvent) : Prop :=
  let kit := decSessKitPlaced w2R.repAlloc w2R.x.F w2R.x.peer w2R.B
  let dir := StoresGhost.opened.sessions
  let rem := (toDecryptGhost w2R.x).rem.val
  let name := addressText rem
  ∃ (b0 : BitVec 8) (bsRest : List (BitVec 8)),
    dir.get cliIo.rd w2R.x.F name = .ok (b0 :: bsRest) ∧
    encodeRecord rec = b0 :: bsRest ∧
    scopeKit rec ∧
    ConcatEnv
      (ConcatEnv (· = rustAllocEvents kit.loadBoxSize 8)
        (ConcatEnv (AddrTextValSuccEnv rem)
          (ConcatEnv (DirGetCacheMissOkBinEnv w2R.x.F dir name)
            (ConcatEnv (· = sessDeserEvents rec) FreeOnlyEvs))))
      (· = rustDeallocEvents kit.loadBoxSize 8)
      evs

/-- Pre-decrypt setup and session-load segment (`pre` in `pre ++ dec ++ store ++ M6`). -/
def RecvWhisperSuccPreEnv [LibsignalPlacement]
    (g : RunCall) (addrOpt : Option AddressCall) (rest : List (BitVec 8))
    (msg : SignalMessage) (w2R : W2BinaryWhisperParams)
    (rec : SessionRecord (List (BitVec 8))) (evsPre : List AllocEvent) : Prop :=
  ConcatEnv (CliMainSetupSuccEnv g.i addrOpt)
    (ConcatEnv (R0BinarySuccEnv g)
      (ConcatEnv (SigTryFromOkEnv rest msg)
        (W2LoadStepSuccEnv w2R rec)))
    evsPre

/-- `W2RealTdEnv` specialized to the existing-chain `0`-jump success path (`S3 = []`, `S4 = []`,
`S7` `errAlloc = false`, `S8` plaintext allocation, `ConcatEnv` throughout). -/
def W2RealTdSuccEnv (F : ShaCompress) (K : MlKem)
    (a : TryDecryptEnvArgs) (evs : List AllocEvent) : Prop :=
  ∃ (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall),
    ConcatEnv (BoundedNonFreeEvs 6 16 160)
      (ConcatEnv (· = [])
        (ConcatEnv (· = [])
          (ConcatEnv (SpqrRecvC07C09aTightLinkedEnv F K a.st.pqRatchetState
            pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
            (ConcatEnv (ConcatEnv (· = s7CoreEvs true false) FreeOnlyEvs)
              (ConcatEnv (· = rustAllocEvents a.msg.ciphertext.length 1)
                (ConcatEnv
                  (ConcatEnv FreeOnlyEvs (ConcatEnv (BoundedLenEvs 6 34) FreeOnlyEvs))
                  FreeOnlyEvs))))))
      evs

/-- Record-decryption segment (`dec` in `pre ++ dec ++ store ++ M6`). -/
def RecordDecryptSuccEnv (F : ShaCompress) (K : MlKem)
    (x : RecordDecryptGhost) (evsDec : List AllocEvent) : Prop :=
  x.st.version.toNat = x.msg.messageVersion.toNat ∧
  ∃ G₁ : SessionGhost, CloneRel x.G G₁ ∧
    ConcatEnv (SegCloneEnv x.G x.st)
      (ConcatEnv (W2RealTdSuccEnv F K (recordTryDecryptEnvArgs x G₁)) FreeOnlyEvs)
      evsDec

/-- Binary `is_trusted_identity` step (`DirGetCacheMissOkBinEnv` + `ConcatEnv`). -/
def W2TrustStepSuccEnv [LibsignalPlacement]
    (w2R : W2BinaryWhisperParams) (evs : List AllocEvent) : Prop :=
  let ikit := decIdKitPlaced w2R.repAlloc w2R.x.F w2R.x.peer w2R.B
  let ist0 := StoresGhost.opened.identity
  let rem := (toDecryptGhost w2R.x).rem.val
  ConcatEnv (· = rustAllocEvents ikit.trustBoxSize 8)
    (ConcatEnv
      (ConcatEnv (DirGetCacheMissOkBinEnv w2R.x.F ist0.peers rem.name) FreeOnlyEvs)
      (· = rustDeallocEvents ikit.trustBoxSize 8))
    evs

/-- Binary `save_identity` step (`DirGetCacheMissOkBinEnv`, `PublicKeySerializeEnv`, and
`DirPutStrEnv` cold-`Vec` `grow_one` path with `ConcatEnv`). -/
def W2SaveStepSuccEnv [LibsignalPlacement]
    (w2R : W2BinaryWhisperParams) (k : IdentityKey) (evs : List AllocEvent) : Prop :=
  let ikit := decIdKitPlaced w2R.repAlloc w2R.x.F w2R.x.peer w2R.B
  let rem := (toDecryptGhost w2R.x).rem.val
  let ist1 := ikit.trustUpdate StoresGhost.opened.identity rem k .receiving (.ok true)
  rem.name ≠ [] ∧
  ist1.peers.changed = [] ∧
  (∃ bs : List (BitVec 8), ist1.peers.get cliIo.rd w2R.x.F rem.name = .ok bs) ∧
  ConcatEnv (· = rustAllocEvents ikit.saveBoxSize 8)
    (ConcatEnv
      (ConcatEnv (DirGetCacheMissOkBinEnv w2R.x.F ist1.peers rem.name)
        (ConcatEnv FreeOnlyEvs
          (ConcatEnv PublicKeySerializeEnv
            (ConcatEnv (· = rustAllocEvents rem.name.length 1)
              (· = rawVecGrowEvents 48 4 8 0#64)))))
      (· = rustDeallocEvents ikit.saveBoxSize 8))
    evs

/-- Binary `store_session` step (`AddrTextValSuccEnv`, `SerializeSomeCancelEnv`, and cold-`Vec`
`DirPutEnv` `rawVecGrowEvents 48 4 8 0#64` with `ConcatEnv`). -/
def W2StoreStepSuccEnv [LibsignalPlacement]
    (w2R : W2BinaryWhisperParams)
    (rec' : SessionRecord (List (BitVec 8))) (ses' : Session (List (BitVec 8)))
    (G' : SessionGhost) (evs : List AllocEvent) : Prop :=
  let kit := decSessKitPlaced w2R.repAlloc w2R.x.F w2R.x.peer w2R.B
  let rem := (toDecryptGhost w2R.x).rem.val
  rec'.currentSession = some ses' ∧
  SessionGhostValid G' ses' ∧
  FreeOnlyEvs (dropClonedSessionEvents G' ses'.state) ∧
  ∃ evsPoll : List AllocEvent,
    ConcatEnv (AddrTextValSuccEnv rem)
      (ConcatEnv (SerializeSomeCancelEnv G' ses')
        (· = rawVecGrowEvents 48 4 8 0#64))
      evsPoll ∧
    ConcatEnv
      (ConcatEnv (· = rustAllocEvents kit.storeBoxSize 8)
        (ConcatEnv (· = evsPoll) (· = rustDeallocEvents kit.storeBoxSize 8)))
      FreeOnlyEvs
      evs

/-- `M5` commit loop with `ConcatEnv` + `IterConcatEnv` on the pinned 2-directory dirty list
`[("identities", [peer.name]), ("sessions", [addressText rem])]`. -/
def RecvWhisperM5SuccEnv (w2R : W2BinaryWhisperParams) (evs : List AllocEvent) : Prop :=
  let dirs : List (List (BitVec 8) × List (List (BitVec 8))) :=
    [(utf8 "identities", [w2R.peer.name.bytes]),
     (utf8 "sessions", [addressText (toDecryptGhost w2R.x).rem.val])]
  ConcatEnv
    (IterConcatEnv
      (fun dn => ConcatEnv (IterConcatEnv (fun nm => M5WriteStepEnv (dn.1, nm)) dn.2) FreeOnlyEvs)
      dirs)
    FreeOnlyEvs
    evs

/-- Identity/session store and `M5` commit segment (`store` in `pre ++ dec ++ store ++ M6`). -/
def RecvWhisperSuccStoreEnv [LibsignalPlacement]
    (w2R : W2BinaryWhisperParams)
    (rec' : SessionRecord (List (BitVec 8))) (ses' : Session (List (BitVec 8)))
    (G' : SessionGhost) (k : IdentityKey) (evsStore : List AllocEvent) : Prop :=
  ConcatEnv (W2TrustStepSuccEnv w2R)
    (ConcatEnv (W2SaveStepSuccEnv w2R k)
      (ConcatEnv (W2StoreStepSuccEnv w2R rec' ses' G')
        (ConcatEnv FreeOnlyEvs
          (ConcatEnv JoinEnv (RecvWhisperM5SuccEnv w2R)))))
    evsStore

/-- `M6` stdout-write segment (`M6` in `pre ++ dec ++ store ++ M6`). -/
def RecvWhisperSuccM6Env (evsM6 : List AllocEvent) : Prop :=
  M6Env true evsM6 ∧
  ConcatEnv (· = rustAllocEvents 1024 1) FreeOnlyEvs evsM6

/-- Whole-`main` `recvWhisper` binary-kit success sub-envelope. -/
def RecvWhisperSuccMainEnv [LibsignalPlacement]
    (_img : Arm64.Obj.Image) (P₀ : PEParams) (i₀ : Inputs) (evs : List AllocEvent) : Prop :=
  ∃ (st st₁ : PqParty) (rc : BitVec 256)
    (g : RunCall) (peerAddr : AddrV) (rest : List (BitVec 8))
    (msg : SignalMessage) (ag : AddressCall)
    (w2R : W2BinaryWhisperParams)
    (rec rec' : SessionRecord (List (BitVec 8)))
    (ses ses' : Session (List (BitVec 8)))
    (G G' : SessionGhost) (pt : List (BitVec 8)) (k : IdentityKey)
    (evsPre evsDec evsStore evsM6 : List AllocEvent),
    let kit := decSessKitPlaced w2R.repAlloc w2R.x.F w2R.x.peer w2R.B
    let dx := toDecryptGhost w2R.x
    evs = evsPre ++ evsDec ++ evsStore ++ evsM6 ∧
    PqxdhPartyInSpecDomain P₀ st ∧
    i₀ = pqRecvInputs P₀ st (wireWhisper :: rest) rc ∧
    pqRecvWhisperModel P₀ st rest rc = some (some (st₁, pt)) ∧
    (∃ x' g', st₁.session = some (x', g') ∧ g'.session = ses'.state) ∧
    g.i = i₀ ∧
    g.c = .recv peerAddr ∧
    parseArgs uuidTryParse (i₀.argv.map bytesOfString) = some (.recv peerAddr) ∧
    i₀.argv.map bytesOfString = [utf8 "recv", ag.bs] ∧
    addrParse uuidTryParse ag.bs = some peerAddr ∧
    i₀.stdin = wireWhisper :: rest ∧
    i₀.stdin.length ≤ msgCapBytes ∧
    dx.msg = msg ∧
    coinsOf dx.rest = rc ∧
    dx.loc.val = partyAddr st.party ∧
    W2BinaryWhisperDom (.recv peerAddr) i₀ w2R ∧
    kit.ScopeAt scopeKit StoresGhost.opened.sessions dx.rem.val rec ∧
    rec.currentSession = some ses ∧
    SessionGhostValid G ses ∧
    decryptRecord P₀.C (spqrV1 P₀.C.F P₀.Q.K) uuidTryParse dx rec = .ok (pt, rec') ∧
    rec'.currentSession = some ses' ∧
    ses'.state.remoteIdentity = some k ∧
    RecvWhisperSuccPreEnv g (some ag) rest msg w2R rec evsPre ∧
    RecordDecryptSuccEnv P₀.C.F P₀.Q.K (recGhostOf dx 0#64 G ses.state) evsDec ∧
    RecvWhisperSuccStoreEnv w2R rec' ses' G' k evsStore ∧
    RecvWhisperSuccM6Env evsM6

/-! ## 2. Concrete `W0` Session, SPQR V1 `recv`, `pqRecvWhisperModel` & `decryptRecord = .ok` Witnesses -/

private theorem ofU8_toU8 : ∀ (bs : List (BitVec 8)), ofU8 (toU8 bs) = bs
  | [] => rfl
  | _ :: xs => congrArg (_ :: ·) (ofU8_toU8 xs)

private theorem u8Vec_vecU8 {n : Nat} (v : List.Vector (BitVec 8) n) : u8Vec n (vecU8 v) = v := by
  apply List.Vector.eq
  rcases v with ⟨l, hl⟩
  dsimp only [u8Vec, vecU8]
  rw [ofU8_toU8]
  simp [fitVec, List.Vector.toList, hl]

private theorem vecU8_length {n : Nat} (v : List.Vector (BitVec 8) n) : (vecU8 v).length = n := by
  rcases v with ⟨l, hl⟩
  simpa [vecU8, toU8] using hl

private abbrev w0B1 : SignalPqxdh.Primitives :=
  { blockLevelPrims X0 W0 with sha512 := SignalPqxdh.sha512Ref (blockLevelPrims X0 W0) }

private theorem sha256Step_w0B1 (blk : List UInt8) :
    SignalPqxdh.sha256Step w0B1 SignalPqxdh.sha256InitState blk =
      SignalPqxdh.sha256InitState := by
  dsimp only [SignalPqxdh.sha256Step, w0B1, blockLevelPrims, W0, C0]
  rfl

private theorem foldl_sha256Step_w0B1 (blocks : List (List UInt8)) :
    blocks.foldl (SignalPqxdh.sha256Step w0B1) SignalPqxdh.sha256InitState =
      SignalPqxdh.sha256InitState := by
  induction blocks with
  | nil => rfl
  | cons blk tl ih =>
    simp only [List.foldl_cons, sha256Step_w0B1]
    exact ih

private theorem sha256Ref_w0B1 (msg : List UInt8) :
    SignalPqxdh.sha256Ref w0B1 msg = SignalPqxdh.sha256InitState := by
  dsimp only [SignalPqxdh.sha256Ref]
  rw [foldl_sha256Step_w0B1]
  rfl

private theorem hmacSha256Ref_w0B1 (k msg : List UInt8) :
    SignalPqxdh.hmacSha256Ref w0B1 k msg = SignalPqxdh.sha256InitState := by
  dsimp only [SignalPqxdh.hmacSha256Ref]
  simp only [sha256Ref_w0B1]

private def w0Dk : SignalPqxdh.DRKey :=
  { rootKey := SignalPqxdh.sha256InitState
    chainKey := SignalPqxdh.sha256InitState
    pqrKey := SignalPqxdh.sha256InitState }

private theorem hkdfDerive96_w0 (secrets : List UInt8) :
    (modelPrims X0 W0).hkdfDerive96 secrets = w0Dk := by
  dsimp only [modelPrims, SignalPqxdh.hkdfDerive96Ref, SignalPqxdh.hkdfExtractRef,
    SignalPqxdh.hkdfExpand96Ref]
  simp only [hmacSha256Ref_w0B1]
  rfl

private theorem sigVerify_w0_zero64 (ikPk msg : List UInt8) (hik : ikPk.length = 32) :
    (modelPrims X0 W0).sigVerify ikPk msg
      (vecU8 (List.Vector.replicate 64 0#8)) = true := by
  have hsig : vecU8 (List.Vector.replicate 64 0#8) = List.replicate 64 0 := rfl
  dsimp only [modelPrims]
  rw [hsig]
  unfold SignalPqxdh.xeddsaVerifyRef
  simp only [hik, List.length_replicate, beq_self_eq_true, Bool.true_and,
    blockLevelPrims, W0, Q0, fitVec]
  rfl

private theorem sha256With_C0 (m : List (BitVec 8)) :
    sha256With C0.F m = sha256IV.toList.flatMap (toBEBytes 4) := by
  unfold sha256With
  have hfold : ∀ (blks : List (List (BitVec 8))),
      blks.foldl C0.F sha256IV = sha256IV := by
    intro blks
    induction blks with
    | nil => rfl
    | cons _ tl ih => exact ih
  rw [hfold]

private theorem computeMac_C0_len (sId rId : IdentityKey) (macKey : BitVec 256)
    (content : List (BitVec 8)) :
    (computeMac C0.F sId rId macKey content).length = macLength := by
  unfold computeMac hmacSha256Trunc8 hmacWith
  simp only [sha256With_C0]
  rfl

private theorem publicKey_deserialize_serialize (rk : PublicKey) :
    PublicKey.deserialize rk.serialize = .ok rk := by
  rcases rk with ⟨⟨l, hl⟩⟩
  unfold PublicKey.deserialize PublicKey.serialize
  dsimp only [List.head?, List.tail, List.Vector.toList]
  have hlen : 32 ≤ l.length := Nat.le_of_eq hl.symm
  simp only [ne_eq, not_true_eq_false, ↓reduceIte, hlen, ↓reduceDIte]
  apply congrArg Except.ok
  apply congrArg PublicKey.mk
  apply Subtype.ext
  exact List.take_of_length_le (Nat.le_of_eq hl)

private theorem tryFrom_protoSignalCodec_new_C0
    (macKey : BitVec 256) (addrs : Option (List (BitVec 8))) (rk : PublicKey)
    (ctr prev : BitVec 32) (ct : List (BitVec 8)) (sId rId : IdentityKey) (pq : List (BitVec 8))
    (hct : ct.length < 2 ^ 64) (hpq : pq.length < 2 ^ 64)
    (haddrs : ∀ a, addrs = some a → a.length < 2 ^ 64) :
    SignalMessage.tryFrom protoSignalCodec
      (SignalMessage.new C0.F protoSignalCodec currentVersion macKey addrs rk ctr prev ct
        sId rId pq).serialized =
    .ok (SignalMessage.new C0.F protoSignalCodec currentVersion macKey addrs rk ctr prev ct
        sId rId pq) := by
  let pm : ProtoSignalMessage :=
    { ratchetKey := some rk.serialize
      counter := some ctr
      previousCounter := some prev
      ciphertext := some ct
      pqRatchet := if pq.isEmpty then none else some pq
      addresses := addrs }
  let body := protoSignalCodec.encode pm
  let content := versionByte currentVersion :: body
  let mac := computeMac C0.F sId rId macKey content
  have hmacLen : mac.length = macLength := computeMac_C0_len sId rId macKey content
  have hser : (SignalMessage.new C0.F protoSignalCodec currentVersion macKey addrs rk ctr
      prev ct sId rId pq).serialized = content ++ mac := rfl
  have hlen : ¬ ((content ++ mac).length < macLength + 1) := by
    simp only [List.length_append, content, List.length_cons, hmacLen, macLength]
    omega
  have htake : (content ++ mac).take ((content ++ mac).length - macLength) = content := by
    rw [List.length_append, hmacLen, Nat.add_sub_cancel]
    exact List.take_left
  have hfit : LengthsFit pm := by
    intro v hv
    rcases hv with hrk | hct' | hpq' | haddr'
    · cases hrk
      rcases rk with ⟨⟨l, hl⟩⟩
      simp [PublicKey.serialize, hl]
    · cases hct'; exact hct
    · by_cases he : pq.isEmpty
      · simp [pm, he] at hpq'
      · simp [pm, he] at hpq'; subst hpq'; exact hpq
    · exact haddrs v haddr'
  have hdec : protoSignalCodec.decode body = some pm :=
    protoSignalCodec_roundTrip pm hfit
  have hpqGet : (if pq.isEmpty then none else some pq).getD [] = pq := by
    cases pq <;> rfl
  have hhead : (content ++ mac).headD 0 = versionByte currentVersion := by
    simp [content]
  have hdrop1 : content.drop 1 = body := rfl
  unfold SignalMessage.tryFrom
  rw [hser]
  dsimp only
  simp only [hlen, ↓reduceIte, htake, hdrop1, hhead,
    show versionByte currentVersion >>> 4 = currentVersion from rfl,
    show ¬ (currentVersion < preKyberVersion) by simp [currentVersion, preKyberVersion],
    show ¬ (currentVersion < currentVersion) by simp,
    bind, Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [hdec]
  dsimp only [pm]
  rw [publicKey_deserialize_serialize, hpqGet]
  rfl

private theorem verifyMacWithAddresses_new_C0
    (macKey : BitVec 256) (addrs expected : Option (List (BitVec 8))) (rk : PublicKey)
    (ctr prev : BitVec 32) (ct : List (BitVec 8)) (sId rId : IdentityKey) (pq : List (BitVec 8))
    (had : addressCheckPasses addrs expected = true) :
    (SignalMessage.new C0.F protoSignalCodec currentVersion macKey addrs rk ctr prev ct
      sId rId pq).verifyMacWithAddresses C0.F expected sId rId macKey = true := by
  unfold SignalMessage.verifyMacWithAddresses SignalMessage.verifyMac
  let content := serializeContent protoSignalCodec currentVersion rk ctr prev ct pq addrs
  let mac := computeMac C0.F sId rId macKey content
  have hmacLen : mac.length = macLength := computeMac_C0_len sId rId macKey content
  have hser : (SignalMessage.new C0.F protoSignalCodec currentVersion macKey addrs rk ctr
      prev ct sId rId pq).serialized = content ++ mac := rfl
  have hadEq : (SignalMessage.new C0.F protoSignalCodec currentVersion macKey addrs rk ctr
      prev ct sId rId pq).addresses = addrs := rfl
  rw [hser, hadEq]
  have htake : (content ++ mac).take ((content ++ mac).length - macLength) = content := by
    rw [List.length_append, hmacLen, Nat.add_sub_cancel]
    exact List.take_left
  have hdrop : (content ++ mac).drop ((content ++ mac).length - macLength) = mac := by
    rw [List.length_append, hmacLen, Nat.add_sub_cancel]
    exact List.drop_left
  rw [htake, hdrop]
  simp only [mac, beq_self_eq_true, had, Bool.and_self]

def w0Vec1568 : List.Vector (BitVec 8) 1568 :=
  List.Vector.replicate 1568 0#8

private theorem w0Vec1568_eq : List.Vector.replicate 1568 0#8 = w0Vec1568 := by
  unfold w0Vec1568; rfl

attribute [local irreducible] w0Vec1568

def w0IdA : KeyPair := keyPairOf C0 emptyParty.me.idPriv
def w0BaseA : KeyPair := keyPairOf C0 (List.Vector.replicate 32 0#8)
def w0EphA : KeyPair := KeyPair.generate C0 (bytesToKey32 (List.replicate 32 0#8))
def w0Key0 : BitVec 256 := bytesToKey32 (ofU8 SignalPqxdh.sha256InitState)
def w0PqA0 : List (BitVec 8) := (pqxdhSpqrSession W0).init .a2b w0Key0

def w0SA0 : SessionState (List (BitVec 8)) :=
  (((SessionState.new currentVersion ⟨w0IdA.publicKey⟩ ⟨⟨b0.idPub⟩⟩
      (rootKdf C0.F w0Key0 nzVec32.toList).1 w0PqA0).addReceiverChain
      ⟨b0.spkPub⟩ ⟨w0Key0, 0#32⟩).setSenderChain
    w0EphA ⟨(rootKdf C0.F w0Key0 nzVec32.toList).2, 0#32⟩).setUnacknowledgedPreKeyMessage

def w0XA : RecordExtras :=
  initiatorRecordExtras emptyParty.me b0 w0BaseA.publicKey w0Vec1568

theorem w0_initiateState_eq :
    initiateState X0 W0 .A emptyParty.me b0 t0 =
      some (w0XA, ⟨.A, w0SA0, 0, [0]⟩) := by
  have hikB : (vecU8 b0.idPub).length = 32 := vecU8_length _
  have hsig1 := sigVerify_w0_zero64 (vecU8 b0.idPub)
    (SignalPqxdh.encodeEC (vecU8 b0.spkPub)) hikB
  have hsig2 := sigVerify_w0_zero64 (vecU8 b0.idPub)
    (SignalPqxdh.encodeKEM (vecU8 w0Vec1568)) hikB
  have hkem : (modelPrims X0 W0).kemEncaps (vecU8 w0Vec1568)
      (vecU8 (initiateKemCoins t0)) =
      some (vecU8 (List.Vector.replicate 32 0#8), vecU8 w0Vec1568) := by
    dsimp only [modelPrims, blockLevelPrims, SignalPqxdh.kyberPkLen, W0, Q0]
    have hpkLen : ((vecU8 w0Vec1568).length == 1568) = true := by
      rw [vecU8_length]; rfl
    simp only [hpkLen, ↓reduceIte]
    rw [w0Vec1568_eq]
  have hxBne : ∀ a b, ((modelPrims X0 W0).x25519 a b != List.replicate 32 0) = true :=
    fun _ _ => rfl
  have hbase : (modelPrims X0 W0).x25519Base (toU8 (t0.toList.take 32)) =
      vecU8 w0BaseA.publicKey.bytes := rfl
  have hinp : initiateInput W0 emptyParty.me b0 t0 =
      { ikASk := vecU8 w0IdA.privateKey.bytes
        ikAPk := vecU8 w0IdA.publicKey.bytes
        ekASk := toU8 (t0.toList.take 32)
        kemCoins := vecU8 (initiateKemCoins t0)
        trustedPeer := true
        bundle :=
          { ikB := vecU8 b0.idPub
            spkId := u32 0#32
            spkB := vecU8 b0.spkPub
            spkSig := vecU8 (List.Vector.replicate 64 0#8)
            opkB? := none
            pqspkId := u32 0#32
            pqspkB := vecU8 w0Vec1568
            pqspkSig := vecU8 (List.Vector.replicate 64 0#8) } } := by
    dsimp only [initiateInput, b0, w0IdA]
    rw [w0Vec1568_eq]
    rfl
  unfold initiateState
  rw [hinp]
  unfold SignalPqxdh.Model.initiateKeys
  simp only [«guard», bind, Bind.bind, Option.bind, Pure.pure, Option.map, ↓reduceIte,
    hsig1, hsig2, hkem, hxBne, SignalPqxdh.dhOptNonZero, hkdfDerive96_w0, hbase]
  have hcoinsA : (t0.toList.drop 160).take 32 = List.replicate 32 0#8 := rfl
  rw [hcoinsA]
  have hinitSess :
      initializeInitiatorSession C0 (pqxdhSpqrSession W0)
        ⟨(keyPairOf C0 emptyParty.me.idPriv).publicKey⟩ ⟨⟨b0.idPub⟩⟩ ⟨b0.spkPub⟩
        w0Key0 w0Key0 w0Key0 (bytesToKey32 (List.replicate 32 0#8)) =
      .ok (((SessionState.new currentVersion ⟨w0IdA.publicKey⟩ ⟨⟨b0.idPub⟩⟩
          (rootKdf C0.F w0Key0 nzVec32.toList).1 w0PqA0).addReceiverChain
          ⟨b0.spkPub⟩ ⟨w0Key0, 0#32⟩).setSenderChain
        w0EphA ⟨(rootKdf C0.F w0Key0 nzVec32.toList).2, 0#32⟩) := rfl
  change (match initializeInitiatorSession C0 (pqxdhSpqrSession W0)
      ⟨(keyPairOf C0 emptyParty.me.idPriv).publicKey⟩ ⟨⟨b0.idPub⟩⟩ ⟨b0.spkPub⟩
      w0Key0 w0Key0 w0Key0 (bytesToKey32 (List.replicate 32 0#8)) with
    | .error _ => none
    | .ok st => _) = _
  rw [hinitSess]
  dsimp only
  rw [u8Vec_vecU8, u8Vec_vecU8]
  rfl

def w0PqMsg : List (BitVec 8) := [1#8, 1#8, 1#8, 0#8]

def stepCedNext (hkdf : HkdfFn) (ced : ChainEpochDirection) :
    ChainEpochDirection × List (BitVec 8) :=
  match ced.nextKey hkdf with
  | .ok (ced', (_, out)) => (ced', out)
  | .error _ => (default, [])

private theorem ced_key_zero_one (hkdf : HkdfFn)
    (nextBytes : List (BitVec 8)) (hnext : nextBytes.length = 32) :
    ChainEpochDirection.key hkdf
      { ctr := 0#32, next := nextBytes, prev := { data := [] } } 1#32
      ChainParams.default.intoPb =
    .ok (stepCedNext hkdf { ctr := 0#32, next := nextBytes, prev := { data := [] } }) := by
  have hadv : ChainEpochDirection.keyAdvanceLoop hkdf
      { ctr := 0#32, next := nextBytes, prev := { data := [] } } 1#32
      ChainParams.default.intoPb =
      .ok { ctr := 0#32, next := nextBytes, prev := { data := [] } } := by
    unfold ChainEpochDirection.keyAdvanceLoop
    simp
  have hlt0 : ¬ ((1#32 : BitVec 32) < 0#32) := fun h => nomatch h
  have hjmp : ¬ ((1#32 - 0#32 : BitVec 32) >
      ChainParams.default.intoPb.maxJumpOrDefault) := fun h => nomatch h
  have hooo1 : ¬ ((0#32 : BitVec 32).toNat +
      ChainParams.default.intoPb.maxOooKeysOrDefault.toNat ≥ 2 ^ 32) := fun h => nomatch h
  have hooo2 : ¬ ((1#32 : BitVec 32) > 0#32 +
      ChainParams.default.intoPb.maxOooKeysOrDefault) := fun h => nomatch h
  unfold ChainEpochDirection.key stepCedNext ChainEpochDirection.nextKey
  simp only [hlt0, show ((1#32 : BitVec 32) == 0#32) = false from rfl,
    hjmp, hooo1, hooo2, Bool.false_eq_true, ↓reduceIte,
    Bind.bind, Except.bind, Pure.pure, Except.pure, hadv]
  have hgc : KeyHistory.gc { data := [] } 0#32 ChainParams.default.intoPb = .ok { data := [] } := rfl
  rw [hgc]
  dsimp only [ChainResult.ofPanic, ChainEpochDirection.nextKeyInternal]
  simp only [hnext, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
    show ((0#32 : BitVec 32) == 0xffffffff#32) = false from rfl]

def stepChainRecv0 (hkdf : HkdfFn) (c : Chain) : Chain × List (BitVec 8) :=
  match c.links with
  | [link] =>
    let (recv', out) := stepCedNext hkdf link.recv
    ({ c with links := [{ link with recv := recv' }] }, out)
  | _ => (default, [])

def w0Auth0 : Authenticator :=
  Authenticator.new C0.F (keyToBytes32 w0Key0) 1#64

def w0VnA : VersionNegotiationPB :=
  { authKey := keyToBytes32 w0Key0
    direction := 0#32
    minVersion := 1#32
    chainParams := some ChainParams.default.intoPb }

def w0ChA0 : Chain :=
  match chainFrom (spqrHkdfWith C0.F) none (some w0VnA) with
  | .ok c => c
  | .error _ => default

def w0ChA1Key : Chain × List (BitVec 8) :=
  stepChainRecv0 (spqrHkdfWith C0.F) w0ChA0

def w0PbInner0 : V1State :=
  { innerState := some (.keysUnsampled { uc := some { epoch := 1#64, auth := some w0Auth0.intoPb } }) }

def w0PbA1 : PqRatchetStatePB V1State :=
  { inner := some w0PbInner0
    versionNegotiation := none
    chain := some w0ChA1Key.1.intoPb }

def w0PqA1 : List (BitVec 8) :=
  (spqrDeps C0.F K0).encodeState w0PbA1

def w0Salt1 : CryptoGames.HKDF.Salt :=
  (recvKeyToSalt? (some w0ChA1Key.2)).getD none

private theorem spqr_recv_v1_none_key
    (D : SpqrApiDeps) (hkdf : HkdfFn)
    (stateBytes msgBytes rem : List (BitVec 8))
    (idx : BitVec 32)
    (pb : D.V1StatePB)
    (optChain : Option ChainPB)
    (vn : VersionNegotiationPB)
    (sckaMsg : D.MessageV1)
    (st0 st1 : D.States)
    (ch0 ch2 : Chain)
    (msgKey : List (BitVec 8))
    (hpre : msgPreamble msgBytes =
      .ok { version := 1#8, epoch := 1#64, index := idx, remaining := rem })
    (hdec : decodeState D stateBytes =
      .ok { inner := some pb, versionNegotiation := some vn, chain := optChain })
    (hvn : vn.minVersion = 1#32)
    (hdeser : D.msgDeserialize 1#64 rem = .ok sckaMsg)
    (hfrom : D.statesFromPb pb = .ok st0)
    (hrecv : D.statesRecv st0 sckaMsg = .ok (none, st1))
    (hchFrom : chainFrom hkdf optChain (some vn) = .ok ch0)
    (hchRecv : ch0.recvKey hkdf (1#64 - 1#64) idx = .ok (ch2, msgKey))
    (hne : msgKey.isEmpty = false) :
    recv D hkdf stateBytes msgBytes =
      .ok { state := D.encodeState
              { inner := some (D.statesIntoPb st1)
                versionNegotiation := none
                chain := some ch2.intoPb }
            key := some msgKey } := by
  cases D
  cases vn
  dsimp only at *
  subst hvn
  unfold recv
  rw [hpre]
  simp only [SpqrApiResult.ofError, SpqrApiResult.ofChainResult,
    Bind.bind, Except.bind, Pure.pure, Except.pure,
    hdec, stateVersion, Version.toU8,
    show ¬ ((1#8 : BitVec 8) < (1#32 : BitVec 32).truncate 8) from (fun h => nomatch h),
    show (((1#8 : BitVec 8) != 1#8) && !true) = false from rfl,
    show ((1#8 : BitVec 8) == 0#8) = false from rfl,
    show ¬ ((1#8 : BitVec 8) > 1#8) from (fun h => nomatch h),
    show ((1#8 : BitVec 8) == 1#8) = true from rfl,
    hdeser, hfrom, hrecv,
    show ((1#64 : BitVec 64) == 0#64) = false from rfl,
    hchFrom, hchRecv, hne,
    Bool.false_eq_true, ↓reduceIte]

theorem w0_spqrRecv :
    (spqrV1 C0.F K0).spqr.recv w0PqA0 w0PqMsg = .ok (w0PqA1, w0Salt1) ∧
    (spqrV1 C0.F K0).spqr.recvPanics w0PqA0 w0PqMsg = false := by
  let D := spqrDeps C0.F K0
  let stUnsampled : D.States :=
    .keysUnsampled { uc := { epoch := 1#64, auth := (spqrAuthApi C0.F).from_pb w0Auth0.intoPb } }
  have hpre : msgPreamble w0PqMsg =
      .ok { version := 1#8, epoch := 1#64, index := 1#32, remaining := [0#8] } := rfl
  have hdec : decodeState D w0PqA0 =
      .ok { inner := some w0PbInner0, versionNegotiation := some w0VnA, chain := none } := rfl
  have hdeser : D.msgDeserialize 1#64 [0#8] = .ok { epoch := 1#64, payload := .none } := rfl
  have hfrom : D.statesFromPb w0PbInner0 = .ok stUnsampled := rfl
  have hrecv : D.statesRecv stUnsampled { epoch := 1#64, payload := .none } =
      .ok (none, stUnsampled) := rfl
  have hchFrom : chainFrom (spqrHkdfWith C0.F) none (some w0VnA) = .ok w0ChA0 := rfl
  have hchRecv : w0ChA0.recvKey (spqrHkdfWith C0.F) (1#64 - 1#64) 1#32 =
      .ok (w0ChA1Key.1, w0ChA1Key.2) := by
    change w0ChA0.recvKey (spqrHkdfWith C0.F) 0#64 1#32 = .ok w0ChA1Key
    unfold Chain.recvKey w0ChA1Key stepChainRecv0
    have hep : w0ChA0.epochIdx 0#64 = .ok 0 := rfl
    simp only [show (0#64 == (0#64 : BitVec 64) && 1#32 == (0#32 : BitVec 32)) = false from rfl,
      Bool.false_eq_true, ↓reduceIte, Bind.bind, Except.bind, Pure.pure, Except.pure,
      ChainResult.ofError, hep]
    have hlinks : ∃ linkA nextBytesA,
        w0ChA0.links = [linkA] ∧
        linkA.recv = { ctr := 0#32, next := nextBytesA, prev := { data := [] } } ∧
        nextBytesA.length = 32 ∧
        w0ChA0.params = ChainParams.default.intoPb :=
      ⟨_, _, rfl, rfl, rfl, rfl⟩
    obtain ⟨linkA, nextBytesA, hlA, hrA, hnA, hpA⟩ := hlinks
    simp only [hlA, List.getElem?_cons_zero, List.set, hrA, hpA]
    rw [ced_key_zero_one _ _ hnA]
  have htop : recv D (spqrHkdfWith C0.F) w0PqA0 w0PqMsg =
      .ok { state := w0PqA1, key := some w0ChA1Key.2 } :=
    spqr_recv_v1_none_key D (spqrHkdfWith C0.F) w0PqA0 w0PqMsg [0#8] 1#32
      w0PbInner0 none w0VnA _ stUnsampled stUnsampled w0ChA0 w0ChA1Key.1 w0ChA1Key.2
      hpre hdec rfl hdeser hfrom hrecv hchFrom hchRecv rfl
  refine ⟨?_, ?_⟩
  · rw [spqrV1_eq]
    dsimp only [toSpqrModel, SpqrModel.spqr]
    rw [htop]
    rfl
  · rw [spqrV1_eq]
    dsimp only [toSpqrModel, SpqrModel.spqr, recvPanicsB, recvPanicsSaltB]
    rw [htop]

def w0Pt : List (BitVec 8) := [0x4F#8, 0x4B#8]

def w0Addrs : Option (List (BitVec 8)) :=
  serializeAddrVals (serviceIdParse uuidTryParse) (partyAddr .B) (partyAddr .A)

def w0Mk : MessageKeys :=
  (ChainKey.messageKeys C0.F ⟨w0Key0, 0#32⟩).generateKeys C0.F w0Salt1

def w0Ct : List (BitVec 8) :=
  aesCbcEncrypt C0.E w0Mk.cipherKey w0Mk.iv w0Pt

theorem w0Ct_len : w0Ct.length = 16 := rfl

def w0Msg : SignalMessage :=
  SignalMessage.new C0.F protoSignalCodec currentVersion w0Mk.macKey w0Addrs
    ⟨b0.spkPub⟩ 0#32 0#32 w0Ct ⟨⟨b0.idPub⟩⟩ ⟨w0IdA.publicKey⟩ w0PqMsg

def w0Rest : List (BitVec 8) := w0Msg.serialized

private theorem mut_exec_bind {S α β : Type} (m : Mut S α) (f : α → Mut S β) (s : S) :
    Mut.exec (m >>= f) s =
      match Mut.exec m s with
      | (.ok a, s') => Mut.exec (f a) s'
      | (.error e, s') => (.error e, s') := by
  rcases hm : Mut.exec m s with ⟨_ | _, s'⟩ <;>
    (change (match m s with | (a, s1) => (ExceptT.bindCont f a) s1) = _;
     change m s = _ at hm; rw [hm]; rfl)

private theorem mut_exec_pure {S α : Type} (a : α) (s : S) :
    Mut.exec (pure a : Mut S α) s = (.ok a, s) := rfl

private theorem mut_exec_modify {S : Type} (f : S → S) (s : S) :
    Mut.exec (modify f : Mut S PUnit) s = (.ok ⟨⟩, f s) := rfl

private theorem mut_exec_liftE {S α : Type} (x : Except SignalProtocolError α) (s : S) :
    Mut.exec (liftE x : Mut S α) s = (x, s) := by cases x <;> rfl

private theorem mut_exec_onRatchet {PQ α : Type} (m : Mut RatchetState α) (t : TripleRatchet PQ) :
    Mut.exec (TripleRatchet.onRatchet m) t =
      match Mut.exec m t.ratchet with
      | (.ok a, r') => (.ok a, { t with ratchet := r' })
      | (.error e, r') => (.error e, { t with ratchet := r' }) := by
  unfold TripleRatchet.onRatchet zoom
  rw [mut_exec_bind]
  have hget : Mut.exec (get : Mut (TripleRatchet PQ) (TripleRatchet PQ)) t = (.ok t, t) := rfl
  have hset : ∀ t', Mut.exec (set t' : Mut (TripleRatchet PQ) PUnit) t = (.ok ⟨⟩, t') :=
    fun _ => rfl
  rw [hget]
  dsimp only
  rcases hm : Mut.exec m t.ratchet with ⟨_ | _, r'⟩ <;>
    (rw [mut_exec_bind, hset]; dsimp only; rw [mut_exec_liftE])

def w0St1 : PqParty :=
  { emptyParty with peerId := some ⟨⟨b0.idPub⟩⟩, session := some (w0XA, ⟨.A, w0SA0, 0, [0]⟩) }

theorem w0St1_domain : PqxdhPartyInSpecDomain W0 w0St1 := by
  obtain ⟨st1, x, g, hinit, hsess, hdom⟩ := pqInitModel_W0_creates_wfSession X0
  have hparty : emptyParty.party = .A := rfl
  have htr : emptyParty.trusts ⟨⟨b0.idPub⟩⟩ = true := rfl
  unfold pqInitModel at hinit
  simp only [htr, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hparty, w0_initiateState_eq] at hinit
  injection hinit with hinit'
  injection hinit' with hst
  have hst' := (Prod.mk.inj hst).1
  subst hst'
  exact hdom

theorem w0_expectedAddrs_eq :
    (pqxdhSessionParams W0).expectedAddrs .A = w0Addrs := rfl

def w0CkAfter : ChainKey :=
  ⟨bytesToKey32 (chainHmac C0.F w0Key0 chainKeySeed), 1#32⟩

def w0RState0 : RatchetState :=
  match (Mut.exec SessionState.takeRatchetState w0SA0).1 with
  | .ok r => r
  | .error _ => ⟨0, none, [], 0, 0⟩

def w0RState1 : RatchetState :=
  { w0RState0 with receiverChains := [⟨⟨b0.spkPub⟩, some w0CkAfter, []⟩] }

def w0SEmpty : SessionState (List (BitVec 8)) :=
  { w0SA0 with receiverChains := [], pqRatchetState := [] }

def w0SA1 : SessionState (List (BitVec 8)) :=
  ((⟨w0RState1, w0PqA1, ⟨w0IdA.publicKey⟩, ⟨⟨b0.idPub⟩⟩⟩ :
      TripleRatchet (List (BitVec 8))).applyToSessionState w0SEmpty).clearUnacknowledgedPreKeyMessage

theorem w0_tryDecryptFromRecord_ok
    (spqr : Spqr (List (BitVec 8)) (List (BitVec 8)))
    (hrecv : spqr.recv w0PqA0 w0PqMsg = .ok (w0PqA1, w0Salt1))
    (hpan : spqr.recvPanics w0PqA0 w0PqMsg = false) :
    SessionState.tryDecryptFromRecord C0 spqr
      ((pqxdhSessionParams W0).expectedAddrs .A) w0Msg .whisper 0#256 w0SA0 =
      (.ok w0Pt, w0SA1) ∧
    w0SA1.remoteIdentity = some ⟨⟨b0.idPub⟩⟩ ∧
    w0SA1.pqRatchetState = w0PqA1 := by
  have htake : Mut.exec TripleRatchet.fromSessionState w0SA0 =
      (.ok ⟨w0RState0, w0PqA0, ⟨w0IdA.publicKey⟩, ⟨⟨b0.idPub⟩⟩⟩, w0SEmpty) := rfl
  have hens : Mut.exec (RatchetState.ensureReceiverChain C0 w0Msg.senderRatchetKey 0#256) w0RState0 =
      (.ok ⟨w0Key0, 0#32⟩, w0RState0) := rfl
  have hcons : Mut.exec (RatchetState.consumeMessageKey C0.F w0Msg.senderRatchetKey
      ⟨w0Key0, 0#32⟩ w0Msg.counter .whisper) w0RState0 =
      (.ok (ChainKey.messageKeys C0.F ⟨w0Key0, 0#32⟩), w0RState1) := rfl
  have hmac : w0Msg.verifyMacWithAddresses C0.F ((pqxdhSessionParams W0).expectedAddrs .A)
      ⟨⟨b0.idPub⟩⟩ ⟨w0IdA.publicKey⟩ w0Mk.macKey = true := by
    refine verifyMacWithAddresses_new_C0 _ _ _ _ _ _ _ _ _ _ ?_
    rw [w0_expectedAddrs_eq]
    cases w0Addrs <;> simp [addressCheckPasses]
  have hcbc : aesCbcDecrypt C0.D w0Mk.cipherKey w0Mk.iv w0Msg.ciphertext = some w0Pt := rfl
  have hpqEq : w0Msg.pqRatchet = w0PqMsg := rfl
  let tr1 : TripleRatchet (List (BitVec 8)) := ⟨w0RState1, w0PqA1, ⟨w0IdA.publicKey⟩, ⟨⟨b0.idPub⟩⟩⟩
  have htrDec : Mut.exec (TripleRatchet.decrypt C0 spqr
      ((pqxdhSessionParams W0).expectedAddrs .A) w0Msg .whisper 0#256)
      ⟨w0RState0, w0PqA0, ⟨w0IdA.publicKey⟩, ⟨⟨b0.idPub⟩⟩⟩ = (.ok w0Pt, tr1) := by
    unfold TripleRatchet.decrypt
    rw [mut_exec_bind, mut_exec_onRatchet]; dsimp only
    rw [hens]; dsimp only
    rw [mut_exec_bind, mut_exec_onRatchet]; dsimp only
    rw [hcons]; dsimp only
    rw [mut_exec_bind]
    have hgetTr : Mut.exec (get : Mut (TripleRatchet (List (BitVec 8))) (TripleRatchet (List (BitVec 8))))
        ⟨w0RState1, w0PqA0, ⟨w0IdA.publicKey⟩, ⟨⟨b0.idPub⟩⟩⟩ =
        (.ok ⟨w0RState1, w0PqA0, ⟨w0IdA.publicKey⟩, ⟨⟨b0.idPub⟩⟩⟩,
         ⟨w0RState1, w0PqA0, ⟨w0IdA.publicKey⟩, ⟨⟨b0.idPub⟩⟩⟩) := rfl
    rw [hgetTr]
    dsimp only
    rw [hpqEq, hpan]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hrecv]; dsimp only
    rw [mut_exec_bind, mut_exec_pure]; dsimp only
    have hgen : (ChainKey.messageKeys C0.F ⟨w0Key0, 0#32⟩).generateKeys C0.F w0Salt1 = w0Mk := rfl
    rw [hgen, hmac]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [hcbc]; dsimp only
    rw [mut_exec_bind, mut_exec_modify]; dsimp only
    rw [mut_exec_pure]
  refine ⟨?_, rfl, rfl⟩
  unfold SessionState.tryDecryptFromRecord
  have hver : ¬ (w0SA0.version.toNat ≠ w0Msg.messageVersion.toNat) := fun h => h rfl
  simp only [hver, ↓reduceIte]
  unfold SessionState.tryDecryptWithState
  rw [mut_exec_bind, htake]
  dsimp only
  rw [htrDec]
  dsimp only
  rw [mut_exec_bind, mut_exec_liftE]; dsimp only
  rw [mut_exec_bind, mut_exec_modify]; dsimp only
  rw [mut_exec_pure]
  rfl

theorem w0Rest_tryFrom : SignalMessage.tryFrom protoSignalCodec w0Rest = .ok w0Msg := by
  have hw0Addrs_fit : ∀ a, w0Addrs = some a → a.length < 2 ^ 64 := by
    intro a ha
    unfold w0Addrs serializeAddrVals at ha
    cases hs : serviceIdParse uuidTryParse (partyAddr .B).name with
    | none => simp [hs, Bind.bind, Option.bind] at ha
    | some s =>
      cases hr : serviceIdParse uuidTryParse (partyAddr .A).name with
      | none => simp [hs, hr, Bind.bind, Option.bind] at ha
      | some r =>
        simp only [hs, hr, Bind.bind, Option.bind, Pure.pure] at ha
        injection ha with ha'
        rw [← ha']
        have hab : ∀ (u : Bool × List.Vector (BitVec 8) 16) (d : BitVec 8),
            (addrBytes u d).length = 18 := by
          intro ⟨b, ⟨l, hl⟩⟩ d
          simp [addrBytes, List.Vector.toList, hl]
        rw [List.length_append, hab, hab]
        decide
  exact tryFrom_protoSignalCodec_new_C0 w0Mk.macKey w0Addrs ⟨b0.spkPub⟩ 0#32 0#32 w0Ct
    ⟨⟨b0.idPub⟩⟩ ⟨w0IdA.publicKey⟩ w0PqMsg
    (by rw [w0Ct_len]; decide) (by decide) hw0Addrs_fit

def w0St2 : PqParty :=
  { w0St1 with peerId := some ⟨⟨b0.idPub⟩⟩, session := some (w0XA, ⟨.A, w0SA1, 0, [0]⟩) }

theorem w0_pqRecvWhisperModel_ok :
    pqRecvWhisperModel W0 w0St1 w0Rest 0#256 = some (some (w0St2, w0Pt)) := by
  have ⟨hdec, hrem, _⟩ :=
    w0_tryDecryptFromRecord_ok (pqxdhSpqrSession W0) w0_spqrRecv.1 w0_spqrRecv.2
  unfold pqRecvWhisperModel
  dsimp only [w0St1]
  rw [w0Rest_tryFrom]
  unfold CryptoVerification.SignalSession.pqxdhSessionDecryptModel
  dsimp only
  change (match SessionState.tryDecryptFromRecord C0 (pqxdhSpqrSession W0)
      ((pqxdhSessionParams W0).expectedAddrs .A) w0Msg .whisper 0#256 w0SA0 with
    | (.ok pt, s) => _
    | (.error .panic, _) => _
    | (.error _, _) => _) = _
  rw [hdec]
  dsimp only
  rw [hrem]
  have htr : w0St1.trusts ⟨⟨b0.idPub⟩⟩ = true := rfl
  change (if (!w0St1.trusts ⟨⟨b0.idPub⟩⟩) = true then _ else _) = _
  rw [htr]
  rfl

theorem w0_decryptRecord_ok (x : DecryptGhost) (ses0 : Session (List (BitVec 8)))
    (hremVal : x.rem.val = partyAddr .B) (hlocVal : x.loc.val = partyAddr .A)
    (hmsg : x.msg = w0Msg) (hrest : coinsOf x.rest = 0#256)
    (hses : ses0.state = w0SA0) :
    let ses' : Session (List (BitVec 8)) :=
      { ses0 with state := w0SA1, pendingPreKey := none, pendingKyberPreKey := none }
    decryptRecord W0.C (spqrV1 W0.C.F W0.Q.K) uuidTryParse x
      { currentSession := some ses0 } = .ok (w0Pt, { currentSession := some ses' }) ∧
    ses'.state.remoteIdentity = some ⟨⟨b0.idPub⟩⟩ ∧
    ses'.state.pqRatchetState = w0PqA1 := by
  intro ses'
  have ⟨hdec, hrem, hpq⟩ :=
    w0_tryDecryptFromRecord_ok (spqrV1 W0.C.F W0.Q.K).spqr w0_spqrRecv.1 w0_spqrRecv.2
  refine ⟨?_, hrem, hpq⟩
  unfold decryptRecord SessionRecord.tryDecryptFromRecord
  simp only [hremVal, hlocVal, hmsg, hrest, hses]
  have haddr : serializeAddrVals (serviceIdParse uuidTryParse) (partyAddr .B) (partyAddr .A) =
      (pqxdhSessionParams W0).expectedAddrs .A := rfl
  rw [haddr]
  have hdec' : SessionState.tryDecryptFromRecord W0.C (spqrV1 W0.C.F W0.Q.K).spqr
      ((pqxdhSessionParams W0).expectedAddrs .A) w0Msg .whisper 0#256 w0SA0 =
      (.ok w0Pt, w0SA1) := hdec
  rw [hdec']

theorem w2RealTdSuccEnv_sub {F : ShaCompress} {K : MlKem}
    {a : TryDecryptEnvArgs} {evs : List AllocEvent}
    (h : W2RealTdSuccEnv F K a evs) :
    W2RealTdEnv F K a evs := by
  obtain ⟨pre_pb, vn, pb, st0, sckaMsg, v,
    xInit, xNew, xAdd, xRk, xSInto, xCInto,
    evs1, _, rfl, h1,
    _, _, rfl, rfl,
    _, _, rfl, rfl,
    evs5, _, rfl, h5,
    _, _, rfl, ⟨_, evs7b, rfl, rfl, h7f⟩,
    _, _, rfl, rfl,
    _, evs9f, rfl, ⟨evs9a, _, rfl, h9a, ⟨evs9b, evs9c, rfl, h9b, h9c⟩⟩, h9f⟩ := h
  refine ⟨0, false, true, false, [], pre_pb, vn, pb, st0, sckaMsg, v,
    xInit, xNew, xAdd, xRk, xSInto, xCInto,
    Nat.zero_le 16, Nat.zero_le 12, trivial, ?_⟩
  unfold W2TryDecryptTightEnv
  refine Or.inr (Or.inr ⟨evs1, _, rfl, h1, ?_⟩)
  refine Or.inr ⟨[], _, rfl, Or.inl FreeOnlyEvs.nil, ?_⟩
  refine Or.inr ⟨[], _, rfl, Or.inl FreeOnlyEvs.nil, ?_⟩
  refine Or.inr ⟨evs5, _, rfl, h5, ?_⟩
  refine Or.inr ⟨_, _, rfl, Or.inr (Or.inr ⟨s7CoreEvs true false, evs7b, rfl, rfl, h7f⟩), ?_⟩
  refine Or.inr ⟨_, _, rfl, Or.inr (Or.inl rfl), ?_⟩
  exact Or.inr ⟨_, evs9f, rfl,
    Or.inr ⟨evs9a, _, rfl, h9a, Or.inr ⟨evs9b, evs9c, rfl, h9b, h9c⟩⟩, h9f⟩

theorem w2RealTdSuccEnv_inhabited (a : TryDecryptEnvArgs)
    (hct : 0 < a.msg.ciphertext.length) :
    ∃ evs, AllocEvent.alloc a.msg.ciphertext.length ∈ evs ∧
      W2RealTdSuccEnv C0.F K0 a evs := by
  let stUnsampled : States spqrPolyApi (spqrAuthApi C0.F) :=
    .keysUnsampled { uc := { epoch := 1#64, auth := (spqrAuthApi C0.F).from_pb w0Auth0.intoPb } }
  let sckaMsg : Message spqrPolyApi := { epoch := 1#64, payload := .none }
  let v : V1Recv spqrPolyApi (spqrAuthApi C0.F) := { key := none, state := stUnsampled }
  let xInit0 : InitInnerGhost := ⟨0#64, .v1, .a2b, 0#64, []⟩
  let xNew0 : ChainNewGhost := ⟨0#64, false, 0#64, [], .a2b, ChainParams.default.intoPb⟩
  let gCh0 : CryptoVerification.SpqrV1.ChainProofs.ChainGhost := ⟨0#64, 0#64, 0#64, [], ⟨0#64, 0#64⟩⟩
  let xSInto0 : StatesIntoPbGhost C0.F := ⟨0#64, 0#64, stUnsampled⟩
  let xCInto0 : ChainIntoPbCall := ⟨0#64, 0#64, gCh0, default⟩
  obtain ⟨xAdd, xRk, hSpqr⟩ := spqrRecvC07TightLinkedEnv_nil_exists
    C0.F K0 StatesRecvProtoEnv a.st.pqRatchetState default w0VnA w0PbInner0 stUnsampled sckaMsg v
    xInit0 xNew0 xSInto0 xCInto0
  let evsS7 := s7CoreEvs true false
  let evsS8 := rustAllocEvents a.msg.ciphertext.length 1
  refine ⟨evsS7 ++ evsS8, ?_,
    default, w0VnA, w0PbInner0, stUnsampled, sckaMsg, v,
    xInit0, xNew0, xAdd, xRk, xSInto0, xCInto0, ?_⟩
  · have hpos : 1 ≤ a.msg.ciphertext.length := hct
    simp [evsS7, evsS8, rustAllocEvents, hpos]
  · exact ⟨[], evsS7 ++ evsS8, rfl, ⟨by decide, by decide, fun _ h => nomatch h⟩,
      [], evsS7 ++ evsS8, rfl, rfl,
      [], evsS7 ++ evsS8, rfl, rfl,
      [], evsS7 ++ evsS8, rfl, hSpqr,
      evsS7, evsS8, rfl, ⟨evsS7, [], (List.append_nil _).symm, rfl, FreeOnlyEvs.nil⟩,
      evsS8, [], (List.append_nil _).symm, rfl,
      [], [], rfl,
        ⟨[], [], rfl, FreeOnlyEvs.nil, ⟨[], [], rfl, ⟨Nat.zero_le 6, fun _ h => nomatch h⟩, FreeOnlyEvs.nil⟩⟩,
        FreeOnlyEvs.nil⟩

/-! ## 3. Inclusion into Binary-Kit Release Envelope -/

private theorem iterConcatEnv_sub {α : Type} {f : α → List AllocEvent → Prop} :
    ∀ (xs : List α) {evs : List AllocEvent}, IterConcatEnv f xs evs → IterSeqEnv f xs evs
  | [], _, h => h
  | _ :: xs, _, ⟨e1, e2, rfl, h1, h2⟩ => Or.inr ⟨e1, e2, rfl, h1, iterConcatEnv_sub xs h2⟩

private theorem readFileOkEnv_sub {rd : CryptoVerification.SignalSession.Cli.ReadRule}
    {files : FsFiles} {path : List (BitVec 8)} {evs : List AllocEvent}
    (h : ReadFileOkEnv rd files path evs) :
    ReadFileRuleEnv rd files path evs := by
  obtain ⟨bs, hrd, hle, hdisj⟩ := h
  unfold ReadFileRuleEnv
  rw [hrd]
  rcases hdisj with h1 | h2
  · exact Or.inl h1
  · exact Or.inr (Or.inr (Or.inl ⟨hle, h2⟩))

private theorem readStdinSuccEnv_sub {bs : List (BitVec 8)} {evs : List AllocEvent}
    (h : ReadStdinSuccEnv bs evs) : ReadStdinEnv bs evs := by
  obtain ⟨hle, h1 | h2⟩ := h
  · exact Or.inl h1
  · exact Or.inr (Or.inl ⟨hle, h2⟩)

private theorem cliMainSetupSuccEnv_sub {i₀ : Inputs} {addrOpt : Option AddressCall}
    {evs : List AllocEvent} (h : CliMainSetupSuccEnv i₀ addrOpt evs) :
    CliMainSetupEnv uuidTryParse i₀ addrOpt true evs := by
  obtain ⟨_, _, rfl, rfl, e2, _, rfl, h2, e3, _, rfl, h3, e4, _, rfl, h4, e5, e6, rfl, h5, h6⟩ := h
  have h5' : ReadFileEnv (initFsState (cliInputs i₀)).files (utf8 "coins") e5 := by
    rw [← readFileRuleEnv_eq_readFileEnv]
    exact readFileOkEnv_sub h5
  exact Or.inr ⟨_, _, rfl, Or.inr rfl,
    Or.inr ⟨e2, _, rfl, iterConcatEnv_sub _ h2,
      Or.inr ⟨e3, _, rfl, h3,
        Or.inr ⟨e4, _, rfl, readStdinSuccEnv_sub h4,
          Or.inr ⟨e5, e6, rfl, h5', h6⟩⟩⟩⟩⟩

private theorem addrTextValSuccEnv_sub {rem : AddrVal} {evs : List AllocEvent}
    (h : AddrTextValSuccEnv rem evs) :
    AddrTextValEnv DecimalEnv rem evs := by
  obtain ⟨e1, _, rfl, h1, e2, _, rfl, h2, e3, _, rfl, h3, e4, e5, rfl, h4, h5⟩ := h
  exact Or.inr ⟨e1, _, rfl, h1,
    Or.inr ⟨e2, _, rfl, h2,
      Or.inr ⟨e3, _, rfl, h3,
        Or.inr ⟨e4, e5, rfl, h4, h5⟩⟩⟩⟩

private theorem dirGetCacheMissOkBinEnv_sub {F0 : FsFiles} {d : DirGhost}
    {name : List (BitVec 8)} {evs : List AllocEvent}
    (h : DirGetCacheMissOkBinEnv F0 d name evs) :
    DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd F0 d name evs := by
  obtain ⟨hd, bs, hrd, _, ePath, _, rfl, hPath, eRd, _, rfl, hRd, eErr, eFree, rfl, hErr, hFree⟩ := h
  unfold DirGetEnv
  rw [hd]
  dsimp only [List.find?]
  refine Or.inr ⟨ePath, _, rfl, hPath,
    Or.inr ⟨eRd, _, rfl, readFileOkEnv_sub hRd,
      Or.inr ⟨eErr, eFree, rfl, ?_, hFree⟩⟩⟩
  unfold DirGetErrAllocEnv
  rw [hrd]
  exact hErr

private theorem r0BinarySuccEnv_sub {g : RunCall} {evs : List AllocEvent}
    (h : R0BinarySuccEnv g evs) :
    R0BinaryEnv cliIo.rd g evs := by
  obtain ⟨ownB, ownAddr, hget, hparse, eGet, _, rfl, hGet, eAddr, eFree, rfl, hAddr, hFree⟩ := h
  refine Or.inr (Or.inr ⟨eGet, eAddr ++ eFree, rfl, dirGetCacheMissOkBinEnv_sub hGet, ?_⟩)
  unfold PreAfterGetEnv
  rw [hget]
  refine Or.inr ⟨eAddr, eFree, rfl, ?_, hFree⟩
  unfold addressEvents
  rw [hparse]
  exact hAddr

private theorem sigTryFromOkEnv_sub {rest : List (BitVec 8)} {msg : SignalMessage}
    {evs : List AllocEvent} (h : SigTryFromOkEnv rest msg evs) :
    SigTryFromSliceEnv rest evs := by
  obtain ⟨htf, evsLoop, _, rfl, hLoop,
    _, evsTail, rfl,
    ⟨evsPf, _, rfl, hPf, ⟨evsCt, _, rfl, hCt, ⟨evsAd, evsCl, rfl, hAd, hCl⟩⟩⟩,
    hTail⟩ := h
  unfold SigTryFromSliceEnv SigTryFromPostEnv
  refine Or.inr (Or.inr ⟨evsLoop, _, rfl, hLoop, Or.inr ⟨_, evsTail, rfl, ?_, hTail⟩⟩)
  rw [htf]
  unfold SigTryFromPostOutPreEnv SigTryFromPostOkAllocEnv
  exact Or.inr ⟨evsPf, _, rfl, hPf,
    Or.inr ⟨evsCt, _, rfl, hCt, Or.inr ⟨evsAd, evsCl, rfl, hAd, hCl⟩⟩⟩

private theorem w2LoadStepSuccEnv_split [LibsignalPlacement]
    {w2R : W2BinaryWhisperParams}
    {rec : SessionRecord (List (BitVec 8))} {evs : List AllocEvent}
    (h : W2LoadStepSuccEnv w2R rec evs) :
    let kit := decSessKitPlaced w2R.repAlloc w2R.x.F w2R.x.peer w2R.B
    let kitEnv := decBinarySessKitPlacedBudget w2R.repAlloc w2R.B w2R.x.F w2R.x.peer
    let rem := (toDecryptGhost w2R.x).rem.val
    ∃ evsLoadStep,
      evs = evsLoadStep ++ rustDeallocEvents kit.loadBoxSize 8 ∧
      LoadPollStepEnv kit kitEnv StoresGhost.opened.sessions rem evsLoadStep := by
  intro kit kitEnv rem
  obtain ⟨b0, bsRest, hget, henc, hsc,
    _, _, rfl,
    ⟨_, _, rfl, rfl, ⟨evsAddr, _, rfl, hAddr, ⟨evsGet, _, rfl, hGet,
      ⟨_, evsFree, rfl, rfl, hFree⟩⟩⟩⟩,
    rfl⟩ := h
  refine ⟨_, rfl, Or.inr ⟨_, _, rfl, Or.inr ⟨show 0 < 24 by decide, rfl⟩, ?_⟩⟩
  change cliSessionKitLoadPollEnv cliIo.rd scopeKit
    (AddrTextValEnv DecimalEnv) (DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd)
    (ofBytesEnv RecordDeserializeCancelEnv) w2R.x.F StoresGhost.opened.sessions rem _
  unfold cliSessionKitLoadPollEnv
  refine Or.inr ⟨evsAddr, _, rfl, addrTextValSuccEnv_sub hAddr,
    Or.inr ⟨evsGet, _, rfl, dirGetCacheMissOkBinEnv_sub hGet,
      Or.inr ⟨_, evsFree, rfl, ?_, hFree⟩⟩⟩
  unfold OptLoadDeserEnv
  rw [hget]
  exact ⟨rec, henc, hsc, sessDeserEvents_mem_recordDeserializeCancelEnv hsc⟩

private theorem recordDecryptSuccEnv_sub {F : ShaCompress} {K : MlKem}
    {x : RecordDecryptGhost} {evs : List AllocEvent}
    (h : RecordDecryptSuccEnv F K x evs) :
    RecordDecryptEnv (W2RealTdEnv F K) x evs := by
  obtain ⟨hver, G₁, hcl, eClone, _, rfl, hClone, eTd, ePost, rfl, hTd, hPost⟩ := h
  unfold RecordDecryptEnv
  simp only [hver, ↓reduceIte]
  exact ⟨G₁, hcl, Or.inr ⟨eClone, eTd ++ ePost, rfl, hClone,
    Or.inr ⟨eTd, ePost, rfl, w2RealTdSuccEnv_sub hTd, Or.inl hPost⟩⟩⟩

private theorem w2TrustStepSuccEnv_sub [LibsignalPlacement]
    {w2R : W2BinaryWhisperParams} (k : IdentityKey) {evs : List AllocEvent}
    (h : W2TrustStepSuccEnv w2R evs) :
    let ikit := decIdKitPlaced w2R.repAlloc w2R.x.F w2R.x.peer w2R.B
    let ikitEnv := decBinaryIdKitPlacedBudget w2R.repAlloc w2R.B w2R.x.F w2R.x.peer
    let rem := (toDecryptGhost w2R.x).rem.val
    TrustStepEnv ikit ikitEnv StoresGhost.opened.identity rem k .receiving evs := by
  intro ikit ikitEnv rem
  obtain ⟨_, _, rfl, rfl, _, _, rfl, ⟨eGet, eFree, rfl, hGet, hFree⟩, rfl⟩ := h
  refine Or.inr ⟨_, _, rfl, Or.inr ⟨show 0 < 32 by decide, rfl⟩, Or.inr ⟨eGet ++ eFree, _, rfl, ?_, rfl⟩⟩
  change cliIdentityKitTrustPollEnv
    (DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd) w2R.x.F
    StoresGhost.opened.identity rem k .receiving (eGet ++ eFree)
  exact Or.inr ⟨eGet, eFree, rfl, dirGetCacheMissOkBinEnv_sub hGet, hFree⟩

private theorem w2SaveStepSuccEnv_sub [LibsignalPlacement]
    {w2R : W2BinaryWhisperParams} {k : IdentityKey} {evs : List AllocEvent}
    (h : W2SaveStepSuccEnv w2R k evs) :
    let ikit := decIdKitPlaced w2R.repAlloc w2R.x.F w2R.x.peer w2R.B
    let ikitEnv := decBinaryIdKitPlacedBudget w2R.repAlloc w2R.B w2R.x.F w2R.x.peer
    let rem := (toDecryptGhost w2R.x).rem.val
    SaveStepEnv ikit ikitEnv
      (ikit.trustUpdate StoresGhost.opened.identity rem k .receiving (.ok true))
      rem k evs := by
  intro ikit ikitEnv rem
  obtain ⟨hne, hchg, ⟨bs, hget⟩, _, _, rfl, rfl, _, _, rfl,
    ⟨eGet, _, rfl, hGet, eFree, _, rfl, hFree, eSer, _, rfl, hSer,
      eOwn, eGrow, rfl, hOwn, hGrow⟩,
    rfl⟩ := h
  refine Or.inr ⟨_, _, rfl, Or.inr ⟨show 0 < 32 by decide, rfl⟩, Or.inr ⟨_, _, rfl, ?_, rfl⟩⟩
  change cliIdentityKitSavePollEnv cliIo.rd
    (DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd) DirPutStrEnv w2R.x.F
    (ikit.trustUpdate StoresGhost.opened.identity rem k .receiving (.ok true)) rem k _
  unfold cliIdentityKitSavePollEnv
  refine Or.inr ⟨eGet, _, rfl, dirGetCacheMissOkBinEnv_sub hGet, ?_⟩
  unfold cliIdentityKitSaveTailEnv
  rw [hget]
  refine Or.inr ⟨eFree, _, rfl, hFree, Or.inr ⟨eSer, _, rfl, hSer, ?_⟩⟩
  unfold DirPutStrEnv
  split
  · next heq => exact absurd heq hne
  · refine Or.inr ⟨eOwn, eGrow, rfl, hOwn, ?_⟩
    unfold DirPutTailEnv
    rw [hchg]
    split
    · exact Or.inr hGrow
    · next hnot => exact absurd (fun _ hm => nomatch hm) hnot

private theorem w2StoreStepSuccEnv_sub [LibsignalPlacement]
    {w2R : W2BinaryWhisperParams}
    {rec' : SessionRecord (List (BitVec 8))} {ses' : Session (List (BitVec 8))}
    {G' : SessionGhost} {evs : List AllocEvent}
    (h : W2StoreStepSuccEnv w2R rec' ses' G' evs) :
    let kit := decSessKitPlaced w2R.repAlloc w2R.x.F w2R.x.peer w2R.B
    let kitEnv := decBinarySessKitPlacedBudget w2R.repAlloc w2R.B w2R.x.F w2R.x.peer
    let rem := (toDecryptGhost w2R.x).rem.val
    FromStoreCallEnv kit kitEnv StoresGhost.opened.sessions rem rec' evs := by
  intro kit kitEnv rem
  obtain ⟨hcur', hgv', hFreeDrop, _,
    ⟨eAddr, _, rfl, hAddr, eSer, ePut, rfl, hSer, hPut⟩,
    _, eFree, rfl, ⟨_, _, rfl, rfl, _, _, rfl, rfl, rfl⟩, hFree⟩ := h
  refine Or.inr ⟨_, eFree, rfl,
    Or.inr ⟨_, _, rfl, Or.inr ⟨show 0 < 32 by decide, rfl⟩,
      Or.inr ⟨_, _, rfl, ?_, rfl⟩⟩,
    hFree⟩
  change cliSessionKitStorePollEnv (AddrTextValEnv DecimalEnv) RecordSerializeSeqFreeValidEnv
    DirPutEnv StoresGhost.opened.sessions rem rec' _
  refine Or.inr ⟨eAddr, _, rfl, addrTextValSuccEnv_sub hAddr,
    Or.inr ⟨eSer, ePut, rfl, ?_, ?_⟩⟩
  · refine ⟨⟨0#64, 8#64, some G'⟩, ?_, ?_⟩
    · unfold RecordGhostValid
      rw [hcur']
      exact hgv'
    · unfold RecordSerializeSeqFreeEnv
      rw [hcur']
      obtain ⟨_, eDrop, rfl, ⟨eClone, eEnc, rfl, hClone, hEnc⟩, rfl⟩ := hSer
      exact Or.inr ⟨eClone, eEnc ++ dropClonedSessionEvents G' ses'.state,
        by simp only [List.append_assoc], hClone, Or.inr ⟨eEnc, _, rfl, hEnc, hFreeDrop⟩⟩
  · unfold DirPutEnv DirPutTailEnv
    have hchg : StoresGhost.opened.sessions.changed = [] := rfl
    rw [hchg]
    split
    · exact Or.inr hPut
    · next hnot => exact absurd (fun _ hm => nomatch hm) hnot

private theorem recvWhisperM5SuccEnv_sub {w2R : W2BinaryWhisperParams} {evs : List AllocEvent}
    (h : RecvWhisperM5SuccEnv w2R evs) :
    LibsignalBinary.Proofs.PeakBudget.CliMainPeakSpec.M5PhaseEnv
      [(utf8 "identities", [w2R.peer.name.bytes]),
       (utf8 "sessions", [addressText (toDecryptGhost w2R.x).rem.val])] evs := by
  obtain ⟨_, eFree, rfl,
    ⟨_, _, rfl, ⟨eW1, eF1, rfl, hW1, hF1⟩,
     ⟨_, _, rfl, ⟨eW2, eF2, rfl, hW2, hF2⟩, rfl⟩⟩,
    hFree⟩ := h
  exact Or.inr ⟨_, eFree, rfl,
    Or.inr ⟨_, _, rfl, Or.inr ⟨eW1, eF1, rfl, iterConcatEnv_sub _ hW1, hF1⟩,
      Or.inr ⟨_, [], rfl, Or.inr ⟨eW2, eF2, rfl, iterConcatEnv_sub _ hW2, hF2⟩, rfl⟩⟩,
    hFree⟩

/-- Inclusion of `RecvWhisperSuccMainEnv` into
`RealCliMainBinaryEnvOf (mkBinaryKitRealCalleeEnvs img S X W) i₀`. -/
theorem recvWhisperSuccMainEnv_sub [LibsignalPlacement]
    (img : Arm64.Obj.Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (i₀ : Inputs) {evs : List AllocEvent}
    (h : RecvWhisperSuccMainEnv img ⟨W.C, W.Q⟩ i₀ evs) :
    RealCliMainBinaryEnvOf (mkBinaryKitRealCalleeEnvs img S X W) i₀ evs := by
  obtain ⟨st, st₁, rc, g, peerAddr, rest, msg, ag, w2R,
    rec, rec', ses, ses', G, G', pt, k,
    evsPre, evsDec, evsStore, evsM6,
    rfl, _, _, _, _, hgi, hgc, hparse, _, _, hstdin, hstdinCap,
    _, _, _, hw2Dom, hScopeAt, hcur, hgv, hdecOk, hcur', hremId,
    hPre, hDec, hStore, hM6⟩ := h
  obtain ⟨evsSetup, _, rfl, hSetup,
    evsR0, _, rfl, hR0,
    evsSig, evsLoad, rfl, hSig, hLoad⟩ := hPre
  obtain ⟨evsLoadStep, rfl, hLoadStep⟩ := w2LoadStepSuccEnv_split hLoad
  obtain ⟨evsTrust, _, rfl, hTrust,
    evsSave, _, rfl, hSave,
    evsStoreStep, _, rfl, hStoreStep,
    evsPostSigFree, _, rfl, hPostSigFree,
    evsJoin, evsM5, rfl, hJoin, hM5⟩ := hStore
  let kit := decSessKitPlaced w2R.repAlloc w2R.x.F w2R.x.peer w2R.B
  let kitEnv := decBinarySessKitPlacedBudget w2R.repAlloc w2R.B w2R.x.F w2R.x.peer
  let ikit := decIdKitPlaced w2R.repAlloc w2R.x.F w2R.x.peer w2R.B
  let ikitEnv := decBinaryIdKitPlacedBudget w2R.repAlloc w2R.B w2R.x.F w2R.x.peer
  let dx := toDecryptGhost w2R.x
  have hFromStore : FromStoreCallEnv kit kitEnv StoresGhost.opened.sessions dx.rem.val rec'
      evsStoreStep := w2StoreStepSuccEnv_sub hStoreStep
  have hTrustedTrue : FromTrustedTrueEnv kit kitEnv StoresGhost.opened.sessions
      ikit ikitEnv StoresGhost.opened.identity dx rec' k
      (evsSave ++ evsStoreStep) :=
    Or.inr ⟨evsSave, evsStoreStep, rfl, w2SaveStepSuccEnv_sub hSave, Or.inr hFromStore⟩
  have hKeyReady : FromKeyReadyEnv kit kitEnv StoresGhost.opened.sessions
      ikit ikitEnv StoresGhost.opened.identity dx rec' k
      (evsTrust ++ (evsSave ++ evsStoreStep)) :=
    Or.inr ⟨evsTrust, _, rfl, w2TrustStepSuccEnv_sub k hTrust, Or.inr (Or.inr hTrustedTrue)⟩
  have hPostSome : FromPostSomeEnv W.C (spqrV1 W.C.F W.Q.K) uuidTryParse
      kit kitEnv StoresGhost.opened.sessions ikit ikitEnv StoresGhost.opened.identity dx rec
      (evsTrust ++ (evsSave ++ evsStoreStep)) :=
    Or.inr ⟨pt, rec', ses', k, hdecOk, hcur', hremId, hKeyReady⟩
  have hRegSome : FromRegionSomeEnv W.C (spqrV1 W.C.F W.Q.K) uuidTryParse
      (W2RealTdEnv W.C.F W.Q.K) kit kitEnv StoresGhost.opened.sessions
      ikit ikitEnv StoresGhost.opened.identity dx rec G ses.state
      (evsDec ++ (evsTrust ++ (evsSave ++ evsStoreStep))) :=
    Or.inr ⟨evsDec, _, rfl, recordDecryptSuccEnv_sub hDec, hPostSome⟩
  have hFromPolled : FromLoadPolledEnv W.C (spqrV1 W.C.F W.Q.K) uuidTryParse
      (W2RealTdEnv W.C.F W.Q.K) kit kitEnv StoresGhost.opened.sessions
      ikit ikitEnv StoresGhost.opened.identity scopeKit dx
      (rustDeallocEvents kit.loadBoxSize 8 ++
        (evsDec ++ (evsTrust ++ (evsSave ++ evsStoreStep)))) :=
    Or.inr ⟨_, _, rfl, rfl,
      Or.inr (Or.inr (Or.inr ⟨rec, ses, G, hScopeAt, hcur, hgv, hRegSome⟩))⟩
  let evsDecSig := evsLoadStep ++ (rustDeallocEvents kit.loadBoxSize 8 ++
    (evsDec ++ (evsTrust ++ (evsSave ++ evsStoreStep))))
  have hSlot : W2RecvWhisperBinaryKitSlotEnv ⟨W.C, W.Q⟩ w2R evsDecSig :=
    Or.inr ⟨evsLoadStep, _, rfl, hLoadStep, hFromPolled⟩
  have hDecSig : (mkBinaryKitRealCalleeEnvs img S X W g).decSigEnv evsDecSig := by
    unfold mkBinaryKitRealCalleeEnvs
    dsimp only
    rw [hgc, hgi]
    exact ⟨w2R, hw2Dom, hSlot⟩
  let evsArm := evsSig ++ (evsDecSig ++ evsPostSigFree)
  have hArmBin : LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge.RunArmBinaryEnv
      cliIo.rd (runFiles g.i) (mkBinaryKitRealCalleeEnvs img S X W g)
      sessionCapBytes g.i.stdin g.c evsArm := by
    rw [hgc, hgi, hstdin]
    unfold LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge.RunArmBinaryEnv
      LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge.RecvArmBinaryEnv
    have hw2 : (wireWhisper : BitVec 8) = 2#8 := rfl
    simp only [hw2, ↓reduceIte]
    exact Or.inr (Or.inr ⟨evsSig, _, rfl, Or.inl (sigTryFromOkEnv_sub hSig),
      Or.inr (Or.inr ⟨evsDecSig, evsPostSigFree, rfl, hDecSig, hPostSigFree⟩)⟩)
  let evsRun := evsR0 ++ (evsArm ++ evsJoin)
  have hRunBin : CliRunBinaryEnv cliIo.rd (mkBinaryKitRealCalleeEnvs img S X W g)
      sessionCapBytes g evsRun :=
    Or.inr (Or.inr ⟨evsR0, _, rfl, r0BinarySuccEnv_sub hR0,
      Or.inr ⟨evsArm, evsJoin, rfl, hArmBin, hJoin⟩⟩)
  have hSetup0 : CliMainSetupEnv uuidTryParse i₀ (some ag) true evsSetup := by
    rw [← hgi]
    exact cliMainSetupSuccEnv_sub hSetup
  have hBoundedSetup : CliMainBoundedSetupEnv i₀.argv.length evsSetup :=
    cliMainBoundedSetupEnv_of_setup_any uuidTryParse i₀ (some ag) true (fun _ => hstdinCap) hSetup0
  let dirs : List (List (BitVec 8) × List (List (BitVec 8))) :=
    [(utf8 "identities", [w2R.peer.name.bytes]),
     (utf8 "sessions", [addressText dx.rem.val])]
  have hdomPeer := hw2Dom peerAddr rfl
  obtain ⟨hpeer40, hrem40, _⟩ :=
    peer_and_rem_name_le_40_of_recv hparse hdomPeer.1 hdomPeer.2.2.1
  have hdirsGuard : ∀ dn ∈ dirs,
      dn.1.length ≤ cliMaxDirPathBytes ∧ ∀ nm ∈ dn.2, nm.length ≤ cliMaxAddrTextBytes := by
    intro dn hdn
    simp only [dirs, List.mem_cons, List.not_mem_nil, or_false] at hdn
    rcases hdn with rfl | rfl
    · refine ⟨?_, ?_⟩
      · have h10 : (utf8 "identities").length = 10 := opened_peers_path_len
        rw [h10]; decide
      · intro nm hnm
        simp only [List.mem_singleton] at hnm; subst hnm
        unfold cliMaxAddrTextBytes; omega
    · refine ⟨?_, ?_⟩
      · have h8 : (utf8 "sessions").length = 8 := opened_sess_path_len
        rw [h8]; decide
      · intro nm hnm
        simp only [List.mem_singleton] at hnm; subst hnm
        have hat := addressText_length_le dx.rem.val
        have hremEq : dx.rem.val.name.length = (toDecryptGhost w2R.x).rem.name.bytes.length := rfl
        dsimp only [dx] at hat hremEq ⊢
        rw [hremEq] at hat
        unfold cliMaxAddrTextBytes; omega
  let wPost : ValidPostSetupWitness i₀ :=
    { g := g
      g_i := hgi
      parse_ok := by rw [hgi, hgc]; exact hparse
      stdin_le := by rw [hgi]; exact hstdinCap
      dirs := dirs
      dirs_sum_le := by simp [dirs, cliMaxDirtyEntries]
      dirs_bounds := hdirsGuard
      ok := true }
  have hMainBin : RealCliMainBinaryEnvOf (mkBinaryKitRealCalleeEnvs img S X W) i₀
      (evsSetup ++ (evsRun ++ (evsM5 ++ evsM6))) :=
    Or.inr ⟨evsSetup, _, rfl, hBoundedSetup,
      Or.inr ⟨wPost, hgi,
        Or.inr ⟨evsRun, _, rfl, hRunBin,
          Or.inr ⟨evsM5, evsM6, rfl, recvWhisperM5SuccEnv_sub hM5, hM6.1⟩⟩⟩⟩
  have heqEvs :
      evsSetup ++ (evsRun ++ (evsM5 ++ evsM6)) =
      (evsSetup ++ (evsR0 ++ (evsSig ++ (evsLoadStep ++ rustDeallocEvents kit.loadBoxSize 8)))) ++
        evsDec ++
        (evsTrust ++ (evsSave ++ (evsStoreStep ++ (evsPostSigFree ++ (evsJoin ++ evsM5))))) ++
        evsM6 := by
    dsimp only [evsRun, evsArm, evsDecSig]
    simp only [List.append_assoc]
  rwa [heqEvs] at hMainBin

/-- Alias form of `recvWhisperSuccMainEnv_sub` on `realCliMainBinaryKitEnvOf img S X W i₀`. -/
theorem recvWhisperSuccMainEnv_sub_kit [LibsignalPlacement]
    (img : Arm64.Obj.Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (i₀ : Inputs) {evs : List AllocEvent}
    (h : RecvWhisperSuccMainEnv img ⟨W.C, W.Q⟩ i₀ evs) :
    realCliMainBinaryKitEnvOf img S X W i₀ evs :=
  recvWhisperSuccMainEnv_sub img S X W i₀ h

/-! ## 4. Concrete `SessionGhostValid` Witnesses (`w0Ses0` & `w0Ses1`) and End-to-End Trace -/

def w0CliHooks : CliHooks where
  C := C0
  Q := Q0
  bcmp a b := if a = b then 0#64 else 1#64
  bcmp_ok a b _ := by by_cases h : a = b <;> simp [h]
  utf8Err _ := (0#64, 0#16)

def w0Rec0 : SessionRecord (List (BitVec 8)) :=
  toRecord (extrasOf fun _ => w0XA) ⟨.A, w0SA0, 0, [0]⟩

private theorem w0Rec0_encode_eq :
    encodeRecord w0Rec0 = pqSessBytes w0St1 := by
  unfold w0Rec0 pqSessBytes w0St1
  exact (encodeRecordX_eq_toRecord (fun _ => w0XA) ⟨.A, w0SA0, 0, [0]⟩).symm

private theorem w0Rec0_encode_ne_nil : encodeRecord w0Rec0 ≠ [] := by
  decide +kernel

private theorem w0Rec0_currentSession_isSome : w0Rec0.currentSession.isSome = true := by
  decide +kernel

def w0Ses0 : Session (List (BitVec 8)) :=
  match w0Rec0.currentSession with
  | some s => s
  | none =>
    { state :=
        { sessionVersion := 4#32
          localIdentity := ⟨pk0⟩
          remoteIdentity := some ⟨pk0⟩
          rootKey := 0#256
          previousCounter := 0#32
          senderChain := none
          receiverChains := []
          pqRatchetState := []
          pendingPreKey := false }
      pendingPreKey := none
      pendingKyberPreKey := none
      aliceBaseKey := []
      remoteRegistrationId := 0#32
      localRegistrationId := 0#32 }

private theorem w0Rec0_currentSession : w0Rec0.currentSession = some w0Ses0 := by
  have his := w0Rec0_currentSession_isSome
  cases hs : w0Rec0.currentSession with
  | none => rw [hs] at his; cases his
  | some s => unfold w0Ses0; rw [hs]

private theorem w0Ses0_state_eq : w0Ses0.state = w0SA0 := by
  have hcur := w0Rec0_currentSession
  unfold w0Rec0 toRecord at hcur
  dsimp only at hcur
  injection hcur with hses
  rw [← hses]

def w0Ses1 : Session (List (BitVec 8)) :=
  { w0Ses0 with state := w0SA1, pendingPreKey := none, pendingKyberPreKey := none }

def w0Rec1 : SessionRecord (List (BitVec 8)) :=
  { currentSession := some w0Ses1 }

private theorem w0Ses0_pendingPreKey_isSome : w0Ses0.pendingPreKey.isSome = true := by
  decide +kernel

def w0Ppk : PendingPreKey :=
  match w0Ses0.pendingPreKey with
  | some p => p
  | none => ⟨none, 0#32, pk0, 0#64⟩

private theorem w0Ses0_pendingPreKey_eq : w0Ses0.pendingPreKey = some w0Ppk := by
  have his := w0Ses0_pendingPreKey_isSome
  cases hp : w0Ses0.pendingPreKey with
  | none => rw [hp] at his; cases his
  | some p => unfold w0Ppk; rw [hp]

private theorem w0Ses0_pendingKyber_isSome : w0Ses0.pendingKyberPreKey.isSome = true := by
  decide +kernel

def w0Kpk : PendingKyberPreKey :=
  match w0Ses0.pendingKyberPreKey with
  | some k => k
  | none => ⟨0#32, []⟩

private theorem w0Ses0_pendingKyber_eq : w0Ses0.pendingKyberPreKey = some w0Kpk := by
  have his := w0Ses0_pendingKyber_isSome
  cases hk : w0Ses0.pendingKyberPreKey with
  | none => rw [hk] at his; cases his
  | some k => unfold w0Kpk; rw [hk]

private theorem w0Kpk_ct_len : w0Kpk.ciphertext.length = 1569 := by
  decide +kernel

private theorem w0PqA0_bounds : 0 < w0PqA0.length ∧ w0PqA0.length ≤ 286196 := by
  decide +kernel

private theorem w0PqA1_bounds : 0 < w0PqA1.length ∧ w0PqA1.length ≤ 286196 := by
  decide +kernel

def w0Sc0 : SenderChain :=
  ⟨w0EphA, ⟨(rootKdf C0.F w0Key0 nzVec32.toList).2, 0#32⟩⟩

def w0RcInit : ReceiverChain :=
  ⟨⟨b0.spkPub⟩, some ⟨w0Key0, 0#32⟩, []⟩

def w0RcPost : ReceiverChain :=
  ⟨⟨b0.spkPub⟩, some w0CkAfter, []⟩

private theorem w0SA0_fields :
    w0SA0.remoteIdentity = some ⟨⟨b0.idPub⟩⟩ ∧
    w0SA0.senderChain = some w0Sc0 ∧
    w0SA0.receiverChains = [w0RcInit] ∧
    w0SA0.pqRatchetState = w0PqA0 ∧
    w0SA0.pendingPreKey = true :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

private theorem w0SA1_fields :
    w0SA1.remoteIdentity = some ⟨⟨b0.idPub⟩⟩ ∧
    w0SA1.senderChain = some w0Sc0 ∧
    w0SA1.receiverChains = [w0RcPost] ∧
    w0SA1.pqRatchetState = w0PqA1 ∧
    w0SA1.pendingPreKey = false :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

private theorem w0_key_deser_facts :
    w0Ses0.aliceBaseKey.length = 33 ∧
    PublicKey.deserialize w0SA0.localIdentity.publicKey.serialize =
      .ok w0SA0.localIdentity.publicKey ∧
    PublicKey.deserialize (⟨⟨b0.idPub⟩⟩ : IdentityKey).publicKey.serialize =
      .ok (⟨⟨b0.idPub⟩⟩ : IdentityKey).publicKey ∧
    PublicKey.deserialize w0Sc0.ratchetKey.publicKey.serialize =
      .ok w0Sc0.ratchetKey.publicKey ∧
    clampScalar w0Sc0.ratchetKey.privateKey.bytes = w0Sc0.ratchetKey.privateKey.bytes ∧
    PublicKey.deserialize w0Ppk.baseKey.serialize = .ok w0Ppk.baseKey ∧
    PublicKey.deserialize (⟨b0.spkPub⟩ : PublicKey).serialize = .ok ⟨b0.spkPub⟩ := by
  decide +kernel

def ghostBase : BitVec 64 := 0x10000#64

def w0PendTail : List (BitVec 8) :=
  (match w0Ppk.preKeyId with
   | none => [0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8]
   | some v => [1#8, 0#8, 0#8, 0#8] ++ leBytes 4 v.toNat) ++
  leBytes 8 w0Ppk.timestamp.toNat ++
  leBytes 4 w0Ppk.signedPreKeyId.toNat ++
  [0#8, 0#8, 0#8, 0#8]

def w0KyberTail : List (BitVec 8) :=
  leBytes 4 w0Kpk.preKeyId.toNat ++ [0#8, 0#8, 0#8, 0#8]

def w0RcGhost : CryptoVerification.LibsignalSessionRepr.ChainGhost where
  srk := ⟨33#64, ghostBase + 896#64, (⟨b0.spkPub⟩ : PublicKey).serialize⟩
  priv := ⟨0#64, 1#64, []⟩
  mkCap := 0#64
  mkPtr := 8#64
  keys := []
  ck := ⟨32#64, ghostBase + 944#64⟩

def w0G0 : SessionGhost where
  localIk := ⟨33#64, ghostBase + 512#64, w0SA0.localIdentity.publicKey.serialize⟩
  remoteIk := ⟨33#64, ghostBase + 560#64, (⟨⟨b0.idPub⟩⟩ : IdentityKey).publicKey.serialize⟩
  root := ⟨32#64, ghostBase + 608#64⟩
  chainsCap := 1#64
  chainsPtr := ghostBase + 352#64
  chains := [w0RcGhost]
  alice := ⟨33#64, ghostBase + 656#64, w0Ses0.aliceBaseKey⟩
  pq := ⟨BitVec.ofNat 64 w0PqA0.length, ghostBase + 4096#64⟩
  sender := some
    { srk := ⟨33#64, ghostBase + 704#64, w0Sc0.ratchetKey.publicKey.serialize⟩
      priv := ⟨32#64, ghostBase + 752#64, w0Sc0.ratchetKey.privateKey.bytes.toList⟩
      mkCap := 0#64
      mkPtr := 8#64
      ck := ⟨32#64, ghostBase + 800#64⟩ }
  pending := some
    { vec := ⟨33#64, ghostBase + 848#64, w0Ppk.baseKey.serialize⟩
      tail := w0PendTail }
  kyber := some
    { vec := ⟨1569#64, ghostBase + 1024#64, w0Kpk.ciphertext⟩
      tail := w0KyberTail }
  regIds :=
    leBytes 4 w0Ses0.remoteRegistrationId.toNat ++
    leBytes 4 w0Ses0.localRegistrationId.toNat

def w0G1 : SessionGhost where
  localIk := ⟨33#64, ghostBase + 512#64, w0SA1.localIdentity.publicKey.serialize⟩
  remoteIk := ⟨33#64, ghostBase + 560#64, (⟨⟨b0.idPub⟩⟩ : IdentityKey).publicKey.serialize⟩
  root := ⟨32#64, ghostBase + 608#64⟩
  chainsCap := 1#64
  chainsPtr := ghostBase + 352#64
  chains := [w0RcGhost]
  alice := ⟨33#64, ghostBase + 656#64, w0Ses1.aliceBaseKey⟩
  pq := ⟨BitVec.ofNat 64 w0PqA1.length, ghostBase + 4096#64⟩
  sender := some
    { srk := ⟨33#64, ghostBase + 704#64, w0Sc0.ratchetKey.publicKey.serialize⟩
      priv := ⟨32#64, ghostBase + 752#64, w0Sc0.ratchetKey.privateKey.bytes.toList⟩
      mkCap := 0#64
      mkPtr := 8#64
      ck := ⟨32#64, ghostBase + 800#64⟩ }
  pending := none
  kyber := none
  regIds :=
    leBytes 4 w0Ses1.remoteRegistrationId.toNat ++
    leBytes 4 w0Ses1.localRegistrationId.toNat

private theorem w0G0_modelRel : sessionModelRel w0G0 w0Ses0 := by
  have hf := w0_key_deser_facts
  have hp_none : w0Ppk.preKeyId = none := by decide +kernel
  have hp_opt : OptU32Rel w0PendTail w0Ppk.preKeyId := by
    unfold w0PendTail; rw [hp_none]; rfl
  unfold sessionModelRel
  rw [w0Ses0_pendingPreKey_eq, w0Ses0_pendingKyber_eq]
  unfold w0G0
  refine ⟨?_, ?_, rfl, by decide +kernel, by decide +kernel⟩
  · unfold PendingRel
    exact ⟨hf.2.2.2.2.2.1, hp_opt, by decide +kernel, by decide +kernel, by decide +kernel⟩
  · unfold KyberRel
    exact ⟨rfl, by decide +kernel⟩

private theorem w0G1_modelRel : sessionModelRel w0G1 w0Ses1 := by
  unfold sessionModelRel w0Ses1 w0G1
  exact ⟨trivial, trivial, rfl, by decide +kernel, by decide +kernel⟩

private def MemHas (P : SepProp) : Prop :=
  ∃ m : Memory, m ⊨ P

private theorem memHas_init :
    MemHas (memRegion (ghostBase + BitVec.ofNat 64 0) 524288 ∗ emp) := by
  let m0 : Memory :=
    Memory.ofFn (fun _ => 0#8)
      (fun a => if (a - ghostBase).toNat < 524288 then some Perm.rw else none)
  have hrw : m0.RW ghostBase 524288 := by
    intro a ha
    unfold InRegion at ha
    rw [Memory.permNoLazy_eq_some_rw_iff]
    simp only [m0, Memory.perm_ofFn, Memory.isLazyFree_ofFn, ha, ↓reduceIte]
    exact ⟨rfl, rfl⟩
  refine ⟨m0, ?_⟩
  rw [BitVec.add_zero, sepConj_emp]
  exact satisfies_memRegion m0 ghostBase 524288 hrw

private theorem MemHas.stepBytes {off off' rem' rem : Nat} {R : SepProp}
    (k : Nat) (bs : List (BitVec 8)) (hlen : bs.length = k)
    (h : MemHas (memRegion (ghostBase + BitVec.ofNat 64 off) rem ∗ R))
    (hc : decide (off + k = off' ∧ k + rem' = rem ∧ rem ≤ 2 ^ 64) = true := by decide) :
    MemHas (memRegion (ghostBase + BitVec.ofNat 64 off') rem' ∗
      (((ghostBase + BitVec.ofNat 64 off) ↦ₛ bs) ∗ R)) := by
  rcases h with ⟨m, hsat⟩
  have ⟨_, _, hle⟩ := of_decide_eq_true hc
  have hbs_le : bs.length ≤ 2 ^ 64 := by omega
  rw [split_arena_region ghostBase hc, sepConj_assoc, ← hlen] at hsat
  refine ⟨m.writeBytes (ghostBase + BitVec.ofNat 64 off) bs, ?_⟩
  have hw := satisfies_writeBytes bs hbs_le hsat
  rwa [sepConj_left_comm] at hw

private theorem MemHas.step64 {off off' rem' rem : Nat} {R : SepProp}
    (v : BitVec 64)
    (h : MemHas (memRegion (ghostBase + BitVec.ofNat 64 off) rem ∗ R))
    (hc : decide (off + 8 = off' ∧ 8 + rem' = rem ∧ rem ≤ 2 ^ 64) = true := by decide) :
    MemHas (memRegion (ghostBase + BitVec.ofNat 64 off') rem' ∗
      (((ghostBase + BitVec.ofNat 64 off) ↦₆₄ v) ∗ R)) := by
  rw [CryptoVerification.LibsignalSession.NonVacuityWitness.pointsTo64_eq_pointsToBytes]
  exact h.stepBytes 8 (bytesOf64 v) rfl hc

private theorem pointsTo32_eq_pointsToBytes (a : BitVec 64) (v : BitVec 32) :
    (a ↦₃₂ v) = (a ↦ₛ bytesOf32 v) := by
  unfold pointsTo32 bytesOf32
  simp only [pointsToBytes_cons, pointsToBytes_nil,
    BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp]

private theorem MemHas.step32 {off off' rem' rem : Nat} {R : SepProp}
    (v : BitVec 32)
    (h : MemHas (memRegion (ghostBase + BitVec.ofNat 64 off) rem ∗ R))
    (hc : decide (off + 4 = off' ∧ 4 + rem' = rem ∧ rem ≤ 2 ^ 64) = true := by decide) :
    MemHas (memRegion (ghostBase + BitVec.ofNat 64 off') rem' ∗
      (((ghostBase + BitVec.ofNat 64 off) ↦₃₂ v) ∗ R)) := by
  rw [pointsTo32_eq_pointsToBytes]
  exact h.stepBytes 4 (bytesOf32 v) rfl hc

private theorem MemHas.stepSkip {off off' rem' rem : Nat} {R : SepProp}
    (k : Nat)
    (h : MemHas (memRegion (ghostBase + BitVec.ofNat 64 off) rem ∗ R))
    (hc : decide (off + k = off' ∧ k + rem' = rem ∧ rem ≤ 2 ^ 64) = true := by decide) :
    MemHas (memRegion (ghostBase + BitVec.ofNat 64 off') rem' ∗
      (memRegion (ghostBase + BitVec.ofNat 64 off) k ∗ R)) := by
  rcases h with ⟨m, hsat⟩
  rw [split_arena_region ghostBase hc, sepConj_assoc, sepConj_left_comm] at hsat
  exact ⟨m, hsat⟩

private theorem vecU8At_A0_exact (v ptr : BitVec 64) (k : Nat) (bs : List (BitVec 8))
    (hlen : bs.length = k) (hpos : 0 < k) (hlt : k < 2 ^ 63) (hptr : ptr ≠ 0) :
    vecU8At A₀ v (BitVec.ofNat 64 k) ptr bs =
      (v ↦₆₄ BitVec.ofNat 64 k) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 k) ∗ (ptr ↦ₛ bs) := by
  have hmod : (BitVec.ofNat 64 k).toNat = k := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_ne : ¬ (BitVec.ofNat 64 k = 0) := by
    intro hz
    have := congrArg BitVec.toNat hz
    rw [hmod] at this
    change k = 0 at this
    omega
  unfold vecU8At vecHeader A₀
  simp only [hlen, hmod, hlt, true_and, Nat.sub_self, memRegion_zero, emp_sepConj, sepConj_emp,
    hcap_ne, ↓reduceIte]
  have hpure : (k ≤ k ∧ ptr ≠ 0) ↔ True := iff_true_intro ⟨Nat.le_refl k, hptr⟩
  rw [propext hpure, pure_true, emp_sepConj]
  sep_ac_rfl

private theorem vecU8At_A0_empty (v : BitVec 64) :
    vecU8At A₀ v 0#64 1#64 [] =
      (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64) := by
  unfold vecU8At vecHeader
  simp only [List.length_nil, BitVec.ofNat_eq_ofNat, true_and,
    show (0#64 : BitVec 64).toNat < 2 ^ 63 by decide, ↓reduceIte, sepConj_emp]
  have hpure : (0 ≤ (0#64 : BitVec 64).toNat ∧ (1#64 : BitVec 64) ≠ 0#64) ↔ True := by decide
  rw [propext hpure, pure_true, sepConj_emp]

private theorem vecAt_A0_empty {α : Type} (elemAt : α → BitVec 64 → SepProp) (v : BitVec 64) :
    vecAt A₀ 104 8 elemAt v 0#64 8#64 [] =
      (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 8#64) ∗ ((v + 16#64) ↦₆₄ 0#64) := by
  unfold vecAt vecHeader vecBuf
  simp only [List.length_nil, BitVec.ofNat_eq_ofNat, true_and,
    show (0#64 : BitVec 64).toNat * 104 < 2 ^ 63 by decide, ↓reduceIte, sepConj_emp]
  have hpure : (0 ≤ (0#64 : BitVec 64).toNat ∧ (8#64 : BitVec 64) ≠ 0#64) ↔ True := by decide
  rw [propext hpure, pure_true, sepConj_emp]

private theorem vecAt_A0_singleton {α : Type} (elemAt : α → BitVec 64 → SepProp)
    (v ptr : BitVec 64) (x : α) (hptr : ptr ≠ 0#64) :
    vecAt A₀ 104 8 elemAt v 1#64 ptr [x] =
      (v ↦₆₄ 1#64) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ 1#64) ∗ elemAt x ptr := by
  unfold vecAt vecHeader vecBuf A₀ arrayAt
  simp only [List.length_singleton, BitVec.ofNat_eq_ofNat, true_and,
    show (1#64 : BitVec 64).toNat * 104 < 2 ^ 63 by decide,
    show ((1#64 : BitVec 64).toNat - 1) * 104 = 0 by decide,
    memRegion_zero, emp_sepConj, sepConj_emp]
  have hpure : (1 ≤ (1#64 : BitVec 64).toNat ∧ ptr ≠ 0#64) ↔ True :=
    iff_true_intro ⟨by decide, hptr⟩
  have hif : ¬ ((1#64 : BitVec 64) = 0#64) := by decide
  rw [propext hpure, pure_true, emp_sepConj]
  simp only [hif, ↓reduceIte]
  unfold arrayAt
  rw [sepConj_emp]
  sep_ac_rfl

theorem w0G0_sessionGhostValid : SessionGhostValid w0G0 w0Ses0 := by
  refine ⟨w0G0_modelRel, A₀, ghostBase, ?_⟩
  rw [w0Ses0_state_eq]
  have hf := w0_key_deser_facts
  have hpq_bounds := w0PqA0_bounds
  let pqLen := w0PqA0.length
  let pqCap := BitVec.ofNat 64 pqLen
  have h0 := memHas_init
  have s1 := h0.step64 (off' := 8) (rem' := 524280) 33#64
  have s2 := s1.step64 (off' := 16) (rem' := 524272) (ghostBase + 512#64)
  have s3 := s2.step64 (off' := 24) (rem' := 524264) 33#64
  have s4 := s3.step64 (off' := 32) (rem' := 524256) 33#64
  have s5 := s4.step64 (off' := 40) (rem' := 524248) (ghostBase + 560#64)
  have s6 := s5.step64 (off' := 48) (rem' := 524240) 33#64
  have s7 := s6.step64 (off' := 56) (rem' := 524232) 32#64
  have s8 := s7.step64 (off' := 64) (rem' := 524224) (ghostBase + 608#64)
  have s9 := s8.step64 (off' := 72) (rem' := 524216) 32#64
  have s10 := s9.step64 (off' := 80) (rem' := 524208) 1#64
  have s11 := s10.step64 (off' := 88) (rem' := 524200) (ghostBase + 352#64)
  have s12 := s11.step64 (off' := 96) (rem' := 524192) 1#64
  have s13 := s12.step64 (off' := 104) (rem' := 524184) 33#64
  have s14 := s13.step64 (off' := 112) (rem' := 524176) (ghostBase + 656#64)
  have s15 := s14.step64 (off' := 120) (rem' := 524168) 33#64
  have s16 := s15.step64 (off' := 128) (rem' := 524160) pqCap
  have s17 := s16.step64 (off' := 136) (rem' := 524152) (ghostBase + 4096#64)
  have s18 := s17.step64 (off' := 144) (rem' := 524144) pqCap
  have s19 := s18.step64 (off' := 152) (rem' := 524136) 33#64
  have s20 := s19.step64 (off' := 160) (rem' := 524128) (ghostBase + 704#64)
  have s21 := s20.step64 (off' := 168) (rem' := 524120) 33#64
  have s22 := s21.step64 (off' := 176) (rem' := 524112) 32#64
  have s23 := s22.step64 (off' := 184) (rem' := 524104) (ghostBase + 752#64)
  have s24 := s23.step64 (off' := 192) (rem' := 524096) 32#64
  have s25 := s24.step64 (off' := 200) (rem' := 524088) 0#64
  have s26 := s25.step64 (off' := 208) (rem' := 524080) 8#64
  have s27 := s26.step64 (off' := 216) (rem' := 524072) 0#64
  have s28 := s27.step64 (off' := 224) (rem' := 524064) 32#64
  have s29 := s28.step64 (off' := 232) (rem' := 524056) (ghostBase + 800#64)
  have s30 := s29.step64 (off' := 240) (rem' := 524048) 32#64
  have s31 := s30.step32 (off' := 244) (rem' := 524044) w0Sc0.chainKey.index
  have s32 := s31.stepSkip (off' := 248) (rem' := 524040) 4
  have s33 := s32.step64 (off' := 256) (rem' := 524032) 33#64
  have s34 := s33.step64 (off' := 264) (rem' := 524024) (ghostBase + 848#64)
  have s35 := s34.step64 (off' := 272) (rem' := 524016) 33#64
  have s36 := s35.stepBytes (off' := 296) (rem' := 523992) 24 w0PendTail (by decide +kernel)
  have s37 := s36.step64 (off' := 304) (rem' := 523984) 1569#64
  have s38 := s37.step64 (off' := 312) (rem' := 523976) (ghostBase + 1024#64)
  have s39 := s38.step64 (off' := 320) (rem' := 523968) 1569#64
  have s40 := s39.stepBytes (off' := 328) (rem' := 523960) 8 w0KyberTail (by decide +kernel)
  have s41 := s40.step32 (off' := 332) (rem' := 523956) w0SA0.sessionVersion
  have s42 := s41.step32 (off' := 336) (rem' := 523952) w0SA0.previousCounter
  have s43 := s42.stepBytes (off' := 344) (rem' := 523944) 8 w0G0.regIds (by decide +kernel)
  have rc0_pad := s43.stepSkip (off' := 352) (rem' := 523936) 8
  have rc1 := rc0_pad.step64 (off' := 360) (rem' := 523928) 33#64
  have rc2 := rc1.step64 (off' := 368) (rem' := 523920) (ghostBase + 896#64)
  have rc3 := rc2.step64 (off' := 376) (rem' := 523912) 33#64
  have rc4 := rc3.step64 (off' := 384) (rem' := 523904) 0#64
  have rc5 := rc4.step64 (off' := 392) (rem' := 523896) 1#64
  have rc6 := rc5.step64 (off' := 400) (rem' := 523888) 0#64
  have rc7 := rc6.step64 (off' := 408) (rem' := 523880) 0#64
  have rc8 := rc7.step64 (off' := 416) (rem' := 523872) 8#64
  have rc9 := rc8.step64 (off' := 424) (rem' := 523864) 0#64
  have rc10 := rc9.step64 (off' := 432) (rem' := 523856) 32#64
  have rc11 := rc10.step64 (off' := 440) (rem' := 523848) (ghostBase + 944#64)
  have rc12 := rc11.step64 (off' := 448) (rem' := 523840) 32#64
  have rc13 := rc12.step32 (off' := 452) (rem' := 523836) 0#32
  have rc14 := rc13.stepSkip (off' := 456) (rem' := 523832) 4
  have h1 := rc14.stepSkip (off' := 512) (rem' := 523776) 56
  have h2 := h1.stepBytes (off' := 545) (rem' := 523743) 33
    w0SA0.localIdentity.publicKey.serialize (by decide +kernel)
  have h3 := h2.stepSkip (off' := 560) (rem' := 523728) 15
  have h4 := h3.stepBytes (off' := 593) (rem' := 523695) 33
    (⟨⟨b0.idPub⟩⟩ : IdentityKey).publicKey.serialize (by decide +kernel)
  have h5 := h4.stepSkip (off' := 608) (rem' := 523680) 15
  have h6 := h5.stepBytes (off' := 640) (rem' := 523648) 32
    (keyToBytes32 w0SA0.rootKey) (by simp [keyToBytes32])
  have h7 := h6.stepSkip (off' := 656) (rem' := 523632) 16
  have h8 := h7.stepBytes (off' := 689) (rem' := 523599) 33 w0Ses0.aliceBaseKey hf.1
  have h9 := h8.stepSkip (off' := 704) (rem' := 523584) 15
  have h10 := h9.stepBytes (off' := 737) (rem' := 523551) 33
    w0Sc0.ratchetKey.publicKey.serialize (by decide +kernel)
  have h11 := h10.stepSkip (off' := 752) (rem' := 523536) 15
  have h12 := h11.stepBytes (off' := 784) (rem' := 523504) 32
    w0Sc0.ratchetKey.privateKey.bytes.toList w0Sc0.ratchetKey.privateKey.bytes.toList_length
  have h13 := h12.stepSkip (off' := 800) (rem' := 523488) 16
  have h14 := h13.stepBytes (off' := 832) (rem' := 523456) 32
    (keyToBytes32 w0Sc0.chainKey.key) (by simp [keyToBytes32])
  have h15 := h14.stepSkip (off' := 848) (rem' := 523440) 16
  have h16 := h15.stepBytes (off' := 881) (rem' := 523407) 33
    w0Ppk.baseKey.serialize (by decide +kernel)
  have h16a := h16.stepSkip (off' := 896) (rem' := 523392) 15
  have h16b := h16a.stepBytes (off' := 929) (rem' := 523359) 33
    (⟨b0.spkPub⟩ : PublicKey).serialize (by decide +kernel)
  have h16c := h16b.stepSkip (off' := 944) (rem' := 523344) 15
  have h16d := h16c.stepBytes (off' := 976) (rem' := 523312) 32
    (keyToBytes32 w0Key0) (by simp [keyToBytes32])
  have h17 := h16d.stepSkip (off' := 1024) (rem' := 523264) 48
  have h18 := h17.stepBytes (off' := 2593) (rem' := 521695) 1569 w0Kpk.ciphertext w0Kpk_ct_len
  have h19 := h18.stepSkip (off' := 4096) (rem' := 520192) 1503
  have hc_pq : decide (4096 + pqLen = 4096 + pqLen ∧
      pqLen + (520192 - pqLen) = 520192 ∧ 520192 ≤ 2 ^ 64) = true :=
    decide_eq_true ⟨rfl, by have := hpq_bounds.2; omega, by decide⟩
  have h20 := h19.stepBytes (off' := 4096 + pqLen) (rem' := 520192 - pqLen) pqLen
    w0PqA0 rfl hc_pq
  rcases h20 with ⟨m, hsat⟩
  have hpure_ss :
      (PublicKey.deserialize w0G0.localIk.bytes = .ok w0SA0.localIdentity.publicKey ∧
        PublicKey.deserialize w0G0.remoteIk.bytes = .ok (⟨⟨b0.idPub⟩⟩ : IdentityKey).publicKey ∧
        w0G0.chains.length = w0SA0.receiverChains.length ∧
        w0G0.pending.isSome = w0SA0.pendingPreKey ∧
        w0G0.regIds.length = 8 ∧
        w0G0.localIk.bytes.length = 33 ∧
        ((some (⟨⟨b0.idPub⟩⟩ : IdentityKey)).isSome = true → w0G0.remoteIk.bytes.length = 33)) ↔
      True := by
    rw [w0SA0_fields.2.2.1, w0SA0_fields.2.2.2.2]
    exact iff_true_intro ⟨hf.2.1, hf.2.2.1, rfl, rfl,
      by decide +kernel, by decide +kernel, fun _ => by decide +kernel⟩
  have hpure_rc :
      (PublicKey.deserialize w0RcGhost.srk.bytes = .ok w0RcInit.senderRatchetKey ∧
        w0RcInit.messageKeys.length ≤ maxMessageKeys ∧
        w0RcGhost.keys.length = w0RcInit.messageKeys.length ∧
        w0RcGhost.srk.bytes.length = 33 ∧
        w0RcGhost.priv.bytes = []) ↔ True :=
    iff_true_intro ⟨hf.2.2.2.2.2.2, Nat.zero_le _, rfl, by decide +kernel, rfl⟩
  have hloc_v := vecU8At_A0_exact ghostBase (ghostBase + 512#64) 33
    w0SA0.localIdentity.publicKey.serialize (by decide +kernel) (by decide) (by decide) (by decide)
  have hrem_v := vecU8At_A0_exact (ghostBase + 24#64) (ghostBase + 560#64) 33
    (⟨⟨b0.idPub⟩⟩ : IdentityKey).publicKey.serialize (by decide +kernel) (by decide) (by decide) (by decide)
  have hroot_v := vecU8At_A0_exact (ghostBase + 48#64) (ghostBase + 608#64) 32
    (keyToBytes32 w0SA0.rootKey) (by simp [keyToBytes32]) (by decide) (by decide) (by decide)
  have hrc_v := vecAt_A0_singleton (chainAt A₀) (ghostBase + 72#64) (ghostBase + 352#64)
    (w0RcGhost, w0RcInit) (by decide)
  have hrc_srk_v := vecU8At_A0_exact (ghostBase + 352#64) (ghostBase + 896#64) 33
    (⟨b0.spkPub⟩ : PublicKey).serialize (by decide +kernel) (by decide) (by decide) (by decide)
  have hrc_priv_v := vecU8At_A0_empty (ghostBase + 376#64)
  have hrc_mk_v := vecAt_A0_empty (messageKeyAt A₀) (ghostBase + 400#64)
  have hrc_ck_v := vecU8At_A0_exact (ghostBase + 424#64) (ghostBase + 944#64) 32
    (keyToBytes32 w0Key0) (by simp [keyToBytes32]) (by decide) (by decide) (by decide)
  have halice_v := vecU8At_A0_exact (ghostBase + 96#64) (ghostBase + 656#64) 33
    w0Ses0.aliceBaseKey hf.1 (by decide) (by decide) (by decide)
  have hpq_v := vecU8At_A0_exact (ghostBase + 120#64) (ghostBase + 4096#64) pqLen
    w0PqA0 rfl hpq_bounds.1 (by have := hpq_bounds.2; omega) (by decide)
  have hsrk_v := vecU8At_A0_exact (ghostBase + 144#64) (ghostBase + 704#64) 33
    w0Sc0.ratchetKey.publicKey.serialize (by decide +kernel) (by decide) (by decide) (by decide)
  have hpriv_v := vecU8At_A0_exact (ghostBase + 168#64) (ghostBase + 752#64) 32
    w0Sc0.ratchetKey.privateKey.bytes.toList
    w0Sc0.ratchetKey.privateKey.bytes.toList_length (by decide) (by decide) (by decide)
  have hsmk_v := vecAt_A0_empty (messageKeyAt A₀) (ghostBase + 192#64)
  have hsck_v := vecU8At_A0_exact (ghostBase + 216#64) (ghostBase + 800#64) 32
    (keyToBytes32 w0Sc0.chainKey.key) (by simp [keyToBytes32]) (by decide) (by decide) (by decide)
  have hpend_v := vecU8At_A0_exact (ghostBase + 248#64) (ghostBase + 848#64) 33
    w0Ppk.baseKey.serialize (by decide +kernel) (by decide) (by decide) (by decide)
  have hkyb_v := vecU8At_A0_exact (ghostBase + 296#64) (ghostBase + 1024#64) 1569
    w0Kpk.ciphertext w0Kpk_ct_len (by decide) (by decide) (by decide)
  have hpure_sc :
      (PublicKey.deserialize w0Sc0.ratchetKey.publicKey.serialize = .ok w0Sc0.ratchetKey.publicKey ∧
        True ∧
        clampScalar w0Sc0.ratchetKey.privateKey.bytes = w0Sc0.ratchetKey.privateKey.bytes ∧
        w0Sc0.ratchetKey.publicKey.serialize.length = 33) ↔ True :=
    iff_true_intro ⟨hf.2.2.2.1, trivial, hf.2.2.2.2.1, by decide +kernel⟩
  have hpure_pt : (w0PendTail.length = 48 - 24) ↔ True := iff_true_intro (by decide +kernel)
  have hpure_kt : (w0KyberTail.length = 32 - 24) ↔ True := iff_true_intro (by decide +kernel)
  let Rframe : SepProp :=
    memRegion (ghostBase + BitVec.ofNat 64 (4096 + pqLen)) (520192 - pqLen) ∗
    memRegion (ghostBase + 344#64) 8 ∗
    memRegion (ghostBase + 456#64) 56 ∗
    memRegion (ghostBase + 545#64) 15 ∗
    memRegion (ghostBase + 593#64) 15 ∗
    memRegion (ghostBase + 640#64) 16 ∗
    memRegion (ghostBase + 689#64) 15 ∗
    memRegion (ghostBase + 737#64) 15 ∗
    memRegion (ghostBase + 784#64) 16 ∗
    memRegion (ghostBase + 832#64) 16 ∗
    memRegion (ghostBase + 881#64) 15 ∗
    memRegion (ghostBase + 929#64) 15 ∗
    memRegion (ghostBase + 976#64) 48 ∗
    memRegion (ghostBase + 2593#64) 1503
  refine ⟨m, Rframe, ?_⟩
  unfold sessionStateAt
  rw [w0SA0_fields.1]
  dsimp only
  rw [propext hpure_ss, pure_true, emp_sepConj]
  dsimp only [w0G0, vecGhostAt]
  rw [w0SA0_fields.2.2.1, w0SA0_fields.2.1, w0SA0_fields.2.2.2.1]
  simp only [List.zip_cons_cons, List.zip_nil_right, optSenderChainAt, optChainKeyAt, optTailVecAt,
    BitVec.add_assoc, BitVec.reduceAdd]
  rw [propext hpure_sc, propext hpure_pt, propext hpure_kt]
  simp only [pure_true, emp_sepConj]
  rw [hrc_v]
  unfold chainAt
  rw [propext hpure_rc, pure_true, emp_sepConj]
  dsimp only [w0RcGhost, w0RcInit, vecGhostAt]
  simp only [List.zip_nil_right, optChainKeyAt, BitVec.add_assoc,
    BitVec.reduceAdd]
  rw [hloc_v, hrem_v, hroot_v, hrc_srk_v, hrc_priv_v, hrc_mk_v, hrc_ck_v,
    halice_v, hpq_v, hsrk_v, hpriv_v, hsmk_v, hsck_v, hpend_v, hkyb_v]
  simp only [BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd,
    sepConj_emp] at hsat ⊢
  refine Eq.mp (congrArg (fun P => m ⊨ P) ?_) hsat
  dsimp only [Rframe]
  sep_ac_rfl

theorem w0G1_sessionGhostValid : SessionGhostValid w0G1 w0Ses1 := by
  refine ⟨w0G1_modelRel, A₀, ghostBase, ?_⟩
  have hf := w0_key_deser_facts
  have hpq_bounds := w0PqA1_bounds
  let pqLen := w0PqA1.length
  let pqCap := BitVec.ofNat 64 pqLen
  have h0 := memHas_init
  have s1 := h0.step64 (off' := 8) (rem' := 524280) 33#64
  have s2 := s1.step64 (off' := 16) (rem' := 524272) (ghostBase + 512#64)
  have s3 := s2.step64 (off' := 24) (rem' := 524264) 33#64
  have s4 := s3.step64 (off' := 32) (rem' := 524256) 33#64
  have s5 := s4.step64 (off' := 40) (rem' := 524248) (ghostBase + 560#64)
  have s6 := s5.step64 (off' := 48) (rem' := 524240) 33#64
  have s7 := s6.step64 (off' := 56) (rem' := 524232) 32#64
  have s8 := s7.step64 (off' := 64) (rem' := 524224) (ghostBase + 608#64)
  have s9 := s8.step64 (off' := 72) (rem' := 524216) 32#64
  have s10 := s9.step64 (off' := 80) (rem' := 524208) 1#64
  have s11 := s10.step64 (off' := 88) (rem' := 524200) (ghostBase + 352#64)
  have s12 := s11.step64 (off' := 96) (rem' := 524192) 1#64
  have s13 := s12.step64 (off' := 104) (rem' := 524184) 33#64
  have s14 := s13.step64 (off' := 112) (rem' := 524176) (ghostBase + 656#64)
  have s15 := s14.step64 (off' := 120) (rem' := 524168) 33#64
  have s16 := s15.step64 (off' := 128) (rem' := 524160) pqCap
  have s17 := s16.step64 (off' := 136) (rem' := 524152) (ghostBase + 4096#64)
  have s18 := s17.step64 (off' := 144) (rem' := 524144) pqCap
  have s19 := s18.step64 (off' := 152) (rem' := 524136) 33#64
  have s20 := s19.step64 (off' := 160) (rem' := 524128) (ghostBase + 704#64)
  have s21 := s20.step64 (off' := 168) (rem' := 524120) 33#64
  have s22 := s21.step64 (off' := 176) (rem' := 524112) 32#64
  have s23 := s22.step64 (off' := 184) (rem' := 524104) (ghostBase + 752#64)
  have s24 := s23.step64 (off' := 192) (rem' := 524096) 32#64
  have s25 := s24.step64 (off' := 200) (rem' := 524088) 0#64
  have s26 := s25.step64 (off' := 208) (rem' := 524080) 8#64
  have s27 := s26.step64 (off' := 216) (rem' := 524072) 0#64
  have s28 := s27.step64 (off' := 224) (rem' := 524064) 32#64
  have s29 := s28.step64 (off' := 232) (rem' := 524056) (ghostBase + 800#64)
  have s30 := s29.step64 (off' := 240) (rem' := 524048) 32#64
  have s31 := s30.step32 (off' := 244) (rem' := 524044) w0Sc0.chainKey.index
  have s32 := s31.stepSkip (off' := 248) (rem' := 524040) 4
  -- `248..296`: `pending = none` (`noneCap` + `40` B skip)
  have s33 := s32.step64 (off' := 256) (rem' := 524032) noneCap
  have s34 := s33.stepSkip (off' := 296) (rem' := 523992) 40
  -- `296..328`: `kyber = none` (`noneCap` + `24` B skip)
  have s35 := s34.step64 (off' := 304) (rem' := 523984) noneCap
  have s36 := s35.stepSkip (off' := 328) (rem' := 523960) 24
  have s41 := s36.step32 (off' := 332) (rem' := 523956) w0SA1.sessionVersion
  have s42 := s41.step32 (off' := 336) (rem' := 523952) w0SA1.previousCounter
  have s43 := s42.stepBytes (off' := 344) (rem' := 523944) 8 w0G1.regIds (by decide +kernel)
  have rc0_pad := s43.stepSkip (off' := 352) (rem' := 523936) 8
  have rc1 := rc0_pad.step64 (off' := 360) (rem' := 523928) 33#64
  have rc2 := rc1.step64 (off' := 368) (rem' := 523920) (ghostBase + 896#64)
  have rc3 := rc2.step64 (off' := 376) (rem' := 523912) 33#64
  have rc4 := rc3.step64 (off' := 384) (rem' := 523904) 0#64
  have rc5 := rc4.step64 (off' := 392) (rem' := 523896) 1#64
  have rc6 := rc5.step64 (off' := 400) (rem' := 523888) 0#64
  have rc7 := rc6.step64 (off' := 408) (rem' := 523880) 0#64
  have rc8 := rc7.step64 (off' := 416) (rem' := 523872) 8#64
  have rc9 := rc8.step64 (off' := 424) (rem' := 523864) 0#64
  have rc10 := rc9.step64 (off' := 432) (rem' := 523856) 32#64
  have rc11 := rc10.step64 (off' := 440) (rem' := 523848) (ghostBase + 944#64)
  have rc12 := rc11.step64 (off' := 448) (rem' := 523840) 32#64
  have rc13 := rc12.step32 (off' := 452) (rem' := 523836) w0CkAfter.index
  have rc14 := rc13.stepSkip (off' := 456) (rem' := 523832) 4
  have h1 := rc14.stepSkip (off' := 512) (rem' := 523776) 56
  have h2 := h1.stepBytes (off' := 545) (rem' := 523743) 33
    w0SA1.localIdentity.publicKey.serialize (by decide +kernel)
  have h3 := h2.stepSkip (off' := 560) (rem' := 523728) 15
  have h4 := h3.stepBytes (off' := 593) (rem' := 523695) 33
    (⟨⟨b0.idPub⟩⟩ : IdentityKey).publicKey.serialize (by decide +kernel)
  have h5 := h4.stepSkip (off' := 608) (rem' := 523680) 15
  have h6 := h5.stepBytes (off' := 640) (rem' := 523648) 32
    (keyToBytes32 w0SA1.rootKey) (by simp [keyToBytes32])
  have h7 := h6.stepSkip (off' := 656) (rem' := 523632) 16
  have h8 := h7.stepBytes (off' := 689) (rem' := 523599) 33 w0Ses1.aliceBaseKey hf.1
  have h9 := h8.stepSkip (off' := 704) (rem' := 523584) 15
  have h10 := h9.stepBytes (off' := 737) (rem' := 523551) 33
    w0Sc0.ratchetKey.publicKey.serialize (by decide +kernel)
  have h11 := h10.stepSkip (off' := 752) (rem' := 523536) 15
  have h12 := h11.stepBytes (off' := 784) (rem' := 523504) 32
    w0Sc0.ratchetKey.privateKey.bytes.toList w0Sc0.ratchetKey.privateKey.bytes.toList_length
  have h13 := h12.stepSkip (off' := 800) (rem' := 523488) 16
  have h14 := h13.stepBytes (off' := 832) (rem' := 523456) 32
    (keyToBytes32 w0Sc0.chainKey.key) (by simp [keyToBytes32])
  have h15 := h14.stepSkip (off' := 896) (rem' := 523392) 64
  have h16b := h15.stepBytes (off' := 929) (rem' := 523359) 33
    (⟨b0.spkPub⟩ : PublicKey).serialize (by decide +kernel)
  have h16c := h16b.stepSkip (off' := 944) (rem' := 523344) 15
  have h16d := h16c.stepBytes (off' := 976) (rem' := 523312) 32
    (keyToBytes32 w0CkAfter.key) (by simp [keyToBytes32])
  have h17 := h16d.stepSkip (off' := 4096) (rem' := 520192) 3120
  have hc_pq : decide (4096 + pqLen = 4096 + pqLen ∧
      pqLen + (520192 - pqLen) = 520192 ∧ 520192 ≤ 2 ^ 64) = true :=
    decide_eq_true ⟨rfl, by have := hpq_bounds.2; omega, by decide⟩
  have h20 := h17.stepBytes (off' := 4096 + pqLen) (rem' := 520192 - pqLen) pqLen
    w0PqA1 rfl hc_pq
  rcases h20 with ⟨m, hsat⟩
  have hpure_ss :
      (PublicKey.deserialize w0G1.localIk.bytes = .ok w0SA1.localIdentity.publicKey ∧
        PublicKey.deserialize w0G1.remoteIk.bytes = .ok (⟨⟨b0.idPub⟩⟩ : IdentityKey).publicKey ∧
        w0G1.chains.length = w0SA1.receiverChains.length ∧
        w0G1.pending.isSome = w0SA1.pendingPreKey ∧
        w0G1.regIds.length = 8 ∧
        w0G1.localIk.bytes.length = 33 ∧
        ((some (⟨⟨b0.idPub⟩⟩ : IdentityKey)).isSome = true → w0G1.remoteIk.bytes.length = 33)) ↔
      True := by
    rw [w0SA1_fields.2.2.1, w0SA1_fields.2.2.2.2]
    exact iff_true_intro ⟨hf.2.1, hf.2.2.1, rfl, rfl,
      by decide +kernel, by decide +kernel, fun _ => by decide +kernel⟩
  have hpure_rc :
      (PublicKey.deserialize w0RcGhost.srk.bytes = .ok w0RcPost.senderRatchetKey ∧
        w0RcPost.messageKeys.length ≤ maxMessageKeys ∧
        w0RcGhost.keys.length = w0RcPost.messageKeys.length ∧
        w0RcGhost.srk.bytes.length = 33 ∧
        w0RcGhost.priv.bytes = []) ↔ True :=
    iff_true_intro ⟨hf.2.2.2.2.2.2, Nat.zero_le _, rfl, by decide +kernel, rfl⟩
  have hloc_v := vecU8At_A0_exact ghostBase (ghostBase + 512#64) 33
    w0SA1.localIdentity.publicKey.serialize (by decide +kernel) (by decide) (by decide) (by decide)
  have hrem_v := vecU8At_A0_exact (ghostBase + 24#64) (ghostBase + 560#64) 33
    (⟨⟨b0.idPub⟩⟩ : IdentityKey).publicKey.serialize (by decide +kernel) (by decide) (by decide) (by decide)
  have hroot_v := vecU8At_A0_exact (ghostBase + 48#64) (ghostBase + 608#64) 32
    (keyToBytes32 w0SA1.rootKey) (by simp [keyToBytes32]) (by decide) (by decide) (by decide)
  have hrc_v := vecAt_A0_singleton (chainAt A₀) (ghostBase + 72#64) (ghostBase + 352#64)
    (w0RcGhost, w0RcPost) (by decide)
  have hrc_srk_v := vecU8At_A0_exact (ghostBase + 352#64) (ghostBase + 896#64) 33
    (⟨b0.spkPub⟩ : PublicKey).serialize (by decide +kernel) (by decide) (by decide) (by decide)
  have hrc_priv_v := vecU8At_A0_empty (ghostBase + 376#64)
  have hrc_mk_v := vecAt_A0_empty (messageKeyAt A₀) (ghostBase + 400#64)
  have hrc_ck_v := vecU8At_A0_exact (ghostBase + 424#64) (ghostBase + 944#64) 32
    (keyToBytes32 w0CkAfter.key) (by simp [keyToBytes32]) (by decide) (by decide) (by decide)
  have halice_v := vecU8At_A0_exact (ghostBase + 96#64) (ghostBase + 656#64) 33
    w0Ses1.aliceBaseKey hf.1 (by decide) (by decide) (by decide)
  have hpq_v := vecU8At_A0_exact (ghostBase + 120#64) (ghostBase + 4096#64) pqLen
    w0PqA1 rfl hpq_bounds.1 (by have := hpq_bounds.2; omega) (by decide)
  have hsrk_v := vecU8At_A0_exact (ghostBase + 144#64) (ghostBase + 704#64) 33
    w0Sc0.ratchetKey.publicKey.serialize (by decide +kernel) (by decide) (by decide) (by decide)
  have hpriv_v := vecU8At_A0_exact (ghostBase + 168#64) (ghostBase + 752#64) 32
    w0Sc0.ratchetKey.privateKey.bytes.toList
    w0Sc0.ratchetKey.privateKey.bytes.toList_length (by decide) (by decide) (by decide)
  have hsmk_v := vecAt_A0_empty (messageKeyAt A₀) (ghostBase + 192#64)
  have hsck_v := vecU8At_A0_exact (ghostBase + 216#64) (ghostBase + 800#64) 32
    (keyToBytes32 w0Sc0.chainKey.key) (by simp [keyToBytes32]) (by decide) (by decide) (by decide)
  have hpure_sc :
      (PublicKey.deserialize w0Sc0.ratchetKey.publicKey.serialize = .ok w0Sc0.ratchetKey.publicKey ∧
        True ∧
        clampScalar w0Sc0.ratchetKey.privateKey.bytes = w0Sc0.ratchetKey.privateKey.bytes ∧
        w0Sc0.ratchetKey.publicKey.serialize.length = 33) ↔ True :=
    iff_true_intro ⟨hf.2.2.2.1, trivial, hf.2.2.2.2.1, by decide +kernel⟩
  let Rframe : SepProp :=
    memRegion (ghostBase + BitVec.ofNat 64 (4096 + pqLen)) (520192 - pqLen) ∗
    memRegion (ghostBase + 344#64) 8 ∗
    memRegion (ghostBase + 456#64) 56 ∗
    memRegion (ghostBase + 545#64) 15 ∗
    memRegion (ghostBase + 593#64) 15 ∗
    memRegion (ghostBase + 640#64) 16 ∗
    memRegion (ghostBase + 689#64) 15 ∗
    memRegion (ghostBase + 737#64) 15 ∗
    memRegion (ghostBase + 784#64) 16 ∗
    memRegion (ghostBase + 832#64) 64 ∗
    memRegion (ghostBase + 929#64) 15 ∗
    memRegion (ghostBase + 976#64) 3120
  refine ⟨m, Rframe, ?_⟩
  unfold sessionStateAt
  rw [show w0Ses1.state = w0SA1 from rfl, w0SA1_fields.1]
  dsimp only
  rw [propext hpure_ss, pure_true, emp_sepConj]
  dsimp only [w0G1, vecGhostAt]
  rw [w0SA1_fields.2.2.1, w0SA1_fields.2.1, w0SA1_fields.2.2.2.1]
  simp only [List.zip_cons_cons, List.zip_nil_right, optSenderChainAt, optChainKeyAt, optTailVecAt,
    BitVec.add_assoc, BitVec.reduceAdd]
  rw [propext hpure_sc, pure_true, emp_sepConj]
  rw [hrc_v]
  unfold chainAt
  rw [propext hpure_rc, pure_true, emp_sepConj]
  dsimp only [w0RcGhost, w0RcPost, vecGhostAt]
  simp only [List.zip_nil_right, optChainKeyAt, BitVec.add_assoc,
    BitVec.reduceAdd]
  rw [hloc_v, hrem_v, hroot_v, hrc_srk_v, hrc_priv_v, hrc_mk_v, hrc_ck_v,
    halice_v, hpq_v, hsrk_v, hpriv_v, hsmk_v, hsck_v]
  simp only [BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd,
    Nat.reduceSub, sepConj_emp] at hsat ⊢
  refine Eq.mp (congrArg (fun P => m ⊨ P) ?_) hsat
  dsimp only [Rframe]
  sep_ac_rfl

private theorem w0G0_cloneRel : CloneRel w0G0 w0G0 :=
  ⟨rfl, rfl, rfl, rfl⟩

private theorem w0G1_drop_freeOnly : FreeOnlyEvs (dropClonedSessionEvents w0G1 w0Ses1.state) := by
  have hdec : (dropClonedSessionEvents w0G1 w0Ses1.state).all
      (fun ev => match ev with | .free _ _ => true | _ => false) = true := by
    decide +kernel
  suffices ∀ l : List AllocEvent,
      l.all (fun ev => match ev with | .free _ _ => true | _ => false) = true → FreeOnlyEvs l by
    exact this _ hdec
  intro l hl
  induction l with
  | nil => exact FreeOnlyEvs.nil
  | cons ev tl ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hl
    cases ev with
    | alloc _ => cases hl.1
    | aligned _ _ => cases hl.1
    | realloc _ _ _ => cases hl.1
    | free al sz =>
      exact (FreeOnlyEvs.singleton al sz).append (ih hl.2)

def w0Inputs : Inputs :=
  pqRecvInputs W0 w0St1 (wireWhisper :: w0Rest) 0#256

def w0PeerAddr : AddrV :=
  ⟨(partyAddr .B).name, (partyAddr .B).device⟩

def w0OwnAddr : AddrV :=
  ⟨(partyAddr .A).name, (partyAddr .A).device⟩

def w0AddressCall : AddressCall :=
  { out := 0#64, p := 0#64, bs := bytesOfString (partyAddress .B).text }

def w0RunCall : RunCall :=
  { i := w0Inputs
    c := .recv w0PeerAddr
    a := none
    res := 0#64
    call := 0#64
    stores := 0#64
    inp := 0#64
    coins := 0#64 }

def mkAddrGhost (a : AddrV) : AddrGhost :=
  { name := { cap := BitVec.ofNat 64 a.name.length, ptr := 0#64, bytes := a.name }
    device := a.device }

def w0W2Params : W2BinaryWhisperParams where
  repAlloc := A₀
  B := ⟨0⟩
  peer := mkAddrGhost w0PeerAddr
  x :=
    { toSlotCtx :=
        { peer := mkAddrGhost w0PeerAddr
          peerA := 0#64
          me := mkAddrGhost w0OwnAddr
          meA := 0#64
          stores := 0#64
          ret := 0#64
          coinsP := 0#64
          F := runFiles w0Inputs
          coins := keyToBytes32 0#256 }
      msgA := 0#64
      msgG := ⟨0#64, 0#64, 0#64, 0#64, 0#64⟩
      msg := w0Msg }

private theorem w0W2Params_dom : W2BinaryWhisperDom (.recv w0PeerAddr) w0Inputs w0W2Params := by
  intro p hp
  injection hp with hp
  subst hp
  exact ⟨rfl, rfl, rfl, by change w0Ct.length ≤ msgCapBytes; rw [w0Ct_len]; decide, rfl⟩

private theorem w0Inputs_parseArgs :
    parseArgs uuidTryParse (w0Inputs.argv.map bytesOfString) = some (.recv w0PeerAddr) :=
  parseArgs_recv .B

private def kutf8 (s : String) : List (BitVec 8) :=
  (s.toList.flatMap String.utf8EncodeChar).map fun b => BitVec.ofNat 8 b.toNat

private theorem kutf8_append (s₁ s₂ : String) : kutf8 (s₁ ++ s₂) = kutf8 s₁ ++ kutf8 s₂ := by
  simp only [kutf8, String.toList_append, List.flatMap_append, List.map_append]

private theorem byteArray_toList_eq_data : ∀ (bs : ByteArray), bs.toList = bs.data.toList
  | ⟨⟨xs⟩⟩ => by
    have hloop : ∀ i r, ByteArray.toList.loop ⟨⟨xs⟩⟩ i r = r.reverse ++ xs.drop i := by
      intro i r
      fun_induction ByteArray.toList.loop ⟨⟨xs⟩⟩ i r with
      | case1 i r hi ih =>
        have hi' : i < xs.length := hi
        have hget : (ByteArray.mk ⟨xs⟩).get! i = xs[i] := getElem!_pos (⟨xs⟩ : Array UInt8) i hi
        rw [ih, hget, List.reverse_cons, List.append_assoc, List.singleton_append,
          List.drop_eq_getElem_cons hi']
      | case2 i r hni =>
        rw [List.drop_eq_nil_of_le (Nat.le_of_not_lt hni), List.append_nil]
    exact hloop 0 []

private theorem utf8_eq_kutf8 (s : String) : utf8 s = kutf8 s := by
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  simp [utf8, kutf8, List.utf8Encode, byteArray_toList_eq_data]

private theorem repr_utf8_eq_kutf8 (s : String) :
    CryptoVerification.LibsignalTripleRatchetRepr.utf8 s = kutf8 s := by
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  simp [CryptoVerification.LibsignalTripleRatchetRepr.utf8, kutf8, List.utf8Encode,
    byteArray_toList_eq_data]

private theorem w0AddressCall_parse :
    addrParse uuidTryParse w0AddressCall.bs = some w0PeerAddr := by
  have hp := parseArgs_recv .B
  have hr : bytesOfString "recv" = utf8 "recv" := by
    rw [utf8_eq_kutf8]; exact of_decide_eq_true rfl
  have hs : utf8 "recv" ≠ utf8 "send" := by rw [utf8_eq_kutf8, utf8_eq_kutf8]; decide
  simp only [Cmd.argv, List.map_cons, List.map_nil, parseArgs, hr, hs, ↓reduceIte] at hp
  cases ha : addrParse uuidTryParse (bytesOfString (partyAddress .B).text) with
  | none => rw [ha] at hp; cases hp
  | some v =>
    rw [ha] at hp
    injection hp with hp
    injection hp with hv
    unfold w0AddressCall
    dsimp only
    rw [ha, hv]
    rfl

private theorem partyAddr_eq (P : Party) : partyAddr P = ⟨kutf8 (partyAddressName P), 1#8⟩ := by
  unfold partyAddr
  rw [utf8_eq_kutf8]

private theorem textBytes_partyA_len : (textBytes (partyAddress .A).text).length = 38 := by
  have hd1 : kutf8 (toString (1 : Nat)) = [0x31#8] := by
    rw [← utf8_eq_kutf8]
    exact CryptoVerification.SignalSession.Cli.Decimal.Helpers.decimalText_digit 1 (by decide)
  unfold textBytes partyAddress Address.text
  rw [repr_utf8_eq_kutf8, kutf8_append, kutf8_append, hd1]
  decide

private theorem encodeVarintAux_len_le : ∀ (k : Nat) (v : BitVec 64),
    (encodeVarintAux k v).length ≤ k
  | 0, _ => Nat.le_refl 0
  | k + 1, v => by
    unfold encodeVarintAux
    split
    · simp
    · simp only [List.length_cons]
      exact Nat.succ_le_succ (encodeVarintAux_len_le k (v >>> 7))

private theorem encodeBytesField_len_le (tag : Nat) :
    ∀ (ov : Option (List (BitVec 8))),
      (encodeBytesField tag ov).length ≤ 20 + (ov.map List.length).getD 0
  | none => by simp [encodeBytesField]
  | some v => by
    unfold encodeBytesField encodeKey encodeVarint
    have h1 := encodeVarintAux_len_le 10 (BitVec.ofNat 64 (tag * 8 + WireType.lengthDelimited.toNat))
    have h2 := encodeVarintAux_len_le 10 (BitVec.ofNat 64 v.length)
    simp only [List.length_append, Option.map_some, Option.getD_some]
    omega

private theorem encodeUint32Field_len_le (tag : Nat) :
    ∀ (ov : Option (BitVec 32)), (encodeUint32Field tag ov).length ≤ 20
  | none => by simp [encodeUint32Field]
  | some v => by
    unfold encodeUint32Field encodeKey encodeVarint
    have h1 := encodeVarintAux_len_le 10 (BitVec.ofNat 64 (tag * 8 + WireType.varint.toNat))
    have h2 := encodeVarintAux_len_le 10 (v.zeroExtend 64)
    simp only [List.length_append]
    omega

private theorem w0Addrs_len_le : ∀ a, w0Addrs = some a → a.length ≤ 36 := by
  intro a ha
  unfold w0Addrs serializeAddrVals at ha
  cases hs : serviceIdParse uuidTryParse (partyAddr .B).name with
  | none => simp [hs, Bind.bind, Option.bind] at ha
  | some s =>
    cases hr : serviceIdParse uuidTryParse (partyAddr .A).name with
    | none => simp [hs, hr, Bind.bind, Option.bind] at ha
    | some r =>
      simp only [hs, hr, Bind.bind, Option.bind, Pure.pure] at ha
      injection ha with ha'
      rw [← ha']
      have hab : ∀ (u : Bool × List.Vector (BitVec 8) 16) (d : BitVec 8),
          (addrBytes u d).length = 18 := by
        intro ⟨b, ⟨l, hl⟩⟩ d
        simp [addrBytes, List.Vector.toList, hl]
      rw [List.length_append, hab, hab]

private theorem w0Rest_len_le : w0Rest.length ≤ 340 := by
  let pm : ProtoSignalMessage :=
    { ratchetKey := some (⟨b0.spkPub⟩ : PublicKey).serialize
      counter := some 0#32
      previousCounter := some 0#32
      ciphertext := some w0Ct
      pqRatchet := if w0PqMsg.isEmpty then none else some w0PqMsg
      addresses := w0Addrs }
  let content := versionByte currentVersion :: encode pm
  let mac := computeMac C0.F ⟨⟨b0.idPub⟩⟩ ⟨w0IdA.publicKey⟩ w0Mk.macKey content
  have hser : w0Rest = content ++ mac := rfl
  have hmac : mac.length = 8 := computeMac_C0_len _ _ _ content
  have h1 := encodeBytesField_len_le 1 pm.ratchetKey
  have h2 := encodeUint32Field_len_le 2 pm.counter
  have h3 := encodeUint32Field_len_le 3 pm.previousCounter
  have h4 := encodeBytesField_len_le 4 pm.ciphertext
  have h5 := encodeBytesField_len_le 5 pm.pqRatchet
  have h6 := encodeBytesField_len_le 6 pm.addresses
  have hrk : (pm.ratchetKey.map List.length).getD 0 = 33 := by decide
  have hct : (pm.ciphertext.map List.length).getD 0 = 16 := by
    dsimp only [pm, Option.map, Option.getD]; rw [w0Ct_len]
  have hpq : (pm.pqRatchet.map List.length).getD 0 ≤ 100 := by
    dsimp only [pm]
    have hpqLen : w0PqMsg.length ≤ 100 := by decide
    split <;> simp_all
  have had : (pm.addresses.map List.length).getD 0 ≤ 36 := by
    dsimp only [pm]
    cases ha : w0Addrs with
    | none => simp
    | some a => simp [w0Addrs_len_le a ha]
  have henc : (encode pm).length ≤ 329 := by
    unfold encode
    simp only [List.length_append]
    omega
  rw [hser, List.length_append, hmac]
  simp only [content, List.length_cons]
  omega

private theorem intoBoxedBoundedEnv_nil {bs : List (BitVec 8)} (hlt : bs.length < 2 ^ 63) :
    IntoBoxedBoundedEnv bs [] := by
  have hlt64 : bs.length < 2 ^ 64 := by omega
  have hto : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64]
  refine ⟨BitVec.ofNat 64 bs.length, by omega, by omega, ?_⟩
  unfold intoBoxedCapEvents
  split
  · rfl
  · next hnot => exact absurd (Nat.le_of_eq hto) hnot

private theorem w0Inputs_argv_map :
    w0Inputs.argv.map bytesOfString = [utf8 "recv", w0AddressCall.bs] := by
  have hr : bytesOfString "recv" = utf8 "recv" := by
    rw [utf8_eq_kutf8]; exact of_decide_eq_true rfl
  have hargv : w0Inputs.argv = ["recv", (partyAddress .B).text] := rfl
  rw [hargv]
  simp only [List.map_cons, List.map_nil, hr]
  rfl

private theorem w0Inputs_coins_readFileResult :
    readFileResult (initFsState (cliInputs w0Inputs)).files (utf8 "coins") =
      .ok (keyToBytes32 0#256) := by
  have hpath : pathStr (utf8 "coins") = "coins" := by
    rw [utf8_eq_kutf8]; exact of_decide_eq_true rfl
  have hcs : CryptoVerification.SignalSession.pathComps "coins" = ["coins".toList] := by
    unfold CryptoVerification.SignalSession.pathComps
    rw [List.splitOn_eq_splitOnP]
    exact List.splitOnP_eq_singleton (by decide)
  have hanc : CryptoVerification.SignalSession.ancestors "coins" = [] := by
    unfold CryptoVerification.SignalSession.ancestors; rw [hcs]; rfl
  have hblk : blockingAncestorF (initFsState (cliInputs w0Inputs)).files "coins" = none := by
    unfold blockingAncestorF; rw [hanc]; rfl
  have hcoins :=
    CryptoVerification.SignalSession.Cli.RunRefine.coinsOf_pqRecv
      W0 w0St1 (wireWhisper :: w0Rest) 0#256
  have hne_nil : keyToBytes32 0#256 ≠ [] := by decide
  have hent0 : (initFsState { files := w0Inputs.files }).files "coins" =
      some (.file (keyToBytes32 0#256)) := by
    change (CryptoVerification.SignalSession.filesOf w0Inputs.files "coins").getD [] =
      keyToBytes32 0#256 at hcoins
    unfold CryptoVerification.SignalSession.filesOf CryptoVerification.SignalSession.fsView at hcoins
    split at hcoins
    · exact absurd hcoins.symm hne_nil
    · cases hf : (initFsState { files := w0Inputs.files }).files "coins" with
      | none => rw [hf] at hcoins; exact absurd hcoins.symm hne_nil
      | some entry =>
        cases entry with
        | dir => rw [hf] at hcoins; exact absurd hcoins.symm hne_nil
        | file bs =>
          rw [hf] at hcoins
          simp only [Option.getD_some] at hcoins
          rw [hcoins]
  have hent : (initFsState (cliInputs w0Inputs)).files "coins" =
      some (.file (keyToBytes32 0#256)) := hent0
  have hcap : (keyToBytes32 0#256).length ≤ fileCapBytes := by decide
  unfold readFileResult readViewF
  rw [hpath, hblk, hent]
  simp [hcap]

private theorem w0Own_get :
    StoresGhost.opened.identity.own.get cliIo.rd (runFiles w0Inputs) (utf8 "address") =
      .ok (textBytes (partyAddress .A).text) :=
  ownAddr_pqRecv W0 w0St1 (wireWhisper :: w0Rest) 0#256

private theorem w0Sess_get :
    StoresGhost.opened.sessions.get cliIo.rd (runFiles w0Inputs) (addressText (partyAddr .B)) =
      .ok (encodeRecord w0Rec0) := by
  rw [w0Rec0_encode_eq]
  exact pqSessGet_recv W0 w0St1 (wireWhisper :: w0Rest) 0#256 (pqSessBytes_le_fileCapBytes w0St1_domain)

private theorem w0Peer_get :
    StoresGhost.opened.identity.peers.get cliIo.rd (runFiles w0Inputs) (partyAddr .B).name =
      .ok (pqIdBytes w0St1) :=
  pqIdGet_recv W0 w0St1 (wireWhisper :: w0Rest) 0#256

/-- All four `Dir::get` calls on `w0Inputs` (`R0` `"address"`, `W2Load` `"sessions/Bob.1"`,
`W2Trust` `"identities/Bob"`, and `W2Save` `"identities/Bob"`) read `.ok _` (`≠ .error ()`), so
`DirGetErrAllocEnv` reduces to `(· = [])` (`0 × alloc 22`). -/
theorem w0Inputs_dirGet_all_ok_no_errAlloc :
    let F0 := runFiles w0Inputs
    let pOwn := pathOf StoresGhost.opened.identity.own.path (utf8 "address")
    let pSess := pathOf StoresGhost.opened.sessions.path (addressText (partyAddr .B))
    let pPeer := pathOf StoresGhost.opened.identity.peers.path (partyAddr .B).name
    cliIo.rd F0 pOwn ≠ .error () ∧
    cliIo.rd F0 pSess ≠ .error () ∧
    cliIo.rd F0 pPeer ≠ .error () ∧
    DirGetErrAllocEnv cliIo.rd F0 pOwn = (· = []) ∧
    DirGetErrAllocEnv cliIo.rd F0 pSess = (· = []) ∧
    DirGetErrAllocEnv cliIo.rd F0 pPeer = (· = []) := by
  have h1 : cliIo.rd (runFiles w0Inputs)
      (pathOf StoresGhost.opened.identity.own.path (utf8 "address")) =
      .ok (textBytes (partyAddress .A).text) := w0Own_get
  have h2 : cliIo.rd (runFiles w0Inputs)
      (pathOf StoresGhost.opened.sessions.path (addressText (partyAddr .B))) =
      .ok (encodeRecord w0Rec0) := w0Sess_get
  have h3 : cliIo.rd (runFiles w0Inputs)
      (pathOf StoresGhost.opened.identity.peers.path (partyAddr .B).name) =
      .ok (pqIdBytes w0St1) := w0Peer_get
  unfold DirGetErrAllocEnv
  dsimp only
  rw [h1, h2, h3]
  exact ⟨(fun h => nomatch h), (fun h => nomatch h), (fun h => nomatch h), rfl, rfl, rfl⟩

private def mkAddrTextValEvs (rem : AddrVal) : List AllocEvent :=
  addrToOwnedEvents rem.name ++
    (addrDotReserveEvents rem.name ++
      (decimalEvents (rem.device.zeroExtend 32) ++
        (addrDecReserveEvents rem.name rem.device ++ rustDeallocEvents 8 1)))

private theorem mkAddrTextValEvs_mem (rem : AddrVal) :
    AddrTextValSuccEnv rem (mkAddrTextValEvs rem) :=
  ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl,
    _, _, rfl, rfl, FreeOnlyEvs.singleton 1 8⟩

private def mkDirGetOkBinEvs (d : DirGhost) (name bs : List (BitVec 8)) : List AllocEvent :=
  (if d.path = [] then allocBytes1Events name else pathEvents d.path name) ++
    (allocBytes1Events bs ++ ([] ++ []))

private theorem mkDirGetOkBinEvs_mem {F0 : FsFiles} {d : DirGhost} {name bs : List (BitVec 8)}
    (hd : d.changed = [])
    (hrd : cliIo.rd F0 (pathOf d.path name) = .ok bs)
    (hle : bs.length ≤ 2097152) :
    DirGetCacheMissOkBinEnv F0 d name (mkDirGetOkBinEvs d name bs) := by
  refine ⟨hd, bs, hrd, hle, _, _, rfl, ?_, _, _, rfl, ⟨bs, hrd, hle, Or.inl rfl⟩,
    [], [], rfl, rfl, FreeOnlyEvs.nil⟩
  unfold DirGetPathEnv PathEnv
  by_cases hp : d.path = [] <;> simp [hp]

private def mkM5EntrySimple (dir name : List (BitVec 8)) : List AllocEvent :=
  let cap0 := dir.length
  let cap1 := reserveCap cap0 cap0 1
  let need2 := decide (cap1 - (cap0 + 1) < name.length)
  let capFinal := if need2 then reserveCap cap1 (cap0 + 1) name.length else cap1
  (((rustAllocEvents cap0 1 ++ rustReallocEvents cap0 cap1 1) ++
      (if need2 then rustReallocEvents cap1 capFinal 1 else [])) ++ []) ++
    rustDeallocEvents capFinal 1

private theorem mkM5EntrySimple_mem (dir name : List (BitVec 8)) (hdir : dir ≠ []) :
    M5WriteStepEnv (dir, name) (mkM5EntrySimple dir name) := by
  unfold M5WriteStepEnv
  simp only [hdir, ↓reduceIte]
  unfold M5LoopAEntryEnv mkM5EntrySimple
  dsimp only
  cases hneed : decide (reserveCap dir.length dir.length 1 - (dir.length + 1) < name.length) <;>
    simp only [Bool.false_eq_true, ↓reduceIte] <;>
    exact ⟨_, _, rfl, ⟨_, [], rfl, ⟨_, _, rfl, ⟨_, _, rfl, rfl, rfl⟩, rfl⟩, Or.inl rfl⟩, rfl⟩

private theorem ratchetScopeCoversPq_scopeIn_local (W : PEParams) :
    ∀ st x g, PqxdhPartyInSpecDomain W st → st.session = some (x, g) →
      scopeIn (toRecord (extrasOf fun _ => x) g) := by
  intro st x g hwf hs
  have hwf_sess := hwf.1 x g hs
  rcases hwf_sess.1 with ⟨g₀, hr, _, hsess₀⟩
  have hlen31 := hwf_sess.2.2
  have hval : CryptoVerification.SpqrV1.Top.StateSize.ValidState g.session.pqRatchetState :=
    hsess₀ ▸ CryptoVerification.SignalSession.Cli.Slots.PqValid.reachPq_validState hr
  have hpq31 : g.session.pqRatchetState.length < 2 ^ 31 :=
    Nat.lt_of_le_of_lt
      (CryptoVerification.SignalSession.Cli.Slots.PqValid.pqRatchetState_length_le_encodeRecordX
        (fun _ => x) g) hlen31
  obtain ⟨hseeds₀, hrc₀, _, _, hrepr₀, _, hts, _, habk, hky⟩ :=
    CryptoVerification.SignalSession.Cli.Slots.PqValid.reachPq_inv hr
  rw [hsess₀] at hseeds₀ hrc₀ hrepr₀
  rw [CryptoVerification.E2E.RecordX.toRecord_extrasOf_eq]
  refine ⟨⟨?_, ?_, ?_⟩, CryptoVerification.E2E.RecordX.sessionOfX (fun _ => x) g, rfl, ?_⟩
  · intro s hs'; injection hs' with hs'; subst hs'
    refine ⟨hseeds₀, Nat.lt_of_le_of_lt hrc₀ (by decide), ?_⟩
    intro k hk'; unfold CryptoVerification.E2E.RecordX.sessionOfX at hk'; dsimp only at hk'
    split at hk'
    · rw [hky k hk']; decide
    · cases hk'
  · intro s hs'; injection hs' with hs'; subst hs'; exact ⟨hval, hpq31⟩
  · intro s hs'; injection hs' with hs'; subst hs'
    refine ⟨hrepr₀.1, hrepr₀.2, CryptoVerification.E2E.RecordX.sessionOfX_wf (fun _ => x) g, ?_⟩
    show x.aliceBaseKey.length < 2 ^ 32; rw [habk]; decide
  · refine ⟨hrc₀, ?_, ?_, Or.inr habk⟩
    · intro p hp; unfold CryptoVerification.E2E.RecordX.sessionOfX at hp; dsimp only at hp
      split at hp
      · injection hp with hp'; subst hp'; exact hts
      · cases hp
    · intro k hk'; unfold CryptoVerification.E2E.RecordX.sessionOfX at hk'; dsimp only at hk'
      split at hk'
      · exact hky k hk'
      · cases hk'

/-- Concrete `recvWhisper` binary-kit success-path non-vacuity witness on
`RealCliMainBinaryEnvOf (mkBinaryKitRealCalleeEnvs img S X W₀) i₀` at `W₀ = w0CliHooks`
(exhibiting Block 594 `address_text` events, `.ok` `Dir::get` reads, hook-model read disjuncts, and
`CliWriteStdoutEnv`'s `alloc 1024` disjunct). -/
theorem realCliMainBinaryEnvOf_concrete_recvWhisper_succ_nonvacuous [LibsignalPlacement]
    (img : Arm64.Obj.Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) :
    ∃ (W₀ : CliHooks) (i₀ : Inputs) (evs : List AllocEvent),
      CliPqxdhInputs ⟨W₀.C, W₀.Q⟩ i₀ ∧
      (∃ peer, parseArgs uuidTryParse (i₀.argv.map bytesOfString) = some (.recv peer)) ∧
      i₀.stdin.head? = some wireWhisper ∧
      RecvWhisperSuccMainEnv img ⟨W₀.C, W₀.Q⟩ i₀ evs ∧
      RealCliMainBinaryEnvOf (mkBinaryKitRealCalleeEnvs img S X W₀) i₀ evs ∧
      AllocEvent.alloc 36 ∈ evs ∧
      AllocEvent.alloc 8 ∈ evs ∧
      AllocEvent.alloc 24 ∈ evs ∧
      AllocEvent.alloc 16 ∈ evs ∧
      AllocEvent.alloc 1024 ∈ evs := by
  let R := w0W2Params
  let dx := toDecryptGhost R.x
  let rem := dx.rem.val
  have hremEq : rem = partyAddr .B := rfl
  have hlocEq : dx.loc.val = partyAddr .A := rfl
  have hW0Eq : (⟨w0CliHooks.C, w0CliHooks.Q⟩ : PEParams) = W0 := rfl
  have hScopeIn : scopeIn w0Rec0 :=
    ratchetScopeCoversPq_scopeIn_local W0 w0St1 w0XA ⟨.A, w0SA0, 0, [0]⟩ w0St1_domain rfl
  have hKitR0 : scopeKit w0Rec0 := scopeKit_of_scopeIn hScopeIn
  have hSessCap : (encodeRecord w0Rec0).length ≤ 2097152 := by
    rw [w0Rec0_encode_eq]
    exact pqSessBytes_le_fileCapBytes w0St1_domain
  have hOwnCap : (textBytes (partyAddress .A).text).length ≤ 2097152 := by
    rw [textBytes_partyA_len]; decide
  have hPeerCap : (pqIdBytes w0St1).length ≤ 2097152 := by decide +kernel
  have hStdinCap : w0Inputs.stdin.length ≤ msgCapBytes := by
    have := w0Rest_len_le
    change (wireWhisper :: w0Rest).length ≤ msgCapBytes
    simp only [List.length_cons, msgCapBytes]
    omega
  have hRestLt : w0Rest.length < 2 ^ 32 := by
    have := w0Rest_len_le
    omega
  let kit := decSessKitPlaced R.repAlloc R.x.F R.x.peer R.B
  have hScAt : kit.ScopeAt scopeKit StoresGhost.opened.sessions rem w0Rec0 := by
    cases henc : encodeRecord w0Rec0 with
    | nil => exact absurd henc w0Rec0_encode_ne_nil
    | cons b0 bsRest =>
      have hget : StoresGhost.opened.sessions.get cliIo.rd R.x.F (addressText rem) =
          .ok (b0 :: bsRest) := by
        rw [hremEq]
        exact henc ▸ w0Sess_get
      exact ⟨hKitR0, b0 :: bsRest, hget, w0Rec0, rfl, henc, hKitR0⟩
  have hM2 : M2CollectSuccEnv w0Inputs.argv.length [] :=
    ⟨[], [], rfl, Or.inl rfl, ⟨[], [], rfl, Or.inl rfl, rfl⟩⟩
  let evsSetup :=
    rustAllocEvents (16 * w0Inputs.argv.length) 8 ++
      ([] ++ (addressEvents uuidTryParse w0AddressCall.bs ++
        (allocBytes1Events w0Inputs.stdin ++ (allocBytes1Events (keyToBytes32 0#256) ++ []))))
  have hSetup : CliMainSetupSuccEnv w0Inputs (some w0AddressCall) evsSetup :=
    ⟨_, _, rfl, rfl,
      [], _, rfl, hM2,
      _, _, rfl, rfl,
      _, _, rfl, ⟨by have := hStdinCap; unfold msgCapBytes at this; omega, Or.inl rfl⟩,
      _, [], rfl, ⟨keyToBytes32 0#256, w0Inputs_coins_readFileResult, by decide, Or.inl rfl⟩,
      FreeOnlyEvs.nil⟩
  let ownB := textBytes (partyAddress .A).text
  let evsR0Get := mkDirGetOkBinEvs StoresGhost.opened.identity.own (utf8 "address") ownB
  let evsR0 := evsR0Get ++ (rustAllocEvents w0OwnAddr.name.length 1 ++ deallocBytes1OfLen ownB.length)
  have hDeallocOwn : FreeOnlyEvs (deallocBytes1OfLen ownB.length) := by
    have hlen : ownB.length = 38 := textBytes_partyA_len
    rw [hlen]
    exact FreeOnlyEvs.singleton 1 38
  have hR0 : R0BinarySuccEnv w0RunCall evsR0 :=
    ⟨ownB, w0OwnAddr, w0Own_get, addrParse_textBytes .A,
      evsR0Get, _, rfl, mkDirGetOkBinEvs_mem rfl w0Own_get hOwnCap,
      _, _, rfl, rfl, hDeallocOwn⟩
  let evsCt : List AllocEvent := []
  let evsAd : List AllocEvent := []
  let evsSer : List AllocEvent :=
    if w0Msg.serialized = [] then [] else rustAllocEvents w0Msg.serialized.length 1
  let evsSig := [] ++ (([] ++ (evsCt ++ (evsAd ++ evsSer))) ++ [])
  have hCtMem : IntoBoxedBoundedEnv w0Msg.ciphertext evsCt :=
    intoBoxedBoundedEnv_nil (by change w0Ct.length < 2 ^ 63; rw [w0Ct_len]; decide)
  have hAdMem : IntoBoxedOptBoundedEnv w0Msg.addresses evsAd := by
    change IntoBoxedOptBoundedEnv w0Addrs []
    cases ha : w0Addrs with
    | none => rfl
    | some ad =>
      have had36 := w0Addrs_len_le ad ha
      exact intoBoxedBoundedEnv_nil (by omega)
  have hSig : SigTryFromOkEnv w0Rest w0Msg evsSig :=
    ⟨w0Rest_tryFrom,
      [], _, rfl, SigTryFromLoopBoundedEnv.done SigTryFromErrTailEnv.nil,
      _, [], rfl,
      ⟨[], _, rfl, FreeOnlyEvs.nil,
        ⟨evsCt, _, rfl, hCtMem,
          ⟨evsAd, evsSer, rfl, hAdMem, rfl⟩⟩⟩,
      FreeOnlyEvs.nil⟩
  let evsAddr := mkAddrTextValEvs rem
  let evsSessGet := mkDirGetOkBinEvs StoresGhost.opened.sessions (addressText rem) (encodeRecord w0Rec0)
  let evsLoad :=
    (rustAllocEvents kit.loadBoxSize 8 ++
      (evsAddr ++ (evsSessGet ++ (sessDeserEvents w0Rec0 ++ [])))) ++
    rustDeallocEvents kit.loadBoxSize 8
  have hLoad : W2LoadStepSuccEnv R w0Rec0 evsLoad := by
    cases henc : encodeRecord w0Rec0 with
    | nil => exact absurd henc w0Rec0_encode_ne_nil
    | cons b0 bsRest =>
      have hget : StoresGhost.opened.sessions.get cliIo.rd R.x.F (addressText rem) =
          .ok (b0 :: bsRest) := henc ▸ w0Sess_get
      exact ⟨b0, bsRest, hget, henc, hKitR0,
        _, _, rfl,
        ⟨_, _, rfl, rfl,
          ⟨evsAddr, _, rfl, mkAddrTextValEvs_mem rem,
            ⟨evsSessGet, _, rfl, mkDirGetOkBinEvs_mem rfl w0Sess_get hSessCap,
              ⟨_, [], rfl, rfl, FreeOnlyEvs.nil⟩⟩⟩⟩,
        rfl⟩
  let evsPre := evsSetup ++ (evsR0 ++ (evsSig ++ evsLoad))
  have hPre : RecvWhisperSuccPreEnv w0RunCall (some w0AddressCall) w0Rest w0Msg R w0Rec0 evsPre :=
    ⟨evsSetup, _, rfl, hSetup, evsR0, _, rfl, hR0, evsSig, evsLoad, rfl, hSig, hLoad⟩
  let rdg := recGhostOf dx 0#64 w0G0 w0Ses0.state
  have hctPos : 0 < (recordTryDecryptEnvArgs rdg w0G0).msg.ciphertext.length := by
    change 0 < w0Msg.ciphertext.length
    have hc : w0Msg.ciphertext = w0Ct := rfl
    rw [hc, w0Ct_len]; decide
  obtain ⟨evsTd, h16Td, hTd⟩ := w2RealTdSuccEnv_inhabited (recordTryDecryptEnvArgs rdg w0G0) hctPos
  let evsDec := segCloneEvents rdg.G rdg.st ++ (evsTd ++ [])
  have hDec : RecordDecryptSuccEnv C0.F K0 rdg evsDec :=
    ⟨by rw [show rdg.st = w0Ses0.state from rfl, w0Ses0_state_eq]; rfl,
      w0G0, w0G0_cloneRel,
      _, _, rfl, rfl, evsTd, [], rfl, hTd, FreeOnlyEvs.nil⟩
  let ikit := decIdKitPlaced R.repAlloc R.x.F R.x.peer R.B
  let evsPeerGet := mkDirGetOkBinEvs StoresGhost.opened.identity.peers rem.name (pqIdBytes w0St1)
  let evsTrust := rustAllocEvents ikit.trustBoxSize 8 ++ ((evsPeerGet ++ []) ++ rustDeallocEvents ikit.trustBoxSize 8)
  have hTrust : W2TrustStepSuccEnv R evsTrust :=
    ⟨_, _, rfl, rfl, _, _, rfl,
      ⟨evsPeerGet, [], rfl, mkDirGetOkBinEvs_mem rfl w0Peer_get hPeerCap, FreeOnlyEvs.nil⟩, rfl⟩
  let kBob : IdentityKey := ⟨⟨b0.idPub⟩⟩
  let evsSave :=
    rustAllocEvents ikit.saveBoxSize 8 ++
      ((evsPeerGet ++ ([] ++ (publicKeySerializeEvents ++
          (rustAllocEvents rem.name.length 1 ++ rawVecGrowEvents 48 4 8 0#64)))) ++
        rustDeallocEvents ikit.saveBoxSize 8)
  have hSave : W2SaveStepSuccEnv R kBob evsSave :=
    ⟨by change rem.name ≠ []; rw [hremEq, partyAddr_eq]; decide, rfl, ⟨pqIdBytes w0St1, w0Peer_get⟩,
      _, _, rfl, rfl, _, _, rfl,
      ⟨evsPeerGet, _, rfl, mkDirGetOkBinEvs_mem rfl w0Peer_get hPeerCap,
        [], _, rfl, FreeOnlyEvs.nil,
        _, _, rfl, rfl,
        _, _, rfl, rfl, rfl⟩,
      rfl⟩
  let encLen1 := (lenField 1 (encSessionMem w0G1 w0Ses1)).length
  let evsSer1 := (segCloneEvents w0G1 w0Ses1.state ++ rustAllocEvents encLen1 1) ++
    dropClonedSessionEvents w0G1 w0Ses1.state
  have hSer1 : SerializeSomeCancelEnv w0G1 w0Ses1 evsSer1 :=
    ⟨_, _, rfl, ⟨_, _, rfl, rfl, rfl⟩, rfl⟩
  let evsStorePoll := evsAddr ++ (evsSer1 ++ rawVecGrowEvents 48 4 8 0#64)
  let evsStoreStep :=
    (rustAllocEvents kit.storeBoxSize 8 ++ (evsStorePoll ++ rustDeallocEvents kit.storeBoxSize 8)) ++ []
  have hStoreStep : W2StoreStepSuccEnv R w0Rec1 w0Ses1 w0G1 evsStoreStep :=
    ⟨rfl, w0G1_sessionGhostValid, w0G1_drop_freeOnly, evsStorePoll,
      ⟨evsAddr, _, rfl, mkAddrTextValEvs_mem rem, evsSer1, _, rfl, hSer1, rfl⟩,
      _, [], rfl, ⟨_, _, rfl, rfl, _, _, rfl, rfl, rfl⟩, FreeOnlyEvs.nil⟩
  let evsM5P := mkM5EntrySimple (utf8 "identities") R.peer.name.bytes
  let evsM5S := mkM5EntrySimple (utf8 "sessions") (addressText rem)
  let evsM5 := ((evsM5P ++ []) ++ ((evsM5S ++ []) ++ [])) ++ []
  have hIdDirNe : utf8 "identities" ≠ [] := by rw [utf8_eq_kutf8]; decide
  have hSessDirNe : utf8 "sessions" ≠ [] := by rw [utf8_eq_kutf8]; decide
  have hM5 : RecvWhisperM5SuccEnv R evsM5 :=
    ⟨_, [], rfl,
      ⟨evsM5P ++ [], _, rfl,
        ⟨evsM5P, [], rfl, ⟨evsM5P, [], (List.append_nil _).symm, mkM5EntrySimple_mem _ _ hIdDirNe, rfl⟩,
          FreeOnlyEvs.nil⟩,
        ⟨evsM5S ++ [], [], rfl,
          ⟨evsM5S, [], rfl, ⟨evsM5S, [], (List.append_nil _).symm, mkM5EntrySimple_mem _ _ hSessDirNe, rfl⟩,
            FreeOnlyEvs.nil⟩,
          rfl⟩⟩,
      FreeOnlyEvs.nil⟩
  let evsStore := evsTrust ++ (evsSave ++ (evsStoreStep ++ ([] ++ ([] ++ evsM5))))
  have hStore : RecvWhisperSuccStoreEnv R w0Rec1 w0Ses1 w0G1 kBob evsStore :=
    ⟨evsTrust, _, rfl, hTrust,
      evsSave, _, rfl, hSave,
      evsStoreStep, _, rfl, hStoreStep,
      [], _, rfl, FreeOnlyEvs.nil,
      [], evsM5, rfl, FreeOnlyEvs.nil, hM5⟩
  let evsM6 := rustAllocEvents 1024 1 ++ []
  have hM6 : RecvWhisperSuccM6Env evsM6 :=
    ⟨Or.inr ⟨_, [], rfl, Or.inr rfl, FreeOnlyEvs.nil⟩,
      _, [], rfl, rfl, FreeOnlyEvs.nil⟩
  let fullLog := evsPre ++ evsDec ++ evsStore ++ evsM6
  have hcoins : coinsOf dx.rest = 0#256 := by decide +kernel
  have ⟨hdecRec, hremId, _⟩ := w0_decryptRecord_ok dx w0Ses0 hremEq hlocEq rfl hcoins w0Ses0_state_eq
  have hMainSucc : RecvWhisperSuccMainEnv img ⟨w0CliHooks.C, w0CliHooks.Q⟩ w0Inputs fullLog := by
    rw [hW0Eq]
    exact ⟨w0St1, w0St2, 0#256, w0RunCall, w0PeerAddr, w0Rest, w0Msg, w0AddressCall, R,
      w0Rec0, w0Rec1, w0Ses0, w0Ses1, w0G0, w0G1, w0Pt, kBob,
      evsPre, evsDec, evsStore, evsM6,
      rfl, w0St1_domain, rfl, w0_pqRecvWhisperModel_ok, ⟨w0XA, ⟨.A, w0SA1, 0, [0]⟩, rfl, rfl⟩,
      rfl, rfl, w0Inputs_parseArgs, w0Inputs_argv_map, w0AddressCall_parse,
      rfl, hStdinCap, rfl, hcoins, hlocEq, w0W2Params_dom,
      hScAt, w0Rec0_currentSession, w0G0_sessionGhostValid, hdecRec, rfl, hremId,
      hPre, hDec, hStore, hM6⟩
  have h36_addr : AllocEvent.alloc 36 ∈ evsAddr := by
    change AllocEvent.alloc 36 ∈ mkAddrTextValEvs (partyAddr .B)
    rw [partyAddr_eq]
    decide
  have h8_addr : AllocEvent.alloc 8 ∈ evsAddr := by
    have hdec1 : decimalEvents ((1#8 : BitVec 8).zeroExtend 32) = [AllocEvent.alloc 8] := by
      unfold decimalEvents
      rw [show ((1#8 : BitVec 8).zeroExtend 32).toNat = 1 by decide,
        CryptoVerification.SignalSession.Cli.Decimal.Helpers.decimalText_digit 1 (by decide)]
      decide
    have hd : rem.device = 1#8 := by rw [hremEq, partyAddr_eq]
    exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _
      (by rw [hd, hdec1]; decide)))
  have h24_load : AllocEvent.alloc 24 ∈ evsLoad :=
    List.mem_append_left _ (List.mem_append_left _
      (show AllocEvent.alloc 24 ∈ rustAllocEvents 24 8 by decide))
  have h36_load : AllocEvent.alloc 36 ∈ evsLoad :=
    List.mem_append_left _ (List.mem_append_right _ (List.mem_append_left _ h36_addr))
  have h8_load : AllocEvent.alloc 8 ∈ evsLoad :=
    List.mem_append_left _ (List.mem_append_right _ (List.mem_append_left _ h8_addr))
  have hLoad_sub : ∀ e ∈ evsLoad, e ∈ fullLog := fun e he =>
    List.mem_append_left _
      (List.mem_append_left _
        (List.mem_append_left _
          (List.mem_append_right _
            (List.mem_append_right _
              (List.mem_append_right _ he)))))
  have h16_dec : AllocEvent.alloc 16 ∈ evsDec := by
    have h16' : AllocEvent.alloc 16 ∈ evsTd := by
      have hc : (recordTryDecryptEnvArgs rdg w0G0).msg.ciphertext.length = 16 := by
        change w0Msg.ciphertext.length = 16
        have h1 : w0Msg.ciphertext = w0Ct := rfl
        rw [h1, w0Ct_len]
      rwa [hc] at h16Td
    exact List.mem_append_right _ (List.mem_append_left _ h16')
  have h16_full : AllocEvent.alloc 16 ∈ fullLog :=
    List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h16_dec))
  have h1024_full : AllocEvent.alloc 1024 ∈ fullLog :=
    List.mem_append_right _ (List.mem_append_left _ (by decide))
  exact ⟨w0CliHooks, w0Inputs, fullLog,
    ⟨w0St1, w0St1_domain, Or.inr (Or.inr (Or.inl ⟨w0Rest, 0#256, hRestLt, rfl⟩))⟩,
    ⟨w0PeerAddr, w0Inputs_parseArgs⟩,
    rfl,
    hMainSucc,
    recvWhisperSuccMainEnv_sub img S X w0CliHooks w0Inputs hMainSucc,
    hLoad_sub _ h36_load,
    hLoad_sub _ h8_load,
    hLoad_sub _ h24_load,
    h16_full,
    h1024_full⟩

/-- Alias form of `realCliMainBinaryEnvOf_concrete_recvWhisper_succ_nonvacuous` on
`realCliMainBinaryKitEnvOf img S X W₀ i₀`. -/
theorem realCliMainBinaryKitEnvOf_concrete_recvWhisper_succ_nonvacuous [LibsignalPlacement]
    (img : Arm64.Obj.Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) :
    ∃ (W₀ : CliHooks) (i₀ : Inputs) (evs : List AllocEvent),
      CliPqxdhInputs ⟨W₀.C, W₀.Q⟩ i₀ ∧
      (∃ peer, parseArgs uuidTryParse (i₀.argv.map bytesOfString) = some (.recv peer)) ∧
      i₀.stdin.head? = some wireWhisper ∧
      RecvWhisperSuccMainEnv img ⟨W₀.C, W₀.Q⟩ i₀ evs ∧
      realCliMainBinaryKitEnvOf img S X W₀ i₀ evs ∧
      AllocEvent.alloc 36 ∈ evs ∧
      AllocEvent.alloc 8 ∈ evs ∧
      AllocEvent.alloc 24 ∈ evs ∧
      AllocEvent.alloc 16 ∈ evs ∧
      AllocEvent.alloc 1024 ∈ evs :=
  realCliMainBinaryEnvOf_concrete_recvWhisper_succ_nonvacuous img S X

end LibsignalBinary.Proofs.PeakBudget.RealMainEnvNonVacSuccWhisper
