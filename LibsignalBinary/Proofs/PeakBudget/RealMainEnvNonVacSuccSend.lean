/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Process.Semantics
public import LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
public import LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith
public import LibsignalBinary.Proofs.PeakBudget.CliMainPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
public import LibsignalBinary.Proofs.PeakBudget.CliRealExistentialCalleeEnvs
public import LibsignalBinary.Proofs.PeakBudget.CliRunArmsPeak
public import LibsignalBinary.Proofs.PeakBudget.CliRunPeakHelpers
public import LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge
public import LibsignalBinary.Proofs.PeakBudget.DirPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.RealMainEnvAdapter
public import LibsignalBinary.Proofs.PeakBudget.RealMainEnvNonVacSend
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
public import LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit
public import LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit
public import LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux
public import LibsignalBinary.Proofs.PeakBudget.SpqrSendPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.SpqrSendRodataCaps
public import LibsignalBinary.Proofs.PeakBudget.SpqrSendTightBuckets
public import LibsignalBinary.Proofs.PeakBudget.SpqrSendTightHelpers
public import LibsignalBinary.Proofs.PeakBudget.W1EncryptSegments
public import LibsignalBinary.Proofs.PeakBudget.W1EncryptSlotPeak
public import LibsignalBinary.Proofs.PeakBudget.W1SendRealSlot
public import LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds
public import LibsignalBinary.Proofs.PeakBudget.WireMsgPeakSpec
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seams
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.SessionDeserializeBudget
public import LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.AddressText.PlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Callees
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.CalleesBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R0ProofPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Concat2Budget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlotOfInnerPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Skeleton
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPoll.LayoutPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser
public import LibsignalBinary.Proofs.SignalSession.NonVacuityPq
public import LibsignalBinary.Proofs.SignalSession.PqStep
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliBinaryPqProofDefs
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.SmDirProofDefs
public import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewDefsBudget
public import LibsignalBinary.Specifications.CryptoGames.AEAD.HKDFDefs
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.CreateChainDefs
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSessionApi
public import LibsignalBinary.Specifications.LibsignalE2E.StateXModel
public import LibsignalBinary.Specifications.LibsignalSession
public import LibsignalBinary.Specifications.SignalSession.PqDir
public import LibsignalBinary.Specifications.SignalSession.SmDir
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.ConsumeMessageKey.NonVacProofs.AllocWitness
import LibsignalBinary.Proofs.ConsumeMessageKey.NonVacProofs.StateWitness
import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3ParseRejectPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Plumbing
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.FilesOk
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ScopeIn
import LibsignalBinary.Proofs.SignalSession.NonVacuity
import LibsignalBinary.Proofs.SignalSession.PqClosure
import LibsignalBinary.Proofs.SpecLemmas.FsFold
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Run
import LibsignalBinary.Specifications.AsmConstants
import ProofLib.VCGen

/-!
# Concrete `send`-Arm Success-Path Envelope Reachability

Proves success-path non-vacuity for the `.send` CLI arm (first-message PreKey branch
`sess₀.pendingPreKey = some items`) on both the existential-kit envelope
`RealCliMainEnvOf (mkExistentialRealCalleeEnvs img S P₀)` and the binary-kit release envelope
`realCliMainBinaryKitEnvOf img S X W₀`:
1. Defines `SendSuccMainEnv` and `SendSuccBinaryKitMainEnv` via strict `ConcatEnv` / `IterConcatEnv`
   composition across `M1..M3`, `R0`, `W1SendSuccSlotEnv` / `W1SendBinarySuccSlotEnv` (with exact
   Block 594 `address_text` trace `[.alloc 36, .realloc 1 36 72, .alloc 8, .free 1 8]` and `.ok`
   cache-miss Block 589 `Dir::get` reads), `R2ConcatTailEnv`, `M5`, and `M6Env true`, tied to
   `pqSendModel P₀ p₀ ptext coins.toList = some (some (st₁, wirePrekey :: bs1))`.
2. Proves inclusion into `RealCliMainEnvOf` and `realCliMainBinaryKitEnvOf`.
3. Exhibits concrete witnesses at `P₀ = NonVacuityPq.W0` / `W₀ = sendWitnessCliHooks`. File-read
   witnesses use the hook-model disjunct of `ReadStdinEnv` / `ReadFileEnv` / `ReadFileRuleEnv`
   rather than the compiled growth trace (`DEV-CLI8`), `M6` uses `CliWriteStdoutEnv`'s `alloc 1024`
   over-approximation disjunct, inner SPQR stages (`SpqrTightEvs` / `FineSmallEvs`) carry protocol
   success via `pqSendModel`, and `st₁` / `wirePrekey :: bs1` are not equated to the stored record
   `r'` or `PreKeySignalMessage` bytes.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.RealMainEnvNonVacSuccSend

open Arm64 ProofLib
open Arm64.Process (bytesOfString initFsState)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession
  (ChainKey GhostState IdentityKey OutgoingTripleRatchet PublicKey ReceiverChain SenderChain
   SessionState SignalMessage maxMessageKeys)
open CryptoGames.LibsignalSessionApi
  (KyberPayload PendingKyberPreKey PendingPreKey PreKeySignalMessage Session SessionRecord
   SystemTime execOk)
open CryptoGames.Ratchet (clampScalar)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.E2E
  (PEParams RecordExtras encodeRecordUnderExtras partyAddressName pqxdhSpqrModel wirePrekey)
open CryptoVerification.E2E.Record (encSession encodeRecord lenField toRecord)
open CryptoVerification.E2E.RecordX (encodeRecordX_eq_toRecord extrasOf)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalPublicApi.MessageDecrypt (sessionModelRel)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
  (PreKeyMsgNewCall WithStoresEncGhost storedRecord)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal KyberRel OptU32Rel PendingRel RecordGhost)
open CryptoVerification.LibsignalSession.NonVacuityWitness
  (A₀ bytesOf32 bytesOf64 pk0 split_arena_region)
open CryptoVerification.LibsignalSessionRepr
  (ChainGhost VecGhost VecPin chainAt leBytes messageKeyAt optChainKeyAt vecGhostAt)
open CryptoVerification.LibsignalTripleRatchet (reserveCap)
open CryptoVerification.LibsignalTripleRatchetRepr
  (AddrGhost SenderChainGhost SessionGhost SignalMessageGhost TailVecGhost optSenderChainAt
   optTailVecAt serializeAddresses serviceIdParse sessionStateAt uuidTryParse)
open CryptoVerification.RustHeap (arrayAt vecAt vecBuf vecHeader vecU8At)
open CryptoVerification.SignalSession
  (CliPqxdhInputs Inputs PqParty PqStep PqxdhPartyInSpecDomain emptyParty encodeDir
   fileCapBytes filesFold lastResortUses partyAddress pqInitModel pqSendInputs pqSendModel
   wfPq_step)
open CryptoVerification.SignalSession.Cli
  (StoresGhost addressText cliInputs pathOf utf8)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddrV AddressCall RunCall addrParse cliIo parseArgs)
open CryptoVerification.SignalSession.Cli.RunCompose (RunSem addrValOf runFiles)
open CryptoVerification.SignalSession.Cli.RunProofs.EncryptLemmas (w1IdKit w1SessKit)
open CryptoVerification.SignalSession.Cli.RunRefine (addrParse_textBytes ownAddr_pqSend parseArgs_send)
open CryptoVerification.SignalSession.Cli.Slots
  (pqIdBytes pqIdGet_send pqSessBytes pqSessBytes_le_fileCapBytes pqSessGet_send scopeIn scopeKit
   scopeKit_of_scopeIn)
open CryptoVerification.SignalSession.CliExt (blockingAncestorF pathStr readFileResult)
open CryptoVerification.SignalSession.NonVacuityPq
  (W0 X0 b0 pqInitModel_W0_creates_wfSession t0)
open LibsignalBinary.Heap
  (AllocEvent FreeOnlyEvs SeqEnv rustAllocEvents rustDeallocEvents rustReallocEvents)
open LibsignalBinary.Heap.SpecBudget (ReadFileEnv allocBytes1Events)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps (addressText_length_le)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith
  (cliMaxAddrTextBytes cliMaxDirPathBytes cliMaxDirtyEntries)
open LibsignalBinary.Proofs.PeakBudget.CliMainPeakSpec
  (CliMainSetupEnv CliWriteFileEnv M1PhaseEnv M2CollectEnv M2CollectStepEnv M3PhaseEnv
   M5DirStepEnv M5LoopAEntryEnv M5PhaseEnv M6Env)
open LibsignalBinary.Proofs.PeakBudget.CliRealExistentialCalleeEnvs (mkExistentialRealCalleeEnvs)
open LibsignalBinary.Proofs.PeakBudget.CliRunArmsPeak
  (CliRunOpenedEnv R0OpenedEnv R2ConcatTailEnv R2Env RunArmEnv TempFileBracketEnv
   cliRunOfR0Env_of_r0_arm)
open LibsignalBinary.Proofs.PeakBudget.CliRunPeakHelpers (deallocBytes1OfLen)
open LibsignalBinary.Proofs.PeakBudget.DirPeakSpec
  (CliAddrTextEnv CliDecimalEnv CliDirGetEnv CliDirPutEnv CliDirPutStrEnv CliPathEnv)
open LibsignalBinary.Proofs.PeakBudget.RealMainEnvAdapter
  (CliMainBoundedSetupEnv RealCliMainEnvOf ValidPostSetupWitness cliMainBoundedSetupEnv_of_setup_any)
open LibsignalBinary.Proofs.PeakBudget.RealMainEnvNonVacSend (nonVacSendAddrGhost nonVacSendPeer)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (ConcatEnv IterConcatEnv IterSeqEnv)
open LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
  (CliSessStorePollEnv CliSmallStorePollEnv)
open LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit (dropClonedSessionEvents)
open LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit
  (RecordSerializeCancelEnv SerializeSomeCancelEnv serializeSomeExactEvents)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit (SpqrTightEvs StatesIntoPbTightEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec
  (DecodeStateTightEnv StatesFromPbTightEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (msgCapBytes sessionCapBytes)
open LibsignalBinary.Proofs.PeakBudget.SpqrSendPeakSpec (SpqrSendTightCapEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrSendRodataCaps
  (PqEncodeCapTightEnv PqEncodeLargeTightEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrSendTightBuckets
  (FineSmallEvs smallAllocCost_le_143484_of_le_135167)
open LibsignalBinary.Proofs.PeakBudget.SpqrSendTightHelpers
  (ChainAddEpochTight4Env ChainFromTightEnv ChainIntoPbTight4Env ChainSendKeyTightEnv
   MessageSerializeTightEnv StatesSendRodataTightEnv)
open LibsignalBinary.Proofs.PeakBudget.W1EncryptSegments
  (FromApplySegEnv FromCmSegEnv FromKeySegEnv FromSaveSegEnv KyberOptStepEnv OtrApplyEnvTight
   OtrEncryptStepEnv WithStoresEncSegEnv)
open LibsignalBinary.Proofs.PeakBudget.W1EncryptSlotPeak
  (FromApplyTightEnv FromCmTightEnv FromOtrTightEnv FromSaveTightEnv WithStoresEncTightEnv
   otrAfterSome w1_peer_addressText_le_64)
open LibsignalBinary.Proofs.PeakBudget.W1SendRealSlot
  (W1SendRealDom W1SendRealEnv W1SendRealParams W1SendRealSlotEnv peer_and_rem_name_le_40_of_send
   w1CtLenCap w1PkOutCap w1RealIdKitBudget w1RealSessKitBudget w1SmSerCap w1StoreEncCap)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds
  (RecordGhostValid encSessionMem_eq_of_sessionGhostValid)
open LibsignalBinary.Proofs.PeakBudget.WireMsgPeakSpec
  (PreKeyMsgNewEnv kyberCopyEvs kyberPayloadLen preKeyMsgNewEvents preKeyMsgNewRawEvents
   preKeyMsgNewRawPrologueEvents signalMessageNewSerLen)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget (SessionGhostValid)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (BoxAllocEnv)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.SessionDeserializeBudget
  (sessDeserEvents)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux
  (RecordDeserializeCancelEnv sessDeserEvents_mem_recordDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.D3 (ratchetScopeCoversPq_scopeIn_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
  (cliSessionKitLoadPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.CalleesBudget (AddressEnv addressEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Concat2Budget (cliConcat2Events)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (ReadFileRuleEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPoll.LayoutPlacedBudget (OptLoadDeserEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget (nonFreeCount)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (segCloneEvents)
open LibsignalBinary.Proofs.TripleRatchet.Wire.NewDefsBudget
  (SignalMessageNewEnv SignalMessageNewGhost signalMessageNewEvents)
open CryptoVerification.E2E.Record.Serialization (encSessionMem)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives pqxdhSpqrModel)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession (CliHooks)
open CryptoVerification.SignalSession.Cli.MainHops (CallV cliWrOk)
open CryptoVerification.SignalSession.Cli.RunCompose (EncGhost)
open CryptoVerification.SignalSession.Cli.RunProofs.EncryptLemmas (w1EncGhost)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlotOfInnerPlacedBudget
  (w1IdKitPlaced w1SessKitPlaced)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rawVecGrowEvents)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefsBudgetAux
  (toTempTwinsIkitEnv toTempTwinsKitEnv)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins
  (FromApplyEnv FromCmEnv FromKeyEnv FromOtrEnv FromSaveEnv KyberOptEnv OtrApplyEnv
   OtrEncryptCoreEnv PreKeyMsgNewRawEnv SaveStepEnv TrustStepEnv WithStoresEncEnv
   freeOnlyEvs_rustDeallocEvents)
open LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
  (RecordSerializeSeqFreeValidEnv W1BinarySendDom W1BinarySendParams W1SendBinaryKitSlotEnv
   mkBinaryKitRealCalleeEnvs realCliMainBinaryKitEnvOf realCliRunBinaryKitEnvOf
   w1BinaryIdKitPlacedBudget w1BinarySessKitPlacedBudget)
open LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge
  (CliRunBinaryEnv R0BinaryEnv RealCliMainBinaryEnvOf RunArmBinaryEnv)
open LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit
  (RecordSerializeSeqFreeEnv SerializeSomeSeqFreeEnv)
open LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins
  (PreKeyPostEncryptEnv pendingKyberPayload preKeyMsgFromItems)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.AddressText.PlacedBudgetAux
  (addrDecReserveEvents addrDotReserveEvents addrToOwnedEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget
  (DecimalEnv decimalCap decimalEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a
  (DirGetEnv DirGetErrAllocEnv DirGetPathEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget (PathEnv pathEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux
  (DirPutEnv dirPutTailEnv_miss_grow)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux
  (DirPutStrEnv dirPutStrEnv_of_nonempty)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
  (cliIdentityKitSavePollEnv cliIdentityKitTrustPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
  (AddrTextValEnv cliSessionKitStorePollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R0ProofPlacedBudget
  (PreAfterGetEnv)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (PublicKeySerializeEnv publicKeySerializeEvents)
open LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget (otrSignalMsgGhost)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (SegCloneEnv)
open Symbolic.Swarm.TRREF.B3Defs (DeserializeScopeP_Q NonEmptyV1Q)

/-! ## 1. Success-Only Sub-Envelopes -/

/-- Strict (`0` `SeqEnv` `Or.inl` shortcut) `address_text(&ProtocolAddress)` envelope: allocates
`(addressText g.val).length ≤ cap ≤ 4 * g.name.bytes.length + 32` and drops it. -/
def CliAddrTextSuccEnv (g : AddrGhost) (evs : List AllocEvent) : Prop :=
  ∃ cap : Nat,
    (addressText g.val).length ≤ cap ∧
    cap ≤ 4 * g.name.bytes.length + 32 ∧
    evs = rustAllocEvents cap 1 ++ rustDeallocEvents cap 1

/-- Ten-stage binary-order `spqr::send` sub-envelope chaining the 9 inner bounded-cost SPQR stages
(`DecodeStateTightEnv` .. `StatesIntoPbTightEnv`) via `ConcatEnv` into the post-send encoded state
allocation `rustAllocEvents stLen' 1` (`0 < stLen' ≤ 286,196`). -/
def SpqrSendSuccTightEnv (stLen' : Nat) (evs : List AllocEvent) : Prop :=
  0 < stLen' ∧ stLen' ≤ 286196 ∧
  ConcatEnv DecodeStateTightEnv
    (ConcatEnv StatesFromPbTightEnv
      (ConcatEnv StatesSendRodataTightEnv
        (ConcatEnv ChainFromTightEnv
          (ConcatEnv ChainAddEpochTight4Env
            (ConcatEnv ChainSendKeyTightEnv
              (ConcatEnv ChainIntoPbTight4Env
                (ConcatEnv MessageSerializeTightEnv
                  (ConcatEnv StatesIntoPbTightEnv
                    (· = rustAllocEvents stLen' 1)))))))))
    evs

/-- Success-only W1 (`send`) sub-envelope over the existential store kit (`ConcatEnv`-chained
`load_session`, PreKey `KyberOpt` + `SpqrSendSuccTightEnv` + AES-CBC + `SignalMessage::new` +
`PreKeySignalMessage::new`, `is_trusted_identity`, `save_identity`, `OTR::apply`, and `store_session`). -/
def W1SendSuccSlotEnv
    (img : Arm64.Obj.Image) (P₀ : PEParams) (i₀ : Inputs) (R : W1SendRealParams)
    (evs : List AllocEvent) : Prop :=
  let F := runFiles i₀
  let kit := w1SessKit R.B img F R.peer
  ∃ (r₀ : SessionRecord (List (BitVec 8))) (sess₀ : Session (List (BitVec 8)))
    (otr₀ : OutgoingTripleRatchet (List (BitVec 8))) (taken₀ : SessionState (List (BitVec 8)))
    (k₀ : IdentityKey) (kpk : PendingKyberPreKey)
    (peerIdBs : List (BitVec 8))
    (g_sm : SignalMessageNewGhost) (call_pk : PreKeyMsgNewCall)
    (G' : SessionGhost) (sess' : Session (List (BitVec 8)))
    (evsAddrL evsPathL evsSpqr evsTrPath evsSvPath evsSvPut
     evsAddrS evsSer evsPutS : List AllocEvent),
    let otr' := otrAfterSome P₀.C (pqxdhSpqrModel P₀) uuidTryParse R.x otr₀
    let r' := storedRecord sess₀ otr' taken₀
    kit.ScopeAt scopeKit StoresGhost.opened.sessions R.x.rem.val r₀ ∧
    DeserializeScopeP_Q NonEmptyV1Q r₀ ∧
    StoresGhost.opened.sessions.get cliIo.rd F (addressText R.x.rem.val) = .ok (encodeRecord r₀) ∧
    encodeRecord r₀ ≠ [] ∧
    r₀.currentSession = some sess₀ ∧
    execOk OutgoingTripleRatchet.fromSessionState sess₀.state = .ok (otr₀, taken₀) ∧
    taken₀.remoteIdentity = some k₀ ∧
    sess₀.pendingPreKey.isSome = true ∧
    sess₀.pendingKyberPreKey = some kpk ∧
    0 < kpk.ciphertext.length ∧
    CliAddrTextSuccEnv R.peer evsAddrL ∧
    CliPathEnv StoresGhost.opened.sessions.path (addressText R.x.rem.val) evsPathL ∧
    SpqrSendSuccTightEnv otr'.pqrState.length evsSpqr ∧
    g_sm.ciphertext.length ≤ w1CtLenCap ∧
    g_sm.pqRatchet.length ≤ 4096 ∧
    signalMessageNewSerLen uuidTryParse g_sm ≤ w1SmSerCap ∧
    kyberPayloadLen call_pk.kp ≤ 1569 ∧
    call_pk.msg.serialized.length ≤ w1SmSerCap ∧
    call_pk.model.serialized.length ≤ w1PkOutCap ∧
    StoresGhost.opened.identity.peers.get cliIo.rd F R.x.rem.val.name = .ok peerIdBs ∧
    CliPathEnv StoresGhost.opened.identity.peers.path R.x.rem.val.name evsTrPath ∧
    CliPathEnv StoresGhost.opened.identity.peers.path R.x.rem.val.name evsSvPath ∧
    CliDirPutEnv StoresGhost.opened.identity.peers R.x.rem.val.name [] evsSvPut ∧
    r'.currentSession = some sess' ∧
    RecordGhostValid ⟨0#64, 8#64, some G'⟩ r' ∧
    (encodeRecord r').length ≤ w1StoreEncCap ∧
    CliAddrTextSuccEnv R.peer evsAddrS ∧
    SerializeSomeCancelEnv G' sess' evsSer ∧
    CliDirPutEnv StoresGhost.opened.sessions [] [] evsPutS ∧
    evs =
      (rustAllocEvents 24 8 ++
        ((evsAddrL ++ ((evsPathL ++ allocBytes1Events (encodeRecord r₀)) ++ sessDeserEvents r₀)) ++
          rustDeallocEvents 24 8)) ++
      (rustAllocEvents kpk.ciphertext.length 1 ++
        ((evsSpqr ++ (rustAllocEvents 32 1 ++
            (rustAllocEvents ((R.x.ptext.length / 16 + 1) * 16) 1 ++
              signalMessageNewEvents uuidTryParse g_sm))) ++
          (preKeyMsgNewEvents call_pk ++
            ((rustAllocEvents 32 8 ++
                ((evsTrPath ++ allocBytes1Events peerIdBs) ++ rustDeallocEvents 32 8)) ++
              ((rustAllocEvents 32 8 ++
                  (((evsSvPath ++ allocBytes1Events peerIdBs) ++
                    (allocBytes1Events R.x.rem.val.name ++ evsSvPut)) ++
                    rustDeallocEvents 32 8)) ++
                (rustAllocEvents 32 1 ++
                  (rustAllocEvents 32 8 ++
                    ((evsAddrS ++ (evsSer ++ evsPutS)) ++ rustDeallocEvents 32 8))))))))

/-- Whole-`main` existential-kit `.send` success-path envelope tying `(P₀, i₀)` to
`pqSendModel P₀ p₀ ptext coins.toList = some (some (st₁, wirePrekey :: bs1))` (`st₁.session = some (x₁, g₁)`)
and composing `M1 → M2 → addressEvents → M3 → R0 → W1SendSuccSlotEnv → R2ConcatTailEnv → M5 → M6Env true`
without `SeqEnv` early-exit shortcuts. -/
def SendSuccMainEnv [LibsignalPlacement]
    (img : Arm64.Obj.Image) (P₀ : PEParams) (i₀ : Inputs) (fullLog : List AllocEvent) : Prop :=
  ∃ (p₀ : PqParty) (ptext : List (BitVec 8)) (coins : List.Vector (BitVec 8) 64)
    (st₁ : PqParty) (x₀ x₁ : RecordExtras) (g₀ g₁ : GhostState (List (BitVec 8)))
    (ag : AddressCall) (peerAddr : AddrV) (w1R : W1SendRealParams)
    (coinsBs ownB bs1 : List (BitVec 8))
    (evsM2 evsR0Path evsEnc evsM5 : List AllocEvent),
    PqxdhPartyInSpecDomain P₀ p₀ ∧
    p₀.session = some (x₀, g₀) ∧
    i₀ = pqSendInputs P₀ p₀ ptext coins ∧
    pqSendModel P₀ p₀ ptext coins.toList = some (some (st₁, wirePrekey :: bs1)) ∧
    st₁.session = some (x₁, g₁) ∧
    PqxdhPartyInSpecDomain P₀ st₁ ∧
    i₀.argv.map bytesOfString = [utf8 "send", ag.bs] ∧
    addrParse uuidTryParse ag.bs = some peerAddr ∧
    parseArgs uuidTryParse (i₀.argv.map bytesOfString) = some (.send peerAddr) ∧
    W1SendRealDom (.send peerAddr) w1R ∧
    w1R.x.ptext = ptext ∧
    coinsBs = coins.toList ∧
    w1R.x.rest = coinsBs ∧
    addrParse uuidTryParse ownB = some ⟨w1R.x.loc.name.bytes, w1R.x.loc.device⟩ ∧
    w1R.x.now = SystemTime.unixEpoch ∧
    i₀.stdin.length ≤ msgCapBytes ∧
    readFileResult (initFsState (cliInputs i₀)).files (utf8 "coins") = .ok coinsBs ∧
    IterConcatEnv M2CollectStepEnv (List.range i₀.argv.length) evsM2 ∧
    StoresGhost.opened.identity.own.get cliIo.rd (runFiles i₀) (utf8 "address") = .ok ownB ∧
    CliPathEnv StoresGhost.opened.identity.own.path (utf8 "address") evsR0Path ∧
    W1SendSuccSlotEnv img P₀ i₀ w1R evsEnc ∧
    0 < bs1.length ∧ bs1.length ≤ sessionCapBytes ∧
    IterConcatEnv (fun dn => IterConcatEnv (fun name => M5LoopAEntryEnv dn.1 name) dn.2)
      [(StoresGhost.opened.identity.peers.path, [w1R.x.rem.val.name]),
       (StoresGhost.opened.sessions.path, [addressText w1R.peer.val])] evsM5 ∧
    AllocEvent.alloc 1568 ∈ evsEnc ∧
    AllocEvent.alloc 16 ∈ evsEnc ∧
    fullLog =
      (rustAllocEvents (16 * i₀.argv.length) 8 ++
        (evsM2 ++ (addressEvents uuidTryParse ag.bs ++
          (allocBytes1Events i₀.stdin ++ allocBytes1Events coinsBs)))) ++
      (((evsR0Path ++ ((allocBytes1Events ownB ++ addressEvents uuidTryParse ownB) ++
            deallocBytes1OfLen ownB.length)) ++
          (evsEnc ++ cliConcat2Events [wirePrekey] bs1)) ++
        (evsM5 ++ rustAllocEvents 1024 1))

/-! ## 2. Inclusion into `RealCliMainEnvOf` -/

private theorem iterSeqEnv_of_iterConcatEnv {α : Type} {Step : α → List AllocEvent → Prop} :
    ∀ {xs : List α} {evs : List AllocEvent},
      IterConcatEnv Step xs evs → IterSeqEnv Step xs evs
  | [], _, h => h
  | _ :: _, _, ⟨e₁, e₂, rfl, h₁, h₂⟩ =>
    Or.inr ⟨e₁, e₂, rfl, h₁, iterSeqEnv_of_iterConcatEnv h₂⟩

private theorem seqEnv_of_self_nil {E : List AllocEvent → Prop} {evs : List AllocEvent}
    (h : E evs) : SeqEnv E FreeOnlyEvs evs :=
  Or.inr ⟨evs, [], (List.append_nil evs).symm, h, FreeOnlyEvs.nil⟩

private theorem cliAddrTextEnv_of_succ {g : AddrGhost} {evs : List AllocEvent}
    (h : CliAddrTextSuccEnv g evs) : CliAddrTextEnv g evs := by
  obtain ⟨cap, _, hcap, rfl⟩ := h
  exact ⟨cap, hcap, Or.inr ⟨rustAllocEvents cap 1, rustDeallocEvents cap 1, rfl, rfl,
    FreeOnlyEvs.singleton 1 cap⟩⟩

private theorem pqEncodeCapTightEnv_of_bounds {stLen' : Nat}
    (hpos : 0 < stLen') (hle : stLen' ≤ 286196) :
    PqEncodeCapTightEnv 286196 (rustAllocEvents stLen' 1) := by
  by_cases hgt : 135167 < stLen'
  · right
    have hcond : 1 ≤ 16 ∧ 1 ≤ stLen' := ⟨by decide, hpos⟩
    simp only [rustAllocEvents, hcond, and_self, ↓reduceIte]
    refine ⟨by simp [nonFreeCount], fun ev hev => ?_⟩
    rw [List.mem_singleton] at hev
    subst hev
    exact ⟨(fun r hr => by injection hr with hr'; subst hr'; exact ⟨hgt, hle⟩),
      (fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩
  · left
    have hsm : stLen' ≤ 135167 := Nat.le_of_not_lt hgt
    exact FineSmallEvs.rustAlloc (by decide) (Nat.le_min.mpr ⟨hle, hsm⟩)
      (smallAllocCost_le_143484_of_le_135167 hsm)

private theorem spqrSendTightCapEnv_of_succ (stBytes ptext : List (BitVec 8))
    {stLen' : Nat} {evs : List AllocEvent}
    (h : SpqrSendSuccTightEnv stLen' evs) :
    SpqrSendTightCapEnv stBytes ptext evs := by
  obtain ⟨hpos, hle,
    e₁, r₁, rfl, h₁,
    e₂, r₂, rfl, h₂,
    e₃, r₃, rfl, h₃,
    e₄, r₄, rfl, h₄,
    e₅, r₅, rfl, h₅,
    e₆, r₆, rfl, h₆,
    e₇, r₇, rfl, h₇,
    e₈, r₈, rfl, h₈,
    e₉, e₁₀, rfl, h₉, rfl⟩ := h
  exact Or.inr (Or.inr ⟨e₁, _, rfl, h₁,
    Or.inr (Or.inr ⟨e₂, _, rfl, h₂,
      Or.inr (Or.inr ⟨e₃, _, rfl, h₃,
        Or.inr (Or.inr ⟨e₄, _, rfl, h₄,
          Or.inr (Or.inr ⟨e₅, _, rfl, h₅,
            Or.inr (Or.inr ⟨e₆, _, rfl, h₆,
              Or.inr (Or.inr ⟨e₇, _, rfl, h₇,
                Or.inr ⟨e₈, _, rfl, h₈,
                  Or.inr ⟨e₉, _, rfl, h₉,
                    seqEnv_of_self_nil (pqEncodeCapTightEnv_of_bounds hpos hle)⟩⟩⟩)⟩)⟩)⟩)⟩)⟩)⟩)

private theorem w1SendRealSlotEnv_of_succ
    {img : Arm64.Obj.Image} {P₀ : PEParams} {i₀ : Inputs} {R : W1SendRealParams}
    {evs : List AllocEvent}
    (h : W1SendSuccSlotEnv img P₀ i₀ R evs) :
    W1SendRealSlotEnv img P₀ i₀ R evs := by
  obtain ⟨r₀, sess₀, otr₀, taken₀, k₀, kpk, peerIdBs, g_sm, call_pk, G', sess',
    evsAddrL, evsPathL, evsSpqr, evsTrPath, evsSvPath, evsSvPut,
    evsAddrS, evsSer, evsPutS,
    hScAt, hDeserQ, hSessGet, henc_ne, hcur₀, hec₀, hremId, hPend, hKpk, hkpk_pos,
    hAddrL, hPathL, hSpqr, hSmCt, hSmPq, hSmSer, hPkKp, hPkMsg, hPkOut,
    hPeerGet, hTrPath, hSvPath, hSvPut, hcur', hRGV, hStoreCap, hAddrS, hSer, hPutS,
    rfl⟩ := h
  let F := runFiles i₀
  have hBoxLoad : BoxAllocEnv (w1SessKit R.B img F R.peer).loadBoxSize (rustAllocEvents 24 8) :=
    Or.inr ⟨by change 0 < 24; decide, rfl⟩
  have hSessRd :
      cliIo.rd F (pathOf StoresGhost.opened.sessions.path (addressText R.x.rem.val)) =
        .ok (encodeRecord r₀) := hSessGet
  have hDirGetL :
      CliDirGetEnv (ReadFileRuleEnv cliIo.rd) F StoresGhost.opened.sessions
        (addressText R.x.rem.val)
        (evsPathL ++ allocBytes1Events (encodeRecord r₀)) := by
    refine Or.inr (Or.inr ⟨evsPathL, allocBytes1Events (encodeRecord r₀), rfl, hPathL, ?_⟩)
    refine seqEnv_of_self_nil ?_
    unfold ReadFileRuleEnv
    rw [hSessRd]
    exact Or.inl rfl
  have hOptDeser :
      OptLoadDeserEnv scopeKit (fun r => RecordDeserializeCancelEnv (encodeRecord r))
        (StoresGhost.opened.sessions.get cliIo.rd F (addressText R.x.rem.val))
        (sessDeserEvents r₀) := by
    cases henc_eq : encodeRecord r₀ with
    | nil => exact absurd henc_eq henc_ne
    | cons b0 bsRest =>
      unfold OptLoadDeserEnv
      rw [hSessGet, henc_eq]
      exact ⟨r₀, henc_eq, hScAt.1, sessDeserEvents_mem_recordDeserializeCancelEnv hDeserQ⟩
  have hLoadPoll :
      (w1RealSessKitBudget F R.peer RecordDeserializeCancelEnv R.B img).loadPollEnv
        StoresGhost.opened.sessions R.x.rem.val
        (evsAddrL ++ ((evsPathL ++ allocBytes1Events (encodeRecord r₀)) ++ sessDeserEvents r₀)) :=
    Or.inr ⟨evsAddrL, _, rfl, cliAddrTextEnv_of_succ hAddrL,
      Or.inr ⟨evsPathL ++ allocBytes1Events (encodeRecord r₀), sessDeserEvents r₀, rfl,
        hDirGetL, seqEnv_of_self_nil hOptDeser⟩⟩
  have hLoadStep :
      SeqEnv (BoxAllocEnv (w1SessKit R.B img F R.peer).loadBoxSize)
        (SeqEnv
          ((w1RealSessKitBudget F R.peer RecordDeserializeCancelEnv R.B img).loadPollEnv
            StoresGhost.opened.sessions R.x.rem.val)
          (· = rustDeallocEvents (w1SessKit R.B img F R.peer).loadBoxSize 8))
        (rustAllocEvents 24 8 ++
          ((evsAddrL ++ ((evsPathL ++ allocBytes1Events (encodeRecord r₀)) ++
              sessDeserEvents r₀)) ++
            rustDeallocEvents 24 8)) :=
    Or.inr ⟨rustAllocEvents 24 8, _, rfl, hBoxLoad,
      Or.inr ⟨_, rustDeallocEvents 24 8, rfl, hLoadPoll, rfl⟩⟩
  have hKyber :
      KyberOptStepEnv (sess₀.pendingKyberPreKey.map (·.ciphertext))
        (rustAllocEvents kpk.ciphertext.length 1) := by
    rw [hKpk]
    exact Or.inr ⟨hkpk_pos, rfl⟩
  have hOtrSome :
      OtrEncryptStepEnv (SpqrSendTightCapEnv otr₀.pqrState R.x.rest) R.x.ptext.length
        (fun evs' =>
          ∃ g : SignalMessageNewGhost,
            (g.ciphertext.length ≤ w1CtLenCap ∧
              g.pqRatchet.length ≤ 4096 ∧
              signalMessageNewSerLen uuidTryParse g ≤ w1SmSerCap) ∧
            SignalMessageNewEnv uuidTryParse g evs')
        (evsSpqr ++ (rustAllocEvents 32 1 ++
          (rustAllocEvents ((R.x.ptext.length / 16 + 1) * 16) 1 ++
            signalMessageNewEvents uuidTryParse g_sm))) :=
    Or.inr ⟨evsSpqr, _, rfl, spqrSendTightCapEnv_of_succ otr₀.pqrState R.x.rest hSpqr,
      Or.inr (Or.inr ⟨rustAllocEvents 32 1, _, rfl, seqEnv_of_self_nil rfl,
        Or.inr ⟨rustAllocEvents ((R.x.ptext.length / 16 + 1) * 16) 1,
          signalMessageNewEvents uuidTryParse g_sm, rfl, rfl,
          seqEnv_of_self_nil ⟨g_sm, ⟨hSmCt, hSmPq, hSmSer⟩, rfl⟩⟩⟩)⟩
  have hPkNew :
      (∃ call : PreKeyMsgNewCall,
        (kyberPayloadLen call.kp ≤ 1569 ∧
          call.msg.serialized.length ≤ w1SmSerCap ∧
          call.model.serialized.length ≤ w1PkOutCap) ∧
        PreKeyMsgNewEnv call (preKeyMsgNewEvents call_pk)) :=
    ⟨call_pk, ⟨hPkKp, hPkMsg, hPkOut⟩, rfl⟩
  have hPeerRd :
      cliIo.rd F (pathOf StoresGhost.opened.identity.peers.path R.x.rem.val.name) =
        .ok peerIdBs := hPeerGet
  have hDirGetPeer : ∀ {evsP},
      CliPathEnv StoresGhost.opened.identity.peers.path R.x.rem.val.name evsP →
      CliDirGetEnv (ReadFileRuleEnv cliIo.rd) F StoresGhost.opened.identity.peers
        R.x.rem.val.name (evsP ++ allocBytes1Events peerIdBs) := by
    intro evsP hP
    refine Or.inr (Or.inr ⟨evsP, allocBytes1Events peerIdBs, rfl, hP, seqEnv_of_self_nil ?_⟩)
    unfold ReadFileRuleEnv
    rw [hPeerRd]
    exact Or.inl rfl
  have hTrustPoll :
      CliSmallStorePollEnv cliIo.rd F StoresGhost.opened.identity.peers R.x.rem.val.name
        (evsTrPath ++ allocBytes1Events peerIdBs) :=
    Or.inr ⟨[], evsTrPath ++ allocBytes1Events peerIdBs, rfl, Or.inl rfl,
      Or.inl (hDirGetPeer hTrPath)⟩
  have hSavePoll :
      CliSmallStorePollEnv cliIo.rd F StoresGhost.opened.identity.peers R.x.rem.val.name
        ((evsSvPath ++ allocBytes1Events peerIdBs) ++
          (allocBytes1Events R.x.rem.val.name ++ evsSvPut)) :=
    Or.inr ⟨[], _, rfl, Or.inl rfl,
      Or.inr ⟨evsSvPath ++ allocBytes1Events peerIdBs,
        allocBytes1Events R.x.rem.val.name ++ evsSvPut, rfl, hDirGetPeer hSvPath,
        Or.inr ⟨[], allocBytes1Events R.x.rem.val.name ++ evsSvPut, rfl,
          ⟨Nat.zero_le 32, fun _ h => nomatch h⟩,
          seqEnv_of_self_nil (Or.inr ⟨allocBytes1Events R.x.rem.val.name, evsSvPut, rfl, rfl, hSvPut⟩)⟩⟩⟩
  let otr' := otrAfterSome P₀.C (pqxdhSpqrModel P₀) uuidTryParse R.x otr₀
  let r' := storedRecord sess₀ otr' taken₀
  have hRecSer : RecordSerializeCancelEnv ⟨0#64, 8#64, some G'⟩ r' evsSer := by
    unfold RecordSerializeCancelEnv
    rw [hcur']
    exact hSer
  have hStorePoll :
      (w1RealSessKitBudget F R.peer RecordDeserializeCancelEnv R.B img).storePollEnv
        StoresGhost.opened.sessions R.x.rem.val r'
        (evsAddrS ++ (evsSer ++ evsPutS)) :=
    ⟨⟨0#64, 8#64, some G'⟩, ⟨hRGV, hStoreCap⟩,
      Or.inr ⟨evsAddrS, evsSer ++ evsPutS, rfl, cliAddrTextEnv_of_succ hAddrS,
        Or.inr ⟨evsSer, evsPutS, rfl, hRecSer, seqEnv_of_self_nil hPutS⟩⟩⟩
  have hApply :
      FromApplyTightEnv (w1SessKit R.B img F R.peer)
        (w1RealSessKitBudget F R.peer RecordDeserializeCancelEnv R.B img)
        StoresGhost.opened.sessions R.x.rem.val sess₀ otr' taken₀
        (rustAllocEvents 32 1 ++
          (rustAllocEvents 32 8 ++ ((evsAddrS ++ (evsSer ++ evsPutS)) ++ rustDeallocEvents 32 8))) :=
    Or.inr ⟨rustAllocEvents 32 1, _, rfl, seqEnv_of_self_nil rfl,
      Or.inr ⟨rustAllocEvents 32 8, _, rfl, Or.inr ⟨by change 0 < 32; decide, rfl⟩,
        Or.inr ⟨evsAddrS ++ (evsSer ++ evsPutS), rustDeallocEvents 32 8, rfl, hStorePoll,
          seqEnv_of_self_nil rfl⟩⟩⟩
  have hSave :
      FromSaveTightEnv (w1SessKit R.B img F R.peer)
        (w1RealSessKitBudget F R.peer RecordDeserializeCancelEnv R.B img)
        StoresGhost.opened.sessions
        (w1IdKit R.B img F R.peer) (w1RealIdKitBudget F R.peer R.B img)
        ((w1IdKit R.B img F R.peer).trustUpdate StoresGhost.opened.identity
          R.x.rem.val k₀ .sending (.ok true))
        R.x.rem.val sess₀ otr' taken₀ k₀
        ((rustAllocEvents 32 8 ++
            (((evsSvPath ++ allocBytes1Events peerIdBs) ++
              (allocBytes1Events R.x.rem.val.name ++ evsSvPut)) ++
              rustDeallocEvents 32 8)) ++
          (rustAllocEvents 32 1 ++
            (rustAllocEvents 32 8 ++
              ((evsAddrS ++ (evsSer ++ evsPutS)) ++ rustDeallocEvents 32 8)))) :=
    Or.inr ⟨_, _, rfl,
      Or.inr ⟨rustAllocEvents 32 8, _, rfl, Or.inr ⟨by change 0 < 32; decide, rfl⟩,
        Or.inr ⟨_, rustDeallocEvents 32 8, rfl, hSavePoll, rfl⟩⟩,
      Or.inr hApply⟩
  have hCm :
      FromCmTightEnv (w1SessKit R.B img F R.peer)
        (w1RealSessKitBudget F R.peer RecordDeserializeCancelEnv R.B img)
        StoresGhost.opened.sessions
        (w1IdKit R.B img F R.peer) (w1RealIdKitBudget F R.peer R.B img)
        StoresGhost.opened.identity
        R.x.rem.val R.x.rem.name sess₀ otr' taken₀ k₀
        ((rustAllocEvents 32 8 ++
            ((evsTrPath ++ allocBytes1Events peerIdBs) ++ rustDeallocEvents 32 8)) ++
          ((rustAllocEvents 32 8 ++
              (((evsSvPath ++ allocBytes1Events peerIdBs) ++
                (allocBytes1Events R.x.rem.val.name ++ evsSvPut)) ++
                rustDeallocEvents 32 8)) ++
            (rustAllocEvents 32 1 ++
              (rustAllocEvents 32 8 ++
                ((evsAddrS ++ (evsSer ++ evsPutS)) ++ rustDeallocEvents 32 8))))) :=
    Or.inr ⟨_, _, rfl,
      Or.inr ⟨rustAllocEvents 32 8, _, rfl, Or.inr ⟨by change 0 < 32; decide, rfl⟩,
        Or.inr ⟨_, rustDeallocEvents 32 8, rfl, hTrustPoll, rfl⟩⟩,
      Or.inr (Or.inr hSave)⟩
  exact Or.inr ⟨_, _, rfl, hLoadStep,
    Or.inr (Or.inr (Or.inr ⟨[], _, rfl, FreeOnlyEvs.nil,
      Or.inr ⟨r₀, sess₀, otr₀, taken₀, hScAt, hcur₀, hec₀,
        Or.inr ⟨k₀, hremId, Or.inr ⟨hPend,
          Or.inr (Or.inr ⟨rustAllocEvents kpk.ciphertext.length 1, _, rfl, hKyber,
            Or.inr ⟨_, _, rfl, hOtrSome,
              Or.inr (Or.inr ⟨preKeyMsgNewEvents call_pk, _, rfl, hPkNew,
                Or.inr hCm⟩)⟩⟩)⟩⟩⟩⟩))⟩

private def succKutf8 (s : String) : List (BitVec 8) :=
  (s.toList.flatMap String.utf8EncodeChar).map fun b => BitVec.ofNat 8 b.toNat

private theorem succ_byteArray_toList_eq_data : ∀ (bs : ByteArray), bs.toList = bs.data.toList
  | ⟨⟨xs⟩⟩ => by
    have hloop : ∀ i r, ByteArray.toList.loop ⟨⟨xs⟩⟩ i r = r.reverse ++ xs.drop i := by
      intro i r
      fun_induction ByteArray.toList.loop ⟨⟨xs⟩⟩ i r with
      | case1 i r hi ih =>
        have hget : (ByteArray.mk ⟨xs⟩).get! i = xs[i] := getElem!_pos (⟨xs⟩ : Array UInt8) i hi
        rw [ih, hget, List.reverse_cons, List.append_assoc, List.singleton_append,
          List.drop_eq_getElem_cons hi]
      | case2 i r hni =>
        rw [List.drop_eq_nil_of_le (Nat.le_of_not_lt hni), List.append_nil]
    exact hloop 0 []

private theorem succ_utf8_eq_kutf8 (s : String) : utf8 s = succKutf8 s := by
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  simp [utf8, succKutf8, List.utf8Encode, succ_byteArray_toList_eq_data]

private theorem peers_path_eq :
    StoresGhost.opened.identity.peers.path = succKutf8 "identities" :=
  succ_utf8_eq_kutf8 "identities"

private theorem sessions_path_eq :
    StoresGhost.opened.sessions.path = succKutf8 "sessions" :=
  succ_utf8_eq_kutf8 "sessions"

private theorem succ_repr_utf8_eq_kutf8 (s : String) :
    CryptoVerification.LibsignalTripleRatchetRepr.utf8 s = succKutf8 s := by
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  simp [CryptoVerification.LibsignalTripleRatchetRepr.utf8, succKutf8,
    List.utf8Encode, succ_byteArray_toList_eq_data]

/-- Inclusion of `SendSuccMainEnv` into
`RealCliMainEnvOf (mkExistentialRealCalleeEnvs img S P₀) i₀`. -/
theorem sendSuccMainEnv_sub_realCliMainEnvOf [LibsignalPlacement]
    (img : Arm64.Obj.Image) (S : RunSem) (P₀ : PEParams) (i₀ : Inputs)
    (evs : List AllocEvent)
    (hSucc : SendSuccMainEnv img P₀ i₀ evs) :
    RealCliMainEnvOf (mkExistentialRealCalleeEnvs img S P₀) i₀ evs := by
  obtain ⟨p₀, ptext, coins, st₁, x₀, x₁, g₀, g₁, ag, peerAddr, w1R,
    coinsBs, ownB, bs1, evsM2, evsR0Path, evsEnc, evsM5,
    _, _, _, _, _, _, _, _, hparse, hw1Dom, _, _, _, _, _,
    hstdin_le, hcoins, hM2,
    hOwnGet, hR0Path, hW1Succ, _, hbs1_le, hM5, _, _, rfl⟩ := hSucc
  have hCoinsEnv :
      ReadFileEnv (initFsState (cliInputs i₀)).files (utf8 "coins")
        (allocBytes1Events coinsBs) := by
    unfold ReadFileEnv
    rw [hcoins]
    exact Or.inl rfl
  have hM3 :
      M3PhaseEnv true i₀.stdin (initFsState (cliInputs i₀)).files (utf8 "coins")
        (allocBytes1Events i₀.stdin ++ allocBytes1Events coinsBs) :=
    Or.inr ⟨allocBytes1Events i₀.stdin, allocBytes1Events coinsBs, rfl, Or.inl rfl,
      seqEnv_of_self_nil hCoinsEnv⟩
  have hSetup :
      CliMainSetupEnv uuidTryParse i₀ (some ag) true
        (rustAllocEvents (16 * i₀.argv.length) 8 ++
          (evsM2 ++ (addressEvents uuidTryParse ag.bs ++
            (allocBytes1Events i₀.stdin ++ allocBytes1Events coinsBs)))) :=
    Or.inr ⟨rustAllocEvents (16 * i₀.argv.length) 8, _, rfl, Or.inr rfl,
      Or.inr ⟨evsM2, _, rfl, iterSeqEnv_of_iterConcatEnv hM2,
        Or.inr ⟨addressEvents uuidTryParse ag.bs, _, rfl, rfl, hM3⟩⟩⟩
  have hBoundedSetup :
      CliMainBoundedSetupEnv i₀.argv.length
        (rustAllocEvents (16 * i₀.argv.length) 8 ++
          (evsM2 ++ (addressEvents uuidTryParse ag.bs ++
            (allocBytes1Events i₀.stdin ++ allocBytes1Events coinsBs)))) :=
    cliMainBoundedSetupEnv_of_setup_any uuidTryParse i₀ (some ag) true (fun _ => hstdin_le) hSetup
  have hd := hw1Dom peerAddr rfl
  have ⟨hPeer40, hRem40⟩ := peer_and_rem_name_le_40_of_send hparse hd.1 hd.2.1
  let dirs : List (List (BitVec 8) × List (List (BitVec 8))) :=
    [(StoresGhost.opened.identity.peers.path, [w1R.x.rem.val.name]),
     (StoresGhost.opened.sessions.path, [addressText w1R.peer.val])]
  have hDirsBounds :
      ∀ dn ∈ dirs,
        dn.1.length ≤ cliMaxDirPathBytes ∧ ∀ nm ∈ dn.2, nm.length ≤ cliMaxAddrTextBytes := by
    intro dn hdn
    rcases List.mem_cons.mp hdn with rfl | hdn2
    · refine ⟨by dsimp only; rw [peers_path_eq]; unfold succKutf8 cliMaxDirPathBytes; decide,
        fun nm hnm => ?_⟩
      rw [List.mem_singleton] at hnm
      subst hnm
      exact Nat.le_trans hRem40 (by unfold cliMaxAddrTextBytes; decide)
    · rw [List.mem_singleton] at hdn2
      subst hdn2
      refine ⟨by dsimp only; rw [sessions_path_eq]; unfold succKutf8 cliMaxDirPathBytes; decide,
        fun nm hnm => ?_⟩
      rw [List.mem_singleton] at hnm
      subst hnm
      exact w1_peer_addressText_le_64 hPeer40
  let w : ValidPostSetupWitness i₀ := {
    g := ⟨i₀, .send peerAddr, some none, 0#64, 0#64, 0#64, 0#64, 0#64⟩
    g_i := rfl
    parse_ok := hparse
    stdin_le := hstdin_le
    dirs := dirs
    dirs_sum_le := by simp [dirs, cliMaxDirtyEntries]
    dirs_bounds := hDirsBounds
    ok := true
  }
  have hOwnRd :
      cliIo.rd (runFiles i₀) (pathOf StoresGhost.opened.identity.own.path (utf8 "address")) =
        .ok ownB := hOwnGet
  have hR0 :
      R0OpenedEnv cliIo.rd (runFiles i₀)
        (evsR0Path ++
          ((allocBytes1Events ownB ++ addressEvents uuidTryParse ownB) ++
            deallocBytes1OfLen ownB.length)) := by
    right
    unfold TempFileBracketEnv
    refine Or.inr ⟨evsR0Path, _, rfl, hR0Path, ?_⟩
    rw [hOwnRd]
    exact seqEnv_of_self_nil
      ⟨allocBytes1Events ownB ++ addressEvents uuidTryParse ownB,
        deallocBytes1OfLen ownB.length, rfl,
        ⟨allocBytes1Events ownB, addressEvents uuidTryParse ownB, rfl, rfl,
          Or.inr ⟨[], addressEvents uuidTryParse ownB, rfl, FreeOnlyEvs.nil, Or.inr rfl⟩⟩,
        rfl⟩
  have hEncSlot : (mkExistentialRealCalleeEnvs img S P₀ w.g).encEnv evsEnc :=
    ⟨w1R, hw1Dom, w1SendRealSlotEnv_of_succ hW1Succ⟩
  have hTail :
      R2ConcatTailEnv sessionCapBytes (cliConcat2Events [wirePrekey] bs1) :=
    Or.inr ⟨[wirePrekey], by decide, bs1, hbs1_le, seqEnv_of_self_nil rfl⟩
  have hArm :
      RunArmEnv cliIo.rd (runFiles w.g.i) (mkExistentialRealCalleeEnvs img S P₀ w.g)
        sessionCapBytes w.g.i.stdin w.g.c
        (evsEnc ++ cliConcat2Events [wirePrekey] bs1) :=
    Or.inr (Or.inr ⟨evsEnc, cliConcat2Events [wirePrekey] bs1, rfl, hEncSlot, hTail⟩)
  have hRunOpened :
      CliRunOpenedEnv cliIo.rd (mkExistentialRealCalleeEnvs img S P₀ w.g) sessionCapBytes w.g
        ((evsR0Path ++
            ((allocBytes1Events ownB ++ addressEvents uuidTryParse ownB) ++
              deallocBytes1OfLen ownB.length)) ++
          (evsEnc ++ cliConcat2Events [wirePrekey] bs1)) :=
    cliRunOfR0Env_of_r0_arm hR0 hArm
  obtain ⟨evsM5_peers, restM5, rfl, hM5_peers, evsM5_sess, endM5, rfl, hM5_sess, rfl⟩ := hM5
  rw [List.append_nil]
  obtain ⟨evsP1, nilP1, rfl, hP1, rfl⟩ := hM5_peers
  rw [List.append_nil]
  obtain ⟨evsS1, nilS1, rfl, hS1, rfl⟩ := hM5_sess
  rw [List.append_nil]
  have hPeersNe : StoresGhost.opened.identity.peers.path ≠ [] := by
    rw [peers_path_eq]; decide
  have hSessNe : StoresGhost.opened.sessions.path ≠ [] := by
    rw [sessions_path_eq]; decide
  have hDirPeers :
      M5DirStepEnv StoresGhost.opened.identity.peers.path [w1R.x.rem.val.name] evsP1 := by
    refine seqEnv_of_self_nil (Or.inr ⟨evsP1, [], (List.append_nil _).symm, ?_, rfl⟩)
    simp only [LibsignalBinary.Proofs.PeakBudget.CliMainPeakSpec.M5WriteStepEnv, hPeersNe,
      ↓reduceIte]
    exact hP1
  have hDirSess :
      M5DirStepEnv StoresGhost.opened.sessions.path [addressText w1R.peer.val] evsS1 := by
    refine seqEnv_of_self_nil (Or.inr ⟨evsS1, [], (List.append_nil _).symm, ?_, rfl⟩)
    simp only [LibsignalBinary.Proofs.PeakBudget.CliMainPeakSpec.M5WriteStepEnv, hSessNe,
      ↓reduceIte]
    exact hS1
  have hM5Phase : M5PhaseEnv w.dirs (evsP1 ++ evsS1) :=
    seqEnv_of_self_nil
      (Or.inr ⟨evsP1, evsS1, rfl, hDirPeers,
        Or.inr ⟨evsS1, [], (List.append_nil _).symm, hDirSess, rfl⟩⟩)
  have hM6 : M6Env w.ok (rustAllocEvents 1024 1) :=
    seqEnv_of_self_nil (Or.inr rfl)
  exact Or.inr ⟨_, _, rfl, hBoundedSetup,
    Or.inr ⟨w, rfl,
      Or.inr ⟨_, _, rfl, hRunOpened,
        Or.inr ⟨evsP1 ++ evsS1, rustAllocEvents 1024 1, rfl, hM5Phase, hM6⟩⟩⟩⟩

/-! ## 3. Concrete Existential-Kit Success-Path Witness -/

private def sendWitnessCoins : List.Vector (BitVec 8) 64 :=
  List.Vector.replicate 64 0#8

private def sendWitnessP0 : PqParty :=
  match pqInitModel X0 W0 emptyParty b0 t0 with
  | some (some (p, _)) => p
  | _ => emptyParty

private theorem sendWitnessP0_props :
    sendWitnessP0.session.isSome = true ∧ PqxdhPartyInSpecDomain W0 sendWitnessP0 := by
  obtain ⟨p, x, g, hp_eq, hp_sess, hp_wf⟩ := pqInitModel_W0_creates_wfSession X0
  have heq : sendWitnessP0 = p := by
    unfold sendWitnessP0
    rw [hp_eq]
  rw [heq]
  have hp_some : p.session.isSome = true := by
    rw [hp_sess]
    rfl
  exact ⟨hp_some, hp_wf⟩

private theorem sendWitnessP0_party : sendWitnessP0.party = .A := by
  decide +kernel

private def sendWitnessX0 : RecordExtras :=
  match sendWitnessP0.session with
  | some (x, _) => x
  | none =>
    { pending := ⟨none, 0#32, pk0, 0#64⟩
      kyber := none
      remoteRegistrationId := 0#32
      localRegistrationId := 0#32
      aliceBaseKey := [] }

private def sendWitnessG0 : GhostState (List (BitVec 8)) :=
  match sendWitnessP0.session with
  | some (_, g) => g
  | none =>
    { party := .A
      session :=
        { sessionVersion := 4#32
          localIdentity := ⟨pk0⟩
          remoteIdentity := some ⟨pk0⟩
          rootKey := 0#256
          previousCounter := 0#32
          senderChain := none
          receiverChains := []
          pqRatchetState := []
          pendingPreKey := false }
      epoch := 0
      chainEpochs := [] }

private theorem sendWitnessP0_session_eq :
    sendWitnessP0.session = some (sendWitnessX0, sendWitnessG0) := by
  cases hs : sendWitnessP0.session with
  | none =>
    have his := sendWitnessP0_props.1
    rw [hs] at his
    cases his
  | some xg =>
    rcases xg with ⟨x, g⟩
    unfold sendWitnessX0 sendWitnessG0
    rw [hs]

private def sendWitnessR0 : SessionRecord (List (BitVec 8)) :=
  toRecord (extrasOf fun _ => sendWitnessX0) sendWitnessG0

private theorem sendWitnessR0_encode_eq :
    encodeRecord sendWitnessR0 = pqSessBytes sendWitnessP0 := by
  unfold sendWitnessR0 pqSessBytes
  rw [sendWitnessP0_session_eq, ← encodeRecordX_eq_toRecord (fun _ => sendWitnessX0) sendWitnessG0]

private theorem sendWitnessR0_encode_len_pos :
    0 < (encodeRecord sendWitnessR0).length := by decide +kernel

private theorem sendWitnessR0_encode_ne_nil :
    encodeRecord sendWitnessR0 ≠ [] := by
  intro hnil
  have hpos := sendWitnessR0_encode_len_pos
  rw [hnil] at hpos
  cases hpos

private def sendWitnessSt1 : PqParty :=
  match pqSendModel W0 sendWitnessP0 [] sendWitnessCoins.toList with
  | some (some (st1, _)) => st1
  | _ => sendWitnessP0

private def sendWitnessBs1 : List (BitVec 8) :=
  match pqSendModel W0 sendWitnessP0 [] sendWitnessCoins.toList with
  | some (some (_, _ :: bs1)) => bs1
  | _ => []

private theorem sendWitness_pqSendModel_head_ok :
    (match pqSendModel W0 sendWitnessP0 [] sendWitnessCoins.toList with
     | some (some (_, b :: _)) => b == wirePrekey
     | _ => false) = true := by
  decide +kernel

private theorem sendWitness_pqSendModel_eq :
    pqSendModel W0 sendWitnessP0 [] sendWitnessCoins.toList =
      some (some (sendWitnessSt1, wirePrekey :: sendWitnessBs1)) := by
  have hok := sendWitness_pqSendModel_head_ok
  unfold sendWitnessSt1 sendWitnessBs1
  cases hm : pqSendModel W0 sendWitnessP0 [] sendWitnessCoins.toList with
  | none => rw [hm] at hok; cases hok
  | some inner =>
    cases inner with
    | none => rw [hm] at hok; cases hok
    | some pair =>
      rcases pair with ⟨st1, out⟩
      cases out with
      | nil => rw [hm] at hok; cases hok
      | cons b bs1 =>
        rw [hm] at hok
        have hb : b = wirePrekey := eq_of_beq hok
        subst hb
        rfl

private theorem prost_varint_len_le_10 : ∀ (fuel n : Nat), n < 128 ^ (fuel + 1) →
    (CryptoGames.LibsignalSessionApi.Prost.varint n).length ≤ fuel + 1
  | 0, n, hn => by
    unfold CryptoGames.LibsignalSessionApi.Prost.varint
    split
    · simp
    · omega
  | fuel + 1, n, hn => by
    unfold CryptoGames.LibsignalSessionApi.Prost.varint
    split
    · simp
    · simp only [List.length_cons]
      have hdiv : n / 128 < 128 ^ (fuel + 1) := by
        rw [Nat.pow_succ] at hn
        omega
      have ih := prost_varint_len_le_10 fuel (n / 128) hdiv
      omega

private theorem prost_uint32Field_len_le (tag : Nat) (htag : tag < 16)
    (o : Option (BitVec 32)) :
    (CryptoGames.LibsignalSessionApi.Prost.uint32Field tag o).length ≤ 6 := by
  cases o with
  | none => simp [CryptoGames.LibsignalSessionApi.Prost.uint32Field]
  | some v =>
    simp only [CryptoGames.LibsignalSessionApi.Prost.uint32Field,
      CryptoGames.LibsignalSessionApi.Prost.key, List.length_append]
    have hk := prost_varint_len_le_10 0 (8 * tag + 0) (by omega)
    have hv := prost_varint_len_le_10 4 v.toNat (by have := v.isLt; omega)
    omega

private theorem prost_bytesField_some_len_le (tag : Nat) (htag : tag < 16)
    (b : List (BitVec 8)) (hb : b.length < 128 ^ 4) :
    (CryptoGames.LibsignalSessionApi.Prost.bytesField tag (some b)).length ≤ 5 + b.length := by
  simp only [CryptoGames.LibsignalSessionApi.Prost.bytesField,
    CryptoGames.LibsignalSessionApi.Prost.key, List.length_append]
  have hk := prost_varint_len_le_10 0 (8 * tag + 2) (by omega)
  have hv := prost_varint_len_le_10 3 b.length hb
  omega

private theorem proto_encodeVarintAux_len_le : ∀ (k : Nat) (v : BitVec 64),
    (CryptoVerification.LibsignalProtoCodec.encodeVarintAux k v).length ≤ k
  | 0, _ => by simp [CryptoVerification.LibsignalProtoCodec.encodeVarintAux]
  | k + 1, v => by
    unfold CryptoVerification.LibsignalProtoCodec.encodeVarintAux
    split
    · simp
    · simp only [List.length_cons]
      have ih := proto_encodeVarintAux_len_le k (v >>> 7)
      omega

private theorem proto_encodeUint32Field_len_le (tag : Nat) (o : Option (BitVec 32)) :
    (CryptoVerification.LibsignalProtoCodec.encodeUint32Field tag o).length ≤ 20 := by
  cases o with
  | none => simp [CryptoVerification.LibsignalProtoCodec.encodeUint32Field]
  | some v =>
    simp only [CryptoVerification.LibsignalProtoCodec.encodeUint32Field,
      CryptoVerification.LibsignalProtoCodec.encodeKey,
      CryptoVerification.LibsignalProtoCodec.encodeVarint, List.length_append]
    have h1 := proto_encodeVarintAux_len_le 10 (BitVec.ofNat 64 (tag * 8 +
      CryptoVerification.LibsignalProtoCodec.WireType.varint.toNat))
    have h2 := proto_encodeVarintAux_len_le 10 (v.zeroExtend 64)
    omega

private theorem proto_encodeBytesField_len_le (tag : Nat) (o : Option (List (BitVec 8))) :
    (CryptoVerification.LibsignalProtoCodec.encodeBytesField tag o).length ≤
      20 + (match o with | none => 0 | some b => b.length) := by
  cases o with
  | none => simp [CryptoVerification.LibsignalProtoCodec.encodeBytesField]
  | some v =>
    simp only [CryptoVerification.LibsignalProtoCodec.encodeBytesField,
      CryptoVerification.LibsignalProtoCodec.encodeKey,
      CryptoVerification.LibsignalProtoCodec.encodeVarint, List.length_append]
    have h1 := proto_encodeVarintAux_len_le 10 (BitVec.ofNat 64 (tag * 8 +
      CryptoVerification.LibsignalProtoCodec.WireType.lengthDelimited.toNat))
    have h2 := proto_encodeVarintAux_len_le 10 (BitVec.ofNat 64 v.length)
    omega

private theorem aesCbcEncrypt_nil_len
    (E : CryptoGames.CBC.AesKey → CryptoGames.CBC.Block → CryptoGames.CBC.Block)
    (k : CryptoGames.CBC.AesKey) (iv : CryptoGames.CBC.Block) :
    (CryptoGames.LibsignalSession.aesCbcEncrypt E k iv []).length = 16 := by
  unfold CryptoGames.LibsignalSession.aesCbcEncrypt
  generalize hv : ((CryptoGames.CBC.cbcPkcs7EncryptOnly E [].length).enc (k, iv) ⟨[], rfl⟩).toList = l
  have hl : l.length = 1 := by
    rw [← hv]
    exact List.Vector.toList_length _
  cases l with
  | nil => cases hl
  | cons b tl =>
    cases tl with
    | cons _ _ => cases hl
    | nil => simp [CryptoGames.CBC.blockToBytesLE]

private theorem serializedPartyAddresses_len_le
    (sender recipient : CryptoGames.Party) (bs : List (BitVec 8))
    (h : CryptoVerification.E2E.serializedPartyAddresses uuidTryParse sender recipient = some bs) :
    bs.length = 36 := by
  unfold CryptoVerification.E2E.serializedPartyAddresses at h
  cases hs : CryptoVerification.LibsignalTripleRatchetRepr.serviceIdParse uuidTryParse
      (CryptoVerification.LibsignalTripleRatchetRepr.utf8 (partyAddressName sender)) with
  | none => rw [hs] at h; cases h
  | some s =>
    rw [hs] at h
    cases hr : CryptoVerification.LibsignalTripleRatchetRepr.serviceIdParse uuidTryParse
        (CryptoVerification.LibsignalTripleRatchetRepr.utf8 (partyAddressName recipient)) with
    | none => rw [hr] at h; cases h
    | some r =>
      rw [hr] at h
      injection h with h
      subst h
      simp [CryptoVerification.LibsignalTripleRatchetRepr.addrBytes]

private theorem signalMessage_new_serialized_bounds
    (C : CryptoGames.LibsignalSession.Crypto) (messageVersion : BitVec 8)
    (macKey : BitVec 256) (addresses : Option (List (BitVec 8))) (senderRatchetKey : PublicKey)
    (counter previousCounter : BitVec 32) (ciphertext : List (BitVec 8))
    (senderIdentity receiverIdentity : IdentityKey) (pqRatchet : List (BitVec 8))
    (hct : ciphertext.length = 16)
    (hpq : pqRatchet.length ≤ 4096)
    (haddrs : ∀ a, addresses = some a → a.length ≤ 36) :
    0 < (SignalMessage.new C.F protoSignalCodec messageVersion macKey addresses senderRatchetKey
          counter previousCounter ciphertext senderIdentity receiverIdentity pqRatchet).serialized.length ∧
    (SignalMessage.new C.F protoSignalCodec messageVersion macKey addresses senderRatchetKey
      counter previousCounter ciphertext senderIdentity receiverIdentity pqRatchet).serialized.length ≤
      4400 := by
  let content := CryptoGames.LibsignalSession.serializeContent protoSignalCodec messageVersion
    senderRatchetKey counter previousCounter ciphertext pqRatchet addresses
  have hmac :
      (CryptoGames.LibsignalSession.computeMac C.F senderIdentity receiverIdentity macKey
        content).length ≤ 8 :=
    List.length_take_le 8 _
  have hcontent : 0 < content.length ∧ content.length ≤ 4392 := by
    dsimp only [content]
    simp only [CryptoGames.LibsignalSession.serializeContent, protoSignalCodec,
      CryptoVerification.LibsignalProtoCodec.encode, List.length_append, List.length_cons]
    have hf1 := proto_encodeBytesField_len_le 1 (some senderRatchetKey.serialize)
    have hrk : senderRatchetKey.serialize.length = 33 := by
      simp [PublicKey.serialize]
    have hf2 := proto_encodeUint32Field_len_le 2 (some counter)
    have hf3 := proto_encodeUint32Field_len_le 3 (some previousCounter)
    have hf4 := proto_encodeBytesField_len_le 4 (some ciphertext)
    have hf5 := proto_encodeBytesField_len_le 5 (if pqRatchet.isEmpty then none else some pqRatchet)
    have hf5_inner :
        (match (if pqRatchet.isEmpty then none else some pqRatchet) with
         | none => 0 | some b => b.length) ≤ 4096 := by
      split <;> simp_all
    have hf6 := proto_encodeBytesField_len_le 6 addresses
    have hf6_inner : (match addresses with | none => 0 | some b => b.length) ≤ 36 := by
      cases addresses with
      | none => exact Nat.zero_le 36
      | some a => exact haddrs a rfl
    dsimp only at hf1 hf4
    omega
  change 0 < (content ++ CryptoGames.LibsignalSession.computeMac C.F senderIdentity
      receiverIdentity macKey content).length ∧
    (content ++ CryptoGames.LibsignalSession.computeMac C.F senderIdentity
      receiverIdentity macKey content).length ≤ 4400
  rw [List.length_append]
  omega

set_option linter.unusedSimpArgs false in
private theorem otr_encrypt_ok_msg_serialized_bounds
    (C : CryptoGames.LibsignalSession.Crypto)
    (spqr : CryptoGames.LibsignalSession.Spqr (List (BitVec 8)) (List (BitVec 8)))
    (addrs : Option (List (BitVec 8))) (coins : List (BitVec 8))
    (o : OutgoingTripleRatchet (List (BitVec 8)))
    (msg : SignalMessage) (o' : OutgoingTripleRatchet (List (BitVec 8)))
    (haddrs : ∀ a, addrs = some a → a.length ≤ 36)
    (hspqr : ∀ ns pk pm, spqr.send o.pqrState coins = some (ns, pk, pm) → pm.length ≤ 4096)
    (h : CryptoGames.LibsignalSession.Mut.exec
      (OutgoingTripleRatchet.encrypt C protoSignalCodec spqr [] addrs coins) o = (.ok msg, o')) :
    0 < msg.serialized.length ∧ msg.serialized.length ≤ 4400 := by
  unfold CryptoGames.LibsignalSession.Mut.exec OutgoingTripleRatchet.encrypt at h
  cases hp : spqr.sendPanics o.pqrState coins
  · cases hs : spqr.send o.pqrState coins with
    | none =>
      simp only [ExceptT.run, StateT.run, pure, ExceptT.mk, bind, ExceptT.bind,
        ExceptT.bindCont, MonadExcept.throw, MonadExceptOf.throw, ExceptT.instMonad,
        MonadState.get, get, getThe, MonadStateOf.get, StateT.get, set, StateT.set,
        StateT.pure, StateT.bind, Functor.map, StateT.map, liftM, monadLift,
        MonadLift.monadLift, ExceptT.lift, ExceptT.pure, throwThe,
        CryptoGames.LibsignalSession.liftE, hp, Bool.false_eq_true, ↓reduceIte, hs] at h
      injection h with h1 _
      nomatch h1
    | some triple =>
      rcases triple with ⟨ns, pk, pm⟩
      cases hn : o.senderChainKey.nextChainKey C.F with
      | error e =>
        simp only [ExceptT.run, StateT.run, pure, ExceptT.mk, bind, ExceptT.bind,
          ExceptT.bindCont, MonadExcept.throw, MonadExceptOf.throw, ExceptT.instMonad,
          MonadState.get, get, getThe, MonadStateOf.get, StateT.get, set, StateT.set,
          StateT.pure, StateT.bind, Functor.map, StateT.map, liftM, monadLift,
          MonadLift.monadLift, ExceptT.lift, ExceptT.pure, throwThe,
          CryptoGames.LibsignalSession.liftE, hp, Bool.false_eq_true, ↓reduceIte, hs, hn] at h
        injection h with h1 _
        nomatch h1
      | ok next =>
        simp only [ExceptT.run, StateT.run, pure, ExceptT.mk, bind, ExceptT.bind,
          ExceptT.bindCont, MonadExcept.throw, MonadExceptOf.throw, ExceptT.instMonad,
          MonadState.get, get, getThe, MonadStateOf.get, StateT.get, set, StateT.set,
          StateT.pure, StateT.bind, Functor.map, StateT.map, liftM, monadLift,
          MonadLift.monadLift, ExceptT.lift, ExceptT.pure, throwThe,
          CryptoGames.LibsignalSession.liftE, hp, Bool.false_eq_true, ↓reduceIte, hs, hn] at h
        injection h with h1 _
        injection h1 with hmsg
        subst hmsg
        exact signalMessage_new_serialized_bounds C o.sessionVersion
          ((o.senderChainKey.messageKeys C.F).generateKeys C.F pk).macKey addrs
          o.senderRatchetKey.publicKey o.senderChainKey.index o.previousCounter
          (CryptoGames.LibsignalSession.aesCbcEncrypt C.E
            ((o.senderChainKey.messageKeys C.F).generateKeys C.F pk).cipherKey
            ((o.senderChainKey.messageKeys C.F).generateKeys C.F pk).iv [])
          o.localIdentityKey o.remoteIdentityKey pm
          (aesCbcEncrypt_nil_len C.E _ _) (hspqr ns pk pm hs) haddrs
  · simp only [ExceptT.run, StateT.run, pure, ExceptT.mk, bind, ExceptT.bind,
      ExceptT.bindCont, MonadExcept.throw, MonadExceptOf.throw, ExceptT.instMonad,
      MonadState.get, get, getThe, MonadStateOf.get, StateT.get, set, StateT.set,
      StateT.pure, StateT.bind, Functor.map, StateT.map, liftM, monadLift,
      MonadLift.monadLift, ExceptT.lift, ExceptT.pure, throwThe,
      CryptoGames.LibsignalSession.liftE, hp, ↓reduceIte] at h
    injection h with h1 _
    nomatch h1

private def spqrSendMsgBounded (P : PEParams)
    (s : SessionState (List (BitVec 8))) (coins : List (BitVec 8)) : Bool :=
  match (CryptoGames.LibsignalSession.Mut.exec OutgoingTripleRatchet.fromSessionState s).1 with
  | .ok otr =>
    match (CryptoVerification.E2E.pqxdhSpqrSession P).send otr.pqrState coins with
    | some (_, _, pm) => decide (pm.length ≤ 4096)
    | none => true
  | .error _ => true

private theorem pqSendModel_some_bs1_bounds
    (P : PEParams) (st : PqParty) (x : RecordExtras)
    (g : GhostState (List (BitVec 8))) (coins : List (BitVec 8))
    (st1 : PqParty) (hd : BitVec 8) (bs1 : List (BitVec 8))
    (hsess : st.session = some (x, g))
    (hm : pqSendModel P st [] coins = some (some (st1, hd :: bs1)))
    (hky : (match x.kyber with | none => 0 | some k => k.ciphertext.length) ≤ 1569)
    (hspqr_b : spqrSendMsgBounded P g.session coins = true) :
    0 < bs1.length ∧ bs1.length ≤ sessionCapBytes := by
  unfold pqSendModel at hm
  rw [hsess] at hm
  dsimp only at hm
  cases henc :
      SessionState.messageEncrypt P.C protoSignalCodec
        (CryptoVerification.E2E.pqxdhSpqrSession P)
        ((CryptoVerification.E2E.pqxdhSessionParams P).sendAddrs g.party)
        [] coins g.session with
  | mk res s1 =>
    cases res with
    | error e =>
      rw [henc] at hm
      cases e <;> cases hm
    | ok msg =>
      rw [henc] at hm
      dsimp only at hm
      cases hrem : g.session.remoteIdentity with
      | none =>
        rw [hrem] at hm
        cases hm
      | some k =>
        rw [hrem] at hm
        dsimp only at hm
        split at hm
        · cases hm
        · injection hm with hm1
          injection hm1 with hpair
          have hwire :
              (if g.session.pendingPreKey then
                 wirePrekey :: CryptoVerification.E2E.firstMessageBody x g.session msg
               else CryptoVerification.E2E.wireWhisper :: msg.serialized) =
                hd :: bs1 :=
            congrArg Prod.snd hpair
          unfold SessionState.messageEncrypt at henc
          cases hfr :
              CryptoGames.LibsignalSession.Mut.exec OutgoingTripleRatchet.fromSessionState
                g.session with
          | mk rfr taken =>
            cases rfr with
            | error e =>
              rw [hfr] at henc
              cases henc
            | ok otr =>
              rw [hfr] at henc
              dsimp only at henc
              cases he2 :
                  CryptoGames.LibsignalSession.Mut.exec
                    (OutgoingTripleRatchet.encrypt P.C protoSignalCodec
                      (CryptoVerification.E2E.pqxdhSpqrSession P) []
                      (g.session.encryptAddresses
                        ((CryptoVerification.E2E.pqxdhSessionParams P).sendAddrs g.party))
                      coins)
                    otr with
              | mk r2 o' =>
                cases r2 with
                | error e =>
                  rw [he2] at henc
                  cases henc
                | ok msg2 =>
                  rw [he2] at henc
                  injection henc with h1 _
                  injection h1 with hmsg_eq
                  subst hmsg_eq
                  have haddrs : ∀ a,
                      g.session.encryptAddresses
                        ((CryptoVerification.E2E.pqxdhSessionParams P).sendAddrs g.party) =
                          some a →
                      a.length ≤ 36 := by
                    intro a ha
                    unfold SessionState.encryptAddresses at ha
                    split at ha
                    · cases hp_party : g.party <;>
                        simp only [hp_party, CryptoVerification.E2E.pqxdhSessionParams,
                          CryptoGames.LibsignalSession.Params.sendAddrs] at ha
                      · have h36 := serializedPartyAddresses_len_le .A .B a ha
                        omega
                      · have h36 := serializedPartyAddresses_len_le .B .A a ha
                        omega
                    · cases ha
                  have hspqr : ∀ ns pk pm,
                      (CryptoVerification.E2E.pqxdhSpqrSession P).send otr.pqrState coins =
                        some (ns, pk, pm) →
                      pm.length ≤ 4096 := by
                    intro ns pk pm hs
                    unfold spqrSendMsgBounded at hspqr_b
                    rw [hfr] at hspqr_b
                    dsimp only at hspqr_b
                    rw [hs] at hspqr_b
                    exact of_decide_eq_true hspqr_b
                  have ⟨hmsg_pos, hmsg_le⟩ :=
                    otr_encrypt_ok_msg_serialized_bounds P.C
                      (CryptoVerification.E2E.pqxdhSpqrSession P) _ coins otr msg2 o'
                      haddrs hspqr he2
                  cases hpp : g.session.pendingPreKey
                  · rw [hpp] at hwire
                    simp only [Bool.false_eq_true, ↓reduceIte, List.cons.injEq] at hwire
                    rcases hwire with ⟨_, hbs1⟩
                    rw [← hbs1]
                    unfold sessionCapBytes
                    omega
                  · rw [hpp] at hwire
                    simp only [↓reduceIte, List.cons.injEq] at hwire
                    rcases hwire with ⟨_, hbs1⟩
                    rw [← hbs1]
                    unfold CryptoVerification.E2E.firstMessageBody PreKeySignalMessage.new
                      CryptoGames.LibsignalSessionApi.ProtoPreKeySignalMessage.encode
                      sessionCapBytes
                    simp only [List.length_cons, List.length_append]
                    have hp1 := prost_uint32Field_len_le 1 (by decide) x.pending.preKeyId
                    have hbk : x.pending.baseKey.serialize.length = 33 := by
                      simp [PublicKey.serialize]
                    have hik : g.session.localIdentity.serialize.length = 33 := by
                      simp [IdentityKey.serialize, PublicKey.serialize]
                    have hp2 := prost_bytesField_some_len_le 2 (by decide)
                      x.pending.baseKey.serialize (by omega)
                    have hp3 := prost_bytesField_some_len_le 3 (by decide)
                      g.session.localIdentity.serialize (by omega)
                    have hp4 := prost_bytesField_some_len_le 4 (by decide) msg2.serialized
                      (by omega)
                    have hp5 := prost_uint32Field_len_le 5 (by decide)
                      (some x.localRegistrationId)
                    have hp6 := prost_uint32Field_len_le 6 (by decide)
                      (some x.pending.signedPreKeyId)
                    have hp7 := prost_uint32Field_len_le 7 (by decide)
                      ((x.kyber.map fun k =>
                        (⟨k.preKeyId, k.ciphertext⟩ : KyberPayload)).map (·.preKeyId))
                    have hp8 :
                        (CryptoGames.LibsignalSessionApi.Prost.bytesField 8
                          ((x.kyber.map fun k =>
                            (⟨k.preKeyId, k.ciphertext⟩ : KyberPayload)).map
                            (·.ciphertext))).length ≤ 1574 := by
                      cases hky_c : x.kyber with
                      | none => simp [CryptoGames.LibsignalSessionApi.Prost.bytesField]
                      | some kv =>
                        rw [hky_c] at hky
                        simp only [Option.map_some] at hky ⊢
                        have h8 := prost_bytesField_some_len_le 8 (by decide) kv.ciphertext
                          (by omega)
                        omega
                    omega

private theorem sendWitnessX0_kyber_le :
    (match sendWitnessX0.kyber with | none => 0 | some k => k.ciphertext.length) ≤ 1569 := by
  decide +kernel

private theorem sendWitness_spqrSendMsgBounded :
    spqrSendMsgBounded W0 sendWitnessG0.session sendWitnessCoins.toList = true := by
  decide +kernel

private theorem sendWitnessBs1_bounds :
    0 < sendWitnessBs1.length ∧ sendWitnessBs1.length ≤ sessionCapBytes :=
  pqSendModel_some_bs1_bounds W0 sendWitnessP0 sendWitnessX0 sendWitnessG0
    sendWitnessCoins.toList sendWitnessSt1 wirePrekey sendWitnessBs1
    sendWitnessP0_session_eq sendWitness_pqSendModel_eq
    sendWitnessX0_kyber_le sendWitness_spqrSendMsgBounded

private theorem sendWitnessSt1_session_isSome :
    sendWitnessSt1.session.isSome = true := by
  decide +kernel

private def sendWitnessX1 : RecordExtras :=
  match sendWitnessSt1.session with
  | some (x, _) => x
  | none => sendWitnessX0

private def sendWitnessG1 : GhostState (List (BitVec 8)) :=
  match sendWitnessSt1.session with
  | some (_, g) => g
  | none => sendWitnessG0

private theorem sendWitnessSt1_session_eq :
    sendWitnessSt1.session = some (sendWitnessX1, sendWitnessG1) := by
  cases hs : sendWitnessSt1.session with
  | none =>
    have his := sendWitnessSt1_session_isSome
    rw [hs] at his
    cases his
  | some xg =>
    rcases xg with ⟨x, g⟩
    unfold sendWitnessX1 sendWitnessG1
    rw [hs]

private theorem sendWitnessSt1_rec_le :
    (encodeRecordUnderExtras (fun _ => sendWitnessX1) sendWitnessG1).length ≤ fileCapBytes := by
  decide +kernel

private theorem sendWitnessSt1_lr_lt :
    lastResortUses sendWitnessSt1 < 2 ^ 25 := by
  decide +kernel

private theorem sendWitnessSt1_wf :
    PqxdhPartyInSpecDomain W0 sendWitnessSt1 := by
  refine wfPq_step X0 W0 sendWitnessP0 sendWitnessSt1 sendWitnessP0_props.2
    (PqStep.send [] sendWitnessCoins sendWitnessSt1 (wirePrekey :: sendWitnessBs1)
      (by decide) sendWitness_pqSendModel_eq)
    sendWitnessSt1_lr_lt ?_
  intro x g hs
  rw [sendWitnessSt1_session_eq] at hs
  injection hs with hpair
  injection hpair with hx hg
  subst hx; subst hg
  exact sendWitnessSt1_rec_le

private def sendWitnessInputs : Inputs :=
  pqSendInputs W0 sendWitnessP0 [] sendWitnessCoins

private def sendWitnessOwnAddr : AddrV :=
  ⟨utf8 (partyAddressName .A), 1#8⟩

private def sendWitnessAddressCall : AddressCall where
  out := 0#64
  p := 0#64
  bs := bytesOfString (partyAddress .B).text

private def sendWitnessEncGhost : WithStoresEncGhost where
  ret := 0#64
  ptA := 0#64
  ptext := []
  remA := 0#64
  rem := nonVacSendAddrGhost nonVacSendPeer
  locA := 0#64
  loc := nonVacSendAddrGhost sendWitnessOwnAddr
  now := SystemTime.unixEpoch
  cur := 0#64
  rest := sendWitnessCoins.toList
  ssA := 0#64
  idA := 0#64

private def sendWitnessW1Params : W1SendRealParams where
  B := ⟨0⟩
  peer := nonVacSendAddrGhost nonVacSendPeer
  x := sendWitnessEncGhost

private theorem sendWitnessW1Params_dom :
    W1SendRealDom (.send nonVacSendPeer) sendWitnessW1Params := by
  intro p hp
  injection hp with hp
  subst hp
  exact ⟨rfl, rfl, Nat.zero_le msgCapBytes⟩

private theorem sendWitnessInputs_cliPqxdh :
    CliPqxdhInputs W0 sendWitnessInputs :=
  ⟨sendWitnessP0, sendWitnessP0_props.2,
    Or.inr (Or.inl ⟨[], sendWitnessCoins, by decide, rfl⟩)⟩

private theorem sendWitnessInputs_argv_map :
    sendWitnessInputs.argv.map bytesOfString = [utf8 "send", sendWitnessAddressCall.bs] := by
  have hs : bytesOfString "send" = utf8 "send" := by
    unfold bytesOfString
    rw [succ_utf8_eq_kutf8 "send"]
    rfl
  unfold sendWitnessInputs pqSendInputs sendWitnessAddressCall
  rw [sendWitnessP0_party]
  simp [CryptoVerification.SignalSession.pqInputs, CryptoVerification.SignalSession.Cmd.argv, hs]

private theorem sendWitnessAddressCall_parse :
    addrParse uuidTryParse sendWitnessAddressCall.bs = some nonVacSendPeer := by
  have hp := parseArgs_send .B
  have hs : bytesOfString "send" = utf8 "send" := by
    unfold bytesOfString
    rw [succ_utf8_eq_kutf8 "send"]
    rfl
  unfold sendWitnessAddressCall nonVacSendPeer
  dsimp only
  cases ha : addrParse uuidTryParse (bytesOfString (partyAddress .B).text) with
  | none =>
    simp only [CryptoVerification.SignalSession.Cmd.argv, List.map_cons, List.map_nil,
      parseArgs, hs, ha, Option.map_none, ↓reduceIte] at hp
    cases hp
  | some a =>
    simp only [CryptoVerification.SignalSession.Cmd.argv, List.map_cons, List.map_nil,
      parseArgs, hs, ha, Option.map_some, ↓reduceIte] at hp
    injection hp with hp'
    injection hp' with hp1
    exact congrArg some hp1

private theorem sendWitnessInputs_parseArgs :
    parseArgs uuidTryParse (sendWitnessInputs.argv.map bytesOfString) =
      some (.send nonVacSendPeer) := by
  unfold sendWitnessInputs pqSendInputs
  rw [sendWitnessP0_party]
  exact parseArgs_send .B

private theorem sendWitnessOwn_get :
    StoresGhost.opened.identity.own.get cliIo.rd (runFiles sendWitnessInputs) (utf8 "address") =
      .ok (CryptoVerification.SignalSession.textBytes (partyAddress .A).text) := by
  have h := ownAddr_pqSend W0 sendWitnessP0 [] sendWitnessCoins
  rwa [sendWitnessP0_party] at h

private theorem sendWitnessOwn_parse :
    addrParse uuidTryParse (CryptoVerification.SignalSession.textBytes (partyAddress .A).text) =
      some ⟨sendWitnessW1Params.x.loc.name.bytes, sendWitnessW1Params.x.loc.device⟩ :=
  addrParse_textBytes .A

private theorem sendWitnessCoins_readFileResult :
    readFileResult (initFsState (cliInputs sendWitnessInputs)).files (utf8 "coins") =
      .ok sendWitnessCoins.toList := by
  have hpath : pathStr (utf8 "coins") = "coins" := by
    unfold pathStr
    rw [succ_utf8_eq_kutf8 "coins"]
    decide
  have hanc : CryptoVerification.SignalSession.ancestors "coins" = [] := by
    unfold CryptoVerification.SignalSession.ancestors CryptoVerification.SignalSession.pathComps
    rw [List.splitOn_eq_splitOnP, List.splitOnP_eq_singleton (by decide)]
    rfl
  have hblk : blockingAncestorF (initFsState (cliInputs sendWitnessInputs)).files "coins" = none := by
    unfold blockingAncestorF
    rw [hanc]
    rfl
  have hne : (Arm64.normalizePath "coins").isEmpty = false := by decide
  have hent : (initFsState (cliInputs sendWitnessInputs)).files "coins" =
      some (.file sendWitnessCoins.toList) := by
    unfold initFsState Arm64.FsState.files Arm64.FsState.getEntry
    simp only [hne, Bool.false_eq_true, ↓reduceIte, Arm64.FsState.setFd]
    have hf_cli : ∀ i : Inputs, (cliInputs i).files = i.files := fun _ => rfl
    have hf_pq : ∀ p : PqParty, (pqSendInputs W0 p [] sendWitnessCoins).files =
        encodeDir W0 p ++ [("coins", sendWitnessCoins.toList)] := by
      intro p
      unfold pqSendInputs CryptoVerification.SignalSession.pqInputs
        CryptoVerification.SignalSession.coinsFile
      simp only [List.append_nil]
    have hf : (cliInputs sendWitnessInputs).files =
        encodeDir W0 sendWitnessP0 ++ [("coins", sendWitnessCoins.toList)] :=
      (hf_cli sendWitnessInputs).trans (hf_pq sendWitnessP0)
    rw [hf, List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp only [Arm64.FsState.setFile, Arm64.FsState.setEntry, beq_self_eq_true, ↓reduceIte]
  have hcap : sendWitnessCoins.toList.length ≤ fileCapBytes := by decide
  unfold readFileResult CryptoVerification.SignalSession.CliExt.readViewF
  rw [hpath, hblk, hent]
  simp only [hcap, ↓reduceIte]

private def mkCliPathSimple (dir name : List (BitVec 8)) : List AllocEvent :=
  if dir = [] then allocBytes1Events name
  else
    let cap0 := dir.length
    let cap1 := reserveCap cap0 cap0 1
    let need2 := decide (cap1 - (cap0 + 1) < name.length)
    let capFinal := if need2 then reserveCap cap1 (cap0 + 1) name.length else cap1
    (rustAllocEvents cap0 1 ++ rustReallocEvents cap0 cap1 1) ++
      (if need2 then rustReallocEvents cap1 capFinal 1 else [])

private theorem mkCliPathSimple_mem (dir name : List (BitVec 8)) :
    CliPathEnv dir name (mkCliPathSimple dir name) := by
  unfold CliPathEnv mkCliPathSimple
  by_cases hdir : dir = []
  · simp only [hdir, ↓reduceIte]
  · simp only [hdir, ↓reduceIte]
    cases hneed : decide (reserveCap dir.length dir.length 1 - (dir.length + 1) < name.length) <;>
      simp only [Bool.false_eq_true, ↓reduceIte] <;>
      exact ⟨_, _, rfl, ⟨_, _, rfl, rfl, rfl⟩, rfl⟩

private def mkM5EntrySimple (dir name : List (BitVec 8)) : List AllocEvent :=
  let cap0 := dir.length
  let cap1 := reserveCap cap0 cap0 1
  let need2 := decide (cap1 - (cap0 + 1) < name.length)
  let capFinal := if need2 then reserveCap cap1 (cap0 + 1) name.length else cap1
  (((rustAllocEvents cap0 1 ++ rustReallocEvents cap0 cap1 1) ++
      (if need2 then rustReallocEvents cap1 capFinal 1 else [])) ++ []) ++
    rustDeallocEvents capFinal 1

private theorem mkM5EntrySimple_mem (dir name : List (BitVec 8)) :
    M5LoopAEntryEnv dir name (mkM5EntrySimple dir name) := by
  unfold M5LoopAEntryEnv mkM5EntrySimple
  dsimp only
  cases hneed : decide (reserveCap dir.length dir.length 1 - (dir.length + 1) < name.length) <;>
    simp only [Bool.false_eq_true, ↓reduceIte] <;>
    exact ⟨_, _, rfl, ⟨_, [], rfl, ⟨_, _, rfl, ⟨_, _, rfl, rfl, rfl⟩, rfl⟩, Or.inl rfl⟩, rfl⟩

private theorem spqrSendSuccTightEnv_of_bounds {stLen' : Nat}
    (hpos : 0 < stLen') (hle : stLen' ≤ 286196) :
    SpqrSendSuccTightEnv stLen' (rustAllocEvents stLen' 1) := by
  have hnilF : ∀ o c r, FineSmallEvs o c r [] := fun _ _ _ =>
    ⟨Nat.zero_le _, Nat.zero_le _, fun _ h => nomatch h⟩
  exact ⟨hpos, hle,
    [], _, rfl, SpqrTightEvs.nil _ _ _,
    [], _, rfl, SpqrTightEvs.nil _ _ _,
    [], _, rfl, hnilF _ _ _,
    [], _, rfl, hnilF _ _ _,
    [], _, rfl, hnilF _ _ _,
    [], _, rfl, hnilF _ _ _,
    [], _, rfl, hnilF _ _ _,
    [], _, rfl, hnilF _ _ _,
    [], _, rfl, SpqrTightEvs.nil _ _ _,
    rfl⟩

/-! ### Concrete Post-Encrypt Session Extraction & `SessionGhostValid` Arena Witness -/

private def sendWitnessSess0 : Session (List (BitVec 8)) :=
  match sendWitnessR0.currentSession with
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

private theorem sendWitnessR0_currentSession :
    sendWitnessR0.currentSession = some sendWitnessSess0 := by
  have his : sendWitnessR0.currentSession.isSome = true := by decide +kernel
  cases hs : sendWitnessR0.currentSession with
  | none => rw [hs] at his; cases his
  | some s =>
    unfold sendWitnessSess0
    rw [hs]

private theorem sendWitnessSess0_fromSessionState_isOk :
    (match execOk OutgoingTripleRatchet.fromSessionState sendWitnessSess0.state with
     | .ok _ => true
     | .error _ => false) = true := by
  decide +kernel

private def sendWitnessOtr0 : OutgoingTripleRatchet (List (BitVec 8)) :=
  match execOk OutgoingTripleRatchet.fromSessionState sendWitnessSess0.state with
  | .ok (otr, _) => otr
  | .error _ =>
    { senderRatchetKey := ⟨pk0, ⟨List.Vector.replicate 32 0#8⟩⟩
      senderChainKey := ⟨0#256, 0#32⟩
      previousCounter := 0#32
      pqrState := []
      sessionVersion := 4#8
      localIdentityKey := ⟨pk0⟩
      remoteIdentityKey := ⟨pk0⟩ }

private def sendWitnessTaken0 : SessionState (List (BitVec 8)) :=
  match execOk OutgoingTripleRatchet.fromSessionState sendWitnessSess0.state with
  | .ok (_, taken) => taken
  | .error _ => sendWitnessSess0.state

private theorem sendWitnessSess0_fromSessionState_eq :
    execOk OutgoingTripleRatchet.fromSessionState sendWitnessSess0.state =
      .ok (sendWitnessOtr0, sendWitnessTaken0) := by
  have hok := sendWitnessSess0_fromSessionState_isOk
  cases he : execOk OutgoingTripleRatchet.fromSessionState sendWitnessSess0.state with
  | error _ => rw [he] at hok; cases hok
  | ok pair =>
    rcases pair with ⟨otr, taken⟩
    unfold sendWitnessOtr0 sendWitnessTaken0
    rw [he]

private theorem sendWitnessTaken0_remoteIdentity_isSome :
    sendWitnessTaken0.remoteIdentity.isSome = true := by
  decide +kernel

private def sendWitnessK0 : IdentityKey :=
  match sendWitnessTaken0.remoteIdentity with
  | some k => k
  | none => ⟨pk0⟩

private theorem sendWitnessTaken0_remoteIdentity_eq :
    sendWitnessTaken0.remoteIdentity = some sendWitnessK0 := by
  have his := sendWitnessTaken0_remoteIdentity_isSome
  cases hk : sendWitnessTaken0.remoteIdentity with
  | none => rw [hk] at his; cases his
  | some k =>
    unfold sendWitnessK0
    rw [hk]

private theorem sendWitnessSess0_pendingPreKey_isSome :
    sendWitnessSess0.pendingPreKey.isSome = true := by
  decide +kernel

private def sendWitnessPpk : PendingPreKey :=
  match sendWitnessSess0.pendingPreKey with
  | some p => p
  | none => ⟨None, 0#32, pk0, 0#64⟩ where
    None : Option (BitVec 32) := none

private theorem sendWitnessSess0_pendingPreKey_eq :
    sendWitnessSess0.pendingPreKey = some sendWitnessPpk := by
  have his := sendWitnessSess0_pendingPreKey_isSome
  cases hp : sendWitnessSess0.pendingPreKey with
  | none => rw [hp] at his; cases his
  | some p =>
    unfold sendWitnessPpk
    rw [hp]

private theorem sendWitnessSess0_pendingKyber_isSome :
    sendWitnessSess0.pendingKyberPreKey.isSome = true := by
  decide +kernel

private def sendWitnessKpk : PendingKyberPreKey :=
  match sendWitnessSess0.pendingKyberPreKey with
  | some k => k
  | none => ⟨0#32, []⟩

private theorem sendWitnessSess0_pendingKyber_eq :
    sendWitnessSess0.pendingKyberPreKey = some sendWitnessKpk := by
  have his := sendWitnessSess0_pendingKyber_isSome
  cases hk : sendWitnessSess0.pendingKyberPreKey with
  | none => rw [hk] at his; cases his
  | some k =>
    unfold sendWitnessKpk
    rw [hk]

private theorem sendWitnessKpk_ct_len :
    sendWitnessKpk.ciphertext.length = 1569 := by
  decide +kernel

private def sendWitnessOtr' : OutgoingTripleRatchet (List (BitVec 8)) :=
  otrAfterSome W0.C (pqxdhSpqrModel W0) uuidTryParse sendWitnessW1Params.x sendWitnessOtr0

private theorem sendWitnessOtr'_pqr_bounds :
    0 < sendWitnessOtr'.pqrState.length ∧ sendWitnessOtr'.pqrState.length ≤ 286196 := by
  decide +kernel

private def sendWitnessR' : SessionRecord (List (BitVec 8)) :=
  storedRecord sendWitnessSess0 sendWitnessOtr' sendWitnessTaken0

private def sendWitnessSess' : Session (List (BitVec 8)) :=
  { sendWitnessSess0 with state := sendWitnessOtr'.applyToSessionState sendWitnessTaken0 }

private theorem sendWitnessR'_currentSession :
    sendWitnessR'.currentSession = some sendWitnessSess' := rfl

private theorem sendWitnessR'_encode_le :
    (encodeRecord sendWitnessR').length ≤ w1StoreEncCap := by
  decide +kernel

private theorem sendWitnessSess'_remoteIdentity_isSome :
    sendWitnessSess'.state.remoteIdentity.isSome = true := by
  decide +kernel

private def sendWitnessRemIk' : IdentityKey :=
  match sendWitnessSess'.state.remoteIdentity with
  | some ik => ik
  | none => ⟨pk0⟩

private theorem sendWitnessSess'_remoteIdentity_eq :
    sendWitnessSess'.state.remoteIdentity = some sendWitnessRemIk' := by
  have his := sendWitnessSess'_remoteIdentity_isSome
  cases hk : sendWitnessSess'.state.remoteIdentity with
  | none => rw [hk] at his; cases his
  | some ik =>
    unfold sendWitnessRemIk'
    rw [hk]

private theorem sendWitnessSess'_senderChain_isSome :
    sendWitnessSess'.state.senderChain.isSome = true := by
  decide +kernel

private def sendWitnessSc' : SenderChain :=
  match sendWitnessSess'.state.senderChain with
  | some sc => sc
  | none => ⟨⟨pk0, ⟨List.Vector.replicate 32 0#8⟩⟩, ⟨0#256, 0#32⟩⟩

private theorem sendWitnessSess'_senderChain_eq :
    sendWitnessSess'.state.senderChain = some sendWitnessSc' := by
  have his := sendWitnessSess'_senderChain_isSome
  cases hsc : sendWitnessSess'.state.senderChain with
  | none => rw [hsc] at his; cases his
  | some sc =>
    unfold sendWitnessSc'
    rw [hsc]

private theorem sendWitnessSess'_rc_len :
    sendWitnessSess'.state.receiverChains.length = 1 := by
  decide +kernel

private def sendWitnessRc0 : ReceiverChain :=
  match sendWitnessSess'.state.receiverChains with
  | rc :: _ => rc
  | [] => { senderRatchetKey := pk0, chainKey := none, messageKeys := [] }

private theorem sendWitnessSess'_receiverChains_eq :
    sendWitnessSess'.state.receiverChains = [sendWitnessRc0] := by
  have hlen := sendWitnessSess'_rc_len
  cases hrc : sendWitnessSess'.state.receiverChains with
  | nil => rw [hrc] at hlen; cases hlen
  | cons rc rest =>
    cases rest with
    | cons _ _ => rw [hrc] at hlen; cases hlen
    | nil =>
      unfold sendWitnessRc0
      rw [hrc]

private theorem sendWitnessRc0_chainKey_isSome :
    sendWitnessRc0.chainKey.isSome = true := by
  decide +kernel

private def sendWitnessRc0Ck : ChainKey :=
  match sendWitnessRc0.chainKey with
  | some ck => ck
  | none => ⟨0#256, 0#32⟩

private theorem sendWitnessRc0_chainKey_eq :
    sendWitnessRc0.chainKey = some sendWitnessRc0Ck := by
  have his := sendWitnessRc0_chainKey_isSome
  cases hck : sendWitnessRc0.chainKey with
  | none => rw [hck] at his; cases his
  | some ck =>
    unfold sendWitnessRc0Ck
    rw [hck]

private theorem sendWitnessSess'_shape_facts :
    sendWitnessRc0.messageKeys = [] ∧
    sendWitnessSess'.state.pendingPreKey = true ∧
    sendWitnessSess'.aliceBaseKey.length = 33 ∧
    PublicKey.deserialize sendWitnessSess'.state.localIdentity.publicKey.serialize =
      .ok sendWitnessSess'.state.localIdentity.publicKey ∧
    PublicKey.deserialize sendWitnessRemIk'.publicKey.serialize =
      .ok sendWitnessRemIk'.publicKey ∧
    PublicKey.deserialize sendWitnessSc'.ratchetKey.publicKey.serialize =
      .ok sendWitnessSc'.ratchetKey.publicKey ∧
    clampScalar sendWitnessSc'.ratchetKey.privateKey.bytes =
      sendWitnessSc'.ratchetKey.privateKey.bytes ∧
    PublicKey.deserialize sendWitnessPpk.baseKey.serialize =
      .ok sendWitnessPpk.baseKey ∧
    PublicKey.deserialize sendWitnessRc0.senderRatchetKey.serialize =
      .ok sendWitnessRc0.senderRatchetKey := by
  decide +kernel

private def ghostBase : BitVec 64 := 0x10000#64

private def sendWitnessPendTail : List (BitVec 8) :=
  (match sendWitnessPpk.preKeyId with
   | none => [0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8]
   | some v => [1#8, 0#8, 0#8, 0#8] ++ leBytes 4 v.toNat) ++
  leBytes 8 sendWitnessPpk.timestamp.toNat ++
  leBytes 4 sendWitnessPpk.signedPreKeyId.toNat ++
  [0#8, 0#8, 0#8, 0#8]

private def sendWitnessKyberTail : List (BitVec 8) :=
  leBytes 4 sendWitnessKpk.preKeyId.toNat ++ [0#8, 0#8, 0#8, 0#8]

private def sendWitnessRc0Ghost : ChainGhost where
  srk := ⟨33#64, ghostBase + 896#64, sendWitnessRc0.senderRatchetKey.serialize⟩
  priv := ⟨0#64, 1#64, []⟩
  mkCap := 0#64
  mkPtr := 8#64
  keys := []
  ck := ⟨32#64, ghostBase + 944#64⟩

private def sendWitnessG' : SessionGhost where
  localIk := ⟨33#64, ghostBase + 512#64, sendWitnessSess'.state.localIdentity.publicKey.serialize⟩
  remoteIk := ⟨33#64, ghostBase + 560#64, sendWitnessRemIk'.publicKey.serialize⟩
  root := ⟨32#64, ghostBase + 608#64⟩
  chainsCap := 1#64
  chainsPtr := ghostBase + 352#64
  chains := [sendWitnessRc0Ghost]
  alice := ⟨33#64, ghostBase + 656#64, sendWitnessSess'.aliceBaseKey⟩
  pq := ⟨BitVec.ofNat 64 sendWitnessSess'.state.pqRatchetState.length, ghostBase + 4096#64⟩
  sender := some
    { srk := ⟨33#64, ghostBase + 704#64, sendWitnessSc'.ratchetKey.publicKey.serialize⟩
      priv := ⟨32#64, ghostBase + 752#64, sendWitnessSc'.ratchetKey.privateKey.bytes.toList⟩
      mkCap := 0#64
      mkPtr := 8#64
      ck := ⟨32#64, ghostBase + 800#64⟩ }
  pending := some
    { vec := ⟨33#64, ghostBase + 848#64, sendWitnessPpk.baseKey.serialize⟩
      tail := sendWitnessPendTail }
  kyber := some
    { vec := ⟨1569#64, ghostBase + 1024#64, sendWitnessKpk.ciphertext⟩
      tail := sendWitnessKyberTail }
  regIds :=
    leBytes 4 sendWitnessSess'.remoteRegistrationId.toNat ++
    leBytes 4 sendWitnessSess'.localRegistrationId.toNat

private theorem sendWitnessSess'_pendingPreKey_eq :
    sendWitnessSess'.pendingPreKey = some sendWitnessPpk := by
  dsimp only [sendWitnessSess']
  exact sendWitnessSess0_pendingPreKey_eq

private theorem sendWitnessSess'_pendingKyber_eq :
    sendWitnessSess'.pendingKyberPreKey = some sendWitnessKpk := by
  dsimp only [sendWitnessSess']
  exact sendWitnessSess0_pendingKyber_eq

private theorem pendingRel_of_none
    {o : Option CryptoVerification.LibsignalTripleRatchetRepr.TailVecGhost}
    {p : PendingPreKey}
    (hs : o.isSome = true)
    (hp : p.preKeyId = none)
    (hb : o.map (fun g => g.vec.bytes) = some p.baseKey.serialize)
    (ht1 : o.map (fun g => g.tail.take 4) = some [0#8, 0#8, 0#8, 0#8])
    (ht3 : o.map (fun g => (g.tail.drop 8).take 8) = some (leBytes 8 p.timestamp.toNat))
    (ht4 : o.map (fun g => (g.tail.drop 16).take 4) = some (leBytes 4 p.signedPreKeyId.toNat))
    (hlen : o.map (fun g => g.vec.bytes.length) = some 33)
    (hd : PublicKey.deserialize p.baseKey.serialize = .ok p.baseKey) :
    PendingRel o (some p) := by
  cases o with
  | none => cases hs
  | some tv =>
    have hbe : tv.vec.bytes = p.baseKey.serialize := Option.some.inj hb
    refine ⟨by rw [hbe]; exact hd, ?_, Option.some.inj ht3, Option.some.inj ht4,
      Option.some.inj hlen⟩
    unfold OptU32Rel
    rw [hp]
    exact Option.some.inj ht1

private theorem kyberRel_of_fields
    {o : Option CryptoVerification.LibsignalTripleRatchetRepr.TailVecGhost}
    {k : PendingKyberPreKey}
    (hs : o.isSome = true)
    (hb : o.map (fun g => g.vec.bytes) = some k.ciphertext)
    (ht : o.map (fun g => g.tail.take 4) = some (leBytes 4 k.preKeyId.toNat)) :
    KyberRel o (some k) := by
  cases o with
  | none => cases hs
  | some kv => exact ⟨Option.some.inj hb, Option.some.inj ht⟩

private theorem sessionModelRel_of_eqs {G : SessionGhost} {s : Session (List (BitVec 8))}
    {p : PendingPreKey} {k : PendingKyberPreKey}
    (hpp : s.pendingPreKey = some p)
    (hkp : s.pendingKyberPreKey = some k)
    (h1 : PendingRel G.pending (some p))
    (h2 : KyberRel G.kyber (some k))
    (h3 : G.alice.bytes = s.aliceBaseKey)
    (h4 : G.regIds.take 4 = leBytes 4 s.remoteRegistrationId.toNat)
    (h5 : (G.regIds.drop 4).take 4 = leBytes 4 s.localRegistrationId.toNat) :
    sessionModelRel G s := by
  unfold sessionModelRel
  rw [hpp, hkp]
  exact ⟨h1, h2, h3, h4, h5⟩

private theorem sendWitnessG'_modelRel :
    sessionModelRel sendWitnessG' sendWitnessSess' :=
  sessionModelRel_of_eqs
    sendWitnessSess'_pendingPreKey_eq
    sendWitnessSess'_pendingKyber_eq
    (pendingRel_of_none
      (by decide +kernel)
      (by decide +kernel)
      (by decide +kernel)
      (by decide +kernel)
      (by decide +kernel)
      (by decide +kernel)
      (by decide +kernel)
      sendWitnessSess'_shape_facts.2.2.2.2.2.2.2.1)
    (kyberRel_of_fields
      (by decide +kernel)
      (by decide +kernel)
      (by decide +kernel))
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)

private def MemHas (P : SepProp) : Prop :=
  ∃ m : Memory, m ⊨ P

private theorem memHas_init :
    MemHas (memRegion (ghostBase + BitVec.ofNat 64 0) 524288 ∗ emp) := by
  let m0 : Memory :=
    Memory.ofFn (fun _ => 0#8) (fun a => if (a - ghostBase).toNat < 524288 then some Perm.rw else none)
  have hrw : m0.RW ghostBase 524288 := by
    intro a ha
    unfold InRegion at ha
    rw [Memory.permNoLazy_eq_some_rw_iff]
    simp only [m0, Memory.perm_ofFn, Memory.isLazyFree_ofFn, ha, ↓reduceIte]
    exact ⟨rfl, rfl⟩
  refine ⟨m0, ?_⟩
  rw [BitVec.add_zero, sepConj_emp]
  exact ProofLib.satisfies_memRegion m0 ghostBase 524288 hrw

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

private theorem sendWitnessG'_sessionGhostValid :
    SessionGhostValid sendWitnessG' sendWitnessSess' := by
  refine ⟨sendWitnessG'_modelRel, A₀, ghostBase, ?_⟩
  have hf := sendWitnessSess'_shape_facts
  have hpq_bounds : 0 < sendWitnessSess'.state.pqRatchetState.length ∧
      sendWitnessSess'.state.pqRatchetState.length ≤ 286196 := by
    simpa [sendWitnessSess', OutgoingTripleRatchet.applyToSessionState] using sendWitnessOtr'_pqr_bounds
  let pqLen := sendWitnessSess'.state.pqRatchetState.length
  let pqCap := BitVec.ofNat 64 pqLen
  have h0 := memHas_init
  -- `0..24`: `localIk` header (`33`, `B+512`, `33`)
  have s1 := h0.step64 (off' := 8) (rem' := 524280) 33#64
  have s2 := s1.step64 (off' := 16) (rem' := 524272) (ghostBase + 512#64)
  have s3 := s2.step64 (off' := 24) (rem' := 524264) 33#64
  -- `24..48`: `remoteIk` header (`33`, `B+560`, `33`)
  have s4 := s3.step64 (off' := 32) (rem' := 524256) 33#64
  have s5 := s4.step64 (off' := 40) (rem' := 524248) (ghostBase + 560#64)
  have s6 := s5.step64 (off' := 48) (rem' := 524240) 33#64
  -- `48..72`: `rootKey` header (`32`, `B+608`, `32`)
  have s7 := s6.step64 (off' := 56) (rem' := 524232) 32#64
  have s8 := s7.step64 (off' := 64) (rem' := 524224) (ghostBase + 608#64)
  have s9 := s8.step64 (off' := 72) (rem' := 524216) 32#64
  -- `72..96`: `receiverChains` 1-element `Vec` (`1`, `B+352`, `1`)
  have s10 := s9.step64 (off' := 80) (rem' := 524208) 1#64
  have s11 := s10.step64 (off' := 88) (rem' := 524200) (ghostBase + 352#64)
  have s12 := s11.step64 (off' := 96) (rem' := 524192) 1#64
  -- `96..120`: `aliceBaseKey` header (`33`, `B+656`, `33`)
  have s13 := s12.step64 (off' := 104) (rem' := 524184) 33#64
  have s14 := s13.step64 (off' := 112) (rem' := 524176) (ghostBase + 656#64)
  have s15 := s14.step64 (off' := 120) (rem' := 524168) 33#64
  -- `120..144`: `pqRatchetState` header (`pqCap`, `B+4096`, `pqCap`)
  have s16 := s15.step64 (off' := 128) (rem' := 524160) pqCap
  have s17 := s16.step64 (off' := 136) (rem' := 524152) (ghostBase + 4096#64)
  have s18 := s17.step64 (off' := 144) (rem' := 524144) pqCap
  -- `144..168`: `sender.srk` header (`33`, `B+704`, `33`)
  have s19 := s18.step64 (off' := 152) (rem' := 524136) 33#64
  have s20 := s19.step64 (off' := 160) (rem' := 524128) (ghostBase + 704#64)
  have s21 := s20.step64 (off' := 168) (rem' := 524120) 33#64
  -- `168..192`: `sender.priv` header (`32`, `B+752`, `32`)
  have s22 := s21.step64 (off' := 176) (rem' := 524112) 32#64
  have s23 := s22.step64 (off' := 184) (rem' := 524104) (ghostBase + 752#64)
  have s24 := s23.step64 (off' := 192) (rem' := 524096) 32#64
  -- `192..216`: `sender.message_keys` empty `Vec` (`0`, `8`, `0`)
  have s25 := s24.step64 (off' := 200) (rem' := 524088) 0#64
  have s26 := s25.step64 (off' := 208) (rem' := 524080) 8#64
  have s27 := s26.step64 (off' := 216) (rem' := 524072) 0#64
  -- `216..248`: `sender.ck` (`32`, `B+800`, `32`, `index`, `4` B pad)
  have s28 := s27.step64 (off' := 224) (rem' := 524064) 32#64
  have s29 := s28.step64 (off' := 232) (rem' := 524056) (ghostBase + 800#64)
  have s30 := s29.step64 (off' := 240) (rem' := 524048) 32#64
  have s31 := s30.step32 (off' := 244) (rem' := 524044) sendWitnessSc'.chainKey.index
  have s32 := s31.stepSkip (off' := 248) (rem' := 524040) 4
  -- `248..296`: `pending` (`33`, `B+848`, `33`, `24` B tail)
  have s33 := s32.step64 (off' := 256) (rem' := 524032) 33#64
  have s34 := s33.step64 (off' := 264) (rem' := 524024) (ghostBase + 848#64)
  have s35 := s34.step64 (off' := 272) (rem' := 524016) 33#64
  have s36 := s35.stepBytes (off' := 296) (rem' := 523992) 24 sendWitnessPendTail (by decide +kernel)
  -- `296..328`: `kyber` (`1569`, `B+1024`, `1569`, `8` B tail)
  have s37 := s36.step64 (off' := 304) (rem' := 523984) 1569#64
  have s38 := s37.step64 (off' := 312) (rem' := 523976) (ghostBase + 1024#64)
  have s39 := s38.step64 (off' := 320) (rem' := 523968) 1569#64
  have s40 := s39.stepBytes (off' := 328) (rem' := 523960) 8 sendWitnessKyberTail (by decide +kernel)
  -- `328..344`: `sessionVersion`, `previousCounter`, `regIds`
  have s41 := s40.step32 (off' := 332) (rem' := 523956) sendWitnessSess'.state.sessionVersion
  have s42 := s41.step32 (off' := 336) (rem' := 523952) sendWitnessSess'.state.previousCounter
  have s43 := s42.stepBytes (off' := 344) (rem' := 523944) 8 sendWitnessG'.regIds (by decide +kernel)
  -- `344..352` skipped (`8` B), then `352..456`: `rc0` `Chain` element (`104` B)
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
  have rc13 := rc12.step32 (off' := 452) (rem' := 523836) sendWitnessRc0Ck.index
  have rc14 := rc13.stepSkip (off' := 456) (rem' := 523832) 4
  -- Heap buffers (`456..512` skipped, then `localIk`, `remoteIk`, `rootKey`, `alice`, `srk`, `priv`, `ck`, `pending`, `rc0.srk`, `rc0.ck`, `kyber`, `pq`)
  have h1 := rc14.stepSkip (off' := 512) (rem' := 523776) 56
  have h2 := h1.stepBytes (off' := 545) (rem' := 523743) 33
    sendWitnessSess'.state.localIdentity.publicKey.serialize (by decide +kernel)
  have h3 := h2.stepSkip (off' := 560) (rem' := 523728) 15
  have h4 := h3.stepBytes (off' := 593) (rem' := 523695) 33
    sendWitnessRemIk'.publicKey.serialize (by decide +kernel)
  have h5 := h4.stepSkip (off' := 608) (rem' := 523680) 15
  have h6 := h5.stepBytes (off' := 640) (rem' := 523648) 32
    (keyToBytes32 sendWitnessSess'.state.rootKey) (by simp [keyToBytes32])
  have h7 := h6.stepSkip (off' := 656) (rem' := 523632) 16
  have h8 := h7.stepBytes (off' := 689) (rem' := 523599) 33
    sendWitnessSess'.aliceBaseKey hf.2.2.1
  have h9 := h8.stepSkip (off' := 704) (rem' := 523584) 15
  have h10 := h9.stepBytes (off' := 737) (rem' := 523551) 33
    sendWitnessSc'.ratchetKey.publicKey.serialize (by decide +kernel)
  have h11 := h10.stepSkip (off' := 752) (rem' := 523536) 15
  have h12 := h11.stepBytes (off' := 784) (rem' := 523504) 32
    sendWitnessSc'.ratchetKey.privateKey.bytes.toList
    sendWitnessSc'.ratchetKey.privateKey.bytes.toList_length
  have h13 := h12.stepSkip (off' := 800) (rem' := 523488) 16
  have h14 := h13.stepBytes (off' := 832) (rem' := 523456) 32
    (keyToBytes32 sendWitnessSc'.chainKey.key) (by simp [keyToBytes32])
  have h15 := h14.stepSkip (off' := 848) (rem' := 523440) 16
  have h16 := h15.stepBytes (off' := 881) (rem' := 523407) 33
    sendWitnessPpk.baseKey.serialize (by decide +kernel)
  have h16a := h16.stepSkip (off' := 896) (rem' := 523392) 15
  have h16b := h16a.stepBytes (off' := 929) (rem' := 523359) 33
    sendWitnessRc0.senderRatchetKey.serialize (by decide +kernel)
  have h16c := h16b.stepSkip (off' := 944) (rem' := 523344) 15
  have h16d := h16c.stepBytes (off' := 976) (rem' := 523312) 32
    (keyToBytes32 sendWitnessRc0Ck.key) (by simp [keyToBytes32])
  have h17 := h16d.stepSkip (off' := 1024) (rem' := 523264) 48
  have h18 := h17.stepBytes (off' := 2593) (rem' := 521695) 1569
    sendWitnessKpk.ciphertext sendWitnessKpk_ct_len
  have h19 := h18.stepSkip (off' := 4096) (rem' := 520192) 1503
  have hc_pq : decide (4096 + pqLen = 4096 + pqLen ∧
      pqLen + (520192 - pqLen) = 520192 ∧ 520192 ≤ 2 ^ 64) = true :=
    decide_eq_true ⟨rfl, by have := hpq_bounds.2; omega, by decide⟩
  have h20 := h19.stepBytes (off' := 4096 + pqLen) (rem' := 520192 - pqLen) pqLen
    sendWitnessSess'.state.pqRatchetState rfl hc_pq
  rcases h20 with ⟨m, hsat⟩
  have hpure_ss :
      (PublicKey.deserialize sendWitnessG'.localIk.bytes =
          .ok sendWitnessSess'.state.localIdentity.publicKey ∧
        PublicKey.deserialize sendWitnessG'.remoteIk.bytes =
          .ok sendWitnessRemIk'.publicKey ∧
        sendWitnessG'.chains.length = sendWitnessSess'.state.receiverChains.length ∧
        sendWitnessG'.pending.isSome = sendWitnessSess'.state.pendingPreKey ∧
        sendWitnessG'.regIds.length = 8 ∧
        sendWitnessG'.localIk.bytes.length = 33 ∧
        ((some sendWitnessRemIk' : Option IdentityKey).isSome = true →
          sendWitnessG'.remoteIk.bytes.length = 33)) ↔
      True := by
    rw [sendWitnessSess'_receiverChains_eq, hf.2.1]
    exact iff_true_intro ⟨hf.2.2.2.1, hf.2.2.2.2.1, by decide +kernel, by decide +kernel,
      by decide +kernel, by decide +kernel, fun _ => by decide +kernel⟩
  have hpure_rc :
      (PublicKey.deserialize sendWitnessRc0Ghost.srk.bytes = .ok sendWitnessRc0.senderRatchetKey ∧
        sendWitnessRc0.messageKeys.length ≤ maxMessageKeys ∧
        sendWitnessRc0Ghost.keys.length = sendWitnessRc0.messageKeys.length ∧
        sendWitnessRc0Ghost.srk.bytes.length = 33 ∧
        sendWitnessRc0Ghost.priv.bytes = []) ↔ True := by
    rw [hf.1]
    exact iff_true_intro ⟨hf.2.2.2.2.2.2.2.2, Nat.zero_le _, rfl, by decide +kernel, rfl⟩
  have hloc_v := vecU8At_A0_exact ghostBase (ghostBase + 512#64) 33
    sendWitnessSess'.state.localIdentity.publicKey.serialize
    (by decide +kernel) (by decide) (by decide) (by decide)
  have hrem_v := vecU8At_A0_exact (ghostBase + 24#64) (ghostBase + 560#64) 33
    sendWitnessRemIk'.publicKey.serialize
    (by decide +kernel) (by decide) (by decide) (by decide)
  have hroot_v := vecU8At_A0_exact (ghostBase + 48#64) (ghostBase + 608#64) 32
    (keyToBytes32 sendWitnessSess'.state.rootKey)
    (by simp [keyToBytes32]) (by decide) (by decide) (by decide)
  have hrc_v := vecAt_A0_singleton (chainAt A₀) (ghostBase + 72#64) (ghostBase + 352#64)
    (sendWitnessRc0Ghost, sendWitnessRc0) (by decide)
  have hrc_srk_v := vecU8At_A0_exact (ghostBase + 352#64) (ghostBase + 896#64) 33
    sendWitnessRc0.senderRatchetKey.serialize
    (by decide +kernel) (by decide) (by decide) (by decide)
  have hrc_priv_v := vecU8At_A0_empty (ghostBase + 376#64)
  have hrc_mk_v := vecAt_A0_empty (messageKeyAt A₀) (ghostBase + 400#64)
  have hrc_ck_v := vecU8At_A0_exact (ghostBase + 424#64) (ghostBase + 944#64) 32
    (keyToBytes32 sendWitnessRc0Ck.key)
    (by simp [keyToBytes32]) (by decide) (by decide) (by decide)
  have halice_v := vecU8At_A0_exact (ghostBase + 96#64) (ghostBase + 656#64) 33
    sendWitnessSess'.aliceBaseKey
    hf.2.2.1 (by decide) (by decide) (by decide)
  have hpq_v := vecU8At_A0_exact (ghostBase + 120#64) (ghostBase + 4096#64) pqLen
    sendWitnessSess'.state.pqRatchetState
    rfl hpq_bounds.1 (by have := hpq_bounds.2; omega) (by decide)
  have hsrk_v := vecU8At_A0_exact (ghostBase + 144#64) (ghostBase + 704#64) 33
    sendWitnessSc'.ratchetKey.publicKey.serialize
    (by decide +kernel) (by decide) (by decide) (by decide)
  have hpriv_v := vecU8At_A0_exact (ghostBase + 168#64) (ghostBase + 752#64) 32
    sendWitnessSc'.ratchetKey.privateKey.bytes.toList
    sendWitnessSc'.ratchetKey.privateKey.bytes.toList_length (by decide) (by decide) (by decide)
  have hsmk_v := vecAt_A0_empty (messageKeyAt A₀) (ghostBase + 192#64)
  have hsck_v := vecU8At_A0_exact (ghostBase + 216#64) (ghostBase + 800#64) 32
    (keyToBytes32 sendWitnessSc'.chainKey.key)
    (by simp [keyToBytes32]) (by decide) (by decide) (by decide)
  have hpend_v := vecU8At_A0_exact (ghostBase + 248#64) (ghostBase + 848#64) 33
    sendWitnessPpk.baseKey.serialize
    (by decide +kernel) (by decide) (by decide) (by decide)
  have hkyb_v := vecU8At_A0_exact (ghostBase + 296#64) (ghostBase + 1024#64) 1569
    sendWitnessKpk.ciphertext
    sendWitnessKpk_ct_len (by decide) (by decide) (by decide)
  have hpure_sc :
      (PublicKey.deserialize sendWitnessSc'.ratchetKey.publicKey.serialize =
          .ok sendWitnessSc'.ratchetKey.publicKey ∧
        True ∧
        clampScalar sendWitnessSc'.ratchetKey.privateKey.bytes =
          sendWitnessSc'.ratchetKey.privateKey.bytes ∧
        sendWitnessSc'.ratchetKey.publicKey.serialize.length = 33) ↔ True :=
    iff_true_intro ⟨hf.2.2.2.2.2.1, trivial, hf.2.2.2.2.2.2.1, by decide +kernel⟩
  have hpure_pt : (sendWitnessPendTail.length = 48 - 24) ↔ True :=
    iff_true_intro (by decide +kernel)
  have hpure_kt : (sendWitnessKyberTail.length = 32 - 24) ↔ True :=
    iff_true_intro (by decide +kernel)
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
  rw [sendWitnessSess'_remoteIdentity_eq]
  dsimp only
  rw [propext hpure_ss, pure_true, emp_sepConj]
  dsimp only [sendWitnessG', vecGhostAt]
  rw [sendWitnessSess'_receiverChains_eq, sendWitnessSess'_senderChain_eq]
  simp only [List.zip_cons_cons, List.zip_nil_right, optSenderChainAt, optChainKeyAt, optTailVecAt,
    BitVec.add_assoc, BitVec.reduceAdd]
  rw [propext hpure_sc, propext hpure_pt, propext hpure_kt, pure_true, emp_sepConj, emp_sepConj,
    emp_sepConj]
  rw [hrc_v]
  unfold chainAt
  rw [propext hpure_rc, pure_true, emp_sepConj]
  dsimp only [sendWitnessRc0Ghost, vecGhostAt]
  rw [hf.1, sendWitnessRc0_chainKey_eq]
  simp only [List.zip_nil_right, optChainKeyAt, BitVec.add_assoc, BitVec.reduceAdd]
  have hreg_eq :
      leBytes 4 sendWitnessSess'.remoteRegistrationId.toNat ++
        leBytes 4 sendWitnessSess'.localRegistrationId.toNat =
      sendWitnessG'.regIds := rfl
  rw [hreg_eq, hloc_v, hrem_v, hroot_v, hrc_srk_v, hrc_priv_v, hrc_mk_v, hrc_ck_v,
    halice_v, hpq_v, hsrk_v, hpriv_v, hsmk_v, hsck_v, hpend_v, hkyb_v]
  simp only [BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp] at hsat ⊢
  refine Eq.mp (congrArg (fun P => m ⊨ P) ?_) hsat
  dsimp only [Rframe, pqCap, pqLen]
  sep_ac_rfl

private def sendWitnessSmGhost : SignalMessageNewGhost where
  messageVersion := 4#8
  macKeyA := 0#64
  macKey := 0#256
  locA := 0#64
  loc := none
  remA := 0#64
  rem := sendWitnessW1Params.peer
  senderRatchetKeyA := 0#64
  senderRatchetKey := pk0
  counter := 0#32
  previousCounter := 0#32
  ciphertextA := 0#64
  ciphertext := []
  senderIkA := 0#64
  senderIk := ⟨pk0⟩
  receiverIkA := 0#64
  receiverIk := ⟨pk0⟩
  pqRatchetA := 0#64
  pqRatchet := []
  ret := 0#64

private def sendWitnessSmModel : SignalMessage :=
  SignalMessage.new W0.C.F protoSignalCodec 4#8 0#256 none pk0 0#32 0#32 [] ⟨pk0⟩ ⟨pk0⟩ []

private def sendWitnessPkCall : PreKeyMsgNewCall where
  ret := 0#64
  ver := 4#8
  regId := 0#32
  preKeyId := sendWitnessPpk.preKeyId
  spk := sendWitnessPpk.signedPreKeyId
  kyA := 0#64
  kyPtr := 0#64
  kp := some ⟨sendWitnessKpk.preKeyId, sendWitnessKpk.ciphertext.tail⟩
  bkA := 0#64
  baseKey := sendWitnessPpk.baseKey
  ikA := 0#64
  ik := sendWitnessSess0.state.localIdentity
  msgA := 0#64
  msgG := ⟨0#64, 0#64, 0#64, 0#64, 0#64⟩
  msg := sendWitnessSmModel

private theorem sendWitness_wire_caps :
    sendWitnessSmGhost.ciphertext.length ≤ w1CtLenCap ∧
    sendWitnessSmGhost.pqRatchet.length ≤ 4096 ∧
    signalMessageNewSerLen uuidTryParse sendWitnessSmGhost ≤ w1SmSerCap ∧
    kyberPayloadLen sendWitnessPkCall.kp ≤ 1569 ∧
    sendWitnessPkCall.msg.serialized.length ≤ w1SmSerCap ∧
    sendWitnessPkCall.model.serialized.length ≤ w1PkOutCap := by
  decide +kernel

/-- Existential-kit `.send` success-path non-vacuity witness on
`RealCliMainEnvOf (mkExistentialRealCalleeEnvs img S P₀) i₀` at `P₀ = NonVacuityPq.W0`. -/
theorem realCliMainEnvOf_concrete_send_succ_nonvacuous [LibsignalPlacement]
    (img : Arm64.Obj.Image) (S : RunSem) :
    ∃ (P₀ : PEParams) (i₀ : Inputs) (evs : List AllocEvent),
      CliPqxdhInputs P₀ i₀ ∧
      (∃ peer, parseArgs uuidTryParse (i₀.argv.map bytesOfString) = some (.send peer)) ∧
      SendSuccMainEnv img P₀ i₀ evs ∧
      RealCliMainEnvOf (mkExistentialRealCalleeEnvs img S P₀) i₀ evs ∧
      AllocEvent.alloc 1568 ∈ evs ∧
      AllocEvent.alloc 16 ∈ evs ∧
      AllocEvent.alloc 1024 ∈ evs := by
  let R := sendWitnessW1Params
  let i₀ := sendWitnessInputs
  have hScopeIn : scopeIn sendWitnessR0 :=
    ratchetScopeCoversPq_scopeIn_placed W0 sendWitnessP0 sendWitnessX0 sendWitnessG0
      sendWitnessP0_props.2 sendWitnessP0_session_eq
  have hScopeR0 : DeserializeScopeP_Q NonEmptyV1Q sendWitnessR0 :=
    scopeKit_of_scopeIn hScopeIn
  have hKitR0 : scopeKit sendWitnessR0 := hScopeR0
  have hSessCap : (pqSessBytes sendWitnessP0).length ≤ fileCapBytes :=
    pqSessBytes_le_fileCapBytes sendWitnessP0_props.2
  have hSessGet :
      StoresGhost.opened.sessions.get cliIo.rd (runFiles i₀) (addressText R.x.rem.val) =
        .ok (encodeRecord sendWitnessR0) := by
    rw [sendWitnessR0_encode_eq]
    have h := pqSessGet_send W0 sendWitnessP0 [] sendWitnessCoins hSessCap
    rwa [sendWitnessP0_party] at h
  have hScAt :
      (w1SessKit R.B img (runFiles i₀) R.peer).ScopeAt scopeKit StoresGhost.opened.sessions
        R.x.rem.val sendWitnessR0 := by
    cases henc_eq : encodeRecord sendWitnessR0 with
    | nil => exact absurd henc_eq sendWitnessR0_encode_ne_nil
    | cons bhd btl =>
      exact ⟨hKitR0, bhd :: btl, henc_eq ▸ hSessGet, sendWitnessR0, rfl, henc_eq, hKitR0⟩
  have hPeerGet :
      StoresGhost.opened.identity.peers.get cliIo.rd (runFiles i₀) R.x.rem.val.name =
        .ok (pqIdBytes sendWitnessP0) := by
    have h := pqIdGet_send W0 sendWitnessP0 [] sendWitnessCoins
    rwa [sendWitnessP0_party] at h
  let addrCap := (addressText R.peer.val).length
  let evsAddr : List AllocEvent := rustAllocEvents addrCap 1 ++ rustDeallocEvents addrCap 1
  have hAddrCapLe : addrCap ≤ 4 * R.peer.name.bytes.length + 32 := by
    have hle := addressText_length_le R.peer.val
    dsimp only [addrCap, R, sendWitnessW1Params, nonVacSendAddrGhost,
      AddrGhost.val, VecGhost.bytes, addrValOf] at hle ⊢
    omega
  have hAddrSucc : CliAddrTextSuccEnv R.peer evsAddr :=
    ⟨addrCap, Nat.le_refl _, hAddrCapLe, rfl⟩
  let evsPathL := mkCliPathSimple StoresGhost.opened.sessions.path (addressText R.x.rem.val)
  let evsTrPath := mkCliPathSimple StoresGhost.opened.identity.peers.path R.x.rem.val.name
  let evsSpqr := rustAllocEvents sendWitnessOtr'.pqrState.length 1
  let encLen' := (lenField 1 (encSessionMem sendWitnessG' sendWitnessSess')).length
  let evsSer := serializeSomeExactEvents sendWitnessG' sendWitnessSess'
  have hSer : SerializeSomeCancelEnv sendWitnessG' sendWitnessSess' evsSer :=
    ⟨segCloneEvents sendWitnessG' sendWitnessSess'.state ++ rustAllocEvents encLen' 1,
      dropClonedSessionEvents sendWitnessG' sendWitnessSess'.state, rfl,
      ⟨segCloneEvents sendWitnessG' sendWitnessSess'.state,
        rustAllocEvents encLen' 1, rfl, rfl, rfl⟩, rfl⟩
  let evsEnc : List AllocEvent :=
    (rustAllocEvents 24 8 ++
      ((evsAddr ++ ((evsPathL ++ allocBytes1Events (encodeRecord sendWitnessR0)) ++
          sessDeserEvents sendWitnessR0)) ++
        rustDeallocEvents 24 8)) ++
    (rustAllocEvents sendWitnessKpk.ciphertext.length 1 ++
      ((evsSpqr ++ (rustAllocEvents 32 1 ++
          (rustAllocEvents ((R.x.ptext.length / 16 + 1) * 16) 1 ++
            signalMessageNewEvents uuidTryParse sendWitnessSmGhost))) ++
        (preKeyMsgNewEvents sendWitnessPkCall ++
          ((rustAllocEvents 32 8 ++
              ((evsTrPath ++ allocBytes1Events (pqIdBytes sendWitnessP0)) ++
                rustDeallocEvents 32 8)) ++
            ((rustAllocEvents 32 8 ++
                (((evsTrPath ++ allocBytes1Events (pqIdBytes sendWitnessP0)) ++
                  (allocBytes1Events R.x.rem.val.name ++ [])) ++
                  rustDeallocEvents 32 8)) ++
              (rustAllocEvents 32 1 ++
                (rustAllocEvents 32 8 ++
                  ((evsAddr ++ (evsSer ++ [])) ++ rustDeallocEvents 32 8))))))))
  have hw_caps := sendWitness_wire_caps
  have hW1Succ : W1SendSuccSlotEnv img W0 i₀ R evsEnc :=
    ⟨sendWitnessR0, sendWitnessSess0, sendWitnessOtr0, sendWitnessTaken0,
      sendWitnessK0, sendWitnessKpk, pqIdBytes sendWitnessP0,
      sendWitnessSmGhost, sendWitnessPkCall, sendWitnessG', sendWitnessSess',
      evsAddr, evsPathL, evsSpqr, evsTrPath, evsTrPath, [],
      evsAddr, evsSer, [],
      hScAt, hScopeR0, hSessGet, sendWitnessR0_encode_ne_nil,
      sendWitnessR0_currentSession, sendWitnessSess0_fromSessionState_eq,
      sendWitnessTaken0_remoteIdentity_eq, sendWitnessSess0_pendingPreKey_isSome,
      sendWitnessSess0_pendingKyber_eq,
      by rw [sendWitnessKpk_ct_len]; decide,
      hAddrSucc,
      mkCliPathSimple_mem _ _,
      spqrSendSuccTightEnv_of_bounds sendWitnessOtr'_pqr_bounds.1 sendWitnessOtr'_pqr_bounds.2,
      hw_caps.1, hw_caps.2.1, hw_caps.2.2.1, hw_caps.2.2.2.1, hw_caps.2.2.2.2.1, hw_caps.2.2.2.2.2,
      hPeerGet,
      mkCliPathSimple_mem _ _,
      mkCliPathSimple_mem _ _,
      Or.inl FreeOnlyEvs.nil,
      sendWitnessR'_currentSession,
      sendWitnessG'_sessionGhostValid,
      sendWitnessR'_encode_le,
      hAddrSucc,
      hSer,
      Or.inl FreeOnlyEvs.nil,
      rfl⟩
  have htail_len : sendWitnessKpk.ciphertext.tail.length = 1568 := by decide +kernel
  have htail_ne : sendWitnessKpk.ciphertext.tail ≠ [] := by
    intro h; rw [h] at htail_len; cases htail_len
  have h1568_pk : AllocEvent.alloc 1568 ∈ preKeyMsgNewEvents sendWitnessPkCall := by
    unfold preKeyMsgNewEvents preKeyMsgNewRawEvents preKeyMsgNewRawPrologueEvents
      sendWitnessPkCall kyberCopyEvs
    dsimp only
    simp only [htail_ne, ↓reduceIte, htail_len, List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (by decide))))))
  have h1568_enc : AllocEvent.alloc 1568 ∈ evsEnc := by
    apply List.mem_append_right
    apply List.mem_append_right
    apply List.mem_append_right
    apply List.mem_append_left
    exact h1568_pk
  have hlen16 : (R.x.ptext.length / 16 + 1) * 16 = 16 := by decide
  have h16_pt : AllocEvent.alloc 16 ∈ rustAllocEvents ((R.x.ptext.length / 16 + 1) * 16) 1 := by
    rw [hlen16]
    decide
  have h16_enc : AllocEvent.alloc 16 ∈ evsEnc :=
    List.mem_append_right _
      (List.mem_append_right _
        (List.mem_append_left _
          (List.mem_append_right _
            (List.mem_append_right _
              (List.mem_append_left _ h16_pt)))))
  have hArgvLen : i₀.argv.length = 2 := rfl
  have hM2 : IterConcatEnv M2CollectStepEnv (List.range i₀.argv.length) [] := by
    rw [hArgvLen]
    exact ⟨[], [], rfl, Or.inl rfl, ⟨[], [], rfl, Or.inl rfl, rfl⟩⟩
  let evsR0Path := mkCliPathSimple StoresGhost.opened.identity.own.path (utf8 "address")
  let evsP1 := mkM5EntrySimple StoresGhost.opened.identity.peers.path R.x.rem.val.name
  let evsS1 := mkM5EntrySimple StoresGhost.opened.sessions.path (addressText R.peer.val)
  let evsM5 := evsP1 ++ evsS1
  have hM5 :
      IterConcatEnv (fun dn => IterConcatEnv (fun name => M5LoopAEntryEnv dn.1 name) dn.2)
        [(StoresGhost.opened.identity.peers.path, [R.x.rem.val.name]),
         (StoresGhost.opened.sessions.path, [addressText R.peer.val])] evsM5 :=
    ⟨evsP1, evsS1, rfl,
      ⟨evsP1, [], (List.append_nil _).symm, mkM5EntrySimple_mem _ _, rfl⟩,
      ⟨evsS1, [], (List.append_nil _).symm,
        ⟨evsS1, [], (List.append_nil _).symm, mkM5EntrySimple_mem _ _, rfl⟩,
        rfl⟩⟩
  let ownB := CryptoVerification.SignalSession.textBytes (partyAddress .A).text
  let fullLog : List AllocEvent :=
    (rustAllocEvents (16 * i₀.argv.length) 8 ++
      ([] ++ (addressEvents uuidTryParse sendWitnessAddressCall.bs ++
        (allocBytes1Events i₀.stdin ++ allocBytes1Events sendWitnessCoins.toList)))) ++
    (((evsR0Path ++ ((allocBytes1Events ownB ++ addressEvents uuidTryParse ownB) ++
          deallocBytes1OfLen ownB.length)) ++
        (evsEnc ++ cliConcat2Events [wirePrekey] sendWitnessBs1)) ++
      (evsM5 ++ rustAllocEvents 1024 1))
  have hSendSucc : SendSuccMainEnv img W0 i₀ fullLog :=
    ⟨sendWitnessP0, [], sendWitnessCoins, sendWitnessSt1,
      sendWitnessX0, sendWitnessX1, sendWitnessG0, sendWitnessG1,
      sendWitnessAddressCall, nonVacSendPeer, R,
      sendWitnessCoins.toList, ownB, sendWitnessBs1,
      [], evsR0Path, evsEnc, evsM5,
      sendWitnessP0_props.2,
      sendWitnessP0_session_eq,
      rfl,
      sendWitness_pqSendModel_eq,
      sendWitnessSt1_session_eq,
      sendWitnessSt1_wf,
      sendWitnessInputs_argv_map,
      sendWitnessAddressCall_parse,
      sendWitnessInputs_parseArgs,
      sendWitnessW1Params_dom,
      rfl,
      rfl,
      rfl,
      sendWitnessOwn_parse,
      rfl,
      Nat.zero_le msgCapBytes,
      sendWitnessCoins_readFileResult,
      hM2,
      sendWitnessOwn_get,
      mkCliPathSimple_mem _ _,
      hW1Succ,
      sendWitnessBs1_bounds.1,
      sendWitnessBs1_bounds.2,
      hM5,
      h1568_enc,
      h16_enc,
      rfl⟩
  have h1568_full : AllocEvent.alloc 1568 ∈ fullLog :=
    List.mem_append_right _
      (List.mem_append_left _
        (List.mem_append_right _
          (List.mem_append_left _ h1568_enc)))
  have h16_full : AllocEvent.alloc 16 ∈ fullLog :=
    List.mem_append_right _
      (List.mem_append_left _
        (List.mem_append_right _
          (List.mem_append_left _ h16_enc)))
  have h1024_full : AllocEvent.alloc 1024 ∈ fullLog := by
    apply List.mem_append_right
    apply List.mem_append_right
    apply List.mem_append_right
    change AllocEvent.alloc 1024 ∈ rustAllocEvents 1024 1
    decide
  exact ⟨W0, i₀, fullLog,
    sendWitnessInputs_cliPqxdh,
    ⟨nonVacSendPeer, sendWitnessInputs_parseArgs⟩,
    hSendSucc,
    sendSuccMainEnv_sub_realCliMainEnvOf img S W0 i₀ fullLog hSendSucc,
    h1568_full,
    h16_full,
    h1024_full⟩

/-! ## 5. Binary-Kit Success Sub-Envelopes, Inclusion, and Non-Vacuity Theorems -/

section BinaryKitStageB

open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.SignalSession.Cli (DirGhost)

/-- Exact binary `address_text` (Block `594`) success sub-envelope chaining `to_owned`, `"."`
reserve, `DecimalEnv`, decimal-append reserve, and temporary `decimal` `Vec<u8>` deallocation. -/
def AddrTextBinarySuccEnv (rem : AddrVal) (evs : List AllocEvent) : Prop :=
  0 < rem.name.length ∧
  ConcatEnv (· = rustAllocEvents rem.name.length 1)
    (ConcatEnv (· = addrDotReserveEvents rem.name)
      (ConcatEnv (· = decimalEvents (rem.device.zeroExtend 32))
        (ConcatEnv (· = addrDecReserveEvents rem.name rem.device)
          (· = rustDeallocEvents (decimalCap (rem.device.zeroExtend 32)).toNat 1))))
    evs

private theorem addrTextValEnv_of_succ {rem : AddrVal} {evs : List AllocEvent}
    (h : AddrTextBinarySuccEnv rem evs) :
    AddrTextValEnv DecimalEnv rem evs := by
  obtain ⟨hpos, e1, r1, rfl, rfl, e2, r2, rfl, rfl, e3, r3, rfl, rfl, e4, e5, rfl, rfl, rfl⟩ := h
  have hne : rem.name.length ≠ 0 := Nat.ne_of_gt hpos
  have hto : addrToOwnedEvents rem.name = rustAllocEvents rem.name.length 1 := by
    unfold addrToOwnedEvents
    simp only [hne, ↓reduceIte]
  exact Or.inr ⟨_, _, rfl, hto.symm,
    Or.inr ⟨_, _, rfl, rfl,
      Or.inr ⟨_, _, rfl, rfl,
        Or.inr ⟨_, _, rfl, rfl,
          FreeOnlyEvs.singleton 1 (decimalCap (rem.device.zeroExtend 32)).toNat⟩⟩⟩⟩

/-- Exact Block `594` (`address_text`) trace on `addrValOf nonVacSendPeer`
(`36`-B UUID, `device = 1#8`). -/
theorem addrTextBinarySuccEnv_nonVacSendPeer :
    AddrTextBinarySuccEnv (addrValOf nonVacSendPeer)
      [AllocEvent.alloc 36, AllocEvent.realloc 1 36 72,
       AllocEvent.alloc 8, AllocEvent.free 1 8] := by
  have hname : (addrValOf nonVacSendPeer).name = succKutf8 (partyAddressName .B) :=
    succ_utf8_eq_kutf8 (partyAddressName .B)
  have hdev : (addrValOf nonVacSendPeer).device = 1#8 := rfl
  have hd1 :
      CryptoVerification.SignalSession.Cli.decimalText ((1#8 : BitVec 8).zeroExtend 32).toNat =
        [0x31#8] := by
    have hz : ((1#8 : BitVec 8).zeroExtend 32).toNat = 1 := by decide
    rw [hz]
    exact CryptoVerification.SignalSession.Cli.Decimal.Helpers.decimalText_digit 1 (by decide)
  refine ⟨by rw [hname]; decide,
    rustAllocEvents (addrValOf nonVacSendPeer).name.length 1,
    addrDotReserveEvents (addrValOf nonVacSendPeer).name ++
      (decimalEvents ((addrValOf nonVacSendPeer).device.zeroExtend 32) ++
        (addrDecReserveEvents (addrValOf nonVacSendPeer).name (addrValOf nonVacSendPeer).device ++
          rustDeallocEvents (decimalCap ((addrValOf nonVacSendPeer).device.zeroExtend 32)).toNat 1)),
    ?_, rfl,
    addrDotReserveEvents (addrValOf nonVacSendPeer).name, _, rfl, rfl,
    decimalEvents ((addrValOf nonVacSendPeer).device.zeroExtend 32), _, rfl, rfl,
    addrDecReserveEvents (addrValOf nonVacSendPeer).name (addrValOf nonVacSendPeer).device,
    rustDeallocEvents (decimalCap ((addrValOf nonVacSendPeer).device.zeroExtend 32)).toNat 1,
    rfl, rfl, rfl⟩
  dsimp only [decimalEvents, decimalCap, addrDecReserveEvents]
  rw [hname, hdev, hd1]
  decide

/-- Cache-miss `.ok bs` binary `Dir::get` (Block `589`) sub-envelope chaining `DirGetPathEnv`,
`allocBytes1Events bs`, and `(· = [])` error/free seams (`d.changed = []`, `0 × alloc 22`). -/
def DirGetMissOkBinarySuccEnv (F0 : FsFiles) (d : DirGhost)
    (name bs : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  d.changed.find? (fun e => e.1 == name) = none ∧
  cliIo.rd F0 (pathOf d.path name) = .ok bs ∧
  ConcatEnv (DirGetPathEnv PathEnv d.path name)
    (ConcatEnv (· = allocBytes1Events bs)
      (ConcatEnv (· = ([] : List AllocEvent))
        (· = ([] : List AllocEvent))))
    evs

private theorem dirGetEnv_of_missOk_succ' {F0 : FsFiles} {d : DirGhost}
    {name bs : List (BitVec 8)} {evs : List AllocEvent}
    (h : DirGetMissOkBinarySuccEnv F0 d name bs evs) :
    DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd F0 d name evs := by
  obtain ⟨hfind, hrd, ePath, r1, rfl, hPath, eRd, r2, rfl, rfl,
    eErr, eFree, rfl, rfl, rfl⟩ := h
  unfold DirGetEnv
  rw [hfind]
  refine Or.inr ⟨ePath, _, rfl, hPath, Or.inr ⟨allocBytes1Events bs, [] ++ [], rfl, ?_, ?_⟩⟩
  · unfold ReadFileRuleEnv
    rw [hrd]
    exact Or.inl rfl
  · exact Or.inr ⟨[], [], rfl, by unfold DirGetErrAllocEnv; rw [hrd], FreeOnlyEvs.nil⟩

/-- Binary-exact (`0` `SeqEnv`) cache-miss `grow_one` `Dir::put::<String>` sub-envelope. -/
def DirPutMissGrowBinarySuccEnv (d : DirGhost)
    (name _bytes : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  (∀ e ∈ d.changed, e.1 ≠ name) ∧
  evs = rawVecGrowEvents 48 4 8 (BitVec.ofNat 64 d.changed.length)

private theorem dirPutEnv_of_missGrow_succ {d : DirGhost} {name bytes : List (BitVec 8)}
    {evs : List AllocEvent}
    (h : DirPutMissGrowBinarySuccEnv d name bytes evs) :
    DirPutEnv d name bytes evs := by
  rcases h with ⟨hmiss, rfl⟩
  exact dirPutTailEnv_miss_grow hmiss

/-- Binary-exact (`0` `SeqEnv`) non-empty cache-miss `grow_one` `Dir::put::<&str>` sub-envelope. -/
def DirPutStrMissGrowBinarySuccEnv (d : DirGhost)
    (name _bytes : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  name ≠ [] ∧
  (∀ e ∈ d.changed, e.1 ≠ name) ∧
  ConcatEnv (· = rustAllocEvents name.length 1)
    (· = rawVecGrowEvents 48 4 8 (BitVec.ofNat 64 d.changed.length))
    evs

private theorem dirPutStrEnv_of_missGrow_succ {d : DirGhost} {name bytes : List (BitVec 8)}
    {evs : List AllocEvent}
    (h : DirPutStrMissGrowBinarySuccEnv d name bytes evs) :
    DirPutStrEnv d name bytes evs := by
  obtain ⟨hne, hmiss, e1, e2, rfl, rfl, rfl⟩ := h
  exact dirPutStrEnv_of_nonempty hne (dirPutTailEnv_miss_grow hmiss)

/-- Binary-exact (`0` `SeqEnv`) `0`-prev `SessionRecord::serialize` (`Some`) sub-envelope
(`SegCloneEnv G sess.state` followed by `rustAllocEvents encLen 1`, matching
`SerializeSomeSeqFreeEnv G sess` with `FreeOnlyEvs.nil`). -/
def SerializeSomeNoDropSuccEnv (G : SessionGhost) (sess : Session (List (BitVec 8)))
    (evs : List AllocEvent) : Prop :=
  ConcatEnv (SegCloneEnv G sess.state)
    (· = rustAllocEvents (lenField 1 (encSessionMem G sess)).length 1)
    evs

private theorem recordSerializeSeqFreeValidEnv_of_succ
    {G : SessionGhost} {sess : Session (List (BitVec 8))}
    {r : SessionRecord (List (BitVec 8))} {evs : List AllocEvent}
    (hcur : r.currentSession = some sess)
    (hGV : SessionGhostValid G sess)
    (hSer : SerializeSomeNoDropSuccEnv G sess evs) :
    RecordSerializeSeqFreeValidEnv r evs := by
  obtain ⟨e1, _, rfl, hcl, rfl⟩ := hSer
  have hRGV : RecordGhostValid ⟨0#64, 8#64, some G⟩ r := by
    unfold RecordGhostValid
    dsimp only
    rw [hcur]
    exact hGV
  refine ⟨⟨0#64, 8#64, some G⟩, hRGV, ?_⟩
  unfold RecordSerializeSeqFreeEnv
  dsimp only
  rw [hcur]
  exact Or.inr ⟨e1, _, rfl, hcl, seqEnv_of_self_nil rfl⟩

/-- Binary-kit W1 (`send`) slot success sub-envelope for `W1SendBinaryKitSlotEnv P R`, chaining
`load_session`, `KyberOptEnv`, `OtrEncryptCoreEnv`, `PreKeyMsgNewRawEnv`, `is_trusted_identity`,
`save_identity`, `OtrApplyEnv`, and `store_session` via `ConcatEnv`. -/
def W1SendBinarySuccSlotEnv [LibsignalPlacement]
    (P : PEParams) (i₀ : Inputs) (R : W1BinarySendParams) (evs : List AllocEvent) : Prop :=
  let F := R.x.F
  let x := w1EncGhost R.x
  F = runFiles i₀ ∧
  ∃ (r₀ : SessionRecord (List (BitVec 8)))
    (sess₀ : Session (List (BitVec 8)))
    (otr₀ : OutgoingTripleRatchet (List (BitVec 8)))
    (taken₀ : SessionState (List (BitVec 8)))
    (k₀ : IdentityKey)
    (items : PendingPreKey)
    (kpk : CryptoGames.LibsignalSessionApi.PendingKyberPreKey)
    (pqrSt' : List (BitVec 8))
    (pqrKey : CryptoGames.HKDF.Salt)
    (pqrMsg : List (BitVec 8))
    (sm : SignalMessage)
    (peerIdBs : List (BitVec 8))
    (G' : SessionGhost)
    (sess' : Session (List (BitVec 8)))
    (evsAddrL evsGetL evsSpqr evsGetTr evsGetSv evsPutSv evsAddrS evsSer evsPutS :
      List AllocEvent),
    let otr' := otrAfterSome P.C (pqxdhSpqrModel P) uuidTryParse x otr₀
    let r' := storedRecord sess₀ otr' taken₀
    let smGhost := otrSignalMsgGhost P.C otr₀ pqrKey pqrMsg x.ptext (some x.loc) x.rem
    let pkOutLen := (preKeyMsgFromItems sess₀ items otr' sm).serialized.length
    (w1SessKitPlaced R.repAlloc R.B F R.x.peer).ScopeAt scopeKit StoresGhost.opened.sessions
      x.rem.val r₀ ∧
    DeserializeScopeP_Q NonEmptyV1Q r₀ ∧
    StoresGhost.opened.sessions.get cliIo.rd F (addressText x.rem.val) =
      .ok (encodeRecord r₀) ∧
    encodeRecord r₀ ≠ [] ∧
    r₀.currentSession = some sess₀ ∧
    execOk OutgoingTripleRatchet.fromSessionState sess₀.state = .ok (otr₀, taken₀) ∧
    taken₀.remoteIdentity = some k₀ ∧
    sess₀.pendingPreKey = some items ∧
    sess₀.pendingKyberPreKey = some kpk ∧
    0 < kpk.ciphertext.length ∧
    (pqxdhSpqrModel P).send otr₀.pqrState x.rest = some (pqrSt', pqrKey, pqrMsg) ∧
    CryptoGames.LibsignalSession.Mut.exec
      (OutgoingTripleRatchet.encrypt P.C protoSignalCodec (pqxdhSpqrModel P).spqr x.ptext
        (serializeAddresses (CryptoVerification.LibsignalTripleRatchetRepr.serviceIdParse uuidTryParse)
          x.loc x.rem) x.rest) otr₀ = (.ok sm, otr') ∧
    AddrTextBinarySuccEnv x.rem.val evsAddrL ∧
    DirGetMissOkBinarySuccEnv F StoresGhost.opened.sessions (addressText x.rem.val)
      (encodeRecord r₀) evsGetL ∧
    SpqrSendSuccTightEnv otr'.pqrState.length evsSpqr ∧
    StoresGhost.opened.identity.peers.get cliIo.rd F x.rem.val.name = .ok peerIdBs ∧
    DirGetMissOkBinarySuccEnv F StoresGhost.opened.identity.peers x.rem.val.name
      peerIdBs evsGetTr ∧
    DirGetMissOkBinarySuccEnv F StoresGhost.opened.identity.peers x.rem.val.name
      peerIdBs evsGetSv ∧
    DirPutStrMissGrowBinarySuccEnv StoresGhost.opened.identity.peers x.rem.val.name
      k₀.publicKey.serialize evsPutSv ∧
    r'.currentSession = some sess' ∧
    SessionGhostValid G' sess' ∧
    AddrTextBinarySuccEnv x.rem.val evsAddrS ∧
    SerializeSomeNoDropSuccEnv G' sess' evsSer ∧
    DirPutMissGrowBinarySuccEnv StoresGhost.opened.sessions (addressText x.rem.val)
      (encodeRecord r') evsPutS ∧
    ConcatEnv
      (ConcatEnv (· = rustAllocEvents 24 8)
        (ConcatEnv (· = evsAddrL)
          (ConcatEnv (· = evsGetL)
            (ConcatEnv (· = sessDeserEvents r₀)
              (· = rustDeallocEvents 24 8)))))
      (ConcatEnv (· = rustAllocEvents kpk.ciphertext.length 1)
        (ConcatEnv
          (ConcatEnv (· = evsSpqr)
            (ConcatEnv (· = rustAllocEvents 32 1)
              (ConcatEnv (· = rustAllocEvents ((x.ptext.length / 16 + 1) * 16) 1)
                (· = signalMessageNewEvents uuidTryParse smGhost))))
          (ConcatEnv
            (PreKeyMsgNewRawEnv (pendingKyberPayload sess₀) sm.serialized.length pkOutLen)
            (ConcatEnv
              (ConcatEnv (· = rustAllocEvents 32 8)
                (ConcatEnv (· = evsGetTr)
                  (· = rustDeallocEvents 32 8)))
              (ConcatEnv
                (ConcatEnv (· = rustAllocEvents 32 8)
                  (ConcatEnv (· = evsGetSv)
                    (ConcatEnv PublicKeySerializeEnv
                      (ConcatEnv (· = evsPutSv)
                        (· = rustDeallocEvents 32 8)))))
                (ConcatEnv (· = rustAllocEvents 32 1)
                  (ConcatEnv (· = rustAllocEvents 32 8)
                    (ConcatEnv (· = evsAddrS)
                      (ConcatEnv (· = evsSer)
                        (ConcatEnv (· = evsPutS)
                          (· = rustDeallocEvents 32 8)))))))))))
      evs

private theorem w1SendBinaryKitSlotEnv_of_succ [LibsignalPlacement]
    {P : PEParams} {i₀ : Inputs} {R : W1BinarySendParams} {evs : List AllocEvent}
    (h : W1SendBinarySuccSlotEnv P i₀ R evs) :
    W1SendBinaryKitSlotEnv P R evs := by
  obtain ⟨_hF_eq, r₀, sess₀, otr₀, taken₀, k₀, items, kpk, pqrSt', pqrKey, pqrMsg, sm,
    peerIdBs, G', sess',
    _, _, _, _, _, _, _, _, _,
    hScAt, hDeserQ, hSessGet, henc_ne, hCur0, hFrom0, hRemIk, hPendPk, hKpk, hkpk_pos,
    hSpqrSend, hMutEnc,
    hAddrL, hGetL, hSpqrSucc, hPeerGet, hGetTr, hGetSv, hPutSv,
    hCur', hGV', hAddrS, hSer, hPutS, hCat⟩ := h
  obtain ⟨evsLoad, rPostLoad, rfl, hLoadCat,
    evsKyber, rPostKyber, rfl, rfl,
    evsOtr, rPostOtr, rfl, hOtrCat,
    evsPkMsg, rPostPk, rfl, hPkRaw,
    evsTrust, rPostTr, rfl, hTrCat,
    evsSave, rPostSv, rfl, hSvCat,
    evsApply, rPostAp, rfl, rfl,
    evsBoxSt, rPostBs, rfl, rfl,
    evsAddrS, rPostAs, rfl, rfl,
    evsSer, rPostSr, rfl, rfl,
    evsPutS, eDeallocSt, rfl, rfl, rfl⟩ := hCat
  obtain ⟨_, _, rfl, rfl, evsAddrL, _, rfl, rfl, evsGetL, _, rfl, rfl, _, _, rfl, rfl, rfl⟩ := hLoadCat
  obtain ⟨evsSpqr, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, rfl⟩ := hOtrCat
  obtain ⟨_, _, rfl, rfl, evsGetTr, _, rfl, rfl, rfl⟩ := hTrCat
  obtain ⟨_, _, rfl, rfl, evsGetSv, _, rfl, rfl, ePkSer, _, rfl, hPkSer, evsPutSv, _, rfl, rfl, rfl⟩ := hSvCat
  let F := R.x.F
  let x := w1EncGhost R.x
  let kit := w1SessKitPlaced R.repAlloc R.B F R.x.peer
  let kitEnv := toTempTwinsKitEnv (w1BinarySessKitPlacedBudget R.repAlloc R.B F R.x.peer)
  let ikit := w1IdKitPlaced R.repAlloc R.B F R.x.peer
  let ikitEnv := toTempTwinsIkitEnv (w1BinaryIdKitPlacedBudget R.repAlloc R.B F R.x.peer)
  have hOptDeser :
      OptLoadDeserEnv scopeKit
        (LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser.ofBytesEnv
          RecordDeserializeCancelEnv)
        (StoresGhost.opened.sessions.get cliIo.rd F (addressText x.rem.val))
        (sessDeserEvents r₀) := by
    cases henc_eq : encodeRecord r₀ with
    | nil => exact absurd henc_eq henc_ne
    | cons b0 bsRest =>
      unfold OptLoadDeserEnv
      rw [hSessGet, henc_eq]
      exact ⟨r₀, henc_eq, hScAt.1, sessDeserEvents_mem_recordDeserializeCancelEnv hDeserQ⟩
  have hLoadPoll :
      kitEnv.loadPollEnv StoresGhost.opened.sessions x.rem.val
        (evsAddrL ++ (evsGetL ++ sessDeserEvents r₀)) :=
    Or.inr ⟨evsAddrL, evsGetL ++ sessDeserEvents r₀, rfl, addrTextValEnv_of_succ hAddrL,
      Or.inr ⟨evsGetL, sessDeserEvents r₀, rfl, dirGetEnv_of_missOk_succ' hGetL,
        seqEnv_of_self_nil hOptDeser⟩⟩
  have hBox24 :
      LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.BoxAllocEnv
        kit.loadBoxSize (rustAllocEvents 24 8) :=
    Or.inr ⟨by change 0 < 24; decide, rfl⟩
  have hLoadStep :
      SeqEnv
        (LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.BoxAllocEnv
          kit.loadBoxSize)
        (SeqEnv (kitEnv.loadPollEnv StoresGhost.opened.sessions x.rem.val)
          (· = rustDeallocEvents kit.loadBoxSize 8))
        (rustAllocEvents 24 8 ++
          (evsAddrL ++ (evsGetL ++ (sessDeserEvents r₀ ++ rustDeallocEvents 24 8)))) := by
    have hassoc :
        rustAllocEvents 24 8 ++
          (evsAddrL ++ (evsGetL ++ (sessDeserEvents r₀ ++ rustDeallocEvents 24 8))) =
        rustAllocEvents 24 8 ++
          ((evsAddrL ++ (evsGetL ++ sessDeserEvents r₀)) ++ rustDeallocEvents 24 8) := by
      simp only [List.append_assoc]
    rw [hassoc]
    exact Or.inr ⟨rustAllocEvents 24 8, _, rfl, hBox24,
      Or.inr ⟨_, rustDeallocEvents 24 8, rfl, hLoadPoll, rfl⟩⟩
  have hKyber :
      KyberOptEnv (sess₀.pendingKyberPreKey.map (·.ciphertext))
        (rustAllocEvents kpk.ciphertext.length 1) := by
    rw [hKpk]
    exact Or.inr ⟨hkpk_pos, rfl⟩
  have hSpqrCap :
      SpqrSendTightCapEnv otr₀.pqrState x.rest evsSpqr :=
    spqrSendTightCapEnv_of_succ otr₀.pqrState x.rest hSpqrSucc
  have hOtrCore :
      OtrEncryptCoreEnv P.C (pqxdhSpqrModel P) SpqrSendTightCapEnv uuidTryParse
        otr₀ x.ptext (some x.loc) x.rem x.rest
        (evsSpqr ++ (rustAllocEvents 32 1 ++
          (rustAllocEvents ((x.ptext.length / 16 + 1) * 16) 1 ++
            signalMessageNewEvents uuidTryParse
              (otrSignalMsgGhost P.C otr₀ pqrKey pqrMsg x.ptext (some x.loc) x.rem)))) := by
    unfold OtrEncryptCoreEnv
    refine Or.inr ⟨evsSpqr, _, rfl, hSpqrCap, ?_⟩
    rw [hSpqrSend]
    exact Or.inr ⟨rustAllocEvents 32 1, _, rfl, seqEnv_of_self_nil rfl,
      Or.inr ⟨rustAllocEvents ((x.ptext.length / 16 + 1) * 16) 1, _, rfl, rfl,
        seqEnv_of_self_nil rfl⟩⟩
  have hBox32Tr :
      LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.BoxAllocEnv
        ikit.trustBoxSize (rustAllocEvents 32 8) :=
    Or.inr ⟨by change 0 < 32; decide, rfl⟩
  have hTrustPoll :
      ikitEnv.trustPollEnv StoresGhost.opened.identity x.rem.val k₀ .sending evsGetTr :=
    seqEnv_of_self_nil (dirGetEnv_of_missOk_succ' hGetTr)
  have hTrustStep :
      TrustStepEnv ikit ikitEnv StoresGhost.opened.identity x.rem.val k₀
        (rustAllocEvents 32 8 ++ (evsGetTr ++ rustDeallocEvents 32 8)) :=
    Or.inr ⟨rustAllocEvents 32 8, _, rfl, hBox32Tr,
      Or.inr ⟨evsGetTr, rustDeallocEvents 32 8, rfl, hTrustPoll, rfl⟩⟩
  have hBox32Sv :
      LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.BoxAllocEnv
        ikit.saveBoxSize (rustAllocEvents 32 8) :=
    Or.inr ⟨by change 0 < 32; decide, rfl⟩
  have hSavePoll :
      ikitEnv.savePollEnv
        (ikit.trustUpdate StoresGhost.opened.identity x.rem.val k₀ .sending (.ok true))
        x.rem.val k₀
        (evsGetSv ++ (ePkSer ++ evsPutSv)) := by
    change cliIdentityKitSavePollEnv cliIo.rd
      (DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd) DirPutStrEnv F
      StoresGhost.opened.identity x.rem.val k₀ (evsGetSv ++ (ePkSer ++ evsPutSv))
    refine Or.inr ⟨evsGetSv, ePkSer ++ evsPutSv, rfl, dirGetEnv_of_missOk_succ' hGetSv, ?_⟩
    unfold LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget.cliIdentityKitSaveTailEnv
    rw [hPeerGet]
    exact Or.inr ⟨[], ePkSer ++ evsPutSv, rfl, FreeOnlyEvs.nil,
      Or.inr ⟨ePkSer, evsPutSv, rfl, hPkSer, dirPutStrEnv_of_missGrow_succ hPutSv⟩⟩
  have hSaveStep :
      SaveStepEnv ikit ikitEnv
        (ikit.trustUpdate StoresGhost.opened.identity x.rem.val k₀ .sending (.ok true))
        x.rem.val k₀
        (rustAllocEvents 32 8 ++ (evsGetSv ++ (ePkSer ++ (evsPutSv ++ rustDeallocEvents 32 8)))) := by
    have hassoc :
        rustAllocEvents 32 8 ++ (evsGetSv ++ (ePkSer ++ (evsPutSv ++ rustDeallocEvents 32 8))) =
        rustAllocEvents 32 8 ++ ((evsGetSv ++ (ePkSer ++ evsPutSv)) ++ rustDeallocEvents 32 8) := by
      simp only [List.append_assoc]
    rw [hassoc]
    exact Or.inr ⟨rustAllocEvents 32 8, _, rfl, hBox32Sv,
      Or.inr ⟨_, rustDeallocEvents 32 8, rfl, hSavePoll, rfl⟩⟩
  have hBox32St :
      LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.BoxAllocEnv
        kit.storeBoxSize (rustAllocEvents 32 8) :=
    Or.inr ⟨by change 0 < 32; decide, rfl⟩
  have hStorePoll :
      kitEnv.storePollEnv StoresGhost.opened.sessions x.rem.val
        (storedRecord sess₀ (otrAfterSome P.C (pqxdhSpqrModel P) uuidTryParse x otr₀) taken₀)
        (evsAddrS ++ (evsSer ++ evsPutS)) :=
    Or.inr ⟨evsAddrS, evsSer ++ evsPutS, rfl, addrTextValEnv_of_succ hAddrS,
      Or.inr ⟨evsSer, evsPutS, rfl,
        recordSerializeSeqFreeValidEnv_of_succ hCur' hGV' hSer,
        dirPutEnv_of_missGrow_succ hPutS⟩⟩
  have hFromApply :
      FromApplyEnv kit kitEnv StoresGhost.opened.sessions x sess₀
        (otrAfterSome P.C (pqxdhSpqrModel P) uuidTryParse x otr₀) taken₀
        (rustAllocEvents 32 1 ++
          (rustAllocEvents 32 8 ++
            (evsAddrS ++ (evsSer ++ (evsPutS ++ rustDeallocEvents 32 8))))) := by
    have hassoc :
        rustAllocEvents 32 8 ++ (evsAddrS ++ (evsSer ++ (evsPutS ++ rustDeallocEvents 32 8))) =
        rustAllocEvents 32 8 ++ ((evsAddrS ++ (evsSer ++ evsPutS)) ++ rustDeallocEvents 32 8) := by
      simp only [List.append_assoc]
    rw [hassoc]
    exact Or.inr ⟨rustAllocEvents 32 1, _, rfl, Or.inl rfl,
      Or.inr ⟨rustAllocEvents 32 8, _, rfl, hBox32St,
        Or.inr ⟨_, rustDeallocEvents 32 8, rfl, hStorePoll,
          seqEnv_of_self_nil rfl⟩⟩⟩
  let evsApplyTail :=
    rustAllocEvents 32 1 ++
      (rustAllocEvents 32 8 ++
        (evsAddrS ++ (evsSer ++ (evsPutS ++ rustDeallocEvents 32 8))))
  let evsSaveTail :=
    (rustAllocEvents 32 8 ++ (evsGetSv ++ (ePkSer ++ (evsPutSv ++ rustDeallocEvents 32 8)))) ++
      evsApplyTail
  let evsCmTail :=
    (rustAllocEvents 32 8 ++ (evsGetTr ++ rustDeallocEvents 32 8)) ++ evsSaveTail
  let evsOtrCore :=
    evsSpqr ++ (rustAllocEvents 32 1 ++
      (rustAllocEvents ((x.ptext.length / 16 + 1) * 16) 1 ++
        signalMessageNewEvents uuidTryParse
          (otrSignalMsgGhost P.C otr₀ pqrKey pqrMsg x.ptext (some x.loc) x.rem)))
  have hFromSave :
      FromSaveEnv kit kitEnv StoresGhost.opened.sessions ikit ikitEnv
        (ikit.trustUpdate StoresGhost.opened.identity x.rem.val k₀ .sending (.ok true))
        x sess₀ (otrAfterSome P.C (pqxdhSpqrModel P) uuidTryParse x otr₀) taken₀ k₀ evsSaveTail :=
    Or.inr ⟨_, _, rfl, hSaveStep, Or.inr hFromApply⟩
  have hFromCm :
      FromCmEnv kit kitEnv StoresGhost.opened.sessions ikit ikitEnv
        StoresGhost.opened.identity x sess₀
        (otrAfterSome P.C (pqxdhSpqrModel P) uuidTryParse x otr₀) taken₀ k₀ evsCmTail :=
    Or.inr ⟨_, _, rfl, hTrustStep, Or.inr (Or.inr hFromSave)⟩
  have hPreKeyPost :
      PreKeyPostEncryptEnv P.C (pqxdhSpqrModel P) uuidTryParse
        kit kitEnv StoresGhost.opened.sessions ikit ikitEnv StoresGhost.opened.identity
        x sess₀ otr₀ taken₀ k₀ items (evsPkMsg ++ evsCmTail) := by
    unfold PreKeyPostEncryptEnv
    dsimp only
    rw [hMutEnc]
    exact Or.inr (Or.inr ⟨evsPkMsg, evsCmTail, rfl, hPkRaw, Or.inr hFromCm⟩)
  have hFromKey :
      FromKeyEnv P.C (pqxdhSpqrModel P) SpqrSendTightCapEnv uuidTryParse
        kit kitEnv StoresGhost.opened.sessions ikit ikitEnv StoresGhost.opened.identity
        x sess₀ otr₀ taken₀ k₀
        (rustAllocEvents kpk.ciphertext.length 1 ++ (evsOtrCore ++ (evsPkMsg ++ evsCmTail))) :=
    Or.inr ⟨items, hPendPk,
      Or.inr (Or.inr ⟨rustAllocEvents kpk.ciphertext.length 1, _, rfl, hKyber,
        Or.inr ⟨evsOtrCore, evsPkMsg ++ evsCmTail, rfl, hOtrCore, hPreKeyPost⟩⟩)⟩
  have hFromOtr :
      FromOtrEnv P.C (pqxdhSpqrModel P) SpqrSendTightCapEnv uuidTryParse
        kit kitEnv StoresGhost.opened.sessions ikit ikitEnv StoresGhost.opened.identity
        x sess₀ otr₀ taken₀
        (rustAllocEvents kpk.ciphertext.length 1 ++ (evsOtrCore ++ (evsPkMsg ++ evsCmTail))) :=
    Or.inr ⟨k₀, hRemIk, hFromKey⟩
  exact Or.inr ⟨_, _, rfl, hLoadStep,
    Or.inr (Or.inr (Or.inr ⟨[], _, rfl, FreeOnlyEvs.nil,
      Or.inr ⟨r₀, sess₀, otr₀, taken₀, hScAt, hCur0, hFrom0, hFromOtr⟩⟩))⟩

/-- Binary-kit `.send`-arm whole-`main` success sub-envelope chained via `ConcatEnv` and
`IterConcatEnv` across `M1 → M2 → M3 → R0 → R2 (W1SendBinarySuccSlotEnv) → M5 → M6`. -/
def SendSuccBinaryKitMainEnv [LibsignalPlacement]
    (W : CliHooks) (i₀ : Inputs) (evs : List AllocEvent) : Prop :=
  let P₀ : PEParams := ⟨W.C, W.Q⟩
  ∃ (p₀ : PqParty) (ptext : List (BitVec 8)) (coins : List.Vector (BitVec 8) 64)
    (st₁ : PqParty) (x₀ x₁ : RecordExtras) (g₀ g₁ : GhostState (List (BitVec 8)))
    (ag : AddressCall) (peerAddr : AddrV) (w1R : W1BinarySendParams)
    (coinsBs ownB bs1 : List (BitVec 8))
    (evsM2 evsR0Get evsEnc evsM5 : List AllocEvent),
    PqxdhPartyInSpecDomain P₀ p₀ ∧
    p₀.session = some (x₀, g₀) ∧
    g₀.session.pendingPreKey = true ∧
    pqSendModel P₀ p₀ ptext coins.toList = some (some (st₁, wirePrekey :: bs1)) ∧
    st₁.session = some (x₁, g₁) ∧
    PqxdhPartyInSpecDomain P₀ st₁ ∧
    i₀ = pqSendInputs P₀ p₀ ptext coins ∧
    i₀.argv.map bytesOfString = [utf8 "send", ag.bs] ∧
    addrParse uuidTryParse ag.bs = some peerAddr ∧
    parseArgs uuidTryParse (i₀.argv.map bytesOfString) = some (.send peerAddr) ∧
    W1BinarySendDom (.send peerAddr) i₀ w1R ∧
    (w1EncGhost w1R.x).ptext = ptext ∧
    coinsBs = coins.toList ∧
    (w1EncGhost w1R.x).rest = coinsBs ∧
    addrParse uuidTryParse ownB =
      some ⟨(w1EncGhost w1R.x).loc.name.bytes, (w1EncGhost w1R.x).loc.device⟩ ∧
    (w1EncGhost w1R.x).now = SystemTime.unixEpoch ∧
    i₀.stdin.length ≤ msgCapBytes ∧
    readFileResult (initFsState (cliInputs i₀)).files (utf8 "coins") = .ok coinsBs ∧
    IterConcatEnv M2CollectStepEnv (List.range i₀.argv.length) evsM2 ∧
    StoresGhost.opened.identity.own.get cliIo.rd (runFiles i₀) (utf8 "address") = .ok ownB ∧
    DirGetMissOkBinarySuccEnv (runFiles i₀) StoresGhost.opened.identity.own
      (utf8 "address") ownB evsR0Get ∧
    W1SendBinarySuccSlotEnv P₀ i₀ w1R evsEnc ∧
    0 < bs1.length ∧
    bs1.length ≤ sessionCapBytes ∧
    IterConcatEnv
      (fun dn => IterConcatEnv (fun name => M5LoopAEntryEnv dn.1 name) dn.2)
      [(StoresGhost.opened.identity.peers.path, [(w1EncGhost w1R.x).rem.val.name]),
       (StoresGhost.opened.sessions.path, [addressText w1R.peer.val])]
      evsM5 ∧
    AllocEvent.alloc 1569 ∈ evsEnc ∧
    AllocEvent.alloc 16 ∈ evsEnc ∧
    AllocEvent.alloc 36 ∈ evsEnc ∧
    AllocEvent.realloc 1 36 72 ∈ evsEnc ∧
    AllocEvent.alloc 8 ∈ evsEnc ∧
    ConcatEnv
      (ConcatEnv (· = rustAllocEvents (16 * i₀.argv.length) 8)
        (ConcatEnv (· = evsM2)
          (ConcatEnv (· = addressEvents uuidTryParse ag.bs)
            (ConcatEnv (· = allocBytes1Events i₀.stdin)
              (· = allocBytes1Events coinsBs)))))
      (ConcatEnv
        (ConcatEnv
          (ConcatEnv (· = evsR0Get)
            (ConcatEnv (· = addressEvents uuidTryParse ownB)
              (· = deallocBytes1OfLen ownB.length)))
          (ConcatEnv (· = evsEnc)
            (· = cliConcat2Events [wirePrekey] bs1)))
        (ConcatEnv (· = evsM5)
          (· = rustAllocEvents 1024 1)))
      evs

private theorem freeOnlyEvs_deallocBytes1OfLen (n : Nat) :
    FreeOnlyEvs (deallocBytes1OfLen n) := by
  unfold deallocBytes1OfLen
  split
  · exact FreeOnlyEvs.nil
  · exact FreeOnlyEvs.singleton 1 n

/-- Inclusion of `SendSuccBinaryKitMainEnv` into `realCliMainBinaryKitEnvOf img S X W i₀`. -/
theorem sendSuccBinaryKitMainEnv_sub_realCliMainBinaryKitEnvOf [LibsignalPlacement]
    (img : Arm64.Obj.Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (i₀ : Inputs) (evs : List AllocEvent)
    (hSucc : SendSuccBinaryKitMainEnv W i₀ evs) :
    realCliMainBinaryKitEnvOf img S X W i₀ evs := by
  obtain ⟨p₀, ptext, coins, st₁, x₀, x₁, g₀, g₁, ag, peerAddr, w1R,
    coinsBs, ownB, bs1, _, _, _, _,
    _, _, _, _, _, _, _, _, _, hparse, hw1Dom, _, _, _, _, _,
    hstdin_le, hcoins, hM2,
    hOwnGet, hR0Get, hW1Succ, _, hbs1_le, hM5, _, _, _, _, _, hMainCat⟩ := hSucc
  obtain ⟨evsSetup, evsPost, rfl, hSetupCat,
    evsRun, evsM5M6, rfl, hRunCat,
    evsM5, eM6, rfl, rfl, rfl⟩ := hMainCat
  obtain ⟨_, _, rfl, rfl, evsM2, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, rfl⟩ := hSetupCat
  obtain ⟨evsR0, evsArm, rfl, hR0Cat, evsEnc, _, rfl, rfl, rfl⟩ := hRunCat
  obtain ⟨evsR0Get, _, rfl, rfl, _, _, rfl, rfl, rfl⟩ := hR0Cat
  have hCoinsEnv :
      ReadFileEnv (initFsState (cliInputs i₀)).files (utf8 "coins")
        (allocBytes1Events coinsBs) := by
    unfold ReadFileEnv
    rw [hcoins]
    exact Or.inl rfl
  have hM3 :
      M3PhaseEnv true i₀.stdin (initFsState (cliInputs i₀)).files (utf8 "coins")
        (allocBytes1Events i₀.stdin ++ allocBytes1Events coinsBs) :=
    Or.inr ⟨allocBytes1Events i₀.stdin, allocBytes1Events coinsBs, rfl, Or.inl rfl,
      seqEnv_of_self_nil hCoinsEnv⟩
  have hSetup :
      CliMainSetupEnv uuidTryParse i₀ (some ag) true
        (rustAllocEvents (16 * i₀.argv.length) 8 ++
          (evsM2 ++ (addressEvents uuidTryParse ag.bs ++
            (allocBytes1Events i₀.stdin ++ allocBytes1Events coinsBs)))) :=
    Or.inr ⟨rustAllocEvents (16 * i₀.argv.length) 8, _, rfl, Or.inr rfl,
      Or.inr ⟨evsM2, _, rfl, iterSeqEnv_of_iterConcatEnv hM2,
        Or.inr ⟨addressEvents uuidTryParse ag.bs, _, rfl, rfl, hM3⟩⟩⟩
  have hBoundedSetup :
      CliMainBoundedSetupEnv i₀.argv.length
        (rustAllocEvents (16 * i₀.argv.length) 8 ++
          (evsM2 ++ (addressEvents uuidTryParse ag.bs ++
            (allocBytes1Events i₀.stdin ++ allocBytes1Events coinsBs)))) :=
    cliMainBoundedSetupEnv_of_setup_any uuidTryParse i₀ (some ag) true (fun _ => hstdin_le) hSetup
  have hd := hw1Dom peerAddr rfl
  have ⟨hPeer40, hRem40⟩ := peer_and_rem_name_le_40_of_send hparse hd.1 hd.2.2.1
  let dirs : List (List (BitVec 8) × List (List (BitVec 8))) :=
    [(StoresGhost.opened.identity.peers.path, [(w1EncGhost w1R.x).rem.val.name]),
     (StoresGhost.opened.sessions.path, [addressText w1R.peer.val])]
  have hDirsBounds :
      ∀ dn ∈ dirs,
        dn.1.length ≤ cliMaxDirPathBytes ∧ ∀ nm ∈ dn.2, nm.length ≤ cliMaxAddrTextBytes := by
    intro dn hdn
    rcases List.mem_cons.mp hdn with rfl | hdn2
    · refine ⟨by dsimp only; rw [peers_path_eq]; unfold succKutf8 cliMaxDirPathBytes; decide,
        fun nm hnm => ?_⟩
      rw [List.mem_singleton] at hnm
      subst hnm
      exact Nat.le_trans hRem40 (by unfold cliMaxAddrTextBytes; decide)
    · rw [List.mem_singleton] at hdn2
      subst hdn2
      refine ⟨by dsimp only; rw [sessions_path_eq]; unfold succKutf8 cliMaxDirPathBytes; decide,
        fun nm hnm => ?_⟩
      rw [List.mem_singleton] at hnm
      subst hnm
      exact w1_peer_addressText_le_64 hPeer40
  let w : ValidPostSetupWitness i₀ := {
    g := ⟨i₀, .send peerAddr, some none, 0#64, 0#64, 0#64, 0#64, 0#64⟩
    g_i := rfl
    parse_ok := hparse
    stdin_le := hstdin_le
    dirs := dirs
    dirs_sum_le := by simp [dirs, cliMaxDirtyEntries]
    dirs_bounds := hDirsBounds
    ok := true
  }
  have hPreAfter :
      PreAfterGetEnv w.g
        (addressEvents uuidTryParse ownB ++ deallocBytes1OfLen ownB.length) := by
    unfold PreAfterGetEnv
    dsimp only [w]
    rw [hOwnGet]
    exact Or.inr ⟨addressEvents uuidTryParse ownB, deallocBytes1OfLen ownB.length, rfl, rfl,
      freeOnlyEvs_deallocBytes1OfLen ownB.length⟩
  have hR0Bin :
      R0BinaryEnv cliIo.rd w.g
        (evsR0Get ++ (addressEvents uuidTryParse ownB ++ deallocBytes1OfLen ownB.length)) :=
    Or.inr (Or.inr ⟨evsR0Get, _, rfl, dirGetEnv_of_missOk_succ' hR0Get, hPreAfter⟩)
  have hEncSlot : (mkBinaryKitRealCalleeEnvs img S X W w.g).encEnv evsEnc :=
    ⟨w1R, hw1Dom, w1SendBinaryKitSlotEnv_of_succ hW1Succ⟩
  have hTail :
      R2ConcatTailEnv sessionCapBytes (cliConcat2Events [wirePrekey] bs1) :=
    Or.inr ⟨[wirePrekey], by decide, bs1, hbs1_le, seqEnv_of_self_nil rfl⟩
  have hArmBin :
      RunArmBinaryEnv cliIo.rd (runFiles w.g.i) (mkBinaryKitRealCalleeEnvs img S X W w.g)
        sessionCapBytes w.g.i.stdin w.g.c
        (evsEnc ++ cliConcat2Events [wirePrekey] bs1) :=
    Or.inr (Or.inr ⟨evsEnc, cliConcat2Events [wirePrekey] bs1, rfl, hEncSlot, hTail⟩)
  have hRunBin :
      CliRunBinaryEnv cliIo.rd (mkBinaryKitRealCalleeEnvs img S X W w.g) sessionCapBytes w.g
        ((evsR0Get ++ (addressEvents uuidTryParse ownB ++ deallocBytes1OfLen ownB.length)) ++
          (evsEnc ++ cliConcat2Events [wirePrekey] bs1)) :=
    Or.inr (Or.inr ⟨_, _, rfl, hR0Bin, seqEnv_of_self_nil hArmBin⟩)
  obtain ⟨evsM5_peers, restM5, rfl, hM5_peers, evsM5_sess, endM5, rfl, hM5_sess, rfl⟩ := hM5
  rw [List.append_nil]
  obtain ⟨evsP1, nilP1, rfl, hP1, rfl⟩ := hM5_peers
  rw [List.append_nil]
  obtain ⟨evsS1, nilS1, rfl, hS1, rfl⟩ := hM5_sess
  rw [List.append_nil]
  have hPeersNe : StoresGhost.opened.identity.peers.path ≠ [] := by
    rw [peers_path_eq]; decide
  have hSessNe : StoresGhost.opened.sessions.path ≠ [] := by
    rw [sessions_path_eq]; decide
  have hDirPeers :
      M5DirStepEnv StoresGhost.opened.identity.peers.path [(w1EncGhost w1R.x).rem.val.name] evsP1 := by
    refine seqEnv_of_self_nil (Or.inr ⟨evsP1, [], (List.append_nil _).symm, ?_, rfl⟩)
    simp only [LibsignalBinary.Proofs.PeakBudget.CliMainPeakSpec.M5WriteStepEnv, hPeersNe,
      ↓reduceIte]
    exact hP1
  have hDirSess :
      M5DirStepEnv StoresGhost.opened.sessions.path [addressText w1R.peer.val] evsS1 := by
    refine seqEnv_of_self_nil (Or.inr ⟨evsS1, [], (List.append_nil _).symm, ?_, rfl⟩)
    simp only [LibsignalBinary.Proofs.PeakBudget.CliMainPeakSpec.M5WriteStepEnv, hSessNe,
      ↓reduceIte]
    exact hS1
  have hM5Phase : M5PhaseEnv w.dirs (evsP1 ++ evsS1) :=
    seqEnv_of_self_nil
      (Or.inr ⟨evsP1, evsS1, rfl, hDirPeers,
        Or.inr ⟨evsS1, [], (List.append_nil _).symm, hDirSess, rfl⟩⟩)
  have hM6 : M6Env w.ok (rustAllocEvents 1024 1) :=
    seqEnv_of_self_nil (Or.inr rfl)
  exact Or.inr ⟨_, _, rfl, hBoundedSetup,
    Or.inr ⟨w, rfl,
      Or.inr ⟨_, _, rfl, hRunBin,
        Or.inr ⟨evsP1 ++ evsS1, rustAllocEvents 1024 1, rfl, hM5Phase, hM6⟩⟩⟩⟩

/-- Alias form of `sendSuccBinaryKitMainEnv_sub_realCliMainBinaryKitEnvOf` on
`RealCliMainBinaryEnvOf (mkBinaryKitRealCalleeEnvs img S X W) i₀`. -/
theorem sendSuccBinaryKitMainEnv_sub_realCliMainBinaryEnvOf [LibsignalPlacement]
    (img : Arm64.Obj.Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (i₀ : Inputs) (evs : List AllocEvent)
    (hSucc : SendSuccBinaryKitMainEnv W i₀ evs) :
    RealCliMainBinaryEnvOf (mkBinaryKitRealCalleeEnvs img S X W) i₀ evs :=
  sendSuccBinaryKitMainEnv_sub_realCliMainBinaryKitEnvOf img S X W i₀ evs hSucc

/-- Concrete `CliHooks` witness lifting `NonVacuityPq.W0 = ⟨C0, Q0⟩` with canonical `bcmp` and
`utf8Err`. -/
private def sendWitnessCliHooks : CliHooks where
  C := CryptoVerification.SignalSession.NonVacuityPq.C0
  Q := CryptoVerification.SignalSession.NonVacuityPq.Q0
  bcmp := fun a b => if a == b then 0#64 else 1#64
  bcmp_ok := by
    intro a b _
    by_cases h : a = b
    · subst h; simp
    · have hbeq : (a == b) = false := beq_false_of_ne h
      simp [hbeq, h]
  utf8Err := fun _ => (0#64, 0#16)

private def sendWitnessRunEncGhost : EncGhost where
  peer := nonVacSendAddrGhost nonVacSendPeer
  peerA := 0#64
  me := nonVacSendAddrGhost sendWitnessOwnAddr
  meA := 0#64
  stores := 0#64
  ret := 0#64
  coinsP := 0#64
  F := runFiles sendWitnessInputs
  coins := sendWitnessCoins.toList
  ptA := 0#64
  ptext := []

private def sendWitnessW1BinParams : W1BinarySendParams where
  repAlloc := { pool := emp, live := fun _ _ _ => emp }
  B := ⟨0⟩
  peer := nonVacSendAddrGhost nonVacSendPeer
  x := sendWitnessRunEncGhost

private theorem sendWitnessW1BinParams_dom :
    W1BinarySendDom (.send nonVacSendPeer) sendWitnessInputs sendWitnessW1BinParams := by
  intro peerAddr h
  injection h with hp
  subst hp
  exact ⟨rfl, rfl, rfl, Nat.zero_le msgCapBytes, rfl⟩

private theorem sendWitness_spqrSend_isSome :
    ((pqxdhSpqrModel W0).send sendWitnessOtr0.pqrState sendWitnessCoins.toList).isSome = true := by
  decide +kernel

private def sendWitnessSpqrTriple :
    List (BitVec 8) × CryptoGames.HKDF.Salt × List (BitVec 8) :=
  match (pqxdhSpqrModel W0).send sendWitnessOtr0.pqrState sendWitnessCoins.toList with
  | some t => t
  | none => ([], none, [])

private theorem sendWitness_spqrSend_eq :
    (pqxdhSpqrModel W0).send sendWitnessOtr0.pqrState sendWitnessCoins.toList =
      some sendWitnessSpqrTriple := by
  have hs := sendWitness_spqrSend_isSome
  unfold sendWitnessSpqrTriple
  cases hm : (pqxdhSpqrModel W0).send sendWitnessOtr0.pqrState sendWitnessCoins.toList with
  | none => rw [hm] at hs; cases hs
  | some t => rfl

private theorem sendWitness_spqrSend_eq' :
    (pqxdhSpqrModel W0).send sendWitnessOtr0.pqrState
      (w1EncGhost sendWitnessW1BinParams.x).rest =
      some (sendWitnessSpqrTriple.1, sendWitnessSpqrTriple.2.1, sendWitnessSpqrTriple.2.2) := by
  have hrest : (w1EncGhost sendWitnessW1BinParams.x).rest = sendWitnessCoins.toList := rfl
  rw [hrest, sendWitness_spqrSend_eq]

private theorem sendWitness_otrAfterSome_eq :
    otrAfterSome W0.C (pqxdhSpqrModel W0) uuidTryParse
      (w1EncGhost sendWitnessW1BinParams.x) sendWitnessOtr0 = sendWitnessOtr' := by
  unfold sendWitnessOtr' otrAfterSome
  dsimp only [w1EncGhost, sendWitnessW1BinParams, sendWitnessRunEncGhost,
    sendWitnessW1Params, sendWitnessEncGhost]

private theorem sendWitness_mutEncrypt_isOk :
    (CryptoGames.LibsignalSession.Mut.exec
      (OutgoingTripleRatchet.encrypt W0.C protoSignalCodec (pqxdhSpqrModel W0).spqr []
        (serializeAddresses
          (CryptoVerification.LibsignalTripleRatchetRepr.serviceIdParse uuidTryParse)
          (w1EncGhost sendWitnessRunEncGhost).loc (w1EncGhost sendWitnessRunEncGhost).rem)
        sendWitnessCoins.toList)
      sendWitnessOtr0).1.isOk = true := by
  decide +kernel

private def sendWitnessRealSm : SignalMessage :=
  match (CryptoGames.LibsignalSession.Mut.exec
      (OutgoingTripleRatchet.encrypt W0.C protoSignalCodec (pqxdhSpqrModel W0).spqr []
        (serializeAddresses
          (CryptoVerification.LibsignalTripleRatchetRepr.serviceIdParse uuidTryParse)
          (w1EncGhost sendWitnessRunEncGhost).loc (w1EncGhost sendWitnessRunEncGhost).rem)
        sendWitnessCoins.toList)
      sendWitnessOtr0).1 with
  | .ok sm => sm
  | .error _ => sendWitnessSmModel

private theorem sendWitness_mutEncrypt_eq :
    CryptoGames.LibsignalSession.Mut.exec
      (OutgoingTripleRatchet.encrypt W0.C protoSignalCodec (pqxdhSpqrModel W0).spqr []
        (serializeAddresses
          (CryptoVerification.LibsignalTripleRatchetRepr.serviceIdParse uuidTryParse)
          (w1EncGhost sendWitnessRunEncGhost).loc (w1EncGhost sendWitnessRunEncGhost).rem)
        sendWitnessCoins.toList)
      sendWitnessOtr0 = (.ok sendWitnessRealSm, sendWitnessOtr') := by
  have hok := sendWitness_mutEncrypt_isOk
  unfold sendWitnessRealSm sendWitnessOtr' otrAfterSome
  dsimp only [w1EncGhost, sendWitnessRunEncGhost, sendWitnessW1Params, sendWitnessEncGhost] at hok ⊢
  generalize hp :
      CryptoGames.LibsignalSession.Mut.exec
        (OutgoingTripleRatchet.encrypt W0.C protoSignalCodec (pqxdhSpqrModel W0).spqr []
          (serializeAddresses
            (CryptoVerification.LibsignalTripleRatchetRepr.serviceIdParse uuidTryParse)
            (nonVacSendAddrGhost sendWitnessOwnAddr) (nonVacSendAddrGhost nonVacSendPeer))
          sendWitnessCoins.toList)
        sendWitnessOtr0 = pair at hok ⊢
  rcases pair with ⟨res, otr1⟩
  cases res with
  | error _ => cases hok
  | ok sm => rfl

private theorem sendWitness_mutEncrypt_eq' :
    let x := w1EncGhost sendWitnessW1BinParams.x
    CryptoGames.LibsignalSession.Mut.exec
      (OutgoingTripleRatchet.encrypt W0.C protoSignalCodec (pqxdhSpqrModel W0).spqr x.ptext
        (serializeAddresses
          (CryptoVerification.LibsignalTripleRatchetRepr.serviceIdParse uuidTryParse)
          x.loc x.rem) x.rest)
      sendWitnessOtr0 =
      (.ok sendWitnessRealSm,
       otrAfterSome W0.C (pqxdhSpqrModel W0) uuidTryParse x sendWitnessOtr0) := by
  dsimp only
  rw [sendWitness_otrAfterSome_eq]
  exact sendWitness_mutEncrypt_eq

/-- All four `Dir::get` calls on the concrete `.send` witness inputs (`R0` `"address"`,
`load_session`, `is_trusted_identity`, and `save_identity`) return `.ok _` (`≠ .error ()`). -/
theorem sendWitness_dirGet_err_unreachable :
    ∃ (i₀ : Inputs),
      CliPqxdhInputs W0 i₀ ∧
      parseArgs uuidTryParse (i₀.argv.map bytesOfString) = some (.send nonVacSendPeer) ∧
      let F := runFiles i₀
      let pOwn := pathOf StoresGhost.opened.identity.own.path (utf8 "address")
      let pSess := pathOf StoresGhost.opened.sessions.path (addressText (addrValOf nonVacSendPeer))
      let pPeer := pathOf StoresGhost.opened.identity.peers.path (addrValOf nonVacSendPeer).name
      cliIo.rd F pOwn ≠ .error () ∧
      cliIo.rd F pSess ≠ .error () ∧
      cliIo.rd F pPeer ≠ .error () ∧
      DirGetErrAllocEnv cliIo.rd F pOwn = (· = []) ∧
      DirGetErrAllocEnv cliIo.rd F pSess = (· = []) ∧
      DirGetErrAllocEnv cliIo.rd F pPeer = (· = []) := by
  have hOwn :
      cliIo.rd (runFiles sendWitnessInputs)
        (pathOf StoresGhost.opened.identity.own.path (utf8 "address")) =
      .ok (CryptoVerification.SignalSession.textBytes (partyAddress .A).text) :=
    sendWitnessOwn_get
  have hSessCap : (pqSessBytes sendWitnessP0).length ≤ fileCapBytes :=
    pqSessBytes_le_fileCapBytes sendWitnessP0_props.2
  have hSess :
      cliIo.rd (runFiles sendWitnessInputs)
        (pathOf StoresGhost.opened.sessions.path (addressText (addrValOf nonVacSendPeer))) =
      .ok (encodeRecord sendWitnessR0) := by
    change StoresGhost.opened.sessions.get cliIo.rd (runFiles sendWitnessInputs)
      (addressText (addrValOf nonVacSendPeer)) = .ok (encodeRecord sendWitnessR0)
    rw [sendWitnessR0_encode_eq]
    have h := pqSessGet_send W0 sendWitnessP0 [] sendWitnessCoins hSessCap
    rwa [sendWitnessP0_party] at h
  have hPeer :
      cliIo.rd (runFiles sendWitnessInputs)
        (pathOf StoresGhost.opened.identity.peers.path (addrValOf nonVacSendPeer).name) =
      .ok (pqIdBytes sendWitnessP0) := by
    change StoresGhost.opened.identity.peers.get cliIo.rd (runFiles sendWitnessInputs)
      (addrValOf nonVacSendPeer).name = .ok (pqIdBytes sendWitnessP0)
    have h := pqIdGet_send W0 sendWitnessP0 [] sendWitnessCoins
    rwa [sendWitnessP0_party] at h
  exact ⟨sendWitnessInputs, sendWitnessInputs_cliPqxdh, sendWitnessInputs_parseArgs,
    (by rw [hOwn]; intro hc; cases hc),
    (by rw [hSess]; intro hc; cases hc),
    (by rw [hPeer]; intro hc; cases hc),
    (by unfold DirGetErrAllocEnv; rw [hOwn]),
    (by unfold DirGetErrAllocEnv; rw [hSess]),
    (by unfold DirGetErrAllocEnv; rw [hPeer])⟩

/-- Binary-kit `.send` success-path non-vacuity witness on
`realCliMainBinaryKitEnvOf img S X W₀ i₀` at `W₀ = sendWitnessCliHooks` (exhibiting the Block `594`
`address_text` trace, `.ok` `Dir::get` reads without `22`-byte error allocations, hook-model read
disjuncts, and `CliWriteStdoutEnv`'s `alloc 1024` disjunct). -/
theorem realCliMainBinaryKitEnvOf_concrete_send_succ_nonvacuous [LibsignalPlacement]
    (img : Arm64.Obj.Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) :
    ∃ (W₀ : CliHooks) (i₀ : Inputs) (evs : List AllocEvent),
      CliPqxdhInputs ⟨W₀.C, W₀.Q⟩ i₀ ∧
      (∃ peer, parseArgs uuidTryParse (i₀.argv.map bytesOfString) = some (.send peer)) ∧
      SendSuccBinaryKitMainEnv W₀ i₀ evs ∧
      realCliMainBinaryKitEnvOf img S X W₀ i₀ evs ∧
      AllocEvent.alloc 1569 ∈ evs ∧
      AllocEvent.alloc 16 ∈ evs ∧
      AllocEvent.alloc 36 ∈ evs ∧
      AllocEvent.realloc 1 36 72 ∈ evs ∧
      AllocEvent.alloc 8 ∈ evs ∧
      AllocEvent.alloc 1024 ∈ evs := by
  have hScopeIn : scopeIn sendWitnessR0 :=
    ratchetScopeCoversPq_scopeIn_placed W0 sendWitnessP0 sendWitnessX0 sendWitnessG0
      sendWitnessP0_props.2 sendWitnessP0_session_eq
  have hScopeR0 : DeserializeScopeP_Q NonEmptyV1Q sendWitnessR0 :=
    scopeKit_of_scopeIn hScopeIn
  have hKitR0 : scopeKit sendWitnessR0 := hScopeR0
  have hSessCap : (pqSessBytes sendWitnessP0).length ≤ fileCapBytes :=
    pqSessBytes_le_fileCapBytes sendWitnessP0_props.2
  have hSessGet :
      StoresGhost.opened.sessions.get cliIo.rd sendWitnessW1BinParams.x.F
        (addressText (w1EncGhost sendWitnessW1BinParams.x).rem.val) =
        .ok (encodeRecord sendWitnessR0) := by
    change StoresGhost.opened.sessions.get cliIo.rd (runFiles sendWitnessInputs)
      (addressText (addrValOf nonVacSendPeer)) = .ok (encodeRecord sendWitnessR0)
    rw [sendWitnessR0_encode_eq]
    have h := pqSessGet_send W0 sendWitnessP0 [] sendWitnessCoins hSessCap
    rwa [sendWitnessP0_party] at h
  have hScAt :
      (w1SessKitPlaced sendWitnessW1BinParams.repAlloc sendWitnessW1BinParams.B
        sendWitnessW1BinParams.x.F sendWitnessW1BinParams.x.peer).ScopeAt scopeKit
        StoresGhost.opened.sessions (w1EncGhost sendWitnessW1BinParams.x).rem.val sendWitnessR0 := by
    cases henc_eq : encodeRecord sendWitnessR0 with
    | nil => exact absurd henc_eq sendWitnessR0_encode_ne_nil
    | cons bhd btl =>
      exact ⟨hKitR0, bhd :: btl, henc_eq ▸ hSessGet, sendWitnessR0, rfl, henc_eq, hKitR0⟩
  have hPeerGet :
      StoresGhost.opened.identity.peers.get cliIo.rd sendWitnessW1BinParams.x.F
        (w1EncGhost sendWitnessW1BinParams.x).rem.val.name =
        .ok (pqIdBytes sendWitnessP0) := by
    change StoresGhost.opened.identity.peers.get cliIo.rd (runFiles sendWitnessInputs)
      (addrValOf nonVacSendPeer).name = .ok (pqIdBytes sendWitnessP0)
    have h := pqIdGet_send W0 sendWitnessP0 [] sendWitnessCoins
    rwa [sendWitnessP0_party] at h
  let evsAddr : List AllocEvent :=
    [AllocEvent.alloc 36, AllocEvent.realloc 1 36 72, AllocEvent.alloc 8, AllocEvent.free 1 8]
  have hAddrSucc : AddrTextBinarySuccEnv (w1EncGhost sendWitnessW1BinParams.x).rem.val evsAddr :=
    addrTextBinarySuccEnv_nonVacSendPeer
  have hPeersNe : StoresGhost.opened.identity.peers.path ≠ [] := by
    rw [peers_path_eq]; decide
  have hSessNe : StoresGhost.opened.sessions.path ≠ [] := by
    rw [sessions_path_eq]; decide
  let evsGetL : List AllocEvent :=
    pathEvents StoresGhost.opened.sessions.path
      (addressText (w1EncGhost sendWitnessW1BinParams.x).rem.val) ++
      (allocBytes1Events (encodeRecord sendWitnessR0) ++ ([] ++ []))
  have hGetL :
      DirGetMissOkBinarySuccEnv sendWitnessW1BinParams.x.F StoresGhost.opened.sessions
        (addressText (w1EncGhost sendWitnessW1BinParams.x).rem.val)
        (encodeRecord sendWitnessR0) evsGetL :=
    ⟨rfl, hSessGet,
      _, _, rfl, (by unfold DirGetPathEnv; simp only [hSessNe, ↓reduceIte]; rfl),
      _, _, rfl, rfl, [], [], rfl, rfl, rfl⟩
  let evsGetPeer : List AllocEvent :=
    pathEvents StoresGhost.opened.identity.peers.path
      (w1EncGhost sendWitnessW1BinParams.x).rem.val.name ++
      (allocBytes1Events (pqIdBytes sendWitnessP0) ++ ([] ++ []))
  have hGetPeer :
      DirGetMissOkBinarySuccEnv sendWitnessW1BinParams.x.F StoresGhost.opened.identity.peers
        (w1EncGhost sendWitnessW1BinParams.x).rem.val.name
        (pqIdBytes sendWitnessP0) evsGetPeer :=
    ⟨rfl, hPeerGet,
      _, _, rfl, (by unfold DirGetPathEnv; simp only [hPeersNe, ↓reduceIte]; rfl),
      _, _, rfl, rfl, [], [], rfl, rfl, rfl⟩
  let evsPutSv : List AllocEvent :=
    rustAllocEvents (w1EncGhost sendWitnessW1BinParams.x).rem.val.name.length 1 ++
      rawVecGrowEvents 48 4 8 0#64
  have hRemNameNe : (w1EncGhost sendWitnessW1BinParams.x).rem.val.name ≠ [] := by
    have hname : (w1EncGhost sendWitnessW1BinParams.x).rem.val.name =
        succKutf8 (partyAddressName .B) :=
      succ_utf8_eq_kutf8 (partyAddressName .B)
    rw [hname]
    decide
  have hPutSv :
      DirPutStrMissGrowBinarySuccEnv StoresGhost.opened.identity.peers
        (w1EncGhost sendWitnessW1BinParams.x).rem.val.name
        sendWitnessK0.publicKey.serialize evsPutSv :=
    ⟨hRemNameNe, (fun _ h => nomatch h), _, _, rfl, rfl, rfl⟩
  let otr' :=
    otrAfterSome W0.C (pqxdhSpqrModel W0) uuidTryParse
      (w1EncGhost sendWitnessW1BinParams.x) sendWitnessOtr0
  let r' := storedRecord sendWitnessSess0 otr' sendWitnessTaken0
  let encLen' := (lenField 1 (encSessionMem sendWitnessG' sendWitnessSess')).length
  let evsSer : List AllocEvent :=
    segCloneEvents sendWitnessG' sendWitnessSess'.state ++ rustAllocEvents encLen' 1
  have hSer : SerializeSomeNoDropSuccEnv sendWitnessG' sendWitnessSess' evsSer :=
    ⟨_, _, rfl, rfl, rfl⟩
  let evsPutS : List AllocEvent := rawVecGrowEvents 48 4 8 0#64
  have hPutS :
      DirPutMissGrowBinarySuccEnv StoresGhost.opened.sessions
        (addressText (w1EncGhost sendWitnessW1BinParams.x).rem.val)
        (encodeRecord r') evsPutS :=
    ⟨(fun _ h => nomatch h), rfl⟩
  let evsSpqr := rustAllocEvents otr'.pqrState.length 1
  have hSpqrSucc : SpqrSendSuccTightEnv otr'.pqrState.length evsSpqr := by
    dsimp only [evsSpqr, otr']
    rw [sendWitness_otrAfterSome_eq]
    exact spqrSendSuccTightEnv_of_bounds sendWitnessOtr'_pqr_bounds.1 sendWitnessOtr'_pqr_bounds.2
  have hCur' : r'.currentSession = some sendWitnessSess' := by
    dsimp only [r', otr']
    rw [sendWitness_otrAfterSome_eq]
    exact sendWitnessR'_currentSession
  let smGhost :=
    otrSignalMsgGhost W0.C sendWitnessOtr0 sendWitnessSpqrTriple.2.1 sendWitnessSpqrTriple.2.2
      (w1EncGhost sendWitnessW1BinParams.x).ptext
      (some (w1EncGhost sendWitnessW1BinParams.x).loc)
      (w1EncGhost sendWitnessW1BinParams.x).rem
  let pkOutLen :=
    (preKeyMsgFromItems sendWitnessSess0 sendWitnessPpk otr' sendWitnessRealSm).serialized.length
  let evsPkMsg :=
    LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleesBudget.preKeyMsgNewRawEvents
      (pendingKyberPayload sendWitnessSess0) sendWitnessRealSm.serialized.length pkOutLen
  have hPkRaw :
      PreKeyMsgNewRawEnv (pendingKyberPayload sendWitnessSess0)
        sendWitnessRealSm.serialized.length pkOutLen evsPkMsg := rfl
  let evsEnc : List AllocEvent :=
    (rustAllocEvents 24 8 ++
      (evsAddr ++ (evsGetL ++ (sessDeserEvents sendWitnessR0 ++ rustDeallocEvents 24 8)))) ++
    (rustAllocEvents sendWitnessKpk.ciphertext.length 1 ++
      ((evsSpqr ++ (rustAllocEvents 32 1 ++
          (rustAllocEvents (((w1EncGhost sendWitnessW1BinParams.x).ptext.length / 16 + 1) * 16) 1 ++
            signalMessageNewEvents uuidTryParse smGhost))) ++
        (evsPkMsg ++
          ((rustAllocEvents 32 8 ++ (evsGetPeer ++ rustDeallocEvents 32 8)) ++
            ((rustAllocEvents 32 8 ++
                (evsGetPeer ++ (publicKeySerializeEvents ++ (evsPutSv ++ rustDeallocEvents 32 8)))) ++
              (rustAllocEvents 32 1 ++
                (rustAllocEvents 32 8 ++
                  (evsAddr ++ (evsSer ++ (evsPutS ++ rustDeallocEvents 32 8))))))))))
  have hW1Succ : W1SendBinarySuccSlotEnv W0 sendWitnessInputs sendWitnessW1BinParams evsEnc :=
    ⟨rfl, sendWitnessR0, sendWitnessSess0, sendWitnessOtr0, sendWitnessTaken0,
      sendWitnessK0, sendWitnessPpk, sendWitnessKpk,
      sendWitnessSpqrTriple.1, sendWitnessSpqrTriple.2.1, sendWitnessSpqrTriple.2.2,
      sendWitnessRealSm, pqIdBytes sendWitnessP0, sendWitnessG', sendWitnessSess',
      evsAddr, evsGetL, evsSpqr, evsGetPeer, evsGetPeer, evsPutSv,
      evsAddr, evsSer, evsPutS,
      hScAt, hScopeR0, hSessGet, sendWitnessR0_encode_ne_nil,
      sendWitnessR0_currentSession, sendWitnessSess0_fromSessionState_eq,
      sendWitnessTaken0_remoteIdentity_eq, sendWitnessSess0_pendingPreKey_eq,
      sendWitnessSess0_pendingKyber_eq,
      (by rw [sendWitnessKpk_ct_len]; decide),
      sendWitness_spqrSend_eq',
      sendWitness_mutEncrypt_eq',
      hAddrSucc, hGetL,
      hSpqrSucc,
      hPeerGet, hGetPeer, hGetPeer, hPutSv,
      hCur', sendWitnessG'_sessionGhostValid,
      hAddrSucc, hSer, hPutS,
      ⟨_, _, rfl,
        ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, rfl⟩,
        _, _, rfl, rfl,
        _, _, rfl,
        ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, rfl⟩,
        _, _, rfl, hPkRaw,
        _, _, rfl,
        ⟨_, _, rfl, rfl, _, _, rfl, rfl, rfl⟩,
        _, _, rfl,
        ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, rfl⟩,
        _, _, rfl, rfl,
        _, _, rfl, rfl,
        _, _, rfl, rfl,
        _, _, rfl, rfl,
        _, _, rfl, rfl, rfl⟩⟩
  have h1569_kyber : AllocEvent.alloc 1569 ∈ rustAllocEvents sendWitnessKpk.ciphertext.length 1 := by
    rw [sendWitnessKpk_ct_len]
    decide
  have h1569_enc : AllocEvent.alloc 1569 ∈ evsEnc :=
    List.mem_append_right _ (List.mem_append_left _ h1569_kyber)
  have hlen16 : ((w1EncGhost sendWitnessW1BinParams.x).ptext.length / 16 + 1) * 16 = 16 := by decide
  have h16_pt :
      AllocEvent.alloc 16 ∈
        rustAllocEvents (((w1EncGhost sendWitnessW1BinParams.x).ptext.length / 16 + 1) * 16) 1 := by
    rw [hlen16]
    decide
  have h16_enc : AllocEvent.alloc 16 ∈ evsEnc :=
    List.mem_append_right _
      (List.mem_append_right _
        (List.mem_append_left _
          (List.mem_append_right _
            (List.mem_append_right _
              (List.mem_append_left _ h16_pt)))))
  have h36_addr : AllocEvent.alloc 36 ∈ evsAddr := by decide
  have hRealloc_addr : AllocEvent.realloc 1 36 72 ∈ evsAddr := by decide
  have h8_addr : AllocEvent.alloc 8 ∈ evsAddr := by decide
  have h36_enc : AllocEvent.alloc 36 ∈ evsEnc :=
    List.mem_append_left _
      (List.mem_append_right _ (List.mem_append_left _ h36_addr))
  have hRealloc_enc : AllocEvent.realloc 1 36 72 ∈ evsEnc :=
    List.mem_append_left _
      (List.mem_append_right _ (List.mem_append_left _ hRealloc_addr))
  have h8_enc : AllocEvent.alloc 8 ∈ evsEnc :=
    List.mem_append_left _
      (List.mem_append_right _ (List.mem_append_left _ h8_addr))
  have hArgvLen : sendWitnessInputs.argv.length = 2 := rfl
  have hM2 : IterConcatEnv M2CollectStepEnv (List.range sendWitnessInputs.argv.length) [] := by
    rw [hArgvLen]
    exact ⟨[], [], rfl, Or.inl rfl, ⟨[], [], rfl, Or.inl rfl, rfl⟩⟩
  let ownB := CryptoVerification.SignalSession.textBytes (partyAddress .A).text
  let evsR0Get : List AllocEvent :=
    allocBytes1Events (utf8 "address") ++
      (allocBytes1Events ownB ++ ([] ++ []))
  have hR0Get :
      DirGetMissOkBinarySuccEnv (runFiles sendWitnessInputs) StoresGhost.opened.identity.own
        (utf8 "address") ownB evsR0Get :=
    ⟨rfl, sendWitnessOwn_get,
      _, _, rfl, rfl, _, _, rfl, rfl, [], [], rfl, rfl, rfl⟩
  let evsP1 :=
    mkM5EntrySimple StoresGhost.opened.identity.peers.path
      (w1EncGhost sendWitnessW1BinParams.x).rem.val.name
  let evsS1 :=
    mkM5EntrySimple StoresGhost.opened.sessions.path
      (addressText sendWitnessW1BinParams.peer.val)
  let evsM5 := evsP1 ++ evsS1
  have hM5 :
      IterConcatEnv (fun dn => IterConcatEnv (fun name => M5LoopAEntryEnv dn.1 name) dn.2)
        [(StoresGhost.opened.identity.peers.path,
            [(w1EncGhost sendWitnessW1BinParams.x).rem.val.name]),
         (StoresGhost.opened.sessions.path,
            [addressText sendWitnessW1BinParams.peer.val])] evsM5 :=
    ⟨evsP1, evsS1, rfl,
      ⟨evsP1, [], (List.append_nil _).symm, mkM5EntrySimple_mem _ _, rfl⟩,
      ⟨evsS1, [], (List.append_nil _).symm,
        ⟨evsS1, [], (List.append_nil _).symm, mkM5EntrySimple_mem _ _, rfl⟩,
        rfl⟩⟩
  let fullLog : List AllocEvent :=
    (rustAllocEvents (16 * sendWitnessInputs.argv.length) 8 ++
      ([] ++ (addressEvents uuidTryParse sendWitnessAddressCall.bs ++
        (allocBytes1Events sendWitnessInputs.stdin ++ allocBytes1Events sendWitnessCoins.toList)))) ++
    (((evsR0Get ++ (addressEvents uuidTryParse ownB ++ deallocBytes1OfLen ownB.length)) ++
        (evsEnc ++ cliConcat2Events [wirePrekey] sendWitnessBs1)) ++
      (evsM5 ++ rustAllocEvents 1024 1))
  have hSendSucc : SendSuccBinaryKitMainEnv sendWitnessCliHooks sendWitnessInputs fullLog :=
    ⟨sendWitnessP0, [], sendWitnessCoins, sendWitnessSt1,
      sendWitnessX0, sendWitnessX1, sendWitnessG0, sendWitnessG1,
      sendWitnessAddressCall, nonVacSendPeer, sendWitnessW1BinParams,
      sendWitnessCoins.toList, ownB, sendWitnessBs1,
      [], evsR0Get, evsEnc, evsM5,
      sendWitnessP0_props.2,
      sendWitnessP0_session_eq,
      by decide +kernel,
      sendWitness_pqSendModel_eq,
      sendWitnessSt1_session_eq,
      sendWitnessSt1_wf,
      rfl,
      sendWitnessInputs_argv_map,
      sendWitnessAddressCall_parse,
      sendWitnessInputs_parseArgs,
      sendWitnessW1BinParams_dom,
      rfl,
      rfl,
      rfl,
      sendWitnessOwn_parse,
      rfl,
      Nat.zero_le msgCapBytes,
      sendWitnessCoins_readFileResult,
      hM2,
      sendWitnessOwn_get,
      hR0Get,
      hW1Succ,
      sendWitnessBs1_bounds.1,
      sendWitnessBs1_bounds.2,
      hM5,
      h1569_enc,
      h16_enc,
      h36_enc,
      hRealloc_enc,
      h8_enc,
      ⟨_, _, rfl,
        ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, rfl⟩,
        _, _, rfl,
        ⟨_, _, rfl,
          ⟨_, _, rfl, rfl, _, _, rfl, rfl, rfl⟩,
          _, _, rfl, rfl, rfl⟩,
        _, _, rfl, rfl, rfl⟩⟩
  have hMemEnc : ∀ {ev : AllocEvent}, ev ∈ evsEnc → ev ∈ fullLog := fun h =>
    List.mem_append_right _
      (List.mem_append_left _
        (List.mem_append_right _
          (List.mem_append_left _ h)))
  have h1024_full : AllocEvent.alloc 1024 ∈ fullLog := by
    apply List.mem_append_right
    apply List.mem_append_right
    apply List.mem_append_right
    change AllocEvent.alloc 1024 ∈ rustAllocEvents 1024 1
    decide
  exact ⟨sendWitnessCliHooks, sendWitnessInputs, fullLog,
    sendWitnessInputs_cliPqxdh,
    ⟨nonVacSendPeer, sendWitnessInputs_parseArgs⟩,
    hSendSucc,
    sendSuccBinaryKitMainEnv_sub_realCliMainBinaryKitEnvOf img S X sendWitnessCliHooks
      sendWitnessInputs fullLog hSendSucc,
    hMemEnc h1569_enc,
    hMemEnc h16_enc,
    hMemEnc h36_enc,
    hMemEnc hRealloc_enc,
    hMemEnc h8_enc,
    h1024_full⟩

/-- Alias form of `realCliMainBinaryKitEnvOf_concrete_send_succ_nonvacuous` on
`RealCliMainBinaryEnvOf (mkBinaryKitRealCalleeEnvs img S X W₀) i₀`. -/
theorem realCliMainBinaryEnvOf_binaryKit_concrete_send_succ_nonvacuous [LibsignalPlacement]
    (img : Arm64.Obj.Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) :
    ∃ (W₀ : CliHooks) (i₀ : Inputs) (evs : List AllocEvent),
      CliPqxdhInputs ⟨W₀.C, W₀.Q⟩ i₀ ∧
      (∃ peer, parseArgs uuidTryParse (i₀.argv.map bytesOfString) = some (.send peer)) ∧
      SendSuccBinaryKitMainEnv W₀ i₀ evs ∧
      RealCliMainBinaryEnvOf (mkBinaryKitRealCalleeEnvs img S X W₀) i₀ evs ∧
      AllocEvent.alloc 1569 ∈ evs ∧
      AllocEvent.alloc 16 ∈ evs ∧
      AllocEvent.alloc 36 ∈ evs ∧
      AllocEvent.realloc 1 36 72 ∈ evs ∧
      AllocEvent.alloc 8 ∈ evs ∧
      AllocEvent.alloc 1024 ∈ evs :=
  realCliMainBinaryKitEnvOf_concrete_send_succ_nonvacuous img S X

end BinaryKitStageB

end LibsignalBinary.Proofs.PeakBudget.RealMainEnvNonVacSuccSend
