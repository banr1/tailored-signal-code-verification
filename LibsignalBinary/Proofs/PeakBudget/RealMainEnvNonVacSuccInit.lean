/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Process.Semantics
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.ConsumeMessageKey.NonVacProofs.AllocWitness
public import LibsignalBinary.Proofs.ConsumeMessageKey.NonVacProofs.StateWitnessPlaced
public import LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
public import LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith
public import LibsignalBinary.Proofs.PeakBudget.CliMainPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
public import LibsignalBinary.Proofs.PeakBudget.CliRealExistentialCalleeEnvs
public import LibsignalBinary.Proofs.PeakBudget.CliRunArmsPeak
public import LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge
public import LibsignalBinary.Proofs.PeakBudget.RealMainEnvAdapter
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit
public import LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit
public import LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds
public import LibsignalBinary.Proofs.PeakBudget.W3InitiatePeakSpec
public import LibsignalBinary.Proofs.PeakBudget.W3InitiateStagesPeak
public import LibsignalBinary.Proofs.PeakBudget.W3InitiateTightSpec
public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Defs
public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget
public import LibsignalBinary.Proofs.RecordCodecs.DepsBudget
public import LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.AddressText.PlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.Digits
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.CalleesBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R0ProofPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdKeyPairPollPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdRegIdPollPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Bundle
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser
public import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Plumbing
import LibsignalBinary.Proofs.SpecLemmas.FsFold
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Process

/-!
# `init`-Arm Binary-Kit Success-Path Non-Vacuity Witness

Proves that the `.init` CLI arm's binary-kit success path is inhabited in
`realCliMainBinaryKitEnvOf img S X W₀` (`= RealCliMainBinaryEnvOf (mkBinaryKitRealCalleeEnvs img S X W₀)`)
for all `img`, `S`, `X` at the concrete witness `W₀ = succInitCliHooks`:
1. Defines `InitSuccMainEnv` using strict `ConcatEnv` / `IterConcatEnv` composition across `M1..M3`,
   `R0BinSuccEnv`, `R1aBinSuccEnv`, `R1bBinSuccEnv`, `W3InitBinSuccSlotEnv` (Stages 1–5 over the
   binary store-kit polls, including the exact Block 594 `address_text` trace on `Bob.1` and `.ok`
   cache-miss `Dir::get` reads with zero `22`-byte error allocations), and `M5`, tied to
   `pqInitModel X ⟨W.C, W.Q⟩ p₀ b₀ t₀ = some (some (st₁, []))`.
2. Proves `InitSuccMainEnv img W i₀ ⊆ realCliMainBinaryKitEnvOf img S X W i₀`.
3. Exhibits concrete `(W₀, i₀, evs)` satisfying `CliPqxdhInputs ⟨W₀.C, W₀.Q⟩ i₀` and
   `InitSuccMainEnv img W₀ i₀ evs` (non-vacuity is witnessed for `W₀ = succInitCliHooks`; file-read
   witnesses use the hook-model disjunct of `ReadFileRuleEnv`/`ReadFileEnv`, and inner bounded-cost
   stages `IdentityKeyPairTryFromEnv`, `W3BoundedEvs`, and `InitialStateEnv` carry protocol success
   via `pqInitModel`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.RealMainEnvNonVacSuccInit

open Arm64 ProofLib SepProp
open Arm64.Process (bytesOfString initFsState)
open CryptoGames (Party)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (Crypto GhostState IdentityKey PublicKey ShaCompress)
open CryptoGames.LibsignalSessionApi (Session SessionRecord)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.E2E
  (LocalIdentity PEParams PqxdhPrims PreKeyBundleFields ReachablePqxdhSession RecordExtras
   UnreachedPqxdhPrimitives djbKey encodeRecordUnderExtras fitVec initiateState initiateTapeLen
   keyPairOf partyAddressName)
open CryptoVerification.E2E.Record (encodeRecord lenField)
open CryptoVerification.E2E.Record.Serialization (encSessionMem)
open CryptoVerification.LibsignalPublicApi.MessageDecrypt (sessionModelRel)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal RecordGhost)
open CryptoVerification.LibsignalSession.NonVacuityWitness
  (A₀ ValidMemPlaced deserialize_pk0_serialize pk0 pk0_serialize_length
   satisfies_mapFresh_unmapped)
open CryptoVerification.LibsignalSessionRepr
  (chainAt leBytes vecGhostAt)
open CryptoVerification.LibsignalSpqrV1 (ChainParams MlKem)
open CryptoVerification.LibsignalTripleRatchet (reserveCap)
open CryptoVerification.LibsignalTripleRatchetRepr
  (AddrGhost SessionGhost noneCap optSenderChainAt optTailVecAt sessionStateAt uuidTryParse)
open CryptoVerification.RecordCodecs (IdentityKeyPairStructure)
open CryptoVerification.RustHeap (Unmapped vecAt vecBuf vecHeader vecU8At)
open CryptoVerification.SignalSession
  (Address CliHooks CliPqxdhInputs Cmd Inputs PqParty PqxdhPartyInSpecDomain addressFile ancestors
   baseKeysFile bundleDir coinsFile dirsFold encodeDir fileCapBytes filesFold files_eq_entries
   identityFile identityKeyPairFile initFsState_entries le32 partyAddress partyDirs pathComps
   pqInitInputs pqInitModel publicBundleOf registrationIdFile sessionFile stdioPaths textBytes)
open CryptoVerification.SignalSession.Cli
  (DirGhost ReadRule StoresGhost addressText cliInputs decimalText pathOf utf8)
open CryptoVerification.SignalSession.Cli.Decimal.Helpers (decimalText_digit)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddrV AddressCall CallV RunCall addrParse cliIo cliRd parseArgs)
open CryptoVerification.SignalSession.Cli.RunCompose
  (InitGhost RunSem addrValOf bundleFile bundlePath exceptOpt readBundleV runFiles)
open CryptoVerification.SignalSession.Cli.RunProofs (kemPkLen)
open CryptoVerification.SignalSession.Cli.RunRefine
  (bundleVE parseArgs_init readBundleV_pqInit)
open CryptoVerification.SignalSession.Cli.Slots (scopeKit)
open CryptoVerification.SignalSession.CliExt (blockingAncestorF pathStr readFileResult readViewF)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open LibsignalBinary.Heap
  (AllocEvent FreeOnlyEvs SeqEnv rustAllocEvents rustDeallocEvents rustReallocEvents)
open LibsignalBinary.Heap.SpecBudget (ReadFileEnv allocBytes1Events readFileEnv_of_hook)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
  (addressText_length_le dirDomainCaps_opened_peers dirDomainCaps_opened_sess
   opened_peers_path_len opened_sess_path_len)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith
  (cliMaxAddrTextBytes cliMaxDirPathBytes cliMaxDirtyEntries)
open LibsignalBinary.Proofs.PeakBudget.CliMainPeakSpec
  (CliMainSetupEnv M1PhaseEnv M2CollectEnv M3PhaseEnv M5DirStepEnv M5LoopAEntryEnv M5PhaseEnv
   M5WriteStepEnv M6Env)
open LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
  (W3BinaryInitDom W3BinaryInitParams W3InitBinaryKitSlotEnv mkBinaryKitRealCalleeEnvs
   realCliMainBinaryKitEnvOf)
open LibsignalBinary.Proofs.PeakBudget.CliRunArmsPeak
  (R1cEnv)
open LibsignalBinary.Proofs.PeakBudget.CliRunPeakHelpers (deallocBytes1OfLen)
open LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge
  (CliRunBinaryEnv InitArmBinaryCoreEnv InitArmBinaryEnv OptStageEnv R0BinaryEnv R1bBinaryEnv
   R1bDeserStageEnv R1bFileStepEnv RealCliMainBinaryEnvOf RunArmBinaryEnv)
open LibsignalBinary.Proofs.PeakBudget.RealMainEnvAdapter
  (ValidPostSetupWitness cliMainBoundedSetupEnv_of_setup_any)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (ConcatEnv IterConcatEnv)
open LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit (dropClonedSessionEvents)
open LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit
  (RecordSerializeSeqFreeEnv SerializeSomeCancelEnv SerializeSomeSeqFreeEnv
   serializeSomeExactEvents)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (msgCapBytes sessionCapBytes)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds (RecordGhostValid)
open LibsignalBinary.Proofs.PeakBudget.W3InitiatePeakSpec (W3BoxedStoreStepEnv)
open LibsignalBinary.Proofs.PeakBudget.W3InitiateStagesPeak
  (W3BoundedEvs W3InitiateFullEnv W3Stage1Env W3Stage2Env W3Stage4Env W3Stage5Env
   w3BoundedEvs_nil w3InitiateFullEnv_imp_wide)
open LibsignalBinary.Proofs.PeakBudget.W3InitiateTightSpec
  (AliceInitiatedAnyCkBounds RecordAliceInitiatedAnyCkBounds)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget (SessionGhostValid)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (BoxAllocEnv)
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget
  (IdentityKeyPairTryFromEnv IkpPostCleanupEnv IkpSubEnv)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget (RecordDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.AddressText.PlacedBudgetAux
  (addrDecReserveEvents addrDotReserveEvents addrToOwnedEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget
  (DecimalEnv decimalEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a
  (DirGetAfterReadEnv DirGetEnv DirGetErrAllocEnv DirGetMissEnv DirGetPathEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget (PathEnv pathEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux
  (DirPutEnv dirPutTailEnv_miss_nil)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux
  (DirPutStrEnv dirPutStrEnv_of_nonempty)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
  (cliIdentityKitSavePollEnv cliIdentityKitSaveTailEnv cliIdentityKitTrustPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
  (AddrTextValEnv cliSessionKitLoadPollEnv cliSessionKitStorePollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.CalleesBudget
  (AddressEnv addressEnv_events addressEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R0ProofPlacedBudget (PreAfterGetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdKeyPairPollPlacedBudget
  (OptIkpTryFromEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdRegIdPollPlacedBudget
  (OptRegIdMalformedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (ReadFileRuleEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPoll.LayoutPlacedBudget (OptLoadDeserEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser (ofBytesEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget (SpqrBoundedEvs)
open LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget (InitialStateEnv)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (PublicKeySerializeEnv publicKeySerializeEvents)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (segCloneEvents)

/-! ## 1. Binary-Kit Success-Path Envelopes -/

/-- Exact deterministic allocator event list of `M3` `"coins"` read on `i`. -/
def succInitCoinsEvents (i : Inputs) : List AllocEvent :=
  match readFileResult (initFsState (cliInputs i)).files (utf8 "coins") with
  | .ok bs => allocBytes1Events bs
  | .error () => []

/-- Empty-trace `ConcatEnv` seam (`evs = []`) for `DirGetErrAllocEnv` on `.ok _` reads
(`"file could not be read"` is never allocated on `.ok bs`). -/
def DirGetErrOkNilSeamEnv (evs : List AllocEvent) : Prop :=
  evs = []

/-- Cache-miss `.ok` binary `Dir::get` envelope (`Block 589`):
`d.changed = []`, `rd F0 (pathOf d.path name) = .ok bs`, and `ConcatEnv` of `DirGetPathEnv PathEnv`,
`ReadFileRuleEnv`, `DirGetErrOkNilSeamEnv` (`[]`), and `FreeOnlyEvs`. -/
def DirGetCacheMissOkBinEnv (rd : ReadRule) (F0 : FsFiles) (d : DirGhost)
    (name : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  d.changed = [] ∧
  (∃ bs, rd F0 (pathOf d.path name) = .ok bs) ∧
  ConcatEnv (DirGetPathEnv PathEnv d.path name)
    (ConcatEnv (ReadFileRuleEnv rd F0 (pathOf d.path name))
      (ConcatEnv DirGetErrOkNilSeamEnv FreeOnlyEvs)) evs

/-- Exact deterministic allocator trace of Block 594 (`signal_session::stores::address_text`) on
`rem`: `to_owned` ++ `.`-reserve ++ `decimal` ++ decimal-append reserve ++ temporary `decimal`
`Vec<u8>` deallocation (`rustDeallocEvents 8 1` for single-digit device `1#8`). -/
def addrTextExactEvents (rem : AddrVal) : List AllocEvent :=
  addrToOwnedEvents rem.name ++
  (addrDotReserveEvents rem.name ++
    (decimalEvents (rem.device.zeroExtend 32) ++
      (addrDecReserveEvents rem.name rem.device ++ rustDeallocEvents 8 1)))

/-- Success-only Block 594 (`address_text`) `ConcatEnv` envelope (`AddrTextValEnv DecimalEnv`). -/
def AddrTextBinSuccEnv (rem : AddrVal) (evs : List AllocEvent) : Prop :=
  ConcatEnv (· = addrToOwnedEvents rem.name)
    (ConcatEnv (· = addrDotReserveEvents rem.name)
      (ConcatEnv (DecimalEnv (rem.device.zeroExtend 32))
        (ConcatEnv (· = addrDecReserveEvents rem.name rem.device)
          (· = rustDeallocEvents 8 1)))) evs

/-- Binary success-only `R0` (`PreEnv`) envelope: `DirGetCacheMissOkBinEnv` on
`StoresGhost.opened.identity.own` `"address"` followed by `addressEvents` and `FreeOnlyEvs`. -/
def R0BinSuccEnv (g : RunCall) (evs : List AllocEvent) : Prop :=
  ∃ ownB,
    StoresGhost.opened.identity.own.get cliIo.rd (runFiles g.i) (utf8 "address") = .ok ownB ∧
    ConcatEnv
      (DirGetCacheMissOkBinEnv cliIo.rd (runFiles g.i)
        StoresGhost.opened.identity.own (utf8 "address"))
      (ConcatEnv (· = addressEvents uuidTryParse ownB) FreeOnlyEvs) evs

/-- Binary success-only bundle file read step (`PathEnv dir name` ++ `allocBytes1Events bs` ++
`deallocBytes1OfLen bs.length`, with `0` `14`/`22`-byte error allocations). -/
def BundleFileReadBinSuccEnv (rd : ReadRule) (files : FsFiles) (dir name : List (BitVec 8))
    (evs : List AllocEvent) : Prop :=
  dir ≠ [] ∧
  ∃ bs,
    rd files (pathOf dir name) = .ok bs ∧
    ConcatEnv (PathEnv dir name)
      (ConcatEnv (· = allocBytes1Events bs) (· = deallocBytes1OfLen bs.length)) evs

/-- Binary success-only `R1a` (`identity-key` bundle read). -/
def R1aBinSuccEnv (rd : ReadRule) (files : FsFiles) (dir : List (BitVec 8))
    (evs : List AllocEvent) : Prop :=
  BundleFileReadBinSuccEnv rd files dir (utf8 "identity-key") evs

/-- Binary success-only `R1b` Stage-4 signature/Kyber clone step (`64 B` + `kemPkLen` + `64 B`). -/
def R1bDeserBinSuccEnv (evs : List AllocEvent) : Prop :=
  ConcatEnv (· = rustAllocEvents 64 1)
    (ConcatEnv (· = rustAllocEvents kemPkLen 1)
      (ConcatEnv (· = rustAllocEvents 64 1) FreeOnlyEvs)) evs

/-- Binary success-only `R1b` (`registration-id`, `signed-pre-key`, `kyber-pre-key`,
`one-time-pre-key`, and `R1bDeserBinSuccEnv`; on `Ok`, `split_signed` and `split_id` return slice
views into the read buffer without allocating `"malformed file"`). -/
def R1bBinSuccEnv (rd : ReadRule) (files : FsFiles) (dir : List (BitVec 8))
    (evs : List AllocEvent) : Prop :=
  ConcatEnv (BundleFileReadBinSuccEnv rd files dir (utf8 "registration-id"))
    (ConcatEnv (BundleFileReadBinSuccEnv rd files dir (utf8 "signed-pre-key"))
      (ConcatEnv (BundleFileReadBinSuccEnv rd files dir (utf8 "kyber-pre-key"))
        (ConcatEnv (BundleFileReadBinSuccEnv rd files dir (utf8 "one-time-pre-key"))
          R1bDeserBinSuccEnv))) evs

/-- Boxed async store-step `ConcatEnv` wrapper (`boxSz`-byte future allocation ++ `PollSucc` ++
future drop `FreeOnlyEvs`). -/
def W3BoxedStoreBinSuccEnv (boxSz : Nat) (PollSucc : List AllocEvent → Prop)
    (evs : List AllocEvent) : Prop :=
  0 < boxSz ∧
  ConcatEnv (· = rustAllocEvents boxSz 8) (ConcatEnv PollSucc FreeOnlyEvs) evs

/-- Stage 1 `is_trusted_identity` binary success step (`32 B` box + `DirGetCacheMissOkBinEnv` on
`peers` `rem.name`). -/
def W3IdTrustBinSuccEnv (rd : ReadRule) (F0 : FsFiles) (rem : AddrVal)
    (evs : List AllocEvent) : Prop :=
  W3BoxedStoreBinSuccEnv 32
    (ConcatEnv (DirGetCacheMissOkBinEnv rd F0 StoresGhost.opened.identity.peers rem.name)
      FreeOnlyEvs) evs

/-- Stage 1 `load_session` binary success step on `p₀.session = none` (`24 B` box + Block 594
`AddrTextBinSuccEnv rem` + `DirGetCacheMissOkBinEnv` on `sessions` `addressText rem` returning
`.ok []` + `evsDeser = []`). -/
def W3SessLoadBinSuccEnv (rd : ReadRule) (F0 : FsFiles) (rem : AddrVal)
    (evs : List AllocEvent) : Prop :=
  StoresGhost.opened.sessions.get rd F0 (addressText rem) = .ok [] ∧
  W3BoxedStoreBinSuccEnv 24
    (ConcatEnv (AddrTextBinSuccEnv rem)
      (ConcatEnv
        (DirGetCacheMissOkBinEnv rd F0 StoresGhost.opened.sessions (addressText rem))
        (ConcatEnv (· = []) FreeOnlyEvs))) evs

/-- Stage 2 `get_identity_key_pair` binary success step (`16 B` box + `DirGetCacheMissOkBinEnv` on
`own` `"identity-key-pair"` + `IdentityKeyPairTryFromEnv bs.length`). -/
def W3IdKeyPairBinSuccEnv (rd : ReadRule) (F0 : FsFiles) (evs : List AllocEvent) : Prop :=
  ∃ bs,
    StoresGhost.opened.identity.own.get rd F0 (utf8 "identity-key-pair") = .ok bs ∧
    W3BoxedStoreBinSuccEnv 16
      (ConcatEnv
        (DirGetCacheMissOkBinEnv rd F0 StoresGhost.opened.identity.own (utf8 "identity-key-pair"))
        (ConcatEnv (IdentityKeyPairTryFromEnv bs.length) FreeOnlyEvs)) evs

/-- Stage 5 `get_local_registration_id` binary success step (`16 B` box + `DirGetCacheMissOkBinEnv`
on `own` `"registration-id"` with `bs.length = 4` so `OptRegIdMalformedEnv` emits `[]`). -/
def W3IdRegIdBinSuccEnv (rd : ReadRule) (F0 : FsFiles) (evs : List AllocEvent) : Prop :=
  ∃ bs,
    StoresGhost.opened.identity.own.get rd F0 (utf8 "registration-id") = .ok bs ∧
    bs.length = 4 ∧
    W3BoxedStoreBinSuccEnv 16
      (ConcatEnv
        (DirGetCacheMissOkBinEnv rd F0 StoresGhost.opened.identity.own (utf8 "registration-id"))
        (ConcatEnv (· = []) FreeOnlyEvs)) evs

/-- Stage 5 `save_identity` binary success step (`32 B` box + `DirGetCacheMissOkBinEnv` on `peers`
`rem.name` + `PublicKeySerializeEnv` `[.alloc 33]` + `DirPutStrEnv` `to_owned` `[.alloc 36]`). -/
def W3IdSaveBinSuccEnv (rd : ReadRule) (F0 : FsFiles) (rem : AddrVal) (key : IdentityKey)
    (evs : List AllocEvent) : Prop :=
  ∃ bs,
    StoresGhost.opened.identity.peers.get rd F0 rem.name = .ok bs ∧
    rem.name ≠ [] ∧
    W3BoxedStoreBinSuccEnv 32
      (ConcatEnv (DirGetCacheMissOkBinEnv rd F0 StoresGhost.opened.identity.peers rem.name)
        (ConcatEnv FreeOnlyEvs
          (ConcatEnv PublicKeySerializeEnv
            (ConcatEnv (· = rustAllocEvents rem.name.length 1)
              (DirPutEnv StoresGhost.opened.identity.peers rem.name key.serialize))))) evs

/-- Stage 5 `store_session` binary success step (`32 B` box + Block 594 `AddrTextBinSuccEnv rem` +
`SerializeSomeCancelEnv G sess` on `Some` session + `DirPutEnv`). -/
def W3SessStoreBinSuccEnv (rem : AddrVal) (G : SessionGhost)
    (sess : Session (List (BitVec 8))) (r_rec : SessionRecord (List (BitVec 8)))
    (evs : List AllocEvent) : Prop :=
  W3BoxedStoreBinSuccEnv 32
    (ConcatEnv (AddrTextBinSuccEnv rem)
      (ConcatEnv (SerializeSomeCancelEnv G sess)
        (DirPutEnv StoresGhost.opened.sessions (addressText rem) (encodeRecord r_rec)))) evs

/-- Binary-kit 5-stage `W3InitBinaryKitSlotEnv` success-spine envelope (`0` `SeqEnv`):
Stage 1 trusted pass-through (`33 B` + `1569 B` + `W3SessLoadBinSuccEnv`) ++
Stage 2 SegC pass-through (`W3IdKeyPairBinSuccEnv` + `1568 B` Kyber SPK clone) ++
Stage 3 PQXDH + KEM serialize (`W3BoundedEvs 8 1569`, bounded-cost wildcard) ++
Stage 4 `create_chain` + SPQR `.v1` `InitialStateEnv` + `SessionState::new` (bounded-cost wildcards) ++
Stage 5 `KyberPreKeyId::fmt` + `W3IdRegIdBinSuccEnv` + `W3IdSaveBinSuccEnv` +
`W3SessStoreBinSuccEnv` + `FreeOnlyEvs`. -/
def W3InitBinSuccSlotEnv (w : W3BinaryInitParams) (evs : List AllocEvent) : Prop :=
  ∃ (G : SessionGhost) (sess : Session (List (BitVec 8)))
    (evsS1Trust evsS1Load evsS2Kp evsS3
     evsS4Pre evsS4Spqr evsS4Post
     evsS5Pre evsS5Reg evsS5Save evsS5Store : List AllocEvent),
    w.x_spqr.p.version = .v1 ∧
    w.g_rec.cur = some G ∧
    w.r_rec.currentSession = some sess ∧
    evs =
      ((((evsS1Trust ++ (rustAllocEvents 33 1 ++ (rustAllocEvents 1569 1 ++ evsS1Load))) ++
         (evsS2Kp ++ rustAllocEvents 1568 1)) ++
        evsS3) ++
       (evsS4Pre ++ (evsS4Spqr ++ evsS4Post))) ++
      (evsS5Pre ++ (evsS5Reg ++ (evsS5Save ++ evsS5Store))) ∧
    W3IdTrustBinSuccEnv cliIo.rd w.x.F w.x.peer.val evsS1Trust ∧
    W3SessLoadBinSuccEnv cliIo.rd w.x.F w.x.peer.val evsS1Load ∧
    W3IdKeyPairBinSuccEnv cliIo.rd w.x.F evsS2Kp ∧
    W3BoundedEvs 8 1569 evsS3 ∧
    W3BoundedEvs 1 33 evsS4Pre ∧
    InitialStateEnv w.F w.x_spqr evsS4Spqr ∧
    W3BoundedEvs 13 416 evsS4Post ∧
    W3BoundedEvs 4 68 evsS5Pre ∧
    W3IdRegIdBinSuccEnv cliIo.rd w.x.F evsS5Reg ∧
    W3IdSaveBinSuccEnv cliIo.rd w.x.F w.x.peer.val w.peerKey evsS5Save ∧
    W3SessStoreBinSuccEnv w.x.peer.val G sess w.r_rec evsS5Store

/-- Whole-`main` binary-kit `init` success-path envelope: ties `(W, i₀)` to
`pqInitInputs ⟨W.C, W.Q⟩ p₀ b₀ t₀` with `∀ X, pqInitModel X ⟨W.C, W.Q⟩ p₀ b₀ t₀ = some (some (st₁, []))`
(`st₁.session = some (x₁, g₁)`), and composes `M1..M3` ++ `R0BinSuccEnv` ++ `R1aBinSuccEnv` ++
`R1bBinSuccEnv` ++ `W3InitBinSuccSlotEnv` ++ `M5` `IterConcatEnv` without `SeqEnv` early-exit shortcuts. -/
def InitSuccMainEnv [LibsignalPlacement]
    (_img : Arm64.Obj.Image) (W : CliHooks) (i₀ : Inputs) (evs : List AllocEvent) : Prop :=
  ∃ (p₀ : PqParty) (b₀ : PreKeyBundleFields) (t₀ : List.Vector (BitVec 8) initiateTapeLen)
    (st₁ : PqParty) (x₁ : RecordExtras) (g₁ : GhostState (List (BitVec 8)))
    (ag : AddressCall) (g₀ : RunCall) (dir : List (BitVec 8)) (w : W3BinaryInitParams)
    (evsSetup evsR0 evs1a evs1b evs1c evsM5 : List AllocEvent),
    PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ p₀ ∧
    p₀.session = none ∧
    i₀ = pqInitInputs ⟨W.C, W.Q⟩ p₀ b₀ t₀ ∧
    st₁.session = some (x₁, g₁) ∧
    PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st₁ ∧
    (∀ X : UnreachedPqxdhPrimitives,
      pqInitModel X ⟨W.C, W.Q⟩ p₀ b₀ t₀ = some (some (st₁, []))) ∧
    ag.bs = bytesOfString (partyAddress p₀.party.other).text ∧
    addrParse uuidTryParse ag.bs = some ⟨w.x.peer.name.bytes, w.x.peer.device⟩ ∧
    g₀.i = i₀ ∧
    parseArgs uuidTryParse (i₀.argv.map bytesOfString) = some g₀.c ∧
    g₀.c = .init ⟨w.x.peer.name.bytes, w.x.peer.device⟩ dir ∧
    w.x.peer.name.bytes = utf8 (partyAddressName p₀.party.other) ∧
    w.x.peer.device = 1#8 ∧
    w.x.me.name.bytes = utf8 (partyAddressName p₀.party) ∧
    w.x.me.device = 1#8 ∧
    w.x.F = runFiles i₀ ∧
    w.x.coins = t₀.toList ∧
    w.x.bundle = bundleVE b₀ ∧
    w.peerKey = ⟨⟨b₀.idPub⟩⟩ ∧
    evsSetup = addressEvents uuidTryParse ag.bs ++ succInitCoinsEvents i₀ ∧
    succInitCoinsEvents i₀ ≠ [] ∧
    evs = evsSetup ++ ((evsR0 ++ ((evs1a ++ evs1b) ++ evs1c)) ++ evsM5) ∧
    CliMainSetupEnv uuidTryParse i₀ (some ag) false evsSetup ∧
    R0BinSuccEnv g₀ evsR0 ∧
    R1aBinSuccEnv cliIo.rd (runFiles i₀) dir evs1a ∧
    R1bBinSuccEnv cliIo.rd (runFiles i₀) dir evs1b ∧
    W3BinaryInitDom g₀.c i₀ w ∧
    W3InitBinSuccSlotEnv w evs1c ∧
    IterConcatEnv (fun dn => IterConcatEnv (fun name => M5LoopAEntryEnv dn.1 name) dn.2)
      [(StoresGhost.opened.identity.peers.path, [w.x.peer.val.name]),
       (StoresGhost.opened.sessions.path, [addressText w.x.peer.val])] evsM5 ∧
    List.Sublist (addrTextExactEvents w.x.peer.val) evs1c ∧
    AllocEvent.alloc 1569 ∈ evs1c ∧
    AllocEvent.alloc 3700 ∈ evs1c ∧
    AllocEvent.alloc 416 ∈ evs1c

/-! ## 2. Inclusion into `realCliMainBinaryKitEnvOf` and `RealCliMainBinaryEnvOf` -/

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

private theorem succ_repr_utf8_eq_kutf8 (s : String) :
    CryptoVerification.LibsignalTripleRatchetRepr.utf8 s = succKutf8 s := by
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  simp [CryptoVerification.LibsignalTripleRatchetRepr.utf8, succKutf8, List.utf8Encode,
    succ_byteArray_toList_eq_data]

private theorem succ_addrParse_bytesOfString (P : Party) :
    addrParse uuidTryParse (bytesOfString (partyAddress P).text) =
      some ⟨utf8 (partyAddressName P), 1#8⟩ := by
  have hp := parseArgs_init P ""
  have hi : bytesOfString "init" = utf8 "init" := by
    unfold bytesOfString
    rw [succ_utf8_eq_kutf8]
    rfl
  have hk : utf8 "init" ≠ utf8 "keygen" := by
    rw [succ_utf8_eq_kutf8, succ_utf8_eq_kutf8]
    decide
  simp only [Cmd.argv, List.map_cons, List.map_nil, parseArgs, hi, hk, ↓reduceIte] at hp
  cases ha : addrParse uuidTryParse (bytesOfString (partyAddress P).text) with
  | none =>
    rw [ha] at hp
    cases hp
  | some a =>
    rw [ha] at hp
    injection hp with hp'
    injection hp' with hp1 _
    exact congrArg some hp1

private theorem succInitCoinsEvents_readFileEnv (i : Inputs) :
    ReadFileEnv (initFsState (cliInputs i)).files (utf8 "coins") (succInitCoinsEvents i) := by
  refine readFileEnv_of_hook (initFsState (cliInputs i)).files (utf8 "coins") ?_
  unfold succInitCoinsEvents
  cases readFileResult (initFsState (cliInputs i)).files (utf8 "coins") with
  | ok _ => rfl
  | error u => cases u; rfl

/-- Whenever `rd F0 pth = .ok bs`, `DirGetErrAllocEnv rd F0 pth` is equivalent to
`DirGetErrOkNilSeamEnv` (`evs = []`). -/
theorem dirGetErrAllocEnv_eq_nil_of_ok {rd : ReadRule} {F0 : FsFiles}
    {pth bs : List (BitVec 8)} {evs : List AllocEvent}
    (hok : rd F0 pth = .ok bs) :
    DirGetErrAllocEnv rd F0 pth evs ↔ DirGetErrOkNilSeamEnv evs := by
  unfold DirGetErrAllocEnv DirGetErrOkNilSeamEnv
  rw [hok]

private theorem dirGetEnv_of_cacheMissOkBin {rd : ReadRule} {F0 : FsFiles} {d : DirGhost}
    {name : List (BitVec 8)} {evs : List AllocEvent}
    (h : DirGetCacheMissOkBinEnv rd F0 d name evs) :
    DirGetEnv PathEnv (ReadFileRuleEnv rd) rd F0 d name evs := by
  obtain ⟨hch, ⟨bs, hok⟩, evsP, evsRest, rfl, hP, evsR, evsAfter, rfl, hR,
    evsErr, evsFree, rfl, hSeam, hFree⟩ := h
  unfold DirGetEnv
  rw [hch]
  dsimp only [List.find?]
  have hErr : DirGetErrAllocEnv rd F0 (pathOf d.path name) evsErr :=
    (dirGetErrAllocEnv_eq_nil_of_ok hok).mpr hSeam
  have hAfter : DirGetAfterReadEnv rd F0 (pathOf d.path name) (evsErr ++ evsFree) :=
    Or.inr ⟨evsErr, evsFree, rfl, hErr, hFree⟩
  exact Or.inr ⟨evsP, evsR ++ (evsErr ++ evsFree), rfl, hP,
    Or.inr ⟨evsR, evsErr ++ evsFree, rfl, hR, hAfter⟩⟩

private theorem addrTextValEnv_of_binSucc {rem : AddrVal} {evs : List AllocEvent}
    (h : AddrTextBinSuccEnv rem evs) :
    AddrTextValEnv DecimalEnv rem evs := by
  obtain ⟨e1, _, rfl, h1, e2, _, rfl, h2, e3, _, rfl, h3, e4, e5, rfl, h4, h5⟩ := h
  have hf5 : FreeOnlyEvs e5 := h5 ▸ FreeOnlyEvs.singleton 1 8
  exact Or.inr ⟨e1, _, rfl, h1,
    Or.inr ⟨e2, _, rfl, h2,
      Or.inr ⟨e3, _, rfl, h3,
        Or.inr ⟨e4, e5, rfl, h4, hf5⟩⟩⟩⟩

private theorem r0BinaryEnv_of_binSucc {g : RunCall} {evs : List AllocEvent}
    (h : R0BinSuccEnv g evs) :
    R0BinaryEnv cliIo.rd g evs := by
  obtain ⟨ownB, hown, evsGet, evsPost, rfl, hGet, eAddr, eFree, rfl, hAddr, hFree⟩ := h
  have hPre : PreAfterGetEnv g (eAddr ++ eFree) := by
    unfold PreAfterGetEnv
    rw [hown]
    exact Or.inr ⟨eAddr, eFree, rfl, hAddr, hFree⟩
  exact Or.inr <| Or.inr ⟨evsGet, eAddr ++ eFree, rfl, dirGetEnv_of_cacheMissOkBin hGet, hPre⟩

private theorem freeOnlyEvs_deallocBytes1OfLen (n : Nat) :
    FreeOnlyEvs (deallocBytes1OfLen n) := by
  unfold deallocBytes1OfLen
  split
  · exact FreeOnlyEvs.nil
  · exact FreeOnlyEvs.singleton 1 n

private theorem r1bFileStepEnv_of_binSucc {rd : ReadRule} {files : FsFiles}
    {dir name : List (BitVec 8)} {evs : List AllocEvent}
    (h : BundleFileReadBinSuccEnv rd files dir name evs) :
    R1bFileStepEnv rd files dir name evs := by
  obtain ⟨hne, bs, hrd, ePath, eRest, rfl, hPath, eRead, eDealloc, rfl, rfl, rfl⟩ := h
  have hslash : utf8 "/" = [0x2f#8] := by rw [succ_utf8_eq_kutf8]; rfl
  have hpth : pathOf dir name = dir ++ [0x2f#8] ++ name := by
    unfold pathOf
    simp only [hne, ↓reduceIte, hslash, List.append_assoc]
  rw [hpth] at hrd
  have hRead : ReadFileRuleEnv rd files (dir ++ [0x2f#8] ++ name) (allocBytes1Events bs) := by
    unfold ReadFileRuleEnv
    rw [hrd]
    exact Or.inl rfl
  have hDealloc : FreeOnlyEvs (deallocBytes1OfLen bs.length) :=
    freeOnlyEvs_deallocBytes1OfLen bs.length
  exact Or.inr ⟨ePath, allocBytes1Events bs ++ deallocBytes1OfLen bs.length, rfl,
    Or.inr hPath,
    Or.inr ⟨allocBytes1Events bs, deallocBytes1OfLen bs.length, rfl,
      Or.inr hRead,
      Or.inl hDealloc⟩⟩

private theorem r1bDeserStageEnv_of_binSucc {evs : List AllocEvent}
    (h : R1bDeserBinSuccEnv evs) :
    R1bDeserStageEnv evs := by
  obtain ⟨e1, _, rfl, h1, e2, _, rfl, h2, e3, e4, rfl, h3, h4⟩ := h
  exact Or.inr ⟨e1, _, rfl, Or.inr h1,
    Or.inr ⟨e2, _, rfl, Or.inr h2,
      Or.inr (Or.inr ⟨e3, e4, rfl, h3, h4⟩)⟩⟩

private theorem r1bBinaryEnv_of_binSucc {rd : ReadRule} {files : FsFiles}
    {dir : List (BitVec 8)} {evs : List AllocEvent}
    (h : R1bBinSuccEnv rd files dir evs) :
    R1bBinaryEnv rd files dir evs := by
  obtain ⟨eReg, _, rfl, hReg, eSpk, _, rfl, hSpk, eKpk, _, rfl, hKpk,
    eOpk, eDeser, rfl, hOpk, hDeser⟩ := h
  let r3 := eOpk ++ eDeser
  let r2 := eKpk ++ r3
  let r1 := eSpk ++ r2
  exact Or.inr ⟨eReg, r1, rfl, r1bFileStepEnv_of_binSucc hReg,
    Or.inr ⟨eSpk, r2, rfl, Or.inr (r1bFileStepEnv_of_binSucc hSpk),
      Or.inr ⟨[], r2, List.nil_append r2, Or.inl FreeOnlyEvs.nil,
        Or.inr ⟨eKpk, r3, rfl, Or.inr (r1bFileStepEnv_of_binSucc hKpk),
          Or.inr ⟨[], r3, List.nil_append r3, Or.inl FreeOnlyEvs.nil,
            Or.inr ⟨eOpk, eDeser, rfl, Or.inr (r1bFileStepEnv_of_binSucc hOpk),
              Or.inr ⟨[], eDeser, List.nil_append eDeser, Or.inl FreeOnlyEvs.nil,
                Or.inr (r1bDeserStageEnv_of_binSucc hDeser)⟩⟩⟩⟩⟩⟩⟩

private theorem w3BoxedStoreStepEnv_of_binSucc {boxSz : Nat}
    {PollSucc PollEnv : List AllocEvent → Prop} {evs : List AllocEvent}
    (hSub : ∀ e, PollSucc e → PollEnv e)
    (h : W3BoxedStoreBinSuccEnv boxSz PollSucc evs) :
    W3BoxedStoreStepEnv boxSz PollEnv evs := by
  obtain ⟨hpos, eBox, eRest, rfl, rfl, ePoll, eFree, rfl, hPoll, hFree⟩ := h
  have hBox : BoxAllocEnv boxSz (rustAllocEvents boxSz 8) := Or.inr ⟨hpos, rfl⟩
  exact Or.inr ⟨rustAllocEvents boxSz 8, ePoll ++ eFree, rfl, hBox,
    Or.inr ⟨ePoll, eFree, rfl, hSub ePoll hPoll, hFree⟩⟩

private theorem freeOnlyEvs_append {a b : List AllocEvent}
    (ha : FreeOnlyEvs a) (hb : FreeOnlyEvs b) : FreeOnlyEvs (a ++ b) := by
  intro ev hev
  rcases List.mem_append.mp hev with h1 | h2
  · exact ha ev h1
  · exact hb ev h2

private theorem freeOnlyEvs_condDealloc {p : Prop} {d : Decidable p} {sz al : Nat} :
    FreeOnlyEvs (@ite _ p d [] (rustDeallocEvents sz al)) := by
  cases d
  · exact FreeOnlyEvs.singleton al sz
  · exact FreeOnlyEvs.nil

private theorem freeOnlyEvs_flatMap {α : Type} {f : α → List AllocEvent} {xs : List α}
    (hf : ∀ x ∈ xs, FreeOnlyEvs (f x)) : FreeOnlyEvs (xs.flatMap f) := by
  induction xs with
  | nil => exact FreeOnlyEvs.nil
  | cons x xs ih =>
    simp only [List.flatMap_cons]
    exact freeOnlyEvs_append (hf x List.mem_cons_self)
      (ih fun y hy => hf y (List.mem_cons_of_mem x hy))

private theorem freeOnlyEvs_dropClonedMessageKeysEvents
    (mks : List CryptoGames.LibsignalSession.MessageKeyGenerator) :
    FreeOnlyEvs (SessionCloneCredit.dropClonedMessageKeysEvents mks) := by
  unfold SessionCloneCredit.dropClonedMessageKeysEvents
  split
  · exact FreeOnlyEvs.nil
  · exact freeOnlyEvs_append
      (freeOnlyEvs_flatMap fun mkg _ => freeOnlyEvs_condDealloc)
      (FreeOnlyEvs.singleton 8 _)

private theorem freeOnlyEvs_dropClonedChainEvents
    (gc : CryptoVerification.LibsignalSessionRepr.ChainGhost ×
      CryptoGames.LibsignalSession.ReceiverChain) :
    FreeOnlyEvs (SessionCloneCredit.dropClonedChainEvents gc) := by
  unfold SessionCloneCredit.dropClonedChainEvents
  refine freeOnlyEvs_append
    (freeOnlyEvs_append
      (freeOnlyEvs_append freeOnlyEvs_condDealloc freeOnlyEvs_condDealloc)
      ?_)
    (freeOnlyEvs_dropClonedMessageKeysEvents gc.2.messageKeys)
  cases gc.2.chainKey with
  | none => exact FreeOnlyEvs.nil
  | some _ => exact FreeOnlyEvs.singleton 1 32

private theorem freeOnlyEvs_dropClonedSessionEvents (G : SessionGhost)
    (st : CryptoGames.LibsignalSession.SessionState (List (BitVec 8))) :
    FreeOnlyEvs (dropClonedSessionEvents G st) := by
  unfold dropClonedSessionEvents
  refine freeOnlyEvs_append ?_ freeOnlyEvs_condDealloc
  refine freeOnlyEvs_append ?_ freeOnlyEvs_condDealloc
  refine freeOnlyEvs_append ?_ ?_
  · refine freeOnlyEvs_append ?_ freeOnlyEvs_condDealloc
    refine freeOnlyEvs_append ?_ freeOnlyEvs_condDealloc
    refine freeOnlyEvs_append ?_ ?_
    · exact freeOnlyEvs_append
        (freeOnlyEvs_append freeOnlyEvs_condDealloc freeOnlyEvs_condDealloc)
        (FreeOnlyEvs.singleton 1 32)
    · split
      · exact FreeOnlyEvs.nil
      · exact freeOnlyEvs_append
          (freeOnlyEvs_flatMap fun gc _ => freeOnlyEvs_dropClonedChainEvents gc)
          (FreeOnlyEvs.singleton 8 _)
  · cases G.sender <;> cases st.senderChain
    · exact FreeOnlyEvs.nil
    · exact FreeOnlyEvs.nil
    · exact FreeOnlyEvs.nil
    · exact freeOnlyEvs_dropClonedChainEvents _

private theorem serializeSomeSeqFreeEnv_of_cancel {G : SessionGhost}
    {sess : Session (List (BitVec 8))} {evs : List AllocEvent}
    (h : SerializeSomeCancelEnv G sess evs) :
    SerializeSomeSeqFreeEnv G sess evs := by
  obtain ⟨e12, eDrop, rfl, ⟨eClone, eOut, rfl, hClone, hOut⟩, rfl⟩ := h
  rw [List.append_assoc]
  exact Or.inr ⟨eClone, eOut ++ dropClonedSessionEvents G sess.state, rfl, hClone,
    Or.inr ⟨eOut, dropClonedSessionEvents G sess.state, rfl, hOut,
      freeOnlyEvs_dropClonedSessionEvents G sess.state⟩⟩

private theorem w3IdTrustStep_of_binSucc {F0 : FsFiles} {rem : AddrVal}
    {key : IdentityKey} {evs : List AllocEvent}
    (h : W3IdTrustBinSuccEnv cliIo.rd F0 rem evs) :
    W3BoxedStoreStepEnv 32
      (cliIdentityKitTrustPollEnv
        (DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd)
        F0 StoresGhost.opened.identity rem key .sending) evs := by
  refine w3BoxedStoreStepEnv_of_binSucc (fun _ hp => ?_) h
  obtain ⟨eGet, eFree, rfl, hGet, hFree⟩ := hp
  exact Or.inr ⟨eGet, eFree, rfl, dirGetEnv_of_cacheMissOkBin hGet, hFree⟩

private theorem w3SessLoadStep_of_binSucc
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {F0 : FsFiles} {rem : AddrVal} {evs : List AllocEvent}
    (h : W3SessLoadBinSuccEnv cliIo.rd F0 rem evs) :
    W3BoxedStoreStepEnv 24
      (cliSessionKitLoadPollEnv cliIo.rd Scope
        (AddrTextValEnv DecimalEnv)
        (DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd)
        DeserEnv F0 StoresGhost.opened.sessions rem) evs := by
  obtain ⟨hget, hBox⟩ := h
  refine w3BoxedStoreStepEnv_of_binSucc (fun _ hp => ?_) hBox
  obtain ⟨eAddr, r1, rfl, hAddr, eGet, r2, rfl, hGet, eDeser, eFree, rfl, rfl, hFree⟩ := hp
  have hDeser : OptLoadDeserEnv Scope DeserEnv
      (StoresGhost.opened.sessions.get cliIo.rd F0 (addressText rem)) [] := by
    rw [hget]
    rfl
  exact Or.inr ⟨eAddr, eGet ++ ([] ++ eFree), rfl, addrTextValEnv_of_binSucc hAddr,
    Or.inr ⟨eGet, [] ++ eFree, rfl, dirGetEnv_of_cacheMissOkBin hGet,
      Or.inr ⟨[], eFree, rfl, hDeser, hFree⟩⟩⟩

private theorem w3IdKeyPairStep_of_binSucc {F0 : FsFiles} {evs : List AllocEvent}
    (h : W3IdKeyPairBinSuccEnv cliIo.rd F0 evs) :
    W3BoxedStoreStepEnv 16
      (SeqEnv
        (DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd
          F0 StoresGhost.opened.identity.own (utf8 "identity-key-pair"))
        (SeqEnv
          (OptIkpTryFromEnv
            (StoresGhost.opened.identity.own.get cliIo.rd F0 (utf8 "identity-key-pair")))
          FreeOnlyEvs)) evs := by
  obtain ⟨bs, hget, hBox⟩ := h
  refine w3BoxedStoreStepEnv_of_binSucc (fun _ hp => ?_) hBox
  obtain ⟨eGet, r1, rfl, hGet, eIkp, eFree, rfl, hIkp, hFree⟩ := hp
  have hOpt : OptIkpTryFromEnv
      (StoresGhost.opened.identity.own.get cliIo.rd F0 (utf8 "identity-key-pair")) eIkp := by
    unfold OptIkpTryFromEnv
    rw [hget]
    exact hIkp
  exact Or.inr ⟨eGet, eIkp ++ eFree, rfl, dirGetEnv_of_cacheMissOkBin hGet,
    Or.inr ⟨eIkp, eFree, rfl, hOpt, hFree⟩⟩

private theorem w3IdRegIdStep_of_binSucc {F0 : FsFiles} {evs : List AllocEvent}
    (h : W3IdRegIdBinSuccEnv cliIo.rd F0 evs) :
    W3BoxedStoreStepEnv 16
      (SeqEnv
        (DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd
          F0 StoresGhost.opened.identity.own (utf8 "registration-id"))
        (SeqEnv
          (OptRegIdMalformedEnv
            (StoresGhost.opened.identity.own.get cliIo.rd F0 (utf8 "registration-id")))
          FreeOnlyEvs)) evs := by
  obtain ⟨bs, hget, hlen4, hBox⟩ := h
  refine w3BoxedStoreStepEnv_of_binSucc (fun _ hp => ?_) hBox
  obtain ⟨eGet, r1, rfl, hGet, eMal, eFree, rfl, rfl, hFree⟩ := hp
  have hOpt : OptRegIdMalformedEnv
      (StoresGhost.opened.identity.own.get cliIo.rd F0 (utf8 "registration-id")) [] := by
    unfold OptRegIdMalformedEnv
    rw [hget]
    simp only [hlen4, ↓reduceIte]
  exact Or.inr ⟨eGet, [] ++ eFree, rfl, dirGetEnv_of_cacheMissOkBin hGet,
    Or.inr ⟨[], eFree, rfl, hOpt, hFree⟩⟩

private theorem w3IdSaveStep_of_binSucc {F0 : FsFiles} {rem : AddrVal}
    {key : IdentityKey} {evs : List AllocEvent}
    (h : W3IdSaveBinSuccEnv cliIo.rd F0 rem key evs) :
    W3BoxedStoreStepEnv 32
      (cliIdentityKitSavePollEnv cliIo.rd
        (DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd)
        DirPutStrEnv F0 StoresGhost.opened.identity rem key) evs := by
  obtain ⟨bs, hget, hne, hBox⟩ := h
  refine w3BoxedStoreStepEnv_of_binSucc (fun _ hp => ?_) hBox
  obtain ⟨eGet, r1, rfl, hGet, eFree, r2, rfl, hFree, ePk, r3, rfl, hPk,
    eOwn, ePut, rfl, rfl, hPut⟩ := hp
  have hPutStr : DirPutStrEnv StoresGhost.opened.identity.peers rem.name key.serialize
      (rustAllocEvents rem.name.length 1 ++ ePut) :=
    dirPutStrEnv_of_nonempty hne hPut
  have hTail : cliIdentityKitSaveTailEnv DirPutStrEnv StoresGhost.opened.identity rem key
      (StoresGhost.opened.identity.peers.get cliIo.rd F0 rem.name)
      (eFree ++ (ePk ++ (rustAllocEvents rem.name.length 1 ++ ePut))) := by
    unfold cliIdentityKitSaveTailEnv
    rw [hget]
    exact Or.inr ⟨eFree, ePk ++ (rustAllocEvents rem.name.length 1 ++ ePut), rfl, hFree,
      Or.inr ⟨ePk, rustAllocEvents rem.name.length 1 ++ ePut, rfl, hPk, hPutStr⟩⟩
  exact Or.inr ⟨eGet, eFree ++ (ePk ++ (rustAllocEvents rem.name.length 1 ++ ePut)), rfl,
    dirGetEnv_of_cacheMissOkBin hGet, hTail⟩

private theorem w3SessStoreStep_of_binSucc {rem : AddrVal}
    {g_rec : RecordGhost} {r_rec : SessionRecord (List (BitVec 8))}
    {G : SessionGhost} {sess : Session (List (BitVec 8))} {evs : List AllocEvent}
    (hg : g_rec.cur = some G) (hr : r_rec.currentSession = some sess)
    (h : W3SessStoreBinSuccEnv rem G sess r_rec evs) :
    W3BoxedStoreStepEnv 32
      (cliSessionKitStorePollEnv
        (AddrTextValEnv DecimalEnv)
        (RecordSerializeSeqFreeEnv g_rec)
        DirPutEnv StoresGhost.opened.sessions rem r_rec) evs := by
  refine w3BoxedStoreStepEnv_of_binSucc (fun _ hp => ?_) h
  obtain ⟨eAddr, r1, rfl, hAddr, eSer, ePut, rfl, hSer, hPut⟩ := hp
  have hSerSeq : RecordSerializeSeqFreeEnv g_rec r_rec eSer := by
    unfold RecordSerializeSeqFreeEnv
    rw [hg, hr]
    exact serializeSomeSeqFreeEnv_of_cancel hSer
  exact Or.inr ⟨eAddr, eSer ++ ePut, rfl, addrTextValEnv_of_binSucc hAddr,
    Or.inr ⟨eSer, ePut, rfl, hSerSeq, hPut⟩⟩

private theorem w3InitBinaryKitSlotEnv_of_binSucc {w : W3BinaryInitParams} {evs : List AllocEvent}
    (h : W3InitBinSuccSlotEnv w evs) :
    W3InitBinaryKitSlotEnv w evs := by
  obtain ⟨G, sess,
    evsS1Trust, evsS1Load, evsS2Kp, evsS3,
    evsS4Pre, evsS4Spqr, evsS4Post,
    evsS5Pre, evsS5Reg, evsS5Save, evsS5Store,
    _hv1, hg, hr, rfl,
    hS1Trust, hS1Load, hS2Kp, hS3, hS4Pre, hS4Spqr, hS4Post,
    hS5Pre, hS5Reg, hS5Save, hS5Store⟩ := h
  have hStage1 : W3Stage1Env _ _ w.x.peer.name.bytes.length
      (evsS1Trust ++ (rustAllocEvents 33 1 ++ (rustAllocEvents 1569 1 ++ evsS1Load))) :=
    Or.inr ⟨evsS1Trust, rustAllocEvents 33 1 ++ (rustAllocEvents 1569 1 ++ evsS1Load), rfl,
      w3IdTrustStep_of_binSucc (key := w.peerKey) hS1Trust,
      Or.inr (Or.inr ⟨rustAllocEvents 33 1, rustAllocEvents 1569 1 ++ evsS1Load, rfl, rfl,
        Or.inr ⟨[], rustAllocEvents 1569 1 ++ evsS1Load, List.nil_append _, FreeOnlyEvs.nil,
          Or.inr ⟨rustAllocEvents 1569 1, evsS1Load, rfl, rfl,
            Or.inr ⟨[], evsS1Load, List.nil_append _, FreeOnlyEvs.nil,
              w3SessLoadStep_of_binSucc (Scope := scopeKit)
                (DeserEnv := ofBytesEnv RecordDeserializeCancelEnv) hS1Load⟩⟩⟩⟩)⟩
  have hStage2 : W3Stage2Env _ (evsS2Kp ++ rustAllocEvents 1568 1) :=
    Or.inr ⟨evsS2Kp, rustAllocEvents 1568 1, rfl, w3IdKeyPairStep_of_binSucc hS2Kp,
      Or.inr (Or.inr rfl)⟩
  have hStage4 : W3Stage4Env _ (evsS4Pre ++ (evsS4Spqr ++ evsS4Post)) :=
    Or.inr ⟨evsS4Pre, evsS4Spqr ++ evsS4Post, rfl, hS4Pre,
      Or.inr ⟨evsS4Spqr, evsS4Post, rfl, hS4Spqr, hS4Post⟩⟩
  have hStage5 : W3Stage5Env _ _ _
      (evsS5Pre ++ (evsS5Reg ++ (evsS5Save ++ evsS5Store))) :=
    Or.inr ⟨evsS5Pre, evsS5Reg ++ (evsS5Save ++ evsS5Store), rfl, hS5Pre,
      Or.inr ⟨evsS5Reg, evsS5Save ++ evsS5Store, rfl, w3IdRegIdStep_of_binSucc hS5Reg,
        Or.inr ⟨evsS5Save, evsS5Store, rfl, w3IdSaveStep_of_binSucc hS5Save,
          Or.inl (w3SessStoreStep_of_binSucc hg hr hS5Store)⟩⟩⟩
  exact w3InitiateFullEnv_imp_wide
    (Or.inr ⟨_, _, rfl,
      Or.inr ⟨_, _, rfl,
        Or.inr ⟨_, _, rfl,
          Or.inr ⟨_, _, rfl, hStage1, hStage2⟩,
          hS3⟩,
        hStage4⟩,
      hStage5⟩)

private theorem m5PhaseEnv_of_iterConcat_two
    {dir₁ dir₂ name₁ name₂ : List (BitVec 8)} {evs : List AllocEvent}
    (hne₁ : dir₁ ≠ []) (hne₂ : dir₂ ≠ [])
    (h : IterConcatEnv (fun dn => IterConcatEnv (fun name => M5LoopAEntryEnv dn.1 name) dn.2)
      [(dir₁, [name₁]), (dir₂, [name₂])] evs) :
    M5PhaseEnv [(dir₁, [name₁]), (dir₂, [name₂])] evs := by
  obtain ⟨e1, eRest, rfl, ⟨e1a, e1b, rfl, hm1, rfl⟩,
    ⟨e2, eNil, rfl, ⟨e2a, e2b, rfl, hm2, rfl⟩, rfl⟩⟩ := h
  simp only [List.append_nil]
  have hw1 : M5WriteStepEnv (dir₁, name₁) e1a := by
    unfold M5WriteStepEnv; simp only [hne₁, ↓reduceIte]; exact hm1
  have hw2 : M5WriteStepEnv (dir₂, name₂) e2a := by
    unfold M5WriteStepEnv; simp only [hne₂, ↓reduceIte]; exact hm2
  have hd1 : M5DirStepEnv dir₁ [name₁] e1a := Or.inl (Or.inl hw1)
  have hd2 : M5DirStepEnv dir₂ [name₂] e2a := Or.inl (Or.inl hw2)
  exact Or.inl (Or.inr ⟨e1a, e2a, rfl, hd1, Or.inl hd2⟩)

/-- Inclusion of `InitSuccMainEnv` into
`RealCliMainBinaryEnvOf (mkBinaryKitRealCalleeEnvs img S X W') i₀` for arbitrary `W' : CliHooks`
(`initEnv` does not inspect `W'`). -/
theorem initSuccMainEnv_sub_realCliMainBinaryEnvOf_anyW [LibsignalPlacement]
    (img : Arm64.Obj.Image) (S : RunSem) (X : UnreachedPqxdhPrimitives)
    (W W' : CliHooks) (i₀ : Inputs) (evs : List AllocEvent)
    (hSucc : InitSuccMainEnv img W i₀ evs) :
    RealCliMainBinaryEnvOf (mkBinaryKitRealCalleeEnvs img S X W') i₀ evs := by
  obtain ⟨_p₀, _b₀, _t₀, _st₁, _x₁, _g₁, ag, g₀, dir, w,
    evsSetup, evsR0, evs1a, evs1b, evs1c, evsM5,
    _, _, hi_eq, _, _, _, _, _, hg_i, hparse, hgc,
    _, _, _, _, _, _, _, _,
    _, _, rfl, hSetup, hR0, h1a, h1b, hDom, hSlot, hM5, _, _, _, _⟩ := hSucc
  have hBSetup :=
    cliMainBoundedSetupEnv_of_setup_any uuidTryParse i₀ (some ag) false (fun h => nomatch h) hSetup
  have hpeer40 : w.x.peer.name.bytes.length ≤ 40 :=
    (hDom ⟨w.x.peer.name.bytes, w.x.peer.device⟩ dir hgc).2.1
  have hname64 : w.x.peer.val.name.length ≤ cliMaxAddrTextBytes := by
    have hv : w.x.peer.val.name.length = w.x.peer.name.bytes.length := rfl
    unfold cliMaxAddrTextBytes
    omega
  have haddr64 : (addressText w.x.peer.val).length ≤ cliMaxAddrTextBytes := by
    have hle := addressText_length_le w.x.peer.val
    have hv : w.x.peer.val.name.length = w.x.peer.name.bytes.length := rfl
    unfold cliMaxAddrTextBytes
    omega
  have hpeersLen : StoresGhost.opened.identity.peers.path.length ≤ cliMaxDirPathBytes :=
    Nat.le_trans dirDomainCaps_opened_peers.path_len_le (by unfold cliMaxDirPathBytes; decide)
  have hsessLen : StoresGhost.opened.sessions.path.length ≤ cliMaxDirPathBytes :=
    Nat.le_trans dirDomainCaps_opened_sess.path_len_le (by unfold cliMaxDirPathBytes; decide)
  have hpeersNe : StoresGhost.opened.identity.peers.path ≠ [] := by
    intro h
    have hlen := opened_peers_path_len
    rw [h] at hlen
    cases hlen
  have hsessNe : StoresGhost.opened.sessions.path ≠ [] := by
    intro h
    have hlen := opened_sess_path_len
    rw [h] at hlen
    cases hlen
  let dirs : List (List (BitVec 8) × List (List (BitVec 8))) :=
    [(StoresGhost.opened.identity.peers.path, [w.x.peer.val.name]),
     (StoresGhost.opened.sessions.path, [addressText w.x.peer.val])]
  have hstdin : g₀.i.stdin.length ≤ msgCapBytes := by
    rw [hg_i, hi_eq]
    exact Nat.zero_le _
  let wPost : ValidPostSetupWitness i₀ :=
    { g := g₀
      g_i := hg_i
      parse_ok := by rw [hg_i]; exact hparse
      stdin_le := hstdin
      dirs := dirs
      dirs_sum_le := by simp [dirs, cliMaxDirtyEntries]
      dirs_bounds := by
        intro dn hdn
        rcases List.mem_cons.mp hdn with rfl | hdn2
        · exact ⟨hpeersLen, fun nm hnm => (List.mem_singleton.mp hnm) ▸ hname64⟩
        · rcases List.mem_singleton.mp hdn2 with rfl
          exact ⟨hsessLen, fun nm hnm => (List.mem_singleton.mp hnm) ▸ haddr64⟩
      ok := false }
  have hInitCallee : (mkBinaryKitRealCalleeEnvs img S X W' g₀).initEnv evs1c := by
    have hDom' : W3BinaryInitDom (.init ⟨w.x.peer.name.bytes, w.x.peer.device⟩ dir) i₀ w :=
      hgc ▸ hDom
    unfold mkBinaryKitRealCalleeEnvs
    dsimp only
    rw [hgc, hg_i]
    exact ⟨w, hDom', w3InitBinaryKitSlotEnv_of_binSucc hSlot⟩
  have hR1c : R1cEnv (mkBinaryKitRealCalleeEnvs img S X W' g₀).initEnv evs1c :=
    Or.inl hInitCallee
  have hInitCore : InitArmBinaryCoreEnv cliIo.rd (runFiles g₀.i) dir
      (mkBinaryKitRealCalleeEnvs img S X W' g₀).initEnv ((evs1a ++ evs1b) ++ evs1c) := by
    rw [List.append_assoc, hg_i]
    exact Or.inr ⟨evs1a, evs1b ++ evs1c, rfl, r1bFileStepEnv_of_binSucc h1a,
      Or.inr ⟨evs1b, evs1c, rfl, Or.inr (r1bBinaryEnv_of_binSucc h1b), Or.inr hR1c⟩⟩
  have hArm : RunArmBinaryEnv cliIo.rd (runFiles g₀.i)
      (mkBinaryKitRealCalleeEnvs img S X W' g₀) sessionCapBytes g₀.i.stdin g₀.c
      ((evs1a ++ evs1b) ++ evs1c) := by
    unfold RunArmBinaryEnv
    rw [hgc]
    exact Or.inr hInitCore
  have hRun : CliRunBinaryEnv cliIo.rd (mkBinaryKitRealCalleeEnvs img S X W' g₀)
      sessionCapBytes g₀ (evsR0 ++ ((evs1a ++ evs1b) ++ evs1c)) :=
    Or.inr <| Or.inr ⟨evsR0, (evs1a ++ evs1b) ++ evs1c, rfl, r0BinaryEnv_of_binSucc hR0,
      Or.inr ⟨(evs1a ++ evs1b) ++ evs1c, [], (List.append_nil _).symm, hArm, FreeOnlyEvs.nil⟩⟩
  have hM5Phase : M5PhaseEnv wPost.dirs evsM5 :=
    m5PhaseEnv_of_iterConcat_two hpeersNe hsessNe hM5
  have hM6Phase : M6Env wPost.ok [] := Or.inl rfl
  exact Or.inr ⟨evsSetup, (evsR0 ++ ((evs1a ++ evs1b) ++ evs1c)) ++ evsM5, rfl, hBSetup,
    Or.inr ⟨wPost, hg_i,
      Or.inr ⟨evsR0 ++ ((evs1a ++ evs1b) ++ evs1c), evsM5, rfl, hRun,
        Or.inr ⟨evsM5, [], (List.append_nil _).symm, hM5Phase, hM6Phase⟩⟩⟩⟩

/-- Inclusion of `InitSuccMainEnv` into
`RealCliMainBinaryEnvOf (mkBinaryKitRealCalleeEnvs img S X W) i₀`. -/
theorem initSuccMainEnv_sub_realCliMainBinaryEnvOf [LibsignalPlacement]
    (img : Arm64.Obj.Image) (S : RunSem) (X : UnreachedPqxdhPrimitives)
    (W : CliHooks) (i₀ : Inputs) (evs : List AllocEvent)
    (hSucc : InitSuccMainEnv img W i₀ evs) :
    RealCliMainBinaryEnvOf (mkBinaryKitRealCalleeEnvs img S X W) i₀ evs :=
  initSuccMainEnv_sub_realCliMainBinaryEnvOf_anyW img S X W W i₀ evs hSucc

/-- Inclusion of `InitSuccMainEnv` into `realCliMainBinaryKitEnvOf img S X W i₀`. -/
theorem initSuccMainEnv_sub_realCliMainBinaryKitEnvOf [LibsignalPlacement]
    (img : Arm64.Obj.Image) (S : RunSem) (X : UnreachedPqxdhPrimitives)
    (W : CliHooks) (i₀ : Inputs) (evs : List AllocEvent)
    (hSucc : InitSuccMainEnv img W i₀ evs) :
    realCliMainBinaryKitEnvOf img S X W i₀ evs :=
  initSuccMainEnv_sub_realCliMainBinaryEnvOf img S X W i₀ evs hSucc

/-! ## 3. Concrete `succInitCliHooks` Witness and `.ok` Read Lemmas -/

/-- `MainHops.cliIo.rd` is definitionally `cliRd`. -/
theorem succInit_cliIo_rd_eq_cliRd : cliIo.rd = cliRd := rfl

/-- `cliIo.rd` is definitionally `CliExt.readFileResult`. -/
theorem succInit_cliIo_rd_eq_readFileResult : cliIo.rd = readFileResult := rfl

def succInitNzVec32 : List.Vector (BitVec 8) 32 := ⟨1#8 :: List.replicate 31 0#8, rfl⟩

/-- Simplified deterministic `Crypto` primitive witness (`NonVacuityPq.C0`). -/
def succInitC0 : Crypto where
  F st _ := st
  E _ b := b
  D _ b := b
  X _ _ := succInitNzVec32
  pubKey _ := succInitNzVec32

/-- Simplified deterministic `MlKem` witness (`NonVacuityPq.K0`). -/
def succInitK0 : MlKem where
  keyPair _ := List.Vector.replicate 2400 0#8
  encaps1 _ _ :=
    some (List.Vector.replicate 960 0#8,
          List.Vector.replicate 2080 0#8,
          List.Vector.replicate 32 0#8)
  encaps2 _ _ := List.Vector.replicate 128 0#8
  decaps _ _ _ := List.Vector.replicate 32 0#8
  validPk _ _ := true

/-- Simplified deterministic `PqxdhPrims` witness (`NonVacuityPq.Q0`). -/
def succInitQ0 : PqxdhPrims where
  F512 st _ := st
  montToEd _ _ := some (List.Vector.replicate 160 0#8)
  compress _ := List.Vector.replicate 32 0#8
  edNeg p := p
  isTorsionFree _ := true
  dsmb _ A _ := A
  scalarMod s := s
  scalarWide w := fitVec 32 w.toList
  encaps _ _ := (List.Vector.replicate 1568 0#8, List.Vector.replicate 32 0#8)
  decaps _ _ := List.Vector.replicate 32 0#8
  K := succInitK0

/-- Simplified deterministic `PEParams` witness (`NonVacuityPq.W0`). -/
def succInitW0 : PEParams := ⟨succInitC0, succInitQ0⟩

/-- Simplified deterministic `CliHooks` witness (`⟨W₀.C, W₀.Q⟩ = succInitW0`). -/
def succInitCliHooks : CliHooks where
  C := succInitC0
  Q := succInitQ0
  bcmp a b := if a = b then 0#64 else 1#64
  bcmp_ok a b _ := by
    by_cases h : a = b
    · simp [h]
    · simp only [h, ↓reduceIte, iff_false]
      decide
  utf8Err _ := (0#64, 0#16)

/-- Concrete Alice `PqParty` witness (`session = none`, `peerId = none`). -/
def succInitParty0 : PqParty where
  party := .A
  me := ⟨List.Vector.replicate 32 0#8, 0#32⟩
  peerId := none
  session := none
  signed := []
  oneTime := []
  kyberOneTime := []
  kyberLastResort := []

/-- Concrete peer bundle witness (`opk = none`, zero-filled keys and signatures). -/
def succInitB0 : PreKeyBundleFields where
  regId := 0#32
  opk := none
  spkId := 0#32
  spkPub := List.Vector.replicate 32 0#8
  spkSig := List.Vector.replicate 64 0#8
  kpkId := 0#32
  kpkPub := List.Vector.replicate 1568 0#8
  kpkSig := List.Vector.replicate 64 0#8
  idPub := List.Vector.replicate 32 0#8

/-- Concrete 192-byte zero random tape for `init`. -/
def succInitT0 : List.Vector (BitVec 8) initiateTapeLen :=
  List.Vector.replicate initiateTapeLen 0#8

/-- Concrete `Inputs` for `init <Bob> bundle` on `(succInitW0, succInitParty0, succInitB0, succInitT0)`. -/
def succInitInputs : Inputs :=
  pqInitInputs succInitW0 succInitParty0 succInitB0 succInitT0

/-- Encoded `"identity-key-pair"` file bytes on `succInitParty0` / `succInitW0`. -/
def succInitIdKeyPairBytes : List (BitVec 8) :=
  IdentityKeyPairStructure.encode
    ⟨djbKey (keyPairOf succInitC0 succInitParty0.me.idPriv).publicKey.bytes,
     succInitParty0.me.idPriv.toList⟩

private def succInitX0 : UnreachedPqxdhPrimitives where
  sigPkGen _ := []
  sigSign _ _ _ := []
  scalarMul _ _ := []
  scalarAdd _ _ := []
  kemKeyGen _ := ([], [])
  pow8 _ := []
  isValidDhTriple _ _ _ := false

private theorem textBytes_partyAddress_length_le (p : Party) :
    (textBytes (partyAddress p).text).length ≤ fileCapBytes := by
  unfold textBytes partyAddress Address.text fileCapBytes
  dsimp only
  rw [succ_repr_utf8_eq_kutf8]
  have hk_app (a b : String) : succKutf8 (a ++ b) = succKutf8 a ++ succKutf8 b := by
    simp [succKutf8, String.toList_append, List.flatMap_append]
  rw [hk_app, hk_app, List.length_append, List.length_append]
  have hd : (succKutf8 (toString (1 : Nat))).length = 1 := by
    rw [← succ_utf8_eq_kutf8]
    change (decimalText 1).length = 1
    rw [decimalText_digit 1 (by decide)]
    rfl
  have hdot : (succKutf8 ".").length = 1 := rfl
  have hp : (succKutf8 (partyAddressName p)).length = 36 := by
    cases p <;> rfl
  omega

private theorem succInitParty0_inSpecDomain :
    PqxdhPartyInSpecDomain succInitW0 succInitParty0 := by
  refine ⟨?_, ?_, List.nodup_nil, List.nodup_nil, List.nodup_nil, List.nodup_nil⟩
  · intro _ _ hs
    nomatch hs
  · intro f hf
    have hle : f.2.length ≤ fileCapBytes := by
      unfold encodeDir succInitParty0 succInitW0 succInitC0 at hf
      simp only [List.map_nil, List.flatten_nil, List.append_nil,
        List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl
      · exact textBytes_partyAddress_length_le .A
      · unfold fileCapBytes; decide
      · unfold fileCapBytes; decide
    exact ⟨by unfold fileCapBytes at hle; omega, fun _ => hle⟩

private theorem initiateKeys_modelPrims_eq (X₁ X₂ : UnreachedPqxdhPrimitives)
    (W : PEParams) (inp : SignalPqxdh.InitiateKeysInput) :
    SignalPqxdh.Model.initiateKeys (CryptoVerification.E2E.modelPrims X₁ W) inp =
      SignalPqxdh.Model.initiateKeys (CryptoVerification.E2E.modelPrims X₂ W) inp := by
  have h1 : (CryptoVerification.E2E.modelPrims X₁ W).sigVerify =
      (CryptoVerification.E2E.modelPrims X₂ W).sigVerify := rfl
  have h2 : (CryptoVerification.E2E.modelPrims X₁ W).kemEncaps =
      (CryptoVerification.E2E.modelPrims X₂ W).kemEncaps := rfl
  have h3 : (CryptoVerification.E2E.modelPrims X₁ W).x25519Base =
      (CryptoVerification.E2E.modelPrims X₂ W).x25519Base := rfl
  have h4 : (CryptoVerification.E2E.modelPrims X₁ W).x25519 =
      (CryptoVerification.E2E.modelPrims X₂ W).x25519 := rfl
  have h5 : (CryptoVerification.E2E.modelPrims X₁ W).hkdfDerive96 =
      (CryptoVerification.E2E.modelPrims X₂ W).hkdfDerive96 := rfl
  simp only [SignalPqxdh.Model.initiateKeys, h1, h2, h3, h4, h5]

private theorem initiateState_succInitW0_eq (X : UnreachedPqxdhPrimitives) :
    initiateState X succInitW0 .A succInitParty0.me succInitB0 succInitT0 =
      initiateState succInitX0 succInitW0 .A succInitParty0.me succInitB0 succInitT0 := by
  simp only [initiateState, initiateKeys_modelPrims_eq X succInitX0]

private theorem initiateState_succInitW0_isSome :
    (initiateState succInitX0 succInitW0 .A succInitParty0.me succInitB0 succInitT0).isSome =
      true := by
  decide +kernel

set_option maxRecDepth 50000 in
private theorem pqInitModel_succInitW0_uniform :
    ∃ (st₁ : PqParty) (x₁ : RecordExtras) (g₁ : GhostState (List (BitVec 8))),
      st₁.session = some (x₁, g₁) ∧
      PqxdhPartyInSpecDomain succInitW0 st₁ ∧
      ∀ X : UnreachedPqxdhPrimitives,
        pqInitModel X succInitW0 succInitParty0 succInitB0 succInitT0 = some (some (st₁, [])) := by
  have hSome := initiateState_succInitW0_isSome
  cases hInit0 :
      initiateState succInitX0 succInitW0 .A succInitParty0.me succInitB0 succInitT0 with
  | none => simp [hInit0] at hSome
  | some xg =>
    rcases xg with ⟨x₁, g₁⟩
    let st₁ : PqParty :=
      { succInitParty0 with peerId := some ⟨⟨succInitB0.idPub⟩⟩, session := some (x₁, g₁) }
    have hrecCap : (encodeRecordUnderExtras (fun _ => x₁) g₁).length ≤ fileCapBytes := by
      have : (match initiateState succInitX0 succInitW0 .A succInitParty0.me succInitB0 succInitT0 with
        | some (x', g') => decide ((encodeRecordUnderExtras (fun _ => x') g').length ≤ fileCapBytes)
        | none => false) = true := by with_unfolding_all rfl
      simpa [hInit0] using this
    have hltCap : fileCapBytes < 2 ^ 31 := by decide
    have hrec : (encodeRecordUnderExtras (fun _ => x₁) g₁).length < 2 ^ 31 :=
      Nat.lt_of_le_of_lt hrecCap hltCap
    have hdir : ∀ f ∈ encodeDir succInitW0 st₁,
        f.2.length < 2 ^ 31 ∧ ((∀ i, f.1 ≠ baseKeysFile i) → f.2.length ≤ fileCapBytes) := by
      intro f hf
      have hle : f.2.length ≤ fileCapBytes := by
        unfold encodeDir st₁ succInitParty0 at hf
        simp only [List.map_nil, List.flatten_nil, List.append_nil, List.cons_append,
          List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hf
        rcases hf with rfl | rfl | rfl | rfl | rfl
        · exact textBytes_partyAddress_length_le .A
        · unfold fileCapBytes; decide
        · unfold fileCapBytes; decide
        · unfold fileCapBytes; decide
        · exact hrecCap
      exact ⟨Nat.lt_of_le_of_lt hle hltCap, fun _ => hle⟩
    have hgparty : g₁.party = .A := by
      have : (match initiateState succInitX0 succInitW0 .A succInitParty0.me succInitB0 succInitT0 with
        | some (_, g') => decide (g'.party = .A)
        | none => false) = true := by with_unfolding_all rfl
      simpa [hInit0] using this
    have hwf : PqxdhPartyInSpecDomain succInitW0 st₁ := by
      refine ⟨?_, hdir, List.nodup_nil, List.nodup_nil, List.nodup_nil, List.nodup_nil⟩
      intro x' g' hs
      injection hs with hpair
      cases hpair
      exact ⟨⟨g₁,
        ReachablePqxdhSession.initiate succInitX0 .A succInitParty0.me succInitB0 succInitT0 x₁ g₁ hInit0,
        rfl, rfl⟩, hgparty, hrec⟩
    refine ⟨st₁, x₁, g₁, rfl, hwf, fun X => ?_⟩
    have hInit : initiateState X succInitW0 .A succInitParty0.me succInitB0 succInitT0 =
        some (x₁, g₁) := (initiateState_succInitW0_eq X).trans hInit0
    have hparty : succInitParty0.party = .A := rfl
    have htrusts : succInitParty0.trusts ⟨⟨succInitB0.idPub⟩⟩ = true := rfl
    simp only [pqInitModel, htrusts, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hparty, hInit]
    rfl

private theorem pathOf_bundleDir_eq_bundlePath (name : String) :
    pathOf (bytesOfString bundleDir) (utf8 name) = bundlePath (bytesOfString bundleDir) name := by
  have hne : bytesOfString bundleDir ≠ [] := by
    change [0x62#8, 0x75#8, 0x6e#8, 0x64#8, 0x6c#8, 0x65#8] ≠ []
    decide
  have hslash : utf8 "/" = [0x2f#8] := by
    rw [succ_utf8_eq_kutf8]; rfl
  unfold pathOf bundlePath
  simp only [hne, ↓reduceIte, hslash]

private theorem bind_eq_some {α β : Type} {oa : Option α} {f : α → Option β} {b : β}
    (h : (oa >>= f) = some b) : ∃ a, oa = some a ∧ f a = some b := by
  cases oa with
  | none => cases h
  | some a => exact ⟨a, rfl, h⟩

private theorem rd_ok_of_bundleFile_some {F : FsFiles} {dir : List (BitVec 8)}
    {name : String} {bs : List (BitVec 8)} (h : bundleFile F dir name = some bs) :
    cliIo.rd F (bundlePath dir name) = .ok bs := by
  unfold bundleFile exceptOpt at h
  cases hrd : cliIo.rd F (bundlePath dir name) with
  | error _ => rw [hrd] at h; cases h
  | ok bs' => rw [hrd] at h; injection h with heq; subst heq; rfl

private theorem succInit_all_bundle_reads :
    (∃ bs, cliIo.rd (runFiles succInitInputs)
      (pathOf (bytesOfString bundleDir) (utf8 "identity-key")) = .ok bs) ∧
    (∃ bs, cliIo.rd (runFiles succInitInputs)
      (pathOf (bytesOfString bundleDir) (utf8 "registration-id")) = .ok bs) ∧
    (∃ bs, cliIo.rd (runFiles succInitInputs)
      (pathOf (bytesOfString bundleDir) (utf8 "signed-pre-key")) = .ok bs) ∧
    (∃ bs, cliIo.rd (runFiles succInitInputs)
      (pathOf (bytesOfString bundleDir) (utf8 "kyber-pre-key")) = .ok bs) ∧
    cliIo.rd (runFiles succInitInputs)
      (pathOf (bytesOfString bundleDir) (utf8 "one-time-pre-key")) = .ok [] := by
  have hread := readBundleV_pqInit succInitW0 succInitParty0 succInitB0 succInitT0
  change readBundleV (runFiles succInitInputs) (bytesOfString bundleDir) 1#8 =
    some (bundleVE succInitB0) at hread
  unfold readBundleV at hread
  obtain ⟨ikB, hik, hread⟩ := bind_eq_some hread
  obtain ⟨_, _, hread⟩ := bind_eq_some hread
  obtain ⟨regB, hreg, hread⟩ := bind_eq_some hread
  obtain ⟨_, _, hread⟩ := bind_eq_some hread
  obtain ⟨spkB, hspk, hread⟩ := bind_eq_some hread
  obtain ⟨⟨_, _, _⟩, _, hread⟩ := bind_eq_some hread
  obtain ⟨kpkB, hkpk, hread⟩ := bind_eq_some hread
  obtain ⟨⟨_, _, _⟩, _, hread⟩ := bind_eq_some hread
  obtain ⟨opkB, hopk, htail⟩ := bind_eq_some hread
  have hopkNil : opkB = [] := by
    cases hopkB : opkB with
    | nil => rfl
    | cons b tl =>
      rw [hopkB] at htail
      dsimp only [List.isEmpty] at htail
      simp only [Bool.false_eq_true, ↓reduceIte] at htail
      obtain ⟨opkOpt, hopkOpt, htail⟩ := bind_eq_some htail
      obtain ⟨_, _, htail⟩ := bind_eq_some htail
      obtain ⟨_, _, htail⟩ := bind_eq_some htail
      injection htail with hbv
      have hnone : opkOpt = none :=
        congrArg CryptoVerification.SignalSession.Cli.RunCompose.BundleV.opk hbv
      rw [hnone] at hopkOpt
      obtain ⟨_, _, hopkOpt⟩ := bind_eq_some hopkOpt
      obtain ⟨_, _, hopkOpt⟩ := bind_eq_some hopkOpt
      cases hopkOpt
  subst hopkNil
  refine ⟨⟨ikB, ?_⟩, ⟨regB, ?_⟩, ⟨spkB, ?_⟩, ⟨kpkB, ?_⟩, ?_⟩
  · rw [pathOf_bundleDir_eq_bundlePath]; exact rd_ok_of_bundleFile_some hik
  · rw [pathOf_bundleDir_eq_bundlePath]; exact rd_ok_of_bundleFile_some hreg
  · rw [pathOf_bundleDir_eq_bundlePath]; exact rd_ok_of_bundleFile_some hspk
  · rw [pathOf_bundleDir_eq_bundlePath]; exact rd_ok_of_bundleFile_some hkpk
  · rw [pathOf_bundleDir_eq_bundlePath]; exact rd_ok_of_bundleFile_some hopk

/-- When `succInitB0.opk = none`, `runFiles succInitInputs` reads `.ok []` at
`"bundle/one-time-pre-key"`. -/
theorem succInit_opk_read_eq_ok_nil :
    cliIo.rd (runFiles succInitInputs)
      (pathOf (bytesOfString bundleDir) (utf8 "one-time-pre-key")) = .ok [] :=
  succInit_all_bundle_reads.2.2.2.2

private theorem succInit_fs_lookup (s : String)
    (hns : normalizePath s ∉ stdioPaths.map normalizePath)
    (hne : (normalizePath s).isEmpty = false) :
    runFiles succInitInputs s =
      (filesFold succInitInputs.files (dirsFold succInitInputs.dirs {})).entries
        (normalizePath s) := by
  change (initFsState (cliInputs succInitInputs)).files s = _
  rw [files_eq_entries, ite_eq_right_iff.mpr (by simp [hne])]
  exact initFsState_entries (cliInputs succInitInputs) (normalizePath s) hns

private theorem foldl_dir_entries_of_forall_ne (l : List FsPath) (fs : FsState) (k : FsPath)
    (h : ∀ p ∈ l, (k == p) = false) :
    (l.foldl (fun acc pref => acc.setEntry pref (some .dir)) fs).entries k = fs.entries k := by
  induction l generalizing fs with
  | nil => rfl
  | cons p l ih =>
    rw [List.foldl_cons, ih _ (fun q hq => h q (List.mem_cons_of_mem _ hq))]
    have hne : (k == p) = false := h p (List.mem_cons_self ..)
    simp only [FsState.setEntry, hne, Bool.false_eq_true, ↓reduceIte]

private theorem dirsFold_entries_of_forall_ne (dirs : List String) (fs : FsState) (k : FsPath)
    (h : ∀ d ∈ dirs, ∀ p ∈ FsPath.nonEmptyPrefixes (normalizePath d), (k == p) = false) :
    (dirsFold dirs fs).entries k = fs.entries k := by
  induction dirs generalizing fs with
  | nil => rfl
  | cons d dirs ih =>
    unfold dirsFold
    rw [List.foldl_cons]
    change (dirsFold dirs _).entries k = fs.entries k
    rw [ih _ (fun d' hd' => h d' (List.mem_cons_of_mem _ hd'))]
    exact foldl_dir_entries_of_forall_ne _ fs k (h d (List.mem_cons_self ..))

private theorem filesFold_entries_of_forall_ne (files : List (String × List (BitVec 8)))
    (fs : FsState) (k : FsPath)
    (h : ∀ p ∈ files.map Prod.fst,
      (k == normalizePath p) = false ∧
      ∀ pref ∈ (FsPath.nonEmptyPrefixes (normalizePath p)).dropLast, (k == pref) = false) :
    (filesFold files fs).entries k = fs.entries k := by
  induction files generalizing fs with
  | nil => rfl
  | cons x files ih =>
    rcases x with ⟨p, _⟩
    have hp := h p (List.mem_cons_self ..)
    unfold filesFold
    rw [List.foldl_cons]
    change (filesFold files _).entries k = fs.entries k
    rw [ih _ (fun q hq => h q (List.mem_cons_of_mem _ hq))]
    simp only [FsState.setFile, FsState.setEntry, hp.1, Bool.false_eq_true, ↓reduceIte]
    exact foldl_dir_entries_of_forall_ne _ fs k hp.2

private def succInitFilePaths : List String :=
  ["address", "identity-key-pair", "registration-id",
   "bundle/identity-key", "bundle/registration-id",
   "bundle/signed-pre-key", "bundle/kyber-pre-key", "coins"]

private theorem succInit_bundle_path_eq (suf full : String)
    (h : "bundle".toList ++ suf.toList = full.toList) :
    bundleDir ++ suf = full := by
  unfold bundleDir
  rw [← String.toList_inj, String.toList_append]
  exact h

private theorem succInit_files_fst_eq :
    succInitInputs.files.map Prod.fst = succInitFilePaths := by
  have h1 := succInit_bundle_path_eq "/identity-key" "bundle/identity-key" (by decide)
  have h2 := succInit_bundle_path_eq "/registration-id" "bundle/registration-id" (by decide)
  have h3 := succInit_bundle_path_eq "/signed-pre-key" "bundle/signed-pre-key" (by decide)
  have h4 := succInit_bundle_path_eq "/kyber-pre-key" "bundle/kyber-pre-key" (by decide)
  have hraw : succInitInputs.files.map Prod.fst =
      ["address", "identity-key-pair", "registration-id",
       bundleDir ++ "/identity-key", bundleDir ++ "/registration-id",
       bundleDir ++ "/signed-pre-key", bundleDir ++ "/kyber-pre-key", "coins"] := rfl
  rw [hraw, h1, h2, h3, h4]
  rfl

private theorem succInit_entries_none (s : String)
    (hns : normalizePath s ∉ stdioPaths.map normalizePath)
    (hne : (normalizePath s).isEmpty = false)
    (hf : ∀ p ∈ succInitFilePaths,
      (normalizePath s == normalizePath p) = false ∧
      ∀ pref ∈ (FsPath.nonEmptyPrefixes (normalizePath p)).dropLast,
        (normalizePath s == pref) = false)
    (hd : ∀ d ∈ partyDirs ++ ["bundle"],
      ∀ p ∈ FsPath.nonEmptyPrefixes (normalizePath d),
        (normalizePath s == p) = false) :
    runFiles succInitInputs s = none := by
  have hdirs : succInitInputs.dirs = partyDirs ++ ["bundle"] := rfl
  rw [succInit_fs_lookup s hns hne,
    filesFold_entries_of_forall_ne succInitInputs.files _ (normalizePath s)
      (by rwa [succInit_files_fst_eq]),
    dirsFold_entries_of_forall_ne succInitInputs.dirs _ (normalizePath s)
      (by rwa [hdirs])]
  show (if (normalizePath s).isEmpty then some FsEntry.dir else none) = none
  rw [hne]
  rfl

/-- `"coins"` reads `.ok succInitT0.toList`, so
`succInitCoinsEvents succInitInputs = [AllocEvent.alloc 192]`. -/
theorem succInit_coins_read_eq_ok :
    readFileResult (initFsState (cliInputs succInitInputs)).files (utf8 "coins") =
      .ok succInitT0.toList := by
  have hp : pathStr (utf8 "coins") = "coins" := by
    rw [succ_utf8_eq_kutf8]; rfl
  have hcs : pathComps "coins" = ["coins".toList] := by
    unfold pathComps
    exact List.splitOn_eq_singleton (by decide)
  have hb : blockingAncestorF (initFsState (cliInputs succInitInputs)).files "coins" = none := by
    unfold blockingAncestorF ancestors
    rw [hcs]
    rfl
  have hf : (initFsState (cliInputs succInitInputs)).files "coins" =
      some (.file succInitT0.toList) := by
    rw [show (initFsState (cliInputs succInitInputs)).files = runFiles succInitInputs from rfl,
      succInit_fs_lookup "coins" (by decide) (by decide)]
    with_unfolding_all rfl
  have hcap : succInitT0.toList.length ≤ fileCapBytes := by
    have hlen : succInitT0.toList.length = initiateTapeLen := succInitT0.2
    rw [hlen]; decide
  unfold readFileResult readViewF
  rw [hp, hb, hf]
  simp only [hcap, ↓reduceIte]

/-- `own` `"address"` reads `.ok (textBytes (partyAddress .A).text)` on `succInitInputs`. -/
theorem succInit_ownAddr_read_eq_ok :
    cliIo.rd (runFiles succInitInputs)
      (pathOf StoresGhost.opened.identity.own.path (utf8 "address")) =
      .ok (textBytes (partyAddress .A).text) := by
  have hp : pathStr (pathOf StoresGhost.opened.identity.own.path (utf8 "address")) = "address" := by
    change pathStr (utf8 "address") = "address"
    rw [succ_utf8_eq_kutf8]
    rfl
  have hcs : pathComps "address" = ["address".toList] := by
    unfold pathComps
    exact List.splitOn_eq_singleton (by decide)
  have hb : blockingAncestorF (runFiles succInitInputs) "address" = none := by
    unfold blockingAncestorF ancestors
    rw [hcs]
    rfl
  have hf : runFiles succInitInputs "address" =
      some (.file (textBytes (partyAddress .A).text)) := by
    rw [succInit_fs_lookup "address" (by decide) (by decide)]
    with_unfolding_all rfl
  have hcap : (textBytes (partyAddress .A).text).length ≤ fileCapBytes :=
    textBytes_partyAddress_length_le .A
  change readFileResult (runFiles succInitInputs) _ = .ok (textBytes (partyAddress .A).text)
  unfold readFileResult readViewF
  rw [hp, hb, hf]
  simp only [hcap, ↓reduceIte]

/-- Absent peer identity file `"identities/" ++ partyAddressName .B` reads `.ok []`. -/
theorem succInit_peers_read_eq_ok_nil :
    cliIo.rd (runFiles succInitInputs)
      (pathOf StoresGhost.opened.identity.peers.path (utf8 (partyAddressName .B))) = .ok [] := by
  let sPeer := "identities/5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6"
  have hp : pathStr (pathOf StoresGhost.opened.identity.peers.path (utf8 (partyAddressName .B))) =
      sPeer := by
    change pathStr (pathOf (utf8 "identities") (utf8 (partyAddressName .B))) = sPeer
    unfold pathOf partyAddressName pathStr
    rw [succ_utf8_eq_kutf8, succ_utf8_eq_kutf8, succ_utf8_eq_kutf8,
      ← String.toList_inj, String.toList_ofList]
    decide
  have hcs : pathComps sPeer =
      ["identities".toList, "5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6".toList] := by
    unfold pathComps sPeer
    have hsplit : "identities/5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6".toList =
        "identities".toList ++ '/' :: "5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6".toList := by decide
    rw [hsplit, List.splitOn_append_cons_self_of_not_mem (by decide),
      List.splitOn_eq_singleton (by decide)]
  have hofIdent :
      String.ofList ['i', 'd', 'e', 'n', 't', 'i', 't', 'i', 'e', 's'] = "identities" := by
    rw [← String.toList_inj, String.toList_ofList]
  have hanc : ancestors sPeer = ["identities"] := by
    unfold ancestors
    rw [hcs]
    dsimp
    rw [List.map_singleton, List.take_zero, List.intercalate_singleton, hofIdent]
  have hdir : runFiles succInitInputs "identities" = some .dir := by
    rw [succInit_fs_lookup "identities" (by decide) (by decide)]
    with_unfolding_all rfl
  have hb : blockingAncestorF (runFiles succInitInputs) sPeer = none := by
    unfold blockingAncestorF
    rw [hanc]
    simp [hdir]
  have hf : runFiles succInitInputs sPeer = none :=
    succInit_entries_none sPeer (by decide) (by decide) (by decide) (by decide)
  change readFileResult (runFiles succInitInputs) _ = .ok []
  unfold readFileResult readViewF
  rw [hp, hb, hf]

/-- Absent session file `"sessions/" ++ (partyAddress .B).text` reads `.ok []`. -/
theorem succInit_sess_read_eq_ok_nil :
    cliIo.rd (runFiles succInitInputs)
      (pathOf StoresGhost.opened.sessions.path
        (addressText ⟨utf8 (partyAddressName .B), 1#8⟩)) = .ok [] := by
  let sSess := "sessions/5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6.1"
  have hdec1 : decimalText (1#8 : BitVec 8).toNat = succKutf8 "1" := by
    change decimalText 1 = succKutf8 "1"
    rw [decimalText_digit 1 (by decide)]
    rfl
  have hp : pathStr (pathOf StoresGhost.opened.sessions.path
      (addressText ⟨utf8 (partyAddressName .B), 1#8⟩)) = sSess := by
    change pathStr (pathOf (utf8 "sessions")
      (utf8 (partyAddressName .B) ++ utf8 "." ++ decimalText (1#8 : BitVec 8).toNat)) = sSess
    rw [hdec1]
    unfold pathOf partyAddressName pathStr
    rw [succ_utf8_eq_kutf8, succ_utf8_eq_kutf8, succ_utf8_eq_kutf8, succ_utf8_eq_kutf8,
      ← String.toList_inj, String.toList_ofList]
    decide
  have hcs : pathComps sSess =
      ["sessions".toList, "5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6.1".toList] := by
    unfold pathComps sSess
    have hsplit : "sessions/5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6.1".toList =
        "sessions".toList ++ '/' :: "5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6.1".toList := by decide
    rw [hsplit, List.splitOn_append_cons_self_of_not_mem (by decide),
      List.splitOn_eq_singleton (by decide)]
  have hofSess : String.ofList ['s', 'e', 's', 's', 'i', 'o', 'n', 's'] = "sessions" := by
    rw [← String.toList_inj, String.toList_ofList]
  have hanc : ancestors sSess = ["sessions"] := by
    unfold ancestors
    rw [hcs]
    dsimp
    rw [List.map_singleton, List.take_zero, List.intercalate_singleton, hofSess]
  have hdir : runFiles succInitInputs "sessions" = some .dir := by
    rw [succInit_fs_lookup "sessions" (by decide) (by decide)]
    with_unfolding_all rfl
  have hb : blockingAncestorF (runFiles succInitInputs) sSess = none := by
    unfold blockingAncestorF
    rw [hanc]
    simp [hdir]
  have hf : runFiles succInitInputs sSess = none :=
    succInit_entries_none sSess (by decide) (by decide) (by decide) (by decide)
  change readFileResult (runFiles succInitInputs) _ = .ok []
  unfold readFileResult readViewF
  rw [hp, hb, hf]

/-- `own` `"identity-key-pair"` reads `.ok succInitIdKeyPairBytes` on `succInitInputs`. -/
theorem succInit_idKeyPair_read_eq_ok :
    cliIo.rd (runFiles succInitInputs)
      (pathOf StoresGhost.opened.identity.own.path (utf8 "identity-key-pair")) =
      .ok succInitIdKeyPairBytes := by
  have hp : pathStr (pathOf StoresGhost.opened.identity.own.path (utf8 "identity-key-pair")) =
      "identity-key-pair" := by
    change pathStr (utf8 "identity-key-pair") = "identity-key-pair"
    rw [succ_utf8_eq_kutf8]
    rfl
  have hcs : pathComps "identity-key-pair" = ["identity-key-pair".toList] := by
    unfold pathComps
    exact List.splitOn_eq_singleton (by decide)
  have hb : blockingAncestorF (runFiles succInitInputs) "identity-key-pair" = none := by
    unfold blockingAncestorF ancestors
    rw [hcs]
    rfl
  have hf : runFiles succInitInputs "identity-key-pair" = some (.file succInitIdKeyPairBytes) := by
    rw [succInit_fs_lookup "identity-key-pair" (by decide) (by decide)]
    with_unfolding_all rfl
  have hcap : succInitIdKeyPairBytes.length ≤ fileCapBytes :=
    of_decide_eq_true (by with_unfolding_all rfl)
  change readFileResult (runFiles succInitInputs) _ = .ok succInitIdKeyPairBytes
  unfold readFileResult readViewF
  rw [hp, hb, hf]
  simp only [hcap, ↓reduceIte]

/-- `own` `"registration-id"` reads `.ok (le32 0#32)` (`4` bytes) on `succInitInputs`. -/
theorem succInit_regId_read_eq_ok :
    cliIo.rd (runFiles succInitInputs)
      (pathOf StoresGhost.opened.identity.own.path (utf8 "registration-id")) =
      .ok (le32 0#32) := by
  have hp : pathStr (pathOf StoresGhost.opened.identity.own.path (utf8 "registration-id")) =
      "registration-id" := by
    change pathStr (utf8 "registration-id") = "registration-id"
    rw [succ_utf8_eq_kutf8]
    rfl
  have hcs : pathComps "registration-id" = ["registration-id".toList] := by
    unfold pathComps
    exact List.splitOn_eq_singleton (by decide)
  have hb : blockingAncestorF (runFiles succInitInputs) "registration-id" = none := by
    unfold blockingAncestorF ancestors
    rw [hcs]
    rfl
  have hf : runFiles succInitInputs "registration-id" = some (.file (le32 0#32)) := by
    rw [succInit_fs_lookup "registration-id" (by decide) (by decide)]
    with_unfolding_all rfl
  have hcap : (le32 0#32).length ≤ fileCapBytes := by
    unfold fileCapBytes
    decide
  change readFileResult (runFiles succInitInputs) _ = .ok (le32 0#32)
  unfold readFileResult readViewF
  rw [hp, hb, hf]
  simp only [hcap, ↓reduceIte]

theorem succInit_ownAddr_read_ne_error :
    cliIo.rd (runFiles succInitInputs)
      (pathOf StoresGhost.opened.identity.own.path (utf8 "address")) ≠ .error () := by
  rw [succInit_ownAddr_read_eq_ok]; intro h; cases h

theorem succInit_peers_read_ne_error :
    cliIo.rd (runFiles succInitInputs)
      (pathOf StoresGhost.opened.identity.peers.path (utf8 (partyAddressName .B))) ≠ .error () := by
  rw [succInit_peers_read_eq_ok_nil]; intro h; cases h

theorem succInit_sess_read_ne_error :
    cliIo.rd (runFiles succInitInputs)
      (pathOf StoresGhost.opened.sessions.path
        (addressText ⟨utf8 (partyAddressName .B), 1#8⟩)) ≠ .error () := by
  rw [succInit_sess_read_eq_ok_nil]; intro h; cases h

theorem succInit_idKeyPair_read_ne_error :
    cliIo.rd (runFiles succInitInputs)
      (pathOf StoresGhost.opened.identity.own.path (utf8 "identity-key-pair")) ≠ .error () := by
  rw [succInit_idKeyPair_read_eq_ok]; intro h; cases h

theorem succInit_regId_read_ne_error :
    cliIo.rd (runFiles succInitInputs)
      (pathOf StoresGhost.opened.identity.own.path (utf8 "registration-id")) ≠ .error () := by
  rw [succInit_regId_read_eq_ok]; intro h; cases h

/-! ## 4. Concrete Binary-Kit Trace Witness, Block 594 (`Bob.1`), and Non-Vacuity Theorems -/

def succInitPeerGhost : AddrGhost :=
  { name := ⟨0#64, 0#64, utf8 (partyAddressName .B)⟩, device := 1#8 }

def succInitMeGhost : AddrGhost :=
  { name := ⟨0#64, 0#64, utf8 (partyAddressName .A)⟩, device := 1#8 }

/-- Exact Block 594 (`address_text`) trace on `Bob.1`. -/
theorem succInit_addrText_events_eq :
    addrTextExactEvents succInitPeerGhost.val =
      [AllocEvent.alloc 36, AllocEvent.realloc 1 36 72,
       AllocEvent.alloc 8, AllocEvent.free 1 8] := by
  have hname : succInitPeerGhost.val.name = succKutf8 (partyAddressName .B) :=
    succ_utf8_eq_kutf8 (partyAddressName .B)
  have hdev : succInitPeerGhost.val.device = 1#8 := rfl
  have hdecLen : (decimalText ((1#8 : BitVec 8).zeroExtend 32).toNat).length = 1 := by
    change (decimalText 1).length = 1
    rw [decimalText_digit 1 (by decide)]
    rfl
  unfold addrTextExactEvents decimalEvents addrDecReserveEvents
  rw [hname, hdev]
  dsimp only
  rw [hdecLen]
  decide

private theorem addrTextBinSuccEnv_exact (rem : AddrVal) :
    AddrTextBinSuccEnv rem (addrTextExactEvents rem) :=
  ⟨addrToOwnedEvents rem.name, _, rfl, rfl,
    addrDotReserveEvents rem.name, _, rfl, rfl,
    decimalEvents (rem.device.zeroExtend 32), _, rfl, rfl,
    addrDecReserveEvents rem.name rem.device, rustDeallocEvents 8 1, rfl, rfl, rfl⟩

private def dirGetCacheMissOkWitnessEvents (d : DirGhost) (name bs : List (BitVec 8)) :
    List AllocEvent :=
  (if d.path = [] then allocBytes1Events name else pathEvents d.path name) ++
    (allocBytes1Events bs ++ ([] ++ deallocBytes1OfLen bs.length))

private theorem dirGetCacheMissOkBinEnv_witness {rd : ReadRule} {F0 : FsFiles}
    {d : DirGhost} {name bs : List (BitVec 8)}
    (hch : d.changed = []) (hok : rd F0 (pathOf d.path name) = .ok bs) :
    DirGetCacheMissOkBinEnv rd F0 d name (dirGetCacheMissOkWitnessEvents d name bs) := by
  have hP : DirGetPathEnv PathEnv d.path name
      (if d.path = [] then allocBytes1Events name else pathEvents d.path name) := by
    unfold DirGetPathEnv PathEnv
    split <;> rfl
  have hR : ReadFileRuleEnv rd F0 (pathOf d.path name) (allocBytes1Events bs) := by
    unfold ReadFileRuleEnv
    rw [hok]
    exact Or.inl rfl
  exact ⟨hch, ⟨bs, hok⟩,
    _, _, rfl, hP,
    allocBytes1Events bs, [] ++ deallocBytes1OfLen bs.length, rfl, hR,
    [], deallocBytes1OfLen bs.length, rfl, rfl, freeOnlyEvs_deallocBytes1OfLen bs.length⟩

private def bundleFileReadWitnessEvents (dir name bs : List (BitVec 8)) : List AllocEvent :=
  pathEvents dir name ++ (allocBytes1Events bs ++ deallocBytes1OfLen bs.length)

private theorem bundleFileReadBinSuccEnv_witness {rd : ReadRule} {files : FsFiles}
    {dir name bs : List (BitVec 8)}
    (hne : dir ≠ []) (hrd : rd files (pathOf dir name) = .ok bs) :
    BundleFileReadBinSuccEnv rd files dir name (bundleFileReadWitnessEvents dir name bs) :=
  ⟨hne, bs, hrd, pathEvents dir name, allocBytes1Events bs ++ deallocBytes1OfLen bs.length,
    rfl, rfl, allocBytes1Events bs, deallocBytes1OfLen bs.length, rfl, rfl, rfl⟩

private def m5LoopAWitnessEvents (dir name : List (BitVec 8)) : List AllocEvent :=
  let cap0 := dir.length
  let cap1 := reserveCap cap0 cap0 1
  let need2 := decide (cap1 - (cap0 + 1) < name.length)
  let capFinal := if need2 then reserveCap cap1 (cap0 + 1) name.length else cap1
  (((rustAllocEvents cap0 1 ++ rustReallocEvents cap0 cap1 1) ++
      (if need2 then rustReallocEvents cap1 capFinal 1 else [])) ++ []) ++
    rustDeallocEvents capFinal 1

private theorem m5LoopAEntryEnv_witness (dir name : List (BitVec 8)) :
    M5LoopAEntryEnv dir name (m5LoopAWitnessEvents dir name) := by
  unfold M5LoopAEntryEnv m5LoopAWitnessEvents
  refine ⟨_, _, rfl, ⟨_, [], rfl, ⟨_, _, rfl, ⟨_, _, rfl, rfl, rfl⟩, ?_⟩, Or.inl rfl⟩, rfl⟩
  split <;> rfl

private def succInitArenaB : BitVec 64 := 0x10000#64

private def succInitSessGhost : SessionGhost :=
  { localIk := ⟨33#64, succInitArenaB + 512#64, pk0.serialize⟩
    remoteIk := ⟨0#64, 1#64, []⟩
    root := ⟨32#64, succInitArenaB + 560#64⟩
    chainsCap := 0#64
    chainsPtr := 8#64
    chains := []
    alice := ⟨0#64, 1#64, []⟩
    pq := ⟨0#64, 1#64⟩
    sender := none
    pending := none
    kyber := none
    regIds := List.replicate 8 0#8 }

private def succInitSessVal : Session (List (BitVec 8)) :=
  { state := { sessionVersion := 0#32
               localIdentity := ⟨pk0⟩
               remoteIdentity := none
               rootKey := 0#256
               previousCounter := 0#32
               senderChain := none
               receiverChains := []
               pendingPreKey := false
               pqRatchetState := [] }
    pendingPreKey := none
    pendingKyberPreKey := none
    localRegistrationId := 0#32
    remoteRegistrationId := 0#32
    aliceBaseKey := [] }

private def succInitRecGhost : RecordGhost :=
  { prevCap := 0#64, prevPtr := 8#64, cur := some succInitSessGhost }

private def succInitRecVal : SessionRecord (List (BitVec 8)) :=
  { currentSession := some succInitSessVal }

private theorem succInit_localIk_eq :
    vecGhostAt A₀ succInitSessGhost.localIk succInitArenaB =
      (succInitArenaB ↦₆₄ 33#64) ∗
      ((succInitArenaB + 8#64) ↦₆₄ (succInitArenaB + 512#64)) ∗
      ((succInitArenaB + 16#64) ↦₆₄ 33#64) ∗
      ((succInitArenaB + 512#64) ↦ₛ pk0.serialize) := by
  unfold vecGhostAt vecU8At vecHeader succInitSessGhost A₀
  simp only [pk0_serialize_length, BitVec.ofNat_eq_ofNat, true_and,
    show (33#64 : BitVec 64).toNat < 2 ^ 63 by decide,
    show (33#64 : BitVec 64).toNat - 33 = 0 by decide,
    memRegion_zero, emp_sepConj, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd]
  have hpure : (33 ≤ (33#64 : BitVec 64).toNat ∧ succInitArenaB + 512#64 ≠ 0#64) ↔ True := by
    unfold succInitArenaB; decide
  have hif : ¬ ((33#64 : BitVec 64) = 0#64) := by decide
  rw [propext hpure, pure_true, emp_sepConj]
  simp only [hif, ↓reduceIte]
  sep_ac_rfl

private theorem succInit_emptyVecU8At_eq (off : BitVec 64) :
    vecU8At A₀ (succInitArenaB + off) 0#64 1#64 [] =
      ((succInitArenaB + off) ↦₆₄ 0#64) ∗
      ((succInitArenaB + off + 8#64) ↦₆₄ 1#64) ∗
      ((succInitArenaB + off + 16#64) ↦₆₄ 0#64) := by
  unfold vecU8At vecHeader A₀
  simp only [List.length_nil, BitVec.ofNat_eq_ofNat, true_and,
    show (0#64 : BitVec 64).toNat < 2 ^ 63 by decide,
    ↓reduceIte, sepConj_emp,
    BitVec.add_assoc]
  have hpure : (0 ≤ (0#64 : BitVec 64).toNat ∧ (1#64 : BitVec 64) ≠ 0#64) ↔ True := by decide
  rw [propext hpure, pure_true, sepConj_emp]

private theorem succInit_rootKey_eq :
    vecU8At A₀ (succInitArenaB + 48#64) 32#64 (succInitArenaB + 560#64) (keyToBytes32 0#256) =
      ((succInitArenaB + 48#64) ↦₆₄ 32#64) ∗
      ((succInitArenaB + 56#64) ↦₆₄ (succInitArenaB + 560#64)) ∗
      ((succInitArenaB + 64#64) ↦₆₄ 32#64) ∗
      ((succInitArenaB + 560#64) ↦ₛ keyToBytes32 0#256) := by
  have hlen : (keyToBytes32 0#256).length = 32 := by simp [keyToBytes32]
  unfold vecU8At vecHeader A₀
  simp only [hlen, BitVec.ofNat_eq_ofNat, true_and,
    show (32#64 : BitVec 64).toNat < 2 ^ 63 by decide,
    show (32#64 : BitVec 64).toNat - 32 = 0 by decide,
    memRegion_zero, emp_sepConj, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd]
  have hpure : (32 ≤ (32#64 : BitVec 64).toNat ∧ succInitArenaB + 560#64 ≠ 0#64) ↔ True := by
    unfold succInitArenaB; decide
  have hif : ¬ ((32#64 : BitVec 64) = 0#64) := by decide
  rw [propext hpure, pure_true, emp_sepConj]
  simp only [hif, ↓reduceIte]
  sep_ac_rfl

private theorem succInit_chains_eq :
    vecAt A₀ 104 8 (chainAt A₀) (succInitArenaB + 72#64) 0#64 8#64 [] =
      ((succInitArenaB + 72#64) ↦₆₄ 0#64) ∗
      ((succInitArenaB + 80#64) ↦₆₄ 8#64) ∗
      ((succInitArenaB + 88#64) ↦₆₄ 0#64) := by
  unfold vecAt vecHeader vecBuf A₀
  simp only [List.length_nil, BitVec.ofNat_eq_ofNat, true_and,
    show (0#64 : BitVec 64).toNat * 104 < 2 ^ 63 by decide,
    ↓reduceIte, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd]
  have hpure : (0 ≤ (0#64 : BitVec 64).toNat ∧ (8#64 : BitVec 64) ≠ 0#64) ↔ True := by decide
  rw [propext hpure, pure_true, sepConj_emp]

private theorem succInit_sessionStateAt_satisfiable :
    ∃ m : Memory, m ⊨ sessionStateAt A₀ succInitArenaB succInitSessGhost succInitSessVal.state ∗ emp := by
  let B := succInitArenaB
  let mBase := Memory.empty.mapFresh B 1024 Perm.rw
  have hunm : Unmapped Memory.empty B 1024 := fun _ _ => rfl
  have hsat0 := satisfies_mapFresh_unmapped (satisfies_emp Memory.empty) hunm
  have h0 : ValidMemPlaced mBase B (memRegion (B + BitVec.ofNat 64 0) 1024 ∗ emp) :=
    ⟨mBase, by simpa only [BitVec.add_zero] using hsat0, rfl, Memory.KeepsFrozen.refl mBase⟩
  have h1 := h0.step64 (off' := 8) (rem' := 1016) 33#64
  have h2 := h1.step64 (off' := 16) (rem' := 1008) (B + 512#64)
  have h3 := h2.step64 (off' := 24) (rem' := 1000) 33#64
  have h4 := h3.step64 (off' := 32) (rem' := 992) 0#64
  have h5 := h4.step64 (off' := 40) (rem' := 984) 1#64
  have h6 := h5.step64 (off' := 48) (rem' := 976) 0#64
  have h7 := h6.step64 (off' := 56) (rem' := 968) 32#64
  have h8 := h7.step64 (off' := 64) (rem' := 960) (B + 560#64)
  have h9 := h8.step64 (off' := 72) (rem' := 952) 32#64
  have h10 := h9.step64 (off' := 80) (rem' := 944) 0#64
  have h11 := h10.step64 (off' := 88) (rem' := 936) 8#64
  have h12 := h11.step64 (off' := 96) (rem' := 928) 0#64
  have h13 := h12.step64 (off' := 104) (rem' := 920) 0#64
  have h14 := h13.step64 (off' := 112) (rem' := 912) 1#64
  have h15 := h14.step64 (off' := 120) (rem' := 904) 0#64
  have h16 := h15.step64 (off' := 128) (rem' := 896) 0#64
  have h17 := h16.step64 (off' := 136) (rem' := 888) 1#64
  have h18 := h17.step64 (off' := 144) (rem' := 880) 0#64
  have h19 := h18.step64 (off' := 152) (rem' := 872) noneCap
  have h20 := h19.stepSkip (off' := 248) (rem' := 776) 96
  have h21 := h20.step64 (off' := 256) (rem' := 768) noneCap
  have h22 := h21.stepSkip (off' := 296) (rem' := 728) 40
  have h23 := h22.step64 (off' := 304) (rem' := 720) noneCap
  have h24 := h23.stepSkip (off' := 328) (rem' := 696) 24
  have h25 := h24.step32 (off' := 332) (rem' := 692) 0#32
  have h26 := h25.step32 (off' := 336) (rem' := 688) 0#32
  have h27 := h26.stepBytes (off' := 344) (rem' := 680) 8 (List.replicate 8 0#8) rfl
  have h28 := h27.stepDrop (off' := 512) (rem' := 512) 168
  have h29 := h28.stepBytes (off' := 545) (rem' := 479) 33 pk0.serialize pk0_serialize_length
  have h30 := h29.stepDrop (off' := 560) (rem' := 464) 15
  have h31 := h30.stepBytes (off' := 592) (rem' := 432) 32 (keyToBytes32 0#256)
    (by simp [keyToBytes32])
  have h32 := h31.stepDrop (off' := 1024) (rem' := 0) 432
  rcases h32 with ⟨m, hsat, _, _⟩
  refine ⟨m, ?_⟩
  rw [memRegion_zero, emp_sepConj, sepConj_emp] at hsat
  dsimp only [B] at hsat
  unfold sessionStateAt
  rw [sepConj_emp, satisfies_pure_sepConj]
  refine ⟨⟨deserialize_pk0_serialize, rfl, rfl, rfl, rfl, pk0_serialize_length, fun h => nomatch h⟩,
    ?_⟩
  change m ⊨
    vecGhostAt A₀ succInitSessGhost.localIk succInitArenaB ∗
    vecU8At A₀ (succInitArenaB + 24#64) 0#64 1#64 [] ∗
    vecU8At A₀ (succInitArenaB + 48#64) 32#64 (succInitArenaB + 560#64) (keyToBytes32 0#256) ∗
    vecAt A₀ 104 8 (chainAt A₀) (succInitArenaB + 72#64) 0#64 8#64 [] ∗
    vecU8At A₀ (succInitArenaB + 96#64) 0#64 1#64 [] ∗
    vecU8At A₀ (succInitArenaB + 120#64) 0#64 1#64 [] ∗
    optSenderChainAt A₀ (succInitArenaB + 144#64) none none ∗
    optTailVecAt A₀ 48 (succInitArenaB + 248#64) none ∗
    optTailVecAt A₀ 32 (succInitArenaB + 296#64) none ∗
    ((succInitArenaB + 328#64) ↦₃₂ 0#32) ∗
    ((succInitArenaB + 332#64) ↦₃₂ 0#32) ∗
    ((succInitArenaB + 336#64) ↦ₛ List.replicate 8 0#8)
  unfold optSenderChainAt optTailVecAt
  rw [succInit_localIk_eq, succInit_emptyVecU8At_eq 24#64, succInit_rootKey_eq,
    succInit_chains_eq, succInit_emptyVecU8At_eq 96#64, succInit_emptyVecU8At_eq 120#64]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.reduceSub] at hsat ⊢
  refine Eq.mp (congrArg (fun P => m ⊨ P) ?_) hsat
  sep_ac_rfl

private theorem succInit_recordGhostValid :
    RecordGhostValid succInitRecGhost succInitRecVal := by
  unfold RecordGhostValid succInitRecGhost succInitRecVal
  dsimp only
  refine ⟨?_, ?_⟩
  · unfold sessionModelRel succInitSessGhost succInitSessVal
    refine ⟨trivial, trivial, rfl, by decide, by decide⟩
  · obtain ⟨m, hm⟩ := succInit_sessionStateAt_satisfiable
    exact ⟨A₀, succInitArenaB, m, emp, hm⟩

private theorem succInit_aliceInitiatedBounds :
    AliceInitiatedAnyCkBounds succInitSessGhost succInitSessVal where
  localIk_le := by rw [show succInitSessGhost.localIk.bytes = pk0.serialize from rfl, pk0_serialize_length]; decide
  remoteIk_le := Nat.zero_le _
  sender_le := fun _ h => nomatch h
  recv_shape := Or.inl rfl
  recv_ghost_le := fun _ h => nomatch h
  pending_le := Nat.zero_le _
  kyber_eq := Or.inl rfl
  alice_le := Nat.zero_le _
  pq_le := Nat.zero_le _
  enc_le := of_decide_eq_true (by with_unfolding_all rfl)

private def succInitGhost : InitGhost :=
  { peer := succInitPeerGhost
    peerA := 0#64
    me := succInitMeGhost
    meA := 0#64
    stores := 0#64
    ret := 0#64
    coinsP := 0#64
    F := runFiles succInitInputs
    coins := succInitT0.toList
    bundleA := 0#64
    bundle := bundleVE succInitB0
    spkSigPtr := 0#64
    kpkSigPtr := 0#64
    kpkPtr := 0#64 }

private def succInitSpqrGhost : InitialStateGhost :=
  { pA := 0#64
    ret := 0#64
    akPtr := 1#64
    p := { direction := .a2b
           version := .v1
           minVersion := .v1
           authKey := []
           chainParams := ChainParams.default } }

private def succInitParams : W3BinaryInitParams :=
  { x := succInitGhost
    F := fun s _ => s
    peerKey := ⟨⟨succInitB0.idPub⟩⟩
    x_spqr := succInitSpqrGhost
    g_rec := succInitRecGhost
    r_rec := succInitRecVal }

private def succInitAddrCall : AddressCall :=
  { out := 0#64
    p := 0#64
    bs := bytesOfString (partyAddress .B).text }

private def succInitCall : RunCall :=
  { i := succInitInputs
    c := .init ⟨succInitPeerGhost.name.bytes, succInitPeerGhost.device⟩ (bytesOfString bundleDir)
    a := some none
    res := 0#64
    call := 0#64
    stores := 0#64
    inp := 0#64
    coins := 0#64 }

private theorem succInit_w3BinaryInitDom :
    W3BinaryInitDom succInitCall.c succInitInputs succInitParams := by
  intro peerAddr dir hc
  change CallV.init ⟨succInitPeerGhost.name.bytes, succInitPeerGhost.device⟩
      (bytesOfString bundleDir) = CallV.init peerAddr dir at hc
  injection hc with hp _
  subst hp
  refine ⟨rfl, ?_, rfl, Nat.zero_le _, succInit_recordGhostValid, ?_⟩
  · change (utf8 (partyAddressName .B)).length ≤ 40
    rw [succ_utf8_eq_kutf8]
    decide
  · unfold RecordAliceInitiatedAnyCkBounds succInitParams succInitRecGhost succInitRecVal
    intro G sess hG hS
    injection hG with hG'
    injection hS with hS'
    subst hG' hS'
    exact succInit_aliceInitiatedBounds

private theorem cliMainSetupEnv_some_len3 (i : Inputs) (ag : AddressCall)
    (hlen : i.argv.length = 3) :
    CliMainSetupEnv uuidTryParse i (some ag) false
      (addressEvents uuidTryParse ag.bs ++ succInitCoinsEvents i) := by
  let evsSetup := addressEvents uuidTryParse ag.bs ++ succInitCoinsEvents i
  have hM1 : M1PhaseEnv i.argv.length [] := Or.inl rfl
  have hM2 : M2CollectEnv i.argv.length [] := by
    rw [hlen]
    exact Or.inr ⟨[], [], rfl, Or.inl rfl,
      Or.inr ⟨[], [], rfl, Or.inl rfl,
        Or.inr ⟨[], [], rfl, Or.inl rfl, rfl⟩⟩⟩
  have hAddr : AddressEnv uuidTryParse ag (addressEvents uuidTryParse ag.bs) :=
    addressEnv_events uuidTryParse ag
  have hM3 : M3PhaseEnv false i.stdin (initFsState (cliInputs i)).files (utf8 "coins")
      (succInitCoinsEvents i) :=
    Or.inr ⟨[], succInitCoinsEvents i, rfl, rfl,
      Or.inr ⟨succInitCoinsEvents i, [], (List.append_nil _).symm,
        succInitCoinsEvents_readFileEnv i, FreeOnlyEvs.nil⟩⟩
  exact Or.inr ⟨[], evsSetup, rfl, hM1,
    Or.inr ⟨[], evsSetup, rfl, hM2,
      Or.inr ⟨addressEvents uuidTryParse ag.bs, succInitCoinsEvents i, rfl, hAddr, hM3⟩⟩⟩

private theorem w3BoundedEvs_singleton_alloc {maxOps maxReq req : Nat}
    (hops : 1 ≤ maxOps) (hreq : req ≤ maxReq) :
    W3BoundedEvs maxOps maxReq [AllocEvent.alloc req] := by
  refine ⟨hops, fun ev hev => ?_⟩
  rcases List.mem_singleton.mp hev with rfl
  exact ⟨hreq, Nat.le_of_ble_eq_true rfl⟩

private theorem spqrBoundedEvs_3700 :
    SpqrBoundedEvs 128 (4 * succInitSpqrGhost.p.authKey.length + 4096) [AllocEvent.alloc 3700] := by
  refine ⟨by decide, fun ev hev => ?_⟩
  rcases List.mem_singleton.mp hev with rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · show (AllocEvent.alloc 3700).withinMaxAlloc
    decide
  · show (AllocEvent.alloc 3700).reqBytes ≤ 4 * 0 + 4096
    decide
  · intro _ _ h
    cases h
  · intro _ _ _ h
    cases h

private theorem sublist_of_left {l a b : List AllocEvent}
    (h : List.Sublist l a) : List.Sublist l (a ++ b) := by
  simpa using List.Sublist.append h (List.nil_sublist b)

private theorem sublist_of_right {l a b : List AllocEvent}
    (h : List.Sublist l b) : List.Sublist l (a ++ b) := by
  induction a with
  | nil => simpa using h
  | cons x xs ih => exact List.Sublist.cons x ih

/-- Concrete `.init` binary-kit success-path non-vacuity witness on
`RealCliMainBinaryEnvOf (mkBinaryKitRealCalleeEnvs img S X W₀) i₀` at `W₀ = succInitCliHooks`
(exhibiting the exact Block 594 `address_text` trace on `Bob.1`, `.ok` `Dir::get` reads without
`22`-byte error allocations, and hook-model read disjuncts). -/
theorem realCliMainBinaryEnvOf_concrete_init_succ_nonvacuous [LibsignalPlacement]
    (img : Arm64.Obj.Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) :
    ∃ (W₀ : CliHooks) (i₀ : Inputs) (evs : List AllocEvent),
      CliPqxdhInputs ⟨W₀.C, W₀.Q⟩ i₀ ∧
      (∃ peer dir, parseArgs uuidTryParse (i₀.argv.map bytesOfString) = some (.init peer dir)) ∧
      InitSuccMainEnv img W₀ i₀ evs ∧
      RealCliMainBinaryEnvOf (mkBinaryKitRealCalleeEnvs img S X W₀) i₀ evs ∧
      List.Sublist
        [AllocEvent.alloc 36, AllocEvent.realloc 1 36 72,
         AllocEvent.alloc 8, AllocEvent.free 1 8] evs ∧
      AllocEvent.alloc 1569 ∈ evs ∧
      AllocEvent.alloc 3700 ∈ evs ∧
      AllocEvent.alloc 416 ∈ evs := by
  obtain ⟨st₁, x₁, g₁, hs₁, hwf₁, hModel⟩ := pqInitModel_succInitW0_uniform
  obtain ⟨⟨ikBs, hik⟩, ⟨regBs, hreg⟩, ⟨spkBs, hspk⟩, ⟨kpkBs, hkpk⟩, hopk⟩ :=
    succInit_all_bundle_reads
  let ownBs := textBytes (partyAddress .A).text
  have hownGet : StoresGhost.opened.identity.own.get cliIo.rd (runFiles succInitInputs)
      (utf8 "address") = .ok ownBs :=
    succInit_ownAddr_read_eq_ok
  have hownRd : cliIo.rd (runFiles succInitInputs)
      (pathOf StoresGhost.opened.identity.own.path (utf8 "address")) = .ok ownBs :=
    succInit_ownAddr_read_eq_ok
  let dir := bytesOfString bundleDir
  have hdirNe : dir ≠ [] := by
    change [0x62#8, 0x75#8, 0x6e#8, 0x64#8, 0x6c#8, 0x65#8] ≠ []
    decide
  let evsSetup := addressEvents uuidTryParse succInitAddrCall.bs ++ succInitCoinsEvents succInitInputs
  have hCoinsNe : succInitCoinsEvents succInitInputs ≠ [] := by
    unfold succInitCoinsEvents
    rw [succInit_coins_read_eq_ok]
    dsimp only
    unfold allocBytes1Events
    have hlen : succInitT0.toList.length = initiateTapeLen := succInitT0.2
    rw [hlen]
    decide
  have hSetupEnv :
      CliMainSetupEnv uuidTryParse succInitInputs (some succInitAddrCall) false evsSetup :=
    cliMainSetupEnv_some_len3 succInitInputs succInitAddrCall rfl
  have hAddrParse : addrParse uuidTryParse succInitAddrCall.bs =
      some ⟨succInitPeerGhost.name.bytes, succInitPeerGhost.device⟩ :=
    succ_addrParse_bytesOfString .B
  let eR0Get := dirGetCacheMissOkWitnessEvents StoresGhost.opened.identity.own (utf8 "address") ownBs
  let evsR0 := eR0Get ++ (addressEvents uuidTryParse ownBs ++ [])
  have hR0 : R0BinSuccEnv succInitCall evsR0 :=
    ⟨ownBs, hownGet, eR0Get, addressEvents uuidTryParse ownBs ++ [], rfl,
      dirGetCacheMissOkBinEnv_witness rfl hownRd,
      addressEvents uuidTryParse ownBs, [], rfl, rfl, FreeOnlyEvs.nil⟩
  let evs1a := bundleFileReadWitnessEvents dir (utf8 "identity-key") ikBs
  have h1a : R1aBinSuccEnv cliIo.rd (runFiles succInitInputs) dir evs1a :=
    bundleFileReadBinSuccEnv_witness hdirNe hik
  let evsDeser : List AllocEvent :=
    rustAllocEvents 64 1 ++ (rustAllocEvents kemPkLen 1 ++ (rustAllocEvents 64 1 ++ []))
  have hDeser : R1bDeserBinSuccEnv evsDeser :=
    ⟨rustAllocEvents 64 1, _, rfl, rfl,
      rustAllocEvents kemPkLen 1, _, rfl, rfl,
      rustAllocEvents 64 1, [], rfl, rfl, FreeOnlyEvs.nil⟩
  let eRegB := bundleFileReadWitnessEvents dir (utf8 "registration-id") regBs
  let eSpkB := bundleFileReadWitnessEvents dir (utf8 "signed-pre-key") spkBs
  let eKpkB := bundleFileReadWitnessEvents dir (utf8 "kyber-pre-key") kpkBs
  let eOpkB := bundleFileReadWitnessEvents dir (utf8 "one-time-pre-key") []
  let evs1b := eRegB ++ (eSpkB ++ (eKpkB ++ (eOpkB ++ evsDeser)))
  have h1b : R1bBinSuccEnv cliIo.rd (runFiles succInitInputs) dir evs1b :=
    ⟨eRegB, _, rfl, bundleFileReadBinSuccEnv_witness hdirNe hreg,
      eSpkB, _, rfl, bundleFileReadBinSuccEnv_witness hdirNe hspk,
      eKpkB, _, rfl, bundleFileReadBinSuccEnv_witness hdirNe hkpk,
      eOpkB, evsDeser, rfl, bundleFileReadBinSuccEnv_witness hdirNe hopk, hDeser⟩
  let remVal := succInitPeerGhost.val
  have hpeersRd : cliIo.rd (runFiles succInitInputs)
      (pathOf StoresGhost.opened.identity.peers.path remVal.name) = .ok [] :=
    succInit_peers_read_eq_ok_nil
  have hpeersGet : StoresGhost.opened.identity.peers.get cliIo.rd (runFiles succInitInputs)
      remVal.name = .ok [] := hpeersRd
  have hsessRd : cliIo.rd (runFiles succInitInputs)
      (pathOf StoresGhost.opened.sessions.path (addressText remVal)) = .ok [] :=
    succInit_sess_read_eq_ok_nil
  have hsessGet : StoresGhost.opened.sessions.get cliIo.rd (runFiles succInitInputs)
      (addressText remVal) = .ok [] := hsessRd
  have hikpGet : StoresGhost.opened.identity.own.get cliIo.rd (runFiles succInitInputs)
      (utf8 "identity-key-pair") = .ok succInitIdKeyPairBytes :=
    succInit_idKeyPair_read_eq_ok
  have hregIdGet : StoresGhost.opened.identity.own.get cliIo.rd (runFiles succInitInputs)
      (utf8 "registration-id") = .ok (le32 0#32) :=
    succInit_regId_read_eq_ok
  have hremNameNe : remVal.name ≠ [] := by
    change utf8 (partyAddressName .B) ≠ []
    rw [succ_utf8_eq_kutf8]
    decide
  let ePeersGet := dirGetCacheMissOkWitnessEvents StoresGhost.opened.identity.peers remVal.name []
  let evsS1Trust := rustAllocEvents 32 8 ++ ((ePeersGet ++ []) ++ [])
  have hS1Trust : W3IdTrustBinSuccEnv cliIo.rd (runFiles succInitInputs) remVal evsS1Trust :=
    ⟨by decide, rustAllocEvents 32 8, _, rfl, rfl,
      ePeersGet ++ [], [], rfl,
      ⟨ePeersGet, [], rfl, dirGetCacheMissOkBinEnv_witness rfl hpeersRd, FreeOnlyEvs.nil⟩,
      FreeOnlyEvs.nil⟩
  let eAddrText := addrTextExactEvents remVal
  let eSessGet := dirGetCacheMissOkWitnessEvents StoresGhost.opened.sessions (addressText remVal) []
  let evsS1Load := rustAllocEvents 24 8 ++ ((eAddrText ++ (eSessGet ++ ([] ++ []))) ++ [])
  have hS1Load : W3SessLoadBinSuccEnv cliIo.rd (runFiles succInitInputs) remVal evsS1Load :=
    ⟨hsessGet, by decide, rustAllocEvents 24 8, _, rfl, rfl,
      eAddrText ++ (eSessGet ++ ([] ++ [])), [], rfl,
      ⟨eAddrText, _, rfl, addrTextBinSuccEnv_exact remVal,
        eSessGet, [] ++ [], rfl, dirGetCacheMissOkBinEnv_witness rfl hsessRd,
        [], [], rfl, rfl, FreeOnlyEvs.nil⟩,
      FreeOnlyEvs.nil⟩
  let eIkpGet := dirGetCacheMissOkWitnessEvents StoresGhost.opened.identity.own
    (utf8 "identity-key-pair") succInitIdKeyPairBytes
  let evsS2Kp := rustAllocEvents 16 8 ++ ((eIkpGet ++ ([] ++ [])) ++ [])
  have hS2Kp : W3IdKeyPairBinSuccEnv cliIo.rd (runFiles succInitInputs) evsS2Kp :=
    ⟨succInitIdKeyPairBytes, hikpGet, by decide, rustAllocEvents 16 8, _, rfl, rfl,
      eIkpGet ++ ([] ++ []), [], rfl,
      ⟨eIkpGet, [] ++ [], rfl, dirGetCacheMissOkBinEnv_witness rfl succInit_idKeyPair_read_eq_ok,
        [], [], rfl, IkpSubEnv.of_cleanup IkpPostCleanupEnv.nil, FreeOnlyEvs.nil⟩,
      FreeOnlyEvs.nil⟩
  let evsS3 : List AllocEvent := [AllocEvent.alloc 1569]
  let evsS4Pre : List AllocEvent := []
  let evsS4Spqr : List AllocEvent := [AllocEvent.alloc 3700]
  let evsS4Post : List AllocEvent := [AllocEvent.alloc 416]
  let evsS5Pre : List AllocEvent := []
  let eRegIdGet := dirGetCacheMissOkWitnessEvents StoresGhost.opened.identity.own
    (utf8 "registration-id") (le32 0#32)
  let evsS5Reg := rustAllocEvents 16 8 ++ ((eRegIdGet ++ ([] ++ [])) ++ [])
  have hS5Reg : W3IdRegIdBinSuccEnv cliIo.rd (runFiles succInitInputs) evsS5Reg :=
    ⟨le32 0#32, hregIdGet, rfl, by decide, rustAllocEvents 16 8, _, rfl, rfl,
      eRegIdGet ++ ([] ++ []), [], rfl,
      ⟨eRegIdGet, [] ++ [], rfl, dirGetCacheMissOkBinEnv_witness rfl succInit_regId_read_eq_ok,
        [], [], rfl, rfl, FreeOnlyEvs.nil⟩,
      FreeOnlyEvs.nil⟩
  let ePkSer := publicKeySerializeEvents
  let eSaveTail := rustAllocEvents remVal.name.length 1 ++ []
  let evsS5Save :=
    rustAllocEvents 32 8 ++ ((ePeersGet ++ ([] ++ (ePkSer ++ eSaveTail))) ++ [])
  have hS5Save : W3IdSaveBinSuccEnv cliIo.rd (runFiles succInitInputs) remVal
      succInitParams.peerKey evsS5Save :=
    ⟨[], hpeersGet, hremNameNe, by decide, rustAllocEvents 32 8, _, rfl, rfl,
      ePeersGet ++ ([] ++ (ePkSer ++ eSaveTail)), [], rfl,
      ⟨ePeersGet, _, rfl, dirGetCacheMissOkBinEnv_witness rfl hpeersRd,
        [], _, rfl, FreeOnlyEvs.nil,
        ePkSer, eSaveTail, rfl, rfl,
        rustAllocEvents remVal.name.length 1, [], rfl, rfl,
        dirPutTailEnv_miss_nil (fun _ hm => nomatch hm)⟩,
      FreeOnlyEvs.nil⟩
  let encLen := (lenField 1 (encSessionMem succInitSessGhost succInitSessVal)).length
  let eSerSome := serializeSomeExactEvents succInitSessGhost succInitSessVal
  have hSerSome : SerializeSomeCancelEnv succInitSessGhost succInitSessVal eSerSome :=
    ⟨segCloneEvents succInitSessGhost succInitSessVal.state ++ rustAllocEvents encLen 1,
      dropClonedSessionEvents succInitSessGhost succInitSessVal.state, rfl,
      ⟨segCloneEvents succInitSessGhost succInitSessVal.state, rustAllocEvents encLen 1,
        rfl, rfl, rfl⟩,
      rfl⟩
  let evsS5Store := rustAllocEvents 32 8 ++ ((eAddrText ++ (eSerSome ++ [])) ++ [])
  have hS5Store : W3SessStoreBinSuccEnv remVal succInitSessGhost succInitSessVal
      succInitRecVal evsS5Store :=
    ⟨by decide, rustAllocEvents 32 8, _, rfl, rfl,
      eAddrText ++ (eSerSome ++ []), [], rfl,
      ⟨eAddrText, eSerSome ++ [], rfl, addrTextBinSuccEnv_exact remVal,
        eSerSome, [], rfl, hSerSome, dirPutTailEnv_miss_nil (fun _ hm => nomatch hm)⟩,
      FreeOnlyEvs.nil⟩
  let evs1c :=
    ((((evsS1Trust ++ (rustAllocEvents 33 1 ++ (rustAllocEvents 1569 1 ++ evsS1Load))) ++
       (evsS2Kp ++ rustAllocEvents 1568 1)) ++
      evsS3) ++
     (evsS4Pre ++ (evsS4Spqr ++ evsS4Post))) ++
    (evsS5Pre ++ (evsS5Reg ++ (evsS5Save ++ evsS5Store)))
  have hSlot : W3InitBinSuccSlotEnv succInitParams evs1c :=
    ⟨succInitSessGhost, succInitSessVal,
      evsS1Trust, evsS1Load, evsS2Kp, evsS3,
      evsS4Pre, evsS4Spqr, evsS4Post,
      evsS5Pre, evsS5Reg, evsS5Save, evsS5Store,
      rfl, rfl, rfl, rfl,
      hS1Trust, hS1Load, hS2Kp,
      w3BoundedEvs_singleton_alloc (by decide) (by decide),
      w3BoundedEvs_nil 1 33,
      spqrBoundedEvs_3700,
      w3BoundedEvs_singleton_alloc (by decide) (by decide),
      w3BoundedEvs_nil 4 68,
      hS5Reg, hS5Save, hS5Store⟩
  have hAddrSubLoad : List.Sublist eAddrText evsS1Load :=
    sublist_of_right (sublist_of_left (sublist_of_left (List.Sublist.refl eAddrText)))
  have hAddrSub1c : List.Sublist eAddrText evs1c :=
    sublist_of_left (sublist_of_left (sublist_of_left (sublist_of_left
      (sublist_of_right (sublist_of_right (sublist_of_right hAddrSubLoad))))))
  have hm1569_1c : AllocEvent.alloc 1569 ∈ evs1c :=
    List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_singleton_self _)))
  have hm3700_1c : AllocEvent.alloc 3700 ∈ evs1c :=
    List.mem_append_left _ (List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_left _ (List.mem_singleton_self _))))
  have hm416_1c : AllocEvent.alloc 416 ∈ evs1c :=
    List.mem_append_left _ (List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_right _ (List.mem_singleton_self _))))
  let eM5Peers := m5LoopAWitnessEvents StoresGhost.opened.identity.peers.path remVal.name
  let eM5Sess := m5LoopAWitnessEvents StoresGhost.opened.sessions.path (addressText remVal)
  let evsM5 := (eM5Peers ++ []) ++ ((eM5Sess ++ []) ++ [])
  have hM5 : IterConcatEnv (fun dn => IterConcatEnv (fun name => M5LoopAEntryEnv dn.1 name) dn.2)
      [(StoresGhost.opened.identity.peers.path, [remVal.name]),
       (StoresGhost.opened.sessions.path, [addressText remVal])] evsM5 :=
    ⟨eM5Peers ++ [], (eM5Sess ++ []) ++ [], rfl,
      ⟨eM5Peers, [], rfl, m5LoopAEntryEnv_witness _ _, rfl⟩,
      ⟨eM5Sess ++ [], [], rfl, ⟨eM5Sess, [], rfl, m5LoopAEntryEnv_witness _ _, rfl⟩, rfl⟩⟩
  let fullLog := evsSetup ++ ((evsR0 ++ ((evs1a ++ evs1b) ++ evs1c)) ++ evsM5)
  have hParse : parseArgs uuidTryParse (succInitInputs.argv.map bytesOfString) =
      some succInitCall.c :=
    parseArgs_init .B bundleDir
  have hCliInputs : CliPqxdhInputs ⟨succInitCliHooks.C, succInitCliHooks.Q⟩ succInitInputs :=
    ⟨succInitParty0, succInitParty0_inSpecDomain, Or.inl ⟨rfl, succInitB0, succInitT0, rfl⟩⟩
  have hInitSucc : InitSuccMainEnv img succInitCliHooks succInitInputs fullLog :=
    ⟨succInitParty0, succInitB0, succInitT0, st₁, x₁, g₁, succInitAddrCall, succInitCall, dir,
      succInitParams, evsSetup, evsR0, evs1a, evs1b, evs1c, evsM5,
      succInitParty0_inSpecDomain, rfl, rfl, hs₁, hwf₁, hModel,
      rfl, hAddrParse, rfl, hParse, rfl,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, hCoinsNe, rfl,
      hSetupEnv, hR0, h1a, h1b, succInit_w3BinaryInitDom, hSlot, hM5,
      hAddrSub1c, hm1569_1c, hm3700_1c, hm416_1c⟩
  have hSub : RealCliMainBinaryEnvOf (mkBinaryKitRealCalleeEnvs img S X succInitCliHooks)
      succInitInputs fullLog :=
    initSuccMainEnv_sub_realCliMainBinaryEnvOf img S X succInitCliHooks succInitInputs
      fullLog hInitSucc
  have hAddrSubFull :
      List.Sublist
        [AllocEvent.alloc 36, AllocEvent.realloc 1 36 72,
         AllocEvent.alloc 8, AllocEvent.free 1 8] fullLog := by
    rw [← succInit_addrText_events_eq]
    exact sublist_of_right (sublist_of_left (sublist_of_right (sublist_of_right hAddrSub1c)))
  have lift1c {ev : AllocEvent} (hm : ev ∈ evs1c) : ev ∈ fullLog :=
    List.mem_append_right _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_append_right _ hm)))
  exact ⟨succInitCliHooks, succInitInputs, fullLog, hCliInputs,
    ⟨⟨succInitPeerGhost.name.bytes, succInitPeerGhost.device⟩, dir, hParse⟩, hInitSucc, hSub,
    hAddrSubFull, lift1c hm1569_1c, lift1c hm3700_1c, lift1c hm416_1c⟩

/-- Alias form of `realCliMainBinaryEnvOf_concrete_init_succ_nonvacuous` on
`realCliMainBinaryKitEnvOf img S X W₀ i₀`. -/
theorem realCliMainBinaryKitEnvOf_concrete_init_succ_nonvacuous [LibsignalPlacement]
    (img : Arm64.Obj.Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) :
    ∃ (W₀ : CliHooks) (i₀ : Inputs) (evs : List AllocEvent),
      CliPqxdhInputs ⟨W₀.C, W₀.Q⟩ i₀ ∧
      (∃ peer dir, parseArgs uuidTryParse (i₀.argv.map bytesOfString) = some (.init peer dir)) ∧
      InitSuccMainEnv img W₀ i₀ evs ∧
      realCliMainBinaryKitEnvOf img S X W₀ i₀ evs ∧
      List.Sublist
        [AllocEvent.alloc 36, AllocEvent.realloc 1 36 72,
         AllocEvent.alloc 8, AllocEvent.free 1 8] evs ∧
      AllocEvent.alloc 1569 ∈ evs ∧
      AllocEvent.alloc 3700 ∈ evs ∧
      AllocEvent.alloc 416 ∈ evs :=
  realCliMainBinaryEnvOf_concrete_init_succ_nonvacuous img S X

end LibsignalBinary.Proofs.PeakBudget.RealMainEnvNonVacSuccInit
