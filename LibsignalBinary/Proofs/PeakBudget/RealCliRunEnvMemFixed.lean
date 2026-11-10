/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefsBudgetAux
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget
public import LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
public import LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
public import LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge
public import LibsignalBinary.Proofs.PeakBudget.RealCliDecPkLinked
public import LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMem
public import LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemSlots
public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortPlacedBudget

/-!
# Over-Cap `ReadFileRuleEnvFixed` Store-Kit and Whole-`run` Envelope Bridges

Establishes `ReadFileRuleEnvFixed` monotonicity and non-`OverCapFile` collapse under
`CliPqxdhInputs P i` (where only `last-resort-kyber-pre-keys/*.base-keys` files can exceed the
`2 MiB` cap), defines `*Fixed` binary store-kit budgets and `W4` `kpkMark` envelopes
(`mkBinaryKitRealCalleeEnvsFixed`, `realCliRunBinaryKitEnvOfFixed`, `realCliMainBinaryKitEnvOfFixed`),
and proves whole-`run` `RunEnv` inclusion into `realCliRunBinaryKitEnvOfFixed`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed

open Arm64 (FsPath FsState normalizePath splitSlash subroutine_ok)
open Arm64.Obj (Image)
open Arm64.Process (ProcessInputs bytesOfString initFsState)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession
  (IdentityKey OutgoingTripleRatchet PublicKey SessionState ShaCompress SignalMessage)
open CryptoGames.LibsignalSessionApi (Direction PreKeySignalMessage Session SessionRecord)
open CryptoVerification
  (LibsignalHooks LibsignalPlacement lsmpl lsρ withLsCodeLoaded)
open CryptoVerification.E2E
  (PEParams PreKeyMessageFields UnreachedPqxdhPrimitives initiateTapeLen pqxdhSpqrModel wirePrekey
   wireWhisper)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.E2E.Record.Placed (lsProg_52)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles SessionStoreSpec withLsCodeRoLoaded)
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity (IdentityStoreSpec)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal RecordGhost)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.LibsignalTripleRatchet (DoReserveCall)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost SessionGhost uuidTryParse)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession
  (CliHooks CliPqxdhInputs Inputs baseKeysFile bundleDir coinsFile encodeDir fileCapBytes
   lsReadFileSym pqInitInputs pqInputs pqRecvInputs pqSendInputs stdinCapBytes)
open CryptoVerification.SignalSession.Cli
  (DirGhost ReadRule StoresGhost addressText cliInputs decimalText keyName pathOf utf8)
open CryptoVerification.SignalSession.Cli.Decimal.Helpers (decimalText_digit decimalText_ge10)
open CryptoVerification.SignalSession.Cli.KitInst (cliIdentityVtRoSym cliSessionVtRoSym)
open CryptoVerification.SignalSession.Cli.KitInst.IdKit
  (savePollNeed saveShimNeed trustPollNeed trustShimNeed)
open CryptoVerification.SignalSession.Cli.KitInst.SessKit
  (loadPollNeed loadShimNeed storePollNeedX storeShimNeed)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddrV CallV RunCall blockingAncestorF cliIo cliRunBudgets cliWrOk coinsOf inputOf parseArgs
   pathStr)
open CryptoVerification.SignalSession.Cli.Placed (lsProg_569 lsProg_589)
open CryptoVerification.SignalSession.Cli.RunCompose
  (DecPkGhost Init1Data Init2Data InitGhost MeAtDispatch PksmGhost RunSem addrValOf runFiles)
open CryptoVerification.SignalSession.Cli.RunProofs (encDef)
open CryptoVerification.SignalSession.Cli.RunProofs.DecryptLemmas (toDecryptGhost)
open CryptoVerification.SignalSession.Cli.RunProofs.EncryptLemmas (w1EncGhost)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm (pksmParse)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (scopeIn scopeKit)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget SeqEnv)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (StringCloneEnv)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefsBudgetAux
  (toTempTwinsIkitEnv toTempTwinsKitEnv)
open LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins
  (FromApplyEnv FromCmEnv FromKeyEnv FromOtrEnv FromSaveEnv PreKeyPostEncryptEnv SaveStepEnv
   TrustStepEnv WithStoresEncEnv)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.KeyPairCalleesAuxBudget
  (KemKeyPairFromPubPrivEnv)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
  (parseArgs_peer_name_length_le pksmParse_lengths_le publicBundleOf_files_le_1637
   signalMessage_tryFrom_lengths_le)
open LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
  (CliPkDecodeEnv CliSpkDecodeEnv RecordSerializeSeqFreeValidEnv W1BinarySendDom W1BinarySendParams
   W1SendBinaryKitSlotEnv W2BinaryWhisperDom W2BinaryWhisperParams W2RecvWhisperBinaryKitSlotEnv
   W3BinaryInitDom W3BinaryInitParams W3InitBinaryKitSlotEnv W4BinaryAcceptWideEnv
   W4BinaryInitBobWideEnv W4BinaryKpkMarkStepEnv W4BinaryPkRemoveStepEnv W4BinaryPromoteArchiveEnv
   W4BinaryRecvPrekeyDom W4BinaryRecvPrekeyParams W4BinaryRecvPrekeyPathAWideEnv
   W4BinaryRecvPrekeyPathBWideEnv W4BinaryRecvPrekeyPathCWideEnv W4BinaryRecvPrekeyWideSlotEnv
   W4BinarySessStorePrev1StepEnv W4BinarySessStoreStepEnv W4BinaryStageP1OkEnv
   W4BinaryStageP1UntrustedEnv W4BinaryStageP2MatchedWideEnv W4BinaryStageP2PathAWideEnv
   W4BinaryStageP2PathCWideEnv W4BinaryStageP4MatchedWideEnv W4BinaryStageP4PathAWideEnv
   W4BinaryStageP4PathCWideEnv W4CloneACDomEnv W4CloneBDomEnv decBinaryIdKitPlacedBudget
   decBinarySessKitPlacedBudget mkBinaryKitRealCalleeEnvs mkW4RecvPrekeyWideSlotParams
   w1BinaryIdKitPlacedBudget w1BinarySessKitPlacedBudget)
open LibsignalBinary.Proofs.PeakBudget.CliRunArmsPeak (CliRunCalleeEnvs)
open LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge
  (CliRunBinaryEnv PubBundleReadEnv RealCliMainBinaryEnvOf cliMainArmEnvs cliRunCalleesEnvs
   init1Env_sub_r1bFileStepEnv init2Env_sub_r1bBinaryEnv preEnv_sub_r0BinaryEnv
   r1cInit3Env_sub_r1cEnv r2SendEnv_sub_r2Env r3aRecvWEnv_sub_r3aBinaryEnv r3bRecvPEnv_sub_r3bEnv
   runEnv_to_cliRunBinaryEnv_of_slots)
open LibsignalBinary.Proofs.PeakBudget.RealCliDecPkLinked (W4BinaryCallSiteDom)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemSlots
  (CanonicalOrFallbackPksmEnv cliSessKitOkSE_seqFree_placed pksmCanonSlice_sub_binaryKit
   pksmCanonicalGuard_sub_binaryKit pksmCanonicalOrFallback_sub_binaryKit
   realCliDecPkBinaryWideSlotEnv realCliInitBinarySlotEnv recv_rest_length_le_msgCapBytes
   serializeCanonSeqFreeSpecX w1_cliEncryptSlotEnv_sub_binaryKit
   w1_send_outPk_serialized_le_sessionCapBytes w1_send_out_serialized_le_sessionCapBytes
   w2_cliDecryptSignalSlotEnv_sub_binaryKit w3_realCliInitBinarySlotEnv_sub_binaryKit)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (IterSeqEnv)
open LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit (dropClonedSessionEvents)
open LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit (RecordSerializeSeqFreeEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (msgCapBytes sessionCapBytes)
open LibsignalBinary.Proofs.PeakBudget.SpqrSendPeakSpec (SpqrSendTightCapEnv)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds (RecordGhostValid)
open LibsignalBinary.Proofs.PeakBudget.W2RecvWhisperRealSlot (W2RealTdEnv)
open LibsignalBinary.Proofs.PeakBudget.W3InitiatePeakSpec (W3BoxedStoreStepEnv)
open LibsignalBinary.Proofs.PeakBudget.W3InitiateStagesPeak
  (W3InitiateFullEnv W3InitiateFullEnvWide)
open LibsignalBinary.Proofs.PeakBudget.W3InitiateTightSpec (RecordAliceInitiatedAnyCkBounds)
open LibsignalBinary.Proofs.PeakBudget.W4ArchiveCancelPeak (ArchivedTrialIterEnv)
open LibsignalBinary.Proofs.PeakBudget.W4InitBobPeak (W4BoundedEvs)
open LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec
  (OptStageEnv W4ErrTailWideEnv W4StageP3WideEnv W4TryDecryptCloneFailWideEnv)
open LibsignalBinary.Proofs.PeakBudget.W4OuterStageHelpers (W4BoxedStoreStepEnv)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot (W4RecvPrekeyTryDecACEnv)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot1MiB (W4RecvPrekeyRealDomOf)
open LibsignalBinary.Proofs.PeakBudget.WirePksmTightCredit (PksmCanonSliceEnv)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget
  (FromKeyReadyEnv FromLoadPolledEnv FromPostSomeEnv FromRegionSomeEnv FromStoreCallEnv
   FromTrustedTrueEnv LoadPollStepEnv WithStoresDecEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (IdentityStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (SessionOnlyKitPlacedOkSE)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget
  (SessionStoreBudgetEnv StoreStepEnv)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget (RecordDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget (DecimalEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a (DirGetEnv DirGetMissEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget (PathEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux (DirPutEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux (DirPutStrEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (OverCapFile ReadFileRuleEnvFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
  (cliIdentityKitDefaultBudgetEnv cliIdentityKitSavePollEnv cliIdentityKitTrustPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
  (AddrTextValEnv cliSessionKitBudgetEnv cliSessionKitLoadPollEnv cliSessionKitStorePollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Pub.BundleRead.PlacedBudgetAux
  (BundleReadEnv BundleReadTailEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R0ProofPlacedBudget (PreEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudget (Init1Env)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadOpkSpinePlacedBudget
  (R1bStepOpkErrEnv R1bStepOpkOkEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1bProofPlacedBudget
  (Init2AfterRegOkEnv Init2Env Init2Stage2Env Init2Stage3Env R1bStepKpkErrEnv R1bStepKpkOkEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cProofPlacedBudget (r1cInitGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2ProofPlacedBudget
  (r2EncGhost r2PeerGhost0)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudget
  (r3aDecSigGhost0)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bProofPlacedBudget
  (r3bDecPkGhost r3bPksmGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudget (RunEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget (RunSlotEnvs)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdKeyPairPollPlacedBudget
  (OptIkpTryFromEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdRegIdPollPlacedBudget
  (OptRegIdMalformedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget
  (decIdKitPlaced decSessKitPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.TopPlacedBudget
  (CliDecryptSignalSlotEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlotOfInnerPlacedBudget
  (CliEncryptSlotEnv w1IdKitPlaced w1SessKitPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (ReadFileRuleEnv readFileSpecPlaced sessDeserializeSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LayoutBudget (CliKpkGetPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortPlacedBudget
  (KpkLastResortPreAfterGetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.SymPlacedBudgetAux
  (CliKpkMarkPollEnv KpkOneTimePreAfterGetEnv OptKpkMarkOneTimeTailEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser (ofBytesEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.LayoutBudget (CliPkGetPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePoll.LayoutPlacedBudget
  (CliPkRemovePollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesBudget (CliSpkGetPollEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget (InitialStateEnv)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (SegCloneEnv)

/-! ## 1. `ReadFileRuleEnvFixed` Monotonicity & Non-`OverCapFile` Collapse -/

/-- Unconditional inclusion `ReadFileRuleEnv rd ⊆ ReadFileRuleEnvFixed rd`. -/
theorem readFileRuleEnv_sub_fixed {rd : ReadRule} {files : FsFiles} {path : List (BitVec 8)}
    {evs : List AllocEvent} (h : ReadFileRuleEnv rd files path evs) :
    ReadFileRuleEnvFixed rd files path evs :=
  Or.inl h

/-- Whenever `¬ OverCapFile files path`, `ReadFileRuleEnvFixed` collapses to `ReadFileRuleEnv`. -/
theorem readFileRuleEnvFixed_iff_of_not_overCap {rd : ReadRule} {files : FsFiles}
    {path : List (BitVec 8)} (hn : ¬ OverCapFile files path) (evs : List AllocEvent) :
    ReadFileRuleEnvFixed rd files path evs ↔ ReadFileRuleEnv rd files path evs :=
  ⟨fun h => h.elim id (fun h2 => False.elim (hn h2.2.1)), Or.inl⟩

/-- Predicate-equality form of `readFileRuleEnvFixed_iff_of_not_overCap`. -/
theorem readFileRuleEnvFixed_eq_of_not_overCap {rd : ReadRule} {files : FsFiles}
    {path : List (BitVec 8)} (hn : ¬ OverCapFile files path) :
    ReadFileRuleEnvFixed rd files path = ReadFileRuleEnv rd files path := by
  funext evs
  exact propext (readFileRuleEnvFixed_iff_of_not_overCap hn evs)

/-- `DirGetEnv` at `ReadFileRuleEnvFixed rd` equals `DirGetEnv` at `ReadFileRuleEnv rd` whenever
the underlying cache-miss path `pathOf d.path name` is not `OverCapFile`. -/
theorem dirGetEnv_fixed_eq_of_not_overCap
    {PathEnv' : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {rd : ReadRule} {F0 : FsFiles} {d : DirGhost} {name : List (BitVec 8)}
    (hn : ¬ OverCapFile F0 (pathOf d.path name)) :
    DirGetEnv PathEnv' (ReadFileRuleEnvFixed rd) rd F0 d name =
      DirGetEnv PathEnv' (ReadFileRuleEnv rd) rd F0 d name := by
  funext evs
  unfold DirGetEnv DirGetMissEnv
  rw [readFileRuleEnvFixed_eq_of_not_overCap hn]

/-- `BundleReadEnv` at `ReadFileRuleEnvFixed rd` equals `BundleReadEnv` at `ReadFileRuleEnv rd`
whenever `dir ++ [0x2f#8] ++ name` is not `OverCapFile`. -/
theorem bundleReadEnv_fixed_eq_of_not_overCap
    {PathEnv' : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {rd : ReadRule} {files : FsFiles} {dir name : List (BitVec 8)}
    (hn : ¬ OverCapFile files (dir ++ [0x2f#8] ++ name)) :
    BundleReadEnv rd PathEnv' (ReadFileRuleEnvFixed rd) files dir name =
      BundleReadEnv rd PathEnv' (ReadFileRuleEnv rd) files dir name := by
  funext evs
  unfold BundleReadEnv BundleReadTailEnv
  rw [readFileRuleEnvFixed_eq_of_not_overCap hn]

/-! ## 2. `normalizePath` Provenance & `¬ OverCapFile (runFiles i)` on Non-`baseKeysFile` Paths -/

private def EntriesFromNorm (files : List (String × List (BitVec 8))) (fs : FsState) : Prop :=
  ∀ k bs, fs.entries k = some (.file bs) → ∃ p, normalizePath p = k ∧ (p, bs) ∈ files

private theorem entriesFromNorm_empty (files : List (String × List (BitVec 8))) :
    EntriesFromNorm files ({} : FsState) := by
  intro k bs hk
  dsimp only at hk
  split at hk <;> cases hk

private theorem entriesFromNorm_setEntry_dir {files : List (String × List (BitVec 8))}
    {fs : FsState} (h : EntriesFromNorm files fs) (pref : FsPath) :
    EntriesFromNorm files (fs.setEntry pref (some .dir)) := by
  intro k bs hk
  unfold FsState.setEntry at hk
  dsimp only at hk
  split at hk
  · cases hk
  · exact h k bs hk

private theorem entriesFromNorm_foldl_dirs {files : List (String × List (BitVec 8))}
    (prefs : List FsPath) {fs : FsState} (h : EntriesFromNorm files fs) :
    EntriesFromNorm files (prefs.foldl (fun acc pref => acc.setEntry pref (some .dir)) fs) := by
  induction prefs generalizing fs with
  | nil => exact h
  | cons hd tl ih => exact ih (entriesFromNorm_setEntry_dir h hd)

private theorem entriesFromNorm_foldl_outer_dirs {files : List (String × List (BitVec 8))}
    (dirs : List String) {fs : FsState} (h : EntriesFromNorm files fs) :
    EntriesFromNorm files
      (dirs.foldl
        (fun acc d => (FsPath.nonEmptyPrefixes (normalizePath d)).foldl
          (fun a pref => a.setEntry pref (some .dir)) acc) fs) := by
  induction dirs generalizing fs with
  | nil => exact h
  | cons hd tl ih => exact ih (entriesFromNorm_foldl_dirs _ h)

private theorem entriesFromNorm_setFile {files : List (String × List (BitVec 8))} {fs : FsState}
    (h : EntriesFromNorm files fs) {p : String} {bs : List (BitVec 8)}
    (hmem : (p, bs) ∈ files) :
    EntriesFromNorm files (fs.setFile p (some (.file bs))) := by
  intro k bs' hk
  unfold FsState.setFile FsState.setEntry at hk
  dsimp only at hk
  split at hk
  · rename_i hbeq
    injection hk with hfile
    injection hfile with hbs
    subst hbs
    exact ⟨p, (eq_of_beq hbeq).symm, hmem⟩
  · exact h k bs' hk

private theorem entriesFromNorm_foldl_files {allFiles : List (String × List (BitVec 8))}
    (rem : List (String × List (BitVec 8)))
    (hsub : ∀ x ∈ rem, x ∈ allFiles)
    {fs : FsState} (h : EntriesFromNorm allFiles fs) :
    EntriesFromNorm allFiles
      (rem.foldl
        (fun acc (p, bs) =>
          let withAnc := ((FsPath.nonEmptyPrefixes (normalizePath p)).dropLast).foldl
            (fun a pref => a.setEntry pref (some .dir)) acc
          withAnc.setFile p (some (.file bs))) fs) := by
  induction rem generalizing fs with
  | nil => exact h
  | cons hd tl ih =>
    rcases hd with ⟨p, bs⟩
    have hanc := entriesFromNorm_foldl_dirs ((FsPath.nonEmptyPrefixes (normalizePath p)).dropLast) h
    have hset := entriesFromNorm_setFile hanc (hsub (p, bs) (List.mem_cons_self ..))
    exact ih (fun x hx => hsub x (List.mem_cons_of_mem _ hx)) hset

private theorem initFsState_files_mem_norm {inputs : ProcessInputs} {q : String}
    {bs : List (BitVec 8)} (h : (initFsState inputs).files q = some (.file bs)) :
    ∃ p, normalizePath p = normalizePath q ∧ (p, bs) ∈ inputs.files := by
  have hd := entriesFromNorm_foldl_outer_dirs inputs.dirs (entriesFromNorm_empty inputs.files)
  have hf := entriesFromNorm_foldl_files inputs.files (fun _ hx => hx) hd
  unfold FsState.files FsState.getEntry at h
  split at h
  · cases h
  · exact hf (normalizePath q) bs h

private theorem splitSlash_go_append_slash (cur a b : List Char) :
    splitSlash.go cur (a ++ ('/' :: b)) = splitSlash.go cur a ++ splitSlash.go [] b := by
  induction a generalizing cur with
  | nil => rfl
  | cons c cs ih =>
    by_cases hc : c = '/'
    · subst hc
      simp only [List.cons_append, splitSlash.go, ih []]
    · rw [List.cons_append, splitSlash.go.eq_3 cur c (cs ++ '/' :: b) hc,
        splitSlash.go.eq_3 cur c cs hc, ih (c :: cur)]

private theorem splitSlash_go_no_slash (cur cs : List Char) (h : '/' ∉ cs) :
    splitSlash.go cur cs = [String.ofList (cur.reverse ++ cs)] := by
  induction cs generalizing cur with
  | nil => simp [splitSlash.go]
  | cons c tl ih =>
    have hc : c ≠ '/' := fun heq => h (heq ▸ List.mem_cons_self ..)
    have htl : '/' ∉ tl := fun hm => h (List.mem_cons_of_mem _ hm)
    rw [splitSlash.go.eq_3 cur c tl hc, ih (c :: cur) htl, List.reverse_cons, List.append_assoc,
      List.singleton_append]

private theorem splitSlash_append_slash (a b : String) :
    splitSlash (a ++ "/" ++ b) = splitSlash a ++ splitSlash b := by
  have htl : (a ++ "/" ++ b).toList = a.toList ++ ('/' :: b.toList) := by
    simp [String.toList_append]
  unfold splitSlash
  rw [htl]
  exact splitSlash_go_append_slash [] a.toList b.toList

private theorem normalizePath_append_slash (a b : String) :
    normalizePath (a ++ "/" ++ b) = normalizePath a ++ normalizePath b := by
  unfold normalizePath
  rw [splitSlash_append_slash, List.filter_append]

private theorem normalizePath_single {s : String} (hslash : '/' ∉ s.toList)
    (hne : s.isEmpty = false) (hdot : (s != ".") = true) :
    normalizePath s = [s] := by
  unfold normalizePath splitSlash
  rw [splitSlash_go_no_slash [] s.toList hslash]
  simp [String.ofList_toList, hne, hdot]

private def kutf8 (s : String) : List (BitVec 8) :=
  (s.toList.flatMap String.utf8EncodeChar).map fun b => BitVec.ofNat 8 b.toNat

private theorem byteArray_toList_eq_data : ∀ (bs : ByteArray), bs.toList = bs.data.toList
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

private theorem utf8_eq_kutf8 (s : String) : utf8 s = kutf8 s := by
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  simp [utf8, kutf8, List.utf8Encode, byteArray_toList_eq_data]

private theorem utf8_slash_eq : utf8 "/" = [0x2f#8] := by
  rw [utf8_eq_kutf8]; rfl

private theorem pathStr_utf8_eq {s : String} (h : pathStr (kutf8 s) = s) :
    pathStr (utf8 s) = s := by
  rw [utf8_eq_kutf8]; exact h

private theorem splitSlash_go_suffix_no_slash (cs : List Char) (hcs : '/' ∉ cs) :
    ∀ (cur a : List Char), ∃ init u,
      splitSlash.go cur (a ++ cs) = init ++ [String.ofList (u ++ cs)]
  | cur, [] => ⟨[], cur.reverse, by simp only [List.nil_append, splitSlash_go_no_slash cur cs hcs]⟩
  | cur, c :: tl => by
    by_cases hc : c = '/'
    · subst hc
      obtain ⟨init, u, ih⟩ := splitSlash_go_suffix_no_slash cs hcs [] tl
      refine ⟨String.ofList cur.reverse :: init, u, ?_⟩
      simp only [List.cons_append, splitSlash.go, ih]
    · rw [List.cons_append, splitSlash.go.eq_3 cur c (tl ++ cs) hc]
      exact splitSlash_go_suffix_no_slash cs hcs (c :: cur) tl

private theorem normalizePath_baseKeysFile_shape (j : BitVec 32) :
    ∃ (mid : List String) (lastSeg : String),
      normalizePath (baseKeysFile j) =
        "last-resort-kyber-pre-keys" :: (mid ++ [lastSeg]) ∧
      '.' ∈ lastSeg.toList := by
  have heq : baseKeysFile j =
      "last-resort-kyber-pre-keys" ++ "/" ++ (toString j.toNat ++ ".base-keys") := by
    unfold baseKeysFile
    exact String.ext (by simp [String.toList_append])
  rw [heq, normalizePath_append_slash]
  have h1 : normalizePath "last-resort-kyber-pre-keys" = ["last-resort-kyber-pre-keys"] := by
    decide
  have hno_slash : '/' ∉ (".base-keys" : String).toList := by decide
  obtain ⟨init, u, hsp⟩ :=
    splitSlash_go_suffix_no_slash (".base-keys" : String).toList hno_slash
      [] (toString j.toNat).toList
  let lastSeg := String.ofList (u ++ (".base-keys" : String).toList)
  have hlen : 10 ≤ lastSeg.toList.length := by
    dsimp only [lastSeg]
    rw [String.toList_ofList, List.length_append]
    have h10 : (".base-keys" : String).toList.length = 10 := by decide
    omega
  have hne : lastSeg.isEmpty = false := by
    cases hb : lastSeg.isEmpty
    · rfl
    · have h0 : lastSeg = "" := String.isEmpty_iff.mp hb
      rw [h0] at hlen
      contradiction
  have hndot : (lastSeg != ".") = true := by
    rw [bne_iff_ne]
    intro hd
    rw [hd] at hlen
    contradiction
  have hnorm2 : normalizePath (toString j.toNat ++ ".base-keys") =
      init.filter (fun seg => !seg.isEmpty && seg != ".") ++ [lastSeg] := by
    unfold normalizePath splitSlash
    rw [String.toList_append, hsp, List.filter_append]
    change init.filter (fun seg => !seg.isEmpty && seg != ".") ++
        List.filter (fun seg => !seg.isEmpty && seg != ".") [lastSeg] =
      init.filter (fun seg => !seg.isEmpty && seg != ".") ++ [lastSeg]
    simp only [List.filter, hne, Bool.not_false, hndot, Bool.true_and]
  have hdot_in : '.' ∈ lastSeg.toList := by
    dsimp only [lastSeg]
    rw [String.toList_ofList, List.mem_append]
    exact Or.inr (by decide)
  refine ⟨init.filter (fun seg => !seg.isEmpty && seg != "."), lastSeg, ?_, hdot_in⟩
  rw [h1, hnorm2, List.singleton_append]

private theorem pathStr_append (a b : List (BitVec 8)) :
    pathStr (a ++ b) = pathStr a ++ pathStr b := by
  unfold pathStr
  exact String.ext (by simp [String.toList_append])

private theorem pathStr_slash : pathStr [0x2f#8] = "/" := rfl

private theorem digit_char_ne_slash_dot :
    ∀ d : Nat, d < 10 →
      Char.ofNat (BitVec.ofNat 8 (0x30 + d)).toNat ≠ '/' ∧
      Char.ofNat (BitVec.ofNat 8 (0x30 + d)).toNat ≠ '.' := by
  intro d hd
  rcases (by omega : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨
                     d = 5 ∨ d = 6 ∨ d = 7 ∨ d = 8 ∨ d = 9) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem decimalText_digits :
    ∀ n : Nat, decimalText n ≠ [] ∧
      ∀ b ∈ decimalText n, ∃ d < 10, b = BitVec.ofNat 8 (0x30 + d) := by
  intro n
  refine Nat.strongRecOn n fun m ih => ?_
  by_cases hm : m < 10
  · rw [decimalText_digit m hm]
    refine ⟨List.cons_ne_nil _ _, ?_⟩
    intro b hb
    rw [List.mem_singleton] at hb
    exact ⟨m, hm, hb⟩
  · have hge : 10 ≤ m := by omega
    rw [decimalText_ge10 m hge]
    obtain ⟨hne, hdig⟩ := ih (m / 10) (by omega)
    refine ⟨by simp [hne], ?_⟩
    intro b hb
    rw [List.mem_append, List.mem_singleton] at hb
    rcases hb with hb1 | rfl
    · exact hdig b hb1
    · exact ⟨m % 10, by omega, rfl⟩

private theorem keyName_pathStr_props (k : BitVec 32) :
    '/' ∉ (pathStr (keyName k)).toList ∧
      '.' ∉ (pathStr (keyName k)).toList ∧
      (pathStr (keyName k)).isEmpty = false ∧
      (pathStr (keyName k) != ".") = true := by
  obtain ⟨hne, hdig⟩ := decimalText_digits k.toNat
  have htl : (pathStr (keyName k)).toList =
      (decimalText k.toNat).map (fun b => Char.ofNat b.toNat) := by
    unfold pathStr keyName
    rw [String.toList_ofList]
  have hslash : '/' ∉ (pathStr (keyName k)).toList := by
    rw [htl, List.mem_map]
    rintro ⟨b, hb, hch⟩
    obtain ⟨d, hd, rfl⟩ := hdig b hb
    exact (digit_char_ne_slash_dot d hd).1 hch
  have hdot : '.' ∉ (pathStr (keyName k)).toList := by
    rw [htl, List.mem_map]
    rintro ⟨b, hb, hch⟩
    obtain ⟨d, hd, rfl⟩ := hdig b hb
    exact (digit_char_ne_slash_dot d hd).2 hch
  have hne_str : (pathStr (keyName k)).isEmpty = false := by
    cases hb : (pathStr (keyName k)).isEmpty
    · rfl
    · have h0 : (pathStr (keyName k)).toList = [] := by
        rw [String.isEmpty_iff.mp hb]
        rfl
      rw [htl, List.map_eq_nil_iff] at h0
      exact False.elim (hne h0)
  have hdot_ne : (pathStr (keyName k) != ".") = true := by
    rw [bne_iff_ne]
    intro hd
    have hdot_in : '.' ∈ (pathStr (keyName k)).toList := by
      rw [hd]
      decide
    exact hdot hdot_in
  exact ⟨hslash, hdot, hne_str, hdot_ne⟩

/-- Under `CliPqxdhInputs P i`, every `OverCapFile (runFiles i) path` (`> 2 MiB`) normalizes to
`"last-resort-kyber-pre-keys" :: (mid ++ [lastSeg])` with `'.' ∈ lastSeg.toList`. -/
theorem overCapFile_runFiles_norm_shape {P : PEParams} {i : Inputs}
    (hi : CliPqxdhInputs P i) {path : List (BitVec 8)}
    (hoc : OverCapFile (runFiles i) path) :
    ∃ (mid : List String) (lastSeg : String),
      normalizePath (pathStr path) =
        "last-resort-kyber-pre-keys" :: (mid ++ [lastSeg]) ∧
      '.' ∈ lastSeg.toList := by
  obtain ⟨_, fbs, hfile, hgt⟩ := hoc
  obtain ⟨p, hnorm, hp_mem⟩ := initFsState_files_mem_norm hfile
  have hp' : (p, fbs) ∈ i.files := hp_mem
  obtain ⟨st, hwf, hcase⟩ := hi
  have hp_ed : (p, fbs) ∈ encodeDir P st := by
    rcases hcase with ⟨_, b, t, rfl⟩ | ⟨m, r, _, rfl⟩ | ⟨c, rc, _, rfl⟩ |
        ⟨m, rc, _, rfl⟩ | ⟨c, rc, _, _, _, rfl⟩
    · simp only [pqInitInputs, pqInputs, List.mem_append, List.mem_singleton] at hp'
      rcases hp' with (hed | hbun) | hcoins
      · exact hed
      · have hb := publicBundleOf_files_le_1637 b bundleDir (p, fbs) hbun
        dsimp only at hb
        omega
      · injection hcoins with _ hbs
        subst hbs
        have ht : t.toList.length = initiateTapeLen := t.toList_length
        unfold initiateTapeLen at ht
        omega
    · simp only [pqSendInputs, pqInputs, List.append_nil, List.mem_append,
        List.mem_singleton] at hp'
      rcases hp' with hed | hcoins
      · exact hed
      · injection hcoins with _ hbs
        subst hbs
        have hr : r.toList.length = 64 := r.toList_length
        omega
    · simp only [pqRecvInputs, pqInputs, List.append_nil, List.mem_append,
        List.mem_singleton] at hp'
      rcases hp' with hed | hcoins
      · exact hed
      · injection hcoins with _ hbs
        subst hbs
        have hrc : (keyToBytes32 rc).length = 32 := by simp [keyToBytes32]
        omega
    · simp only [pqRecvInputs, pqInputs, List.append_nil, List.mem_append,
        List.mem_singleton] at hp'
      rcases hp' with hed | hcoins
      · exact hed
      · injection hcoins with _ hbs
        subst hbs
        have hrc : (keyToBytes32 rc).length = 32 := by simp [keyToBytes32]
        omega
    · simp only [pqRecvInputs, pqInputs, List.append_nil, List.mem_append,
        List.mem_singleton] at hp'
      rcases hp' with hed | hcoins
      · exact hed
      · injection hcoins with _ hbs
        subst hbs
        have hrc : (keyToBytes32 rc).length = 32 := by simp [keyToBytes32]
        omega
  have hcap := (hwf.2.1 (p, fbs) hp_ed).2
  have hex : ∃ j : BitVec 32, p = baseKeysFile j := by
    apply Classical.byContradiction
    intro hne
    have hall : ∀ j : BitVec 32, p ≠ baseKeysFile j := fun j hj => hne ⟨j, hj⟩
    have hle : fbs.length ≤ fileCapBytes := hcap hall
    unfold fileCapBytes at hle
    omega
  obtain ⟨j, rfl⟩ := hex
  obtain ⟨mid, lastSeg, hj, hdot⟩ := normalizePath_baseKeysFile_shape j
  exact ⟨mid, lastSeg, hnorm.symm.trans hj, hdot⟩

/-- Any path whose `normalizePath` has length `< 2` is not `OverCapFile (runFiles i)`. -/
theorem not_overCapFile_runFiles_of_norm_len_lt {P : PEParams} {i : Inputs}
    (hi : CliPqxdhInputs P i) {path : List (BitVec 8)}
    (hlen : (normalizePath (pathStr path)).length < 2) :
    ¬ OverCapFile (runFiles i) path := by
  intro hoc
  obtain ⟨mid, lastSeg, hj, _⟩ := overCapFile_runFiles_norm_shape hi hoc
  rw [hj, List.length_cons, List.length_append, List.length_singleton] at hlen
  omega

/-- Any `pathOf d name` whose first segment `d` is non-empty, normalizes to `[pathStr d]`,
and `≠ "last-resort-kyber-pre-keys"` is not `OverCapFile (runFiles i)` for arbitrary `name`. -/
theorem not_overCapFile_runFiles_of_head_ne {P : PEParams} {i : Inputs}
    (hi : CliPqxdhInputs P i) {d : List (BitVec 8)} (name : List (BitVec 8))
    (hd_ne_nil : d ≠ [])
    (hd_norm : normalizePath (pathStr d) = [pathStr d])
    (hd_ne_lr : pathStr d ≠ "last-resort-kyber-pre-keys") :
    ¬ OverCapFile (runFiles i) (pathOf d name) := by
  intro hoc
  obtain ⟨_, _, hj, _⟩ := overCapFile_runFiles_norm_shape hi hoc
  have hpth : pathOf d name = d ++ [0x2f#8] ++ name := by
    unfold pathOf
    simp [hd_ne_nil, utf8_slash_eq]
  have hstr : pathStr (pathOf d name) = pathStr d ++ "/" ++ pathStr name := by
    rw [hpth, pathStr_append, pathStr_append, pathStr_slash]
  rw [hstr, normalizePath_append_slash, hd_norm, List.singleton_append] at hj
  injection hj with hhd _
  exact hd_ne_lr hhd

/-- Any `dir ++ [0x2f#8] ++ tail` whose trailing segment `pathStr tail` normalizes to `[pathStr tail]`
and contains no `'.'` is not `OverCapFile (runFiles i)` for arbitrary prefix `dir`. -/
theorem not_overCapFile_runFiles_of_last_no_dot {P : PEParams} {i : Inputs}
    (hi : CliPqxdhInputs P i) (dir : List (BitVec 8)) {tail : List (BitVec 8)}
    (ht_norm : normalizePath (pathStr tail) = [pathStr tail])
    (ht_no_dot : '.' ∉ (pathStr tail).toList) :
    ¬ OverCapFile (runFiles i) (dir ++ [0x2f#8] ++ tail) := by
  intro hoc
  obtain ⟨mid, lastSeg, hj, hdot_in⟩ := overCapFile_runFiles_norm_shape hi hoc
  have hstr : pathStr (dir ++ [0x2f#8] ++ tail) = pathStr dir ++ "/" ++ pathStr tail := by
    rw [pathStr_append, pathStr_append, pathStr_slash]
  rw [hstr, normalizePath_append_slash, ht_norm, ← List.cons_append] at hj
  have hlast : (normalizePath (pathStr dir) ++ [pathStr tail]).getLast? =
      (("last-resort-kyber-pre-keys" :: mid) ++ [lastSeg]).getLast? :=
    congrArg List.getLast? hj
  rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _),
    List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)] at hlast
  simp only [List.getLast?_singleton, Option.some.injEq] at hlast
  rw [← hlast] at hdot_in
  exact ht_no_dot hdot_in

private theorem not_overCapFile_runFiles_utf8_dir {P : PEParams} {i : Inputs}
    (hi : CliPqxdhInputs P i) {s : String} (name : List (BitVec 8))
    (hkne : kutf8 s ≠ [])
    (hkstr : pathStr (kutf8 s) = s)
    (hnorm : normalizePath s = [s])
    (hlr : s ≠ "last-resort-kyber-pre-keys") :
    ¬ OverCapFile (runFiles i) (pathOf (utf8 s) name) := by
  have hne : utf8 s ≠ [] := by rw [utf8_eq_kutf8]; exact hkne
  have hstr : pathStr (utf8 s) = s := pathStr_utf8_eq hkstr
  exact not_overCapFile_runFiles_of_head_ne hi name hne (by rw [hstr]; exact hnorm)
    (by rw [hstr]; exact hlr)

private theorem not_overCapFile_runFiles_utf8_bundle {P : PEParams} {i : Inputs}
    (hi : CliPqxdhInputs P i) (dir : List (BitVec 8)) {s : String}
    (hkstr : pathStr (kutf8 s) = s)
    (hnorm : normalizePath s = [s])
    (hdot : '.' ∉ s.toList) :
    ¬ OverCapFile (runFiles i) (dir ++ [0x2f#8] ++ utf8 s) := by
  have hstr : pathStr (utf8 s) = s := pathStr_utf8_eq hkstr
  exact not_overCapFile_runFiles_of_last_no_dot hi dir (by rw [hstr]; exact hnorm)
    (by rw [hstr]; exact hdot)

theorem not_overCapFile_runFiles_own_address {P : PEParams} {i : Inputs}
    (hi : CliPqxdhInputs P i) :
    ¬ OverCapFile (runFiles i) (pathOf StoresGhost.opened.identity.own.path (utf8 "address")) := by
  apply not_overCapFile_runFiles_of_norm_len_lt hi
  change (normalizePath (pathStr (utf8 "address"))).length < 2
  rw [pathStr_utf8_eq rfl]
  decide

theorem not_overCapFile_runFiles_own_ikp {P : PEParams} {i : Inputs}
    (hi : CliPqxdhInputs P i) :
    ¬ OverCapFile (runFiles i)
        (pathOf StoresGhost.opened.identity.own.path (utf8 "identity-key-pair")) := by
  apply not_overCapFile_runFiles_of_norm_len_lt hi
  change (normalizePath (pathStr (utf8 "identity-key-pair"))).length < 2
  rw [pathStr_utf8_eq rfl]
  decide

theorem not_overCapFile_runFiles_own_regId {P : PEParams} {i : Inputs}
    (hi : CliPqxdhInputs P i) :
    ¬ OverCapFile (runFiles i)
        (pathOf StoresGhost.opened.identity.own.path (utf8 "registration-id")) := by
  apply not_overCapFile_runFiles_of_norm_len_lt hi
  change (normalizePath (pathStr (utf8 "registration-id"))).length < 2
  rw [pathStr_utf8_eq rfl]
  decide

theorem not_overCapFile_runFiles_sessions {P : PEParams} {i : Inputs}
    (hi : CliPqxdhInputs P i) (name : List (BitVec 8)) :
    ¬ OverCapFile (runFiles i) (pathOf StoresGhost.opened.sessions.path name) :=
  not_overCapFile_runFiles_utf8_dir hi name (by decide) rfl (by decide) (by decide)

theorem not_overCapFile_runFiles_identities {P : PEParams} {i : Inputs}
    (hi : CliPqxdhInputs P i) (name : List (BitVec 8)) :
    ¬ OverCapFile (runFiles i) (pathOf StoresGhost.opened.identity.peers.path name) :=
  not_overCapFile_runFiles_utf8_dir hi name (by decide) rfl (by decide) (by decide)

theorem not_overCapFile_runFiles_signed {P : PEParams} {i : Inputs}
    (hi : CliPqxdhInputs P i) (name : List (BitVec 8)) :
    ¬ OverCapFile (runFiles i) (pathOf StoresGhost.opened.signed.path name) :=
  not_overCapFile_runFiles_utf8_dir hi name (by decide) rfl (by decide) (by decide)

theorem not_overCapFile_runFiles_oneTime {P : PEParams} {i : Inputs}
    (hi : CliPqxdhInputs P i) (name : List (BitVec 8)) :
    ¬ OverCapFile (runFiles i) (pathOf StoresGhost.opened.oneTime.path name) :=
  not_overCapFile_runFiles_utf8_dir hi name (by decide) rfl (by decide) (by decide)

theorem not_overCapFile_runFiles_kyberOneTime {P : PEParams} {i : Inputs}
    (hi : CliPqxdhInputs P i) (name : List (BitVec 8)) :
    ¬ OverCapFile (runFiles i) (pathOf StoresGhost.opened.kyber.oneTime.path name) :=
  not_overCapFile_runFiles_utf8_dir hi name (by decide) rfl (by decide) (by decide)

theorem not_overCapFile_runFiles_kyberLastResort_keyName {P : PEParams} {i : Inputs}
    (hi : CliPqxdhInputs P i) (k : BitVec 32) :
    ¬ OverCapFile (runFiles i) (pathOf StoresGhost.opened.kyber.lastResort.path (keyName k)) := by
  have hne : StoresGhost.opened.kyber.lastResort.path ≠ [] := by
    show utf8 "last-resort-kyber-pre-keys" ≠ []
    rw [utf8_eq_kutf8]; decide
  have hpth : pathOf StoresGhost.opened.kyber.lastResort.path (keyName k) =
      StoresGhost.opened.kyber.lastResort.path ++ [0x2f#8] ++ keyName k := by
    unfold pathOf
    simp [hne, utf8_slash_eq]
  rw [hpth]
  obtain ⟨hslash, hdot, hne_kn, hndot⟩ := keyName_pathStr_props k
  exact not_overCapFile_runFiles_of_last_no_dot hi _
    (normalizePath_single hslash hne_kn hndot) hdot

theorem not_overCapFile_runFiles_bundle_idKey {P : PEParams} {i : Inputs}
    (hi : CliPqxdhInputs P i) (dir : List (BitVec 8)) :
    ¬ OverCapFile (runFiles i) (dir ++ [0x2f#8] ++ utf8 "identity-key") :=
  not_overCapFile_runFiles_utf8_bundle hi dir rfl (by decide) (by decide)

theorem not_overCapFile_runFiles_bundle_regId {P : PEParams} {i : Inputs}
    (hi : CliPqxdhInputs P i) (dir : List (BitVec 8)) :
    ¬ OverCapFile (runFiles i) (dir ++ [0x2f#8] ++ utf8 "registration-id") :=
  not_overCapFile_runFiles_utf8_bundle hi dir rfl (by decide) (by decide)

theorem not_overCapFile_runFiles_bundle_spk {P : PEParams} {i : Inputs}
    (hi : CliPqxdhInputs P i) (dir : List (BitVec 8)) :
    ¬ OverCapFile (runFiles i) (dir ++ [0x2f#8] ++ utf8 "signed-pre-key") :=
  not_overCapFile_runFiles_utf8_bundle hi dir rfl (by decide) (by decide)

theorem not_overCapFile_runFiles_bundle_kpk {P : PEParams} {i : Inputs}
    (hi : CliPqxdhInputs P i) (dir : List (BitVec 8)) :
    ¬ OverCapFile (runFiles i) (dir ++ [0x2f#8] ++ utf8 "kyber-pre-key") :=
  not_overCapFile_runFiles_utf8_bundle hi dir rfl (by decide) (by decide)

theorem not_overCapFile_runFiles_bundle_opk {P : PEParams} {i : Inputs}
    (hi : CliPqxdhInputs P i) (dir : List (BitVec 8)) :
    ¬ OverCapFile (runFiles i) (dir ++ [0x2f#8] ++ utf8 "one-time-pre-key") :=
  not_overCapFile_runFiles_utf8_bundle hi dir rfl (by decide) (by decide)

/-! ## 3. `*Fixed` Store-Kit Budgets, `SessionOnlyKitPlacedOkSE` Lifts, & W1/W2 Collapse -/

/-- Binary-kit `SessionStoreBudgetEnv` for `w1SessKitPlaced A B F0 peer` at
`ReadFileRuleEnvFixed cliIo.rd`. -/
noncomputable abbrev w1BinarySessKitPlacedBudgetFixed [LibsignalPlacement]
    (A : RustAlloc) (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost) :
    SessionStoreBudgetEnv (w1SessKitPlaced A B F0 peer) :=
  cliSessionKitBudgetEnv A cliIo.rd F0 cliWrOk scopeKit peer
    loadShimNeed (loadPollNeed B.readFile)
    storeShimNeed storePollNeedX
    (AddrTextValEnv DecimalEnv)
    (DirGetEnv PathEnv (ReadFileRuleEnvFixed cliIo.rd) cliIo.rd)
    (ofBytesEnv RecordDeserializeCancelEnv)
    RecordSerializeSeqFreeValidEnv
    DirPutEnv
    cliSessionVtRoSym cliIdentityVtRoSym

/-- Binary-kit `IdentityStoreBudgetEnv` for `w1IdKitPlaced A B F0 peer` at
`ReadFileRuleEnvFixed cliIo.rd`. -/
noncomputable abbrev w1BinaryIdKitPlacedBudgetFixed [LibsignalPlacement]
    (A : RustAlloc) (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost) :
    IdentityStoreBudgetEnv (w1IdKitPlaced A B F0 peer) :=
  cliIdentityKitDefaultBudgetEnv A cliIo.rd F0 cliWrOk peer
    trustShimNeed (trustPollNeed B.readFile)
    saveShimNeed (savePollNeed B.readFile)
    cliIdentityVtRoSym (ReadFileRuleEnvFixed cliIo.rd)

/-- Binary-kit `SessionStoreBudgetEnv` for `decSessKitPlaced A F0 peer B` at
`ReadFileRuleEnvFixed cliIo.rd`. -/
noncomputable abbrev decBinarySessKitPlacedBudgetFixed [LibsignalPlacement]
    (A : RustAlloc) (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost) :
    SessionStoreBudgetEnv (decSessKitPlaced A F0 peer B) :=
  w1BinarySessKitPlacedBudgetFixed A B F0 peer

/-- Binary-kit `IdentityStoreBudgetEnv` for `decIdKitPlaced A F0 peer B` at
`ReadFileRuleEnvFixed cliIo.rd`. -/
noncomputable abbrev decBinaryIdKitPlacedBudgetFixed [LibsignalPlacement]
    (A : RustAlloc) (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost) :
    IdentityStoreBudgetEnv (decIdKitPlaced A F0 peer B) :=
  w1BinaryIdKitPlacedBudgetFixed A B F0 peer

/-- Direct `SessionOnlyKitPlacedOkSE` instantiation at `w1BinarySessKitPlacedBudgetFixed` (`ReadEnv :=
ReadFileRuleEnvFixed cliIo.rd`) on any `H : LibsignalHooks` (including `cliExternsPlaced mmpl W`). -/
theorem w1BinarySessKitPlacedFixed_okSE [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : RunHooksPlaced A lim H)
    (hRead : subroutine_ok (lsProg_589 H) (lsρ lsReadFileSym)
      (withLsCodeRoLoaded lsmpl
        (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile (ReadFileRuleEnvFixed cliIo.rd))))
    (hDeser : subroutine_ok (lsProg_569 H) (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim (ofBytesEnv RecordDeserializeCancelEnv)))
    (hSerSeqFree : subroutine_ok (lsProg_52 H) (lsmpl.base 52)
      (withLsCodeLoaded lsmpl (serializeCanonSeqFreeSpecX M A lim))) :
    SessionOnlyKitPlacedOkSE A lim
      (w1SessKitPlaced A.repAlloc B F0 peer)
      (w1BinarySessKitPlacedBudgetFixed A.repAlloc B F0 peer)
      scopeKit encodeRecord H :=
  cliSessKitOkSE_seqFree_placed
    (readProg := lsProg_589 H) (jRead := 589)
    (deserProg := lsProg_569 H) (deserBlk := 569)
    (serProg := lsProg_52 H) (serBlk := 52)
    hDropNz (fun _ hp => hp.2) hh hRead hDeser hSerSeqFree
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Direct `SessionOnlyKitPlacedOkSE` instantiation at `decBinarySessKitPlacedBudgetFixed` (`ReadEnv :=
ReadFileRuleEnvFixed cliIo.rd`) on any `H : LibsignalHooks`. -/
theorem decBinarySessKitPlacedFixed_okSE [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : RunHooksPlaced A lim H)
    (hRead : subroutine_ok (lsProg_589 H) (lsρ lsReadFileSym)
      (withLsCodeRoLoaded lsmpl
        (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile (ReadFileRuleEnvFixed cliIo.rd))))
    (hDeser : subroutine_ok (lsProg_569 H) (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim (ofBytesEnv RecordDeserializeCancelEnv)))
    (hSerSeqFree : subroutine_ok (lsProg_52 H) (lsmpl.base 52)
      (withLsCodeLoaded lsmpl (serializeCanonSeqFreeSpecX M A lim))) :
    SessionOnlyKitPlacedOkSE A lim
      (decSessKitPlaced A.repAlloc F0 peer B)
      (decBinarySessKitPlacedBudgetFixed A.repAlloc B F0 peer)
      scopeKit encodeRecord H :=
  w1BinarySessKitPlacedFixed_okSE B F0 peer hDropNz hh hRead hDeser hSerSeqFree

private theorem w1SessLoadPoll_fixed_eq {P : PEParams} {i : Inputs}
    (hi : CliPqxdhInputs P i) (a : AddrVal) :
    cliSessionKitLoadPollEnv cliIo.rd scopeKit (AddrTextValEnv DecimalEnv)
        (DirGetEnv PathEnv (ReadFileRuleEnvFixed cliIo.rd) cliIo.rd)
        (ofBytesEnv RecordDeserializeCancelEnv) (runFiles i) StoresGhost.opened.sessions a =
      cliSessionKitLoadPollEnv cliIo.rd scopeKit (AddrTextValEnv DecimalEnv)
        (DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd)
        (ofBytesEnv RecordDeserializeCancelEnv) (runFiles i) StoresGhost.opened.sessions a := by
  unfold cliSessionKitLoadPollEnv
  rw [dirGetEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_sessions hi _)]

private theorem w1IdTrustPoll_fixed_eq {P : PEParams} {i : Inputs}
    (hi : CliPqxdhInputs P i) (a : AddrVal) (k : IdentityKey)
    (d : Direction) :
    cliIdentityKitTrustPollEnv (DirGetEnv PathEnv (ReadFileRuleEnvFixed cliIo.rd) cliIo.rd)
        (runFiles i) StoresGhost.opened.identity a k d =
      cliIdentityKitTrustPollEnv (DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd)
        (runFiles i) StoresGhost.opened.identity a k d := by
  unfold cliIdentityKitTrustPollEnv
  rw [dirGetEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_identities hi _)]

private theorem w1IdSavePoll_fixed_eq {P : PEParams} {i : Inputs}
    (hi : CliPqxdhInputs P i) (a : AddrVal) (k : IdentityKey) :
    cliIdentityKitSavePollEnv cliIo.rd (DirGetEnv PathEnv (ReadFileRuleEnvFixed cliIo.rd) cliIo.rd)
        DirPutStrEnv (runFiles i) StoresGhost.opened.identity a k =
      cliIdentityKitSavePollEnv cliIo.rd (DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd)
        DirPutStrEnv (runFiles i) StoresGhost.opened.identity a k := by
  unfold cliIdentityKitSavePollEnv
  rw [dirGetEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_identities hi _)]

/-- Under `CliPqxdhInputs P i`, `CliEncryptSlotEnv` at `*BudgetFixed` collapses to `*Budget` on
`x.F = runFiles i` (`"sessions"` and `"identities"` are never `OverCapFile`). -/
theorem cliEncryptSlotEnv_fixed_eq_plain [LibsignalPlacement] {M : AllocCostModel}
    {P : PEParams} {i : Inputs} (hi : CliPqxdhInputs P i)
    (A : RustCliAllocBudget M) (B : RunBudgets)
    {x : CryptoVerification.SignalSession.Cli.RunCompose.EncGhost} (hx : x.F = runFiles i) :
    CliEncryptSlotEnv P A B SpqrSendTightCapEnv
        (w1BinarySessKitPlacedBudgetFixed A.repAlloc B)
        (w1BinaryIdKitPlacedBudgetFixed A.repAlloc B) x =
      CliEncryptSlotEnv P A B SpqrSendTightCapEnv
        (w1BinarySessKitPlacedBudget A.repAlloc B)
        (w1BinaryIdKitPlacedBudget A.repAlloc B) x := by
  have hload :
      (toTempTwinsKitEnv
          (w1BinarySessKitPlacedBudgetFixed A.repAlloc B x.F x.peer)).loadPollEnv
          StoresGhost.opened.sessions (w1EncGhost x).rem.val =
        (toTempTwinsKitEnv
          (w1BinarySessKitPlacedBudget A.repAlloc B x.F x.peer)).loadPollEnv
          StoresGhost.opened.sessions (w1EncGhost x).rem.val := by
    change cliSessionKitLoadPollEnv _ _ _ _ _ x.F _ _ = cliSessionKitLoadPollEnv _ _ _ _ _ x.F _ _
    rw [hx]
    exact w1SessLoadPoll_fixed_eq hi _
  have htrust : ∀ k,
      (toTempTwinsIkitEnv
          (w1BinaryIdKitPlacedBudgetFixed A.repAlloc B x.F x.peer)).trustPollEnv
          StoresGhost.opened.identity (w1EncGhost x).rem.val k .sending =
        (toTempTwinsIkitEnv
          (w1BinaryIdKitPlacedBudget A.repAlloc B x.F x.peer)).trustPollEnv
          StoresGhost.opened.identity (w1EncGhost x).rem.val k .sending := by
    intro k
    change cliIdentityKitTrustPollEnv _ x.F _ _ k .sending =
      cliIdentityKitTrustPollEnv _ x.F _ _ k .sending
    rw [hx]
    exact w1IdTrustPoll_fixed_eq hi _ k .sending
  have hsave : ∀ k,
      (toTempTwinsIkitEnv
          (w1BinaryIdKitPlacedBudgetFixed A.repAlloc B x.F x.peer)).savePollEnv
          ((w1IdKitPlaced A.repAlloc B x.F x.peer).trustUpdate StoresGhost.opened.identity
            (w1EncGhost x).rem.val k .sending (.ok true))
          (w1EncGhost x).rem.val k =
        (toTempTwinsIkitEnv
          (w1BinaryIdKitPlacedBudget A.repAlloc B x.F x.peer)).savePollEnv
          ((w1IdKitPlaced A.repAlloc B x.F x.peer).trustUpdate StoresGhost.opened.identity
            (w1EncGhost x).rem.val k .sending (.ok true))
          (w1EncGhost x).rem.val k := by
    intro k
    change cliIdentityKitSavePollEnv _ _ _ x.F StoresGhost.opened.identity _ _ =
      cliIdentityKitSavePollEnv _ _ _ x.F StoresGhost.opened.identity _ _
    rw [hx]
    exact w1IdSavePoll_fixed_eq hi _ k
  have hstore :
      (toTempTwinsKitEnv
          (w1BinarySessKitPlacedBudgetFixed A.repAlloc B x.F x.peer)).storePollEnv =
        (toTempTwinsKitEnv
          (w1BinarySessKitPlacedBudget A.repAlloc B x.F x.peer)).storePollEnv := rfl
  have hcm : ∀ sess (otr' : OutgoingTripleRatchet (List (BitVec 8))) taken k,
      FromCmEnv (w1SessKitPlaced A.repAlloc B x.F x.peer)
          (toTempTwinsKitEnv (w1BinarySessKitPlacedBudgetFixed A.repAlloc B x.F x.peer))
          StoresGhost.opened.sessions
          (w1IdKitPlaced A.repAlloc B x.F x.peer)
          (toTempTwinsIkitEnv (w1BinaryIdKitPlacedBudgetFixed A.repAlloc B x.F x.peer))
          StoresGhost.opened.identity (w1EncGhost x) sess otr' taken k =
        FromCmEnv (w1SessKitPlaced A.repAlloc B x.F x.peer)
          (toTempTwinsKitEnv (w1BinarySessKitPlacedBudget A.repAlloc B x.F x.peer))
          StoresGhost.opened.sessions
          (w1IdKitPlaced A.repAlloc B x.F x.peer)
          (toTempTwinsIkitEnv (w1BinaryIdKitPlacedBudget A.repAlloc B x.F x.peer))
          StoresGhost.opened.identity (w1EncGhost x) sess otr' taken k := by
    intro sess otr' taken k
    funext evs
    unfold FromCmEnv TrustStepEnv FromSaveEnv SaveStepEnv FromApplyEnv
    rw [htrust k, hsave k, hstore]
  have hotr : ∀ sess otr taken,
      FromOtrEnv P.C (pqxdhSpqrModel P) SpqrSendTightCapEnv uuidTryParse
          (w1SessKitPlaced A.repAlloc B x.F x.peer)
          (toTempTwinsKitEnv (w1BinarySessKitPlacedBudgetFixed A.repAlloc B x.F x.peer))
          StoresGhost.opened.sessions
          (w1IdKitPlaced A.repAlloc B x.F x.peer)
          (toTempTwinsIkitEnv (w1BinaryIdKitPlacedBudgetFixed A.repAlloc B x.F x.peer))
          StoresGhost.opened.identity (w1EncGhost x) sess otr taken =
        FromOtrEnv P.C (pqxdhSpqrModel P) SpqrSendTightCapEnv uuidTryParse
          (w1SessKitPlaced A.repAlloc B x.F x.peer)
          (toTempTwinsKitEnv (w1BinarySessKitPlacedBudget A.repAlloc B x.F x.peer))
          StoresGhost.opened.sessions
          (w1IdKitPlaced A.repAlloc B x.F x.peer)
          (toTempTwinsIkitEnv (w1BinaryIdKitPlacedBudget A.repAlloc B x.F x.peer))
          StoresGhost.opened.identity (w1EncGhost x) sess otr taken := by
    intro sess otr taken
    funext evs
    unfold FromOtrEnv FromKeyEnv PreKeyPostEncryptEnv
    simp only [hcm]
  funext evs
  unfold CliEncryptSlotEnv WithStoresEncEnv
  rw [hload]
  simp only [hotr]

/-- Under `CliPqxdhInputs P i`, `CliDecryptSignalSlotEnv` at `*BudgetFixed` collapses to `*Budget`
on `x.F = runFiles i`. -/
theorem cliDecryptSignalSlotEnv_fixed_eq_plain [LibsignalPlacement] {M : AllocCostModel}
    {P : PEParams} {i : Inputs} (hi : CliPqxdhInputs P i)
    (A : RustCliAllocBudget M) (B : RunBudgets)
    {x : CryptoVerification.SignalSession.Cli.RunCompose.DecSigGhost} (hx : x.F = runFiles i) :
    CliDecryptSignalSlotEnv P A B (W2RealTdEnv P.C.F P.Q.K)
        (decBinarySessKitPlacedBudgetFixed A.repAlloc B)
        (decBinaryIdKitPlacedBudgetFixed A.repAlloc B) x =
      CliDecryptSignalSlotEnv P A B (W2RealTdEnv P.C.F P.Q.K)
        (decBinarySessKitPlacedBudget A.repAlloc B)
        (decBinaryIdKitPlacedBudget A.repAlloc B) x := by
  have hload :
      (decBinarySessKitPlacedBudgetFixed A.repAlloc B x.F x.peer).loadPollEnv
          StoresGhost.opened.sessions (toDecryptGhost x).rem.val =
        (decBinarySessKitPlacedBudget A.repAlloc B x.F x.peer).loadPollEnv
          StoresGhost.opened.sessions (toDecryptGhost x).rem.val := by
    change cliSessionKitLoadPollEnv _ _ _ _ _ x.F _ _ = cliSessionKitLoadPollEnv _ _ _ _ _ x.F _ _
    rw [hx]
    exact w1SessLoadPoll_fixed_eq hi _
  have htrust : ∀ k,
      (decBinaryIdKitPlacedBudgetFixed A.repAlloc B x.F x.peer).trustPollEnv
          StoresGhost.opened.identity (toDecryptGhost x).rem.val k .receiving =
        (decBinaryIdKitPlacedBudget A.repAlloc B x.F x.peer).trustPollEnv
          StoresGhost.opened.identity (toDecryptGhost x).rem.val k .receiving := by
    intro k
    change cliIdentityKitTrustPollEnv _ x.F _ _ k .receiving =
      cliIdentityKitTrustPollEnv _ x.F _ _ k .receiving
    rw [hx]
    exact w1IdTrustPoll_fixed_eq hi _ k .receiving
  have hsave : ∀ k,
      (decBinaryIdKitPlacedBudgetFixed A.repAlloc B x.F x.peer).savePollEnv
          ((decIdKitPlaced A.repAlloc x.F x.peer B).trustUpdate StoresGhost.opened.identity
            (toDecryptGhost x).rem.val k .receiving (.ok true))
          (toDecryptGhost x).rem.val k =
        (decBinaryIdKitPlacedBudget A.repAlloc B x.F x.peer).savePollEnv
          ((decIdKitPlaced A.repAlloc x.F x.peer B).trustUpdate StoresGhost.opened.identity
            (toDecryptGhost x).rem.val k .receiving (.ok true))
          (toDecryptGhost x).rem.val k := by
    intro k
    change cliIdentityKitSavePollEnv _ _ _ x.F StoresGhost.opened.identity _ _ =
      cliIdentityKitSavePollEnv _ _ _ x.F StoresGhost.opened.identity _ _
    rw [hx]
    exact w1IdSavePoll_fixed_eq hi _ k
  have hstore :
      (decBinarySessKitPlacedBudgetFixed A.repAlloc B x.F x.peer).storePollEnv =
        (decBinarySessKitPlacedBudget A.repAlloc B x.F x.peer).storePollEnv := rfl
  have hkr : ∀ r' k,
      FromKeyReadyEnv (decSessKitPlaced A.repAlloc x.F x.peer B)
          (decBinarySessKitPlacedBudgetFixed A.repAlloc B x.F x.peer)
          StoresGhost.opened.sessions
          (decIdKitPlaced A.repAlloc x.F x.peer B)
          (decBinaryIdKitPlacedBudgetFixed A.repAlloc B x.F x.peer)
          StoresGhost.opened.identity (toDecryptGhost x) r' k =
        FromKeyReadyEnv (decSessKitPlaced A.repAlloc x.F x.peer B)
          (decBinarySessKitPlacedBudget A.repAlloc B x.F x.peer)
          StoresGhost.opened.sessions
          (decIdKitPlaced A.repAlloc x.F x.peer B)
          (decBinaryIdKitPlacedBudget A.repAlloc B x.F x.peer)
          StoresGhost.opened.identity (toDecryptGhost x) r' k := by
    intro r' k
    funext evs
    unfold FromKeyReadyEnv
      LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget.TrustStepEnv
      FromTrustedTrueEnv
      LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget.SaveStepEnv
      FromStoreCallEnv StoreStepEnv
    rw [htrust k, hsave k, hstore]
  have hps : ∀ r,
      FromPostSomeEnv P.C (pqxdhSpqrModel P) uuidTryParse
          (decSessKitPlaced A.repAlloc x.F x.peer B)
          (decBinarySessKitPlacedBudgetFixed A.repAlloc B x.F x.peer)
          StoresGhost.opened.sessions
          (decIdKitPlaced A.repAlloc x.F x.peer B)
          (decBinaryIdKitPlacedBudgetFixed A.repAlloc B x.F x.peer)
          StoresGhost.opened.identity (toDecryptGhost x) r =
        FromPostSomeEnv P.C (pqxdhSpqrModel P) uuidTryParse
          (decSessKitPlaced A.repAlloc x.F x.peer B)
          (decBinarySessKitPlacedBudget A.repAlloc B x.F x.peer)
          StoresGhost.opened.sessions
          (decIdKitPlaced A.repAlloc x.F x.peer B)
          (decBinaryIdKitPlacedBudget A.repAlloc B x.F x.peer)
          StoresGhost.opened.identity (toDecryptGhost x) r := by
    intro r
    funext evs
    unfold FromPostSomeEnv
    simp only [hkr]
  have hrs : ∀ r G ses_st,
      FromRegionSomeEnv P.C (pqxdhSpqrModel P) uuidTryParse (W2RealTdEnv P.C.F P.Q.K)
          (decSessKitPlaced A.repAlloc x.F x.peer B)
          (decBinarySessKitPlacedBudgetFixed A.repAlloc B x.F x.peer)
          StoresGhost.opened.sessions
          (decIdKitPlaced A.repAlloc x.F x.peer B)
          (decBinaryIdKitPlacedBudgetFixed A.repAlloc B x.F x.peer)
          StoresGhost.opened.identity (toDecryptGhost x) r G ses_st =
        FromRegionSomeEnv P.C (pqxdhSpqrModel P) uuidTryParse (W2RealTdEnv P.C.F P.Q.K)
          (decSessKitPlaced A.repAlloc x.F x.peer B)
          (decBinarySessKitPlacedBudget A.repAlloc B x.F x.peer)
          StoresGhost.opened.sessions
          (decIdKitPlaced A.repAlloc x.F x.peer B)
          (decBinaryIdKitPlacedBudget A.repAlloc B x.F x.peer)
          StoresGhost.opened.identity (toDecryptGhost x) r G ses_st := by
    intro r G ses_st
    funext evs
    unfold FromRegionSomeEnv
    rw [hps r]
  have hlp :
      FromLoadPolledEnv P.C (pqxdhSpqrModel P) uuidTryParse (W2RealTdEnv P.C.F P.Q.K)
          (decSessKitPlaced A.repAlloc x.F x.peer B)
          (decBinarySessKitPlacedBudgetFixed A.repAlloc B x.F x.peer)
          StoresGhost.opened.sessions
          (decIdKitPlaced A.repAlloc x.F x.peer B)
          (decBinaryIdKitPlacedBudgetFixed A.repAlloc B x.F x.peer)
          StoresGhost.opened.identity scopeKit (toDecryptGhost x) =
        FromLoadPolledEnv P.C (pqxdhSpqrModel P) uuidTryParse (W2RealTdEnv P.C.F P.Q.K)
          (decSessKitPlaced A.repAlloc x.F x.peer B)
          (decBinarySessKitPlacedBudget A.repAlloc B x.F x.peer)
          StoresGhost.opened.sessions
          (decIdKitPlaced A.repAlloc x.F x.peer B)
          (decBinaryIdKitPlacedBudget A.repAlloc B x.F x.peer)
          StoresGhost.opened.identity scopeKit (toDecryptGhost x) := by
    funext evs
    unfold FromLoadPolledEnv
    simp only [hrs]
  funext evs
  unfold CliDecryptSignalSlotEnv WithStoresDecEnv LoadPollStepEnv
  rw [hload, hlp]

/-! ## 4. `*Fixed` W4 `kpkMark` Envelopes and Whole-`run`/`main` Callee Bundles -/

/-- Binary-kit `mark_kyber_pre_key_used` boxed step (`32` B box + `CliKpkMarkPollEnv`) at
`DirGetEnv PathEnv (ReadFileRuleEnvFixed rd) rd` (admitting over-cap `baseKeysFile` reads). -/
def W4BinaryKpkMarkStepEnvFixed (rd : ReadRule) (files : FsFiles)
    (kpkId spkId : BitVec 32) (baseKey : PublicKey) : List AllocEvent → Prop :=
  W4BoxedStoreStepEnv 32
    (CliKpkMarkPollEnv rd DecimalEnv (DirGetEnv PathEnv (ReadFileRuleEnvFixed rd) rd) DirPutEnv
      files ⟨0#64, 0#64, 0#64, 0#64, kpkId, spkId, baseKey, StoresGhost.opened.kyber⟩)

/-- Binary-kit Stage P4 Path A (`0`-prev) envelope at `W4BinaryKpkMarkStepEnvFixed`. -/
def W4BinaryStageP4PathAWideEnvFixed (hasOpk : Bool) (rd : ReadRule) (files : FsFiles)
    (peer : AddrGhost) (remoteIdKey : IdentityKey)
    (kpkId spkId opkId : BitVec 32) (baseKey : PublicKey)
    (g_out0 : RecordGhost) (r_out0 : SessionRecord (List (BitVec 8)))
    (evs : List AllocEvent) : Prop :=
  SeqEnv (OptStageEnv (CliRealBinaryKitEnvs.W4BinaryIdSaveStepEnv rd files peer remoteIdKey))
    (SeqEnv (OptStageEnv (W4BinaryKpkMarkStepEnvFixed rd files kpkId spkId baseKey))
      (SeqEnv (OptStageEnv (if hasOpk then W4BinaryPkRemoveStepEnv rd files opkId else (· = [])))
        (SeqEnv (OptStageEnv (W4BinarySessStoreStepEnv peer g_out0 r_out0)) FreeOnlyEvs))) evs

/-- Binary-kit Stage P4 Path C (`prev1`) envelope at `W4BinaryKpkMarkStepEnvFixed`. -/
def W4BinaryStageP4PathCWideEnvFixed (hasOpk : Bool) (rd : ReadRule) (files : FsFiles)
    (peer : AddrGhost) (remoteIdKey : IdentityKey)
    (kpkId spkId opkId : BitVec 32) (baseKey : PublicKey)
    (G_out1 : SessionGhost) (sess_out1 : Session (List (BitVec 8))) (enc_prev1 : List (BitVec 8))
    (evs : List AllocEvent) : Prop :=
  SeqEnv (OptStageEnv (CliRealBinaryKitEnvs.W4BinaryIdSaveStepEnv rd files peer remoteIdKey))
    (SeqEnv (OptStageEnv (W4BinaryKpkMarkStepEnvFixed rd files kpkId spkId baseKey))
      (SeqEnv (OptStageEnv (if hasOpk then W4BinaryPkRemoveStepEnv rd files opkId else (· = [])))
        (SeqEnv (OptStageEnv (W4BinarySessStorePrev1StepEnv peer G_out1 sess_out1 enc_prev1))
          FreeOnlyEvs))) evs

/-- Binary-kit Path A (`0`-prev) Stages P1–P4 envelope over `W4BinaryRecvPrekeyParams` at
`W4BinaryStageP4PathAWideEnvFixed`. -/
def W4BinaryRecvPrekeyPathAWideEnvFixed (w : W4BinaryRecvPrekeyParams)
    (evs : List AllocEvent) : Prop :=
  SeqEnv (W4BinaryStageP1OkEnv w.base.rd w.base.files w.base.peer w.remoteIdKey)
    (SeqEnv
      (OptStageEnv
        (W4BinaryStageP2PathAWideEnv w.base.hasOpk w.base.rd w.base.files
          w.base.spkId w.base.kpkId w.base.opkId w.base.F w.base.x_res w.base.x_spqr))
      (SeqEnv (OptStageEnv (W4StageP3WideEnv W4CloneACDomEnv (W4RecvPrekeyTryDecACEnv w.base)))
        (OptStageEnv
          (W4BinaryStageP4PathAWideEnvFixed w.base.hasOpk w.base.rd w.base.files w.base.peer
            w.remoteIdKey w.base.kpkId w.base.spkId w.base.opkId w.baseKey
            w.base.g_out0 w.base.r_out0)))) evs

/-- Binary-kit Path C (`prev1`) Stages P1–P4 envelope over `W4BinaryRecvPrekeyParams` at
`W4BinaryStageP4PathCWideEnvFixed`. -/
def W4BinaryRecvPrekeyPathCWideEnvFixed (w : W4BinaryRecvPrekeyParams)
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
          (W4BinaryStageP4PathCWideEnvFixed w.base.hasOpk w.base.rd w.base.files w.base.peer
            w.remoteIdKey w.base.kpkId w.base.spkId w.base.opkId w.baseKey
            w.base.G_out1 w.base.sess_out1 w.base.enc_prev1)))) evs

/-- Four-arm binary-kit W4 (`recv-prekey`) slot envelope over `W4BinaryRecvPrekeyParams` at
`W4BinaryKpkMarkStepEnvFixed` on Paths A and C (`PathBWide` has no `kpkMark`). -/
def W4BinaryRecvPrekeyWideSlotEnvFixed (w : W4BinaryRecvPrekeyParams)
    (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨
  SeqEnv
    (fun e =>
      W4BinaryStageP1UntrustedEnv w.base.rd w.base.files w.base.peer w.remoteIdKey e ∨
      W4BinaryRecvPrekeyPathBWideEnv w e ∨
      W4BinaryRecvPrekeyPathAWideEnvFixed w e ∨
      W4BinaryRecvPrekeyPathCWideEnvFixed w e)
    FreeOnlyEvs evs

/-- Mode-dispatched `CliRunCalleeEnvs` bundle coinciding definitionally (`rfl`) with
`mkBinaryKitRealCalleeEnvs` on `initEnv`, `encEnv`, `decSigEnv`, and `pksmEnv`, and widening
`decPkEnv` to `W4BinaryRecvPrekeyWideSlotEnvFixed` (`kpkMark` over-cap `baseKeysFile` arm). -/
def mkBinaryKitRealCalleeEnvsFixed [LibsignalPlacement]
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (g : RunCall) : CliRunCalleeEnvs :=
  { mkBinaryKitRealCalleeEnvs img S X W g with
    decPkEnv := match g.c with
      | .recv _ => fun evs =>
        ∃ w4 : W4BinaryRecvPrekeyParams,
          W4BinaryRecvPrekeyDom g.c g.i w4 ∧ W4BinaryRecvPrekeyWideSlotEnvFixed w4 evs
      | _ => fun _ => False }

/-- Whole-`signal_session::run` binary-kit allocator trace predicate at
`mkBinaryKitRealCalleeEnvsFixed`. -/
abbrev realCliRunBinaryKitEnvOfFixed [LibsignalPlacement]
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (g : RunCall) : List AllocEvent → Prop :=
  CliRunBinaryEnv cliIo.rd (mkBinaryKitRealCalleeEnvsFixed img S X W g) sessionCapBytes g

/-- Whole-`main` binary-kit allocator trace predicate at `mkBinaryKitRealCalleeEnvsFixed`. -/
abbrev realCliMainBinaryKitEnvOfFixed [LibsignalPlacement]
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (i : Inputs) : List AllocEvent → Prop :=
  RealCliMainBinaryEnvOf (mkBinaryKitRealCalleeEnvsFixed img S X W) i

private theorem seqEnv_mono_local {A₁ A₂ B₁ B₂ : List AllocEvent → Prop}
    (ha : ∀ e, A₁ e → A₂ e) (hb : ∀ e, B₁ e → B₂ e) {evs : List AllocEvent}
    (h : SeqEnv A₁ B₁ evs) : SeqEnv A₂ B₂ evs := by
  rcases h with h1 | ⟨e₁, e₂, rfl, h1, h2⟩
  · exact Or.inl (ha evs h1)
  · exact Or.inr ⟨e₁, e₂, rfl, ha e₁ h1, hb e₂ h2⟩

private theorem optStageEnv_mono_local {A₁ A₂ : List AllocEvent → Prop}
    (ha : ∀ e, A₁ e → A₂ e) {evs : List AllocEvent}
    (h : OptStageEnv A₁ evs) : OptStageEnv A₂ evs :=
  h.elim Or.inl fun h1 => Or.inr (ha _ h1)

private theorem dirGetEnv_sub_fixed
    {PathEnv' : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {rd : ReadRule} {F0 : FsFiles} {d : DirGhost} {name : List (BitVec 8)}
    {evs : List AllocEvent}
    (h : DirGetEnv PathEnv' (ReadFileRuleEnv rd) rd F0 d name evs) :
    DirGetEnv PathEnv' (ReadFileRuleEnvFixed rd) rd F0 d name evs := by
  unfold DirGetEnv DirGetMissEnv at h ⊢
  cases hfind : d.changed.find? (fun e => e.1 == name) with
  | some _ =>
    rw [hfind] at h
    exact h
  | none =>
    rw [hfind] at h
    exact seqEnv_mono_local (fun _ hp => hp)
      (fun _ hr => seqEnv_mono_local (fun _ hrf => Or.inl hrf) (fun _ ha => ha) hr) h

private theorem kpkMarkPoll_sub_fixed {rd : ReadRule} {files : FsFiles}
    {kpkId spkId : BitVec 32} {baseKey : PublicKey} {evs : List AllocEvent}
    (h : W4BinaryKpkMarkStepEnv rd files kpkId spkId baseKey evs) :
    W4BinaryKpkMarkStepEnvFixed rd files kpkId spkId baseKey evs := by
  unfold W4BinaryKpkMarkStepEnv W4BoxedStoreStepEnv CliKpkMarkPollEnv
    KpkOneTimePreAfterGetEnv OptKpkMarkOneTimeTailEnv at h
  unfold W4BinaryKpkMarkStepEnvFixed W4BoxedStoreStepEnv CliKpkMarkPollEnv
    KpkOneTimePreAfterGetEnv OptKpkMarkOneTimeTailEnv
  refine seqEnv_mono_local (fun _ hb => hb) (fun _ hp => ?_) h
  refine seqEnv_mono_local (fun _ hpoll => ?_) (fun _ hf => hf) hp
  refine seqEnv_mono_local
    (fun _ hot => seqEnv_mono_local (fun _ hd => hd) (fun _ hg => dirGetEnv_sub_fixed hg) hot)
    (fun _ htail => ?_) hpoll
  dsimp only at htail ⊢
  cases hget : StoresGhost.opened.kyber.oneTime.get rd files (keyName kpkId) with
  | error u =>
    rw [hget] at htail
    cases u
    exact htail
  | ok bs =>
    cases bs with
    | cons _ _ =>
      rw [hget] at htail
      exact htail
    | nil =>
      rw [hget] at htail
      unfold KpkLastResortPreAfterGetEnv at htail ⊢
      exact seqEnv_mono_local (fun _ hf => hf)
        (fun _ hlr => seqEnv_mono_local
          (fun _ hpre => seqEnv_mono_local (fun _ hd => hd)
            (fun _ hres => seqEnv_mono_local (fun _ hr => hr)
              (fun _ hg => dirGetEnv_sub_fixed hg) hres) hpre)
          (fun _ hpost => hpost) hlr) htail

/-- Unconditional inclusion `W4BinaryRecvPrekeyWideSlotEnv w ⊆ W4BinaryRecvPrekeyWideSlotEnvFixed w`. -/
theorem w4BinaryRecvPrekeyWideSlotEnv_sub_fixed (w : W4BinaryRecvPrekeyParams)
    {evs : List AllocEvent} (h : W4BinaryRecvPrekeyWideSlotEnv w evs) :
    W4BinaryRecvPrekeyWideSlotEnvFixed w evs := by
  rcases h with hf | hs
  · exact Or.inl hf
  · refine Or.inr (seqEnv_mono_local (fun e he => ?_) (fun _ hf => hf) hs)
    rcases he with hu | hb | ha | hc
    · exact Or.inl hu
    · exact Or.inr (Or.inl hb)
    · refine Or.inr (Or.inr (Or.inl ?_))
      unfold W4BinaryRecvPrekeyPathAWideEnv at ha
      unfold W4BinaryRecvPrekeyPathAWideEnvFixed
      refine seqEnv_mono_local (fun _ h1 => h1) (fun _ h2 => ?_) ha
      refine seqEnv_mono_local (fun _ hp2 => hp2) (fun _ h3 => ?_) h2
      refine seqEnv_mono_local (fun _ hp3 => hp3)
        (fun _ h4 => optStageEnv_mono_local (fun _ hp4 => ?_) h4) h3
      unfold W4BinaryStageP4PathAWideEnv at hp4
      unfold W4BinaryStageP4PathAWideEnvFixed
      exact seqEnv_mono_local (fun _ hi => hi)
        (fun _ hm => seqEnv_mono_local
          (fun _ hm0 => optStageEnv_mono_local (fun _ hk => kpkMarkPoll_sub_fixed hk) hm0)
          (fun _ hr => hr) hm) hp4
    · refine Or.inr (Or.inr (Or.inr ?_))
      unfold W4BinaryRecvPrekeyPathCWideEnv at hc
      unfold W4BinaryRecvPrekeyPathCWideEnvFixed
      refine seqEnv_mono_local (fun _ h1 => h1) (fun _ h2 => ?_) hc
      refine seqEnv_mono_local (fun _ hp2 => hp2) (fun _ h3 => ?_) h2
      refine seqEnv_mono_local (fun _ hp3 => hp3)
        (fun _ h4 => optStageEnv_mono_local (fun _ hp4 => ?_) h4) h3
      unfold W4BinaryStageP4PathCWideEnv at hp4
      unfold W4BinaryStageP4PathCWideEnvFixed
      exact seqEnv_mono_local (fun _ hi => hi)
        (fun _ hm => seqEnv_mono_local
          (fun _ hm0 => optStageEnv_mono_local (fun _ hk => kpkMarkPoll_sub_fixed hk) hm0)
          (fun _ hr => hr) hm) hp4

/-! ## 5. `*Fixed` Slot Envelopes (`W3`, `W4` `AllFixed`, `binaryKitRunSlotEnvsFixed`) & Whole-`run` Bridges -/

/-- Binary-kit W3 (`init`) slot envelope at `ReadFileRuleEnvFixed cliIo.rd`
(`W3InitiateFullEnvWide`). -/
def W3InitBinaryKitSlotEnvFixed (w : W3BinaryInitParams) (evs : List AllocEvent) : Prop :=
  W3InitiateFullEnvWide
    (W3BoxedStoreStepEnv 32
      (cliIdentityKitTrustPollEnv
        (DirGetEnv PathEnv (ReadFileRuleEnvFixed cliIo.rd) cliIo.rd)
        w.x.F StoresGhost.opened.identity w.x.peer.val w.peerKey .sending))
    (W3BoxedStoreStepEnv 24
      (cliSessionKitLoadPollEnv cliIo.rd scopeKit
        (AddrTextValEnv DecimalEnv)
        (DirGetEnv PathEnv (ReadFileRuleEnvFixed cliIo.rd) cliIo.rd)
        (ofBytesEnv RecordDeserializeCancelEnv)
        w.x.F StoresGhost.opened.sessions w.x.peer.val))
    (W3BoxedStoreStepEnv 16
      (SeqEnv
        (DirGetEnv PathEnv (ReadFileRuleEnvFixed cliIo.rd) cliIo.rd
          w.x.F StoresGhost.opened.identity.own (utf8 "identity-key-pair"))
        (SeqEnv
          (OptIkpTryFromEnv
            (StoresGhost.opened.identity.own.get cliIo.rd w.x.F (utf8 "identity-key-pair")))
          FreeOnlyEvs)))
    (InitialStateEnv w.F w.x_spqr)
    (W3BoxedStoreStepEnv 16
      (SeqEnv
        (DirGetEnv PathEnv (ReadFileRuleEnvFixed cliIo.rd) cliIo.rd
          w.x.F StoresGhost.opened.identity.own (utf8 "registration-id"))
        (SeqEnv
          (OptRegIdMalformedEnv
            (StoresGhost.opened.identity.own.get cliIo.rd w.x.F (utf8 "registration-id")))
          FreeOnlyEvs)))
    (W3BoxedStoreStepEnv 32
      (cliIdentityKitSavePollEnv cliIo.rd
        (DirGetEnv PathEnv (ReadFileRuleEnvFixed cliIo.rd) cliIo.rd)
        DirPutStrEnv w.x.F StoresGhost.opened.identity w.x.peer.val w.peerKey))
    (W3BoxedStoreStepEnv 32
      (cliSessionKitStorePollEnv
        (AddrTextValEnv DecimalEnv)
        (RecordSerializeSeqFreeEnv w.g_rec)
        DirPutEnv StoresGhost.opened.sessions w.x.peer.val w.r_rec))
    w.x.peer.name.bytes.length
    evs

/-- `W3` (`init`) `InitGhost` slot envelope at `ReadFileRuleEnvFixed cliIo.rd`
(`RecordAliceInitiatedAnyCkBounds`). -/
def realCliInitBinarySlotEnvFixed (W : CliHooks) (x : InitGhost) (evs : List AllocEvent) : Prop :=
  ∃ w : W3BinaryInitParams,
    w.x = x ∧
    w.F = W.C.F ∧
    w.x_spqr.p.authKey.length ≤ 32 ∧
    RecordGhostValid w.g_rec w.r_rec ∧
    RecordAliceInitiatedAnyCkBounds w.g_rec w.r_rec ∧
    W3InitBinaryKitSlotEnvFixed w evs

/-- Under `CliPqxdhInputs P i` and `w.x.F = runFiles i`, `W3InitBinaryKitSlotEnvFixed w` collapses
to `W3InitBinaryKitSlotEnv w`. -/
theorem w3InitBinaryKitSlotEnvFixed_eq_plain {P : PEParams} {i : Inputs}
    (hi : CliPqxdhInputs P i) {w : W3BinaryInitParams} (hx : w.x.F = runFiles i) :
    W3InitBinaryKitSlotEnvFixed w = W3InitBinaryKitSlotEnv w := by
  funext evs
  unfold W3InitBinaryKitSlotEnvFixed W3InitBinaryKitSlotEnv
  rw [hx,
    w1IdTrustPoll_fixed_eq hi w.x.peer.val w.peerKey .sending,
    w1SessLoadPoll_fixed_eq hi w.x.peer.val,
    dirGetEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_own_ikp hi),
    dirGetEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_own_regId hi),
    w1IdSavePoll_fixed_eq hi w.x.peer.val w.peerKey]

/-- W4 binary-kit step envelopes with `ReadFileRuleEnvFixed rd` on all store-kit `Dir::get` calls
(matching Block-`579` / `DecPkD2cSlotOkLinked` instantiated at `ReadEnv := ReadFileRuleEnvFixed cliIo.rd`
before `CliPqxdhInputs` collapses the non-`kpkMark` steps). -/
def W4BinarySessLoadStepEnvAllFixed (rd : ReadRule) (files : FsFiles) (peer : AddrGhost) :
    List AllocEvent → Prop :=
  W4BoxedStoreStepEnv 24
    (cliSessionKitLoadPollEnv rd scopeKit (AddrTextValEnv DecimalEnv)
      (DirGetEnv PathEnv (ReadFileRuleEnvFixed rd) rd) (ofBytesEnv RecordDeserializeCancelEnv)
      files StoresGhost.opened.sessions peer.val)

def W4BinaryIdTrustStepEnvAllFixed (rd : ReadRule) (files : FsFiles) (peer : AddrGhost)
    (remoteIdKey : IdentityKey) : List AllocEvent → Prop :=
  W4BoxedStoreStepEnv 32
    (cliIdentityKitTrustPollEnv (DirGetEnv PathEnv (ReadFileRuleEnvFixed rd) rd)
      files StoresGhost.opened.identity peer.val remoteIdKey .receiving)

def W4BinaryIdSaveStepEnvAllFixed (rd : ReadRule) (files : FsFiles) (peer : AddrGhost)
    (remoteIdKey : IdentityKey) : List AllocEvent → Prop :=
  W4BoxedStoreStepEnv 32
    (cliIdentityKitSavePollEnv rd (DirGetEnv PathEnv (ReadFileRuleEnvFixed rd) rd)
      DirPutStrEnv files StoresGhost.opened.identity peer.val remoteIdKey)

def W4BinarySpkGetStepEnvAllFixed (rd : ReadRule) (files : FsFiles) (spkId : BitVec 32) :
    List AllocEvent → Prop :=
  W4BoxedStoreStepEnv 16
    (CliSpkGetPollEnv DecimalEnv
      (fun d k => DirGetEnv PathEnv (ReadFileRuleEnvFixed rd) rd files d (keyName k))
      CliSpkDecodeEnv rd files ⟨0#64, 0#64, 0#64, spkId, StoresGhost.opened.signed⟩)

def W4BinaryKpkGetStepEnvAllFixed (rd : ReadRule) (files : FsFiles) (kpkId : BitVec 32) :
    List AllocEvent → Prop :=
  W4BoxedStoreStepEnv 16
    (CliKpkGetPollEnv DecimalEnv
      (fun d k => DirGetEnv PathEnv (ReadFileRuleEnvFixed rd) rd files d (keyName k))
      CliSpkDecodeEnv rd files ⟨0#64, 0#64, 0#64, kpkId, StoresGhost.opened.kyber⟩)

def W4BinaryPkGetStepEnvAllFixed (rd : ReadRule) (files : FsFiles) (opkId : BitVec 32) :
    List AllocEvent → Prop :=
  W4BoxedStoreStepEnv 16
    (CliPkGetPollEnv DecimalEnv (DirGetEnv PathEnv (ReadFileRuleEnvFixed rd) rd files)
      CliPkDecodeEnv rd files ⟨0#64, 0#64, 0#64, opkId, StoresGhost.opened.oneTime⟩)

def W4BinarySelfKpStepEnvAllFixed (rd : ReadRule) (files : FsFiles) : List AllocEvent → Prop :=
  CliRealBinaryKitEnvs.W4OptBoxedStoreStepEnv 16
    (SeqEnv (DirGetEnv PathEnv (ReadFileRuleEnvFixed rd) rd files
        StoresGhost.opened.identity.own (utf8 "identity-key-pair"))
      (SeqEnv
        (OptIkpTryFromEnv (StoresGhost.opened.identity.own.get rd files (utf8 "identity-key-pair")))
        FreeOnlyEvs))

abbrev W4BinarySelfKpStepOptEnvAllFixed := W4BinarySelfKpStepEnvAllFixed

def W4BinarySelfRegIdStepEnvAllFixed (rd : ReadRule) (files : FsFiles) : List AllocEvent → Prop :=
  W4BoxedStoreStepEnv 16
    (SeqEnv (DirGetEnv PathEnv (ReadFileRuleEnvFixed rd) rd files
        StoresGhost.opened.identity.own (utf8 "registration-id"))
      (SeqEnv
        (OptRegIdMalformedEnv
          (StoresGhost.opened.identity.own.get rd files (utf8 "registration-id")))
        FreeOnlyEvs))

def W4BinaryPkRemoveStepEnvAllFixed (rd : ReadRule) (files : FsFiles) (opkId : BitVec 32) :
    List AllocEvent → Prop :=
  W4BoxedStoreStepEnv 16
    (CliPkRemovePollEnv rd DecimalEnv (DirGetEnv PathEnv (ReadFileRuleEnvFixed rd) rd) DirPutEnv
      files ⟨0#64, 0#64, 0#64, opkId, StoresGhost.opened.oneTime⟩)

def W4BinaryStageP1OkEnvAllFixed (rd : ReadRule) (files : FsFiles) (peer : AddrGhost)
    (remoteIdKey : IdentityKey) (evs : List AllocEvent) : Prop :=
  SeqEnv (W4BinarySessLoadStepEnvAllFixed rd files peer)
    (OptStageEnv (W4BinaryIdTrustStepEnvAllFixed rd files peer remoteIdKey)) evs

def W4BinaryStageP1UntrustedEnvAllFixed (rd : ReadRule) (files : FsFiles) (peer : AddrGhost)
    (remoteIdKey : IdentityKey) (evs : List AllocEvent) : Prop :=
  SeqEnv (W4BinarySessLoadStepEnvAllFixed rd files peer)
    (SeqEnv (W4BinaryIdTrustStepEnvAllFixed rd files peer remoteIdKey)
      (SeqEnv (StringCloneEnv peer.name) FreeOnlyEvs)) evs

def W4BinaryStageP2PathAWideEnvAllFixed (hasOpk : Bool) (rd : ReadRule) (files : FsFiles)
    (spkId kpkId opkId : BitVec 32)
    (F : ShaCompress) (x_res : DoReserveCall) (x_spqr : InitialStateGhost)
    (evs : List AllocEvent) : Prop :=
  SeqEnv (OptStageEnv (SeqEnv (W4BoundedEvs 1 33) FreeOnlyEvs))
    (SeqEnv (OptStageEnv (W4BinarySpkGetStepEnvAllFixed rd files spkId))
      (SeqEnv (OptStageEnv (W4BinaryKpkGetStepEnvAllFixed rd files kpkId))
        (SeqEnv (OptStageEnv (SeqEnv KemKeyPairFromPubPrivEnv FreeOnlyEvs))
          (SeqEnv (OptStageEnv (SeqEnv (W4BoundedEvs 1 21) FreeOnlyEvs))
            (SeqEnv (OptStageEnv (if hasOpk then W4BinaryPkGetStepEnvAllFixed rd files opkId else (· = [])))
              (SeqEnv (OptStageEnv (W4BinarySelfKpStepEnvAllFixed rd files))
                (SeqEnv (OptStageEnv (W4BinaryInitBobWideEnv F x_res hasOpk x_spqr))
                  (SeqEnv (OptStageEnv (W4BinarySelfRegIdStepEnvAllFixed rd files))
                    W4ErrTailWideEnv)))))))) evs

def W4BinaryStageP2PathCWideEnvAllFixed {α : Type}
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
        (SeqEnv (OptStageEnv (W4BinarySpkGetStepEnvAllFixed rd files spkId))
          (SeqEnv (OptStageEnv (W4BinaryKpkGetStepEnvAllFixed rd files kpkId))
            (SeqEnv (OptStageEnv (SeqEnv KemKeyPairFromPubPrivEnv FreeOnlyEvs))
              (SeqEnv (OptStageEnv (SeqEnv (W4BoundedEvs 1 21) FreeOnlyEvs))
                (SeqEnv (OptStageEnv (if hasOpk then W4BinaryPkGetStepEnvAllFixed rd files opkId else (· = [])))
                  (SeqEnv (OptStageEnv (W4BinarySelfKpStepEnvAllFixed rd files))
                    (SeqEnv (OptStageEnv (W4BinaryInitBobWideEnv F x_res hasOpk x_spqr))
                      (SeqEnv (OptStageEnv (W4BinarySelfRegIdStepEnvAllFixed rd files))
                        (SeqEnv (OptStageEnv (W4BinaryPromoteArchiveEnv g_arch r_arch))
                          W4ErrTailWideEnv))))))))))) evs

def W4BinaryStageP4MatchedWideEnvAllFixed (rd : ReadRule) (files : FsFiles) (peer : AddrGhost)
    (remoteIdKey : IdentityKey) (g_out0 : RecordGhost) (r_out0 : SessionRecord (List (BitVec 8)))
    (evs : List AllocEvent) : Prop :=
  SeqEnv (OptStageEnv (W4BinaryIdSaveStepEnvAllFixed rd files peer remoteIdKey))
    (SeqEnv (OptStageEnv (W4BinarySessStoreStepEnv peer g_out0 r_out0)) FreeOnlyEvs) evs

def W4BinaryStageP4PathAWideEnvAllFixed (hasOpk : Bool) (rd : ReadRule) (files : FsFiles)
    (peer : AddrGhost) (remoteIdKey : IdentityKey)
    (kpkId spkId opkId : BitVec 32) (baseKey : PublicKey)
    (g_out0 : RecordGhost) (r_out0 : SessionRecord (List (BitVec 8)))
    (evs : List AllocEvent) : Prop :=
  SeqEnv (OptStageEnv (W4BinaryIdSaveStepEnvAllFixed rd files peer remoteIdKey))
    (SeqEnv (OptStageEnv (W4BinaryKpkMarkStepEnvFixed rd files kpkId spkId baseKey))
      (SeqEnv (OptStageEnv (if hasOpk then W4BinaryPkRemoveStepEnvAllFixed rd files opkId else (· = [])))
        (SeqEnv (OptStageEnv (W4BinarySessStoreStepEnv peer g_out0 r_out0)) FreeOnlyEvs))) evs

def W4BinaryStageP4PathCWideEnvAllFixed (hasOpk : Bool) (rd : ReadRule) (files : FsFiles)
    (peer : AddrGhost) (remoteIdKey : IdentityKey)
    (kpkId spkId opkId : BitVec 32) (baseKey : PublicKey)
    (G_out1 : SessionGhost) (sess_out1 : Session (List (BitVec 8))) (enc_prev1 : List (BitVec 8))
    (evs : List AllocEvent) : Prop :=
  SeqEnv (OptStageEnv (W4BinaryIdSaveStepEnvAllFixed rd files peer remoteIdKey))
    (SeqEnv (OptStageEnv (W4BinaryKpkMarkStepEnvFixed rd files kpkId spkId baseKey))
      (SeqEnv (OptStageEnv (if hasOpk then W4BinaryPkRemoveStepEnvAllFixed rd files opkId else (· = [])))
        (SeqEnv (OptStageEnv (W4BinarySessStorePrev1StepEnv peer G_out1 sess_out1 enc_prev1))
          FreeOnlyEvs))) evs

/-- Complete 4-arm W4 (`recv-prekey`) slot envelope with `ReadFileRuleEnvFixed` on all store-kit
`Dir::get` steps; under `CliPqxdhInputs P i` (`w.base.files = runFiles i`, `w.base.rd = cliIo.rd`),
collapses to `W4BinaryRecvPrekeyWideSlotEnvFixed w`. -/
def W4BinaryRecvPrekeyWideSlotEnvAllFixed (w : W4BinaryRecvPrekeyParams)
    (evs : List AllocEvent) : Prop :=
  let P := mkW4RecvPrekeyWideSlotParams w.base
  FreeOnlyEvs evs ∨
  SeqEnv
    (fun e =>
      W4BinaryStageP1UntrustedEnvAllFixed w.base.rd w.base.files w.base.peer w.remoteIdKey e ∨
      SeqEnv (W4BinaryStageP1OkEnvAllFixed w.base.rd w.base.files w.base.peer w.remoteIdKey)
        (SeqEnv
          (OptStageEnv
            (W4BinaryStageP2MatchedWideEnv P.DecEnv P.TrialEnv P.DropEnv P.archivedTrials
              w.base.g_arch w.base.r_arch))
          (SeqEnv (OptStageEnv (W4StageP3WideEnv W4CloneBDomEnv P.TryDecEnv))
            (OptStageEnv
              (W4BinaryStageP4MatchedWideEnvAllFixed w.base.rd w.base.files w.base.peer
                w.remoteIdKey w.base.g_out0 w.base.r_out0)))) e ∨
      SeqEnv (W4BinaryStageP1OkEnvAllFixed w.base.rd w.base.files w.base.peer w.remoteIdKey)
        (SeqEnv
          (OptStageEnv
            (W4BinaryStageP2PathAWideEnvAllFixed w.base.hasOpk w.base.rd w.base.files
              w.base.spkId w.base.kpkId w.base.opkId w.base.F w.base.x_res w.base.x_spqr))
          (SeqEnv (OptStageEnv (W4StageP3WideEnv W4CloneACDomEnv (W4RecvPrekeyTryDecACEnv w.base)))
            (OptStageEnv
              (W4BinaryStageP4PathAWideEnvAllFixed w.base.hasOpk w.base.rd w.base.files w.base.peer
                w.remoteIdKey w.base.kpkId w.base.spkId w.base.opkId w.baseKey
                w.base.g_out0 w.base.r_out0)))) e ∨
      SeqEnv (W4BinaryStageP1OkEnvAllFixed w.base.rd w.base.files w.base.peer w.remoteIdKey)
        (SeqEnv
          (OptStageEnv
            (W4BinaryStageP2PathCWideEnvAllFixed w.base.G_cur w.base.st_cur P.CurTrialFailEnv
              P.DecEnv P.TrialEnv P.DropEnv P.archivedTrials w.base.g_arch w.base.r_arch
              w.base.hasOpk w.base.rd w.base.files w.base.spkId w.base.kpkId w.base.opkId
              w.base.F w.base.x_res w.base.x_spqr))
          (SeqEnv (OptStageEnv (W4StageP3WideEnv W4CloneACDomEnv (W4RecvPrekeyTryDecACEnv w.base)))
            (OptStageEnv
              (W4BinaryStageP4PathCWideEnvAllFixed w.base.hasOpk w.base.rd w.base.files w.base.peer
                w.remoteIdKey w.base.kpkId w.base.spkId w.base.opkId w.baseKey
                w.base.G_out1 w.base.sess_out1 w.base.enc_prev1)))) e)
    FreeOnlyEvs evs

/-- Under `CliPqxdhInputs P i` (`w.base.files = runFiles i`, `w.base.rd = cliIo.rd`), all 9
non-`kpkMark` store steps in `W4BinaryRecvPrekeyWideSlotEnvAllFixed w` satisfy `¬ OverCapFile`, so
`W4BinaryRecvPrekeyWideSlotEnvAllFixed w` equals `W4BinaryRecvPrekeyWideSlotEnvFixed w`. -/
theorem w4BinaryRecvPrekeyWideSlotEnvAllFixed_eq_fixed {P : PEParams} {i : Inputs}
    (hi : CliPqxdhInputs P i) {w : W4BinaryRecvPrekeyParams}
    (hfiles : w.base.files = runFiles i) (hrd : w.base.rd = cliIo.rd) :
    W4BinaryRecvPrekeyWideSlotEnvAllFixed w = W4BinaryRecvPrekeyWideSlotEnvFixed w := by
  have hsess : ∀ peer,
      W4BinarySessLoadStepEnvAllFixed cliIo.rd (runFiles i) peer =
        CliRealBinaryKitEnvs.W4BinarySessLoadStepEnv cliIo.rd (runFiles i) peer := by
    intro peer
    unfold W4BinarySessLoadStepEnvAllFixed CliRealBinaryKitEnvs.W4BinarySessLoadStepEnv
    rw [w1SessLoadPoll_fixed_eq hi peer.val]
  have htrust : ∀ peer k,
      W4BinaryIdTrustStepEnvAllFixed cliIo.rd (runFiles i) peer k =
        CliRealBinaryKitEnvs.W4BinaryIdTrustStepEnv cliIo.rd (runFiles i) peer k := by
    intro peer k
    unfold W4BinaryIdTrustStepEnvAllFixed CliRealBinaryKitEnvs.W4BinaryIdTrustStepEnv
    rw [w1IdTrustPoll_fixed_eq hi peer.val k .receiving]
  have hsave : ∀ peer k,
      W4BinaryIdSaveStepEnvAllFixed cliIo.rd (runFiles i) peer k =
        CliRealBinaryKitEnvs.W4BinaryIdSaveStepEnv cliIo.rd (runFiles i) peer k := by
    intro peer k
    unfold W4BinaryIdSaveStepEnvAllFixed CliRealBinaryKitEnvs.W4BinaryIdSaveStepEnv
    rw [w1IdSavePoll_fixed_eq hi peer.val k]
  have hspk : ∀ id,
      W4BinarySpkGetStepEnvAllFixed cliIo.rd (runFiles i) id =
        CliRealBinaryKitEnvs.W4BinarySpkGetStepEnv cliIo.rd (runFiles i) id := by
    intro id
    unfold W4BinarySpkGetStepEnvAllFixed CliRealBinaryKitEnvs.W4BinarySpkGetStepEnv CliSpkGetPollEnv
    dsimp only
    rw [dirGetEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_signed hi _)]
  have hkpk : ∀ id,
      W4BinaryKpkGetStepEnvAllFixed cliIo.rd (runFiles i) id =
        CliRealBinaryKitEnvs.W4BinaryKpkGetStepEnv cliIo.rd (runFiles i) id := by
    intro id
    unfold W4BinaryKpkGetStepEnvAllFixed CliRealBinaryKitEnvs.W4BinaryKpkGetStepEnv CliKpkGetPollEnv
      SignalSession.Cli.Store.KpkGetPoll.LayoutBudget.KpkPassEnv
    dsimp only
    rw [dirGetEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_kyberOneTime hi _),
      dirGetEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_kyberLastResort_keyName hi id)]
  have hpk : ∀ id,
      W4BinaryPkGetStepEnvAllFixed cliIo.rd (runFiles i) id =
        CliRealBinaryKitEnvs.W4BinaryPkGetStepEnv cliIo.rd (runFiles i) id := by
    intro id
    unfold W4BinaryPkGetStepEnvAllFixed CliRealBinaryKitEnvs.W4BinaryPkGetStepEnv CliPkGetPollEnv
    dsimp only
    rw [dirGetEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_oneTime hi _)]
  have hselfKp :
      W4BinarySelfKpStepEnvAllFixed cliIo.rd (runFiles i) =
        CliRealBinaryKitEnvs.W4BinarySelfKpStepEnv cliIo.rd (runFiles i) := by
    unfold W4BinarySelfKpStepEnvAllFixed CliRealBinaryKitEnvs.W4BinarySelfKpStepEnv
    rw [dirGetEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_own_ikp hi)]
  have hselfReg :
      W4BinarySelfRegIdStepEnvAllFixed cliIo.rd (runFiles i) =
        CliRealBinaryKitEnvs.W4BinarySelfRegIdStepEnv cliIo.rd (runFiles i) := by
    unfold W4BinarySelfRegIdStepEnvAllFixed CliRealBinaryKitEnvs.W4BinarySelfRegIdStepEnv
    rw [dirGetEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_own_regId hi)]
  have hpkRem : ∀ id,
      W4BinaryPkRemoveStepEnvAllFixed cliIo.rd (runFiles i) id =
        W4BinaryPkRemoveStepEnv cliIo.rd (runFiles i) id := by
    intro id
    unfold W4BinaryPkRemoveStepEnvAllFixed W4BinaryPkRemoveStepEnv CliPkRemovePollEnv
    dsimp only
    rw [dirGetEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_oneTime hi _)]
  have hp1ok : ∀ peer k,
      W4BinaryStageP1OkEnvAllFixed cliIo.rd (runFiles i) peer k =
        W4BinaryStageP1OkEnv cliIo.rd (runFiles i) peer k := by
    intro peer k; funext evs
    unfold W4BinaryStageP1OkEnvAllFixed W4BinaryStageP1OkEnv
    rw [hsess, htrust]
  have hp1un : ∀ peer k,
      W4BinaryStageP1UntrustedEnvAllFixed cliIo.rd (runFiles i) peer k =
        W4BinaryStageP1UntrustedEnv cliIo.rd (runFiles i) peer k := by
    intro peer k; funext evs
    unfold W4BinaryStageP1UntrustedEnvAllFixed W4BinaryStageP1UntrustedEnv
    rw [hsess, htrust]
  have hp2a : ∀ hasOpk spkId kpkId opkId F x_res x_spqr,
      W4BinaryStageP2PathAWideEnvAllFixed hasOpk cliIo.rd (runFiles i) spkId kpkId opkId F x_res x_spqr =
        W4BinaryStageP2PathAWideEnv hasOpk cliIo.rd (runFiles i) spkId kpkId opkId F x_res x_spqr := by
    intro hasOpk spkId kpkId opkId F x_res x_spqr; funext evs
    unfold W4BinaryStageP2PathAWideEnvAllFixed W4BinaryStageP2PathAWideEnv
    rw [hspk, hkpk, hpk, hselfKp, hselfReg]
  have hp2c : ∀ {α : Type} G_cur st_cur CurTrialFailEnv
      (DecEnv TrialEnv DropEnv : α → List AllocEvent → Prop) xs g_arch r_arch
      hasOpk spkId kpkId opkId F x_res x_spqr,
      W4BinaryStageP2PathCWideEnvAllFixed G_cur st_cur CurTrialFailEnv DecEnv TrialEnv DropEnv xs
          g_arch r_arch hasOpk cliIo.rd (runFiles i) spkId kpkId opkId F x_res x_spqr =
        W4BinaryStageP2PathCWideEnv G_cur st_cur CurTrialFailEnv DecEnv TrialEnv DropEnv xs
          g_arch r_arch hasOpk cliIo.rd (runFiles i) spkId kpkId opkId F x_res x_spqr := by
    intro α G_cur st_cur CurTrialFailEnv DecEnv TrialEnv DropEnv xs g_arch r_arch
      hasOpk spkId kpkId opkId F x_res x_spqr; funext evs
    unfold W4BinaryStageP2PathCWideEnvAllFixed W4BinaryStageP2PathCWideEnv
    rw [hspk, hkpk, hpk, hselfKp, hselfReg]
  have hp4m : ∀ peer k g_out0 r_out0,
      W4BinaryStageP4MatchedWideEnvAllFixed cliIo.rd (runFiles i) peer k g_out0 r_out0 =
        W4BinaryStageP4MatchedWideEnv cliIo.rd (runFiles i) peer k g_out0 r_out0 := by
    intro peer k g_out0 r_out0; funext evs
    unfold W4BinaryStageP4MatchedWideEnvAllFixed W4BinaryStageP4MatchedWideEnv
    rw [hsave]
  have hp4a : ∀ hasOpk peer k kpkId spkId opkId bk g_out0 r_out0,
      W4BinaryStageP4PathAWideEnvAllFixed hasOpk cliIo.rd (runFiles i) peer k kpkId spkId opkId bk g_out0 r_out0 =
        W4BinaryStageP4PathAWideEnvFixed hasOpk cliIo.rd (runFiles i) peer k kpkId spkId opkId bk g_out0 r_out0 := by
    intro hasOpk peer k kpkId spkId opkId bk g_out0 r_out0; funext evs
    unfold W4BinaryStageP4PathAWideEnvAllFixed W4BinaryStageP4PathAWideEnvFixed
    rw [hsave, hpkRem]
  have hp4c : ∀ hasOpk peer k kpkId spkId opkId bk G_out1 sess_out1 enc_prev1,
      W4BinaryStageP4PathCWideEnvAllFixed hasOpk cliIo.rd (runFiles i) peer k kpkId spkId opkId bk
          G_out1 sess_out1 enc_prev1 =
        W4BinaryStageP4PathCWideEnvFixed hasOpk cliIo.rd (runFiles i) peer k kpkId spkId opkId bk
          G_out1 sess_out1 enc_prev1 := by
    intro hasOpk peer k kpkId spkId opkId bk G_out1 sess_out1 enc_prev1; funext evs
    unfold W4BinaryStageP4PathCWideEnvAllFixed W4BinaryStageP4PathCWideEnvFixed
    rw [hsave, hpkRem]
  funext evs
  unfold W4BinaryRecvPrekeyWideSlotEnvAllFixed W4BinaryRecvPrekeyWideSlotEnvFixed
    W4BinaryRecvPrekeyPathBWideEnv W4BinaryRecvPrekeyPathAWideEnvFixed
    W4BinaryRecvPrekeyPathCWideEnvFixed
  dsimp only
  rw [hfiles, hrd, hp1un, hp1ok, hp2a, hp2c, hp4m, hp4a, hp4c]

/-- Widened binary-kit `W4` (`recv-prekey`) slot envelope over `W4BinaryRecvPrekeyParams` at
`W4BinaryRecvPrekeyWideSlotEnvAllFixed` (`ReadFileRuleEnvFixed` on all W4 store steps). -/
abbrev realCliDecPkBinaryWideSlotEnvFixed [LibsignalPlacement]
    (_X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x : DecPkGhost) (evs : List AllocEvent) : Prop :=
  ∃ w4 : W4BinaryRecvPrekeyParams,
    W4BinaryCallSiteDom W.C.F W.Q.K x.msg.message.ciphertext.length x.peer.val x.F w4.base ∧
      w4.remoteIdKey = x.msg.identityKey ∧
      w4.baseKey = x.msg.baseKey ∧
      W4BinaryRecvPrekeyWideSlotEnvAllFixed w4 evs

theorem realCliDecPkBinaryWideSlotEnvFixed_ghost_congr [LibsignalPlacement]
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (x y : DecPkGhost)
    (hp : x.peer.val = y.peer.val)
    (_hm : x.me.val = y.me.val)
    (_hs : x.stores = y.stores)
    (_hcp : x.coinsP = y.coinsP)
    (hf : x.F = y.F)
    (_hc : x.coins = y.coins)
    (hmsg : x.msg = y.msg) :
    realCliDecPkBinaryWideSlotEnvFixed X W x = realCliDecPkBinaryWideSlotEnvFixed X W y := by
  funext evs
  simp only [realCliDecPkBinaryWideSlotEnvFixed, hp, hf, hmsg]

/-- Binary-kit `RunSlotEnvs` bundle at `w1BinarySessKitPlacedBudgetFixed`,
`w1BinaryIdKitPlacedBudgetFixed`, `decBinarySessKitPlacedBudgetFixed`,
`decBinaryIdKitPlacedBudgetFixed`, `SpqrSendTightCapEnv`, `W2RealTdEnv W.C.F W.Q.K`, and
caller-supplied `InitEnv` / `DecPkEnv`. -/
noncomputable def binaryKitRunSlotEnvsFixed [LibsignalPlacement] {M : AllocCostModel}
    (W : CliHooks) (A : RustCliAllocBudget M) (B : RunBudgets := cliRunBudgets)
    (InitEnv : InitGhost → List AllocEvent → Prop)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop) : RunSlotEnvs where
  encrypt := CliEncryptSlotEnv ⟨W.C, W.Q⟩ A B SpqrSendTightCapEnv
    (w1BinarySessKitPlacedBudgetFixed A.repAlloc B)
    (w1BinaryIdKitPlacedBudgetFixed A.repAlloc B)
  decryptSignal := CliDecryptSignalSlotEnv ⟨W.C, W.Q⟩ A B (W2RealTdEnv W.C.F W.Q.K)
    (decBinarySessKitPlacedBudgetFixed A.repAlloc B)
    (decBinaryIdKitPlacedBudgetFixed A.repAlloc B)
  initiate := InitEnv
  decryptPrekey := DecPkEnv

private theorem preEnv_fixed_eq_plain {P : PEParams} {g : RunCall} (hi : CliPqxdhInputs P g.i) :
    PreEnv (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd)) g =
      PreEnv (cliRunCalleesEnvs (ReadFileRuleEnv cliIo.rd)) g := by
  funext evs
  unfold PreEnv cliRunCalleesEnvs
  dsimp only
  rw [dirGetEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_own_address hi)]

private theorem init1Env_fixed_eq_plain {P : PEParams} {g : RunCall} (hi : CliPqxdhInputs P g.i)
    (me : MeAtDispatch) (peerV : AddrV) (dir : List (BitVec 8)) :
    Init1Env (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd)) g me peerV dir =
      Init1Env (cliRunCalleesEnvs (ReadFileRuleEnv cliIo.rd)) g me peerV dir := by
  funext evs
  cases me with
  | none => rfl
  | some _ _ =>
    unfold Init1Env cliRunCalleesEnvs
    dsimp only
    rw [readFileRuleEnvFixed_eq_of_not_overCap (not_overCapFile_runFiles_bundle_idKey hi dir)]

private theorem init2Env_fixed_eq_plain {P : PEParams} {g : RunCall} (hi : CliPqxdhInputs P g.i)
    (d1 : Init1Data) :
    Init2Env (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd)) g d1 =
      Init2Env (cliRunCalleesEnvs (ReadFileRuleEnv cliIo.rd)) g d1 := by
  let cF := cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd)
  let cP := cliRunCalleesEnvs (ReadFileRuleEnv cliIo.rd)
  have hreg : cF.readFile (runFiles g.i) (d1.dir ++ [0x2f#8] ++ utf8 "registration-id") =
      cP.readFile (runFiles g.i) (d1.dir ++ [0x2f#8] ++ utf8 "registration-id") :=
    readFileRuleEnvFixed_eq_of_not_overCap (not_overCapFile_runFiles_bundle_regId hi d1.dir)
  have hspk : cF.readFile (runFiles g.i) (d1.dir ++ [0x2f#8] ++ utf8 "signed-pre-key") =
      cP.readFile (runFiles g.i) (d1.dir ++ [0x2f#8] ++ utf8 "signed-pre-key") :=
    readFileRuleEnvFixed_eq_of_not_overCap (not_overCapFile_runFiles_bundle_spk hi d1.dir)
  have hkpk : cF.bundleRead (runFiles g.i) d1.dir (utf8 "kyber-pre-key") =
      cP.bundleRead (runFiles g.i) d1.dir (utf8 "kyber-pre-key") :=
    bundleReadEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_bundle_kpk hi d1.dir)
  have hopk : cF.bundleRead (runFiles g.i) d1.dir (utf8 "one-time-pre-key") =
      cP.bundleRead (runFiles g.i) d1.dir (utf8 "one-time-pre-key") :=
    bundleReadEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_bundle_opk hi d1.dir)
  have hsid : cF.splitId = cP.splitId := rfl
  have hssg : cF.splitSigned = cP.splitSigned := rfl
  have hopkOk : ∀ bs, R1bStepOpkOkEnv cF (runFiles g.i) d1.dir bs =
      R1bStepOpkOkEnv cP (runFiles g.i) d1.dir bs := by
    intro bs; funext evs; unfold R1bStepOpkOkEnv; rw [hopk, hsid]
  have hopkErr : R1bStepOpkErrEnv cF (runFiles g.i) d1.dir =
      R1bStepOpkErrEnv cP (runFiles g.i) d1.dir := by
    funext evs; unfold R1bStepOpkErrEnv; rw [hopk, hsid]
  have hst3 : ∀ spkKey kpkKey, Init2Stage3Env cF (runFiles g.i) d1.dir spkKey kpkKey =
      Init2Stage3Env cP (runFiles g.i) d1.dir spkKey kpkKey := by
    intro spkKey kpkKey; funext evs; unfold Init2Stage3Env
    rw [hopk, hopkErr, hsid]; simp only [hopkOk]
  have hkpkOk : ∀ bs, R1bStepKpkOkEnv cF (runFiles g.i) d1.dir bs =
      R1bStepKpkOkEnv cP (runFiles g.i) d1.dir bs := by
    intro bs; funext evs; unfold R1bStepKpkOkEnv; rw [hkpk, hssg]
  have hkpkErr : R1bStepKpkErrEnv cF (runFiles g.i) d1.dir =
      R1bStepKpkErrEnv cP (runFiles g.i) d1.dir := by
    funext evs; unfold R1bStepKpkErrEnv; rw [hkpk]; simp only [hkpkOk]
  have hst2 : ∀ spkKey, Init2Stage2Env cF (runFiles g.i) d1.dir spkKey =
      Init2Stage2Env cP (runFiles g.i) d1.dir spkKey := by
    intro spkKey; funext evs; unfold Init2Stage2Env
    rw [hkpk, hkpkErr]; simp only [hkpkOk, hst3]
  have hafter : Init2AfterRegOkEnv cF (runFiles g.i) d1.dir =
      Init2AfterRegOkEnv cP (runFiles g.i) d1.dir := by
    funext evs; unfold Init2AfterRegOkEnv
    dsimp only
    rw [hspk, hssg]; simp only [hst2]
  funext evs
  change Init2Env cF g d1 evs = Init2Env cP g d1 evs
  unfold Init2Env
  dsimp only
  rw [hreg, hafter]

/-- `W4` (`recv-prekey`, `hrecvP_slot`) containment from `realCliDecPkBinaryWideSlotEnvFixed` into
`(mkBinaryKitRealCalleeEnvsFixed img S X W g).decPkEnv` under `CliPqxdhInputs ⟨W.C, W.Q⟩ g.i`. -/
theorem w4_realCliDecPkBinaryWideSlotEnvFixed_sub_binaryKitFixed [LibsignalPlacement]
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (g : RunCall) (meV : AddrV) (peerV : AddrV)
    (rest : List (BitVec 8)) (pm : PreKeySignalMessage)
    (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c)
    (hin : (inputOf g.i g.c).length ≤ stdinCapBytes)
    (hc : g.c = .recv peerV)
    (hst : g.i.stdin = 3#8 :: rest)
    (hpk : S.pksmParse rest = some pm)
    {evs : List AllocEvent}
    (hevs : realCliDecPkBinaryWideSlotEnvFixed X W (r3bDecPkGhost g meV peerV pm) evs)
    (hS_pksm : S.pksmParse = pksmParse := by rfl) :
    (mkBinaryKitRealCalleeEnvsFixed img S X W g).decPkEnv evs := by
  obtain ⟨w4, hcs, _hik, _hbk, henvAll⟩ := hevs
  have hparse_recv : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) :=
    hc ▸ hparse
  have hpk' : pksmParse rest = some pm := hS_pksm ▸ hpk
  have hct_rest : pm.message.ciphertext.length ≤ rest.length :=
    (pksmParse_lengths_le hpk').2.2.1
  have hrest_cap : rest.length ≤ msgCapBytes :=
    recv_rest_length_le_msgCapBytes hin hc hst
  have hct_cap : pm.message.ciphertext.length ≤ msgCapBytes :=
    Nat.le_trans hct_rest hrest_cap
  have hdom : W4RecvPrekeyRealDomOf sessionCapBytes msgCapBytes w4.base :=
    hcs.toRealDomOf hparse_recv hct_cap
  have hdom4 : W4BinaryRecvPrekeyDom g.c g.i w4 := by
    intro pAddr hpAddr
    rw [hc] at hpAddr
    injection hpAddr with hpEq
    subst hpEq
    exact ⟨hcs.eq_peerVal, hdom.outer_dom.peer_len, hcs.eq_files, hcs.eq_rd, hdom⟩
  have henvFixed : W4BinaryRecvPrekeyWideSlotEnvFixed w4 evs := by
    rw [← w4BinaryRecvPrekeyWideSlotEnvAllFixed_eq_fixed hi hcs.eq_files hcs.eq_rd]
    exact henvAll
  dsimp only [mkBinaryKitRealCalleeEnvsFixed]
  rw [hc]
  exact ⟨w4, hc ▸ hdom4, henvFixed⟩

/-- Parametric whole-`run` bridge turning `RunEnv` at `ReadFileRuleEnvFixed cliIo.rd` and
`binaryKitRunSlotEnvsFixed` into `realCliRunBinaryKitEnvOfFixed img S X W g` under
`CliPqxdhInputs ⟨W.C, W.Q⟩ g.i`, discharging R0/R1a/R1b, `W1` (`send`), and `W2` (`recv` whisper)
automatically and taking `hinit3`, `hrecvP_pksm`, and `hrecvP_slot` for `W3`, `PKSM`, and `W4`. -/
theorem runEnvFixed_sub_realCliRunBinaryKitEnvOfFixed_of_slots [LibsignalPlacement]
    {M : AllocCostModel}
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (A : RustCliAllocBudget M) (B : RunBudgets)
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {PksmTryFromEnv : PksmGhost → List AllocEvent → Prop}
    {g : RunCall}
    (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i)
    (hin : (inputOf g.i g.c).length ≤ stdinCapBytes)
    (hinit3 : ∀ peerV dir d2 evs, g.c = .init peerV dir → d2.dir = dir →
      d2.peerV = peerV → d2.peerG.val = addrValOf peerV →
      d2.spkSigPtr ≠ 0 → d2.kpkSigPtr ≠ 0 → d2.kpkPtr ≠ 0 →
      InitEnv (r1cInitGhost g d2 0#64) evs →
      (mkBinaryKitRealCalleeEnvsFixed img S X W g).initEnv evs)
    (hrecvP_pksm : ∀ peerV rest evs, g.c = .recv peerV → g.i.stdin = 3#8 :: rest →
      PksmTryFromEnv (r3bPksmGhost rest) evs →
      (mkBinaryKitRealCalleeEnvsFixed img S X W g).pksmEnv rest evs)
    (hrecvP_slot : ∀ (meV : AddrV) (_meG : AddrGhost) peerV rest pm evs, g.c = .recv peerV →
      g.i.stdin = 3#8 :: rest →
      S.pksmParse rest = some pm →
      DecPkEnv (r3bDecPkGhost g meV peerV pm) evs →
      (mkBinaryKitRealCalleeEnvsFixed img S X W g).decPkEnv evs)
    (hS_enc : S.encrypt = encDef ⟨W.C, W.Q⟩ scopeIn := by rfl) :
    ∀ evs,
      RunEnv
        (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          (binaryKitRunSlotEnvsFixed W A B InitEnv DecPkEnv)
          PksmTryFromEnv S)
        g evs →
      realCliRunBinaryKitEnvOfFixed img S X W g evs :=
  runEnv_to_cliRunBinaryEnv_of_slots
    (fun _ hp =>
      preEnv_sub_r0BinaryEnv (cEnvs := cliRunCalleesEnvs (ReadFileRuleEnv cliIo.rd)) rfl g
        (Eq.mp (congrFun (preEnv_fixed_eq_plain hi) _) hp))
    (fun me peerV dir _ _ h1 =>
      init1Env_sub_r1bFileStepEnv (cEnvs := cliRunCalleesEnvs (ReadFileRuleEnv cliIo.rd))
        rfl g me peerV dir (Eq.mp (congrFun (init1Env_fixed_eq_plain hi me peerV dir) _) h1))
    (fun _ _ d1 _ _ hd1 h2 =>
      hd1 ▸ init2Env_sub_r1bBinaryEnv (cEnvs := cliRunCalleesEnvs (ReadFileRuleEnv cliIo.rd))
        rfl rfl rfl rfl g d1 (Eq.mp (congrFun (init2Env_fixed_eq_plain hi d1) _) h2))
    (fun peerV dir d2 _ hc hd2 hpv hpval hspk hkpkS hkpkP h3 =>
      r1cInit3Env_sub_r1cEnv (hinit3 peerV dir d2 · hc hd2 hpv hpval hspk hkpkS hkpkP) h3)
    (fun _me peerV _ hc hs =>
      r2SendEnv_sub_r2Env
        (fun _ meG evs _hme he =>
          w1_cliEncryptSlotEnv_sub_binaryKit img S X W A B g meG peerV hin hc
            (Eq.mp
              (congrFun
                (cliEncryptSlotEnv_fixed_eq_plain hi A B
                  (x := r2EncGhost g (r2PeerGhost0 peerV) meG 0#64) rfl)
                evs)
              he))
        (fun meV f m heq =>
          w1_send_out_serialized_le_sessionCapBytes X W g peerV meV f m hin hc heq hS_enc)
        (fun meV f m heq =>
          w1_send_outPk_serialized_le_sessionCapBytes X W g peerV meV f m hin hc heq hS_enc) hs)
    (fun _me peerV rest _ hc hst hrw =>
      r3aRecvWEnv_sub_r3aBinaryEnv
        (fun _ meG m evs _hme htr hd =>
          w2_cliDecryptSignalSlotEnv_sub_binaryKit img S X W A B g meG peerV rest m hin hc hst htr
            (Eq.mp
              (congrFun
                (cliDecryptSignalSlotEnv_fixed_eq_plain hi A B
                  (x := r3aDecSigGhost0 g peerV meG m) rfl)
                evs)
              hd)) hrw)
    (fun _me peerV rest _ hc hst hrp =>
      r3bRecvPEnv_sub_r3bEnv
        (hrecvP_pksm peerV rest · hc hst)
        (fun meV meG pm evs _hme hp hd => hrecvP_slot meV meG peerV rest pm evs hc hst hp hd) hrp)

/-- Concrete whole-`run` Fixed bridge under `CliPqxdhInputs ⟨W.C, W.Q⟩ g.i` at
`realCliInitBinarySlotEnvFixed W`, `realCliDecPkBinaryWideSlotEnvFixed X W`, and any
`PksmTryFromEnv` reducing to `PksmCanonSliceEnv x.bytes` on canonical outer `PreKeyMessageFields`. -/
theorem runEnvFixed_sub_realCliRunBinaryKitEnvOfFixed [LibsignalPlacement] {M : AllocCostModel}
    {PksmTryFromEnv : PksmGhost → List AllocEvent → Prop}
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (A : RustCliAllocBudget M) (B : RunBudgets)
    {g : RunCall}
    (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c)
    (hin : (inputOf g.i g.c).length ≤ stdinCapBytes)
    (hpksm_canon : ∀ (x : PksmGhost) (evs : List AllocEvent),
      (∃ m : PreKeyMessageFields, x.bytes = m.bytes) →
      PksmTryFromEnv x evs → PksmCanonSliceEnv x.bytes evs)
    (hS_enc : S.encrypt = encDef ⟨W.C, W.Q⟩ scopeIn := by rfl)
    (hS_pksm : S.pksmParse = pksmParse := by rfl) :
    ∀ evs,
      RunEnv
        (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          (binaryKitRunSlotEnvsFixed W A B (realCliInitBinarySlotEnvFixed W)
            (realCliDecPkBinaryWideSlotEnvFixed X W))
          PksmTryFromEnv
          S)
        g evs →
      realCliRunBinaryKitEnvOfFixed img S X W g evs :=
  runEnvFixed_sub_realCliRunBinaryKitEnvOfFixed_of_slots img S X W A B hi hin
    (fun peerV dir d2 _ hc _ hpv hpval _ _ _ ⟨w, hx, hF, hspqr, hgv, halice, hslotF⟩ =>
      w3_realCliInitBinarySlotEnv_sub_binaryKit img S X W g peerV dir d2 hparse hc hpv hpval
        ⟨w, hx, hF, hspqr, hgv, halice,
          Eq.mp
            (congrFun (w3InitBinaryKitSlotEnvFixed_eq_plain hi (congrArg (·.F) hx)) _)
            hslotF⟩)
    (fun peerV rest _ hc hst hpk =>
      pksmCanonicalGuard_sub_binaryKit img S X W g peerV rest hi hparse hc hst rfl
        (hpksm_canon (r3bPksmGhost rest) _) hpk)
    (fun meV _ peerV rest pm _ hc hst hpk hd =>
      w4_realCliDecPkBinaryWideSlotEnvFixed_sub_binaryKitFixed img S X W g meV peerV rest pm
        hi hparse hin hc hst hpk hd hS_pksm)
    hS_enc

/-- Concrete whole-`run` Fixed bridge specialized to `CanonicalOrFallbackPksmEnv FallbackEnv` under
`CliPqxdhInputs ⟨W.C, W.Q⟩ g.i`. -/
theorem runEnvFixed_sub_realCliRunBinaryKitEnvOfFixed_canonOrFallback [LibsignalPlacement]
    {M : AllocCostModel}
    {FallbackEnv : PksmGhost → List AllocEvent → Prop}
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (A : RustCliAllocBudget M) (B : RunBudgets)
    {g : RunCall}
    (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c)
    (hin : (inputOf g.i g.c).length ≤ stdinCapBytes)
    (hS_enc : S.encrypt = encDef ⟨W.C, W.Q⟩ scopeIn := by rfl)
    (hS_pksm : S.pksmParse = pksmParse := by rfl) :
    ∀ evs,
      RunEnv
        (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          (binaryKitRunSlotEnvsFixed W A B (realCliInitBinarySlotEnvFixed W)
            (realCliDecPkBinaryWideSlotEnvFixed X W))
          (CanonicalOrFallbackPksmEnv FallbackEnv)
          S)
        g evs →
      realCliRunBinaryKitEnvOfFixed img S X W g evs :=
  runEnvFixed_sub_realCliRunBinaryKitEnvOfFixed_of_slots img S X W A B hi hin
    (fun peerV dir d2 _ hc _ hpv hpval _ _ _ ⟨w, hx, hF, hspqr, hgv, halice, hslotF⟩ =>
      w3_realCliInitBinarySlotEnv_sub_binaryKit img S X W g peerV dir d2 hparse hc hpv hpval
        ⟨w, hx, hF, hspqr, hgv, halice,
          Eq.mp
            (congrFun (w3InitBinaryKitSlotEnvFixed_eq_plain hi (congrArg (·.F) hx)) _)
            hslotF⟩)
    (fun peerV rest _ hc hst hpk =>
      pksmCanonicalOrFallback_sub_binaryKit img S X W g peerV rest hi hparse hc hst rfl hpk)
    (fun meV _ peerV rest pm _ hc hst hpk hd =>
      w4_realCliDecPkBinaryWideSlotEnvFixed_sub_binaryKitFixed img S X W g meV peerV rest pm
        hi hparse hin hc hst hpk hd hS_pksm)
    hS_enc

/-- Whole-`run` Fixed bridge at `PksmTryFromEnv := fun x => PksmCanonSliceEnv x.bytes` under
`CliPqxdhInputs ⟨W.C, W.Q⟩ g.i`. -/
theorem runEnvFixed_sub_realCliRunBinaryKitEnvOfFixed_canonSlice [LibsignalPlacement]
    {M : AllocCostModel}
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (A : RustCliAllocBudget M) (B : RunBudgets)
    {g : RunCall}
    (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c)
    (hin : (inputOf g.i g.c).length ≤ stdinCapBytes)
    (hS_enc : S.encrypt = encDef ⟨W.C, W.Q⟩ scopeIn := by rfl)
    (hS_pksm : S.pksmParse = pksmParse := by rfl) :
    ∀ evs,
      RunEnv
        (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          (binaryKitRunSlotEnvsFixed W A B (realCliInitBinarySlotEnvFixed W)
            (realCliDecPkBinaryWideSlotEnvFixed X W))
          (fun x => PksmCanonSliceEnv x.bytes)
          S)
        g evs →
      realCliRunBinaryKitEnvOfFixed img S X W g evs :=
  runEnvFixed_sub_realCliRunBinaryKitEnvOfFixed_of_slots img S X W A B hi hin
    (fun peerV dir d2 _ hc _ hpv hpval _ _ _ ⟨w, hx, hF, hspqr, hgv, halice, hslotF⟩ =>
      w3_realCliInitBinarySlotEnv_sub_binaryKit img S X W g peerV dir d2 hparse hc hpv hpval
        ⟨w, hx, hF, hspqr, hgv, halice,
          Eq.mp
            (congrFun (w3InitBinaryKitSlotEnvFixed_eq_plain hi (congrArg (·.F) hx)) _)
            hslotF⟩)
    (fun _ rest _ _ _ hpk => pksmCanonSlice_sub_binaryKit img S X W g rest hpk)
    (fun meV _ peerV rest pm _ hc hst hpk hd =>
      w4_realCliDecPkBinaryWideSlotEnvFixed_sub_binaryKitFixed img S X W g meV peerV rest pm
        hi hparse hin hc hst hpk hd hS_pksm)
    hS_enc

end LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
