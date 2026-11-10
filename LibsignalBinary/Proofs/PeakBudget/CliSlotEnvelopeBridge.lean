/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Process.Semantics
public import LibsignalBinary.Heap.Fine.ClientBounds
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
public import LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith
public import LibsignalBinary.Proofs.PeakBudget.CliGroupBounds
public import LibsignalBinary.Proofs.PeakBudget.CliMainIoCredit
public import LibsignalBinary.Proofs.PeakBudget.CliMainPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.CliRealExistentialCalleeEnvs
public import LibsignalBinary.Proofs.PeakBudget.CliRunArmsPeak
public import LibsignalBinary.Proofs.PeakBudget.CliRunPeakHelpers
public import LibsignalBinary.Proofs.PeakBudget.CliRunPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.CliTopBudgetReal
public import LibsignalBinary.Proofs.PeakBudget.CliTopBudgetSpec
public import LibsignalBinary.Proofs.PeakBudget.DirPeakHelpers
public import LibsignalBinary.Proofs.PeakBudget.DirPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.GroupCreditKit
public import LibsignalBinary.Proofs.PeakBudget.RealMainEnvAdapter
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
public import LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
public import LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux
public import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot1MiB
public import LibsignalBinary.Proofs.PeakBudget.WireMsgPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.WirePksmTightCredit
public import LibsignalBinary.Proofs.PeakBudget.WireTryFromHelpers
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.CalleesBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Pub.BundleRead.PlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Pub.SplitId.PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Pub.SplitSigned.PlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R0ProofPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.DeserClonePlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadOpkSpinePlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1bProofPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cProofPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cStepsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2ProofPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bProofPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunRel
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Concat2Budget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.KemDeserialize.SpecBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeserAux
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliBinaryPqProofDefs
public import LibsignalBinary.Specifications.LibsignalE2E.SchemeModel
public import LibsignalBinary.Specifications.SignalSession.PqDir
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Plumbing

/-!
# Binary-Exact `RunEnv` to `CliRunBinaryEnv` and `RealCliMainBinaryEnvOf` Bridge

Defines the binary-exact whole-`run` and whole-`main` allocator event envelopes `CliRunBinaryEnv`
and `RealCliMainBinaryEnvOf`, proves `< 90%` (`965,750,441 ≤ 966,367,641` B), `≤ 1 GiB`, and
`cliBudgetLimits` `FitsTrace` / `FitsEnv` bounds on `fineCostModel` under `CliPqxdhInputs` with an
allocating `recv-prekey` (`3#8`) non-vacuity witness, and bridges `RunOkPlacedBudget.RunEnv` into
`CliRunBinaryEnv`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge

open Arm64.Process (bytesOfString)
open CryptoGames.LibsignalSession (PublicKey SignalMessage)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.E2E (PEParams)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost uuidTryParse)
open CryptoVerification.SignalSession
  (CliPqxdhInputs Cmd Inputs bundleDir partyAddress)
open CryptoVerification.SignalSession.Cli (ReadRule StoresGhost pathOf splitId splitSigned utf8)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddrV CallV RunCall cliIo coinsOf parseArgs)
open CryptoVerification.SignalSession.Cli.RunCompose
  (Init1Data Init2Data MeAtDispatch PksmGhost RunSem addrValOf runFiles)
open CryptoVerification.SignalSession.Cli.RunProofs (kemPkDeserialize kemPkLen)
open CryptoVerification.SpqrV1.Alloc (reserveCapStride)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FitsTrace FreeOnlyEvs SeqEnv
   fitsEvents_append rustAllocEvents rustReallocEvents)
open LibsignalBinary.Heap.Fine (FineScale fineCostModel)
open LibsignalBinary.Heap.Fine.ClientBounds (fineCostModel_smallMaxReq_eq)
open LibsignalBinary.Heap.SpecBudget (allocBytes1Events)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
  (DirDomainCaps argv_length_le_of_cliPqInputs dirDomainCaps_opened_own)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith
  (cliBudgetLimits cliDecoupledRamNeed cliDecoupledRamNeed_mono cliDecoupledVaNeed
   cliDecoupledVaNeed_mono cliDefaultStaticBytes cliDefaultStaticCount cliMaxAddrTextBytes
   cliMaxDirPathBytes cliMaxDirtyEntries cliOneGiB
   fitsEnv_fineCostModel_of_group_literal_bounds fitsTrace_fineCostModel_of_group_literal_bounds)
open LibsignalBinary.Proofs.PeakBudget.CliGroupBounds
  (cliIoReadFileEnv_nonFreeBound cliIoReadStdinEnv_nonFreeBound cliMainSetupFineGrpS
   fine_rustAlloc_le_44 m1PhaseEnv_le_3_fine_groupSpec m2CollectEnv_groupSpec
   m2CollectStepEnv_groupSpec m5PhaseEnv_groupSpec m6Env_groupSpec phaseGroupSpec_append_eq
   readFileRuleEnv_groupSpec)
open LibsignalBinary.Proofs.PeakBudget.CliMainIoCredit
  (phaseCreditSpec_cliIoReadFile_anyR_tight phaseCreditSpec_cliIoReadStdin_anyR_tight
   phaseCredit_allocBytes1_tight phaseCredit_m1Phase_small64 phaseCredit_m2Collect_small64
   phaseCredit_rustRealloc_small_any)
open LibsignalBinary.Proofs.PeakBudget.CliMainPeakSpec
  (M2CollectStepEnv M5DirStepEnv M5PhaseEnv M6Env cliMainDeltaCum_tight cliMainDeltaLive_tight
   cliMainDeltaPeak_tight cliMainMaxReq m3PhaseDeltaCum_tight m3PhaseDeltaLive m3PhaseDeltaPeak
   m3PhaseMaxReq m5DirStepDeltaPeak m5DirStepMaxReq m5DirStep_phaseCredit m6DeltaCum
   m6_phaseCredit_small1024 readFileDeltaCum_tight readStdinDeltaCum_tight readStdinDeltaLive
   readStdinDeltaPeak readStdinMaxReq)
open LibsignalBinary.Proofs.PeakBudget.CliRealExistentialCalleeEnvs
  (existentialRealCalleeFineSpecs existentialRealCalleeFineSpecs_direct_run_bounds
   mkExistentialRealCalleeEnvs)
open LibsignalBinary.Proofs.PeakBudget.CliRunArmsPeak
  (CliRunCalleeEnvs CliRunOpenedEnv InitArmEnv JoinEnv R0OpenedEnv R1cEnv R2ConcatTailEnv R2Env
   R3bEnv RecvArmEnv RecvBadEnv RunArmEnv SigTryFromSliceEnv SplitIdEnv SplitSignedEnv
   addressTryParseDeltaCum addressTryParseDeltaLive addressTryParseDeltaPeak addressTryParseMaxReq
   addressTryParse_phaseCredit cliRunOfR0Env_append_freeOnly fineCostModel_cliRunTightHyps
   freeOnlyEvs_append initArmDeltaCum initArmDeltaLive initArmDeltaPeak initArmMaxReq
   r1aMaxReq r1bMaxReq r2DeltaLive r2DeltaPeak r2MaxReq r2TailTightCum r2TightDeltaCum
   r2_tight_phaseCredit
   r3b_phaseCredit recvBad_phaseCredit runArmDeltaLive_le_peak runArmEnv_nil
   sigSliceCum sigSliceLive sigSliceMaxReq sigSlicePeak
   splitIdDeltaCum splitIdMaxReq splitId_small_phaseCredit
   splitSignedDeltaCum splitSignedMaxReq splitSigned_small_phaseCredit tempFilePostMaxReq
   utf8_address_length_le utf8_bundleNames_length_le_16)
open LibsignalBinary.Proofs.PeakBudget.CliRunPeakHelpers
  (phaseCredit_or_freeOnly_left phaseCredit_seq_freeOnly_left phaseCredit_seq_freeOnly_right)
open LibsignalBinary.Proofs.PeakBudget.CliRunPeakSpec
  (r0Opened1MiBCum r0Opened1MiBLive r0Opened1MiBMaxReq r0Opened1MiBPeak)
open LibsignalBinary.Proofs.PeakBudget.CliTopBudgetReal
  (CliRealCalleeFineSpecs cliRealNinetyPctOneGiB
   cliRun1MiBCustomPksmCum cliRun1MiBCustomPksmLive cliRun1MiBCustomPksmMaxReq
   cliRun1MiBCustomPksmPeak cliRunOpenedCustomPksmGrpS
   r3bEnv_of_pksm_fine_groupSpec w3InitRealGrpS)
open LibsignalBinary.Proofs.PeakBudget.CliTopBudgetSpec
  (cliMainTightCumOf cliMainTightGrpCountOf cliMainTightGrpSOf cliMainTightLiveOf
   cliMainTightPeakOf cliMainTightRamNeedOf cliMainTightReqOf cliMainTightStepReserveOf
   cliMainTightVaNeedOf cliRunOfR0_fine_groupSpec initArmEnv_fine_groupSpec
   r0OpenedEnv_fine_groupSpec r2Env_fine_groupSpec)
open LibsignalBinary.Proofs.PeakBudget.DirPeakHelpers (cliIoCapEvents cliIoReadCaps)
open LibsignalBinary.Proofs.PeakBudget.DirPeakSpec
  (pathDeltaCum pathDeltaLive pathDeltaPeak pathMaxReq)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit (NonFreeBound PhaseGroupSpec)
open LibsignalBinary.Proofs.PeakBudget.RealMainEnvAdapter
  (AddrOptBoundedEnv BoundedReadFileEnv BoundedReadStdinEnv BundleOptBoundedEnv
   CliMainBoundedSetupEnv CliPqRunDomain M2CollectFullEnv M3BoundedSetupEnv RealCliMainEnvOf
   ValidPostSetupWitness cliIo_rd_initBundle_caps_of_cliPqInputs
   cliIo_rd_ownAddress_le_40_of_cliPqInputs cliMainWidenedCumOf cliMainWidenedGrpCountOf
   cliMainWidenedGrpSOf cliMainWidenedSetupFineGrpS cliMainWidenedStepReserveOf
   realCliMainEnvOf_concrete_recvPrekey_nonvacuous)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (IterSeqEnv PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas (fineCostModel_modelHyps)
open LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
  (fineReadFileCum fineReadFileLive fineReadFileMaxReq fineReadFilePeak
   readFile_rule_fine_phaseCredit_tight)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (msgCapBytes sessionCapBytes)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot1MiB
  (cliRealDirectRunCum_i cliRealDirectRunGrpS_i cliRealDirectRunLive_i
   cliRealDirectRunMaxReq_i cliRealDirectRunPeak_i)
open LibsignalBinary.Proofs.PeakBudget.WireMsgPeakSpec
  (fineCostModel_wireLowInterceptHyps sigTryFromCapDeltaGrpS
   sigTryFromDeltaCum_le_cap sigTryFromDeltaGrpS_le_cap sigTryFromDeltaLive_le_cap
   sigTryFromDeltaPeak_le_cap sigTryFromMaxReq_le_cap)
open LibsignalBinary.Proofs.PeakBudget.WirePksmTightCredit
  (PksmCanonSliceEnv SigTryFromCanonInnerEnv cliPqInputs_recv_prekey_canonical
   pksmCanonSliceCum pksmCanonSliceGrpS sigTryFromCanonInner_phaseCredit
   sigTryFromCanonInner_phaseGroup sigTryFromConcreteEnv_sub_canonInner)
open LibsignalBinary.Proofs.PeakBudget.WireTryFromHelpers (fineCostModel_wireGroupHyps)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a (DirGetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget (PathEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.CalleesBudget (addressEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Pub.BundleRead.PlacedBudgetAux
  (BundleReadAfterReadEnv BundleReadTailEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Pub.SplitSigned.PlacedBudgetAux
  (SplitSignedTailEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R0ProofPlacedBudget
  (PreAfterGetEnv PreEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudget
  (Init1AfterReadEnv Init1Env)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.DeserClonePlacedBudget
  (R1bDeserCloneErrEnv R1bDeserCloneOkEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadOpkSpinePlacedBudget
  (R1bStepOpkErrEnv R1bStepOpkOkEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1bProofPlacedBudget
  (Init2AfterRegOkEnv Init2Env Init2Stage2Env Init2Stage3Env Init2Stage4Env R1bStepKpkErrEnv
   R1bStepKpkOkEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cProofPlacedBudget
  (R1cInit3Env r1cInitGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cStepsPlacedBudget
  (r1cOkTailEvs_freeOnly)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2ProofPlacedBudget
  (R2SendEnv R2TailEnv r2EncGhost r2PeerGhost0)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudget
  (R3aRecvWEnv r3aDecSigGhost0)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bProofPlacedBudget
  (R3bRecvPEnv r3bDecPkGhost r3bPksmGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudget
  (RunArmAtMeEnv RunArmEnvs RunCoreEnv RunDispatchEnv RunEnv RunInit2ChainEnv RunInit3Env)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget (RunSlotEnvs)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Concat2Budget (cliConcat2Events)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.KemDeserialize.SpecBudget
  (kemDeserializeEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunCalleesEnvs)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (ReadFileRuleEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeserAux
  (dirGetEnv_path_readFile_fine_phaseCredit_tight dirGetEnv_path_readFile_groupSpec
   pathEnv_fine_phaseCredit_tight)

private abbrev seqEnv_mono := @LibsignalBinary.Proofs.PeakBudget.SeqCreditKit.SeqEnv.mono

/-! ## 1. Binary-Exact `run` Arm and Whole-`main` Envelopes -/

/-- Optional stage wrapper (`FreeOnlyEvs ∪ P`), containing `[]`, `FreeOnlyEvs`, and `P`. -/
def OptStageEnv (P : List AllocEvent → Prop) (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨ P evs

/-- Prefix-closed binary single-file read step (`PathEnv`, `ReadFileRuleEnv`, optional `FreeOnlyEvs`,
and optional `14`/`22`-byte error string allocation + `FreeOnlyEvs`). -/
def R1bFileStepEnv (rd : ReadRule) (files : FsFiles) (dir name : List (BitVec 8))
    (evs : List AllocEvent) : Prop :=
  SeqEnv (OptStageEnv (PathEnv dir name))
    (SeqEnv (OptStageEnv (ReadFileRuleEnv rd files (dir ++ [0x2f#8] ++ name)))
      (SeqEnv FreeOnlyEvs
        (OptStageEnv
          (SeqEnv (fun e => e = rustAllocEvents 22 1 ∨ e = rustAllocEvents 14 1) FreeOnlyEvs))))
    evs

/-- Prefix-closed Stage-4 (`spkSig` 64-byte clone, `kemDeserializeEvents`, `kpkSig` 64-byte clone,
and cleanup frees) envelope of Arm `R1b`. -/
def R1bDeserStageEnv (evs : List AllocEvent) : Prop :=
  SeqEnv (OptStageEnv (· = rustAllocEvents 64 1))
    (SeqEnv (OptStageEnv (· = rustAllocEvents kemPkLen 1))
      (OptStageEnv (SeqEnv (· = rustAllocEvents 64 1) FreeOnlyEvs))) evs

/-- Prefix-closed binary Arm `R1b` (`Init2Env`) envelope over `registration-id`, `signed-pre-key`,
`kyber-pre-key`, `one-time-pre-key`, and Stage-4 key deserialization/cloning. -/
def R1bBinaryEnv (rd : ReadRule) (files : FsFiles) (dir : List (BitVec 8))
    (evs : List AllocEvent) : Prop :=
  SeqEnv (R1bFileStepEnv rd files dir (utf8 "registration-id"))
    (SeqEnv (OptStageEnv (R1bFileStepEnv rd files dir (utf8 "signed-pre-key")))
      (SeqEnv (OptStageEnv (SplitSignedEnv []))
        (SeqEnv (OptStageEnv (R1bFileStepEnv rd files dir (utf8 "kyber-pre-key")))
          (SeqEnv (OptStageEnv (SplitSignedEnv []))
            (SeqEnv (OptStageEnv (R1bFileStepEnv rd files dir (utf8 "one-time-pre-key")))
              (SeqEnv (OptStageEnv (SplitIdEnv []))
                (OptStageEnv R1bDeserStageEnv))))))) evs

/-- Prefix-closed binary `.init` arm (`R1a → R1b → R1c`) core envelope. -/
def InitArmBinaryCoreEnv (rd : ReadRule) (files : FsFiles) (dir : List (BitVec 8))
    (InitEnv : List AllocEvent → Prop) (evs : List AllocEvent) : Prop :=
  SeqEnv (R1bFileStepEnv rd files dir (utf8 "identity-key"))
    (SeqEnv (OptStageEnv (R1bBinaryEnv rd files dir))
      (OptStageEnv (R1cEnv InitEnv))) evs

/-- Combined `.init` arm envelope covering both `InitArmEnv` and `InitArmBinaryCoreEnv`. -/
def InitArmBinaryEnv (rd : ReadRule) (files : FsFiles) (dir : List (BitVec 8))
    (InitEnv : List AllocEvent → Prop) (evs : List AllocEvent) : Prop :=
  InitArmEnv rd files dir InitEnv evs ∨ InitArmBinaryCoreEnv rd files dir InitEnv evs

/-- Binary Arm `R3a` (`2#8` Whisper `recv`) envelope using `SigTryFromCanonInnerEnv`
(which contains both `SigTryFromSliceEnv` and Block `85`'s `TryFromEnv`). -/
def R3aBinaryEnv (rest : List (BitVec 8)) (DecSigEnv : List AllocEvent → Prop)
    (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨ SeqEnv (SigTryFromCanonInnerEnv rest)
    (fun evs2 => FreeOnlyEvs evs2 ∨ SeqEnv DecSigEnv FreeOnlyEvs evs2) evs

/-- Binary `.recv` arm dispatch envelope. -/
def RecvArmBinaryEnv (stdin : List (BitVec 8)) (DecSigEnv : List AllocEvent → Prop)
    (PksmEnv : List (BitVec 8) → List AllocEvent → Prop)
    (DecPkEnv : List AllocEvent → Prop) (evs : List AllocEvent) : Prop :=
  match stdin with
  | b :: rest =>
    if b = 2#8 then R3aBinaryEnv rest DecSigEnv evs
    else if b = 3#8 then R3bEnv (PksmEnv rest) DecPkEnv evs
    else RecvBadEnv evs
  | [] => RecvBadEnv evs

/-- Binary post-`R0` arm dispatch envelope. -/
def RunArmBinaryEnv (rd : ReadRule) (files : FsFiles) (E : CliRunCalleeEnvs)
    (wireOutCap : Nat) (stdin : List (BitVec 8)) (c : CallV) (evs : List AllocEvent) : Prop :=
  match c with
  | .keygen _ _ => FreeOnlyEvs evs
  | .init _ dir => InitArmBinaryEnv rd files dir E.initEnv evs
  | .send _ => R2Env E.encEnv wireOutCap evs
  | .recv _ => RecvArmBinaryEnv stdin E.decSigEnv E.pksmEnv E.decPkEnv evs

/-- Binary Arm `R0` (`PreEnv`) envelope covering both `R0OpenedEnv` and
`DirGetEnv PathEnv (ReadFileRuleEnv rd) rd` + `PreAfterGetEnv`. -/
def R0BinaryEnv (rd : ReadRule) (g : RunCall) (evs : List AllocEvent) : Prop :=
  R0OpenedEnv rd (runFiles g.i) evs ∨
  SeqEnv (DirGetEnv PathEnv (ReadFileRuleEnv rd) rd (runFiles g.i)
      StoresGhost.opened.identity.own (utf8 "address"))
    (PreAfterGetEnv g) evs

/-- Whole-`signal_session::run` binary-exact allocator event envelope (`R0 → Arm → Join`). -/
def CliRunBinaryEnv (rd : ReadRule) (E : CliRunCalleeEnvs) (wireOutCap : Nat) (g : RunCall)
    (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨
  SeqEnv (R0BinaryEnv rd g)
    (SeqEnv (RunArmBinaryEnv rd (runFiles g.i) E wireOutCap g.i.stdin g.c) JoinEnv) evs

/-- Whole-`main` binary-exact allocator trace predicate on `i : Inputs` over callee slot family `E`. -/
def RealCliMainBinaryEnvOf (E : RunCall → CliRunCalleeEnvs) (i : Inputs)
    (evs : List AllocEvent) : Prop :=
  SeqEnv (CliMainBoundedSetupEnv i.argv.length) (fun evs' =>
    FreeOnlyEvs evs' ∨ ∃ w : ValidPostSetupWitness i, w.g.i = i ∧
      SeqEnv (CliRunBinaryEnv cliIo.rd (E w.g) sessionCapBytes w.g)
        (SeqEnv (M5PhaseEnv w.dirs) (M6Env w.ok)) evs') evs

/-! ## 2. Monotonic Containment (`CliRunOpenedEnv` ⊆ `CliRunBinaryEnv`) & Non-Vacuity -/

theorem runArmEnv_sub_runArmBinaryEnv {rd : ReadRule} {files : FsFiles}
    {E : CliRunCalleeEnvs} {wireOutCap : Nat} {stdin : List (BitVec 8)} {c : CallV}
    {evs : List AllocEvent}
    (h : RunArmEnv rd files E wireOutCap stdin c evs) :
    RunArmBinaryEnv rd files E wireOutCap stdin c evs := by
  cases c with
  | keygen _ _ => exact h
  | init _ _ => exact Or.inl h
  | send _ => exact h
  | recv _ =>
    unfold RunArmEnv RecvArmEnv at h
    unfold RunArmBinaryEnv RecvArmBinaryEnv
    rcases stdin with _ | ⟨b, rest⟩
    · exact h
    · by_cases hb2 : b = 2#8
      · simp only [hb2, ↓reduceIte] at h ⊢
        rcases h with hf | hs
        · exact Or.inl hf
        · exact Or.inr (seqEnv_mono (fun _ h1 => Or.inl h1) (fun _ h2 => h2) hs)
      · simp only [hb2, ↓reduceIte] at h ⊢
        exact h

theorem cliRunOpenedEnv_sub_cliRunBinaryEnv {rd : ReadRule} {E : CliRunCalleeEnvs}
    {wireOutCap : Nat} {g : RunCall} {evs : List AllocEvent}
    (h : CliRunOpenedEnv rd E wireOutCap g evs) :
    CliRunBinaryEnv rd E wireOutCap g evs := by
  rcases h with hf | hs
  · exact Or.inl hf
  · exact Or.inr (seqEnv_mono (fun _ hr0 => Or.inl hr0)
      (fun _ haj => seqEnv_mono (fun _ ha => runArmEnv_sub_runArmBinaryEnv ha) (fun _ hj => hj) haj)
      hs)

theorem realCliMainEnvOf_sub_realCliMainBinaryEnvOf {E : RunCall → CliRunCalleeEnvs}
    {i : Inputs} {evs : List AllocEvent}
    (h : RealCliMainEnvOf E i evs) :
    RealCliMainBinaryEnvOf E i evs :=
  seqEnv_mono (fun _ h1 => h1)
    (fun _ h2 => h2.elim Or.inl fun ⟨w, hgi, hseq⟩ =>
      Or.inr ⟨w, hgi, seqEnv_mono (fun _ hr => cliRunOpenedEnv_sub_cliRunBinaryEnv hr)
        (fun _ hm => hm) hseq⟩)
    h

/-- Allocating `3#8` `recv-prekey` non-vacuity witness on
`RealCliMainBinaryEnvOf (mkExistentialRealCalleeEnvs img S P₀) i₀`
(`AllocEvent.alloc 72 ∈ fullLog` and `AllocEvent.realloc 1 2048 1569 ∈ fullLog`). -/
theorem realCliMainBinaryEnvOf_concrete_recvPrekey_nonvacuous [LibsignalPlacement]
    (img : Arm64.Obj.Image) (S : RunSem) :
    ∃ (P₀ : PEParams) (i₀ : Inputs) (fullLog : List AllocEvent),
      CliPqxdhInputs P₀ i₀ ∧
      RealCliMainBinaryEnvOf (mkExistentialRealCalleeEnvs img S P₀) i₀ fullLog ∧
      AllocEvent.alloc 72 ∈ fullLog ∧ AllocEvent.realloc 1 2048 1569 ∈ fullLog := by
  obtain ⟨P₀, i₀, fullLog, hi, hEnv, ha, hr⟩ :=
    realCliMainEnvOf_concrete_recvPrekey_nonvacuous img S
  exact ⟨P₀, i₀, fullLog, hi, realCliMainEnvOf_sub_realCliMainBinaryEnvOf hEnv, ha, hr⟩

/-! ## 3. `PhaseCreditSpec` & `PhaseGroupSpec` for Binary Stages (`R0`, `R1a`, `R1b`, `R3a`) -/

private theorem optStage_phaseCredit {P : List AllocEvent → Prop} {c l p r : Nat}
    (h : PhaseCreditSpec fineCostModel P c l p r) :
    PhaseCreditSpec fineCostModel (OptStageEnv P) c l p r :=
  phaseCredit_or_freeOnly_left fineCostModel_modelHyps (fun _ hf => hf) h

private theorem optStage_groupSpec {P : List AllocEvent → Prop} {g : Nat}
    (h : PhaseGroupSpec fineCostModel P g) :
    PhaseGroupSpec fineCostModel (OptStageEnv P) g :=
  ((PhaseGroupSpec.freeOnly fineCostModel).or h).mono (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)

private theorem max_self_le (a : Nat) : max a a ≤ a :=
  Nat.max_le.mpr ⟨Nat.le_refl a, Nat.le_refl a⟩

private def kutf8 (s : String) : List (BitVec 8) :=
  (s.toList.flatMap String.utf8EncodeChar).map fun b => BitVec.ofNat 8 b.toNat

private theorem byteArray_toList_eq_data : ∀ (bs : ByteArray), bs.toList = bs.data.toList
  | ⟨⟨xs⟩⟩ => by
    have hloop : ∀ i r, ByteArray.toList.loop ⟨⟨xs⟩⟩ i r = r.reverse ++ xs.drop i := by
      intro i r; fun_induction ByteArray.toList.loop ⟨⟨xs⟩⟩ i r with
      | case1 i r hi ih =>
        have hget : (ByteArray.mk ⟨xs⟩).get! i = xs[i] := getElem!_pos (⟨xs⟩ : Array UInt8) i hi
        rw [ih, hget, List.reverse_cons, List.append_assoc, List.singleton_append,
          List.drop_eq_getElem_cons hi]
      | case2 i r hni => rw [List.drop_eq_nil_of_le (Nat.le_of_not_lt hni), List.append_nil]
    exact hloop 0 []

private theorem utf8_eq_kutf8 (s : String) : utf8 s = kutf8 s := by
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  simp [utf8, kutf8, List.utf8Encode, byteArray_toList_eq_data]

private theorem dirDomainCaps_opened_own_64 :
    DirDomainCaps 64 0 0 StoresGhost.opened.identity.own :=
  dirDomainCaps_opened_own.mono (by decide) (Nat.le_refl 0) (Nat.le_refl 0)

private theorem cliIo_rd_initBundle_nonempty_caps_of_cliPqInputs {W : PEParams} {g : RunCall}
    (hi : CliPqxdhInputs W g.i)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c) :
    ∀ peer dir, g.c = .init peer dir →
      dir ≠ [] ∧ dir.length ≤ 26 ∧
      (∀ name bs, cliIo.rd (runFiles g.i) (dir ++ [0x2f#8] ++ name) = .ok bs →
        bs.length ≤ 1637) := by
  intro peer dir hcmd
  have hcaps := cliIo_rd_initBundle_caps_of_cliPqInputs hi hparse peer dir hcmd
  have hne : dir ≠ [] := by
    rcases hi with ⟨st, _, hcase⟩
    have hrecv (harg : g.i.argv = (Cmd.recv (partyAddress st.party.other)).argv) : False := by
      rw [harg, CryptoVerification.SignalSession.Cli.RunRefine.parseArgs_recv, hcmd] at hparse
      cases hparse
    rcases hcase with ⟨_, b, t, hi_eq⟩ | ⟨_, _, _, hi_eq⟩ | ⟨_, _, _, hi_eq⟩ |
        ⟨_, _, _, hi_eq⟩ | ⟨_, _, _, _, _, hi_eq⟩
    · have harg : g.i.argv = (Cmd.init (partyAddress st.party.other) bundleDir).argv := by
        rw [hi_eq]; rfl
      rw [harg, CryptoVerification.SignalSession.Cli.RunRefine.parseArgs_init, hcmd] at hparse
      injection hparse with hcmd_eq
      injection hcmd_eq with _ hdir_eq
      subst hdir_eq
      decide
    · have harg : g.i.argv = (Cmd.send (partyAddress st.party.other)).argv := by rw [hi_eq]; rfl
      rw [harg, CryptoVerification.SignalSession.Cli.RunRefine.parseArgs_send, hcmd] at hparse
      cases hparse
    · exact False.elim (hrecv (by rw [hi_eq]; rfl))
    · exact False.elim (hrecv (by rw [hi_eq]; rfl))
    · exact False.elim (hrecv (by rw [hi_eq]; rfl))
  refine ⟨hne, hcaps.1, fun name bs hrd => ?_⟩
  have hp : dir ++ [0x2f#8] ++ name = pathOf dir name := by
    have hslash : utf8 "/" = [0x2f#8] := by rw [utf8_eq_kutf8]; rfl
    simp [pathOf, hne, hslash]
  exact hcaps.2 name bs (hp ▸ hrd)

private theorem pathEnv_groupSpec (dir name : List (BitVec 8)) :
    PhaseGroupSpec fineCostModel (PathEnv dir name) (9 * FineScale) := by
  unfold PathEnv LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget.pathEvents
  have h1 : PhaseGroupSpec fineCostModel
      (· = LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget.pathToOwnedEvents dir.length)
      (3 * FineScale) := by
    unfold LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget.pathToOwnedEvents
    split
    · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
    · exact PhaseGroupSpec.rustAlloc_any fineCostModel dir.length 1
  have h2 : PhaseGroupSpec fineCostModel
      (· = LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget.pathPushSlashEvents dir.length)
      (3 * FineScale) := by
    unfold LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget.pathPushSlashEvents
    split
    · exact PhaseGroupSpec.rustAlloc_any fineCostModel _ 1
    · exact PhaseGroupSpec.rustRealloc_any fineCostModel _ _ 1
  have h3 : PhaseGroupSpec fineCostModel
      (· = LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget.pathAppendNameEvents
        dir.length name.length)
      (3 * FineScale) := by
    unfold LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget.pathAppendNameEvents
    dsimp only
    split
    · exact PhaseGroupSpec.rustRealloc_any fineCostModel _ _ 1
    · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
  exact (phaseGroupSpec_append_eq fineCostModel h1
    (phaseGroupSpec_append_eq fineCostModel h2 h3)).mono (by generalize FineScale = fs; omega)

private theorem r0BinaryEnv_fine_phaseCredit {W : PEParams} {g : RunCall}
    (hi : CliPqxdhInputs W g.i) :
    PhaseCreditSpec fineCostModel (R0BinaryEnv cliIo.rd g)
      r0Opened1MiBCum r0Opened1MiBLive r0Opened1MiBPeak r0Opened1MiBMaxReq := by
  have hcap40 : ∀ bs,
      cliIo.rd (runFiles g.i) (pathOf StoresGhost.opened.identity.own.path (utf8 "address")) =
        .ok bs → bs.length ≤ 40 :=
    fun _ hrd => cliIo_rd_ownAddress_le_40_of_cliPqInputs hi hrd
  have hcapSess : ∀ bs,
      cliIo.rd (runFiles g.i) (pathOf StoresGhost.opened.identity.own.path (utf8 "address")) =
        .ok bs → bs.length ≤ sessionCapBytes :=
    fun bs hrd => Nat.le_trans (hcap40 bs hrd) (by unfold sessionCapBytes; decide)
  have hop : PhaseCreditSpec fineCostModel (R0OpenedEnv cliIo.rd (runFiles g.i))
      r0Opened1MiBCum r0Opened1MiBLive r0Opened1MiBPeak r0Opened1MiBMaxReq :=
    CliRunArmsPeak.r0Opened_phaseCredit_of_path fineCostModel_modelHyps
      (DirPeakSpec.path_phaseCredit fineCostModel_modelHyps (by decide : StoresGhost.opened.identity.own.path.length ≤ 26)
        utf8_address_length_le) hcapSess
  have hdg := dirGetEnv_path_readFile_fine_phaseCredit_tight cliIo.rd (runFiles g.i)
    StoresGhost.opened.identity.own (utf8 "address") dirDomainCaps_opened_own_64
    (Nat.le_trans utf8_address_length_le (by decide)) hcap40
  have hafter : PhaseCreditSpec fineCostModel (PreAfterGetEnv g)
      addressTryParseDeltaCum addressTryParseDeltaLive
      addressTryParseDeltaPeak addressTryParseMaxReq := by
    unfold PreAfterGetEnv
    cases StoresGhost.opened.identity.own.get cliIo.rd (runFiles g.i) (utf8 "address") with
    | error _ =>
      exact (PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    | ok ownB =>
      exact phaseCredit_seq_freeOnly_right fineCostModel_modelHyps
        (addressTryParse_phaseCredit fineCostModel_modelHyps ownB) (fun _ hf => hf) (Nat.le_refl _)
  have hbin : PhaseCreditSpec fineCostModel
      (SeqEnv (DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd (runFiles g.i)
          StoresGhost.opened.identity.own (utf8 "address"))
        (PreAfterGetEnv g))
      r0Opened1MiBCum r0Opened1MiBLive r0Opened1MiBPeak r0Opened1MiBMaxReq :=
    (hdg.seq hafter).mono (by decide) (by decide) (by decide) (by decide)
  exact (hop.or hbin).mono
    (max_self_le _) (max_self_le _) (max_self_le _) (max_self_le _)

private theorem r0BinaryEnv_fine_groupSpec (rd : ReadRule) (g : RunCall) :
    PhaseGroupSpec fineCostModel (R0BinaryEnv rd g) (42 * FineScale) := by
  have hop : PhaseGroupSpec fineCostModel (R0OpenedEnv rd (runFiles g.i)) (42 * FineScale) :=
    (r0OpenedEnv_fine_groupSpec rd (runFiles g.i)).mono (by unfold FineScale; decide)
  have hdg := dirGetEnv_path_readFile_groupSpec fineCostModel rd (runFiles g.i)
    StoresGhost.opened.identity.own (utf8 "address")
  have hafter : PhaseGroupSpec fineCostModel (PreAfterGetEnv g) (3 * FineScale) := by
    unfold PreAfterGetEnv
    cases StoresGhost.opened.identity.own.get cliIo.rd (runFiles g.i) (utf8 "address") with
    | error _ => exact (PhaseGroupSpec.freeOnly fineCostModel).mono (Nat.zero_le _)
    | ok ownB =>
      have haddr : PhaseGroupSpec fineCostModel (· = addressEvents uuidTryParse ownB)
          (3 * FineScale) := by
        unfold addressEvents
        cases CryptoVerification.SignalSession.Cli.MainHops.addrParse uuidTryParse ownB with
        | none => exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
        | some a => exact PhaseGroupSpec.rustAlloc_any fineCostModel a.name.length 1
      exact (haddr.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono (by generalize FineScale = fs; omega)
  have hbin : PhaseGroupSpec fineCostModel
      (SeqEnv (DirGetEnv PathEnv (ReadFileRuleEnv rd) rd (runFiles g.i)
          StoresGhost.opened.identity.own (utf8 "address"))
        (PreAfterGetEnv g))
      (42 * FineScale) :=
    (hdg.seq hafter).mono (by generalize FineScale = fs; omega)
  exact (hop.or hbin).mono (max_self_le _)

def r1bFileStepCum : Nat := 21185 + fineReadFileCum 1637 + (2 * 22 + 9539)

private theorem r1bFileStepEnv_fine_phaseCredit {rd : ReadRule} {files : FsFiles}
    {dir name : List (BitVec 8)} (hdir : dir.length ≤ 26) (hname : name.length ≤ 16)
    (hcap : ∀ bs, rd files (dir ++ [0x2f#8] ++ name) = .ok bs → bs.length ≤ 1637) :
    PhaseCreditSpec fineCostModel (R1bFileStepEnv rd files dir name)
      r1bFileStepCum 0 0 (fineReadFileMaxReq 1637) := by
  have hp := optStage_phaseCredit
    (pathEnv_fine_phaseCredit_tight (Nat.le_trans hdir (by decide)) (Nat.le_trans hname (by decide)))
  have hr := optStage_phaseCredit
    (readFile_rule_fine_phaseCredit_tight rd files (dir ++ [0x2f#8] ++ name) hcap)
  have hsm22 : 22 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have hsm14 : 14 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have ha22 : PhaseCreditSpec fineCostModel (· = rustAllocEvents 22 1) (2 * 22 + 9539) 0 0 22 :=
    (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps
      (req := 22) (al := 1) (by decide) hsm22).mono
      (fineCostModel_modelHyps.smallAlloc_le hsm22) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 22)
  have ha14 : PhaseCreditSpec fineCostModel (· = rustAllocEvents 14 1) (2 * 22 + 9539) 0 0 22 :=
    (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps
      (req := 14) (al := 1) (by decide) hsm14).mono
      (Nat.le_trans (fineCostModel_modelHyps.smallAlloc_le hsm14) (by decide))
      (Nat.le_refl 0) (Nat.le_refl 0) (by decide : 14 ≤ 22)
  have herr : PhaseCreditSpec fineCostModel
      (fun e => e = rustAllocEvents 22 1 ∨ e = rustAllocEvents 14 1) (2 * 22 + 9539) 0 0 22 :=
    (ha22.or ha14).mono (max_self_le _) (max_self_le _) (max_self_le _) (max_self_le _)
  have htail := phaseCredit_seq_freeOnly_left fineCostModel_modelHyps (fun _ hf => hf)
    (optStage_phaseCredit
      (phaseCredit_seq_freeOnly_right fineCostModel_modelHyps herr (fun _ hf => hf) (Nat.le_refl 0)))
  exact (hp.seq (hr.seq htail)).mono
    (by unfold r1bFileStepCum; omega)
    (by decide)
    (by decide)
    (by decide)

private theorem r1bFileStepEnv_fine_groupSpec (rd : ReadRule) (files : FsFiles)
    (dir name : List (BitVec 8)) :
    PhaseGroupSpec fineCostModel (R1bFileStepEnv rd files dir name) (42 * FineScale) := by
  have hp := optStage_groupSpec (pathEnv_groupSpec dir name)
  have hr := optStage_groupSpec (readFileRuleEnv_groupSpec fineCostModel rd files (dir ++ [0x2f#8] ++ name))
  have herr : PhaseGroupSpec fineCostModel
      (fun e => e = rustAllocEvents 22 1 ∨ e = rustAllocEvents 14 1) (3 * FineScale) :=
    ((PhaseGroupSpec.rustAlloc_any fineCostModel 22 1).or
      (PhaseGroupSpec.rustAlloc_any fineCostModel 14 1)).mono (max_self_le _)
  have herrFree : PhaseGroupSpec fineCostModel
      (SeqEnv (fun e => e = rustAllocEvents 22 1 ∨ e = rustAllocEvents 14 1) FreeOnlyEvs)
      (3 * FineScale) :=
    (herr.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono (by generalize FineScale = fs; omega)
  have htail : PhaseGroupSpec fineCostModel
      (SeqEnv FreeOnlyEvs
        (OptStageEnv (SeqEnv (fun e => e = rustAllocEvents 22 1 ∨ e = rustAllocEvents 14 1) FreeOnlyEvs)))
      (3 * FineScale) :=
    ((PhaseGroupSpec.freeOnly fineCostModel).seq (optStage_groupSpec herrFree)).mono
      (by generalize FineScale = fs; omega)
  exact (hp.seq (hr.seq htail)).mono (by generalize FineScale = fs; omega)

def r1bDeserStageCum : Nat := (2 * 64 + 9539) + (2 * kemPkLen + 9539) + (2 * 64 + 9539)

private theorem r1bDeserStageEnv_fine_phaseCredit :
    PhaseCreditSpec fineCostModel R1bDeserStageEnv r1bDeserStageCum 0 0 kemPkLen := by
  have hsm64 : 64 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have hsmKem : kemPkLen ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have ha64 := optStage_phaseCredit
    ((PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps
      (req := 64) (al := 1) (by decide) hsm64).mono
      (fineCostModel_modelHyps.smallAlloc_le hsm64) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 64))
  have haKem := optStage_phaseCredit
    ((PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps
      (req := kemPkLen) (al := 1) (by decide) hsmKem).mono
      (fineCostModel_modelHyps.smallAlloc_le hsmKem) (Nat.le_refl 0) (Nat.le_refl 0)
      (Nat.le_refl kemPkLen))
  have ha64Free := optStage_phaseCredit
    (phaseCredit_seq_freeOnly_right fineCostModel_modelHyps
      ((PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps
        (req := 64) (al := 1) (by decide) hsm64).mono
        (fineCostModel_modelHyps.smallAlloc_le hsm64) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 64))
      (fun _ hf => hf) (Nat.le_refl 0))
  exact (ha64.seq (haKem.seq ha64Free)).mono
    (by unfold r1bDeserStageCum; omega) (by decide) (by decide) (by decide)

private theorem r1bDeserStageEnv_fine_groupSpec :
    PhaseGroupSpec fineCostModel R1bDeserStageEnv (9 * FineScale) := by
  have ha64 := optStage_groupSpec (PhaseGroupSpec.rustAlloc_any fineCostModel 64 1)
  have haKem := optStage_groupSpec (PhaseGroupSpec.rustAlloc_any fineCostModel kemPkLen 1)
  have ha64Seq : PhaseGroupSpec fineCostModel
      (SeqEnv (· = rustAllocEvents 64 1) FreeOnlyEvs) (3 * FineScale) :=
    ((PhaseGroupSpec.rustAlloc_any fineCostModel 64 1).seq
      (PhaseGroupSpec.freeOnly fineCostModel)).mono (by generalize FineScale = fs; omega)
  have ha64Free := optStage_groupSpec ha64Seq
  exact (ha64.seq (haKem.seq ha64Free)).mono (by generalize FineScale = fs; omega)

def initArmBinaryPrefixCum : Nat :=
  5 * r1bFileStepCum + 2 * splitSignedDeltaCum + splitIdDeltaCum + r1bDeserStageCum

private theorem initArmBinaryEnv_fine_phaseCredit {rd : ReadRule} {files : FsFiles}
    {dir : List (BitVec 8)} {InitEnv : List AllocEvent → Prop}
    {initCum initLive initPeak initMaxReq : Nat}
    (hdir : dir.length ≤ 26)
    (hcapPath : ∀ name bs, rd files (pathOf dir name) = .ok bs → bs.length ≤ 1637)
    (hcapSlash : ∀ name bs, rd files (dir ++ [0x2f#8] ++ name) = .ok bs → bs.length ≤ 1637)
    (hinit : PhaseCreditSpec fineCostModel InitEnv initCum initLive initPeak initMaxReq)
    (hlp : initLive ≤ initPeak) :
    PhaseCreditSpec fineCostModel (InitArmBinaryEnv rd files dir InitEnv)
      (max (initArmDeltaCum (pathDeltaCum 26 16) 1637 initCum)
        (initArmBinaryPrefixCum + initCum))
      (initArmDeltaLive (pathDeltaLive 26 16) initLive)
      (initArmDeltaPeak (pathDeltaLive 26 16) (pathDeltaPeak 26 16) 1637 initPeak)
      (max (initArmMaxReq (pathMaxReq 26 16) 1637 initMaxReq)
        (max (fineReadFileMaxReq 1637) initMaxReq)) := by
  obtain ⟨hn1, hn2, hn3, hn4, hn5⟩ := utf8_bundleNames_length_le_16
  have hop := CliRunArmsPeak.initArm_phaseCredit_of_paths fineCostModel_modelHyps
    (DirPeakSpec.path_phaseCredit fineCostModel_modelHyps hdir hn1)
    (DirPeakSpec.path_phaseCredit fineCostModel_modelHyps hdir hn2)
    (DirPeakSpec.path_phaseCredit fineCostModel_modelHyps hdir hn3)
    (DirPeakSpec.path_phaseCredit fineCostModel_modelHyps hdir hn4)
    (DirPeakSpec.path_phaseCredit fineCostModel_modelHyps hdir hn5)
    hcapPath hinit hlp
  have hsm14 : 14 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have hs1 := r1bFileStepEnv_fine_phaseCredit hdir hn1 (hcapSlash _)
  have hs2 := r1bFileStepEnv_fine_phaseCredit hdir hn2 (hcapSlash _)
  have hs3 := optStage_phaseCredit (r1bFileStepEnv_fine_phaseCredit hdir hn3 (hcapSlash _))
  have hs4 := optStage_phaseCredit (r1bFileStepEnv_fine_phaseCredit hdir hn4 (hcapSlash _))
  have hs5 := optStage_phaseCredit (r1bFileStepEnv_fine_phaseCredit hdir hn5 (hcapSlash _))
  have hss := optStage_phaseCredit (splitSigned_small_phaseCredit fineCostModel_modelHyps hsm14 [])
  have hsi := optStage_phaseCredit (splitId_small_phaseCredit fineCostModel_modelHyps hsm14 [])
  have hds := optStage_phaseCredit r1bDeserStageEnv_fine_phaseCredit
  have hr1b : PhaseCreditSpec fineCostModel (R1bBinaryEnv rd files dir)
      (4 * r1bFileStepCum + 2 * splitSignedDeltaCum + splitIdDeltaCum + r1bDeserStageCum)
      0 0 (fineReadFileMaxReq 1637) :=
    (hs2.seq (hs3.seq (hss.seq (hs4.seq (hss.seq (hs5.seq (hsi.seq hds))))))).mono
      (by omega) (by decide) (by decide) (by decide)
  have hr1c : PhaseCreditSpec fineCostModel (OptStageEnv (R1cEnv InitEnv))
      initCum initLive initPeak initMaxReq :=
    optStage_phaseCredit
      (CliRunArmsPeak.r1c_phaseCredit fineCostModel_modelHyps hinit hlp)
  have hcore : PhaseCreditSpec fineCostModel (InitArmBinaryCoreEnv rd files dir InitEnv)
      (initArmBinaryPrefixCum + initCum)
      (initArmDeltaLive (pathDeltaLive 26 16) initLive)
      (initArmDeltaPeak (pathDeltaLive 26 16) (pathDeltaPeak 26 16) 1637 initPeak)
      (max (fineReadFileMaxReq 1637) initMaxReq) := by
    refine (hs1.seq ((optStage_phaseCredit hr1b).seq hr1c)).mono ?_ ?_ ?_ ?_
    · unfold initArmBinaryPrefixCum; omega
    · unfold initArmDeltaLive; omega
    · unfold initArmDeltaPeak
      exact Nat.le_trans (by omega : max 0 (0 + max 0 (0 + initPeak)) ≤ initPeak)
        (Nat.le_trans (Nat.le_add_left initPeak _)
          (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_max_right _ _))))
    · exact Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_refl _⟩
  exact (hop.or hcore).mono (Nat.le_refl _) (max_self_le _) (max_self_le _) (Nat.le_refl _)

private theorem splitId_fine_groupSpec (bs : List (BitVec 8)) :
    PhaseGroupSpec fineCostModel (SplitIdEnv bs) (3 * FineScale) :=
  ((PhaseGroupSpec.rustAlloc_any fineCostModel 14 1).seq
    (PhaseGroupSpec.freeOnly fineCostModel)).mono (by generalize FineScale = fs; omega)

private theorem splitSigned_fine_groupSpec (bs : List (BitVec 8)) :
    PhaseGroupSpec fineCostModel (SplitSignedEnv bs) (6 * FineScale) := by
  have h1 := splitId_fine_groupSpec bs
  exact (h1.seq (optStage_groupSpec h1)).mono (by generalize FineScale = fs; omega)

private theorem initArmBinaryEnv_fine_groupSpec (rd : ReadRule) (files : FsFiles)
    (dir : List (BitVec 8)) {InitEnv : List AllocEvent → Prop} {g_init : Nat}
    (hinit : PhaseGroupSpec fineCostModel InitEnv g_init) :
    PhaseGroupSpec fineCostModel (InitArmBinaryEnv rd files dir InitEnv)
      (234 * FineScale + g_init) := by
  have hop : PhaseGroupSpec fineCostModel (InitArmEnv rd files dir InitEnv)
      (234 * FineScale + g_init) :=
    (initArmEnv_fine_groupSpec rd files dir hinit).mono (by generalize FineScale = fs; omega)
  have hs1 := r1bFileStepEnv_fine_groupSpec rd files dir (utf8 "identity-key")
  have hs2 := r1bFileStepEnv_fine_groupSpec rd files dir (utf8 "registration-id")
  have hs3 := optStage_groupSpec (r1bFileStepEnv_fine_groupSpec rd files dir (utf8 "signed-pre-key"))
  have hs4 := optStage_groupSpec (r1bFileStepEnv_fine_groupSpec rd files dir (utf8 "kyber-pre-key"))
  have hs5 := optStage_groupSpec (r1bFileStepEnv_fine_groupSpec rd files dir (utf8 "one-time-pre-key"))
  have hss := optStage_groupSpec (splitSigned_fine_groupSpec [])
  have hsi := optStage_groupSpec (splitId_fine_groupSpec [])
  have hds := optStage_groupSpec r1bDeserStageEnv_fine_groupSpec
  have hr1b : PhaseGroupSpec fineCostModel (R1bBinaryEnv rd files dir) (192 * FineScale) :=
    (hs2.seq (hs3.seq (hss.seq (hs4.seq (hss.seq (hs5.seq (hsi.seq hds))))))).mono
      (by generalize FineScale = fs; omega)
  have hr1cSeq : PhaseGroupSpec fineCostModel (R1cEnv InitEnv) g_init :=
    (hinit.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono (by generalize FineScale = fs; omega)
  have hr1c : PhaseGroupSpec fineCostModel (OptStageEnv (R1cEnv InitEnv)) g_init :=
    optStage_groupSpec hr1cSeq
  have hcore : PhaseGroupSpec fineCostModel (InitArmBinaryCoreEnv rd files dir InitEnv)
      (234 * FineScale + g_init) :=
    (hs1.seq ((optStage_groupSpec hr1b).seq hr1c)).mono (by generalize FineScale = fs; omega)
  exact (hop.or hcore).mono (max_self_le _)

private theorem r3aBinaryEnv_fine_phaseCredit {rest : List (BitVec 8)}
    {DecSigEnv : List AllocEvent → Prop} {c_d l_d p_d r_d : Nat}
    (hrest : rest.length ≤ msgCapBytes)
    (hdec : PhaseCreditSpec fineCostModel DecSigEnv c_d l_d p_d r_d) (hlp_d : l_d ≤ p_d) :
    PhaseCreditSpec fineCostModel (R3aBinaryEnv rest DecSigEnv)
      (sigSliceCum msgCapBytes + c_d) (sigSliceLive msgCapBytes + l_d)
      (max (sigSlicePeak msgCapBytes) (sigSliceLive msgCapBytes + p_d))
      (max (sigSliceMaxReq msgCapBytes) r_d) := by
  have hsig := (sigTryFromCanonInner_phaseCredit fineCostModel_modelHyps
    fineCostModel_wireLowInterceptHyps rest).mono
    (sigTryFromDeltaCum_le_cap hrest) (sigTryFromDeltaLive_le_cap hrest)
    (sigTryFromDeltaPeak_le_cap hrest) (sigTryFromMaxReq_le_cap hrest)
  exact phaseCredit_or_freeOnly_left fineCostModel_modelHyps (fun _ hf => hf)
    (hsig.seq (phaseCredit_or_freeOnly_left fineCostModel_modelHyps (fun _ hf => hf)
      (phaseCredit_seq_freeOnly_right fineCostModel_modelHyps hdec (fun _ hf => hf) hlp_d)))

private theorem r3aBinaryEnv_fine_groupSpec {rest : List (BitVec 8)}
    {DecSigEnv : List AllocEvent → Prop} {g_decSig : Nat}
    (hrest : rest.length ≤ msgCapBytes)
    (hdec : PhaseGroupSpec fineCostModel DecSigEnv g_decSig) :
    PhaseGroupSpec fineCostModel (R3aBinaryEnv rest DecSigEnv)
      (sigTryFromCapDeltaGrpS msgCapBytes + g_decSig) := by
  have hsig : PhaseGroupSpec fineCostModel (SigTryFromCanonInnerEnv rest)
      (sigTryFromCapDeltaGrpS msgCapBytes) :=
    (sigTryFromCanonInner_phaseGroup fineCostModel_wireGroupHyps rest).mono
      (sigTryFromDeltaGrpS_le_cap hrest)
  have hdecFree : PhaseGroupSpec fineCostModel (SeqEnv DecSigEnv FreeOnlyEvs) g_decSig :=
    (hdec.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono
      (by generalize FineScale = fs; omega)
  have htail : PhaseGroupSpec fineCostModel (OptStageEnv (SeqEnv DecSigEnv FreeOnlyEvs)) g_decSig :=
    optStage_groupSpec hdecFree
  exact optStage_groupSpec (hsig.seq htail)

/-! ## 4. Whole-`run` & Whole-`main` `< 90%` / `≤ 1 GiB` / `cliBudgetLimits` `FitsTrace` & `FitsEnv` -/

/-- Binary whole-`run` scaled group count `grpS` (`cliRealDirectRunGrpS_i + 27 * FineScale`). -/
def cliRealBinaryDirectRunGrpS_i : Nat :=
  cliRealDirectRunGrpS_i + 27 * FineScale

/-- Canonical binary whole-`main` `stepReserve` (widened `16384`-B `AddrOpt`/`BundleOpt` setup). -/
def cliRealBinaryDirectMainStepReserve_i : Nat :=
  cliMainWidenedStepReserveOf cliRealDirectRunMaxReq_i cliRealBinaryDirectRunGrpS_i

/-- `< 90%` (`≤ 966,367,641` B), `≤ 1 GiB`, and `VA ≤ 2 ^ 48` bounds for
`cliRealBinaryDirectRunGrpS_i` under the widened `16384`-B setup. -/
theorem cliRealBinaryDirect1MiB_i_fits_90pct_and_oneGiB :
    cliDecoupledRamNeed cliDefaultStaticBytes (cliMainWidenedCumOf cliRealDirectRunCum_i)
      (cliMainTightPeakOf cliRealDirectRunLive_i cliRealDirectRunPeak_i)
      (cliMainTightReqOf cliRealDirectRunMaxReq_i)
      (cliMainWidenedGrpCountOf cliRealBinaryDirectRunGrpS_i) ≤ cliRealNinetyPctOneGiB ∧
    cliDecoupledRamNeed cliDefaultStaticBytes (cliMainWidenedCumOf cliRealDirectRunCum_i)
      (cliMainTightPeakOf cliRealDirectRunLive_i cliRealDirectRunPeak_i)
      (cliMainTightReqOf cliRealDirectRunMaxReq_i)
      (cliMainWidenedGrpCountOf cliRealBinaryDirectRunGrpS_i) ≤ cliOneGiB ∧
    cliDecoupledVaNeed cliDefaultStaticBytes cliDefaultStaticCount
      (cliMainWidenedCumOf cliRealDirectRunCum_i)
      (cliMainTightPeakOf cliRealDirectRunLive_i cliRealDirectRunPeak_i)
      (cliMainTightReqOf cliRealDirectRunMaxReq_i)
      (cliMainWidenedGrpCountOf cliRealBinaryDirectRunGrpS_i) ≤ 2 ^ 48 :=
  ⟨by decide, by decide, by decide⟩

/-- Parametric `1 MiB` binary whole-`run` `Δcum` taking `max` over both `initArmDeltaCum` and
`initArmBinaryPrefixCum + initCum`. -/
def cliRunBinary1MiBCustomPksmCum (pksmCum initCum encCum decSigCum decPkCum : Nat) : Nat :=
  r0Opened1MiBCum +
    max
      (max (initArmDeltaCum (pathDeltaCum 26 16) 1637 initCum)
        (initArmBinaryPrefixCum + initCum))
      (max (r2TightDeltaCum encCum sessionCapBytes)
        (max (sigSliceCum msgCapBytes + decSigCum)
          (pksmCum + decPkCum)))

/-- Parametric `1 MiB` binary whole-`run` `maxReq` including `fineReadFileMaxReq 1637` in `init`. -/
def cliRunBinary1MiBCustomPksmMaxReq
    (pksmMaxReq initMaxReq encMaxReq decSigMaxReq decPkMaxReq : Nat) : Nat :=
  max r0Opened1MiBMaxReq
    (max
      (max (initArmMaxReq (pathMaxReq 26 16) 1637 initMaxReq)
        (max (fineReadFileMaxReq 1637) initMaxReq))
      (max (r2MaxReq encMaxReq sessionCapBytes)
        (max (max (sigSliceMaxReq msgCapBytes) decSigMaxReq)
          (max pksmMaxReq decPkMaxReq))))

/-- Whole-`run` `PhaseCreditSpec fineCostModel` on `CliRunBinaryEnv` requiring only
`CliPqxdhInputs W g.i`, `g.i.stdin.length ≤ msgCapBytes`, and `parseArgs = some g.c`. -/
theorem cliRunBinaryEnv_real_1MiB_fine_phaseCredit_of_cliPqInputs
    {W : PEParams} {E : RunCall → CliRunCalleeEnvs} {g : RunCall}
    (SE : CliRealCalleeFineSpecs (E g))
    (hi : CliPqxdhInputs W g.i)
    (hstdin : g.i.stdin.length ≤ msgCapBytes)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c) :
    PhaseCreditSpec fineCostModel (CliRunBinaryEnv cliIo.rd (E g) sessionCapBytes g)
      (cliRunBinary1MiBCustomPksmCum SE.pksmCum SE.initCum SE.encCum SE.decSigCum SE.decPkCum)
      (cliRun1MiBCustomPksmLive SE.pksmLive SE.initLive SE.encLive SE.decSigLive SE.decPkLive)
      (cliRun1MiBCustomPksmPeak SE.pksmLive SE.pksmPeak
        SE.initPeak SE.encLive SE.encPeak SE.decSigPeak SE.decPkPeak)
      (cliRunBinary1MiBCustomPksmMaxReq SE.pksmMaxReq
        SE.initMaxReq SE.encMaxReq SE.decSigMaxReq SE.decPkMaxReq) := by
  have hr0 := r0BinaryEnv_fine_phaseCredit hi
  have harm : PhaseCreditSpec fineCostModel
      (RunArmBinaryEnv cliIo.rd (runFiles g.i) (E g) sessionCapBytes g.i.stdin g.c)
      (max
        (max (initArmDeltaCum (pathDeltaCum 26 16) 1637 SE.initCum)
          (initArmBinaryPrefixCum + SE.initCum))
        (max (r2TightDeltaCum SE.encCum sessionCapBytes)
          (max (sigSliceCum msgCapBytes + SE.decSigCum) (SE.pksmCum + SE.decPkCum))))
      (max (initArmDeltaLive (pathDeltaLive 26 16) SE.initLive)
        (max (r2DeltaLive fineCostModel SE.encLive sessionCapBytes)
          (max (sigSliceLive msgCapBytes + SE.decSigLive) (SE.pksmLive + SE.decPkLive))))
      (max (initArmDeltaPeak (pathDeltaLive 26 16) (pathDeltaPeak 26 16) 1637 SE.initPeak)
        (max (r2DeltaPeak fineCostModel SE.encLive SE.encPeak sessionCapBytes)
          (max (max (sigSlicePeak msgCapBytes) (sigSliceLive msgCapBytes + SE.decSigPeak))
            (max SE.pksmPeak (SE.pksmLive + SE.decPkPeak)))))
      (max
        (max (initArmMaxReq (pathMaxReq 26 16) 1637 SE.initMaxReq)
          (max (fineReadFileMaxReq 1637) SE.initMaxReq))
        (max (r2MaxReq SE.encMaxReq sessionCapBytes)
          (max (max (sigSliceMaxReq msgCapBytes) SE.decSigMaxReq)
            (max SE.pksmMaxReq SE.decPkMaxReq)))) := by
    cases hcmd : g.c with
    | keygen _ _ =>
      exact (PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    | init peer dir =>
      have hpath := cliIo_rd_initBundle_caps_of_cliPqInputs hi hparse peer dir hcmd
      have hslash := cliIo_rd_initBundle_nonempty_caps_of_cliPqInputs hi hparse peer dir hcmd
      exact (initArmBinaryEnv_fine_phaseCredit hpath.1 hpath.2 hslash.2.2
        SE.init_spec SE.init_lp).mono
        (Nat.le_max_left _ _) (Nat.le_max_left _ _) (Nat.le_max_left _ _) (Nat.le_max_left _ _)
    | send _ =>
      exact (r2_tight_phaseCredit fineCostModel_modelHyps fineCostModel_cliRunTightHyps
        SE.enc_spec).mono
        (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
        (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
        (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
        (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
    | recv _ =>
      have hrecv : PhaseCreditSpec fineCostModel
          (RecvArmBinaryEnv g.i.stdin (E g).decSigEnv (E g).pksmEnv (E g).decPkEnv)
          (max (sigSliceCum msgCapBytes + SE.decSigCum) (SE.pksmCum + SE.decPkCum))
          (max (sigSliceLive msgCapBytes + SE.decSigLive) (SE.pksmLive + SE.decPkLive))
          (max (max (sigSlicePeak msgCapBytes) (sigSliceLive msgCapBytes + SE.decSigPeak))
            (max SE.pksmPeak (SE.pksmLive + SE.decPkPeak)))
          (max (max (sigSliceMaxReq msgCapBytes) SE.decSigMaxReq)
            (max SE.pksmMaxReq SE.decPkMaxReq)) := by
        unfold RecvArmBinaryEnv
        rcases hst : g.i.stdin with _ | ⟨b, rest⟩
        · exact (recvBad_phaseCredit fineCostModel_modelHyps).mono
            (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
        · have hrest : rest.length ≤ msgCapBytes := by
            rw [hst, List.length_cons] at hstdin; omega
          by_cases hb2 : b = 2#8
          · simp only [hb2, ↓reduceIte]
            exact (r3aBinaryEnv_fine_phaseCredit hrest SE.decSig_spec SE.decSig_lp).mono
              (Nat.le_max_left _ _) (Nat.le_max_left _ _)
              (Nat.le_max_left _ _) (Nat.le_max_left _ _)
          · simp only [hb2, ↓reduceIte]
            by_cases hb3 : b = 3#8
            · simp only [hb3, ↓reduceIte]
              exact (r3b_phaseCredit fineCostModel_modelHyps (SE.pksm_spec rest hrest)
                SE.decPk_spec SE.decPk_lp).mono
                (Nat.le_max_right _ _) (Nat.le_max_right _ _)
                (Nat.le_max_right _ _) (Nat.le_max_right _ _)
            · simp only [hb3, ↓reduceIte]
              exact (recvBad_phaseCredit fineCostModel_modelHyps).mono
                (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
      exact hrecv.mono
        (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
        (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
        (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
        (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
  have haj := phaseCredit_seq_freeOnly_right fineCostModel_modelHyps harm (fun _ hf => hf)
    (CliRunArmsPeak.runArmDeltaLive_le_peak SE.toSlotCalleeSpecs)
  exact phaseCredit_or_freeOnly_left fineCostModel_modelHyps (fun _ hf => hf) (hr0.seq haj)

/-- Parametric whole-`run` `PhaseGroupSpec fineCostModel` on `CliRunBinaryEnv` over abstract `SE`. -/
theorem cliRunBinaryEnv_real_fine_groupSpec
    {E : RunCall → CliRunCalleeEnvs} {g : RunCall}
    (SE : CliRealCalleeFineSpecs (E g))
    (hstdin : g.i.stdin.length ≤ msgCapBytes)
    (hinit_sub : 234 * FineScale + SE.initGrpS ≤ cliRealDirectRunGrpS_i - 15 * FineScale)
    (h5 : cliRunOpenedCustomPksmGrpS msgCapBytes SE.pksmGrpS
      SE.initGrpS SE.encGrpS SE.decSigGrpS SE.decPkGrpS ≤ cliRealDirectRunGrpS_i) :
    PhaseGroupSpec fineCostModel
      (CliRunBinaryEnv cliIo.rd (E g) sessionCapBytes g)
      cliRealBinaryDirectRunGrpS_i := by
  have harm : PhaseGroupSpec fineCostModel
      (RunArmBinaryEnv cliIo.rd (runFiles g.i) (E g) sessionCapBytes g.i.stdin g.c)
      (max (234 * FineScale + SE.initGrpS)
        (max (SE.encGrpS + 3 * FineScale)
          (max (sigTryFromCapDeltaGrpS msgCapBytes + SE.decSigGrpS)
            (SE.pksmGrpS + SE.decPkGrpS)))) := by
    cases g.c with
    | keygen _ _ =>
      exact (PhaseGroupSpec.freeOnly fineCostModel).mono (Nat.zero_le _)
    | init _ dir =>
      exact (initArmBinaryEnv_fine_groupSpec cliIo.rd (runFiles g.i) dir SE.init_grp).mono
        (Nat.le_max_left _ _)
    | send _ =>
      exact (r2Env_fine_groupSpec sessionCapBytes SE.enc_grp).mono
        (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
    | recv _ =>
      have hrecv : PhaseGroupSpec fineCostModel
          (RecvArmBinaryEnv g.i.stdin (E g).decSigEnv (E g).pksmEnv (E g).decPkEnv)
          (max (sigTryFromCapDeltaGrpS msgCapBytes + SE.decSigGrpS)
            (SE.pksmGrpS + SE.decPkGrpS)) := by
        unfold RecvArmBinaryEnv
        rcases hst : g.i.stdin with _ | ⟨b, rest⟩
        · exact (PhaseGroupSpec.freeOnly fineCostModel).mono (Nat.zero_le _)
        · have hrest : rest.length ≤ msgCapBytes := by
            rw [hst, List.length_cons] at hstdin; omega
          by_cases hb2 : b = 2#8
          · simp only [hb2, ↓reduceIte]
            exact (r3aBinaryEnv_fine_groupSpec hrest SE.decSig_grp).mono (Nat.le_max_left _ _)
          · simp only [hb2, ↓reduceIte]
            by_cases hb3 : b = 3#8
            · simp only [hb3, ↓reduceIte]
              exact (r3bEnv_of_pksm_fine_groupSpec (SE.pksm_grp rest hrest) SE.decPk_grp).mono
                (Nat.le_max_right _ _)
            · simp only [hb3, ↓reduceIte]
              exact (PhaseGroupSpec.freeOnly fineCostModel).mono (Nat.zero_le _)
      exact hrecv.mono (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
  have hrest_sub :
      max (SE.encGrpS + 3 * FineScale)
        (max (sigTryFromCapDeltaGrpS msgCapBytes + SE.decSigGrpS)
          (SE.pksmGrpS + SE.decPkGrpS)) ≤ cliRealDirectRunGrpS_i - 15 * FineScale := by
    unfold cliRunOpenedCustomPksmGrpS at h5
    generalize FineScale = fs at h5 ⊢
    omega
  exact (cliRunOfR0_fine_groupSpec (r0BinaryEnv_fine_groupSpec cliIo.rd g) harm).mono (by
    have hmax := Nat.max_le.mpr ⟨hinit_sub, hrest_sub⟩
    unfold cliRealBinaryDirectRunGrpS_i
    have hge : 15 * FineScale ≤ cliRealDirectRunGrpS_i := by decide
    generalize FineScale = fs at hmax hge ⊢
    omega)

private theorem existentialRealCalleeFineSpecs_initGrpS_bound [LibsignalPlacement]
    (img : Arm64.Obj.Image) (S : RunSem) {P : PEParams} {g : RunCall}
    (hi : CliPqxdhInputs P g.i)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c) :
    234 * FineScale + (existentialRealCalleeFineSpecs img S hi hparse).initGrpS ≤
      cliRealDirectRunGrpS_i - 15 * FineScale := by
  dsimp only [existentialRealCalleeFineSpecs]
  decide

private theorem existentialRealCalleeFineSpecs_binaryRunCum_bound [LibsignalPlacement]
    (img : Arm64.Obj.Image) (S : RunSem) {P : PEParams} {g : RunCall}
    (hi : CliPqxdhInputs P g.i)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c) :
    let SE := existentialRealCalleeFineSpecs img S hi hparse
    cliRunBinary1MiBCustomPksmCum SE.pksmCum SE.initCum SE.encCum SE.decSigCum SE.decPkCum ≤
      cliRealDirectRunCum_i ∧
    cliRunBinary1MiBCustomPksmMaxReq SE.pksmMaxReq SE.initMaxReq SE.encMaxReq
      SE.decSigMaxReq SE.decPkMaxReq ≤ cliRealDirectRunMaxReq_i := by
  dsimp only [existentialRealCalleeFineSpecs]
  exact ⟨by decide, by decide⟩

/-- Whole-`run` `PhaseGroupSpec fineCostModel` on `CliRunBinaryEnv` at
`mkExistentialRealCalleeEnvs img S W g`. -/
theorem cliRunBinaryEnv_existential_fine_groupSpec [LibsignalPlacement]
    (img : Arm64.Obj.Image) (S : RunSem) {W : PEParams} {g : RunCall}
    (hi : CliPqxdhInputs W g.i)
    (hstdin : g.i.stdin.length ≤ msgCapBytes)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c) :
    PhaseGroupSpec fineCostModel
      (CliRunBinaryEnv cliIo.rd (mkExistentialRealCalleeEnvs img S W g) sessionCapBytes g)
      cliRealBinaryDirectRunGrpS_i :=
  cliRunBinaryEnv_real_fine_groupSpec (existentialRealCalleeFineSpecs img S hi hparse) hstdin
    (existentialRealCalleeFineSpecs_initGrpS_bound img S hi hparse)
    (existentialRealCalleeFineSpecs_direct_run_bounds img S hi hparse).2.2.2.2

private theorem realCliMainBinaryEnvOf_90pct_bounds_direct {lim : BudgetLimits}
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes) (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap90 : cliRealNinetyPctOneGiB ≤ lim.physCap) :
    cliMainTightLiveOf cliRealDirectRunLive_i ≤
      cliMainTightPeakOf cliRealDirectRunLive_i cliRealDirectRunPeak_i ∧
    cliDecoupledRamNeed lim.staticBytes (cliMainWidenedCumOf cliRealDirectRunCum_i)
      (cliMainTightPeakOf cliRealDirectRunLive_i cliRealDirectRunPeak_i)
      (cliMainTightReqOf cliRealDirectRunMaxReq_i)
      (cliMainWidenedGrpCountOf cliRealBinaryDirectRunGrpS_i) ≤ lim.physCap ∧
    cliDecoupledVaNeed lim.staticBytes lim.staticCount (cliMainWidenedCumOf cliRealDirectRunCum_i)
      (cliMainTightPeakOf cliRealDirectRunLive_i cliRealDirectRunPeak_i)
      (cliMainTightReqOf cliRealDirectRunMaxReq_i)
      (cliMainWidenedGrpCountOf cliRealBinaryDirectRunGrpS_i) ≤ 2 ^ 48 :=
  ⟨by unfold cliMainTightLiveOf cliMainTightPeakOf cliMainDeltaLive_tight cliMainDeltaPeak_tight
      exact Nat.le_trans (Nat.add_le_add_left
        (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_max_right _ _)) _) (Nat.le_max_right _ _),
   Nat.le_trans
     (cliDecoupledRamNeed_mono hsb (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
     (Nat.le_trans cliRealBinaryDirect1MiB_i_fits_90pct_and_oneGiB.1 hcap90),
   Nat.le_trans
     (cliDecoupledVaNeed_mono hsb hsc (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
       (Nat.le_refl _))
     cliRealBinaryDirect1MiB_i_fits_90pct_and_oneGiB.2.2⟩

private theorem m2CollectFull_phaseCredit_fine {argvLen : Nat} (hargv : argvLen ≤ 3) :
    PhaseCreditSpec fineCostModel (M2CollectFullEnv argvLen) 29001 0 0 64 := by
  have hM := fineCostModel_modelHyps
  have hsm64 : 64 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have halloc64 : PhaseCreditSpec fineCostModel (· = rustAllocEvents 64 8) (2 * 64 + 9539) 0 0 64 :=
    (PhaseCreditSpec.rustAlloc_small_any hM (req := 64) (al := 8) (by decide) hsm64).mono
      (hM.smallAlloc_le hsm64) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 64)
  have hstep : ∀ k ∈ List.range' 1 (argvLen - 1),
      PhaseCreditSpec fineCostModel (M2CollectStepEnv k) 9667 0 0 64 := by
    intro k hk; rw [List.mem_range'] at hk; obtain ⟨i, _, rfl⟩ := hk
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · have hcap : reserveCapStride 16 1 1 1 = 4 := by decide
      unfold M2CollectStepEnv; rw [hcap]
      exact ((PhaseCreditSpec.nil fineCostModel).or
        (phaseCredit_rustRealloc_small_any hM (old := 16 * 1) (new := 16 * 4) (al := 8)
          (by decide) (by decide) (by omega) (by omega))).mono
        (by decide) (by decide) (by decide) (by decide)
    · have hcap : reserveCapStride 16 2 2 1 = 4 := by decide
      unfold M2CollectStepEnv; rw [hcap]
      exact ((PhaseCreditSpec.nil fineCostModel).or
        (phaseCredit_rustRealloc_small_any hM (old := 16 * 2) (new := 16 * 4) (al := 8)
          (by decide) (by decide) (by omega) (by omega))).mono
        (by decide) (by decide) (by decide) (by decide)
  have hiter : PhaseCreditSpec fineCostModel
      (IterSeqEnv M2CollectStepEnv (List.range' 1 (argvLen - 1))) ((argvLen - 1) * 9667) 0 0 64 := by
    simpa only [List.length_range'] using PhaseCreditSpec.iter_zero_live (M := fineCostModel)
      (Step := M2CollectStepEnv) (c := 9667) (p := 0) (r := 64) (List.range' 1 (argvLen - 1)) hstep
  exact ((phaseCredit_m2Collect_small64 hM hsm64 hargv).or (halloc64.seq hiter)).mono
    (by omega) (by omega) (by omega) (by omega)

private theorem m2CollectFull_fine_groupSpec {argvLen : Nat} (hargv : argvLen ≤ 3) :
    PhaseGroupSpec fineCostModel (M2CollectFullEnv argvLen) (3 * (3 * FineScale)) := by
  have h1 := (m2CollectEnv_groupSpec fineCostModel argvLen).mono
    (Nat.mul_le_mul_right (3 * FineScale) hargv)
  have hiter : PhaseGroupSpec fineCostModel
      (IterSeqEnv M2CollectStepEnv (List.range' 1 (argvLen - 1)))
      ((argvLen - 1) * (3 * FineScale)) := by
    simpa only [List.length_range'] using PhaseGroupSpec.iterSeq_const (M := fineCostModel)
      (Step := M2CollectStepEnv) (3 * FineScale) (List.range' 1 (argvLen - 1))
      (fun k _ => m2CollectStepEnv_groupSpec fineCostModel k)
  refine (h1.or ((PhaseGroupSpec.rustAlloc_any fineCostModel 64 8).seq hiter)).mono ?_
  have hc : (argvLen - 1) * (3 * FineScale) ≤ 2 * (3 * FineScale) :=
    Nat.mul_le_mul_right _ (by omega)
  unfold FineScale at hc ⊢; omega

private theorem optAlloc16384_phaseCredit_fine :
    PhaseCreditSpec fineCostModel
      (fun evs => evs = [] ∨ ∃ n : Nat, n ≤ 16384 ∧ evs = rustAllocEvents n 1)
      42307 0 0 16384 := by
  have halloc (n : Nat) (hn : n ≤ 16384) :
      PhaseCreditSpec fineCostModel (· = rustAllocEvents n 1) 42307 0 0 16384 := by
    have hsm : n ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
      rw [fineCostModel_smallMaxReq_eq]; omega
    exact (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps
      (req := n) (al := 1) (by decide) hsm).mono
      (Nat.le_trans (fineCostModel_modelHyps.smallAlloc_le hsm) (by omega))
      (Nat.le_refl 0) (Nat.le_refl 0) hn
  have h1 : PhaseCreditSpec fineCostModel
      (fun evs => ∃ n : Nat, n ≤ 16384 ∧ evs = rustAllocEvents n 1) 42307 0 0 16384 :=
    { req_align := fun evs ⟨n, hn, he⟩ ev hev => (halloc n hn).req_align evs he ev hev
      credit_le := fun st0 {_} ⟨n, hn, he⟩ => (halloc n hn).credit_le st0 he }
  exact ((PhaseCreditSpec.nil fineCostModel).or h1).mono
    (by decide) (by decide) (by decide) (by decide)

private theorem addrOptBounded_phaseCredit_fine :
    PhaseCreditSpec fineCostModel AddrOptBoundedEnv 42307 0 0 16384 :=
  optAlloc16384_phaseCredit_fine

private theorem bundleOptBounded_phaseCredit_fine :
    PhaseCreditSpec fineCostModel BundleOptBoundedEnv 42307 0 0 16384 :=
  optAlloc16384_phaseCredit_fine

private theorem optAlloc16384_fine_groupSpec :
    PhaseGroupSpec fineCostModel
      (fun evs => evs = [] ∨ ∃ n : Nat, n ≤ 16384 ∧ evs = rustAllocEvents n 1)
      (3 * FineScale) where
  groups_le st0 {_} h := by
    rcases h with rfl | ⟨n, _, rfl⟩
    · simp [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
    · exact (PhaseGroupSpec.rustAlloc_any fineCostModel n 1).groups_le st0 rfl

private theorem addrOptBounded_fine_groupSpec :
    PhaseGroupSpec fineCostModel AddrOptBoundedEnv (3 * FineScale) :=
  optAlloc16384_fine_groupSpec

private theorem bundleOptBounded_fine_groupSpec :
    PhaseGroupSpec fineCostModel BundleOptBoundedEnv (3 * FineScale) :=
  optAlloc16384_fine_groupSpec

private theorem fine_sm_bounds :
    131072 ≤ HasFineReallocCredit.smallMaxReq fineCostModel ∧
    HasFineReallocCredit.smallMaxReq fineCostModel < 262144 := by
  rw [fineCostModel_smallMaxReq_eq]; decide

private theorem allocBytes1_bounded_phaseCredit_fine (cap cum live peak req : Nat)
    (hc : 533825 ≤ cum) (hl : cap + 8195 ≤ live) (hp : cap + 8195 ≤ peak) (hr : cap ≤ req) :
    PhaseCreditSpec fineCostModel
      (fun evs => ∃ bs : List (BitVec 8), bs.length ≤ cap ∧ evs = allocBytes1Events bs)
      cum live peak req where
  req_align evs := fun ⟨bs, hbs, he⟩ ev hev =>
    ((phaseCredit_allocBytes1_tight fineCostModel_modelHyps fine_sm_bounds.2 bs hbs).mono
      hc hl hp hr).req_align evs he ev hev
  credit_le st0 {_} := fun ⟨bs, hbs, he⟩ =>
    ((phaseCredit_allocBytes1_tight fineCostModel_modelHyps fine_sm_bounds.2 bs hbs).mono
      hc hl hp hr).credit_le st0 he

private theorem boundedReadStdin_phaseCredit_fine :
    PhaseCreditSpec fineCostModel BoundedReadStdinEnv readStdinDeltaCum_tight
      (readStdinDeltaLive msgCapBytes) (readStdinDeltaPeak msgCapBytes)
      (readStdinMaxReq msgCapBytes) := by
  have hM := fineCostModel_modelHyps
  have h1 := allocBytes1_bounded_phaseCredit_fine msgCapBytes readStdinDeltaCum_tight
    (readStdinDeltaLive msgCapBytes) (readStdinDeltaPeak msgCapBytes) (readStdinMaxReq msgCapBytes)
    (by unfold readStdinDeltaCum_tight; decide) (by unfold readStdinDeltaLive msgCapBytes; decide)
    (by unfold readStdinDeltaPeak msgCapBytes; decide) (by unfold readStdinMaxReq msgCapBytes; decide)
  have hcap_raw : PhaseCreditSpec fineCostModel
      (fun e => ∃ r : Nat, e = cliIoCapEvents (cliIoReadCaps 8 r)) 573696 1056771 1589254 1048576 :=
    PhaseCreditSpec.of_imp (fun _ ⟨r, he⟩ => ⟨r, he⟩)
      (phaseCreditSpec_cliIoReadStdin_anyR_tight hM fine_sm_bounds.1 fine_sm_bounds.2)
  exact ((PhaseCreditSpec.nil fineCostModel).or
    (h1.or (hcap_raw.seq (PhaseCreditSpec.freeOnly hM.freeNonInc)))).mono
    (by unfold readStdinDeltaCum_tight; decide) (by unfold readStdinDeltaLive msgCapBytes; decide)
    (by unfold readStdinDeltaPeak msgCapBytes; decide) (by unfold readStdinMaxReq msgCapBytes; decide)

private theorem boundedReadFile_phaseCredit_fine :
    PhaseCreditSpec fineCostModel BoundedReadFileEnv readFileDeltaCum_tight
      (max (sessionCapBytes + 8195) (2097152 + 8195))
      (max (sessionCapBytes + 8195) 3162118) (max sessionCapBytes 2097152) := by
  have hM := fineCostModel_modelHyps
  have h1 := allocBytes1_bounded_phaseCredit_fine sessionCapBytes readFileDeltaCum_tight
    (max (sessionCapBytes + 8195) (2097152 + 8195))
    (max (sessionCapBytes + 8195) 3162118) (max sessionCapBytes 2097152)
    (by unfold readFileDeltaCum_tight; decide)
    (Nat.le_max_left _ _) (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have hcap_raw : PhaseCreditSpec fineCostModel
      (fun e => ∃ r : Nat, e = cliIoCapEvents (cliIoReadCaps 9 r)) 573818 2105347 3162118 2097152 :=
    PhaseCreditSpec.of_imp (fun _ ⟨r, he⟩ => ⟨r, he⟩)
      (phaseCreditSpec_cliIoReadFile_anyR_tight hM fine_sm_bounds.1 fine_sm_bounds.2)
  exact ((PhaseCreditSpec.nil fineCostModel).or
    (h1.or (hcap_raw.seq (PhaseCreditSpec.freeOnly hM.freeNonInc)))).mono
    (by unfold readFileDeltaCum_tight; decide) (by unfold sessionCapBytes; decide)
    (by unfold sessionCapBytes; decide) (by unfold sessionCapBytes; decide)

private theorem m3BoundedSetup_phaseCredit_fine :
    PhaseCreditSpec fineCostModel M3BoundedSetupEnv m3PhaseDeltaCum_tight
      (m3PhaseDeltaLive msgCapBytes sessionCapBytes)
      (m3PhaseDeltaPeak msgCapBytes sessionCapBytes)
      (m3PhaseMaxReq msgCapBytes sessionCapBytes) :=
  (boundedReadStdin_phaseCredit_fine.seq
    (boundedReadFile_phaseCredit_fine.seq
      (PhaseCreditSpec.freeOnly fineCostModel_modelHyps.freeNonInc))).mono
    (by unfold m3PhaseDeltaCum_tight readStdinDeltaCum_tight readFileDeltaCum_tight; decide)
    (by unfold m3PhaseDeltaLive readStdinDeltaLive msgCapBytes sessionCapBytes; decide)
    (by unfold m3PhaseDeltaPeak readStdinDeltaPeak readStdinDeltaLive msgCapBytes sessionCapBytes
        decide)
    (by unfold m3PhaseMaxReq readStdinMaxReq msgCapBytes sessionCapBytes; decide)

private theorem allocBytes1_bounded_fine_groupSpec (cap grp : Nat) (hgrp : 3 * FineScale ≤ grp) :
    PhaseGroupSpec fineCostModel
      (fun evs => ∃ bs : List (BitVec 8), bs.length ≤ cap ∧ evs = allocBytes1Events bs) grp where
  groups_le st0 {_} := fun ⟨bs, _, hevs⟩ => by
    subst hevs; unfold allocBytes1Events; split
    · simp [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
    · exact Nat.le_trans
        ((PhaseGroupSpec.rustAlloc_any fineCostModel bs.length 1).groups_le st0 rfl)
        (Nat.add_le_add_left hgrp _)

private theorem boundedReadStdin_fine_groupSpec :
    PhaseGroupSpec fineCostModel BoundedReadStdinEnv (27 * FineScale) := by
  have h1 := allocBytes1_bounded_fine_groupSpec msgCapBytes (27 * FineScale)
    (by unfold FineScale; decide)
  have hnf : NonFreeBound (fun e => ∃ r : Nat, e = cliIoCapEvents (cliIoReadCaps 8 r)) 9 :=
    fun _ ⟨r, hr⟩ => hr ▸ cliIoReadStdinEnv_nonFreeBound r _ rfl
  exact ((PhaseGroupSpec.nil fineCostModel).or
    (h1.or ((PhaseGroupSpec.of_nonFreeBound fineCostModel hnf).seq
      (PhaseGroupSpec.freeOnly fineCostModel)))).mono (by unfold FineScale; decide)

private theorem boundedReadFile_fine_groupSpec :
    PhaseGroupSpec fineCostModel BoundedReadFileEnv (30 * FineScale) := by
  have h1 := allocBytes1_bounded_fine_groupSpec sessionCapBytes (30 * FineScale)
    (by unfold FineScale; decide)
  have hnf : NonFreeBound (fun e => ∃ r : Nat, e = cliIoCapEvents (cliIoReadCaps 9 r)) 10 :=
    fun _ ⟨r, hr⟩ => hr ▸ cliIoReadFileEnv_nonFreeBound r _ rfl
  exact ((PhaseGroupSpec.nil fineCostModel).or
    (h1.or ((PhaseGroupSpec.of_nonFreeBound fineCostModel hnf).seq
      (PhaseGroupSpec.freeOnly fineCostModel)))).mono (by unfold FineScale; decide)

theorem cliMainBoundedSetup_phaseCredit_fine {argvLen : Nat} (hargv : argvLen ≤ 3) :
    PhaseCreditSpec fineCostModel (CliMainBoundedSetupEnv argvLen)
      (123250 + m3PhaseDeltaCum_tight) (m3PhaseDeltaLive msgCapBytes sessionCapBytes)
      (m3PhaseDeltaPeak msgCapBytes sessionCapBytes)
      (max 16384 (m3PhaseMaxReq msgCapBytes sessionCapBytes)) := by
  have hM := fineCostModel_modelHyps
  have hsm64 : 64 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  exact ((PhaseCreditSpec.freeOnly hM.freeNonInc).or
    ((phaseCredit_m1Phase_small64 hM hsm64 hargv).seq
      ((m2CollectFull_phaseCredit_fine hargv).seq
        (addrOptBounded_phaseCredit_fine.seq
          (bundleOptBounded_phaseCredit_fine.seq
            ((PhaseCreditSpec.freeOnly hM.freeNonInc).seq m3BoundedSetup_phaseCredit_fine)))))).mono
    (by omega) (by omega) (by omega) (by omega)

theorem cliMainBoundedSetup_fine_groupSpec {argvLen : Nat} (hargv : argvLen ≤ 3) :
    PhaseGroupSpec fineCostModel (CliMainBoundedSetupEnv argvLen) cliMainWidenedSetupFineGrpS := by
  have hm3 : PhaseGroupSpec fineCostModel M3BoundedSetupEnv (57 * FineScale) :=
    (boundedReadStdin_fine_groupSpec.seq
      (boundedReadFile_fine_groupSpec.seq (PhaseGroupSpec.freeOnly fineCostModel))).mono
      (by unfold FineScale; decide)
  exact ((PhaseGroupSpec.freeOnly fineCostModel).or
    ((m1PhaseEnv_le_3_fine_groupSpec hargv).seq
      ((m2CollectFull_fine_groupSpec hargv).seq
        (addrOptBounded_fine_groupSpec.seq
          (bundleOptBounded_fine_groupSpec.seq
            ((PhaseGroupSpec.freeOnly fineCostModel).seq hm3)))))).mono
    (by unfold cliMainWidenedSetupFineGrpS FineScale; decide)

theorem m5Phase_Bounded_phaseCredit_fine
    {dirs : List (List (BitVec 8) × List (List (BitVec 8)))}
    (hsum : (dirs.map (fun dn => dn.2.length)).sum ≤ cliMaxDirtyEntries)
    (hdirs : ∀ dn ∈ dirs,
      dn.1.length ≤ cliMaxDirPathBytes ∧ ∀ nm ∈ dn.2, nm.length ≤ cliMaxAddrTextBytes) :
    PhaseCreditSpec fineCostModel (M5PhaseEnv dirs)
      (cliMaxDirtyEntries *
        (10 * max (4 * cliMaxDirPathBytes + cliMaxAddrTextBytes + 16) 16 + 4 * 9539))
      0 (m5DirStepDeltaPeak cliMaxDirPathBytes cliMaxAddrTextBytes)
      (m5DirStepMaxReq cliMaxDirPathBytes cliMaxAddrTextBytes) := by
  have hM := fineCostModel_modelHyps
  have hit : PhaseCreditSpec fineCostModel (IterSeqEnv (fun dn => M5DirStepEnv dn.1 dn.2) dirs)
      (((dirs.map (fun dn => dn.2.length)).sum) *
        (10 * max (4 * cliMaxDirPathBytes + cliMaxAddrTextBytes + 16) 16 + 4 * 9539))
      0 (m5DirStepDeltaPeak cliMaxDirPathBytes cliMaxAddrTextBytes)
      (m5DirStepMaxReq cliMaxDirPathBytes cliMaxAddrTextBytes) := by
    clear hsum; induction dirs with
    | nil =>
      exact (PhaseCreditSpec.nil fineCostModel).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    | cons dn dns ih =>
      obtain ⟨hd1, hd2⟩ := hdirs dn List.mem_cons_self
      refine ((m5DirStep_phaseCredit hM hd1 hd2).seq
        (ih (fun d hd => hdirs d (List.mem_cons_of_mem dn hd)))).mono ?_ (Nat.le_refl 0) ?_ ?_
      · simp only [List.map_cons, List.sum_cons, Nat.add_mul]; exact Nat.le_refl _
      · rw [Nat.zero_add]; exact Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩
      · exact Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩
  refine (hit.seq (PhaseCreditSpec.freeOnly hM.freeNonInc)).mono ?_ (Nat.le_refl 0) ?_ ?_
  · rw [Nat.add_zero]; exact Nat.mul_le_mul_right _ hsum
  · rw [Nat.zero_add]; exact Nat.max_le.mpr ⟨Nat.le_refl _, Nat.zero_le _⟩
  · exact Nat.max_le.mpr ⟨Nat.le_refl _, Nat.zero_le _⟩

/-- Concrete `PhaseCreditSpec fineCostModel` on `RealCliMainBinaryEnvOf (mkExistentialRealCalleeEnvs img S W) i`. -/
theorem realCliMainBinaryEnvOf_phaseCredit_fine_concrete [LibsignalPlacement]
    (img : Arm64.Obj.Image) (S : RunSem) {W : PEParams} {i : Inputs}
    (hi : CliPqxdhInputs W i) :
    PhaseCreditSpec fineCostModel
      (RealCliMainBinaryEnvOf (mkExistentialRealCalleeEnvs img S W) i)
      (cliMainWidenedCumOf cliRealDirectRunCum_i) (cliMainTightLiveOf cliRealDirectRunLive_i)
      (cliMainTightPeakOf cliRealDirectRunLive_i cliRealDirectRunPeak_i)
      (cliMainTightReqOf cliRealDirectRunMaxReq_i) := by
  have hsm1024 : 1024 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have hw (w : ValidPostSetupWitness i) : PhaseCreditSpec fineCostModel
      (SeqEnv (CliRunBinaryEnv cliIo.rd (mkExistentialRealCalleeEnvs img S W w.g)
          sessionCapBytes w.g)
        (SeqEnv (M5PhaseEnv w.dirs) (M6Env w.ok)))
      (cliRealDirectRunCum_i + cliMaxDirtyEntries *
        (10 * max (4 * cliMaxDirPathBytes + cliMaxAddrTextBytes + 16) 16 + 4 * 9539) + m6DeltaCum)
      cliRealDirectRunLive_i
      (max cliRealDirectRunPeak_i
        (cliRealDirectRunLive_i + m5DirStepDeltaPeak cliMaxDirPathBytes cliMaxAddrTextBytes))
      (max cliRealDirectRunMaxReq_i
        (max 1024 (m5DirStepMaxReq cliMaxDirPathBytes cliMaxAddrTextBytes))) := by
    have hi_g : CliPqxdhInputs W w.g.i := w.g_i.symm ▸ hi
    obtain ⟨h1_cum, h1_req⟩ := existentialRealCalleeFineSpecs_binaryRunCum_bound img S hi_g w.parse_ok
    obtain ⟨_, h2, h3, _, _⟩ :=
      existentialRealCalleeFineSpecs_direct_run_bounds img S hi_g w.parse_ok
    have hrun :=
      (cliRunBinaryEnv_real_1MiB_fine_phaseCredit_of_cliPqInputs
        (existentialRealCalleeFineSpecs img S hi_g w.parse_ok) hi_g w.stdin_le
        w.parse_ok).mono h1_cum h2 h3 h1_req
    refine (hrun.seq ((m5Phase_Bounded_phaseCredit_fine w.dirs_sum_le
      w.dirs_bounds).seq (m6_phaseCredit_small1024 fineCostModel_modelHyps hsm1024 w.ok))).mono
      ?_ ?_ ?_ ?_
    · rw [Nat.add_assoc]; exact Nat.le_refl _
    · simp only [Nat.add_zero]; exact Nat.le_refl _
    · exact Nat.max_le.mpr ⟨Nat.le_max_left _ _,
        Nat.le_trans (Nat.add_le_add_left
          (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.zero_le _⟩) _) (Nat.le_max_right _ _)⟩
    · exact Nat.max_le.mpr ⟨Nat.le_max_left _ _,
        Nat.le_trans (Nat.le_of_eq (Nat.max_comm _ _)) (Nat.le_max_right _ _)⟩
  have hex : PhaseCreditSpec fineCostModel
      (fun evs' => ∃ w : ValidPostSetupWitness i, w.g.i = i ∧
        SeqEnv (CliRunBinaryEnv cliIo.rd (mkExistentialRealCalleeEnvs img S W w.g)
            sessionCapBytes w.g)
          (SeqEnv (M5PhaseEnv w.dirs) (M6Env w.ok)) evs')
      (cliRealDirectRunCum_i + cliMaxDirtyEntries *
        (10 * max (4 * cliMaxDirPathBytes + cliMaxAddrTextBytes + 16) 16 + 4 * 9539) + m6DeltaCum)
      cliRealDirectRunLive_i
      (max cliRealDirectRunPeak_i
        (cliRealDirectRunLive_i + m5DirStepDeltaPeak cliMaxDirPathBytes cliMaxAddrTextBytes))
      (max cliRealDirectRunMaxReq_i
        (max 1024 (m5DirStepMaxReq cliMaxDirPathBytes cliMaxAddrTextBytes))) :=
    { req_align := fun evs ⟨w, _, hseq⟩ ev hev => (hw w).req_align evs hseq ev hev
      credit_le := fun st0 {_} ⟨w, _, hseq⟩ => (hw w).credit_le st0 hseq }
  have htail := optStage_phaseCredit hex
  refine ((cliMainBoundedSetup_phaseCredit_fine (argv_length_le_of_cliPqInputs hi)).seq htail).mono
    ?_ ?_ ?_ ?_
  · unfold cliMainWidenedCumOf; simp only [Nat.add_assoc]; exact Nat.le_refl _
  · unfold cliMainTightLiveOf cliMainDeltaLive_tight; exact Nat.le_refl _
  · unfold cliMainTightPeakOf cliMainDeltaPeak_tight; exact Nat.le_refl _
  · unfold cliMainTightReqOf cliMainMaxReq
    have h16k : max 16384 (m3PhaseMaxReq msgCapBytes sessionCapBytes) =
        m3PhaseMaxReq msgCapBytes sessionCapBytes := by
      unfold m3PhaseMaxReq msgCapBytes sessionCapBytes; decide
    rw [h16k]

/-- Concrete `PhaseGroupSpec fineCostModel` on `RealCliMainBinaryEnvOf (mkExistentialRealCalleeEnvs img S W) i`. -/
theorem realCliMainBinaryEnvOf_fine_groupSpec_concrete [LibsignalPlacement]
    (img : Arm64.Obj.Image) (S : RunSem) {W : PEParams} {i : Inputs}
    (hi : CliPqxdhInputs W i) :
    PhaseGroupSpec fineCostModel
      (RealCliMainBinaryEnvOf (mkExistentialRealCalleeEnvs img S W) i)
      (cliMainWidenedGrpSOf cliRealBinaryDirectRunGrpS_i) := by
  have hex : PhaseGroupSpec fineCostModel
      (fun evs' => ∃ w : ValidPostSetupWitness i, w.g.i = i ∧
        SeqEnv (CliRunBinaryEnv cliIo.rd (mkExistentialRealCalleeEnvs img S W w.g)
            sessionCapBytes w.g)
          (SeqEnv (M5PhaseEnv w.dirs) (M6Env w.ok)) evs')
      (cliRealBinaryDirectRunGrpS_i + cliMaxDirtyEntries * (12 * FineScale) + 3 * FineScale) :=
    { groups_le := fun st0 {_} ⟨w, _, hseq⟩ => by
        have hi_g : CliPqxdhInputs W w.g.i := w.g_i.symm ▸ hi
        have hrun := cliRunBinaryEnv_existential_fine_groupSpec img S hi_g w.stdin_le w.parse_ok
        have hm5 := (m5PhaseEnv_groupSpec fineCostModel w.dirs).mono
          (Nat.mul_le_mul_right (12 * FineScale) w.dirs_sum_le)
        have htot : PhaseGroupSpec fineCostModel
            (SeqEnv (CliRunBinaryEnv cliIo.rd (mkExistentialRealCalleeEnvs img S W w.g)
                sessionCapBytes w.g)
              (SeqEnv (M5PhaseEnv w.dirs) (M6Env w.ok)))
            (cliRealBinaryDirectRunGrpS_i + cliMaxDirtyEntries * (12 * FineScale) + 3 * FineScale) :=
          (hrun.seq (hm5.seq (m6Env_groupSpec fineCostModel w.ok))).mono
            (by generalize FineScale = fs; omega)
        exact htot.groups_le st0 hseq }
  have htail := optStage_groupSpec hex
  exact ((cliMainBoundedSetup_fine_groupSpec (argv_length_le_of_cliPqInputs hi)).seq htail).mono
    (by unfold cliMainWidenedGrpSOf; generalize FineScale = fs; omega)

/-- `< 90%` (`965,750,441 ≤ 966,367,641` B) whole-`main` `FitsTrace fineCostModel` on `RealCliMainBinaryEnvOf`. -/
theorem realCliMainBinaryEnvOf_90pct_fitsTrace_concrete [LibsignalPlacement]
    {lim : BudgetLimits}
    (henf : lim.enforced = true)
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes)
    (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap90 : cliRealNinetyPctOneGiB ≤ lim.physCap)
    (img : Arm64.Obj.Image) (S : RunSem) (W : PEParams)
    {i : Inputs} (hi : CliPqxdhInputs W i)
    {fullLog : List AllocEvent}
    (hEnv : RealCliMainBinaryEnvOf (mkExistentialRealCalleeEnvs img S W) i fullLog) :
    FitsTrace fineCostModel lim cliRealBinaryDirectMainStepReserve_i fullLog := by
  obtain ⟨hlp, hram, hva⟩ := realCliMainBinaryEnvOf_90pct_bounds_direct hsb hsc hcap90
  exact fitsTrace_fineCostModel_of_group_literal_bounds
    (realCliMainBinaryEnvOf_phaseCredit_fine_concrete img S hi)
    (realCliMainBinaryEnvOf_fine_groupSpec_concrete img S hi)
    (Nat.le_refl _) hlp (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) henf hram hva hEnv

/-- `< 90%` (`965,750,441 ≤ 966,367,641` B) whole-`main` `FitsEnv fineCostModel` on `RealCliMainBinaryEnvOf`. -/
theorem realCliMainBinaryEnvOf_90pct_fitsEnv_concrete [LibsignalPlacement]
    {lim : BudgetLimits}
    (henf : lim.enforced = true)
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes)
    (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap90 : cliRealNinetyPctOneGiB ≤ lim.physCap)
    (img : Arm64.Obj.Image) (S : RunSem) (W : PEParams) :
    ∀ i : Inputs, CliPqxdhInputs W i →
      FitsEnv fineCostModel lim fineCostModel.init
        (RealCliMainBinaryEnvOf (mkExistentialRealCalleeEnvs img S W) i) := by
  intro i hi
  obtain ⟨hlp, hram, hva⟩ := realCliMainBinaryEnvOf_90pct_bounds_direct hsb hsc hcap90
  exact fitsEnv_fineCostModel_of_group_literal_bounds
    (realCliMainBinaryEnvOf_phaseCredit_fine_concrete img S hi)
    (realCliMainBinaryEnvOf_fine_groupSpec_concrete img S hi)
    (Nat.le_refl _) hlp (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) henf hram hva

/-- `≤ 1 GiB` whole-`main` `FitsEnv fineCostModel` on `RealCliMainBinaryEnvOf`. -/
theorem realCliMainBinaryEnvOf_fitsEnv_concrete [LibsignalPlacement]
    {lim : BudgetLimits}
    (henf : lim.enforced = true)
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes)
    (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap1G : cliOneGiB ≤ lim.physCap)
    (img : Arm64.Obj.Image) (S : RunSem) (W : PEParams) :
    ∀ i : Inputs, CliPqxdhInputs W i →
      FitsEnv fineCostModel lim fineCostModel.init
        (RealCliMainBinaryEnvOf (mkExistentialRealCalleeEnvs img S W) i) :=
  realCliMainBinaryEnvOf_90pct_fitsEnv_concrete henf hsb hsc
    (Nat.le_trans (by unfold cliRealNinetyPctOneGiB cliOneGiB; decide) hcap1G) img S W

/-- `cliBudgetLimits` (`1 GiB`) whole-`main` `FitsEnv fineCostModel` on `RealCliMainBinaryEnvOf`. -/
theorem realCliMainBinaryEnvOf_fitsEnv_cliBudgetLimits_concrete [LibsignalPlacement]
    (img : Arm64.Obj.Image) (S : RunSem) (W : PEParams) :
    ∀ i : Inputs, CliPqxdhInputs W i →
      FitsEnv fineCostModel cliBudgetLimits fineCostModel.init
        (RealCliMainBinaryEnvOf (mkExistentialRealCalleeEnvs img S W) i) :=
  realCliMainBinaryEnvOf_90pct_fitsEnv_concrete rfl (Nat.le_refl _) (Nat.le_refl _)
    (by unfold cliBudgetLimits cliRealNinetyPctOneGiB cliOneGiB; decide) img S W

/-- Suffix-splitting helper extracting `FitsEnv M lim (M.stepEvents evs₁ M.init) P` from any
whole-`main` `FitsEnv M lim M.init (RealCliMainBinaryEnvOf E i)`. -/
theorem fitsEnv_suffix_of_realCliMainBinaryEnvOf {M : AllocCostModel} {lim : BudgetLimits}
    {E : RunCall → CliRunCalleeEnvs} {i : Inputs} {evs₁ : List AllocEvent}
    {P : List AllocEvent → Prop}
    (hMain : FitsEnv M lim M.init (RealCliMainBinaryEnvOf E i))
    (hsub : ∀ evs₂, P evs₂ → RealCliMainBinaryEnvOf E i (evs₁ ++ evs₂)) :
    FitsEnv M lim (M.stepEvents evs₁ M.init) P :=
  fun evs₂ hp =>
    ((fitsEvents_append M lim evs₁ evs₂ M.init).mp (hMain (evs₁ ++ evs₂) (hsub evs₂ hp))).2

/-- `CliRunBinaryEnv` is closed under right-appending `FreeOnlyEvs`. -/
theorem cliRunBinaryEnv_append_freeOnly {rd : ReadRule} {E : CliRunCalleeEnvs}
    {wireOutCap : Nat} {g : RunCall} {e₁ ef : List AllocEvent}
    (h₁ : CliRunBinaryEnv rd E wireOutCap g e₁) (hf : FreeOnlyEvs ef) :
    CliRunBinaryEnv rd E wireOutCap g (e₁ ++ ef) := by
  rcases h₁ with hf0 | hr0 | ⟨e0, eaj, rfl, he0, haj⟩
  · exact Or.inl (freeOnlyEvs_append hf0 hf)
  · have hnil : RunArmBinaryEnv rd (runFiles g.i) E wireOutCap g.i.stdin g.c [] :=
      runArmEnv_sub_runArmBinaryEnv
        (CliRunArmsPeak.runArmEnv_nil rd (runFiles g.i) E wireOutCap g.i.stdin g.c)
    exact Or.inr (Or.inr ⟨e₁, ef, rfl, hr0, Or.inr ⟨[], ef, rfl, hnil, hf⟩⟩)
  · refine Or.inr (Or.inr ⟨e0, eaj ++ ef, List.append_assoc e0 eaj ef, he0, ?_⟩)
    rcases haj with ha | ⟨ea, ej, rfl, ha, hj⟩
    · exact Or.inr ⟨eaj, ef, rfl, ha, hf⟩
    · exact Or.inr ⟨ea, ej ++ ef, List.append_assoc ea ej ef, ha, freeOnlyEvs_append hj hf⟩

theorem realCliMainBinaryEnvOf_of_setup (E : RunCall → CliRunCalleeEnvs) {i : Inputs}
    {evs : List AllocEvent} (h : CliMainBoundedSetupEnv i.argv.length evs) :
    RealCliMainBinaryEnvOf E i evs :=
  Or.inl h

theorem realCliMainBinaryEnvOf_of_setup_freeOnly (E : RunCall → CliRunCalleeEnvs) {i : Inputs}
    {eSetup ef : List AllocEvent}
    (hSetup : CliMainBoundedSetupEnv i.argv.length eSetup) (hf : FreeOnlyEvs ef) :
    RealCliMainBinaryEnvOf E i (eSetup ++ ef) :=
  Or.inr ⟨eSetup, ef, rfl, hSetup, Or.inl hf⟩

theorem realCliMainBinaryEnvOf_of_setup_run {E : RunCall → CliRunCalleeEnvs} {i : Inputs}
    (w : ValidPostSetupWitness i) (hgi : w.g.i = i)
    {eSetup eRun : List AllocEvent}
    (hSetup : CliMainBoundedSetupEnv i.argv.length eSetup)
    (hRun : CliRunBinaryEnv cliIo.rd (E w.g) sessionCapBytes w.g eRun) :
    RealCliMainBinaryEnvOf E i (eSetup ++ eRun) :=
  Or.inr ⟨eSetup, eRun, rfl, hSetup, Or.inr ⟨w, hgi, Or.inl hRun⟩⟩

theorem realCliMainBinaryEnvOf_of_setup_run_m5m6 {E : RunCall → CliRunCalleeEnvs} {i : Inputs}
    (w : ValidPostSetupWitness i) (hgi : w.g.i = i)
    {eSetup eRun eTail : List AllocEvent}
    (hSetup : CliMainBoundedSetupEnv i.argv.length eSetup)
    (hRun : CliRunBinaryEnv cliIo.rd (E w.g) sessionCapBytes w.g eRun)
    (hTail : SeqEnv (M5PhaseEnv w.dirs) (M6Env w.ok) eTail) :
    RealCliMainBinaryEnvOf E i (eSetup ++ (eRun ++ eTail)) :=
  Or.inr ⟨eSetup, eRun ++ eTail, rfl, hSetup, Or.inr ⟨w, hgi, Or.inr ⟨eRun, eTail, rfl, hRun, hTail⟩⟩⟩

/-! ## 5. Parametric `RunOkPlacedBudget.RunEnv` → `CliRunBinaryEnv` Bridge (`runEnv_to_cliRunBinaryEnv_of_slots`) -/

abbrev PubBundleReadEnv (rd : ReadRule)
    (PathEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop) :=
  LibsignalBinary.Proofs.SignalSession.Cli.Pub.BundleRead.PlacedBudgetAux.BundleReadEnv
    rd PathEnv (ReadEnv := ReadEnv)
abbrev PubSplitIdEnv :=
  LibsignalBinary.Proofs.SignalSession.Cli.Pub.SplitId.PlacedBudget.SplitIdEnv
abbrev PubSplitSignedEnv :=
  LibsignalBinary.Proofs.SignalSession.Cli.Pub.SplitSigned.PlacedBudgetAux.SplitSignedEnv

/-- Concrete non-slot callee allocation-event envelopes on `signal_session::run` (Block `579`)
parameterized by `ReadEnv` (definitionally equal to `AllPlacedBudget.cliRunCalleesEnvs`, avoiding
`AllPlacedBudget` import). -/
def cliRunCalleesEnvs
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop :=
      ReadFileRuleEnv cliIo.rd) : RunCalleesEnvs where
  readFile := ReadEnv
  dirGet := DirGetEnv PathEnv ReadEnv cliIo.rd
  bundleRead := PubBundleReadEnv cliIo.rd PathEnv ReadEnv
  splitId := PubSplitIdEnv
  splitSigned := PubSplitSignedEnv PubSplitIdEnv

/-- Concrete arm allocation-event envelopes on `signal_session::run` (Block `579`) over `cEnvs`,
`sEnvs`, `PksmTryFromEnv`, and `S` (definitionally equal to `AllPlacedBudget.cliRunArmEnvs` /
`MainInstAllPlacedBudgetSeams.cliMainArmEnvs`). -/
def cliMainArmEnvs (cEnvs : RunCalleesEnvs) (sEnvs : RunSlotEnvs)
    (PksmTryFromEnv : PksmGhost → List AllocEvent → Prop) (S : RunSem) : RunArmEnvs where
  pre := PreEnv cEnvs
  init1 := Init1Env cEnvs
  init2 := Init2Env cEnvs
  init3 := R1cInit3Env sEnvs
  send := R2SendEnv sEnvs S
  recvW := R3aRecvWEnv sEnvs
  pksmTryFrom := PksmTryFromEnv
  recvP := R3bRecvPEnv S sEnvs PksmTryFromEnv

abbrev cliRunArmEnvs := cliMainArmEnvs

/-- Canonical `PreEnv` (`R0ProofPlacedBudget`) containment in `R0BinaryEnv`. -/
theorem preEnv_sub_r0BinaryEnv {cEnvs : RunCalleesEnvs} {rd : ReadRule}
    (hdir : cEnvs.dirGet = DirGetEnv PathEnv (ReadFileRuleEnv rd) rd)
    (g : RunCall) {evs : List AllocEvent}
    (h : PreEnv cEnvs g evs) :
    R0BinaryEnv rd g evs := by
  unfold PreEnv at h
  rw [hdir] at h
  exact Or.inr h

theorem splitIdEnv_append_freeOnly {file : List (BitVec 8)} {e₁ ef : List AllocEvent}
    (h₁ : SplitIdEnv file e₁) (hf : FreeOnlyEvs ef) :
    SplitIdEnv file (e₁ ++ ef) := by
  rcases h₁ with he₁ | ⟨ea, ef0, rfl, ha, hf0⟩
  · exact Or.inr ⟨e₁, ef, rfl, he₁, hf⟩
  · exact Or.inr ⟨ea, ef0 ++ ef, List.append_assoc ea ef0 ef, ha, freeOnlyEvs_append hf0 hf⟩

theorem splitSignedEnv_append_freeOnly {file : List (BitVec 8)} {e₁ ef : List AllocEvent}
    (h₁ : SplitSignedEnv file e₁) (hf : FreeOnlyEvs ef) :
    SplitSignedEnv file (e₁ ++ ef) := by
  rcases h₁ with hs1 | ⟨ea, eb, rfl, ha, hb⟩
  · exact Or.inr ⟨e₁, ef, rfl, hs1, Or.inl hf⟩
  · refine Or.inr ⟨ea, eb ++ ef, List.append_assoc ea eb ef, ha, ?_⟩
    rcases hb with hfb | hsb
    · exact Or.inl (freeOnlyEvs_append hfb hf)
    · exact Or.inr (splitIdEnv_append_freeOnly (file := file) hsb hf)

theorem r1bFileStepEnv_append_freeOnly {rd : ReadRule} {files : FsFiles}
    {dir name : List (BitVec 8)} {e₁ ef : List AllocEvent}
    (h₁ : R1bFileStepEnv rd files dir name e₁) (hf : FreeOnlyEvs ef) :
    R1bFileStepEnv rd files dir name (e₁ ++ ef) := by
  rcases h₁ with hp | ⟨ep, er, rfl, hp, hr⟩
  · exact Or.inr ⟨e₁, ef, rfl, hp, Or.inl (Or.inl hf)⟩
  · refine Or.inr ⟨ep, er ++ ef, List.append_assoc ep er ef, hp, ?_⟩
    rcases hr with hr0 | ⟨er0, et, rfl, hr0, ht⟩
    · exact Or.inr ⟨er, ef, rfl, hr0, Or.inl hf⟩
    · refine Or.inr ⟨er0, et ++ ef, List.append_assoc er0 et ef, hr0, ?_⟩
      rcases ht with hft | ⟨ef0, eu, rfl, hf0, hu⟩
      · exact Or.inl (freeOnlyEvs_append hft hf)
      · refine Or.inr ⟨ef0, eu ++ ef, List.append_assoc ef0 eu ef, hf0, ?_⟩
        rcases hu with hfu | hv
        · exact Or.inl (freeOnlyEvs_append hfu hf)
        · refine Or.inr ?_
          rcases hv with ha | ⟨ea, ef1, rfl, ha, hf1⟩
          · exact Or.inr ⟨eu, ef, rfl, ha, hf⟩
          · exact Or.inr ⟨ea, ef1 ++ ef, List.append_assoc ea ef1 ef, ha,
              freeOnlyEvs_append hf1 hf⟩

theorem pubSplitIdEnv_sub_splitIdEnv {file : List (BitVec 8)} {evs : List AllocEvent}
    (h : PubSplitIdEnv file evs) :
    SplitIdEnv [] evs := by
  unfold PubSplitIdEnv
    LibsignalBinary.Proofs.SignalSession.Cli.Pub.SplitId.PlacedBudget.SplitIdEnv at h
  unfold SplitIdEnv
  split at h
  · exact Or.inl h
  · exact h

theorem pubSplitSignedEnv_sub_splitSignedEnv {file : List (BitVec 8)} {evs : List AllocEvent}
    (h : PubSplitSignedEnv PubSplitIdEnv file evs) :
    SplitSignedEnv [] evs := by
  rcases h with h1 | ⟨e1, e2, rfl, h1, h2⟩
  · exact Or.inl (pubSplitIdEnv_sub_splitIdEnv h1)
  · refine Or.inr ⟨e1, e2, rfl, pubSplitIdEnv_sub_splitIdEnv h1, ?_⟩
    unfold SplitSignedTailEnv at h2
    cases hsid : splitId file with
    | none =>
      rw [hsid] at h2
      subst h2
      exact Or.inl (fun _ hm => nomatch hm)
    | some p =>
      rw [hsid] at h2
      dsimp only at h2
      split at h2
      · exact Or.inr (Or.inl h2)
      · exact Or.inr h2

theorem bundleReadEnv_sub_r1bFileStepEnv {rd : ReadRule} {files : FsFiles}
    {dir name : List (BitVec 8)} {evs : List AllocEvent}
    (h : PubBundleReadEnv rd PathEnv (ReadFileRuleEnv rd) files dir name evs) :
    R1bFileStepEnv rd files dir name evs := by
  have hnil : FreeOnlyEvs [] := fun _ hm => nomatch hm
  rcases h with hp | ⟨ep, et, rfl, hp, ht⟩
  · exact Or.inl (Or.inr hp)
  · rcases ht with hr | ⟨er, ea, rfl, hr, ha⟩
    · exact Or.inr ⟨ep, et, rfl, Or.inr hp, Or.inl (Or.inr hr)⟩
    · refine Or.inr ⟨ep, er ++ ea, rfl, Or.inr hp,
        Or.inr ⟨er, ea, rfl, Or.inr hr, ?_⟩⟩
      unfold BundleReadAfterReadEnv at ha
      cases hrd : rd files (dir ++ [0x2f#8] ++ name) with
      | ok _ =>
        rw [hrd] at ha
        exact Or.inl ha
      | error _ =>
        rw [hrd] at ha
        exact Or.inr ⟨[], ea, rfl, hnil,
          Or.inr (seqEnv_mono (fun _ he => Or.inl he) (fun _ hf => hf) ha)⟩

private theorem rawRead_sub_r1bFileStepEnv {rd : ReadRule} {files : FsFiles}
    {dir name : List (BitVec 8)} {evs : List AllocEvent}
    (h : SeqEnv (PathEnv dir name) (ReadFileRuleEnv rd files (dir ++ [0x2f#8] ++ name)) evs) :
    R1bFileStepEnv rd files dir name evs := by
  rcases h with hp | ⟨ep, er, rfl, hp, hr⟩
  · exact Or.inl (Or.inr hp)
  · exact Or.inr ⟨ep, er, rfl, Or.inr hp, Or.inl (Or.inr hr)⟩

private theorem rawReadFree_sub_r1bFileStepEnv {rd : ReadRule} {files : FsFiles}
    {dir name : List (BitVec 8)} {evs : List AllocEvent}
    (h : SeqEnv (SeqEnv (PathEnv dir name) (ReadFileRuleEnv rd files (dir ++ [0x2f#8] ++ name)))
      FreeOnlyEvs evs) :
    R1bFileStepEnv rd files dir name evs := by
  rcases h with hpr | ⟨epr, ef, rfl, hpr, hf⟩
  · exact rawRead_sub_r1bFileStepEnv hpr
  · exact r1bFileStepEnv_append_freeOnly (rawRead_sub_r1bFileStepEnv hpr) hf

private theorem rawReadFree_append_err_sub_r1bFileStepEnv {rd : ReadRule} {files : FsFiles}
    {dir name : List (BitVec 8)} {evs : List AllocEvent}
    (h : SeqEnv
      (SeqEnv (SeqEnv (PathEnv dir name) (ReadFileRuleEnv rd files (dir ++ [0x2f#8] ++ name)))
        FreeOnlyEvs)
      (SeqEnv (fun e => e = rustAllocEvents 22 1 ∨ e = rustAllocEvents 14 1) FreeOnlyEvs) evs) :
    R1bFileStepEnv rd files dir name evs := by
  have hnil : FreeOnlyEvs [] := fun _ hm => nomatch hm
  rcases h with hrf | ⟨erf, ee, rfl, hrf, hee⟩
  · exact rawReadFree_sub_r1bFileStepEnv hrf
  · rcases hrf with hpr | ⟨epr, ef, rfl, hpr, hf⟩
    · rcases hpr with hp | ⟨ep, er, rfl, hp, hr⟩
      · exact Or.inr ⟨erf, ee, rfl, Or.inr hp,
          Or.inr ⟨[], ee, rfl, Or.inl hnil, Or.inr ⟨[], ee, rfl, hnil, Or.inr hee⟩⟩⟩
      · exact Or.inr ⟨ep, er ++ ee, List.append_assoc ep er ee, Or.inr hp,
          Or.inr ⟨er, ee, rfl, Or.inr hr, Or.inr ⟨[], ee, rfl, hnil, Or.inr hee⟩⟩⟩
    · rcases hpr with hp | ⟨ep, er, rfl, hp, hr⟩
      · exact Or.inr ⟨epr, ef ++ ee, List.append_assoc epr ef ee, Or.inr hp,
          Or.inr ⟨[], ef ++ ee, rfl, Or.inl hnil, Or.inr ⟨ef, ee, rfl, hf, Or.inr hee⟩⟩⟩
      · rw [List.append_assoc ep er ef, List.append_assoc ep (er ++ ef) ee,
          List.append_assoc er ef ee]
        exact Or.inr ⟨ep, er ++ (ef ++ ee), rfl, Or.inr hp,
          Or.inr ⟨er, ef ++ ee, rfl, Or.inr hr, Or.inr ⟨ef, ee, rfl, hf, Or.inr hee⟩⟩⟩

theorem init2Stage4Env_sub_r1bDeserStageEnv {spkKey kpkKey : List (BitVec 8)}
    {evs : List AllocEvent}
    (h : Init2Stage4Env spkKey kpkKey evs) :
    OptStageEnv R1bDeserStageEnv evs := by
  have hkem : OptStageEnv (· = rustAllocEvents kemPkLen 1) (kemDeserializeEvents kpkKey) := by
    unfold kemDeserializeEvents
    split
    · exact Or.inr rfl
    · exact Or.inl (fun _ hm => nomatch hm)
  unfold Init2Stage4Env at h
  cases hspk : PublicKey.deserialize spkKey with
  | error _ =>
    rw [hspk] at h
    exact Or.inl h
  | ok _ =>
    rw [hspk] at h
    rcases h with rfl | rfl | h3
    · exact Or.inr (Or.inl (Or.inr rfl))
    · exact Or.inr (Or.inr ⟨_, _, rfl, Or.inr rfl, Or.inl hkem⟩)
    · split at h3
      · rcases h3 with he1 | ⟨e1, ef, rfl, he1, hf⟩
        · unfold R1bDeserCloneOkEnv at he1
          rw [he1, List.append_assoc]
          exact Or.inr (Or.inr ⟨_, _, rfl, Or.inr rfl,
            Or.inr ⟨_, _, rfl, hkem, Or.inr (Or.inl rfl)⟩⟩)
        · unfold R1bDeserCloneOkEnv at he1
          rw [he1, List.append_assoc, List.append_assoc]
          exact Or.inr (Or.inr ⟨_, _, rfl, Or.inr rfl,
            Or.inr ⟨_, _, rfl, hkem, Or.inr (Or.inr ⟨_, ef, rfl, rfl, hf⟩)⟩⟩)
      · unfold R1bDeserCloneErrEnv at h3
        rw [hspk] at h3
        dsimp only at h3
        split at h3
        · exact False.elim h3
        · rcases h3 with he1 | ⟨e1, ef, rfl, he1, hf⟩
          · rw [he1]
            exact Or.inr (Or.inr ⟨_, _, rfl, Or.inr rfl, Or.inl hkem⟩)
          · rw [he1, List.append_assoc]
            exact Or.inr (Or.inr ⟨_, _, rfl, Or.inr rfl, Or.inr ⟨_, ef, rfl, hkem, Or.inl hf⟩⟩)

private abbrev R1bTail3 (rd : ReadRule) (files : FsFiles) (dir : List (BitVec 8)) :
    List AllocEvent → Prop :=
  SeqEnv (OptStageEnv (R1bFileStepEnv rd files dir (utf8 "one-time-pre-key")))
    (SeqEnv (OptStageEnv (SplitIdEnv [])) (OptStageEnv R1bDeserStageEnv))

private abbrev R1bTail2 (rd : ReadRule) (files : FsFiles) (dir : List (BitVec 8)) :
    List AllocEvent → Prop :=
  SeqEnv (OptStageEnv (R1bFileStepEnv rd files dir (utf8 "kyber-pre-key")))
    (SeqEnv (OptStageEnv (SplitSignedEnv [])) (R1bTail3 rd files dir))

private abbrev R1bTail1 (rd : ReadRule) (files : FsFiles) (dir : List (BitVec 8)) :
    List AllocEvent → Prop :=
  SeqEnv (OptStageEnv (R1bFileStepEnv rd files dir (utf8 "signed-pre-key")))
    (SeqEnv (OptStageEnv (SplitSignedEnv [])) (R1bTail2 rd files dir))

private theorem init2Stage3Env_sub_r1bTail3 {cEnvs : RunCalleesEnvs}
    (hbundle : cEnvs.bundleRead = PubBundleReadEnv cliIo.rd PathEnv (ReadFileRuleEnv cliIo.rd))
    (hsid : cEnvs.splitId = PubSplitIdEnv)
    {files : FsFiles} {dir spkKey kpkKey : List (BitVec 8)} {evs : List AllocEvent}
    (h : Init2Stage3Env cEnvs files dir spkKey kpkKey evs) :
    R1bTail3 cliIo.rd files dir evs := by
  have hnil : FreeOnlyEvs [] := fun _ hm => nomatch hm
  have hbSub : ∀ {e}, cEnvs.bundleRead files dir (utf8 "one-time-pre-key") e →
      R1bFileStepEnv cliIo.rd files dir (utf8 "one-time-pre-key") e := by
    intro e he; rw [hbundle] at he; exact bundleReadEnv_sub_r1bFileStepEnv he
  have hsidSub : ∀ {b e}, cEnvs.splitId b e → SplitIdEnv [] e := by
    intro b e he; rw [hsid] at he; exact pubSplitIdEnv_sub_splitIdEnv he
  have hopkSplitFree : ∀ {b} {e},
      SeqEnv (SeqEnv (cEnvs.bundleRead files dir (utf8 "one-time-pre-key")) (cEnvs.splitId b))
        FreeOnlyEvs e →
      R1bTail3 cliIo.rd files dir e := by
    intro b e hs0
    rcases hs0 with hs | ⟨ebs, ef, rfl, hs, hf⟩
    · rcases hs with hb | ⟨eb, es, rfl, hb, hsi⟩
      · exact Or.inl (Or.inr (hbSub hb))
      · exact Or.inr ⟨eb, es, rfl, Or.inr (hbSub hb), Or.inl (Or.inr (hsidSub hsi))⟩
    · rcases hs with hb | ⟨eb, es, rfl, hb, hsi⟩
      · exact Or.inl (Or.inr (r1bFileStepEnv_append_freeOnly (hbSub hb) hf))
      · exact Or.inr ⟨eb, es ++ ef, List.append_assoc eb es ef, Or.inr (hbSub hb),
          Or.inl (Or.inr (splitIdEnv_append_freeOnly (hsidSub hsi) hf))⟩
  rcases h with hb | herr | hm
  · exact Or.inl (Or.inr (hbSub hb))
  · unfold R1bStepOpkErrEnv at herr
    cases hrd : cliIo.rd files (dir ++ [0x2f#8] ++ utf8 "one-time-pre-key") with
    | error _ =>
      rw [hrd] at herr
      rcases herr with hb | ⟨eb, ef, rfl, hb, hf⟩
      · exact Or.inl (Or.inr (hbSub hb))
      · exact Or.inl (Or.inr (r1bFileStepEnv_append_freeOnly (hbSub hb) hf))
    | ok opkBs =>
      rw [hrd] at herr
      cases opkBs with
      | nil => exact False.elim herr
      | cons b bs =>
        dsimp only at herr
        cases hsp : splitId (b :: bs) with
        | none =>
          rw [hsp] at herr
          exact hopkSplitFree herr
        | some p =>
          rw [hsp] at herr
          dsimp only at herr
          split at herr
          · exact hopkSplitFree herr
          · exact False.elim herr
  · cases hrd : cliIo.rd files (dir ++ [0x2f#8] ++ utf8 "one-time-pre-key") with
    | error _ =>
      rw [hrd] at hm
      exact False.elim hm
    | ok opkBs =>
      rw [hrd] at hm
      cases opkBs with
      | nil =>
        have hokNil : ∀ {e}, R1bStepOpkOkEnv cEnvs files dir [] e →
            R1bFileStepEnv cliIo.rd files dir (utf8 "one-time-pre-key") e := by
          intro e he
          unfold R1bStepOpkOkEnv at he
          simp only [List.isEmpty_nil, ↓reduceIte] at he
          rcases he with hb | ⟨eb, ef, rfl, hb, hf⟩
          · exact hbSub hb
          · exact r1bFileStepEnv_append_freeOnly (hbSub hb) hf
        rcases hm with hok | ⟨eok, e4, rfl, hok, h4⟩
        · exact Or.inl (Or.inr (hokNil hok))
        · exact Or.inr ⟨eok, e4, rfl, Or.inr (hokNil hok),
            Or.inr ⟨[], e4, rfl, Or.inl hnil, init2Stage4Env_sub_r1bDeserStageEnv h4⟩⟩
      | cons b bs =>
        rcases hm with hbs | hm2
        · exact hopkSplitFree (Or.inl hbs)
        · split at hm2
          · exact False.elim hm2
          · split at hm2
            · exact False.elim hm2
            · unfold R1bStepOpkOkEnv at hm2
              simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at hm2
              rcases hm2 with hok | ⟨eok, e4, rfl, hok, h4⟩
              · exact hopkSplitFree hok
              · have h4' := init2Stage4Env_sub_r1bDeserStageEnv h4
                rcases hok with hs | ⟨ebs, ef, rfl, hs, hf⟩
                · rcases hs with hb | ⟨eb, es, rfl, hb, hsi⟩
                  · exact Or.inr ⟨eok, e4, rfl, Or.inr (hbSub hb),
                      Or.inr ⟨[], e4, rfl, Or.inl hnil, h4'⟩⟩
                  · exact Or.inr ⟨eb, es ++ e4, List.append_assoc eb es e4, Or.inr (hbSub hb),
                      Or.inr ⟨es, e4, rfl, Or.inr (hsidSub hsi), h4'⟩⟩
                · rcases hs with hb | ⟨eb, es, rfl, hb, hsi⟩
                  · exact Or.inr ⟨ebs ++ ef, e4, rfl,
                      Or.inr (r1bFileStepEnv_append_freeOnly (hbSub hb) hf),
                      Or.inr ⟨[], e4, rfl, Or.inl hnil, h4'⟩⟩
                  · rw [List.append_assoc eb es ef, List.append_assoc eb (es ++ ef) e4]
                    exact Or.inr ⟨eb, (es ++ ef) ++ e4, rfl, Or.inr (hbSub hb),
                      Or.inr ⟨es ++ ef, e4, rfl,
                        Or.inr (splitIdEnv_append_freeOnly (hsidSub hsi) hf), h4'⟩⟩

private theorem init2Stage2Env_sub_r1bTail2 {cEnvs : RunCalleesEnvs}
    (hbundle : cEnvs.bundleRead = PubBundleReadEnv cliIo.rd PathEnv (ReadFileRuleEnv cliIo.rd))
    (hsid : cEnvs.splitId = PubSplitIdEnv)
    (hssg : cEnvs.splitSigned = PubSplitSignedEnv PubSplitIdEnv)
    {files : FsFiles} {dir spkKey : List (BitVec 8)} {evs : List AllocEvent}
    (h : Init2Stage2Env cEnvs files dir spkKey evs) :
    R1bTail2 cliIo.rd files dir evs := by
  have hnil : FreeOnlyEvs [] := fun _ hm => nomatch hm
  have hbSub : ∀ {e}, cEnvs.bundleRead files dir (utf8 "kyber-pre-key") e →
      R1bFileStepEnv cliIo.rd files dir (utf8 "kyber-pre-key") e := by
    intro e he; rw [hbundle] at he; exact bundleReadEnv_sub_r1bFileStepEnv he
  have hssgSub : ∀ {b e}, cEnvs.splitSigned b e → SplitSignedEnv [] e := by
    intro b e he; rw [hssg] at he; exact pubSplitSignedEnv_sub_splitSignedEnv he
  have hkpkFree : ∀ {b e}, SeqEnv (R1bStepKpkOkEnv cEnvs files dir b) FreeOnlyEvs e →
      R1bTail2 cliIo.rd files dir e := by
    intro b e hs0
    rcases hs0 with hs | ⟨ebs, ef, rfl, hs, hf⟩
    · rcases hs with hb | ⟨eb, es, rfl, hb, hss⟩
      · exact Or.inl (Or.inr (hbSub hb))
      · exact Or.inr ⟨eb, es, rfl, Or.inr (hbSub hb), Or.inl (Or.inr (hssgSub hss))⟩
    · rcases hs with hb | ⟨eb, es, rfl, hb, hss⟩
      · exact Or.inl (Or.inr (r1bFileStepEnv_append_freeOnly (hbSub hb) hf))
      · exact Or.inr ⟨eb, es ++ ef, List.append_assoc eb es ef, Or.inr (hbSub hb),
          Or.inl (Or.inr (splitSignedEnv_append_freeOnly (hssgSub hss) hf))⟩
  rcases h with hb | herr | hm
  · exact Or.inl (Or.inr (hbSub hb))
  · unfold R1bStepKpkErrEnv at herr
    cases hrd : cliIo.rd files (dir ++ [0x2f#8] ++ utf8 "kyber-pre-key") with
    | error _ =>
      rw [hrd] at herr
      rcases herr with hb | ⟨eb, ef, rfl, hb, hf⟩
      · exact Or.inl (Or.inr (hbSub hb))
      · exact Or.inl (Or.inr (r1bFileStepEnv_append_freeOnly (hbSub hb) hf))
    | ok kpkBs =>
      rw [hrd] at herr
      exact hkpkFree herr.2
  · cases hrd : cliIo.rd files (dir ++ [0x2f#8] ++ utf8 "kyber-pre-key") with
    | error _ =>
      rw [hrd] at hm
      exact False.elim hm
    | ok kpkBs =>
      rw [hrd] at hm
      rcases hm with hok | hm2
      · exact hkpkFree (Or.inl hok)
      · split at hm2
        · exact False.elim hm2
        · rcases hm2 with hok | ⟨eok, e3, rfl, hok, h3⟩
          · exact hkpkFree (Or.inl hok)
          · have h3' := init2Stage3Env_sub_r1bTail3 hbundle hsid h3
            rcases hok with hb | ⟨eb, es, rfl, hb, hss⟩
            · exact Or.inr ⟨eok, e3, rfl, Or.inr (hbSub hb),
                Or.inr ⟨[], e3, rfl, Or.inl hnil, h3'⟩⟩
            · exact Or.inr ⟨eb, es ++ e3, List.append_assoc eb es e3, Or.inr (hbSub hb),
                Or.inr ⟨es, e3, rfl, Or.inr (hssgSub hss), h3'⟩⟩

private theorem init2AfterRegOkEnv_sub_r1bTail1 {cEnvs : RunCalleesEnvs}
    (hread : cEnvs.readFile = ReadFileRuleEnv cliIo.rd)
    (hbundle : cEnvs.bundleRead = PubBundleReadEnv cliIo.rd PathEnv (ReadFileRuleEnv cliIo.rd))
    (hsid : cEnvs.splitId = PubSplitIdEnv)
    (hssg : cEnvs.splitSigned = PubSplitSignedEnv PubSplitIdEnv)
    {files : FsFiles} {dir : List (BitVec 8)} {evs : List AllocEvent}
    (h : Init2AfterRegOkEnv cEnvs files dir evs) :
    R1bTail1 cliIo.rd files dir evs := by
  have hnil : FreeOnlyEvs [] := fun _ hm => nomatch hm
  have hssgSub : ∀ {b e}, cEnvs.splitSigned b e → SplitSignedEnv [] e := by
    intro b e he; rw [hssg] at he; exact pubSplitSignedEnv_sub_splitSignedEnv he
  unfold Init2AfterRegOkEnv at h
  dsimp only at h
  rw [hread] at h
  rcases h with hp | hpr | hm
  · exact Or.inl (Or.inr (Or.inl (Or.inr hp)))
  · exact Or.inl (Or.inr (rawRead_sub_r1bFileStepEnv hpr))
  · cases hrd : cliIo.rd files (dir ++ [0x2f#8] ++ utf8 "signed-pre-key") with
    | error _ =>
      rw [hrd] at hm
      exact Or.inl (Or.inr (rawReadFree_append_err_sub_r1bFileStepEnv
        (seqEnv_mono (fun _ h1 => Or.inl h1)
          (fun _ h2 => seqEnv_mono (fun _ he => Or.inl he) (fun _ hf => hf) h2) hm)))
    | ok spkBs =>
      rw [hrd] at hm
      dsimp only at hm
      have hspkFree : ∀ {e},
          SeqEnv (SeqEnv
            (SeqEnv (SeqEnv (PathEnv dir (utf8 "signed-pre-key"))
              (ReadFileRuleEnv cliIo.rd files (dir ++ [0x2f#8] ++ utf8 "signed-pre-key")))
              FreeOnlyEvs)
            (cEnvs.splitSigned spkBs)) FreeOnlyEvs e →
          R1bTail1 cliIo.rd files dir e := by
        intro e hs0
        rcases hs0 with hs | ⟨ebs, ef, rfl, hs, hf⟩
        · rcases hs with hr | ⟨eb, es, rfl, hr, hss⟩
          · exact Or.inl (Or.inr (rawReadFree_sub_r1bFileStepEnv hr))
          · exact Or.inr ⟨eb, es, rfl, Or.inr (rawReadFree_sub_r1bFileStepEnv hr),
              Or.inl (Or.inr (hssgSub hss))⟩
        · rcases hs with hr | ⟨eb, es, rfl, hr, hss⟩
          · exact Or.inl (Or.inr (r1bFileStepEnv_append_freeOnly
              (rawReadFree_sub_r1bFileStepEnv hr) hf))
          · exact Or.inr ⟨eb, es ++ ef, List.append_assoc eb es ef,
              Or.inr (rawReadFree_sub_r1bFileStepEnv hr),
              Or.inl (Or.inr (splitSignedEnv_append_freeOnly (hssgSub hss) hf))⟩
      rcases hm with hok | hm2
      · exact hspkFree (Or.inl hok)
      · split at hm2
        · exact hspkFree hm2
        · rcases hm2 with hok | ⟨eok, e2, rfl, hok, h2⟩
          · exact hspkFree (Or.inl hok)
          · have h2' := init2Stage2Env_sub_r1bTail2 hbundle hsid hssg h2
            rcases hok with hr | ⟨eb, es, rfl, hr, hss⟩
            · exact Or.inr ⟨eok, e2, rfl, Or.inr (rawReadFree_sub_r1bFileStepEnv hr),
                Or.inr ⟨[], e2, rfl, Or.inl hnil, h2'⟩⟩
            · exact Or.inr ⟨eb, es ++ e2, List.append_assoc eb es e2,
                Or.inr (rawReadFree_sub_r1bFileStepEnv hr),
                Or.inr ⟨es, e2, rfl, Or.inr (hssgSub hss), h2'⟩⟩

/-- `Init2Env` (`R1bProofPlacedBudget`) containment in `R1bBinaryEnv`. -/
theorem init2Env_sub_r1bBinaryEnv {cEnvs : RunCalleesEnvs}
    (hread : cEnvs.readFile = ReadFileRuleEnv cliIo.rd)
    (hbundle : cEnvs.bundleRead = PubBundleReadEnv cliIo.rd PathEnv (ReadFileRuleEnv cliIo.rd))
    (hsid : cEnvs.splitId = PubSplitIdEnv)
    (hssg : cEnvs.splitSigned = PubSplitSignedEnv PubSplitIdEnv)
    (g : RunCall) (d : Init1Data) {evs : List AllocEvent}
    (h : Init2Env cEnvs g d evs) :
    R1bBinaryEnv cliIo.rd (runFiles g.i) d.dir evs := by
  unfold Init2Env at h
  dsimp only at h
  rw [hread] at h
  rcases h with hp | hpr | hm
  · exact Or.inl (Or.inl (Or.inr hp))
  · exact Or.inl (rawRead_sub_r1bFileStepEnv hpr)
  · cases hrd : cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") with
    | error _ =>
      rw [hrd] at hm
      exact Or.inl (rawReadFree_append_err_sub_r1bFileStepEnv
        (seqEnv_mono (fun _ h1 => Or.inl h1)
          (fun _ h2 => seqEnv_mono (fun _ he => Or.inl he) (fun _ hf => hf) h2) hm))
    | ok regBs =>
      rw [hrd] at hm
      dsimp only at hm
      split at hm
      · rcases hm with hr | ⟨er, e1, rfl, hr, h1⟩
        · exact Or.inl (rawReadFree_sub_r1bFileStepEnv hr)
        · exact Or.inr ⟨er, e1, rfl, rawReadFree_sub_r1bFileStepEnv hr,
            init2AfterRegOkEnv_sub_r1bTail1 hread hbundle hsid hssg h1⟩
      · exact Or.inl (rawReadFree_append_err_sub_r1bFileStepEnv
          (seqEnv_mono (fun _ h1 => h1)
            (fun _ h2 => seqEnv_mono (fun _ he => Or.inr he) (fun _ hf => hf) h2) hm))

/-- Canonical `Init1Env` (`R1aProofPlacedBudget`) containment in `R1bFileStepEnv`. -/
theorem init1Env_sub_r1bFileStepEnv {cEnvs : RunCalleesEnvs} {rd : ReadRule}
    (hread : cEnvs.readFile = ReadFileRuleEnv rd)
    (g : RunCall) (me : MeAtDispatch) (peerV : AddrV) (dir : List (BitVec 8))
    {evs : List AllocEvent}
    (h : Init1Env cEnvs g me peerV dir evs) :
    R1bFileStepEnv rd (runFiles g.i) dir (utf8 "identity-key") evs := by
  cases me with
  | none =>
    exact Or.inl (Or.inl h)
  | some _ _ =>
    dsimp only [Init1Env] at h
    rw [hread] at h
    rcases h with hp | ⟨ep, er, hp, hr, rfl⟩ | ⟨ep, er, et, hp, hr, ht, rfl⟩
    · exact Or.inl (Or.inr hp)
    · exact Or.inr ⟨ep, er, rfl, Or.inr hp, Or.inl (Or.inr hr)⟩
    · refine Or.inr ⟨ep, er ++ et, List.append_assoc ep er et, Or.inr hp,
        Or.inr ⟨er, et, rfl, Or.inr hr, ?_⟩⟩
      unfold Init1AfterReadEnv at ht
      split at ht
      · obtain ⟨ef, hf, rfl⟩ := ht
        exact Or.inr ⟨[], rustAllocEvents 22 1 ++ ef, rfl,
          fun _ hm => False.elim (List.not_mem_nil hm),
          Or.inr (Or.inr ⟨rustAllocEvents 22 1, ef, rfl, Or.inl rfl, hf⟩)⟩
      · exact Or.inl ht

/-- Canonical `R1cInit3Env` containment in `R1cEnv E.initEnv`. -/
theorem r1cInit3Env_sub_r1cEnv {sEnvs : RunSlotEnvs} {InitEnv : List AllocEvent → Prop}
    {g : RunCall} {d2 : Init2Data}
    (hslot : ∀ evs, sEnvs.initiate (r1cInitGhost g d2 0#64) evs → InitEnv evs)
    {evs : List AllocEvent}
    (h : R1cInit3Env sEnvs g d2 evs) :
    R1cEnv InitEnv evs := by
  rcases h with h1 | ⟨e1, et, h_eq, h1, ht⟩
  · exact Or.inr ⟨evs, [], (List.append_nil evs).symm, hslot evs h1,
      fun _ hm => False.elim (List.not_mem_nil hm)⟩
  · refine Or.inr ⟨e1, et, h_eq, hslot e1 h1, ?_⟩
    rcases ht with rfl | ⟨ed, hd, rfl⟩
    · exact r1cOkTailEvs_freeOnly d2
    · exact freeOnlyEvs_append hd (r1cOkTailEvs_freeOnly d2)

/-- Canonical `R2SendEnv` containment in `R2Env E.encEnv wireOutCap`. -/
theorem r2SendEnv_sub_r2Env {sEnvs : RunSlotEnvs} {S : RunSem}
    {EncEnv : List AllocEvent → Prop} {wireOutCap : Nat}
    {g : RunCall} {me : MeAtDispatch} {peerV : AddrV}
    (hslot : ∀ meV meG evs, me = .some meV meG →
      sEnvs.encrypt (r2EncGhost g (r2PeerGhost0 peerV) meG 0#64) evs → EncEnv evs)
    (hout : ∀ meV f m, S.encrypt (runFiles g.i) (addrValOf peerV) (addrValOf meV)
        g.i.stdin (coinsOf g.i) = some (some (f, .signalMessage m)) →
      m.serialized.length ≤ wireOutCap)
    (houtPk : ∀ meV f m, S.encrypt (runFiles g.i) (addrValOf peerV) (addrValOf meV)
        g.i.stdin (coinsOf g.i) = some (some (f, .preKeySignalMessage m)) →
      m.serialized.length ≤ wireOutCap)
    {evs : List AllocEvent}
    (h : R2SendEnv sEnvs S g me peerV evs) :
    R2Env EncEnv wireOutCap evs := by
  cases me with
  | none => exact Or.inl h
  | some meV meG =>
    refine Or.inr (seqEnv_mono (fun e1 h1 => hslot meV meG e1 rfl h1) (fun et ht => ?_) h)
    rcases ht with hf | hm
    · exact Or.inl hf
    · split at hm
      · rename_i f m heq
        refine Or.inr ⟨[2#8], by decide, m.serialized, hout meV f m heq, ?_⟩
        rcases hm with rfl | ⟨ef, hf, rfl⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨_, ef, rfl, rfl, hf⟩
      · rename_i f m heq
        refine Or.inr ⟨[3#8], by decide, m.serialized, houtPk meV f m heq, ?_⟩
        rcases hm with rfl | ⟨ef, hf, rfl⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨_, ef, rfl, rfl, hf⟩
      · exact False.elim hm

/-- Canonical `R3aRecvWEnv` containment in `R3aBinaryEnv rest E.decSigEnv` via
`WirePksmTightCredit.sigTryFromConcreteEnv_sub_canonInner`. -/
theorem r3aRecvWEnv_sub_r3aBinaryEnv {sEnvs : RunSlotEnvs}
    {DecSigEnv : List AllocEvent → Prop}
    {g : RunCall} {me : MeAtDispatch} {peerV : AddrV} {rest : List (BitVec 8)}
    (hslot : ∀ meV meG m evs, me = .some meV meG →
      SignalMessage.tryFrom protoSignalCodec rest = .ok m →
      sEnvs.decryptSignal (r3aDecSigGhost0 g peerV meG m) evs → DecSigEnv evs)
    {evs : List AllocEvent}
    (h : R3aRecvWEnv sEnvs g me peerV rest evs) :
    R3aBinaryEnv rest DecSigEnv evs := by
  cases me with
  | none => exact Or.inl h
  | some meV meG =>
    refine Or.inr (seqEnv_mono (fun _ h1 => sigTryFromConcreteEnv_sub_canonInner rest h1)
      (fun et ht => ?_) h)
    cases htr : SignalMessage.tryFrom protoSignalCodec rest with
    | error _ =>
      rw [htr] at ht
      exact Or.inl ht
    | ok m =>
      rw [htr] at ht
      exact Or.inr (seqEnv_mono (fun ed hd => hslot meV meG m ed rfl htr hd) (fun _ hf => hf) ht)

/-- Canonical `R3bRecvPEnv` containment in `R3bEnv (E.pksmEnv rest) E.decPkEnv`. -/
theorem r3bRecvPEnv_sub_r3bEnv {S : RunSem} {sEnvs : RunSlotEnvs}
    {PksmTryFromEnv : CryptoVerification.SignalSession.Cli.RunCompose.PksmGhost →
      List AllocEvent → Prop}
    {PksmEnv DecPkEnv : List AllocEvent → Prop}
    {g : RunCall} {me : MeAtDispatch} {peerV : AddrV} {rest : List (BitVec 8)}
    (hpksm : ∀ evs, PksmTryFromEnv (r3bPksmGhost rest) evs → PksmEnv evs)
    (hslot : ∀ meV meG pm evs, me = .some meV meG →
      S.pksmParse rest = some pm →
      sEnvs.decryptPrekey (r3bDecPkGhost g meV peerV pm) evs → DecPkEnv evs)
    {evs : List AllocEvent}
    (h : R3bRecvPEnv S sEnvs PksmTryFromEnv g me peerV rest evs) :
    R3bEnv PksmEnv DecPkEnv evs := by
  cases me with
  | none => exact Or.inl h
  | some meV meG =>
    dsimp only [R3bRecvPEnv] at h
    cases hp : S.pksmParse rest with
    | none =>
      rw [hp] at h
      exact Or.inr (seqEnv_mono (fun _ h1 => hpksm _ h1) (fun _ hf => Or.inl hf) h)
    | some pm =>
      rw [hp] at h
      exact Or.inr (seqEnv_mono (fun _ h1 => hpksm _ h1)
        (fun _ h2 => Or.inr (seqEnv_mono (fun ed hd => hslot meV meG pm ed rfl hp hd)
          (fun _ hf => hf) h2)) h)

/-- Parametric bridge from `RunOkPlacedBudget.RunEnv aEnvs g` to `CliRunBinaryEnv rd E wireOutCap g`
under per-arm containment hypotheses. -/
theorem runEnv_to_cliRunBinaryEnv_of_slots
    {aEnvs : RunArmEnvs} {rd : ReadRule} {E : CliRunCalleeEnvs} {wireOutCap : Nat} {g : RunCall}
    (hpre : ∀ evs, aEnvs.pre g evs → R0BinaryEnv rd g evs)
    (hinit1 : ∀ me peerV dir evs, g.c = .init peerV dir →
      aEnvs.init1 g me peerV dir evs →
      R1bFileStepEnv rd (runFiles g.i) dir (utf8 "identity-key") evs)
    (hinit2 : ∀ peerV dir d1 evs, g.c = .init peerV dir → d1.dir = dir →
      aEnvs.init2 g d1 evs → R1bBinaryEnv rd (runFiles g.i) dir evs)
    (hinit3 : ∀ peerV dir d2 evs, g.c = .init peerV dir → d2.dir = dir →
      d2.peerV = peerV → d2.peerG.val = addrValOf peerV →
      d2.spkSigPtr ≠ 0 → d2.kpkSigPtr ≠ 0 → d2.kpkPtr ≠ 0 →
      aEnvs.init3 g d2 evs → R1cEnv E.initEnv evs)
    (hsend : ∀ me peerV evs, g.c = .send peerV →
      aEnvs.send g me peerV evs → R2Env E.encEnv wireOutCap evs)
    (hrecvW : ∀ me peerV rest evs, g.c = .recv peerV → g.i.stdin = 2#8 :: rest →
      aEnvs.recvW g me peerV rest evs → R3aBinaryEnv rest E.decSigEnv evs)
    (hrecvP : ∀ me peerV rest evs, g.c = .recv peerV → g.i.stdin = 3#8 :: rest →
      aEnvs.recvP g me peerV rest evs → R3bEnv (E.pksmEnv rest) E.decPkEnv evs) :
    ∀ evs, RunEnv aEnvs g evs → CliRunBinaryEnv rd E wireOutCap g evs := by
  have harmAtMe : ∀ me evs, RunArmAtMeEnv aEnvs g me evs →
      RunArmBinaryEnv rd (runFiles g.i) E wireOutCap g.i.stdin g.c evs := by
    intro me evs ha
    unfold RunArmAtMeEnv at ha
    cases hcmd : g.c with
    | keygen _ _ =>
      rw [hcmd] at ha
      exact False.elim ha
    | send peerV =>
      rw [hcmd] at ha
      exact hsend me peerV evs hcmd ha
    | init peerV dir =>
      rw [hcmd] at ha
      refine Or.inr ?_
      cases me with
      | none =>
        exact Or.inl (hinit1 .none peerV dir evs hcmd ha)
      | some meV meG =>
        refine seqEnv_mono (fun _ h1 => hinit1 (.some meV meG) peerV dir _ hcmd h1)
          (fun ec hc => ?_) ha
        unfold RunInit2ChainEnv at hc
        split at hc
        · exact False.elim hc
        · split at hc
          · exact False.elim hc
          · obtain ⟨d1, _, hd1_dir, _, _, _, _, _, hseq23⟩ := hc
            refine seqEnv_mono (fun _ h2 => Or.inr (hinit2 peerV dir d1 _ hcmd hd1_dir h2))
              (fun e3 h3 => ?_) hseq23
            unfold RunInit3Env at h3
            split at h3
            · exact False.elim h3
            · obtain ⟨d2, hd2_peer, hd2_dir, _, _, hd2_pv, _, hspk, hkpkS, hkpkP, hi3⟩ := h3
              exact Or.inr (hinit3 peerV dir d2 e3 hcmd hd2_dir hd2_peer hd2_pv hspk hkpkS hkpkP hi3)
    | recv peerV =>
      rw [hcmd] at ha
      unfold RunArmBinaryEnv RecvArmBinaryEnv
      cases hst : g.i.stdin with
      | nil =>
        rw [hst] at ha
        exact ha
      | cons t rest =>
        rw [hst] at ha
        by_cases ht2 : t = 2#8
        · simp only [ht2, ↓reduceIte] at ha ⊢
          exact hrecvW me peerV rest evs hcmd (ht2 ▸ hst) ha
        · simp only [ht2, ↓reduceIte] at ha ⊢
          by_cases ht3 : t = 3#8
          · simp only [ht3, ↓reduceIte] at ha ⊢
            exact hrecvP me peerV rest evs hcmd (ht3 ▸ hst) ha
          · simp only [ht3, ↓reduceIte] at ha ⊢
            exact ha
  have hdisp : ∀ evs, RunDispatchEnv aEnvs g evs →
      RunArmBinaryEnv rd (runFiles g.i) E wireOutCap g.i.stdin g.c evs := by
    intro evs hd
    unfold RunDispatchEnv at hd
    split at hd
    · exact False.elim hd
    · split at hd
      · exact harmAtMe .none evs hd
      · obtain ⟨meG, _, _, _, ha⟩ := hd
        exact harmAtMe (.some _ meG) evs ha
  have hcore : ∀ evs, RunCoreEnv aEnvs g evs → CliRunBinaryEnv rd E wireOutCap g evs := by
    intro evs hc
    rcases hc with he0 | ⟨e0, e1, rfl, he0, he1⟩
    · exact Or.inr (Or.inl (hpre evs he0))
    · exact Or.inr (Or.inr ⟨e0, e1, rfl, hpre e0 he0, Or.inl (hdisp e1 he1)⟩)
  intro evs hrun
  rcases hrun with hc | ⟨ec, ef, rfl, hc, hf⟩
  · exact hcore evs hc
  · rcases hcore ec hc with hf0 | hr0 | ⟨e0, eaj, rfl, he0, haj⟩
    · exact Or.inl (freeOnlyEvs_append hf0 hf)
    · have hnil : RunArmBinaryEnv rd (runFiles g.i) E wireOutCap g.i.stdin g.c [] :=
        runArmEnv_sub_runArmBinaryEnv
          (CliRunArmsPeak.runArmEnv_nil rd (runFiles g.i) E wireOutCap g.i.stdin g.c)
      exact Or.inr (Or.inr ⟨ec, ef, rfl, hr0, Or.inr ⟨[], ef, rfl, hnil, hf⟩⟩)
    · refine Or.inr (Or.inr ⟨e0, eaj ++ ef, List.append_assoc e0 eaj ef, he0, ?_⟩)
      rcases haj with ha | ⟨ea, ej, rfl, ha, hj⟩
      · exact Or.inr ⟨eaj, ef, rfl, ha, hf⟩
      · exact Or.inr ⟨ea, ej ++ ef, List.append_assoc ea ej ef, ha, freeOnlyEvs_append hj hf⟩

/-- Direct specialization of `runEnv_to_cliRunBinaryEnv_of_slots` to
`cliMainArmEnvs (cliRunCalleesEnvs ReadEnv) sEnvs PksmTryFromEnv S`, discharging `PreEnv`,
`Init1Env`, `Init2Env`, `R1cInit3Env`, `R2SendEnv`, `R3aRecvWEnv`, and `R3bRecvPEnv` automatically
from the 5 slot containment obligations. -/
theorem cliMainArmEnvs_runEnv_to_cliRunBinaryEnv
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {sEnvs : RunSlotEnvs}
    {PksmTryFromEnv : PksmGhost → List AllocEvent → Prop}
    {S : RunSem} {E : CliRunCalleeEnvs} {wireOutCap : Nat} {g : RunCall}
    (hread : ReadEnv = ReadFileRuleEnv cliIo.rd)
    (hinit3 : ∀ peerV dir d2 evs, g.c = .init peerV dir → d2.dir = dir →
      d2.peerV = peerV → d2.peerG.val = addrValOf peerV →
      d2.spkSigPtr ≠ 0 → d2.kpkSigPtr ≠ 0 → d2.kpkPtr ≠ 0 →
      sEnvs.initiate (r1cInitGhost g d2 0#64) evs → E.initEnv evs)
    (hsend_slot : ∀ (_meV : AddrV) (meG : AddrGhost) peerV evs, g.c = .send peerV →
      sEnvs.encrypt (r2EncGhost g (r2PeerGhost0 peerV) meG 0#64) evs → E.encEnv evs)
    (hsend_out : ∀ peerV meV f m, g.c = .send peerV →
      S.encrypt (runFiles g.i) (addrValOf peerV) (addrValOf meV)
        g.i.stdin (coinsOf g.i) = some (some (f, .signalMessage m)) →
      m.serialized.length ≤ wireOutCap)
    (hsend_outPk : ∀ peerV meV f m, g.c = .send peerV →
      S.encrypt (runFiles g.i) (addrValOf peerV) (addrValOf meV)
        g.i.stdin (coinsOf g.i) = some (some (f, .preKeySignalMessage m)) →
      m.serialized.length ≤ wireOutCap)
    (hrecvW_slot : ∀ (_meV : AddrV) (meG : AddrGhost) peerV rest m evs, g.c = .recv peerV →
      g.i.stdin = 2#8 :: rest →
      SignalMessage.tryFrom protoSignalCodec rest = .ok m →
      sEnvs.decryptSignal (r3aDecSigGhost0 g peerV meG m) evs → E.decSigEnv evs)
    (hrecvP_pksm : ∀ peerV rest evs, g.c = .recv peerV → g.i.stdin = 3#8 :: rest →
      PksmTryFromEnv (r3bPksmGhost rest) evs → E.pksmEnv rest evs)
    (hrecvP_slot : ∀ (meV : AddrV) (_meG : AddrGhost) peerV rest pm evs, g.c = .recv peerV →
      g.i.stdin = 3#8 :: rest →
      S.pksmParse rest = some pm →
      sEnvs.decryptPrekey (r3bDecPkGhost g meV peerV pm) evs → E.decPkEnv evs) :
    ∀ evs, RunEnv (cliMainArmEnvs (cliRunCalleesEnvs ReadEnv) sEnvs PksmTryFromEnv S) g evs →
      CliRunBinaryEnv cliIo.rd E wireOutCap g evs := by
  subst hread
  exact runEnv_to_cliRunBinaryEnv_of_slots
    (fun _ hp => preEnv_sub_r0BinaryEnv rfl g hp)
    (fun me peerV dir _ _ h1 => init1Env_sub_r1bFileStepEnv rfl g me peerV dir h1)
    (fun _ _ d1 _ _ hd1 h2 => hd1 ▸ init2Env_sub_r1bBinaryEnv rfl rfl rfl rfl g d1 h2)
    (fun peerV dir d2 _ hc hd2 hpv hpval hspk hkpkS hkpkP h3 =>
      r1cInit3Env_sub_r1cEnv (hinit3 peerV dir d2 · hc hd2 hpv hpval hspk hkpkS hkpkP) h3)
    (fun me peerV _ hc hs =>
      r2SendEnv_sub_r2Env
        (fun meV meG evs _hme he => hsend_slot meV meG peerV evs hc he)
        (fun meV f m heq => hsend_out peerV meV f m hc heq)
        (fun meV f m heq => hsend_outPk peerV meV f m hc heq) hs)
    (fun me peerV rest _ hc hst hrw =>
      r3aRecvWEnv_sub_r3aBinaryEnv
        (fun meV meG m evs _hme htr hd => hrecvW_slot meV meG peerV rest m evs hc hst htr hd)
        hrw)
    (fun me peerV rest _ hc hst hrp =>
      r3bRecvPEnv_sub_r3bEnv
        (fun evs hpk => hrecvP_pksm peerV rest evs hc hst hpk)
        (fun meV meG pm evs _hme hp hd => hrecvP_slot meV meG peerV rest pm evs hc hst hp hd)
        hrp)

abbrev runEnv_cliMainArmEnvs_to_cliRunBinaryEnv_of_slots :=
  @cliMainArmEnvs_runEnv_to_cliRunBinaryEnv

end LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge
