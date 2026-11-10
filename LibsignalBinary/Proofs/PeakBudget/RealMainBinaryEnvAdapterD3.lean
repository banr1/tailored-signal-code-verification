/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge
public import LibsignalBinary.Proofs.PeakBudget.MainResidualFitsEnv
public import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift
public import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftWf
public import LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromPeakSpec
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Plumbing

/-!
# Whole-`main` `RealCliMainBinaryEnvOf` Non-Canonical Input Domain Adapter

Binary-envelope counterpart of `RealMainEnvAdapterD3`, proving
`FitsEnv fineCostModel cliBudgetLimits fineCostModel.init (RealCliMainBinaryEnvOf E i)` and
parametric-domain `mainSt0Dom`..`mainSt3Dom` hop invariants across the non-canonical `pqRecvInputs`
and flat-bundle `init` input domains:
1. Closed-form physical RAM (`≤ 1,063,684,458` B `≤ cliOneGiB`) and virtual-address (`≤ 2 ^ 48`)
   bounds pairing widened `argv ≤ 3` setup with `R0BinaryEnv`.
2. `PhaseCreditSpec` and `PhaseGroupSpec` for `CliRunBinaryEnv` under `CliPqOrD3RecvInputs`.
3. Whole-`main` `FitsEnv` on `RealCliMainBinaryEnvOf` for `pqRecvInputs` (standard and extended W4
   ceilings) and flat-bundle `init` (`bundleCap := sessionCapBytes = 2 MiB`).
4. Domain-parametric residual cost-model invariants `mainSt0Dom`..`mainSt3Dom`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.PeakBudget.RealMainBinaryEnvAdapterD3

open Arm64.Obj (Image)
open Arm64.Process (bytesOfString)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.E2E (PEParams)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost uuidTryParse)
open CryptoVerification.SignalSession
  (CliPqxdhInputs Cmd Inputs PqParty PqxdhPartyInSpecDomain bundleDir partyAddress pqInputs
   pqRecvInputs)
open CryptoVerification.SignalSession.Cli (CliInputsOk ReadRule StoresGhost pathOf utf8)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddrV CallV RunCall addrParse argvFits_length_le cliIo parseArgs)
open CryptoVerification.SignalSession.Cli.RunCompose (RunSem addrValOf runFiles)
open CryptoVerification.SignalSession.Cli.RunProofs (kemPkLen)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs SeqEnv fitsEvents_append
   rustAllocEvents)
open LibsignalBinary.Heap.Fine (FineBudget FineScale fineCostModel)
open LibsignalBinary.Heap.Fine.ClientBounds (fineCostModel_smallMaxReq_eq)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
  (DirDomainCaps argv_length_le_of_cliPqInputs dirDomainCaps_opened_own
   parseArgs_peer_name_length_le)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith
  (cliBudgetLimits cliDecoupledRamNeed cliDecoupledRamNeed_mono cliDecoupledVaNeed
   cliDecoupledVaNeed_mono cliDefaultStaticBytes cliDefaultStaticCount cliMaxAddrTextBytes
   cliMaxDirPathBytes cliMaxDirtyEntries cliOneGiB
   fitsEnv_fineCostModel_of_group_literal_bounds)
open LibsignalBinary.Proofs.PeakBudget.CliGroupBounds
  (m5PhaseEnv_groupSpec m6Env_groupSpec phaseGroupSpec_append_eq readFileRuleEnv_groupSpec)
open LibsignalBinary.Proofs.PeakBudget.CliMainPeakSpec
  (M1PhaseEnv M5PhaseEnv M6Env cliMainDeltaLive_tight cliMainDeltaPeak_tight cliMainMaxReq
   m3PhaseDeltaCum_tight m3PhaseMaxReq m5DirStepDeltaPeak m5DirStepMaxReq m6DeltaCum
   m6_phaseCredit_small1024)
open LibsignalBinary.Proofs.PeakBudget.CliRealExistentialCalleeEnvs
  (W3InitRealParams cliIo_rd_ok_length_le_sessionCapBytes existentialW1_credit
   existentialW1_groups existentialW2_credit existentialW2_groups existentialW3_credit
   existentialW3_groups existentialW4_credit existentialW4_groups mkExistentialRealCalleeEnvs)
open LibsignalBinary.Proofs.PeakBudget.CliRunArmsPeak
  (CliRunCalleeEnvs InitArmEnv JoinEnv PksmTryFromSliceEnv R0OpenedEnv R1cEnv R3bEnv
   RecvBadEnv SplitIdEnv SplitSignedEnv addressTryParseDeltaCum
   addressTryParseDeltaLive addressTryParseDeltaPeak addressTryParseMaxReq
   addressTryParse_phaseCredit fineCostModel_cliRunTightHyps initArmDeltaCum initArmDeltaLive
   initArmDeltaPeak initArmMaxReq pksmSliceCum pksmSliceLive pksmSliceLive_le_peak pksmSliceMaxReq
   pksmSlicePeak pksmTryFromSlice_phaseCredit r2DeltaLive r2DeltaPeak r2MaxReq r2TightDeltaCum
   r2_tight_phaseCredit r3b_phaseCredit recvBad_phaseCredit sigSliceCum sigSliceLive sigSliceMaxReq
   sigSlicePeak splitIdDeltaCum splitId_small_phaseCredit splitSignedDeltaCum
   splitSigned_small_phaseCredit utf8_address_length_le utf8_bundleNames_length_le_16)
open LibsignalBinary.Proofs.PeakBudget.CliRunPeakHelpers
  (phaseCredit_or_freeOnly_left phaseCredit_seq_freeOnly_left phaseCredit_seq_freeOnly_right)
open LibsignalBinary.Proofs.PeakBudget.CliRunPeakSpec
  (r0Opened1MiBCum r0Opened1MiBLive r0Opened1MiBMaxReq r0Opened1MiBPeak)
open LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge
  (CliRunBinaryEnv InitArmBinaryCoreEnv InitArmBinaryEnv OptStageEnv R0BinaryEnv R1bBinaryEnv
   R1bDeserStageEnv R1bFileStepEnv R3aBinaryEnv RealCliMainBinaryEnvOf RecvArmBinaryEnv
   RunArmBinaryEnv cliMainBoundedSetup_fine_groupSpec cliMainBoundedSetup_phaseCredit_fine
   cliRunBinary1MiBCustomPksmCum cliRunBinary1MiBCustomPksmMaxReq
   cliRunBinaryEnv_real_1MiB_fine_phaseCredit_of_cliPqInputs initArmBinaryPrefixCum
   m5Phase_Bounded_phaseCredit_fine r1bDeserStageCum)
open LibsignalBinary.Proofs.PeakBudget.CliSlotFineSpec (SingleSlotFineSpec)
open LibsignalBinary.Proofs.PeakBudget.CliTopBudgetReal
  (CliRealCalleeFineSpecs cliRun1MiBCustomPksmCum cliRun1MiBCustomPksmLive
   cliRun1MiBCustomPksmMaxReq cliRun1MiBCustomPksmPeak cliRunOpenedCustomPksmGrpS
   emptyPhaseCreditSpec emptyPhaseGroupSpec r3bEnv_of_pksm_fine_groupSpec w3InitRealCum
   w3InitRealGrpS w3InitRealLive w3InitRealMaxReq w3InitRealPeak w3InitReal_caps_le)
open LibsignalBinary.Proofs.PeakBudget.CliTopBudgetSpec
  (cliMainTightLiveOf cliMainTightPeakOf cliMainTightReqOf cliRunOfR0_fine_groupSpec
   initArmEnv_fine_groupSpec pksmTryFromSlice_fine_groupSpec r0OpenedEnv_fine_groupSpec
   r2Env_fine_groupSpec)
open LibsignalBinary.Proofs.PeakBudget.DirPeakSpec
  (pathDeltaCum pathDeltaLive pathDeltaPeak pathMaxReq)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit (PhaseGroupSpec)
open LibsignalBinary.Proofs.PeakBudget.MainResidualFitsEnv
  (M2PhaseEnv PostM1SetupEnv PostSetupTailEnv fitsEvents_and_fitsEnv_stepEvents_of_seqEnv
   m3BoundedSetupEnv_nil mainSt0 mainSt1 mainSt2 mainSt3 mainSt4 postM1SetupEnv_nil
   postM1SetupEnv_of_m2Phase postM1SetupEnv_of_seq_m2Phase_m3)
open LibsignalBinary.Proofs.PeakBudget.RealMainEnvAdapter
  (CliMainBoundedSetupEnv M3BoundedSetupEnv ValidPostSetupWitness
   cliIo_rd_initBundle_caps_of_cliPqInputs cliIo_rd_ownAddress_le_40_of_cliPqInputs
   cliMainSetupEarlyExit_fitsEnv_cliBudgetLimits_le1820 cliMainWidenedSetupFineGrpS)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas (fineCostModel_modelHyps)
open LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
  (fineReadFileCum fineReadFileLive fineReadFileMaxReq fineReadFilePeak
   readFile_rule_fine_phaseCredit_tight)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (msgCapBytes sessionCapBytes)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift
  (PeerSpqrStateTight640 peerSpqrStateTight640_of_cliPqInputs_recv)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftWf (peerSpqrStateTight640_of_pqRecv_wf)
open LibsignalBinary.Proofs.PeakBudget.W1SendRealSlot
  (w1SendRealDcanCum w1SendRealDcanGrpS w1SendRealDcanLive w1SendRealDcanMaxReq
   w1SendRealDcanPeak w1SendRealDcan_live_le_peak)
open LibsignalBinary.Proofs.PeakBudget.W2RecvWhisperRealSlot
  (w2RecvWhisperRealDcanCum w2RecvWhisperRealDcanGrpS w2RecvWhisperRealDcanLive
   w2RecvWhisperRealDcanMaxReq w2RecvWhisperRealDcanPeak w2RecvWhisperRealDcan_live_le_peak)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot (w4RecvPrekeyRealGrpS)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot1MiB
  (cliD3DirectMainRamNeed_i cliD3DirectRunCum_i cliD3DirectRunGrpS_i cliRealDirectRunLive_i
   cliRealDirectRunMaxReq_i cliRealDirectRunPeak_i w4RecvPrekeyReal1MiB_i_Cum
   w4RecvPrekeyReal1MiB_i_Live w4RecvPrekeyReal1MiB_i_MaxReq w4RecvPrekeyReal1MiB_i_Peak
   w4RecvPrekeyReal1MiB_i_eq)
open LibsignalBinary.Proofs.PeakBudget.WireMsgPeakSpec
  (fineCostModel_wireLowInterceptHyps sigTryFromCapDeltaGrpS sigTryFromDeltaCum_le_cap
   sigTryFromDeltaGrpS_le_cap sigTryFromDeltaLive_le_cap sigTryFromDeltaPeak_le_cap
   sigTryFromMaxReq_le_cap)
open LibsignalBinary.Proofs.PeakBudget.WirePksmTightCredit
  (SigTryFromCanonInnerEnv pksmCanonSliceCum pksmCanonSliceGrpS pksmCanonSliceLive
   pksmCanonSliceLive_le_peak pksmCanonSliceMaxReq pksmCanonSlicePeak
   pksmCanonSlice_fine_groupSpec pksmCanonSlice_fine_phaseCredit
   sigTryFromCanonInner_phaseCredit sigTryFromCanonInner_phaseGroup)
open LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromPeakSpec (pksmTryFromCapDeltaGrpS)
open LibsignalBinary.Proofs.PeakBudget.WireTryFromHelpers (fineCostModel_wireGroupHyps)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a (DirGetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget
  (PathEnv pathAppendNameEvents pathEvents pathPushSlashEvents pathToOwnedEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.CalleesBudget (addressEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R0ProofPlacedBudget (PreAfterGetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (ReadFileRuleEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeserAux
  (dirGetEnv_path_readFile_fine_phaseCredit_tight dirGetEnv_path_readFile_groupSpec
   pathEnv_fine_phaseCredit_tight)

/-! ## 0. Non-Canonical Domain Transfer, Callee Envelopes, and 5-Slot `SE` Specs -/

private theorem max_self_le (a : Nat) : max a a ≤ a :=
  Nat.max_le.mpr ⟨Nat.le_refl a, Nat.le_refl a⟩

private theorem max_mono {a1 a2 b1 b2 : Nat} (ha : a1 ≤ a2) (hb : b1 ≤ b2) :
    max a1 b1 ≤ max a2 b2 :=
  Nat.max_le.mpr ⟨Nat.le_trans ha (Nat.le_max_left _ _), Nat.le_trans hb (Nat.le_max_right _ _)⟩

private theorem max4_le {a1 a2 b1 b2 c1 c2 d1 d2 : Nat}
    (ha : a1 ≤ a2) (hb : b1 ≤ b2) (hc : c1 ≤ c2) (hd : d1 ≤ d2) :
    max a1 (max b1 (max c1 d1)) ≤ max a2 (max b2 (max c2 d2)) :=
  max_mono ha (max_mono hb (max_mono hc hd))

theorem peer_name_le_40_of_parseArgs_init {args : List (List (BitVec 8))}
    {peerAddr : AddrV} {dir : List (BitVec 8)} {peer : AddrGhost}
    (hparse : parseArgs uuidTryParse args = some (.init peerAddr dir))
    (hpeerVal : peer.val = addrValOf peerAddr) :
    peer.name.bytes.length ≤ 40 := by
  have hp40 : peerAddr.name.length ≤ 40 := parseArgs_peer_name_length_le hparse
  change peer.val.name.length ≤ 40
  rw [hpeerVal]
  exact hp40

theorem w3InitRealDom_peer_len_of_parseArgs {g : RunCall} {w : W3InitRealParams}
    {peerAddr : AddrV} {dir₀ : List (BitVec 8)}
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.init peerAddr dir₀))
    (hpeerVal : w.x.peer.val = addrValOf peerAddr) :
    ∀ peerV dir, g.c = .init peerV dir → w.x.peer.name.bytes.length ≤ 40 := fun _ _ _ =>
  peer_name_le_40_of_parseArgs_init hparse hpeerVal

theorem peer_name_le_40_of_parseArgs_recv {args : List (List (BitVec 8))}
    {peerAddr : AddrV} {peer : AddrGhost}
    (hparse : parseArgs uuidTryParse args = some (.recv peerAddr))
    (hpeerVal : peer.val = addrValOf peerAddr) :
    peer.name.bytes.length ≤ 40 := by
  have hp40 : peerAddr.name.length ≤ 40 := parseArgs_peer_name_length_le hparse
  change peer.val.name.length ≤ 40
  rw [hpeerVal]
  exact hp40

theorem cliPqxdhInputs_pqRecvInputs_nil {P : PEParams} {st : PqParty}
    (hwf : PqxdhPartyInSpecDomain P st) (rc : BitVec 256) :
    CliPqxdhInputs P (pqRecvInputs P st [] rc) :=
  ⟨st, hwf, Or.inr (Or.inr (Or.inr (Or.inr ⟨[], rc, by decide, by decide, by decide, rfl⟩)))⟩

theorem runFiles_pqRecvInputs_eq_nil (P : PEParams) (st : PqParty)
    (ct : List (BitVec 8)) (rc : BitVec 256) :
    runFiles (pqRecvInputs P st ct rc) = runFiles (pqRecvInputs P st [] rc) := rfl

theorem argv_length_le_3_of_pqOrD3Recv {P : PEParams} {i : Inputs}
    (hi : CliPqxdhInputs P i ∨
      ∃ (st : PqParty) (ct : List (BitVec 8)) (rc : BitVec 256),
        PqxdhPartyInSpecDomain P st ∧ i = pqRecvInputs P st ct rc) :
    i.argv.length ≤ 3 := by
  rcases hi with hi_pq | ⟨st, ct, rc, _, rfl⟩
  · exact argv_length_le_of_cliPqInputs hi_pq
  · simp only [pqRecvInputs, pqInputs, Cmd.argv, List.length_cons, List.length_nil]
    omega

theorem peerSpqrStateTight640_of_pqOrD3Recv {P : PEParams} {i : Inputs} {peer : AddrV}
    (hi : CliPqxdhInputs P i ∨
      ∃ (st : PqParty) (ct : List (BitVec 8)) (rc : BitVec 256),
        PqxdhPartyInSpecDomain P st ∧ i = pqRecvInputs P st ct rc)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peer)) :
    PeerSpqrStateTight640 P.C.F P.Q.K (runFiles i) (addrValOf peer) := by
  rcases hi with hi_pq | ⟨st, ct, rc, hwf, rfl⟩
  · exact peerSpqrStateTight640_of_cliPqInputs_recv hi_pq hparse
  · exact peerSpqrStateTight640_of_pqRecv_wf hwf hparse

theorem cliIo_rd_ownAddress_le_40_of_pqOrD3Recv {P : PEParams} {i : Inputs}
    (hi : CliPqxdhInputs P i ∨
      ∃ (st : PqParty) (ct : List (BitVec 8)) (rc : BitVec 256),
        PqxdhPartyInSpecDomain P st ∧ i = pqRecvInputs P st ct rc)
    {bs : List (BitVec 8)}
    (hrd : cliIo.rd (runFiles i) (pathOf StoresGhost.opened.identity.own.path (utf8 "address")) =
      .ok bs) :
    bs.length ≤ 40 := by
  rcases hi with hi_pq | ⟨st, ct, rc, hwf, rfl⟩
  · exact cliIo_rd_ownAddress_le_40_of_cliPqInputs hi_pq hrd
  · exact cliIo_rd_ownAddress_le_40_of_cliPqInputs (cliPqxdhInputs_pqRecvInputs_nil hwf rc) hrd

theorem cliIo_rd_initBundle_caps_of_pqOrD3Recv {P : PEParams} {g : RunCall}
    (hi : CliPqxdhInputs P g.i ∨
      ∃ (st : PqParty) (ct : List (BitVec 8)) (rc : BitVec 256),
        PqxdhPartyInSpecDomain P st ∧ g.i = pqRecvInputs P st ct rc)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c) :
    ∀ peer dir, g.c = .init peer dir → dir.length ≤ 26 ∧
      (∀ name bs, cliIo.rd (runFiles g.i) (pathOf dir name) = .ok bs → bs.length ≤ 1637) := by
  rcases hi with hi_pq | ⟨st, ct, rc, hwf, hgi⟩
  · exact cliIo_rd_initBundle_caps_of_cliPqInputs hi_pq hparse
  · let g₀ : RunCall := { g with i := pqRecvInputs P st [] rc }
    have hi₀ : CliPqxdhInputs P g₀.i := cliPqxdhInputs_pqRecvInputs_nil hwf rc
    have hparse₀ : parseArgs uuidTryParse (g₀.i.argv.map bytesOfString) = some g₀.c := by
      change parseArgs uuidTryParse ((pqRecvInputs P st [] rc).argv.map bytesOfString) = some g.c
      have harg : g.i.argv = (pqRecvInputs P st [] rc).argv := by rw [hgi]; rfl
      rwa [← harg]
    have hcaps₀ := cliIo_rd_initBundle_caps_of_cliPqInputs hi₀ hparse₀
    intro peer dir hc
    obtain ⟨hd, hb⟩ := hcaps₀ peer dir hc
    refine ⟨hd, fun name bs hrd => hb name bs ?_⟩
    have hf : runFiles g.i = runFiles g₀.i := by rw [hgi]; rfl
    rwa [← hf]

theorem d3RecvW1_credit [LibsignalPlacement]
    (img : Image) (S : RunSem) {P : PEParams} {g : RunCall}
    (hi : CliPqxdhInputs P g.i ∨
      ∃ (st : PqParty) (ct : List (BitVec 8)) (rc : BitVec 256),
        PqxdhPartyInSpecDomain P st ∧ g.i = pqRecvInputs P st ct rc)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c) :
    PhaseCreditSpec fineCostModel
      (mkExistentialRealCalleeEnvs img S P g).encEnv
      w1SendRealDcanCum w1SendRealDcanLive w1SendRealDcanPeak w1SendRealDcanMaxReq := by
  rcases hi with hi_pq | ⟨st, ct, rc, _, hgi⟩
  · exact existentialW1_credit img S hi_pq hparse
  · have harg : g.i.argv = (Cmd.recv (partyAddress st.party.other)).argv := by rw [hgi]; rfl
    rw [harg, CryptoVerification.SignalSession.Cli.RunRefine.parseArgs_recv] at hparse
    rcases g with ⟨i', c', a', res', call', stores', inp', coins'⟩
    cases c' <;> cases hparse
    exact emptyPhaseCreditSpec _ _ _ _

theorem d3RecvW1_groups [LibsignalPlacement]
    (img : Image) (S : RunSem) {P : PEParams} {g : RunCall}
    (hi : CliPqxdhInputs P g.i ∨
      ∃ (st : PqParty) (ct : List (BitVec 8)) (rc : BitVec 256),
        PqxdhPartyInSpecDomain P st ∧ g.i = pqRecvInputs P st ct rc)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c) :
    PhaseGroupSpec fineCostModel
      (mkExistentialRealCalleeEnvs img S P g).encEnv
      w1SendRealDcanGrpS := by
  rcases hi with hi_pq | ⟨st, ct, rc, _, hgi⟩
  · exact existentialW1_groups img S hi_pq hparse
  · have harg : g.i.argv = (Cmd.recv (partyAddress st.party.other)).argv := by rw [hgi]; rfl
    rw [harg, CryptoVerification.SignalSession.Cli.RunRefine.parseArgs_recv] at hparse
    rcases g with ⟨i', c', a', res', call', stores', inp', coins'⟩
    cases c' <;> cases hparse
    exact emptyPhaseGroupSpec _

theorem d3RecvW2_credit [LibsignalPlacement]
    (img : Image) (S : RunSem) {P : PEParams} {g : RunCall}
    (hi : CliPqxdhInputs P g.i ∨
      ∃ (st : PqParty) (ct : List (BitVec 8)) (rc : BitVec 256),
        PqxdhPartyInSpecDomain P st ∧ g.i = pqRecvInputs P st ct rc)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c) :
    PhaseCreditSpec fineCostModel
      (mkExistentialRealCalleeEnvs img S P g).decSigEnv
      w2RecvWhisperRealDcanCum w2RecvWhisperRealDcanLive w2RecvWhisperRealDcanPeak
      w2RecvWhisperRealDcanMaxReq := by
  rcases hi with hi_pq | ⟨st, ct, rc, hwf, hgi⟩
  · exact existentialW2_credit img S hi_pq hparse
  · let g₀ : RunCall := { g with i := pqRecvInputs P st [] rc }
    have hi₀ : CliPqxdhInputs P g₀.i := cliPqxdhInputs_pqRecvInputs_nil hwf rc
    have hparse₀ : parseArgs uuidTryParse (g₀.i.argv.map bytesOfString) = some g₀.c := by
      change parseArgs uuidTryParse ((pqRecvInputs P st [] rc).argv.map bytesOfString) = some g.c
      have harg : g.i.argv = (pqRecvInputs P st [] rc).argv := by rw [hgi]; rfl
      rwa [← harg]
    have heq : (mkExistentialRealCalleeEnvs img S P g).decSigEnv =
        (mkExistentialRealCalleeEnvs img S P g₀).decSigEnv := by
      rcases g with ⟨i', c', a', res', call', stores', inp', coins'⟩
      dsimp only [g₀] at *
      subst hgi
      rfl
    rw [heq]
    exact existentialW2_credit img S hi₀ hparse₀

theorem d3RecvW2_groups [LibsignalPlacement]
    (img : Image) (S : RunSem) {P : PEParams} {g : RunCall}
    (hi : CliPqxdhInputs P g.i ∨
      ∃ (st : PqParty) (ct : List (BitVec 8)) (rc : BitVec 256),
        PqxdhPartyInSpecDomain P st ∧ g.i = pqRecvInputs P st ct rc)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c) :
    PhaseGroupSpec fineCostModel
      (mkExistentialRealCalleeEnvs img S P g).decSigEnv
      w2RecvWhisperRealDcanGrpS := by
  rcases hi with hi_pq | ⟨st, ct, rc, hwf, hgi⟩
  · exact existentialW2_groups img S hi_pq hparse
  · let g₀ : RunCall := { g with i := pqRecvInputs P st [] rc }
    have hi₀ : CliPqxdhInputs P g₀.i := cliPqxdhInputs_pqRecvInputs_nil hwf rc
    have hparse₀ : parseArgs uuidTryParse (g₀.i.argv.map bytesOfString) = some g₀.c := by
      change parseArgs uuidTryParse ((pqRecvInputs P st [] rc).argv.map bytesOfString) = some g.c
      have harg : g.i.argv = (pqRecvInputs P st [] rc).argv := by rw [hgi]; rfl
      rwa [← harg]
    have heq : (mkExistentialRealCalleeEnvs img S P g).decSigEnv =
        (mkExistentialRealCalleeEnvs img S P g₀).decSigEnv := by
      rcases g with ⟨i', c', a', res', call', stores', inp', coins'⟩
      dsimp only [g₀] at *
      subst hgi
      rfl
    rw [heq]
    exact existentialW2_groups img S hi₀ hparse₀

def mkD3RecvCalleeEnvs [LibsignalPlacement]
    (img : Image) (S : RunSem) (P : PEParams)
    (DecPkEnv : RunCall → List AllocEvent → Prop) (g : RunCall) :
    CliRunCalleeEnvs where
  initEnv := (mkExistentialRealCalleeEnvs img S P g).initEnv
  encEnv := (mkExistentialRealCalleeEnvs img S P g).encEnv
  decSigEnv := (mkExistentialRealCalleeEnvs img S P g).decSigEnv
  pksmEnv := PksmTryFromSliceEnv
  decPkEnv := DecPkEnv g

def mkExistentialD3RecvCalleeEnvs [LibsignalPlacement]
    (img : Image) (S : RunSem) (P : PEParams) (g : RunCall) :
    CliRunCalleeEnvs :=
  mkD3RecvCalleeEnvs img S P (fun g' => (mkExistentialRealCalleeEnvs img S P g').decPkEnv) g

def d3RecvCalleeFineSpecs [LibsignalPlacement]
    (img : Image) (S : RunSem) {P : PEParams}
    {DecPkEnv : RunCall → List AllocEvent → Prop} {g : RunCall}
    (S_pk : SingleSlotFineSpec (DecPkEnv g))
    (hi : CliPqxdhInputs P g.i ∨
      ∃ (st : PqParty) (ct : List (BitVec 8)) (rc : BitVec 256),
        PqxdhPartyInSpecDomain P st ∧ g.i = pqRecvInputs P st ct rc)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c) :
    CliRealCalleeFineSpecs (mkD3RecvCalleeEnvs img S P DecPkEnv g) where
  initCum := w3InitRealCum
  initLive := w3InitRealLive
  initPeak := w3InitRealPeak
  initMaxReq := w3InitRealMaxReq
  initGrpS := w3InitRealGrpS
  init_spec := existentialW3_credit img S P g
  init_lp := w3InitReal_caps_le.2.2.1
  init_grp := existentialW3_groups img S P g
  encCum := w1SendRealDcanCum
  encLive := w1SendRealDcanLive
  encPeak := w1SendRealDcanPeak
  encMaxReq := w1SendRealDcanMaxReq
  encGrpS := w1SendRealDcanGrpS
  enc_spec := d3RecvW1_credit img S hi hparse
  enc_lp := w1SendRealDcan_live_le_peak
  enc_grp := d3RecvW1_groups img S hi hparse
  decSigCum := w2RecvWhisperRealDcanCum
  decSigLive := w2RecvWhisperRealDcanLive
  decSigPeak := w2RecvWhisperRealDcanPeak
  decSigMaxReq := w2RecvWhisperRealDcanMaxReq
  decSigGrpS := w2RecvWhisperRealDcanGrpS
  decSig_spec := d3RecvW2_credit img S hi hparse
  decSig_lp := w2RecvWhisperRealDcan_live_le_peak
  decSig_grp := d3RecvW2_groups img S hi hparse
  pksmCum := pksmSliceCum msgCapBytes
  pksmLive := pksmSliceLive msgCapBytes
  pksmPeak := pksmSlicePeak msgCapBytes
  pksmMaxReq := pksmSliceMaxReq msgCapBytes
  pksmGrpS := pksmTryFromCapDeltaGrpS msgCapBytes
  pksm_spec := fun _ hrest =>
    pksmTryFromSlice_phaseCredit fineCostModel_modelHyps fineCostModel_wireLowInterceptHyps hrest
  pksm_lp := pksmSliceLive_le_peak msgCapBytes
  pksm_grp := fun _ hrest => pksmTryFromSlice_fine_groupSpec hrest
  decPkCum := S_pk.cum
  decPkLive := S_pk.live
  decPkPeak := S_pk.peak
  decPkMaxReq := S_pk.maxReq
  decPkGrpS := S_pk.grpS
  decPk_spec := S_pk.credit
  decPk_lp := S_pk.live_le_peak
  decPk_grp := S_pk.groups

theorem d3RecvCalleeFineSpecs_direct_run_bounds [LibsignalPlacement]
    (img : Image) (S : RunSem) {P : PEParams}
    {DecPkEnv : RunCall → List AllocEvent → Prop} {g : RunCall}
    (S_pk : SingleSlotFineSpec (DecPkEnv g))
    (hCaps : S_pk.cum ≤ w4RecvPrekeyReal1MiB_i_Cum ∧
      S_pk.live ≤ w4RecvPrekeyReal1MiB_i_Live ∧
      S_pk.peak ≤ w4RecvPrekeyReal1MiB_i_Peak ∧
      S_pk.maxReq ≤ w4RecvPrekeyReal1MiB_i_MaxReq ∧
      S_pk.grpS ≤ w4RecvPrekeyRealGrpS)
    (hi : CliPqxdhInputs P g.i ∨
      ∃ (st : PqParty) (ct : List (BitVec 8)) (rc : BitVec 256),
        PqxdhPartyInSpecDomain P st ∧ g.i = pqRecvInputs P st ct rc)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c) :
    let SE := d3RecvCalleeFineSpecs img S S_pk hi hparse
    cliRun1MiBCustomPksmCum SE.pksmCum SE.initCum SE.encCum SE.decSigCum SE.decPkCum ≤
      cliD3DirectRunCum_i ∧
    cliRun1MiBCustomPksmLive SE.pksmLive SE.initLive SE.encLive SE.decSigLive SE.decPkLive ≤
      cliRealDirectRunLive_i ∧
    cliRun1MiBCustomPksmPeak SE.pksmLive SE.pksmPeak
      SE.initPeak SE.encLive SE.encPeak SE.decSigPeak SE.decPkPeak ≤
      cliRealDirectRunPeak_i ∧
    cliRun1MiBCustomPksmMaxReq SE.pksmMaxReq
      SE.initMaxReq SE.encMaxReq SE.decSigMaxReq SE.decPkMaxReq ≤
      cliRealDirectRunMaxReq_i ∧
    cliRunOpenedCustomPksmGrpS msgCapBytes SE.pksmGrpS
      SE.initGrpS SE.encGrpS SE.decSigGrpS SE.decPkGrpS ≤
      cliD3DirectRunGrpS_i := by
  rcases hCaps with ⟨hpc, hpl, hpp, hpr, hpg⟩
  dsimp only [d3RecvCalleeFineSpecs]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold cliD3DirectRunCum_i cliRun1MiBCustomPksmCum
    exact Nat.add_le_add_left (max4_le (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
      (Nat.add_le_add_left hpc _)) _
  · unfold cliRealDirectRunLive_i CliTopBudgetReal.cliRealPksmLiveCap cliRun1MiBCustomPksmLive
    exact Nat.add_le_add_left (max4_le (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
      (Nat.add_le_add_left hpl _)) _
  · unfold cliRealDirectRunPeak_i CliTopBudgetReal.cliRealPksmLiveCap
      CliTopBudgetReal.cliRealPksmPeakCap cliRun1MiBCustomPksmPeak
    exact max_mono (Nat.le_refl _) (Nat.add_le_add_left (max4_le (Nat.le_refl _) (Nat.le_refl _)
      (Nat.le_refl _) (max_mono (Nat.le_refl _) (Nat.add_le_add_left hpp _))) _)
  · unfold cliRealDirectRunMaxReq_i CliTopBudgetReal.cliRealPksmReqCap cliRun1MiBCustomPksmMaxReq
    exact max_mono (Nat.le_refl _) (max4_le (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
      (max_mono (Nat.le_refl _) hpr))
  · unfold cliD3DirectRunGrpS_i cliRunOpenedCustomPksmGrpS
    exact Nat.add_le_add_left (max4_le (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
      (Nat.add_le_add_left hpg _)) _

def cliD3MainLive : Nat :=
  cliMainTightLiveOf cliRealDirectRunLive_i

def cliD3MainPeak : Nat :=
  cliMainTightPeakOf cliRealDirectRunLive_i cliRealDirectRunPeak_i

def cliD3MainReq : Nat :=
  max (max (16 * 2048) 16384) (cliMainTightReqOf cliRealDirectRunMaxReq_i)

def d3RecvW4ExtCum : Nat := w4RecvPrekeyReal1MiB_i_Cum + 2000000
def d3RecvW4ExtLive : Nat := w4RecvPrekeyReal1MiB_i_Live + 500000
def d3RecvW4ExtPeak : Nat := w4RecvPrekeyReal1MiB_i_Peak + 500000
def d3RecvW4ExtMaxReq : Nat := w4RecvPrekeyReal1MiB_i_MaxReq + 200000
def d3RecvW4ExtGrpS : Nat := w4RecvPrekeyRealGrpS + 100 * FineScale

theorem d3RecvW4Ext_live_le_peak : d3RecvW4ExtLive ≤ d3RecvW4ExtPeak :=
  Nat.add_le_add_right w4RecvPrekeyReal1MiB_i_eq.2.2.2.2 500000

def cliD3ExtRunCum : Nat :=
  cliRun1MiBCustomPksmCum (pksmSliceCum msgCapBytes) w3InitRealCum
    w1SendRealDcanCum w2RecvWhisperRealDcanCum d3RecvW4ExtCum

def cliD3ExtRunLive : Nat :=
  cliRun1MiBCustomPksmLive CliTopBudgetReal.cliRealPksmLiveCap w3InitRealLive
    w1SendRealDcanLive w2RecvWhisperRealDcanLive d3RecvW4ExtLive

def cliD3ExtRunPeak : Nat :=
  cliRun1MiBCustomPksmPeak CliTopBudgetReal.cliRealPksmLiveCap CliTopBudgetReal.cliRealPksmPeakCap
    w3InitRealPeak w1SendRealDcanLive w1SendRealDcanPeak w2RecvWhisperRealDcanPeak d3RecvW4ExtPeak

def cliD3ExtRunMaxReq : Nat :=
  cliRun1MiBCustomPksmMaxReq CliTopBudgetReal.cliRealPksmReqCap w3InitRealMaxReq
    w1SendRealDcanMaxReq w2RecvWhisperRealDcanMaxReq d3RecvW4ExtMaxReq

def cliD3ExtRunGrpS : Nat :=
  cliRunOpenedCustomPksmGrpS msgCapBytes (pksmTryFromCapDeltaGrpS msgCapBytes) w3InitRealGrpS
    w1SendRealDcanGrpS w2RecvWhisperRealDcanGrpS d3RecvW4ExtGrpS

def cliD3ExtMainLive : Nat :=
  cliMainTightLiveOf cliD3ExtRunLive

def cliD3ExtMainPeak : Nat :=
  cliMainTightPeakOf cliD3ExtRunLive cliD3ExtRunPeak

def cliD3ExtMainReq : Nat :=
  max (max (16 * 2048) 16384) (cliMainTightReqOf cliD3ExtRunMaxReq)

theorem d3RecvCalleeFineSpecs_ext_direct_run_bounds [LibsignalPlacement]
    (img : Image) (S : RunSem) {P : PEParams}
    {DecPkEnv : RunCall → List AllocEvent → Prop} {g : RunCall}
    (S_pk : SingleSlotFineSpec (DecPkEnv g))
    (hCaps : S_pk.cum ≤ d3RecvW4ExtCum ∧
      S_pk.live ≤ d3RecvW4ExtLive ∧
      S_pk.peak ≤ d3RecvW4ExtPeak ∧
      S_pk.maxReq ≤ d3RecvW4ExtMaxReq ∧
      S_pk.grpS ≤ d3RecvW4ExtGrpS)
    (hi : CliPqxdhInputs P g.i ∨
      ∃ (st : PqParty) (ct : List (BitVec 8)) (rc : BitVec 256),
        PqxdhPartyInSpecDomain P st ∧ g.i = pqRecvInputs P st ct rc)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c) :
    let SE := d3RecvCalleeFineSpecs img S S_pk hi hparse
    cliRun1MiBCustomPksmCum SE.pksmCum SE.initCum SE.encCum SE.decSigCum SE.decPkCum ≤
      cliD3ExtRunCum ∧
    cliRun1MiBCustomPksmLive SE.pksmLive SE.initLive SE.encLive SE.decSigLive SE.decPkLive ≤
      cliD3ExtRunLive ∧
    cliRun1MiBCustomPksmPeak SE.pksmLive SE.pksmPeak
      SE.initPeak SE.encLive SE.encPeak SE.decSigPeak SE.decPkPeak ≤
      cliD3ExtRunPeak ∧
    cliRun1MiBCustomPksmMaxReq SE.pksmMaxReq
      SE.initMaxReq SE.encMaxReq SE.decSigMaxReq SE.decPkMaxReq ≤
      cliD3ExtRunMaxReq ∧
    cliRunOpenedCustomPksmGrpS msgCapBytes SE.pksmGrpS
      SE.initGrpS SE.encGrpS SE.decSigGrpS SE.decPkGrpS ≤
      cliD3ExtRunGrpS := by
  rcases hCaps with ⟨hpc, hpl, hpp, hpr, hpg⟩
  dsimp only [d3RecvCalleeFineSpecs]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold cliD3ExtRunCum cliRun1MiBCustomPksmCum
    exact Nat.add_le_add_left (max4_le (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
      (Nat.add_le_add_left hpc _)) _
  · unfold cliD3ExtRunLive CliTopBudgetReal.cliRealPksmLiveCap cliRun1MiBCustomPksmLive
    exact Nat.add_le_add_left (max4_le (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
      (Nat.add_le_add_left hpl _)) _
  · unfold cliD3ExtRunPeak CliTopBudgetReal.cliRealPksmLiveCap
      CliTopBudgetReal.cliRealPksmPeakCap cliRun1MiBCustomPksmPeak
    exact max_mono (Nat.le_refl _) (Nat.add_le_add_left (max4_le (Nat.le_refl _) (Nat.le_refl _)
      (Nat.le_refl _) (max_mono (Nat.le_refl _) (Nat.add_le_add_left hpp _))) _)
  · unfold cliD3ExtRunMaxReq CliTopBudgetReal.cliRealPksmReqCap cliRun1MiBCustomPksmMaxReq
    exact max_mono (Nat.le_refl _) (max4_le (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
      (max_mono (Nat.le_refl _) hpr))
  · unfold cliD3ExtRunGrpS cliRunOpenedCustomPksmGrpS
    exact Nat.add_le_add_left (max4_le (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
      (Nat.add_le_add_left hpg _)) _

/-! ## 1. Binary D3 Whole-`main` Constants & `≤ cliD3DirectMainRamNeed_i` Arithmetic -/

/-- Binary whole-`run` D3 scaled group count (`cliD3DirectRunGrpS_i + 27 * FineScale`). -/
def cliD3BinaryDirectRunGrpS_i : Nat :=
  cliD3DirectRunGrpS_i + 27 * FineScale

/-- Binary whole-`main` D3 cumulative credit (`argv ≤ 3` widened `16384`-B setup). -/
def cliD3BinaryMainCum : Nat :=
  123250 + m3PhaseDeltaCum_tight + cliD3DirectRunCum_i +
    cliMaxDirtyEntries *
      (10 * max (4 * cliMaxDirPathBytes + cliMaxAddrTextBytes + 16) 16 + 4 * 9539) +
    m6DeltaCum

/-- Binary whole-`main` D3 scaled group count (`argv ≤ 3` widened setup + `R0BinaryEnv`). -/
def cliD3BinaryMainGrpS : Nat :=
  cliMainWidenedSetupFineGrpS + cliD3BinaryDirectRunGrpS_i +
    cliMaxDirtyEntries * (12 * FineScale) + 3 * FineScale

/-- Closed-form physical RAM need on `RealCliMainBinaryEnvOf` for D3 `recv` (`+0` B above
`cliD3DirectMainRamNeed_i = 1,063,684,458` B). -/
def cliD3BinaryDirectMainRamNeed_i : Nat :=
  cliDecoupledRamNeed cliDefaultStaticBytes cliD3BinaryMainCum cliD3MainPeak cliD3MainReq
    ((cliD3BinaryMainGrpS + FineScale - 1) / FineScale)

/-- Kernel-checked bound proving `cliD3BinaryDirectMainRamNeed_i ≤ cliD3DirectMainRamNeed_i`
(`1,063,684,458` B) and `≤ cliOneGiB` (`1,073,741,824` B), plus `VA ≤ 2 ^ 48`. -/
theorem cliD3BinaryDirectMainRamNeed_i_le_d3_and_oneGiB :
    cliD3BinaryDirectMainRamNeed_i ≤ cliD3DirectMainRamNeed_i ∧
    cliD3BinaryDirectMainRamNeed_i ≤ cliOneGiB ∧
    cliDecoupledVaNeed cliDefaultStaticBytes cliDefaultStaticCount cliD3BinaryMainCum
      cliD3MainPeak cliD3MainReq ((cliD3BinaryMainGrpS + FineScale - 1) / FineScale) ≤ 2 ^ 48 :=
  ⟨by decide, by decide, by decide⟩

private theorem cliD3BinaryMain_arith_bounds {lim : BudgetLimits}
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes)
    (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap1G : cliOneGiB ≤ lim.physCap) :
    cliD3MainLive ≤ cliD3MainPeak ∧
    cliDecoupledRamNeed lim.staticBytes cliD3BinaryMainCum cliD3MainPeak cliD3MainReq
      ((cliD3BinaryMainGrpS + FineScale - 1) / FineScale) ≤ lim.physCap ∧
    cliDecoupledVaNeed lim.staticBytes lim.staticCount cliD3BinaryMainCum cliD3MainPeak
      cliD3MainReq ((cliD3BinaryMainGrpS + FineScale - 1) / FineScale) ≤ 2 ^ 48 :=
  ⟨by unfold cliD3MainLive cliD3MainPeak cliMainTightLiveOf cliMainTightPeakOf
        cliMainDeltaLive_tight cliMainDeltaPeak_tight
      exact Nat.le_trans (Nat.add_le_add_left
        (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_max_right _ _)) _) (Nat.le_max_right _ _),
   Nat.le_trans
     (cliDecoupledRamNeed_mono hsb (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
     (Nat.le_trans cliD3BinaryDirectMainRamNeed_i_le_d3_and_oneGiB.2.1 hcap1G),
   Nat.le_trans
     (cliDecoupledVaNeed_mono hsb hsc (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
       (Nat.le_refl _))
     cliD3BinaryDirectMainRamNeed_i_le_d3_and_oneGiB.2.2⟩

/-- Extended-ceiling (`d3RecvW4Ext*`) binary whole-`run` and whole-`main` constants. -/
def cliD3BinaryExtRunGrpS : Nat :=
  cliD3ExtRunGrpS + 27 * FineScale

def cliD3BinaryExtMainCum : Nat :=
  123250 + m3PhaseDeltaCum_tight + cliD3ExtRunCum +
    cliMaxDirtyEntries *
      (10 * max (4 * cliMaxDirPathBytes + cliMaxAddrTextBytes + 16) 16 + 4 * 9539) +
    m6DeltaCum

def cliD3BinaryExtMainGrpS : Nat :=
  cliMainWidenedSetupFineGrpS + cliD3BinaryExtRunGrpS +
    cliMaxDirtyEntries * (12 * FineScale) + 3 * FineScale

private theorem cliD3BinaryExtMain_arith_bounds :
    cliD3ExtMainLive ≤ cliD3ExtMainPeak ∧
    cliDecoupledRamNeed cliDefaultStaticBytes cliD3BinaryExtMainCum cliD3ExtMainPeak
      cliD3ExtMainReq ((cliD3BinaryExtMainGrpS + FineScale - 1) / FineScale) ≤ cliOneGiB ∧
    cliDecoupledVaNeed cliDefaultStaticBytes cliDefaultStaticCount cliD3BinaryExtMainCum
      cliD3ExtMainPeak cliD3ExtMainReq
      ((cliD3BinaryExtMainGrpS + FineScale - 1) / FineScale) ≤ 2 ^ 48 :=
  ⟨by unfold cliD3ExtMainLive cliD3ExtMainPeak cliMainTightLiveOf cliMainTightPeakOf
        cliMainDeltaLive_tight cliMainDeltaPeak_tight
      exact Nat.le_trans (Nat.add_le_add_left
        (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_max_right _ _)) _) (Nat.le_max_right _ _),
   by decide,
   by decide⟩

/-! ## 2. Binary `M4` (`CliRunBinaryEnv`) `PhaseCreditSpec` & `PhaseGroupSpec` -/

private theorem optStage_phaseCredit {P : List AllocEvent → Prop} {c l p r : Nat}
    (h : PhaseCreditSpec fineCostModel P c l p r) :
    PhaseCreditSpec fineCostModel (OptStageEnv P) c l p r :=
  phaseCredit_or_freeOnly_left fineCostModel_modelHyps (fun _ hf => hf) h

private theorem optStage_groupSpec {P : List AllocEvent → Prop} {g : Nat}
    (h : PhaseGroupSpec fineCostModel P g) :
    PhaseGroupSpec fineCostModel (OptStageEnv P) g :=
  ((PhaseGroupSpec.freeOnly fineCostModel).or h).mono (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)

private theorem dirDomainCaps_opened_own_64 :
    DirDomainCaps 64 0 0 StoresGhost.opened.identity.own :=
  dirDomainCaps_opened_own.mono (by decide) (Nat.le_refl 0) (Nat.le_refl 0)

private theorem preAfterGetEnv_fine_phaseCredit (g : RunCall) :
    PhaseCreditSpec fineCostModel (PreAfterGetEnv g)
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

private theorem r0BinaryEnv_fine_phaseCredit_of_pqOrD3Recv {P : PEParams} {g : RunCall}
    (hi : CliPqxdhInputs P g.i ∨
      ∃ (st : PqParty) (ct : List (BitVec 8)) (rc : BitVec 256),
        PqxdhPartyInSpecDomain P st ∧ g.i = pqRecvInputs P st ct rc) :
    PhaseCreditSpec fineCostModel (R0BinaryEnv cliIo.rd g)
      r0Opened1MiBCum r0Opened1MiBLive r0Opened1MiBPeak r0Opened1MiBMaxReq := by
  have hcap40 : ∀ bs,
      cliIo.rd (runFiles g.i) (pathOf StoresGhost.opened.identity.own.path (utf8 "address")) =
        .ok bs → bs.length ≤ 40 :=
    fun _ hrd => cliIo_rd_ownAddress_le_40_of_pqOrD3Recv hi hrd
  have hcapSess : ∀ bs,
      cliIo.rd (runFiles g.i) (pathOf StoresGhost.opened.identity.own.path (utf8 "address")) =
        .ok bs → bs.length ≤ sessionCapBytes :=
    fun bs hrd => Nat.le_trans (hcap40 bs hrd) (by unfold sessionCapBytes; decide)
  have hop : PhaseCreditSpec fineCostModel (R0OpenedEnv cliIo.rd (runFiles g.i))
      r0Opened1MiBCum r0Opened1MiBLive r0Opened1MiBPeak r0Opened1MiBMaxReq :=
    CliRunArmsPeak.r0Opened_phaseCredit_of_path fineCostModel_modelHyps
      (DirPeakSpec.path_phaseCredit fineCostModel_modelHyps
        (by decide : StoresGhost.opened.identity.own.path.length ≤ 26) utf8_address_length_le)
      hcapSess
  have hdg := dirGetEnv_path_readFile_fine_phaseCredit_tight cliIo.rd (runFiles g.i)
    StoresGhost.opened.identity.own (utf8 "address") dirDomainCaps_opened_own_64
    (Nat.le_trans utf8_address_length_le (by decide)) hcap40
  have hbin : PhaseCreditSpec fineCostModel
      (SeqEnv (DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd (runFiles g.i)
          StoresGhost.opened.identity.own (utf8 "address"))
        (PreAfterGetEnv g))
      r0Opened1MiBCum r0Opened1MiBLive r0Opened1MiBPeak r0Opened1MiBMaxReq :=
    (hdg.seq (preAfterGetEnv_fine_phaseCredit g)).mono
      (by decide) (by decide) (by decide) (by decide)
  exact (hop.or hbin).mono (max_self_le _) (max_self_le _) (max_self_le _) (max_self_le _)

private theorem r0BinaryEnv_fine_groupSpec_local (rd : ReadRule) (g : RunCall) :
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
        cases addrParse uuidTryParse ownB with
        | none => exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
        | some a => exact PhaseGroupSpec.rustAlloc_any fineCostModel a.name.length 1
      exact (haddr.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono
        (by generalize FineScale = fs; omega)
  have hbin : PhaseGroupSpec fineCostModel
      (SeqEnv (DirGetEnv PathEnv (ReadFileRuleEnv rd) rd (runFiles g.i)
          StoresGhost.opened.identity.own (utf8 "address"))
        (PreAfterGetEnv g))
      (42 * FineScale) :=
    (hdg.seq hafter).mono (by generalize FineScale = fs; omega)
  exact (hop.or hbin).mono (max_self_le _)

private theorem r3aBinaryEnv_fine_phaseCredit_local {rest : List (BitVec 8)}
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

private theorem r3aBinaryEnv_fine_groupSpec_local {rest : List (BitVec 8)}
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
  exact optStage_groupSpec (hsig.seq (optStage_groupSpec hdecFree))

private theorem pathEnv_groupSpec_local (dir name : List (BitVec 8)) :
    PhaseGroupSpec fineCostModel (PathEnv dir name) (9 * FineScale) := by
  unfold PathEnv pathEvents
  have h1 : PhaseGroupSpec fineCostModel (· = pathToOwnedEvents dir.length) (3 * FineScale) := by
    unfold pathToOwnedEvents
    split
    · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
    · exact PhaseGroupSpec.rustAlloc_any fineCostModel dir.length 1
  have h2 : PhaseGroupSpec fineCostModel (· = pathPushSlashEvents dir.length) (3 * FineScale) := by
    unfold pathPushSlashEvents
    split
    · exact PhaseGroupSpec.rustAlloc_any fineCostModel _ 1
    · exact PhaseGroupSpec.rustRealloc_any fineCostModel _ _ 1
  have h3 : PhaseGroupSpec fineCostModel (· = pathAppendNameEvents dir.length name.length)
      (3 * FineScale) := by
    unfold pathAppendNameEvents
    dsimp only
    split
    · exact PhaseGroupSpec.rustRealloc_any fineCostModel _ _ 1
    · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
  exact (phaseGroupSpec_append_eq fineCostModel h1
    (phaseGroupSpec_append_eq fineCostModel h2 h3)).mono (by generalize FineScale = fs; omega)

private theorem r1bFileStepEnv_fine_groupSpec_local (rd : ReadRule) (files : FsFiles)
    (dir name : List (BitVec 8)) :
    PhaseGroupSpec fineCostModel (R1bFileStepEnv rd files dir name) (42 * FineScale) := by
  have hp := optStage_groupSpec (pathEnv_groupSpec_local dir name)
  have hr := optStage_groupSpec
    (readFileRuleEnv_groupSpec fineCostModel rd files (dir ++ [0x2f#8] ++ name))
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
        (OptStageEnv
          (SeqEnv (fun e => e = rustAllocEvents 22 1 ∨ e = rustAllocEvents 14 1) FreeOnlyEvs)))
      (3 * FineScale) :=
    ((PhaseGroupSpec.freeOnly fineCostModel).seq (optStage_groupSpec herrFree)).mono
      (by generalize FineScale = fs; omega)
  exact (hp.seq (hr.seq htail)).mono (by generalize FineScale = fs; omega)

private theorem r1bDeserStageEnv_fine_groupSpec_local :
    PhaseGroupSpec fineCostModel R1bDeserStageEnv (9 * FineScale) := by
  have ha64 := optStage_groupSpec (PhaseGroupSpec.rustAlloc_any fineCostModel 64 1)
  have haKem := optStage_groupSpec (PhaseGroupSpec.rustAlloc_any fineCostModel kemPkLen 1)
  have ha64Seq : PhaseGroupSpec fineCostModel
      (SeqEnv (· = rustAllocEvents 64 1) FreeOnlyEvs) (3 * FineScale) :=
    ((PhaseGroupSpec.rustAlloc_any fineCostModel 64 1).seq
      (PhaseGroupSpec.freeOnly fineCostModel)).mono (by generalize FineScale = fs; omega)
  exact (ha64.seq (haKem.seq (optStage_groupSpec ha64Seq))).mono
    (by generalize FineScale = fs; omega)

private theorem splitId_fine_groupSpec_local (bs : List (BitVec 8)) :
    PhaseGroupSpec fineCostModel (SplitIdEnv bs) (3 * FineScale) :=
  ((PhaseGroupSpec.rustAlloc_any fineCostModel 14 1).seq
    (PhaseGroupSpec.freeOnly fineCostModel)).mono (by generalize FineScale = fs; omega)

private theorem splitSigned_fine_groupSpec_local (bs : List (BitVec 8)) :
    PhaseGroupSpec fineCostModel (SplitSignedEnv bs) (6 * FineScale) := by
  have h1 := splitId_fine_groupSpec_local bs
  exact (h1.seq (optStage_groupSpec h1)).mono (by generalize FineScale = fs; omega)

private theorem initArmBinaryEnv_fine_groupSpec_local (rd : ReadRule) (files : FsFiles)
    (dir : List (BitVec 8)) {InitEnv : List AllocEvent → Prop} {g_init : Nat}
    (hinit : PhaseGroupSpec fineCostModel InitEnv g_init) :
    PhaseGroupSpec fineCostModel (InitArmBinaryEnv rd files dir InitEnv)
      (234 * FineScale + g_init) := by
  have hop : PhaseGroupSpec fineCostModel (InitArmEnv rd files dir InitEnv)
      (234 * FineScale + g_init) :=
    (initArmEnv_fine_groupSpec rd files dir hinit).mono (by generalize FineScale = fs; omega)
  have hs1 := r1bFileStepEnv_fine_groupSpec_local rd files dir (utf8 "identity-key")
  have hs2 := r1bFileStepEnv_fine_groupSpec_local rd files dir (utf8 "registration-id")
  have hs3 := optStage_groupSpec
    (r1bFileStepEnv_fine_groupSpec_local rd files dir (utf8 "signed-pre-key"))
  have hs4 := optStage_groupSpec
    (r1bFileStepEnv_fine_groupSpec_local rd files dir (utf8 "kyber-pre-key"))
  have hs5 := optStage_groupSpec
    (r1bFileStepEnv_fine_groupSpec_local rd files dir (utf8 "one-time-pre-key"))
  have hss := optStage_groupSpec (splitSigned_fine_groupSpec_local [])
  have hsi := optStage_groupSpec (splitId_fine_groupSpec_local [])
  have hds := optStage_groupSpec r1bDeserStageEnv_fine_groupSpec_local
  have hr1b : PhaseGroupSpec fineCostModel (R1bBinaryEnv rd files dir) (192 * FineScale) :=
    (hs2.seq (hs3.seq (hss.seq (hs4.seq (hss.seq (hs5.seq (hsi.seq hds))))))).mono
      (by generalize FineScale = fs; omega)
  have hr1cSeq : PhaseGroupSpec fineCostModel (R1cEnv InitEnv) g_init :=
    (hinit.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono (by generalize FineScale = fs; omega)
  have hcore : PhaseGroupSpec fineCostModel (InitArmBinaryCoreEnv rd files dir InitEnv)
      (234 * FineScale + g_init) :=
    (hs1.seq ((optStage_groupSpec hr1b).seq (optStage_groupSpec hr1cSeq))).mono
      (by generalize FineScale = fs; omega)
  exact (hop.or hcore).mono (max_self_le _)

/-- Whole-`run` `PhaseCreditSpec fineCostModel` on `CliRunBinaryEnv` under `CliPqOrD3RecvInputs`. -/
theorem cliRunBinaryEnv_real_1MiB_fine_phaseCredit_of_pqOrD3Recv
    {P : PEParams} {E : RunCall → CliRunCalleeEnvs} {g : RunCall}
    (SE : CliRealCalleeFineSpecs (E g))
    (hi : CliPqxdhInputs P g.i ∨
      ∃ (st : PqParty) (ct : List (BitVec 8)) (rc : BitVec 256),
        PqxdhPartyInSpecDomain P st ∧ g.i = pqRecvInputs P st ct rc)
    (hstdin : g.i.stdin.length ≤ msgCapBytes)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c) :
    PhaseCreditSpec fineCostModel (CliRunBinaryEnv cliIo.rd (E g) sessionCapBytes g)
      (cliRunBinary1MiBCustomPksmCum SE.pksmCum SE.initCum SE.encCum SE.decSigCum SE.decPkCum)
      (cliRun1MiBCustomPksmLive SE.pksmLive SE.initLive SE.encLive SE.decSigLive SE.decPkLive)
      (cliRun1MiBCustomPksmPeak SE.pksmLive SE.pksmPeak
        SE.initPeak SE.encLive SE.encPeak SE.decSigPeak SE.decPkPeak)
      (cliRunBinary1MiBCustomPksmMaxReq SE.pksmMaxReq
        SE.initMaxReq SE.encMaxReq SE.decSigMaxReq SE.decPkMaxReq) := by
  rcases hi with hi_pq | ⟨st, ct, rc, hwf, hgi⟩
  · exact cliRunBinaryEnv_real_1MiB_fine_phaseCredit_of_cliPqInputs SE hi_pq hstdin hparse
  · have hr0 := r0BinaryEnv_fine_phaseCredit_of_pqOrD3Recv (Or.inr ⟨st, ct, rc, hwf, hgi⟩)
    have harg : g.i.argv = (Cmd.recv (partyAddress st.party.other)).argv := by rw [hgi]; rfl
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
        rw [harg, CryptoVerification.SignalSession.Cli.RunRefine.parseArgs_recv, hcmd] at hparse
        cases hparse
      | init _ _ =>
        rw [harg, CryptoVerification.SignalSession.Cli.RunRefine.parseArgs_recv, hcmd] at hparse
        cases hparse
      | send _ =>
        rw [harg, CryptoVerification.SignalSession.Cli.RunRefine.parseArgs_recv, hcmd] at hparse
        cases hparse
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
              exact (r3aBinaryEnv_fine_phaseCredit_local hrest SE.decSig_spec SE.decSig_lp).mono
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

/-- Parametric `grpCap` generalization of `CliSlotEnvelopeBridge.cliRunBinaryEnv_real_fine_groupSpec`. -/
theorem cliRunBinaryEnv_fine_groupSpec_of_cap
    {E : RunCall → CliRunCalleeEnvs} {g : RunCall} {grpCap : Nat}
    (SE : CliRealCalleeFineSpecs (E g))
    (hstdin : g.i.stdin.length ≤ msgCapBytes)
    (hge : 15 * FineScale ≤ grpCap)
    (hinit_sub : 234 * FineScale + SE.initGrpS ≤ grpCap - 15 * FineScale)
    (h5 : cliRunOpenedCustomPksmGrpS msgCapBytes SE.pksmGrpS
      SE.initGrpS SE.encGrpS SE.decSigGrpS SE.decPkGrpS ≤ grpCap) :
    PhaseGroupSpec fineCostModel
      (CliRunBinaryEnv cliIo.rd (E g) sessionCapBytes g)
      (grpCap + 27 * FineScale) := by
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
      exact (initArmBinaryEnv_fine_groupSpec_local cliIo.rd (runFiles g.i) dir SE.init_grp).mono
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
            exact (r3aBinaryEnv_fine_groupSpec_local hrest SE.decSig_grp).mono (Nat.le_max_left _ _)
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
          (SE.pksmGrpS + SE.decPkGrpS)) ≤ grpCap - 15 * FineScale := by
    unfold cliRunOpenedCustomPksmGrpS at h5
    generalize FineScale = fs at h5 ⊢
    omega
  exact (cliRunOfR0_fine_groupSpec (r0BinaryEnv_fine_groupSpec_local cliIo.rd g) harm).mono (by
    have hmax := Nat.max_le.mpr ⟨hinit_sub, hrest_sub⟩
    generalize FineScale = fs at hmax hge ⊢
    omega)

/-! ## 3. Whole-`main` `RealCliMainBinaryEnvOf` D3 `recv` `FitsEnv` (`cliBudgetLimits`) -/

private theorem d3RecvCalleeFineSpecs_binary_cum_req_bounds [LibsignalPlacement]
    (img : Image) (S : RunSem) {P : PEParams}
    {DecPkEnv : RunCall → List AllocEvent → Prop} {g : RunCall}
    (S_pk : SingleSlotFineSpec (DecPkEnv g))
    (hpc : S_pk.cum ≤ w4RecvPrekeyReal1MiB_i_Cum)
    (hpr : S_pk.maxReq ≤ w4RecvPrekeyReal1MiB_i_MaxReq)
    (hi : CliPqxdhInputs P g.i ∨
      ∃ (st : PqParty) (ct : List (BitVec 8)) (rc : BitVec 256),
        PqxdhPartyInSpecDomain P st ∧ g.i = pqRecvInputs P st ct rc)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c) :
    let SE := d3RecvCalleeFineSpecs img S S_pk hi hparse
    cliRunBinary1MiBCustomPksmCum SE.pksmCum SE.initCum SE.encCum SE.decSigCum SE.decPkCum ≤
      cliD3DirectRunCum_i ∧
    cliRunBinary1MiBCustomPksmMaxReq SE.pksmMaxReq SE.initMaxReq SE.encMaxReq
      SE.decSigMaxReq SE.decPkMaxReq ≤ cliRealDirectRunMaxReq_i := by
  dsimp only [d3RecvCalleeFineSpecs]
  have hi_cum : max (initArmDeltaCum (pathDeltaCum 26 16) 1637 w3InitRealCum)
      (initArmBinaryPrefixCum + w3InitRealCum) ≤
      max (r2TightDeltaCum w1SendRealDcanCum sessionCapBytes)
        (max (sigSliceCum msgCapBytes + w2RecvWhisperRealDcanCum)
          (CliRunArmsPeak.pksmSliceCum msgCapBytes + w4RecvPrekeyReal1MiB_i_Cum)) := by decide
  have hi_req : max (initArmMaxReq (pathMaxReq 26 16) 1637 w3InitRealMaxReq)
      (max (fineReadFileMaxReq 1637) w3InitRealMaxReq) ≤
      max (r2MaxReq w1SendRealDcanMaxReq sessionCapBytes)
        (max (max (sigSliceMaxReq msgCapBytes) w2RecvWhisperRealDcanMaxReq)
          (max CliTopBudgetReal.cliRealPksmReqCap w4RecvPrekeyReal1MiB_i_MaxReq)) := by decide
  refine ⟨?_, ?_⟩
  · unfold cliD3DirectRunCum_i cliRunBinary1MiBCustomPksmCum cliRun1MiBCustomPksmCum
    exact Nat.add_le_add_left (Nat.max_le.mpr
      ⟨Nat.le_trans hi_cum (Nat.le_max_right _ _),
       Nat.le_trans (max_mono (Nat.le_refl _) (max_mono (Nat.le_refl _)
         (Nat.add_le_add_left hpc _))) (Nat.le_max_right _ _)⟩) _
  · unfold cliRealDirectRunMaxReq_i cliRunBinary1MiBCustomPksmMaxReq cliRun1MiBCustomPksmMaxReq
    have hpk_req : CliRunArmsPeak.pksmSliceMaxReq msgCapBytes ≤
        CliTopBudgetReal.cliRealPksmReqCap := by decide
    exact max_mono (Nat.le_refl _) (Nat.max_le.mpr
      ⟨Nat.le_trans hi_req (Nat.le_max_right _ _),
       Nat.le_trans (max_mono (Nat.le_refl _) (max_mono (Nat.le_refl _)
         (max_mono hpk_req hpr))) (Nat.le_max_right _ _)⟩)

/-- Call-contextual whole-`main` `PhaseCreditSpec fineCostModel` on
`RealCliMainBinaryEnvOf (mkD3RecvCalleeEnvs img S P DecPkEnv) i`. -/
theorem realCliMainBinaryEnvOf_phaseCredit_fine_pqRecv_d3_of_callSpecs [LibsignalPlacement]
    (img : Image) (S : RunSem) {P : PEParams}
    {DecPkEnv : RunCall → List AllocEvent → Prop}
    (S_pk : ∀ (g : RunCall),
      (CliPqxdhInputs P g.i ∨
        ∃ (st : PqParty) (ct : List (BitVec 8)) (rc : BitVec 256),
          PqxdhPartyInSpecDomain P st ∧ g.i = pqRecvInputs P st ct rc) →
      g.i.stdin.length ≤ msgCapBytes →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      SingleSlotFineSpec (DecPkEnv g))
    (hCaps : ∀ (g : RunCall)
      (hi_g : CliPqxdhInputs P g.i ∨
        ∃ (st : PqParty) (ct : List (BitVec 8)) (rc : BitVec 256),
          PqxdhPartyInSpecDomain P st ∧ g.i = pqRecvInputs P st ct rc)
      (hstdin : g.i.stdin.length ≤ msgCapBytes)
      (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c),
      (S_pk g hi_g hstdin hparse).cum ≤ w4RecvPrekeyReal1MiB_i_Cum ∧
      (S_pk g hi_g hstdin hparse).live ≤ w4RecvPrekeyReal1MiB_i_Live ∧
      (S_pk g hi_g hstdin hparse).peak ≤ w4RecvPrekeyReal1MiB_i_Peak ∧
      (S_pk g hi_g hstdin hparse).maxReq ≤ w4RecvPrekeyReal1MiB_i_MaxReq ∧
      (S_pk g hi_g hstdin hparse).grpS ≤ w4RecvPrekeyRealGrpS)
    {i : Inputs}
    (hi : CliPqxdhInputs P i ∨
      ∃ (st : PqParty) (ct : List (BitVec 8)) (rc : BitVec 256),
        PqxdhPartyInSpecDomain P st ∧ i = pqRecvInputs P st ct rc) :
    PhaseCreditSpec fineCostModel (RealCliMainBinaryEnvOf (mkD3RecvCalleeEnvs img S P DecPkEnv) i)
      cliD3BinaryMainCum cliD3MainLive cliD3MainPeak cliD3MainReq := by
  have hsm1024 : 1024 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have hw (w : ValidPostSetupWitness i) : PhaseCreditSpec fineCostModel
      (SeqEnv (CliRunBinaryEnv cliIo.rd (mkD3RecvCalleeEnvs img S P DecPkEnv w.g)
          sessionCapBytes w.g)
        (SeqEnv (M5PhaseEnv w.dirs) (M6Env w.ok)))
      (cliD3DirectRunCum_i + cliMaxDirtyEntries *
        (10 * max (4 * cliMaxDirPathBytes + cliMaxAddrTextBytes + 16) 16 + 4 * 9539) + m6DeltaCum)
      cliRealDirectRunLive_i
      (max cliRealDirectRunPeak_i
        (cliRealDirectRunLive_i + m5DirStepDeltaPeak cliMaxDirPathBytes cliMaxAddrTextBytes))
      (max cliRealDirectRunMaxReq_i
        (max 1024 (m5DirStepMaxReq cliMaxDirPathBytes cliMaxAddrTextBytes))) := by
    have hi_g := w.g_i.symm ▸ hi
    let Spk := S_pk w.g hi_g w.stdin_le w.parse_ok
    let SE := d3RecvCalleeFineSpecs img S Spk hi_g w.parse_ok
    have hc := hCaps w.g hi_g w.stdin_le w.parse_ok
    obtain ⟨h1_cum, h1_req⟩ :=
      d3RecvCalleeFineSpecs_binary_cum_req_bounds img S Spk hc.1 hc.2.2.2.1 hi_g w.parse_ok
    obtain ⟨_, h2, h3, _, _⟩ :=
      d3RecvCalleeFineSpecs_direct_run_bounds img S Spk hc hi_g w.parse_ok
    have hrun :=
      (cliRunBinaryEnv_real_1MiB_fine_phaseCredit_of_pqOrD3Recv SE hi_g w.stdin_le
        w.parse_ok).mono h1_cum h2 h3 h1_req
    refine (hrun.seq ((m5Phase_Bounded_phaseCredit_fine w.dirs_sum_le w.dirs_bounds).seq
      (m6_phaseCredit_small1024 fineCostModel_modelHyps hsm1024 w.ok))).mono ?_ ?_ ?_ ?_
    · rw [Nat.add_assoc]; exact Nat.le_refl _
    · simp only [Nat.add_zero]; exact Nat.le_refl _
    · exact max_mono (Nat.le_refl _)
        (Nat.add_le_add_left (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.zero_le _⟩) _)
    · exact max_mono (Nat.le_refl _) (Nat.le_of_eq (Nat.max_comm _ _))
  have hex : PhaseCreditSpec fineCostModel
      (fun evs' => ∃ w : ValidPostSetupWitness i, w.g.i = i ∧
        SeqEnv (CliRunBinaryEnv cliIo.rd (mkD3RecvCalleeEnvs img S P DecPkEnv w.g)
            sessionCapBytes w.g)
          (SeqEnv (M5PhaseEnv w.dirs) (M6Env w.ok)) evs')
      (cliD3DirectRunCum_i + cliMaxDirtyEntries *
        (10 * max (4 * cliMaxDirPathBytes + cliMaxAddrTextBytes + 16) 16 + 4 * 9539) + m6DeltaCum)
      cliRealDirectRunLive_i
      (max cliRealDirectRunPeak_i
        (cliRealDirectRunLive_i + m5DirStepDeltaPeak cliMaxDirPathBytes cliMaxAddrTextBytes))
      (max cliRealDirectRunMaxReq_i
        (max 1024 (m5DirStepMaxReq cliMaxDirPathBytes cliMaxAddrTextBytes))) :=
    { req_align := fun evs ⟨w, _, hseq⟩ ev hev => (hw w).req_align evs hseq ev hev
      credit_le := fun st0 {_} ⟨w, _, hseq⟩ => (hw w).credit_le st0 hseq }
  have htail := optStage_phaseCredit hex
  refine ((cliMainBoundedSetup_phaseCredit_fine (argv_length_le_3_of_pqOrD3Recv hi)).seq htail).mono
    ?_ ?_ ?_ ?_
  · unfold cliD3BinaryMainCum; simp only [Nat.add_assoc]; exact Nat.le_refl _
  · unfold cliD3MainLive cliMainTightLiveOf cliMainDeltaLive_tight; exact Nat.le_refl _
  · unfold cliD3MainPeak cliMainTightPeakOf cliMainDeltaPeak_tight; exact Nat.le_refl _
  · unfold cliD3MainReq cliMainTightReqOf cliMainMaxReq
    have h16k : max 16384 (m3PhaseMaxReq msgCapBytes sessionCapBytes) =
        m3PhaseMaxReq msgCapBytes sessionCapBytes := by
      unfold m3PhaseMaxReq msgCapBytes sessionCapBytes; decide
    rw [h16k]
    exact Nat.le_max_right _ _

/-- Call-contextual whole-`main` `PhaseGroupSpec fineCostModel` on
`RealCliMainBinaryEnvOf (mkD3RecvCalleeEnvs img S P DecPkEnv) i`. -/
theorem realCliMainBinaryEnvOf_fine_groupSpec_pqRecv_d3_of_callSpecs [LibsignalPlacement]
    (img : Image) (S : RunSem) {P : PEParams}
    {DecPkEnv : RunCall → List AllocEvent → Prop}
    (S_pk : ∀ (g : RunCall),
      (CliPqxdhInputs P g.i ∨
        ∃ (st : PqParty) (ct : List (BitVec 8)) (rc : BitVec 256),
          PqxdhPartyInSpecDomain P st ∧ g.i = pqRecvInputs P st ct rc) →
      g.i.stdin.length ≤ msgCapBytes →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      SingleSlotFineSpec (DecPkEnv g))
    (hCaps : ∀ (g : RunCall)
      (hi_g : CliPqxdhInputs P g.i ∨
        ∃ (st : PqParty) (ct : List (BitVec 8)) (rc : BitVec 256),
          PqxdhPartyInSpecDomain P st ∧ g.i = pqRecvInputs P st ct rc)
      (hstdin : g.i.stdin.length ≤ msgCapBytes)
      (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c),
      (S_pk g hi_g hstdin hparse).cum ≤ w4RecvPrekeyReal1MiB_i_Cum ∧
      (S_pk g hi_g hstdin hparse).live ≤ w4RecvPrekeyReal1MiB_i_Live ∧
      (S_pk g hi_g hstdin hparse).peak ≤ w4RecvPrekeyReal1MiB_i_Peak ∧
      (S_pk g hi_g hstdin hparse).maxReq ≤ w4RecvPrekeyReal1MiB_i_MaxReq ∧
      (S_pk g hi_g hstdin hparse).grpS ≤ w4RecvPrekeyRealGrpS)
    {i : Inputs}
    (hi : CliPqxdhInputs P i ∨
      ∃ (st : PqParty) (ct : List (BitVec 8)) (rc : BitVec 256),
        PqxdhPartyInSpecDomain P st ∧ i = pqRecvInputs P st ct rc) :
    PhaseGroupSpec fineCostModel (RealCliMainBinaryEnvOf (mkD3RecvCalleeEnvs img S P DecPkEnv) i)
      cliD3BinaryMainGrpS := by
  have hex : PhaseGroupSpec fineCostModel
      (fun evs' => ∃ w : ValidPostSetupWitness i, w.g.i = i ∧
        SeqEnv (CliRunBinaryEnv cliIo.rd (mkD3RecvCalleeEnvs img S P DecPkEnv w.g)
            sessionCapBytes w.g)
          (SeqEnv (M5PhaseEnv w.dirs) (M6Env w.ok)) evs')
      (cliD3BinaryDirectRunGrpS_i + cliMaxDirtyEntries * (12 * FineScale) + 3 * FineScale) :=
    { groups_le := fun st0 {_} ⟨w, _, hseq⟩ => by
        have hi_g := w.g_i.symm ▸ hi
        let Spk := S_pk w.g hi_g w.stdin_le w.parse_ok
        let SE := d3RecvCalleeFineSpecs img S Spk hi_g w.parse_ok
        obtain ⟨_, _, _, _, h5⟩ :=
          d3RecvCalleeFineSpecs_direct_run_bounds img S Spk
            (hCaps w.g hi_g w.stdin_le w.parse_ok) hi_g w.parse_ok
        have hinit_sub : 234 * FineScale + SE.initGrpS ≤ cliD3DirectRunGrpS_i - 15 * FineScale := by
          dsimp only [SE, d3RecvCalleeFineSpecs]; decide
        have hrun := cliRunBinaryEnv_fine_groupSpec_of_cap SE w.stdin_le
          (by decide : 15 * FineScale ≤ cliD3DirectRunGrpS_i) hinit_sub h5
        have hm5 := (m5PhaseEnv_groupSpec fineCostModel w.dirs).mono
          (Nat.mul_le_mul_right (12 * FineScale) w.dirs_sum_le)
        have htot : PhaseGroupSpec fineCostModel
            (SeqEnv (CliRunBinaryEnv cliIo.rd (mkD3RecvCalleeEnvs img S P DecPkEnv w.g)
                sessionCapBytes w.g)
              (SeqEnv (M5PhaseEnv w.dirs) (M6Env w.ok)))
            (cliD3BinaryDirectRunGrpS_i + cliMaxDirtyEntries * (12 * FineScale) + 3 * FineScale) :=
          (hrun.seq (hm5.seq (m6Env_groupSpec fineCostModel w.ok))).mono
            (by unfold cliD3BinaryDirectRunGrpS_i; generalize FineScale = fs; omega)
        exact htot.groups_le st0 hseq }
  exact ((cliMainBoundedSetup_fine_groupSpec (argv_length_le_3_of_pqOrD3Recv hi)).seq
    (optStage_groupSpec hex)).mono
    (by unfold cliD3BinaryMainGrpS; generalize FineScale = fs; omega)

/-- Call-contextual `cliBudgetLimits` (`1 GiB`) whole-`main` `RealCliMainBinaryEnvOf` `FitsEnv`. -/
theorem realCliMainBinaryEnvOf_fitsEnv_cliBudgetLimits_pqRecv_d3_of_callSpecs [LibsignalPlacement]
    (img : Image) (S : RunSem) (P : PEParams)
    {DecPkEnv : RunCall → List AllocEvent → Prop}
    (S_pk : ∀ (g : RunCall),
      (CliPqxdhInputs P g.i ∨
        ∃ (st : PqParty) (ct : List (BitVec 8)) (rc : BitVec 256),
          PqxdhPartyInSpecDomain P st ∧ g.i = pqRecvInputs P st ct rc) →
      g.i.stdin.length ≤ msgCapBytes →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      SingleSlotFineSpec (DecPkEnv g))
    (hCaps : ∀ (g : RunCall)
      (hi_g : CliPqxdhInputs P g.i ∨
        ∃ (st : PqParty) (ct : List (BitVec 8)) (rc : BitVec 256),
          PqxdhPartyInSpecDomain P st ∧ g.i = pqRecvInputs P st ct rc)
      (hstdin : g.i.stdin.length ≤ msgCapBytes)
      (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c),
      (S_pk g hi_g hstdin hparse).cum ≤ w4RecvPrekeyReal1MiB_i_Cum ∧
      (S_pk g hi_g hstdin hparse).live ≤ w4RecvPrekeyReal1MiB_i_Live ∧
      (S_pk g hi_g hstdin hparse).peak ≤ w4RecvPrekeyReal1MiB_i_Peak ∧
      (S_pk g hi_g hstdin hparse).maxReq ≤ w4RecvPrekeyReal1MiB_i_MaxReq ∧
      (S_pk g hi_g hstdin hparse).grpS ≤ w4RecvPrekeyRealGrpS) :
    ∀ i : Inputs,
      (CliPqxdhInputs P i ∨
        ∃ (st : PqParty) (ct : List (BitVec 8)) (rc : BitVec 256),
          PqxdhPartyInSpecDomain P st ∧ i = pqRecvInputs P st ct rc) →
      FitsEnv fineCostModel cliBudgetLimits fineCostModel.init
        (RealCliMainBinaryEnvOf (mkD3RecvCalleeEnvs img S P DecPkEnv) i) := by
  intro i hi
  obtain ⟨hlp, hram, hva⟩ := cliD3BinaryMain_arith_bounds (lim := cliBudgetLimits)
    (Nat.le_refl _) (Nat.le_refl _) (by unfold cliBudgetLimits cliOneGiB; decide)
  exact fitsEnv_fineCostModel_of_group_literal_bounds
    (realCliMainBinaryEnvOf_phaseCredit_fine_pqRecv_d3_of_callSpecs img S S_pk hCaps hi)
    (realCliMainBinaryEnvOf_fine_groupSpec_pqRecv_d3_of_callSpecs img S S_pk hCaps hi)
    (Nat.le_refl _) hlp (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) rfl hram hva

/-- Call-contextual `PhaseCreditSpec` + `PhaseGroupSpec` companion of
`realCliMainBinaryEnvOf_fitsEnv_cliBudgetLimits_pqRecv_d3_of_callSpecs`. -/
theorem realCliMainBinaryEnvOf_fitsEnv_cliBudgetLimits_pqRecv_d3_of_callPhaseSpecs
    [LibsignalPlacement]
    (img : Image) (S : RunSem) (P : PEParams)
    {DecPkEnv : RunCall → List AllocEvent → Prop}
    (hCredit : ∀ (g : RunCall),
      (CliPqxdhInputs P g.i ∨
        ∃ (st : PqParty) (ct : List (BitVec 8)) (rc : BitVec 256),
          PqxdhPartyInSpecDomain P st ∧ g.i = pqRecvInputs P st ct rc) →
      g.i.stdin.length ≤ msgCapBytes →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      PhaseCreditSpec fineCostModel (DecPkEnv g)
        w4RecvPrekeyReal1MiB_i_Cum w4RecvPrekeyReal1MiB_i_Live
        w4RecvPrekeyReal1MiB_i_Peak w4RecvPrekeyReal1MiB_i_MaxReq)
    (hGrp : ∀ (g : RunCall),
      (CliPqxdhInputs P g.i ∨
        ∃ (st : PqParty) (ct : List (BitVec 8)) (rc : BitVec 256),
          PqxdhPartyInSpecDomain P st ∧ g.i = pqRecvInputs P st ct rc) →
      g.i.stdin.length ≤ msgCapBytes →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      PhaseGroupSpec fineCostModel (DecPkEnv g) w4RecvPrekeyRealGrpS) :
    ∀ i : Inputs,
      (CliPqxdhInputs P i ∨
        ∃ (st : PqParty) (ct : List (BitVec 8)) (rc : BitVec 256),
          PqxdhPartyInSpecDomain P st ∧ i = pqRecvInputs P st ct rc) →
      FitsEnv fineCostModel cliBudgetLimits fineCostModel.init
        (RealCliMainBinaryEnvOf (mkD3RecvCalleeEnvs img S P DecPkEnv) i) :=
  realCliMainBinaryEnvOf_fitsEnv_cliBudgetLimits_pqRecv_d3_of_callSpecs img S P
    (fun g hi_g hstdin hparse =>
      { cum := w4RecvPrekeyReal1MiB_i_Cum
        live := w4RecvPrekeyReal1MiB_i_Live
        peak := w4RecvPrekeyReal1MiB_i_Peak
        maxReq := w4RecvPrekeyReal1MiB_i_MaxReq
        grpS := w4RecvPrekeyRealGrpS
        credit := hCredit g hi_g hstdin hparse
        live_le_peak := w4RecvPrekeyReal1MiB_i_eq.2.2.2.2
        groups := hGrp g hi_g hstdin hparse })
    (fun _ _ _ _ => ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩)

/-- Inclusion-pullback `cliBudgetLimits` (`1 GiB`) whole-`main` `RealCliMainBinaryEnvOf` `FitsEnv`
from `W4RecvPrekeyRealSlotEnv`. -/
theorem realCliMainBinaryEnvOf_fitsEnv_cliBudgetLimits_pqRecv_d3_of_mem_w4 [LibsignalPlacement]
    (img : Image) (S : RunSem) (P : PEParams)
    {DecPkEnv : RunCall → List AllocEvent → Prop}
    (hMem : ∀ (g : RunCall),
      (CliPqxdhInputs P g.i ∨
        ∃ (st : PqParty) (ct : List (BitVec 8)) (rc : BitVec 256),
          PqxdhPartyInSpecDomain P st ∧ g.i = pqRecvInputs P st ct rc) →
      g.i.stdin.length ≤ msgCapBytes →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      ∀ evs, DecPkEnv g evs → (mkExistentialRealCalleeEnvs img S P g).decPkEnv evs) :
    ∀ i : Inputs,
      (CliPqxdhInputs P i ∨
        ∃ (st : PqParty) (ct : List (BitVec 8)) (rc : BitVec 256),
          PqxdhPartyInSpecDomain P st ∧ i = pqRecvInputs P st ct rc) →
      FitsEnv fineCostModel cliBudgetLimits fineCostModel.init
        (RealCliMainBinaryEnvOf (mkD3RecvCalleeEnvs img S P DecPkEnv) i) :=
  realCliMainBinaryEnvOf_fitsEnv_cliBudgetLimits_pqRecv_d3_of_callPhaseSpecs img S P
    (fun g hi_g hstdin hparse =>
      PhaseCreditSpec.of_imp (hMem g hi_g hstdin hparse) (existentialW4_credit img S P g))
    (fun g hi_g hstdin hparse =>
      PhaseGroupSpec.of_imp (existentialW4_groups img S P g) (hMem g hi_g hstdin hparse))

/-- Call-independent `SingleSlotFineSpec` companion of
`realCliMainBinaryEnvOf_fitsEnv_cliBudgetLimits_pqRecv_d3_of_callSpecs`. -/
theorem realCliMainBinaryEnvOf_fitsEnv_cliBudgetLimits_pqRecv_d3_of_specs [LibsignalPlacement]
    (img : Image) (S : RunSem) (P : PEParams)
    {DecPkEnv : RunCall → List AllocEvent → Prop}
    (S_pk : ∀ g : RunCall, SingleSlotFineSpec (DecPkEnv g))
    (hCaps : ∀ g : RunCall,
      (S_pk g).cum ≤ w4RecvPrekeyReal1MiB_i_Cum ∧
      (S_pk g).live ≤ w4RecvPrekeyReal1MiB_i_Live ∧
      (S_pk g).peak ≤ w4RecvPrekeyReal1MiB_i_Peak ∧
      (S_pk g).maxReq ≤ w4RecvPrekeyReal1MiB_i_MaxReq ∧
      (S_pk g).grpS ≤ w4RecvPrekeyRealGrpS) :
    ∀ i : Inputs,
      (CliPqxdhInputs P i ∨
        ∃ (st : PqParty) (ct : List (BitVec 8)) (rc : BitVec 256),
          PqxdhPartyInSpecDomain P st ∧ i = pqRecvInputs P st ct rc) →
      FitsEnv fineCostModel cliBudgetLimits fineCostModel.init
        (RealCliMainBinaryEnvOf (mkD3RecvCalleeEnvs img S P DecPkEnv) i) :=
  realCliMainBinaryEnvOf_fitsEnv_cliBudgetLimits_pqRecv_d3_of_callSpecs img S P
    (fun g _ _ _ => S_pk g) (fun g _ _ _ => hCaps g)

/-- Call-independent `PhaseCreditSpec` + `PhaseGroupSpec` companion of
`realCliMainBinaryEnvOf_fitsEnv_cliBudgetLimits_pqRecv_d3_of_specs`. -/
theorem realCliMainBinaryEnvOf_fitsEnv_cliBudgetLimits_pqRecv_d3_of_phaseSpecs [LibsignalPlacement]
    (img : Image) (S : RunSem) (P : PEParams)
    {DecPkEnv : RunCall → List AllocEvent → Prop}
    (hCredit : ∀ g : RunCall, PhaseCreditSpec fineCostModel (DecPkEnv g)
      w4RecvPrekeyReal1MiB_i_Cum w4RecvPrekeyReal1MiB_i_Live
      w4RecvPrekeyReal1MiB_i_Peak w4RecvPrekeyReal1MiB_i_MaxReq)
    (hGrp : ∀ g : RunCall, PhaseGroupSpec fineCostModel (DecPkEnv g) w4RecvPrekeyRealGrpS) :
    ∀ i : Inputs,
      (CliPqxdhInputs P i ∨
        ∃ (st : PqParty) (ct : List (BitVec 8)) (rc : BitVec 256),
          PqxdhPartyInSpecDomain P st ∧ i = pqRecvInputs P st ct rc) →
      FitsEnv fineCostModel cliBudgetLimits fineCostModel.init
        (RealCliMainBinaryEnvOf (mkD3RecvCalleeEnvs img S P DecPkEnv) i) :=
  realCliMainBinaryEnvOf_fitsEnv_cliBudgetLimits_pqRecv_d3_of_callPhaseSpecs img S P
    (fun g _ _ _ => hCredit g) (fun g _ _ _ => hGrp g)

/-- Concrete `cliBudgetLimits` (`1 GiB`) whole-`main` `RealCliMainBinaryEnvOf` `FitsEnv` at
`mkExistentialD3RecvCalleeEnvs img S P`. -/
theorem realCliMainBinaryEnvOf_fitsEnv_cliBudgetLimits_pqRecv_d3 [LibsignalPlacement]
    (img : Image) (S : RunSem) (P : PEParams) :
    ∀ i : Inputs,
      (CliPqxdhInputs P i ∨
        ∃ (st : PqParty) (ct : List (BitVec 8)) (rc : BitVec 256),
          PqxdhPartyInSpecDomain P st ∧ i = pqRecvInputs P st ct rc) →
      FitsEnv fineCostModel cliBudgetLimits fineCostModel.init
        (RealCliMainBinaryEnvOf (mkExistentialD3RecvCalleeEnvs img S P) i) :=
  realCliMainBinaryEnvOf_fitsEnv_cliBudgetLimits_pqRecv_d3_of_phaseSpecs img S P
    (existentialW4_credit img S P) (existentialW4_groups img S P)

/-! ### 3b. Extended `1 GiB` `W4` Ceilings (`d3RecvW4Ext*`) -/

private theorem d3RecvCalleeFineSpecs_ext_binary_cum_req_bounds [LibsignalPlacement]
    (img : Image) (S : RunSem) {P : PEParams}
    {DecPkEnv : RunCall → List AllocEvent → Prop} {g : RunCall}
    (S_pk : SingleSlotFineSpec (DecPkEnv g))
    (hpc : S_pk.cum ≤ d3RecvW4ExtCum)
    (hpr : S_pk.maxReq ≤ d3RecvW4ExtMaxReq)
    (hi : CliPqxdhInputs P g.i ∨
      ∃ (st : PqParty) (ct : List (BitVec 8)) (rc : BitVec 256),
        PqxdhPartyInSpecDomain P st ∧ g.i = pqRecvInputs P st ct rc)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c) :
    let SE := d3RecvCalleeFineSpecs img S S_pk hi hparse
    cliRunBinary1MiBCustomPksmCum SE.pksmCum SE.initCum SE.encCum SE.decSigCum SE.decPkCum ≤
      cliD3ExtRunCum ∧
    cliRunBinary1MiBCustomPksmMaxReq SE.pksmMaxReq SE.initMaxReq SE.encMaxReq
      SE.decSigMaxReq SE.decPkMaxReq ≤ cliD3ExtRunMaxReq := by
  dsimp only [d3RecvCalleeFineSpecs]
  have hi_cum : max (initArmDeltaCum (pathDeltaCum 26 16) 1637 w3InitRealCum)
      (initArmBinaryPrefixCum + w3InitRealCum) ≤
      max (r2TightDeltaCum w1SendRealDcanCum sessionCapBytes)
        (max (sigSliceCum msgCapBytes + w2RecvWhisperRealDcanCum)
          (CliRunArmsPeak.pksmSliceCum msgCapBytes + d3RecvW4ExtCum)) := by decide
  have hi_req : max (initArmMaxReq (pathMaxReq 26 16) 1637 w3InitRealMaxReq)
      (max (fineReadFileMaxReq 1637) w3InitRealMaxReq) ≤
      max (r2MaxReq w1SendRealDcanMaxReq sessionCapBytes)
        (max (max (sigSliceMaxReq msgCapBytes) w2RecvWhisperRealDcanMaxReq)
          (max CliTopBudgetReal.cliRealPksmReqCap d3RecvW4ExtMaxReq)) := by decide
  refine ⟨?_, ?_⟩
  · unfold cliD3ExtRunCum cliRunBinary1MiBCustomPksmCum cliRun1MiBCustomPksmCum
    exact Nat.add_le_add_left (Nat.max_le.mpr
      ⟨Nat.le_trans hi_cum (Nat.le_max_right _ _),
       Nat.le_trans (max_mono (Nat.le_refl _) (max_mono (Nat.le_refl _)
         (Nat.add_le_add_left hpc _))) (Nat.le_max_right _ _)⟩) _
  · unfold cliD3ExtRunMaxReq cliRunBinary1MiBCustomPksmMaxReq cliRun1MiBCustomPksmMaxReq
    have hpk_req : CliRunArmsPeak.pksmSliceMaxReq msgCapBytes ≤
        CliTopBudgetReal.cliRealPksmReqCap := by decide
    exact max_mono (Nat.le_refl _) (Nat.max_le.mpr
      ⟨Nat.le_trans hi_req (Nat.le_max_right _ _),
       Nat.le_trans (max_mono (Nat.le_refl _) (max_mono (Nat.le_refl _)
         (max_mono hpk_req hpr))) (Nat.le_max_right _ _)⟩)

/-- Extended-ceiling (`d3RecvW4Ext*`) call-contextual `cliBudgetLimits` (`1 GiB`) whole-`main`
`RealCliMainBinaryEnvOf` `FitsEnv`. -/
theorem realCliMainBinaryEnvOf_fitsEnv_cliBudgetLimits_pqRecv_d3_of_callSpecs_1GiB
    [LibsignalPlacement]
    (img : Image) (S : RunSem) (P : PEParams)
    {DecPkEnv : RunCall → List AllocEvent → Prop}
    (S_pk : ∀ (g : RunCall),
      (CliPqxdhInputs P g.i ∨
        ∃ (st : PqParty) (ct : List (BitVec 8)) (rc : BitVec 256),
          PqxdhPartyInSpecDomain P st ∧ g.i = pqRecvInputs P st ct rc) →
      g.i.stdin.length ≤ msgCapBytes →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      SingleSlotFineSpec (DecPkEnv g))
    (hCaps : ∀ (g : RunCall)
      (hi_g : CliPqxdhInputs P g.i ∨
        ∃ (st : PqParty) (ct : List (BitVec 8)) (rc : BitVec 256),
          PqxdhPartyInSpecDomain P st ∧ g.i = pqRecvInputs P st ct rc)
      (hstdin : g.i.stdin.length ≤ msgCapBytes)
      (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c),
      (S_pk g hi_g hstdin hparse).cum ≤ d3RecvW4ExtCum ∧
      (S_pk g hi_g hstdin hparse).live ≤ d3RecvW4ExtLive ∧
      (S_pk g hi_g hstdin hparse).peak ≤ d3RecvW4ExtPeak ∧
      (S_pk g hi_g hstdin hparse).maxReq ≤ d3RecvW4ExtMaxReq ∧
      (S_pk g hi_g hstdin hparse).grpS ≤ d3RecvW4ExtGrpS) :
    ∀ i : Inputs,
      (CliPqxdhInputs P i ∨
        ∃ (st : PqParty) (ct : List (BitVec 8)) (rc : BitVec 256),
          PqxdhPartyInSpecDomain P st ∧ i = pqRecvInputs P st ct rc) →
      FitsEnv fineCostModel cliBudgetLimits fineCostModel.init
        (RealCliMainBinaryEnvOf (mkD3RecvCalleeEnvs img S P DecPkEnv) i) := by
  intro i hi
  have hsm1024 : 1024 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have hw (w : ValidPostSetupWitness i) : PhaseCreditSpec fineCostModel
      (SeqEnv (CliRunBinaryEnv cliIo.rd (mkD3RecvCalleeEnvs img S P DecPkEnv w.g)
          sessionCapBytes w.g)
        (SeqEnv (M5PhaseEnv w.dirs) (M6Env w.ok)))
      (cliD3ExtRunCum + cliMaxDirtyEntries *
        (10 * max (4 * cliMaxDirPathBytes + cliMaxAddrTextBytes + 16) 16 + 4 * 9539) + m6DeltaCum)
      cliD3ExtRunLive
      (max cliD3ExtRunPeak
        (cliD3ExtRunLive + m5DirStepDeltaPeak cliMaxDirPathBytes cliMaxAddrTextBytes))
      (max cliD3ExtRunMaxReq
        (max 1024 (m5DirStepMaxReq cliMaxDirPathBytes cliMaxAddrTextBytes))) := by
    have hi_g := w.g_i.symm ▸ hi
    let Spk := S_pk w.g hi_g w.stdin_le w.parse_ok
    let SE := d3RecvCalleeFineSpecs img S Spk hi_g w.parse_ok
    have hc := hCaps w.g hi_g w.stdin_le w.parse_ok
    obtain ⟨h1_cum, h1_req⟩ :=
      d3RecvCalleeFineSpecs_ext_binary_cum_req_bounds img S Spk hc.1 hc.2.2.2.1 hi_g w.parse_ok
    obtain ⟨_, h2, h3, _, _⟩ :=
      d3RecvCalleeFineSpecs_ext_direct_run_bounds img S Spk hc hi_g w.parse_ok
    have hrun :=
      (cliRunBinaryEnv_real_1MiB_fine_phaseCredit_of_pqOrD3Recv SE hi_g w.stdin_le
        w.parse_ok).mono h1_cum h2 h3 h1_req
    refine (hrun.seq ((m5Phase_Bounded_phaseCredit_fine w.dirs_sum_le w.dirs_bounds).seq
      (m6_phaseCredit_small1024 fineCostModel_modelHyps hsm1024 w.ok))).mono ?_ ?_ ?_ ?_
    · rw [Nat.add_assoc]; exact Nat.le_refl _
    · simp only [Nat.add_zero]; exact Nat.le_refl _
    · exact max_mono (Nat.le_refl _)
        (Nat.add_le_add_left (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.zero_le _⟩) _)
    · exact max_mono (Nat.le_refl _) (Nat.le_of_eq (Nat.max_comm _ _))
  have hex : PhaseCreditSpec fineCostModel
      (fun evs' => ∃ w : ValidPostSetupWitness i, w.g.i = i ∧
        SeqEnv (CliRunBinaryEnv cliIo.rd (mkD3RecvCalleeEnvs img S P DecPkEnv w.g)
            sessionCapBytes w.g)
          (SeqEnv (M5PhaseEnv w.dirs) (M6Env w.ok)) evs')
      (cliD3ExtRunCum + cliMaxDirtyEntries *
        (10 * max (4 * cliMaxDirPathBytes + cliMaxAddrTextBytes + 16) 16 + 4 * 9539) + m6DeltaCum)
      cliD3ExtRunLive
      (max cliD3ExtRunPeak
        (cliD3ExtRunLive + m5DirStepDeltaPeak cliMaxDirPathBytes cliMaxAddrTextBytes))
      (max cliD3ExtRunMaxReq
        (max 1024 (m5DirStepMaxReq cliMaxDirPathBytes cliMaxAddrTextBytes))) :=
    { req_align := fun evs ⟨w, _, hseq⟩ ev hev => (hw w).req_align evs hseq ev hev
      credit_le := fun st0 {_} ⟨w, _, hseq⟩ => (hw w).credit_le st0 hseq }
  have hcr : PhaseCreditSpec fineCostModel
      (RealCliMainBinaryEnvOf (mkD3RecvCalleeEnvs img S P DecPkEnv) i)
      cliD3BinaryExtMainCum cliD3ExtMainLive cliD3ExtMainPeak cliD3ExtMainReq := by
    refine ((cliMainBoundedSetup_phaseCredit_fine (argv_length_le_3_of_pqOrD3Recv hi)).seq
      (optStage_phaseCredit hex)).mono ?_ ?_ ?_ ?_
    · unfold cliD3BinaryExtMainCum; simp only [Nat.add_assoc]; exact Nat.le_refl _
    · unfold cliD3ExtMainLive cliMainTightLiveOf cliMainDeltaLive_tight; exact Nat.le_refl _
    · unfold cliD3ExtMainPeak cliMainTightPeakOf cliMainDeltaPeak_tight; exact Nat.le_refl _
    · unfold cliD3ExtMainReq cliMainTightReqOf cliMainMaxReq
      have h16k : max 16384 (m3PhaseMaxReq msgCapBytes sessionCapBytes) =
          m3PhaseMaxReq msgCapBytes sessionCapBytes := by
        unfold m3PhaseMaxReq msgCapBytes sessionCapBytes; decide
      rw [h16k]
      exact Nat.le_max_right _ _
  have hex_grp : PhaseGroupSpec fineCostModel
      (fun evs' => ∃ w : ValidPostSetupWitness i, w.g.i = i ∧
        SeqEnv (CliRunBinaryEnv cliIo.rd (mkD3RecvCalleeEnvs img S P DecPkEnv w.g)
            sessionCapBytes w.g)
          (SeqEnv (M5PhaseEnv w.dirs) (M6Env w.ok)) evs')
      (cliD3BinaryExtRunGrpS + cliMaxDirtyEntries * (12 * FineScale) + 3 * FineScale) :=
    { groups_le := fun st0 {_} ⟨w, _, hseq⟩ => by
        have hi_g := w.g_i.symm ▸ hi
        let Spk := S_pk w.g hi_g w.stdin_le w.parse_ok
        let SE := d3RecvCalleeFineSpecs img S Spk hi_g w.parse_ok
        obtain ⟨_, _, _, _, h5⟩ :=
          d3RecvCalleeFineSpecs_ext_direct_run_bounds img S Spk
            (hCaps w.g hi_g w.stdin_le w.parse_ok) hi_g w.parse_ok
        have hinit_sub : 234 * FineScale + SE.initGrpS ≤ cliD3ExtRunGrpS - 15 * FineScale := by
          dsimp only [SE, d3RecvCalleeFineSpecs]; decide
        have hrun := cliRunBinaryEnv_fine_groupSpec_of_cap SE w.stdin_le
          (by decide : 15 * FineScale ≤ cliD3ExtRunGrpS) hinit_sub h5
        have hm5 := (m5PhaseEnv_groupSpec fineCostModel w.dirs).mono
          (Nat.mul_le_mul_right (12 * FineScale) w.dirs_sum_le)
        have htot : PhaseGroupSpec fineCostModel
            (SeqEnv (CliRunBinaryEnv cliIo.rd (mkD3RecvCalleeEnvs img S P DecPkEnv w.g)
                sessionCapBytes w.g)
              (SeqEnv (M5PhaseEnv w.dirs) (M6Env w.ok)))
            (cliD3BinaryExtRunGrpS + cliMaxDirtyEntries * (12 * FineScale) + 3 * FineScale) :=
          (hrun.seq (hm5.seq (m6Env_groupSpec fineCostModel w.ok))).mono
            (by unfold cliD3BinaryExtRunGrpS; generalize FineScale = fs; omega)
        exact htot.groups_le st0 hseq }
  have hgrp : PhaseGroupSpec fineCostModel
      (RealCliMainBinaryEnvOf (mkD3RecvCalleeEnvs img S P DecPkEnv) i)
      cliD3BinaryExtMainGrpS :=
    ((cliMainBoundedSetup_fine_groupSpec (argv_length_le_3_of_pqOrD3Recv hi)).seq
      (optStage_groupSpec hex_grp)).mono
      (by unfold cliD3BinaryExtMainGrpS; generalize FineScale = fs; omega)
  obtain ⟨hlp, hram, hva⟩ := cliD3BinaryExtMain_arith_bounds
  exact fitsEnv_fineCostModel_of_group_literal_bounds hcr hgrp
    (Nat.le_refl _) hlp (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) rfl hram hva

theorem realCliMainBinaryEnvOf_fitsEnv_cliBudgetLimits_pqRecv_d3_of_callPhaseSpecs_1GiB
    [LibsignalPlacement]
    (img : Image) (S : RunSem) (P : PEParams)
    {DecPkEnv : RunCall → List AllocEvent → Prop}
    (hCredit : ∀ (g : RunCall),
      (CliPqxdhInputs P g.i ∨
        ∃ (st : PqParty) (ct : List (BitVec 8)) (rc : BitVec 256),
          PqxdhPartyInSpecDomain P st ∧ g.i = pqRecvInputs P st ct rc) →
      g.i.stdin.length ≤ msgCapBytes →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      PhaseCreditSpec fineCostModel (DecPkEnv g)
        d3RecvW4ExtCum d3RecvW4ExtLive d3RecvW4ExtPeak d3RecvW4ExtMaxReq)
    (hGrp : ∀ (g : RunCall),
      (CliPqxdhInputs P g.i ∨
        ∃ (st : PqParty) (ct : List (BitVec 8)) (rc : BitVec 256),
          PqxdhPartyInSpecDomain P st ∧ g.i = pqRecvInputs P st ct rc) →
      g.i.stdin.length ≤ msgCapBytes →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      PhaseGroupSpec fineCostModel (DecPkEnv g) d3RecvW4ExtGrpS) :
    ∀ i : Inputs,
      (CliPqxdhInputs P i ∨
        ∃ (st : PqParty) (ct : List (BitVec 8)) (rc : BitVec 256),
          PqxdhPartyInSpecDomain P st ∧ i = pqRecvInputs P st ct rc) →
      FitsEnv fineCostModel cliBudgetLimits fineCostModel.init
        (RealCliMainBinaryEnvOf (mkD3RecvCalleeEnvs img S P DecPkEnv) i) :=
  realCliMainBinaryEnvOf_fitsEnv_cliBudgetLimits_pqRecv_d3_of_callSpecs_1GiB img S P
    (fun g hi_g hstdin hparse =>
      { cum := d3RecvW4ExtCum
        live := d3RecvW4ExtLive
        peak := d3RecvW4ExtPeak
        maxReq := d3RecvW4ExtMaxReq
        grpS := d3RecvW4ExtGrpS
        credit := hCredit g hi_g hstdin hparse
        live_le_peak := d3RecvW4Ext_live_le_peak
        groups := hGrp g hi_g hstdin hparse })
    (fun _ _ _ _ => ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩)

theorem realCliMainBinaryEnvOf_fitsEnv_cliBudgetLimits_pqRecv_d3_of_specs_1GiB [LibsignalPlacement]
    (img : Image) (S : RunSem) (P : PEParams)
    {DecPkEnv : RunCall → List AllocEvent → Prop}
    (S_pk : ∀ g : RunCall, SingleSlotFineSpec (DecPkEnv g))
    (hCaps : ∀ g : RunCall,
      (S_pk g).cum ≤ d3RecvW4ExtCum ∧
      (S_pk g).live ≤ d3RecvW4ExtLive ∧
      (S_pk g).peak ≤ d3RecvW4ExtPeak ∧
      (S_pk g).maxReq ≤ d3RecvW4ExtMaxReq ∧
      (S_pk g).grpS ≤ d3RecvW4ExtGrpS) :
    ∀ i : Inputs,
      (CliPqxdhInputs P i ∨
        ∃ (st : PqParty) (ct : List (BitVec 8)) (rc : BitVec 256),
          PqxdhPartyInSpecDomain P st ∧ i = pqRecvInputs P st ct rc) →
      FitsEnv fineCostModel cliBudgetLimits fineCostModel.init
        (RealCliMainBinaryEnvOf (mkD3RecvCalleeEnvs img S P DecPkEnv) i) :=
  realCliMainBinaryEnvOf_fitsEnv_cliBudgetLimits_pqRecv_d3_of_callSpecs_1GiB img S P
    (fun g _ _ _ => S_pk g) (fun g _ _ _ => hCaps g)

theorem realCliMainBinaryEnvOf_fitsEnv_cliBudgetLimits_pqRecv_d3_of_phaseSpecs_1GiB
    [LibsignalPlacement]
    (img : Image) (S : RunSem) (P : PEParams)
    {DecPkEnv : RunCall → List AllocEvent → Prop}
    (hCredit : ∀ g : RunCall, PhaseCreditSpec fineCostModel (DecPkEnv g)
      d3RecvW4ExtCum d3RecvW4ExtLive d3RecvW4ExtPeak d3RecvW4ExtMaxReq)
    (hGrp : ∀ g : RunCall, PhaseGroupSpec fineCostModel (DecPkEnv g) d3RecvW4ExtGrpS) :
    ∀ i : Inputs,
      (CliPqxdhInputs P i ∨
        ∃ (st : PqParty) (ct : List (BitVec 8)) (rc : BitVec 256),
          PqxdhPartyInSpecDomain P st ∧ i = pqRecvInputs P st ct rc) →
      FitsEnv fineCostModel cliBudgetLimits fineCostModel.init
        (RealCliMainBinaryEnvOf (mkD3RecvCalleeEnvs img S P DecPkEnv) i) :=
  realCliMainBinaryEnvOf_fitsEnv_cliBudgetLimits_pqRecv_d3_of_callPhaseSpecs_1GiB img S P
    (fun g _ _ _ => hCredit g) (fun g _ _ _ => hGrp g)

/-! ## 4. Flat-Bundle `init` Whole-`main` `RealCliMainBinaryEnvOf` `FitsEnv` (`2 MiB` Cap) -/

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

private theorem parseArgs_init_bundleDir {peerText : String} {c : CallV}
    (hparse : parseArgs uuidTryParse
      ([bytesOfString "init", bytesOfString peerText, bytesOfString bundleDir]) = some c) :
    ∃ peerV : AddrV, c = .init peerV (bytesOfString bundleDir) := by
  have hin : bytesOfString "init" = utf8 "init" := by rw [utf8_eq_kutf8]; decide
  have hkg : utf8 "init" ≠ utf8 "keygen" := by rw [utf8_eq_kutf8, utf8_eq_kutf8]; decide
  simp only [parseArgs, hin, hkg, ↓reduceIte, Option.map_eq_some_iff] at hparse
  obtain ⟨peerV, _, rfl⟩ := hparse
  exact ⟨peerV, rfl⟩

private def r0BinarySessCum : Nat :=
  max r0Opened1MiBCum (21185 + max 738 (fineReadFileCum sessionCapBytes) + addressTryParseDeltaCum)

private def r0BinarySessLive : Nat :=
  max r0Opened1MiBLive (fineReadFileLive sessionCapBytes + addressTryParseDeltaLive)

private def r0BinarySessPeak : Nat :=
  max r0Opened1MiBPeak
    (max (fineReadFilePeak sessionCapBytes)
      (fineReadFileLive sessionCapBytes + addressTryParseDeltaPeak))

private def r0BinarySessMaxReq : Nat :=
  max r0Opened1MiBMaxReq (max (max 256 (fineReadFileMaxReq sessionCapBytes)) addressTryParseMaxReq)

private theorem r0BinaryEnv_sessionCap_phaseCredit (g : RunCall) :
    PhaseCreditSpec fineCostModel (R0BinaryEnv cliIo.rd g)
      r0BinarySessCum r0BinarySessLive r0BinarySessPeak r0BinarySessMaxReq := by
  have hcapSess : ∀ bs,
      cliIo.rd (runFiles g.i) (pathOf StoresGhost.opened.identity.own.path (utf8 "address")) =
        .ok bs → bs.length ≤ sessionCapBytes :=
    fun bs hrd => cliIo_rd_ok_length_le_sessionCapBytes (runFiles g.i) _ bs hrd
  have hop : PhaseCreditSpec fineCostModel (R0OpenedEnv cliIo.rd (runFiles g.i))
      r0Opened1MiBCum r0Opened1MiBLive r0Opened1MiBPeak r0Opened1MiBMaxReq :=
    CliRunArmsPeak.r0Opened_phaseCredit_of_path fineCostModel_modelHyps
      (DirPeakSpec.path_phaseCredit fineCostModel_modelHyps
        (by decide : StoresGhost.opened.identity.own.path.length ≤ 26) utf8_address_length_le)
      hcapSess
  have hdg := dirGetEnv_path_readFile_fine_phaseCredit_tight cliIo.rd (runFiles g.i)
    StoresGhost.opened.identity.own (utf8 "address") dirDomainCaps_opened_own_64
    (Nat.le_trans utf8_address_length_le (by decide)) hcapSess
  have hmax_eq : max 0 sessionCapBytes = sessionCapBytes := Nat.zero_max sessionCapBytes
  rw [hmax_eq] at hdg
  exact hop.or (hdg.seq (preAfterGetEnv_fine_phaseCredit g))

private def r1bFileStepSessCum : Nat :=
  21185 + fineReadFileCum sessionCapBytes + (2 * 22 + 9539)

private theorem r1bFileStepEnv_sessionCap_phaseCredit {files : FsFiles}
    {dir name : List (BitVec 8)} (hdir : dir.length ≤ 26) (hname : name.length ≤ 16) :
    PhaseCreditSpec fineCostModel (R1bFileStepEnv cliIo.rd files dir name)
      r1bFileStepSessCum
      (fineReadFileLive sessionCapBytes)
      (fineReadFilePeak sessionCapBytes)
      (fineReadFileMaxReq sessionCapBytes) := by
  have hp := optStage_phaseCredit
    (pathEnv_fine_phaseCredit_tight (Nat.le_trans hdir (by decide)) (Nat.le_trans hname (by decide)))
  have hr := optStage_phaseCredit
    (readFile_rule_fine_phaseCredit_tight cliIo.rd files (dir ++ [0x2f#8] ++ name)
      (fun bs hrd => cliIo_rd_ok_length_le_sessionCapBytes files _ bs hrd))
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
    (by unfold r1bFileStepSessCum; omega)
    (by decide)
    (by decide)
    (by decide)

private theorem r1bDeserStageEnv_fine_phaseCredit_local :
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

private def initArmBinarySessPrefixCum : Nat :=
  5 * r1bFileStepSessCum + 2 * splitSignedDeltaCum + splitIdDeltaCum + r1bDeserStageCum

private def initArmBinarySessCum : Nat :=
  max (initArmDeltaCum (pathDeltaCum 26 16) sessionCapBytes w3InitRealCum)
    (initArmBinarySessPrefixCum + w3InitRealCum)

private def initArmBinarySessLive : Nat :=
  max (initArmDeltaLive (pathDeltaLive 26 16) w3InitRealLive)
    (5 * fineReadFileLive sessionCapBytes + w3InitRealLive)

private def initArmBinarySessPeak : Nat :=
  max (initArmDeltaPeak (pathDeltaLive 26 16) (pathDeltaPeak 26 16) sessionCapBytes w3InitRealPeak)
    (5 * fineReadFilePeak sessionCapBytes + w3InitRealPeak)

private def initArmBinarySessMaxReq : Nat :=
  max (initArmMaxReq (pathMaxReq 26 16) sessionCapBytes w3InitRealMaxReq)
    (max (fineReadFileMaxReq sessionCapBytes) w3InitRealMaxReq)

private theorem initArmBinaryEnv_sessionCap_phaseCredit {files : FsFiles}
    {dir : List (BitVec 8)} {InitEnv : List AllocEvent → Prop}
    (hdir : dir.length ≤ 26)
    (hinit : PhaseCreditSpec fineCostModel InitEnv
      w3InitRealCum w3InitRealLive w3InitRealPeak w3InitRealMaxReq) :
    PhaseCreditSpec fineCostModel (InitArmBinaryEnv cliIo.rd files dir InitEnv)
      initArmBinarySessCum initArmBinarySessLive initArmBinarySessPeak initArmBinarySessMaxReq := by
  obtain ⟨hn1, hn2, hn3, hn4, hn5⟩ := utf8_bundleNames_length_le_16
  have hop := CliRunArmsPeak.initArm_phaseCredit_of_paths fineCostModel_modelHyps
    (DirPeakSpec.path_phaseCredit fineCostModel_modelHyps hdir hn1)
    (DirPeakSpec.path_phaseCredit fineCostModel_modelHyps hdir hn2)
    (DirPeakSpec.path_phaseCredit fineCostModel_modelHyps hdir hn3)
    (DirPeakSpec.path_phaseCredit fineCostModel_modelHyps hdir hn4)
    (DirPeakSpec.path_phaseCredit fineCostModel_modelHyps hdir hn5)
    (fun _ bs hrd => cliIo_rd_ok_length_le_sessionCapBytes files _ bs hrd)
    hinit w3InitReal_caps_le.2.2.1
  have hsm14 : 14 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have hs1 := r1bFileStepEnv_sessionCap_phaseCredit (files := files) hdir hn1
  have hs2 := r1bFileStepEnv_sessionCap_phaseCredit (files := files) hdir hn2
  have hs3 := optStage_phaseCredit (r1bFileStepEnv_sessionCap_phaseCredit (files := files) hdir hn3)
  have hs4 := optStage_phaseCredit (r1bFileStepEnv_sessionCap_phaseCredit (files := files) hdir hn4)
  have hs5 := optStage_phaseCredit (r1bFileStepEnv_sessionCap_phaseCredit (files := files) hdir hn5)
  have hss := optStage_phaseCredit (splitSigned_small_phaseCredit fineCostModel_modelHyps hsm14 [])
  have hsi := optStage_phaseCredit (splitId_small_phaseCredit fineCostModel_modelHyps hsm14 [])
  have hds := optStage_phaseCredit r1bDeserStageEnv_fine_phaseCredit_local
  have hr1b : PhaseCreditSpec fineCostModel (R1bBinaryEnv cliIo.rd files dir)
      (4 * r1bFileStepSessCum + 2 * splitSignedDeltaCum + splitIdDeltaCum + r1bDeserStageCum)
      (4 * fineReadFileLive sessionCapBytes)
      (4 * fineReadFilePeak sessionCapBytes)
      (fineReadFileMaxReq sessionCapBytes) :=
    (hs2.seq (hs3.seq (hss.seq (hs4.seq (hss.seq (hs5.seq (hsi.seq hds))))))).mono
      (by omega) (by decide) (by decide) (by decide)
  have hr1c : PhaseCreditSpec fineCostModel (OptStageEnv (R1cEnv InitEnv))
      w3InitRealCum w3InitRealLive w3InitRealPeak w3InitRealMaxReq :=
    optStage_phaseCredit
      (CliRunArmsPeak.r1c_phaseCredit fineCostModel_modelHyps hinit w3InitReal_caps_le.2.2.1)
  have hlp_rf : fineReadFileLive sessionCapBytes ≤ fineReadFilePeak sessionCapBytes := by decide
  have hcore : PhaseCreditSpec fineCostModel (InitArmBinaryCoreEnv cliIo.rd files dir InitEnv)
      (initArmBinarySessPrefixCum + w3InitRealCum)
      (5 * fineReadFileLive sessionCapBytes + w3InitRealLive)
      (5 * fineReadFilePeak sessionCapBytes + w3InitRealPeak)
      (max (fineReadFileMaxReq sessionCapBytes) w3InitRealMaxReq) := by
    refine (hs1.seq ((optStage_phaseCredit hr1b).seq hr1c)).mono ?_ ?_ ?_ ?_
    · unfold initArmBinarySessPrefixCum; omega
    · omega
    · have h4 : 4 * fineReadFileLive sessionCapBytes ≤ 4 * fineReadFilePeak sessionCapBytes :=
        Nat.mul_le_mul_left 4 hlp_rf
      omega
    · exact Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_refl _⟩
  exact hop.or hcore

private def cliD3BinaryInitRunCum : Nat := r0BinarySessCum + initArmBinarySessCum
private def cliD3BinaryInitRunLive : Nat := r0BinarySessLive + initArmBinarySessLive
private def cliD3BinaryInitRunPeak : Nat :=
  max r0BinarySessPeak (r0BinarySessLive + initArmBinarySessPeak)
private def cliD3BinaryInitRunMaxReq : Nat := max r0BinarySessMaxReq initArmBinarySessMaxReq
private def cliD3BinaryInitRunGrpS : Nat :=
  cliRunOpenedCustomPksmGrpS msgCapBytes (pksmCanonSliceGrpS msgCapBytes) w3InitRealGrpS 0 0 0 +
    27 * FineScale

private def cliD3BinaryInitMainCum : Nat :=
  123250 + m3PhaseDeltaCum_tight + cliD3BinaryInitRunCum +
    cliMaxDirtyEntries *
      (10 * max (4 * cliMaxDirPathBytes + cliMaxAddrTextBytes + 16) 16 + 4 * 9539) +
    m6DeltaCum

private def cliD3BinaryInitMainLive : Nat :=
  cliMainTightLiveOf cliD3BinaryInitRunLive

private def cliD3BinaryInitMainPeak : Nat :=
  cliMainTightPeakOf cliD3BinaryInitRunLive cliD3BinaryInitRunPeak

private def cliD3BinaryInitMainReq : Nat :=
  cliMainTightReqOf cliD3BinaryInitRunMaxReq

private def cliD3BinaryInitMainGrpS : Nat :=
  cliMainWidenedSetupFineGrpS + cliD3BinaryInitRunGrpS +
    cliMaxDirtyEntries * (12 * FineScale) + 3 * FineScale

private theorem cliD3BinaryInitMain_arith_bounds :
    cliD3BinaryInitMainLive ≤ cliD3BinaryInitMainPeak ∧
    cliDecoupledRamNeed cliDefaultStaticBytes cliD3BinaryInitMainCum cliD3BinaryInitMainPeak
      cliD3BinaryInitMainReq ((cliD3BinaryInitMainGrpS + FineScale - 1) / FineScale) ≤ cliOneGiB ∧
    cliDecoupledVaNeed cliDefaultStaticBytes cliDefaultStaticCount cliD3BinaryInitMainCum
      cliD3BinaryInitMainPeak cliD3BinaryInitMainReq
      ((cliD3BinaryInitMainGrpS + FineScale - 1) / FineScale) ≤ 2 ^ 48 :=
  ⟨by unfold cliD3BinaryInitMainLive cliD3BinaryInitMainPeak cliMainTightLiveOf cliMainTightPeakOf
        cliMainDeltaLive_tight cliMainDeltaPeak_tight
      exact Nat.le_trans (Nat.add_le_add_left
        (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_max_right _ _)) _) (Nat.le_max_right _ _),
   by decide,
   by decide⟩

/-- Parametric-`E` flat-bundle `init` whole-`main` `RealCliMainBinaryEnvOf` `FitsEnv` at
`cliBudgetLimits` (`bundleCap := sessionCapBytes = 2 MiB`). -/
theorem realCliMainBinaryEnvOf_fitsEnv_cliBudgetLimits_init_d3_of_specs
    {E : RunCall → CliRunCalleeEnvs}
    (hInitCredit : ∀ g : RunCall, PhaseCreditSpec fineCostModel (E g).initEnv
      w3InitRealCum w3InitRealLive w3InitRealPeak w3InitRealMaxReq)
    (hInitGrp : ∀ g : RunCall, PhaseGroupSpec fineCostModel (E g).initEnv w3InitRealGrpS) :
    ∀ i : Inputs, (∃ peerText : String, i.argv = ["init", peerText, bundleDir]) →
      FitsEnv fineCostModel cliBudgetLimits fineCostModel.init
        (RealCliMainBinaryEnvOf E i) := by
  intro i ⟨peerText, hargv_eq⟩
  have hargv_le : i.argv.length ≤ 3 := by rw [hargv_eq]; exact Nat.le_refl 3
  have hsm1024 : 1024 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have hdir_le : (bytesOfString bundleDir).length ≤ 26 := by decide
  have hw (w : ValidPostSetupWitness i) : PhaseCreditSpec fineCostModel
      (SeqEnv (CliRunBinaryEnv cliIo.rd (E w.g) sessionCapBytes w.g)
        (SeqEnv (M5PhaseEnv w.dirs) (M6Env w.ok)))
      (cliD3BinaryInitRunCum + cliMaxDirtyEntries *
        (10 * max (4 * cliMaxDirPathBytes + cliMaxAddrTextBytes + 16) 16 + 4 * 9539) + m6DeltaCum)
      cliD3BinaryInitRunLive
      (max cliD3BinaryInitRunPeak
        (cliD3BinaryInitRunLive + m5DirStepDeltaPeak cliMaxDirPathBytes cliMaxAddrTextBytes))
      (max cliD3BinaryInitRunMaxReq
        (max 1024 (m5DirStepMaxReq cliMaxDirPathBytes cliMaxAddrTextBytes))) := by
    have hparse_init : parseArgs uuidTryParse
        ([bytesOfString "init", bytesOfString peerText, bytesOfString bundleDir]) = some w.g.c := by
      simpa only [w.g_i, hargv_eq, List.map_cons, List.map_nil] using w.parse_ok
    obtain ⟨peerV, hc⟩ := parseArgs_init_bundleDir hparse_init
    have harm : PhaseCreditSpec fineCostModel
        (RunArmBinaryEnv cliIo.rd (runFiles w.g.i) (E w.g) sessionCapBytes w.g.i.stdin w.g.c)
        initArmBinarySessCum initArmBinarySessLive initArmBinarySessPeak initArmBinarySessMaxReq := by
      rw [hc]
      exact initArmBinaryEnv_sessionCap_phaseCredit hdir_le (hInitCredit w.g)
    have haj := phaseCredit_seq_freeOnly_right fineCostModel_modelHyps harm (fun _ hf => hf)
      (by decide : initArmBinarySessLive ≤ initArmBinarySessPeak)
    have hrun : PhaseCreditSpec fineCostModel
        (CliRunBinaryEnv cliIo.rd (E w.g) sessionCapBytes w.g)
        cliD3BinaryInitRunCum cliD3BinaryInitRunLive cliD3BinaryInitRunPeak
        cliD3BinaryInitRunMaxReq :=
      phaseCredit_or_freeOnly_left fineCostModel_modelHyps (fun _ hf => hf)
        ((r0BinaryEnv_sessionCap_phaseCredit w.g).seq haj)
    refine (hrun.seq ((m5Phase_Bounded_phaseCredit_fine w.dirs_sum_le w.dirs_bounds).seq
      (m6_phaseCredit_small1024 fineCostModel_modelHyps hsm1024 w.ok))).mono ?_ ?_ ?_ ?_
    · rw [Nat.add_assoc]; exact Nat.le_refl _
    · simp only [Nat.add_zero]; exact Nat.le_refl _
    · exact max_mono (Nat.le_refl _)
        (Nat.add_le_add_left (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.zero_le _⟩) _)
    · exact max_mono (Nat.le_refl _) (Nat.le_of_eq (Nat.max_comm _ _))
  have hex : PhaseCreditSpec fineCostModel
      (fun evs' => ∃ w : ValidPostSetupWitness i, w.g.i = i ∧
        SeqEnv (CliRunBinaryEnv cliIo.rd (E w.g) sessionCapBytes w.g)
          (SeqEnv (M5PhaseEnv w.dirs) (M6Env w.ok)) evs')
      (cliD3BinaryInitRunCum + cliMaxDirtyEntries *
        (10 * max (4 * cliMaxDirPathBytes + cliMaxAddrTextBytes + 16) 16 + 4 * 9539) + m6DeltaCum)
      cliD3BinaryInitRunLive
      (max cliD3BinaryInitRunPeak
        (cliD3BinaryInitRunLive + m5DirStepDeltaPeak cliMaxDirPathBytes cliMaxAddrTextBytes))
      (max cliD3BinaryInitRunMaxReq
        (max 1024 (m5DirStepMaxReq cliMaxDirPathBytes cliMaxAddrTextBytes))) :=
    { req_align := fun evs ⟨w, _, hseq⟩ ev hev => (hw w).req_align evs hseq ev hev
      credit_le := fun st0 {_} ⟨w, _, hseq⟩ => (hw w).credit_le st0 hseq }
  have hcr : PhaseCreditSpec fineCostModel (RealCliMainBinaryEnvOf E i)
      cliD3BinaryInitMainCum cliD3BinaryInitMainLive cliD3BinaryInitMainPeak
      cliD3BinaryInitMainReq := by
    refine ((cliMainBoundedSetup_phaseCredit_fine hargv_le).seq (optStage_phaseCredit hex)).mono
      ?_ ?_ ?_ ?_
    · unfold cliD3BinaryInitMainCum; simp only [Nat.add_assoc]; exact Nat.le_refl _
    · unfold cliD3BinaryInitMainLive cliMainTightLiveOf cliMainDeltaLive_tight; exact Nat.le_refl _
    · unfold cliD3BinaryInitMainPeak cliMainTightPeakOf cliMainDeltaPeak_tight; exact Nat.le_refl _
    · unfold cliD3BinaryInitMainReq cliMainTightReqOf cliMainMaxReq
      have h16k : max 16384 (m3PhaseMaxReq msgCapBytes sessionCapBytes) =
          m3PhaseMaxReq msgCapBytes sessionCapBytes := by
        unfold m3PhaseMaxReq msgCapBytes sessionCapBytes; decide
      rw [h16k]
  have hex_grp : PhaseGroupSpec fineCostModel
      (fun evs' => ∃ w : ValidPostSetupWitness i, w.g.i = i ∧
        SeqEnv (CliRunBinaryEnv cliIo.rd (E w.g) sessionCapBytes w.g)
          (SeqEnv (M5PhaseEnv w.dirs) (M6Env w.ok)) evs')
      (cliD3BinaryInitRunGrpS + cliMaxDirtyEntries * (12 * FineScale) + 3 * FineScale) :=
    { groups_le := fun st0 {_} ⟨w, _, hseq⟩ => by
        have hparse_init : parseArgs uuidTryParse
            ([bytesOfString "init", bytesOfString peerText, bytesOfString bundleDir]) =
              some w.g.c := by
          simpa only [w.g_i, hargv_eq, List.map_cons, List.map_nil] using w.parse_ok
        obtain ⟨peerV, hc⟩ := parseArgs_init_bundleDir hparse_init
        have harm_g : PhaseGroupSpec fineCostModel
            (RunArmBinaryEnv cliIo.rd (runFiles w.g.i) (E w.g) sessionCapBytes w.g.i.stdin w.g.c)
            (234 * FineScale + w3InitRealGrpS) := by
          rw [hc]
          exact initArmBinaryEnv_fine_groupSpec_local cliIo.rd (runFiles w.g.i)
            (bytesOfString bundleDir) (hInitGrp w.g)
        have hrun : PhaseGroupSpec fineCostModel
            (CliRunBinaryEnv cliIo.rd (E w.g) sessionCapBytes w.g)
            cliD3BinaryInitRunGrpS :=
          (cliRunOfR0_fine_groupSpec (r0BinaryEnv_fine_groupSpec_local cliIo.rd w.g) harm_g).mono
            (by unfold cliD3BinaryInitRunGrpS; decide)
        have hm5 := (m5PhaseEnv_groupSpec fineCostModel w.dirs).mono
          (Nat.mul_le_mul_right (12 * FineScale) w.dirs_sum_le)
        have htot : PhaseGroupSpec fineCostModel
            (SeqEnv (CliRunBinaryEnv cliIo.rd (E w.g) sessionCapBytes w.g)
              (SeqEnv (M5PhaseEnv w.dirs) (M6Env w.ok)))
            (cliD3BinaryInitRunGrpS + cliMaxDirtyEntries * (12 * FineScale) + 3 * FineScale) :=
          (hrun.seq (hm5.seq (m6Env_groupSpec fineCostModel w.ok))).mono
            (by generalize FineScale = fs; omega)
        exact htot.groups_le st0 hseq }
  have hgrp : PhaseGroupSpec fineCostModel (RealCliMainBinaryEnvOf E i) cliD3BinaryInitMainGrpS :=
    ((cliMainBoundedSetup_fine_groupSpec hargv_le).seq (optStage_groupSpec hex_grp)).mono
      (by unfold cliD3BinaryInitMainGrpS; generalize FineScale = fs; omega)
  obtain ⟨hlp, hram, hva⟩ := cliD3BinaryInitMain_arith_bounds
  exact fitsEnv_fineCostModel_of_group_literal_bounds hcr hgrp
    (Nat.le_refl _) hlp (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) rfl hram hva

/-- Concrete flat-bundle `init` whole-`main` `RealCliMainBinaryEnvOf` `FitsEnv` at
`bundleCap := sessionCapBytes = 2 MiB`. -/
theorem realCliMainBinaryEnvOf_fitsEnv_cliBudgetLimits_init_d3 [LibsignalPlacement]
    (img : Image) (S : RunSem) (P : PEParams) :
    ∀ i : Inputs, (∃ peerText : String, i.argv = ["init", peerText, bundleDir]) →
      FitsEnv fineCostModel cliBudgetLimits fineCostModel.init
        (RealCliMainBinaryEnvOf (mkExistentialRealCalleeEnvs img S P) i) :=
  realCliMainBinaryEnvOf_fitsEnv_cliBudgetLimits_init_d3_of_specs
    (existentialW3_credit img S P) (existentialW3_groups img S P)

/-! ## 5. Parametric-`Dom` Residual Cost-Model State Invariants `mainSt0Dom`..`mainSt3Dom` -/

private theorem seqEnv_mono_local {E₁ E₁' E₂ E₂' : List AllocEvent → Prop}
    (h1 : ∀ evs, E₁ evs → E₁' evs) (h2 : ∀ evs, E₂ evs → E₂' evs)
    {evs : List AllocEvent} (h : SeqEnv E₁ E₂ evs) :
    SeqEnv E₁' E₂' evs := by
  rcases h with hE1 | ⟨evs₁, evs₂, rfl, hE1, hE2⟩
  · exact Or.inl (h1 evs hE1)
  · exact Or.inr ⟨evs₁, evs₂, rfl, h1 evs₁ hE1, h2 evs₂ hE2⟩

private theorem seqEnv_assoc_left_local {E₁ E₂ E₃ : List AllocEvent → Prop} {evs : List AllocEvent}
    (h : SeqEnv E₁ (SeqEnv E₂ E₃) evs) :
    SeqEnv (SeqEnv E₁ E₂) E₃ evs := by
  rcases h with h1 | ⟨evs₁, evs₂₃, rfl, h1, h23⟩
  · exact Or.inl (Or.inl h1)
  · rcases h23 with h2 | ⟨evs₂, evs₃, rfl, h2, h3⟩
    · exact Or.inl (Or.inr ⟨evs₁, evs₂₃, rfl, h1, h2⟩)
    · exact Or.inr ⟨evs₁ ++ evs₂, evs₃, (List.append_assoc evs₁ evs₂ evs₃).symm,
        Or.inr ⟨evs₁, evs₂, rfl, h1, h2⟩, h3⟩

/-- Entry cost-model invariant at `M0`/`M1` parameterized by `Dom : Inputs → Prop`. -/
def mainSt0Dom (Dom : Inputs → Prop) (E : RunCall → CliRunCalleeEnvs) (lim : BudgetLimits)
    (i : Inputs) (st0 : FineBudget) : Prop :=
  FitsEnv fineCostModel lim st0 (SeqEnv (CliMainBoundedSetupEnv i.argv.length) FreeOnlyEvs) ∧
  (Dom i → FitsEnv fineCostModel lim st0 (RealCliMainBinaryEnvOf E i))

/-- Post-`M1` (`argv` buffer allocated) residual cost-model invariant over `Dom`. -/
def mainSt1Dom (Dom : Inputs → Prop) (E : RunCall → CliRunCalleeEnvs) (lim : BudgetLimits)
    (i : Inputs) (st1 : FineBudget) : Prop :=
  FitsEnv fineCostModel lim st1 (SeqEnv (PostM1SetupEnv i.argv.length) FreeOnlyEvs) ∧
  (Dom i →
    FitsEnv fineCostModel lim st1 (SeqEnv (PostM1SetupEnv i.argv.length) (PostSetupTailEnv E i)))

/-- Post-`M2` (`parseArgs = some c`) residual cost-model invariant entering `M3` over `Dom`. -/
def mainSt2Dom (Dom : Inputs → Prop) (E : RunCall → CliRunCalleeEnvs) (lim : BudgetLimits)
    (i : Inputs) (c : CallV) (st2 : FineBudget) : Prop :=
  parseArgs uuidTryParse (i.argv.map bytesOfString) = some c ∧
  FitsEnv fineCostModel lim st2 (SeqEnv M3BoundedSetupEnv FreeOnlyEvs) ∧
  (Dom i →
    FitsEnv fineCostModel lim st2 (SeqEnv M3BoundedSetupEnv (PostSetupTailEnv E i)))

/-- Post-`M3` (`read_stdin` + `"coins"` `read_file` completed) residual invariant over `Dom`. -/
def mainSt3Dom (Dom : Inputs → Prop) (E : RunCall → CliRunCalleeEnvs) (lim : BudgetLimits)
    (i : Inputs) (c : CallV) (st3 : FineBudget) : Prop :=
  parseArgs uuidTryParse (i.argv.map bytesOfString) = some c ∧
  FitsEnv fineCostModel lim st3 FreeOnlyEvs ∧
  (Dom i → FitsEnv fineCostModel lim st3 (PostSetupTailEnv E i))

theorem mainSt0Dom_cliPqxdh_eq (WP : PEParams) (E : RunCall → CliRunCalleeEnvs)
    (lim : BudgetLimits) :
    mainSt0Dom (CliPqxdhInputs WP) E lim = mainSt0 WP E lim := rfl

theorem mainSt1Dom_cliPqxdh_eq (WP : PEParams) (E : RunCall → CliRunCalleeEnvs)
    (lim : BudgetLimits) :
    mainSt1Dom (CliPqxdhInputs WP) E lim = mainSt1 WP E lim := rfl

theorem mainSt2Dom_cliPqxdh_eq (WP : PEParams) (E : RunCall → CliRunCalleeEnvs)
    (lim : BudgetLimits) :
    mainSt2Dom (CliPqxdhInputs WP) E lim = mainSt2 WP E lim := rfl

theorem mainSt3Dom_cliPqxdh_eq (WP : PEParams) (E : RunCall → CliRunCalleeEnvs)
    (lim : BudgetLimits) :
    mainSt3Dom (CliPqxdhInputs WP) E lim = mainSt3 WP E lim := rfl

/-- Generic `hSt0` constructor for arbitrary `Dom : Inputs → Prop`. -/
theorem mainSt0Dom_init_of_fitsEnv {Dom : Inputs → Prop} {E : RunCall → CliRunCalleeEnvs}
    {lim : BudgetLimits}
    (hEarly : ∀ argvLen : Nat, argvLen ≤ 1820 →
      FitsEnv fineCostModel lim fineCostModel.init
        (SeqEnv (CliMainBoundedSetupEnv argvLen) FreeOnlyEvs))
    (hMain : ∀ i : Inputs, Dom i →
      FitsEnv fineCostModel lim fineCostModel.init (RealCliMainBinaryEnvOf E i))
    {i : Inputs} (hok : CliInputsOk i) :
    mainSt0Dom Dom E lim i fineCostModel.init :=
  ⟨hEarly i.argv.length (argvFits_length_le hok.2), hMain i⟩

/-- **`M1` transition (`st0 → st1`)** over `Dom`. -/
theorem fitsEvents_and_st1Dom_of_st0 {Dom : Inputs → Prop} {E : RunCall → CliRunCalleeEnvs}
    {lim : BudgetLimits} {i : Inputs} {st0 : FineBudget}
    (hst0 : mainSt0Dom Dom E lim i st0)
    {evs₁ : List AllocEvent} (hm1 : M1PhaseEnv i.argv.length evs₁) :
    FitsEvents fineCostModel lim st0 evs₁ ∧
      mainSt1Dom Dom E lim i (fineCostModel.stepEvents evs₁ st0) := by
  have hEarlySeq : FitsEnv fineCostModel lim st0
      (SeqEnv (M1PhaseEnv i.argv.length)
        (SeqEnv (PostM1SetupEnv i.argv.length) FreeOnlyEvs)) :=
    fun evs h => hst0.1 evs
      (seqEnv_mono_local (fun _ => Or.inr) (fun _ hf => hf) (seqEnv_assoc_left_local h))
  obtain ⟨hfits₁, hEarly₁⟩ := fitsEvents_and_fitsEnv_stepEvents_of_seqEnv hEarlySeq hm1
  refine ⟨hfits₁, hEarly₁, fun hi => ?_⟩
  have hMainSeq : FitsEnv fineCostModel lim st0
      (SeqEnv (M1PhaseEnv i.argv.length)
        (SeqEnv (PostM1SetupEnv i.argv.length) (PostSetupTailEnv E i))) :=
    fun evs h => hst0.2 hi evs
      (seqEnv_mono_local (fun _ => Or.inr) (fun _ ht => ht) (seqEnv_assoc_left_local h))
  exact (fitsEvents_and_fitsEnv_stepEvents_of_seqEnv hMainSeq hm1).2

/-- Combined `M0 → M1` `FitsEvents` and `mainSt1Dom` transition from `mainSt0Dom`. -/
theorem mainSt01Dom_of_st0 {Dom : Inputs → Prop} {E : RunCall → CliRunCalleeEnvs}
    {lim : BudgetLimits} {i : Inputs} {st0 : FineBudget}
    (_hok : CliInputsOk i) (hst0 : mainSt0Dom Dom E lim i st0) (_hne : i.argv ≠ []) :
    FitsEvents fineCostModel lim st0 (rustAllocEvents (16 * i.argv.length) 8) ∧
      mainSt1Dom Dom E lim i
        (fineCostModel.stepEvents (rustAllocEvents (16 * i.argv.length) 8) st0) :=
  fitsEvents_and_st1Dom_of_st0 hst0 (Or.inr rfl)

theorem fitsEnv_freeOnly_of_st0Dom {Dom : Inputs → Prop} {E : RunCall → CliRunCalleeEnvs}
    {lim : BudgetLimits} {i : Inputs} {st0 : FineBudget}
    (hst0 : mainSt0Dom Dom E lim i st0) :
    FitsEnv fineCostModel lim st0 FreeOnlyEvs :=
  fun evs hf => hst0.1 evs (Or.inl (Or.inl hf))

theorem fitsEnv_freeOnly_of_st1Dom {Dom : Inputs → Prop} {E : RunCall → CliRunCalleeEnvs}
    {lim : BudgetLimits} {i : Inputs} {st1 : FineBudget}
    (hst1 : mainSt1Dom Dom E lim i st1) :
    FitsEnv fineCostModel lim st1 FreeOnlyEvs :=
  fun evs hf => hst1.1 evs (Or.inr ⟨[], evs, rfl, postM1SetupEnv_nil i.argv.length, hf⟩)

theorem fitsEnv_m2EarlyExit_of_st1Dom {Dom : Inputs → Prop} {E : RunCall → CliRunCalleeEnvs}
    {lim : BudgetLimits} {i : Inputs} {st1 : FineBudget}
    (hst1 : mainSt1Dom Dom E lim i st1) :
    FitsEnv fineCostModel lim st1 (SeqEnv (M2PhaseEnv i.argv.length) FreeOnlyEvs) :=
  fun evs h => hst1.1 evs
    (seqEnv_mono_local (fun _ => postM1SetupEnv_of_m2Phase) (fun _ hf => hf) h)

/-- **`M2` transition (`st1 → st2`)** over `Dom`. -/
theorem fitsEvents_and_st2Dom_of_st1 {Dom : Inputs → Prop} {E : RunCall → CliRunCalleeEnvs}
    {lim : BudgetLimits} {i : Inputs} {c : CallV} {st1 : FineBudget}
    (hst1 : mainSt1Dom Dom E lim i st1)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some c)
    {evs₂ : List AllocEvent} (hm2 : M2PhaseEnv i.argv.length evs₂) :
    FitsEvents fineCostModel lim st1 evs₂ ∧
      mainSt2Dom Dom E lim i c (fineCostModel.stepEvents evs₂ st1) := by
  have hEarlySeq : FitsEnv fineCostModel lim st1
      (SeqEnv (M2PhaseEnv i.argv.length) (SeqEnv M3BoundedSetupEnv FreeOnlyEvs)) :=
    fun evs h => hst1.1 evs
      (seqEnv_mono_local (fun _ => postM1SetupEnv_of_seq_m2Phase_m3) (fun _ hf => hf)
        (seqEnv_assoc_left_local h))
  obtain ⟨hfits₂, hEarly₂⟩ := fitsEvents_and_fitsEnv_stepEvents_of_seqEnv hEarlySeq hm2
  refine ⟨hfits₂, hparse, hEarly₂, fun hi => ?_⟩
  have hMainSeq : FitsEnv fineCostModel lim st1
      (SeqEnv (M2PhaseEnv i.argv.length)
        (SeqEnv M3BoundedSetupEnv (PostSetupTailEnv E i))) :=
    fun evs h => hst1.2 hi evs
      (seqEnv_mono_local (fun _ => postM1SetupEnv_of_seq_m2Phase_m3) (fun _ ht => ht)
        (seqEnv_assoc_left_local h))
  exact (fitsEvents_and_fitsEnv_stepEvents_of_seqEnv hMainSeq hm2).2

theorem fitsEnv_freeOnly_of_st2Dom {Dom : Inputs → Prop} {E : RunCall → CliRunCalleeEnvs}
    {lim : BudgetLimits} {i : Inputs} {c : CallV} {st2 : FineBudget}
    (hst2 : mainSt2Dom Dom E lim i c st2) :
    FitsEnv fineCostModel lim st2 FreeOnlyEvs :=
  fun evs hf => hst2.2.1 evs (Or.inr ⟨[], evs, rfl, m3BoundedSetupEnv_nil, hf⟩)

theorem fitsEnv_m3EarlyExit_of_st2Dom {Dom : Inputs → Prop} {E : RunCall → CliRunCalleeEnvs}
    {lim : BudgetLimits} {i : Inputs} {c : CallV} {st2 : FineBudget}
    (hst2 : mainSt2Dom Dom E lim i c st2) :
    FitsEnv fineCostModel lim st2 (SeqEnv M3BoundedSetupEnv FreeOnlyEvs) :=
  hst2.2.1

/-- **`M3` transition (`st2 → st3`)** over `Dom`. -/
theorem fitsEvents_and_st3Dom_of_st2 {Dom : Inputs → Prop} {E : RunCall → CliRunCalleeEnvs}
    {lim : BudgetLimits} {i : Inputs} {c : CallV} {st2 : FineBudget}
    (hst2 : mainSt2Dom Dom E lim i c st2)
    {evs₃ : List AllocEvent} (hm3 : M3BoundedSetupEnv evs₃) :
    FitsEvents fineCostModel lim st2 evs₃ ∧
      mainSt3Dom Dom E lim i c (fineCostModel.stepEvents evs₃ st2) := by
  obtain ⟨hfits₃, hFree₃⟩ := fitsEvents_and_fitsEnv_stepEvents_of_seqEnv hst2.2.1 hm3
  exact ⟨hfits₃, hst2.1, hFree₃, fun hi =>
    (fitsEvents_and_fitsEnv_stepEvents_of_seqEnv (hst2.2.2 hi) hm3).2⟩

theorem fitsEnv_freeOnly_of_st3Dom {Dom : Inputs → Prop} {E : RunCall → CliRunCalleeEnvs}
    {lim : BudgetLimits} {i : Inputs} {c : CallV} {st3 : FineBudget}
    (hst3 : mainSt3Dom Dom E lim i c st3) :
    FitsEnv fineCostModel lim st3 FreeOnlyEvs :=
  hst3.2.1

/-- **`M4` `run` precondition & transition (`st3Dom → mainSt4`, `step4_call`)** over `Dom`. -/
theorem fitsEnv_run_and_st4_of_st3Dom {Dom : Inputs → Prop} {E : RunCall → CliRunCalleeEnvs}
    {lim : BudgetLimits} {i : Inputs} {c : CallV} {st3 : FineBudget}
    (hst3 : mainSt3Dom Dom E lim i c st3)
    (hi : Dom i)
    (hstdin : i.stdin.length ≤ msgCapBytes)
    (rc : RunCall) (hrc_i : rc.i = i) (hrc_c : rc.c = c) :
    FitsEnv fineCostModel lim st3 (CliRunBinaryEnv cliIo.rd (E rc) sessionCapBytes rc) ∧
      ∀ evs₄ : List AllocEvent,
        CliRunBinaryEnv cliIo.rd (E rc) sessionCapBytes rc evs₄ →
        FitsEnv fineCostModel lim (fineCostModel.stepEvents evs₄ st3) FreeOnlyEvs ∧
          ∀ g : StoresGhost, mainSt4 lim i c g (fineCostModel.stepEvents evs₄ st3) := by
  have hTail := hst3.2.2 hi
  have hparse_rc : parseArgs uuidTryParse (rc.i.argv.map bytesOfString) = some rc.c := by
    rw [hrc_i, hrc_c]; exact hst3.1
  have hstdin_rc : rc.i.stdin.length ≤ msgCapBytes := by
    rw [hrc_i]; exact hstdin
  let w0 : ValidPostSetupWitness i :=
    { g := rc
      g_i := hrc_i
      parse_ok := hparse_rc
      stdin_le := hstdin_rc
      dirs := []
      dirs_sum_le := Nat.zero_le _
      dirs_bounds := fun _ hm => nomatch hm
      ok := false }
  have hRunFits : FitsEnv fineCostModel lim st3
      (CliRunBinaryEnv cliIo.rd (E rc) sessionCapBytes rc) :=
    fun evs hrun => hTail evs (Or.inr ⟨w0, hrc_i, Or.inl hrun⟩)
  refine ⟨hRunFits, fun evs₄ hrun₄ => ?_⟩
  have hFree₄ : FitsEnv fineCostModel lim (fineCostModel.stepEvents evs₄ st3) FreeOnlyEvs := by
    intro evs_f hf
    have hm5 : M5PhaseEnv [] evs_f := Or.inr ⟨[], evs_f, rfl, rfl, hf⟩
    exact ((fitsEvents_append fineCostModel lim evs₄ evs_f st3).mp
      (hTail (evs₄ ++ evs_f)
        (Or.inr ⟨w0, hrc_i, Or.inr ⟨evs₄, evs_f, rfl, hrun₄, Or.inl hm5⟩⟩))).2
  refine ⟨hFree₄, fun _g => ⟨hst3.1, hstdin, hFree₄, fun dirs ok hsum hbounds => ?_⟩⟩
  let w : ValidPostSetupWitness i :=
    { g := rc
      g_i := hrc_i
      parse_ok := hparse_rc
      stdin_le := hstdin_rc
      dirs := dirs
      dirs_sum_le := hsum
      dirs_bounds := hbounds
      ok := ok }
  intro evs₅₆ hm56
  exact ((fitsEvents_append fineCostModel lim evs₄ evs₅₆ st3).mp
    (hTail (evs₄ ++ evs₅₆)
      (Or.inr ⟨w, hrc_i, Or.inr ⟨evs₄, evs₅₆, rfl, hrun₄, hm56⟩⟩))).2

/-- D3 `pqRecv` + `CliPqxdhInputs` domain predicate (`CliPqOrD3RecvInputs P`). -/
abbrev CliPqOrD3RecvDom (P : PEParams) (i : Inputs) : Prop :=
  CliPqxdhInputs P i ∨
    ∃ (st : PqParty) (ct : List (BitVec 8)) (rc : BitVec 256),
      PqxdhPartyInSpecDomain P st ∧ i = pqRecvInputs P st ct rc

/-- Flat-bundle `init` argv domain predicate. -/
abbrev CliFlatInitArgvDom (i : Inputs) : Prop :=
  ∃ peerText : String, i.argv = ["init", peerText, bundleDir]

theorem mainSt0Dom_init_cliBudgetLimits_pqRecv_d3_of_callSpecs [LibsignalPlacement]
    (img : Image) (S : RunSem) (P : PEParams)
    {DecPkEnv : RunCall → List AllocEvent → Prop}
    (S_pk : ∀ (g : RunCall), CliPqOrD3RecvDom P g.i → g.i.stdin.length ≤ msgCapBytes →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      SingleSlotFineSpec (DecPkEnv g))
    (hCaps : ∀ (g : RunCall) (hi_g : CliPqOrD3RecvDom P g.i) (hstdin : g.i.stdin.length ≤ msgCapBytes)
      (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c),
      (S_pk g hi_g hstdin hparse).cum ≤ w4RecvPrekeyReal1MiB_i_Cum ∧
      (S_pk g hi_g hstdin hparse).live ≤ w4RecvPrekeyReal1MiB_i_Live ∧
      (S_pk g hi_g hstdin hparse).peak ≤ w4RecvPrekeyReal1MiB_i_Peak ∧
      (S_pk g hi_g hstdin hparse).maxReq ≤ w4RecvPrekeyReal1MiB_i_MaxReq ∧
      (S_pk g hi_g hstdin hparse).grpS ≤ w4RecvPrekeyRealGrpS)
    (i : Inputs) (hok : CliInputsOk i) :
    mainSt0Dom (CliPqOrD3RecvDom P) (mkD3RecvCalleeEnvs img S P DecPkEnv) cliBudgetLimits i
      fineCostModel.init :=
  mainSt0Dom_init_of_fitsEnv
    cliMainSetupEarlyExit_fitsEnv_cliBudgetLimits_le1820
    (realCliMainBinaryEnvOf_fitsEnv_cliBudgetLimits_pqRecv_d3_of_callSpecs img S P S_pk hCaps)
    hok

theorem mainSt0Dom_init_cliBudgetLimits_pqRecv_d3_of_mem_w4 [LibsignalPlacement]
    (img : Image) (S : RunSem) (P : PEParams)
    {DecPkEnv : RunCall → List AllocEvent → Prop}
    (hMem : ∀ (g : RunCall), CliPqOrD3RecvDom P g.i → g.i.stdin.length ≤ msgCapBytes →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      ∀ evs, DecPkEnv g evs → (mkExistentialRealCalleeEnvs img S P g).decPkEnv evs)
    (i : Inputs) (hok : CliInputsOk i) :
    mainSt0Dom (CliPqOrD3RecvDom P) (mkD3RecvCalleeEnvs img S P DecPkEnv) cliBudgetLimits i
      fineCostModel.init :=
  mainSt0Dom_init_of_fitsEnv
    cliMainSetupEarlyExit_fitsEnv_cliBudgetLimits_le1820
    (realCliMainBinaryEnvOf_fitsEnv_cliBudgetLimits_pqRecv_d3_of_mem_w4 img S P hMem)
    hok

theorem mainSt0Dom_init_cliBudgetLimits_pqRecv_d3 [LibsignalPlacement]
    (img : Image) (S : RunSem) (P : PEParams)
    (i : Inputs) (hok : CliInputsOk i) :
    mainSt0Dom (CliPqOrD3RecvDom P) (mkExistentialD3RecvCalleeEnvs img S P) cliBudgetLimits i
      fineCostModel.init :=
  mainSt0Dom_init_of_fitsEnv
    cliMainSetupEarlyExit_fitsEnv_cliBudgetLimits_le1820
    (realCliMainBinaryEnvOf_fitsEnv_cliBudgetLimits_pqRecv_d3 img S P)
    hok

theorem mainSt0Dom_init_cliBudgetLimits_pqRecv_d3_of_callSpecs_1GiB [LibsignalPlacement]
    (img : Image) (S : RunSem) (P : PEParams)
    {DecPkEnv : RunCall → List AllocEvent → Prop}
    (S_pk : ∀ (g : RunCall), CliPqOrD3RecvDom P g.i → g.i.stdin.length ≤ msgCapBytes →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      SingleSlotFineSpec (DecPkEnv g))
    (hCaps : ∀ (g : RunCall) (hi_g : CliPqOrD3RecvDom P g.i) (hstdin : g.i.stdin.length ≤ msgCapBytes)
      (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c),
      (S_pk g hi_g hstdin hparse).cum ≤ d3RecvW4ExtCum ∧
      (S_pk g hi_g hstdin hparse).live ≤ d3RecvW4ExtLive ∧
      (S_pk g hi_g hstdin hparse).peak ≤ d3RecvW4ExtPeak ∧
      (S_pk g hi_g hstdin hparse).maxReq ≤ d3RecvW4ExtMaxReq ∧
      (S_pk g hi_g hstdin hparse).grpS ≤ d3RecvW4ExtGrpS)
    (i : Inputs) (hok : CliInputsOk i) :
    mainSt0Dom (CliPqOrD3RecvDom P) (mkD3RecvCalleeEnvs img S P DecPkEnv) cliBudgetLimits i
      fineCostModel.init :=
  mainSt0Dom_init_of_fitsEnv
    cliMainSetupEarlyExit_fitsEnv_cliBudgetLimits_le1820
    (realCliMainBinaryEnvOf_fitsEnv_cliBudgetLimits_pqRecv_d3_of_callSpecs_1GiB img S P S_pk hCaps)
    hok

theorem mainSt0Dom_init_cliBudgetLimits_init_d3 [LibsignalPlacement]
    (img : Image) (S : RunSem) (P : PEParams)
    (i : Inputs) (hok : CliInputsOk i) :
    mainSt0Dom CliFlatInitArgvDom (mkExistentialRealCalleeEnvs img S P) cliBudgetLimits i
      fineCostModel.init :=
  mainSt0Dom_init_of_fitsEnv
    cliMainSetupEarlyExit_fitsEnv_cliBudgetLimits_le1820
    (realCliMainBinaryEnvOf_fitsEnv_cliBudgetLimits_init_d3 img S P)
    hok

end LibsignalBinary.Proofs.PeakBudget.RealMainBinaryEnvAdapterD3
