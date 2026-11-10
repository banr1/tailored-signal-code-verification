/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.ClientBounds
public import LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
public import LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith
public import LibsignalBinary.Proofs.PeakBudget.CliGroupBounds
public import LibsignalBinary.Proofs.PeakBudget.CliKitEnvFitsExact
public import LibsignalBinary.Proofs.PeakBudget.CliMainPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
public import LibsignalBinary.Proofs.PeakBudget.CliRunArmsPeak
public import LibsignalBinary.Proofs.PeakBudget.CliRunPeakHelpers
public import LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge
public import LibsignalBinary.Proofs.PeakBudget.CliSlotFineSpec
public import LibsignalBinary.Proofs.PeakBudget.CliTopBudgetReal
public import LibsignalBinary.Proofs.PeakBudget.CliTopBudgetSpec
public import LibsignalBinary.Proofs.PeakBudget.GroupCreditKit
public import LibsignalBinary.Proofs.PeakBudget.MainEntryBudgetFitsCapReal
public import LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemExact
public import LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
public import LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemSlots
public import LibsignalBinary.Proofs.PeakBudget.RealMainBinaryEnvAdapterD3
public import LibsignalBinary.Proofs.PeakBudget.RealMainEnvAdapter
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
public import LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux
public import LibsignalBinary.Proofs.PeakBudget.WireMsgPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.WirePksmLoopCredit
public import LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit
public import LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromHelpers
public import LibsignalBinary.Proofs.PeakBudget.WireTryFromHelpers
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3ParseRejectF3
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.MainEntryBudgetFitsInst
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.AllPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bAssemblyPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Plumbing

/-!
# Slot-Parametric D3 `pqD3ScopedRun` `MainEntryBudgetFitsCapOf` Closure

**Checked by Lean.**

Whole-`main` `FitsEnv` and `MainEntryBudgetFitsCapOf` closures on `pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel S)`
(`CliPqOrD3RecvInputs ⟨W.C, W.Q⟩`), parametric in `(EncSlot, DecSigSlot)` and `DecPkSlotEnv` with
caller-supplied `Nat` cumulative, peak, request, and group bounds checked via `d3SlotMainFitsOneGiBOf`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.PeakBudget.D3MainEntryBudgetFitsCapDom0

open Arm64.Obj (Image)
open Arm64.Process (bytesOfString)
open CryptoGames.LibsignalSession (PublicKey SignalMessage)
open CryptoGames.LibsignalSessionApi (PreKeySignalMessage)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.E2E (PEParams UnreachedPqxdhPrimitives)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost uuidTryParse)
open CryptoVerification.SignalSession
  (CliHooks CliPqxdhInputs Cmd Inputs PqParty partyAddress pqRecvInputs stdinCapBytes)
open CryptoVerification.SignalSession.Cli.MainHops (AddrV CallV RunCall cliIo inputOf parseArgs)
open CryptoVerification.SignalSession.Cli.RunCompose
  (DecPkGhost DecSigGhost EncGhost PksmGhost RunSem addrValOf runAns runFiles runRel)
open CryptoVerification.SignalSession.Cli.RunProofs (encDef)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm (decodeProto pksmParse)
open CryptoVerification.SignalSession.Cli.RunRefine (parseArgs_recv)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (scopeIn)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv)
open LibsignalBinary.Heap.Fine (FineScale fineCostModel)
open LibsignalBinary.Heap.Fine.ClientBounds (fineCostModel_smallMaxReq_eq)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps (signalMessage_tryFrom_lengths_le)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith
  (cliBudgetLimits cliDecoupledRamNeed cliDecoupledRamNeed_mono cliDecoupledVaNeed
   cliDecoupledVaNeed_mono cliDefaultStaticBytes cliDefaultStaticCount cliMaxAddrTextBytes
   cliMaxDirPathBytes cliMaxDirtyEntries cliOneGiB fitsEnv_fineCostModel_of_group_literal_bounds)
open LibsignalBinary.Proofs.PeakBudget.CliGroupBounds (m5PhaseEnv_groupSpec m6Env_groupSpec)
open LibsignalBinary.Proofs.PeakBudget.CliKitEnvFitsExact
  (binaryKitSlotInit_credit binaryKitSlotInit_fineSpec binaryKitSlotInit_groups
   w1EncExactCum w1EncExactGrpS w1EncExactLive w1EncExactMaxReq w1EncExactPeak
   w2DecSigExactCum w2DecSigExactGrpS w2DecSigExactLive w2DecSigExactMaxReq w2DecSigExactPeak
   w3InitExactCum w3InitExactGrpS w3InitExactLive w3InitExactMaxReq w3InitExactPeak)
open LibsignalBinary.Proofs.PeakBudget.CliMainPeakSpec
  (M5PhaseEnv M6Env cliMainDeltaLive_tight cliMainDeltaPeak_tight cliMainMaxReq
   m3PhaseDeltaCum_tight m3PhaseMaxReq m5DirStepDeltaPeak m5DirStepMaxReq m6DeltaCum
   m6_phaseCredit_small1024)
open LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
  (W1BinarySendDom W1BinarySendParams W2BinaryWhisperDom W2BinaryWhisperParams)
open LibsignalBinary.Proofs.PeakBudget.CliRunArmsPeak
  (CliRunCalleeEnvs pksmSliceCum pksmSliceLive pksmSliceLive_le_peak pksmSliceMaxReq pksmSlicePeak)
open LibsignalBinary.Proofs.PeakBudget.CliRunPeakHelpers (phaseCredit_or_freeOnly_left)
open LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge
  (CliRunBinaryEnv OptStageEnv RealCliMainBinaryEnvOf RunArmBinaryEnv
   cliMainArmEnvs cliMainBoundedSetup_fine_groupSpec cliMainBoundedSetup_phaseCredit_fine
   cliRunBinary1MiBCustomPksmCum cliRunBinary1MiBCustomPksmMaxReq cliRunCalleesEnvs
   m5Phase_Bounded_phaseCredit_fine preEnv_sub_r0BinaryEnv r3aRecvWEnv_sub_r3aBinaryEnv
   r3bRecvPEnv_sub_r3bEnv runEnv_to_cliRunBinaryEnv_of_slots)
open LibsignalBinary.Proofs.PeakBudget.CliSlotFineSpec (SingleSlotFineSpec)
open LibsignalBinary.Proofs.PeakBudget.CliTopBudgetReal
  (CliRealCalleeFineSpecs cliRun1MiBCustomPksmLive cliRun1MiBCustomPksmPeak
   cliRunOpenedCustomPksmGrpS)
open LibsignalBinary.Proofs.PeakBudget.CliTopBudgetSpec
  (cliMainTightLiveOf cliMainTightPeakOf cliMainTightReqOf)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit (PhaseGroupSpec)
open LibsignalBinary.Proofs.PeakBudget.MainEntryBudgetFitsCapReal
  (boundedReadFileEnv_overCapSchedule mainEntryBudgetFitsCapOf_domScopedRun_cliBudgetLimits_of_kitEnvFits
   stdin_le_msgCapBytes_of_pqInputs_and_inputOf stdin_le_msgCapBytes_of_pqRecvInputs_and_inputOf)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemExact
  (hmx_binaryKitRunSlotEnvsSlotOf hmx_runEnvSlotOf_sub_runBinaryKitEnvOfSlot_of_slots
   mkBinaryKitRealCalleeEnvsSlotOf realCliRunBinaryKitEnvOfSlot)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
  (dirGetEnv_fixed_eq_of_not_overCap not_overCapFile_runFiles_own_address
   realCliInitBinarySlotEnvFixed w3InitBinaryKitSlotEnvFixed_eq_plain)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemSlots
  (recv_rest_length_le_msgCapBytes w3_realCliInitBinarySlotEnv_sub_binaryKit)
open LibsignalBinary.Proofs.PeakBudget.RealMainBinaryEnvAdapterD3
  (argv_length_le_3_of_pqOrD3Recv cliPqxdhInputs_pqRecvInputs_nil
   cliRunBinaryEnv_fine_groupSpec_of_cap cliRunBinaryEnv_real_1MiB_fine_phaseCredit_of_pqOrD3Recv)
open LibsignalBinary.Proofs.PeakBudget.RealMainEnvAdapter
  (BoundedReadFileEnv ValidPostSetupWitness boundedReadFileEnv_of_readFileRuleEnv_cliIo
   cliMainWidenedSetupFineGrpS)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas (fineCostModel_modelHyps)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (msgCapBytes sessionCapBytes)
open LibsignalBinary.Proofs.PeakBudget.WireMsgPeakSpec
  (IntoBoxedBoundedEnv IntoBoxedOptBoundedEnv SigTryFromBoundedEnv SigTryFromPostEnv
   SigTryFromPostOutPreEnv sigTryFromDeltaCum sigTryFromDeltaGrpS sigTryFromDeltaLive
   sigTryFromDeltaPeak sigTryFromMaxReq)
open LibsignalBinary.Proofs.PeakBudget.WirePksmLoopCredit (phaseCreditSpec_protoLoop4_S)
open LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit
  (PksmAfterKyberOkEnv PksmLoopTailBoundedEnv PksmPostBoundedEnv PksmTryFromLoopBoundedEnv
   phaseCreditSpec_pksmLoopTail_S phaseCreditSpec_pksmPost_blackbox
   phaseGroupSpec_pksmPost_blackbox pksmDecodedInnerBytes pksmDecodedKyberOpt
   pksmDecodedKyberOpt_length_le pksmInnerGhost pksmTryFromCapDeltaGrpS pksmTryFromDeltaCum
   pksmTryFromDeltaCum_le_cap pksmTryFromDeltaGrpS pksmTryFromDeltaGrpS_le_cap
   pksmTryFromDeltaLive pksmTryFromDeltaLive_le_cap pksmTryFromDeltaPeak
   pksmTryFromDeltaPeak_le_cap pksmTryFromLoopDeltaGrpS pksmTryFromLoop_phaseGroup
   pksmTryFromMaxReq pksmTryFromMaxReq_le_cap)
open LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromHelpers (ProtoCaps4 ProtoField4)
open LibsignalBinary.Proofs.PeakBudget.WireTryFromHelpers
  (fineCostModel_wireGroupHyps fineCostModel_wireLowInterceptHyps)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3ParseRejectF3
  (CliPqOrD3RecvInputs pqD3ScopedRun)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (ReadFileRuleEnvFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainEntryBudgetFitsInst (MainEntryBudgetFitsCapOf)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R0ProofPlacedBudget (PreEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudget (r3aDecSigGhost0)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bProofPlacedBudget (r3bDecPkGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudget (RunEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bAssemblyPlacedBudget
  (PksmAfterLoopEnv PksmFrom5b4PreEnv PksmFrom684PreEnv PksmFrom830PreEnv PksmFrom864PreEnv
   PksmPostEnv PksmPostPreEnv PksmTryFromEnv SigMsgCallEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (ReadFileRuleEnv)

/-! ## 1. `ReadFileRuleEnvFixed` → `BoundedReadFileEnv` and `PksmTryFromWireSliceEnv` -/

/-- `ReadFileRuleEnvFixed cliIo.rd` embeds into `BoundedReadFileEnv` (`MainEntryBudgetFitsCapReal`). -/
theorem boundedReadFileEnv_of_readFileRuleEnvFixed_cliIo
    (files : FsFiles) (path : List (BitVec 8)) (evs : List AllocEvent)
    (h : ReadFileRuleEnvFixed cliIo.rd files path evs) :
    BoundedReadFileEnv evs := by
  rcases h with hok | ⟨_, _, rfl⟩
  · exact boundedReadFileEnv_of_readFileRuleEnv_cliIo files path hok
  · exact boundedReadFileEnv_overCapSchedule

/-- Address-normalized wire slice projection of `W8bAssemblyPlacedBudget.PksmTryFromEnv`. -/
def PksmTryFromWireSliceEnv (rest : List (BitVec 8)) : List AllocEvent → Prop :=
  PksmTryFromEnv ⟨0#64, rest, 0#64⟩

private theorem d3z_freeOnlyEvs_nil : FreeOnlyEvs [] := by
  intro _ hm; nomatch hm

private theorem d3z_freeOnlyEvs_append {a b : List AllocEvent}
    (ha : FreeOnlyEvs a) (hb : FreeOnlyEvs b) : FreeOnlyEvs (a ++ b) := by
  intro ev hm
  rcases List.mem_append.mp hm with h1 | h2
  · exact ha ev h1
  · exact hb ev h2

private theorem d3z_seqEnv_mono {E₁ E₂ F₁ F₂ : List AllocEvent → Prop} {evs : List AllocEvent}
    (h1 : ∀ x, E₁ x → F₁ x) (h2 : ∀ x, E₂ x → F₂ x) (h : SeqEnv E₁ E₂ evs) :
    SeqEnv F₁ F₂ evs := by
  rcases h with ha | ⟨a, b, rfl, ha, hb⟩
  · exact Or.inl (h1 evs ha)
  · exact Or.inr ⟨a, b, rfl, h1 a ha, h2 b hb⟩

private theorem d3z_seqEnv_nil_freeOnly_sub {evs : List AllocEvent}
    (h : SeqEnv (· = []) FreeOnlyEvs evs) : FreeOnlyEvs evs := by
  rcases h with rfl | ⟨_, c, rfl, rfl, hc⟩
  · exact d3z_freeOnlyEvs_nil
  · simpa using hc

private theorem d3z_seqEnv_free_left_right {P Q : List AllocEvent → Prop} {evs : List AllocEvent}
    (hSub : ∀ e, SeqEnv P FreeOnlyEvs e → Q e)
    (h : SeqEnv (SeqEnv FreeOnlyEvs P) FreeOnlyEvs evs) :
    SeqEnv FreeOnlyEvs Q evs := by
  rcases h with (hf | ⟨a, b, rfl, ha, hb⟩) | ⟨ab, c, rfl, hab, hc⟩
  · exact Or.inl hf
  · exact Or.inr ⟨a, b, rfl, ha, hSub b (Or.inl hb)⟩
  · rcases hab with ha | ⟨a, b, rfl, ha, hb⟩
    · exact Or.inl (d3z_freeOnlyEvs_append ha hc)
    · exact Or.inr ⟨a, b ++ c, List.append_assoc a b c, ha,
        hSub (b ++ c) (Or.inr ⟨b, c, rfl, hb, hc⟩)⟩

private theorem d3z_seqEnv_push_free_right {E₁ P Q : List AllocEvent → Prop} {evs : List AllocEvent}
    (hFreeQ : ∀ e, FreeOnlyEvs e → Q e)
    (hSub : ∀ e, SeqEnv P FreeOnlyEvs e → Q e)
    (h : SeqEnv (SeqEnv E₁ P) FreeOnlyEvs evs) :
    SeqEnv E₁ Q evs := by
  rcases h with (h1 | ⟨a, b, rfl, h1, hp⟩) | ⟨ab, c, rfl, hab, hc⟩
  · exact Or.inl h1
  · exact Or.inr ⟨a, b, rfl, h1, hSub b (Or.inl hp)⟩
  · rcases hab with h1 | ⟨a, b, rfl, h1, hp⟩
    · exact Or.inr ⟨ab, c, rfl, h1, hFreeQ c hc⟩
    · exact Or.inr ⟨a, b ++ c, List.append_assoc a b c, h1,
        hSub (b ++ c) (Or.inr ⟨b, c, rfl, hp, hc⟩)⟩

private def d3z_mapMsgField :
    LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget.SigTryFromField →
    LibsignalBinary.Proofs.PeakBudget.WireMsgPeakSpec.SigTryFromField
  | .rk => .rk | .ct => .ct | .pq => .pq | .ad => .ad

private def d3z_mapMsgCaps
    (c : LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget.SigTryFromCaps) :
    LibsignalBinary.Proofs.PeakBudget.WireMsgPeakSpec.SigTryFromCaps :=
  ⟨c.rk, c.ct, c.pq, c.ad⟩

private theorem d3z_mapMsgCaps_get
    (c : LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget.SigTryFromCaps)
    (f : LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget.SigTryFromField) :
    (d3z_mapMsgCaps c).get (d3z_mapMsgField f) = c.get f := by
  cases f <;> rfl

private theorem d3z_mapMsgCaps_set
    (c : LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget.SigTryFromCaps)
    (f : LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget.SigTryFromField) (v : Nat) :
    d3z_mapMsgCaps (c.set f v) = (d3z_mapMsgCaps c).set (d3z_mapMsgField f) v := by
  cases f <;> rfl

private theorem d3z_sigErrTail_concrete_sub_msg {evs : List AllocEvent}
    (h : LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget.SigTryFromErrTailEnv evs) :
    LibsignalBinary.Proofs.PeakBudget.WireMsgPeakSpec.SigTryFromErrTailEnv evs := by
  cases h with
  | nil => exact .nil
  | fromOnly => exact .fromOnly
  | fromPush hp => exact .fromPush hp

private theorem d3z_sigLoop_concrete_sub_msg {rem : Nat}
    {caps : LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget.SigTryFromCaps}
    {evs : List AllocEvent}
    (h : LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget.SigTryFromLoopBoundedEnv
      rem caps evs) :
    LibsignalBinary.Proofs.PeakBudget.WireMsgPeakSpec.SigTryFromLoopBoundedEnv
      rem (d3z_mapMsgCaps caps) evs := by
  induction h with
  | done ht =>
    exact .done (d3z_sigErrTail_concrete_sub_msg ht)
  | skipStep hlt _ ih =>
    exact .skipStep hlt ih
  | @bytesStep f rem rem' caps wt bs v rest evs₂ hm hlen hprog hcap _ ih =>
    rw [← d3z_mapMsgCaps_get caps f]
    refine .bytesStep (d3z_mapMsgField f) wt bs v rest hm hlen hprog ?_ ?_
    · rw [d3z_mapMsgCaps_get]; exact hcap
    · rw [d3z_mapMsgCaps_get, ← d3z_mapMsgCaps_set]; exact ih

private def d3z_mapProtoField4 :
    LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget.SigTryFromField → ProtoField4
  | .rk => .f0 | .ct => .f1 | .pq => .f2 | .ad => .f3

private def d3z_mapProtoCaps4
    (c : LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget.SigTryFromCaps) : ProtoCaps4 :=
  ⟨c.rk, c.ct, c.pq, c.ad⟩

private theorem d3z_mapProtoCaps4_get
    (c : LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget.SigTryFromCaps)
    (f : LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget.SigTryFromField) :
    (d3z_mapProtoCaps4 c).get (d3z_mapProtoField4 f) = c.get f := by
  cases f <;> rfl

private theorem d3z_mapProtoCaps4_set
    (c : LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget.SigTryFromCaps)
    (f : LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget.SigTryFromField) (v : Nat) :
    d3z_mapProtoCaps4 (c.set f v) = (d3z_mapProtoCaps4 c).set (d3z_mapProtoField4 f) v := by
  cases f <;> rfl

private theorem d3z_sigLoop_concrete_sub_pksmLoop {rem : Nat}
    {caps : LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget.SigTryFromCaps}
    {evs : List AllocEvent}
    (h : LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget.SigTryFromLoopBoundedEnv
      rem caps evs) :
    PksmTryFromLoopBoundedEnv rem (d3z_mapProtoCaps4 caps) evs := by
  induction h with
  | done ht =>
    exact .done (PksmLoopTailBoundedEnv.of_sigTryFromErrTail (d3z_sigErrTail_concrete_sub_msg ht))
  | skipStep hlt _ ih =>
    exact .skipStep (Nat.le_of_lt hlt) ih
  | @bytesStep f rem rem' caps wt bs v rest evs₂ hm hlen hprog hcap _ ih =>
    rw [← d3z_mapProtoCaps4_get caps f]
    refine .bytesStep (d3z_mapProtoField4 f) wt bs v rest hm hlen hprog ?_ ?_
    · rw [d3z_mapProtoCaps4_get]
      exact Nat.lt_trans hcap (by decide : 2 ^ 63 < 2 ^ 64)
    · rw [d3z_mapProtoCaps4_get, ← d3z_mapProtoCaps4_set]
      exact ih

private theorem d3z_intoBoxed_concrete_sub_msg {bs : List (BitVec 8)} {evs : List AllocEvent}
    (h : LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBudget.IntoBoxedBoundedEnv bs evs) :
    IntoBoxedBoundedEnv bs evs := by
  rcases h with ⟨cap, h1, h2, rfl⟩
  exact ⟨cap, h1, h2, rfl⟩

private theorem d3z_intoBoxedOpt_concrete_sub_msg {opt : Option (List (BitVec 8))}
    {evs : List AllocEvent}
    (h : LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBudget.IntoBoxedOptBoundedEnv
      opt evs) :
    IntoBoxedOptBoundedEnv opt evs := by
  cases opt with
  | none => exact h
  | some ad => exact d3z_intoBoxed_concrete_sub_msg h

private theorem d3z_sigPost_concrete_sub_msg {bs : List (BitVec 8)} {evs : List AllocEvent}
    (h : LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBudget.TryFromPostEnv bs evs) :
    SigTryFromPostEnv bs evs := by
  refine d3z_seqEnv_mono (fun evs₁ hpre => ?_) (fun _ hf => hf) h
  unfold LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBudget.TryFromPostOutPreEnv at hpre
  unfold SigTryFromPostOutPreEnv
  cases htr : SignalMessage.tryFrom protoSignalCodec bs with
  | error _ =>
    rw [htr] at hpre
    exact hpre
  | ok _ =>
    rw [htr] at hpre
    exact d3z_seqEnv_mono (fun _ hf => hf)
      (fun _ hok => d3z_seqEnv_mono (fun _ hct => d3z_intoBoxed_concrete_sub_msg hct)
        (fun _ hrest => d3z_seqEnv_mono (fun _ had => d3z_intoBoxedOpt_concrete_sub_msg had)
          (fun _ hcl => hcl) hrest) hok) hpre

private theorem d3z_sigMsgCallEnv_sub_bounded (msg : List (BitVec 8)) {evs : List AllocEvent}
    (h : SigMsgCallEnv msg evs) :
    SigTryFromBoundedEnv ⟨0#64, msg, 0#64⟩ evs := by
  cases h with
  | nil =>
    exact Or.inl rfl
  | loopOnly h1 =>
    exact Or.inr (Or.inl (d3z_sigLoop_concrete_sub_msg h1))
  | loopPost h1 h2 =>
    exact Or.inr (Or.inr ⟨_, _, rfl, d3z_sigLoop_concrete_sub_msg h1, d3z_sigPost_concrete_sub_msg h2⟩)

private def d3z_PksmTryFromWideEnv (x : PksmGhost) (evs : List AllocEvent) : Prop :=
  evs = [] ∨
  SeqEnv (PksmTryFromLoopBoundedEnv x.bytes.length ProtoCaps4.zero)
    (SeqEnv FreeOnlyEvs
      (PksmPostBoundedEnv x.bytes (pksmDecodedKyberOpt x.bytes) (pksmInnerGhost x))) evs

private theorem d3z_pksmFrom864_sub_afterKyber (xBytes msg : List (BitVec 8)) {evs : List AllocEvent}
    (h : SeqEnv (PksmFrom864PreEnv xBytes msg) FreeOnlyEvs evs) :
    PksmAfterKyberOkEnv xBytes ⟨0#64, msg, 0#64⟩ evs := by
  unfold PksmFrom864PreEnv at h
  cases htr : SignalMessage.tryFrom protoSignalCodec msg with
  | error _ =>
    rw [htr] at h
    exact Or.inr (d3z_seqEnv_mono (fun _ hs => d3z_sigMsgCallEnv_sub_bounded msg hs)
      (fun _ hf => Or.inl (Or.inl hf)) h)
  | ok _ =>
    rw [htr] at h
    exact Or.inr
      (d3z_seqEnv_mono (fun _ hs => d3z_sigMsgCallEnv_sub_bounded msg hs) (fun _ hq => hq)
        (d3z_seqEnv_push_free_right (fun _ hf => Or.inl (Or.inl hf))
          (fun _ hc => Or.inl (Or.inr hc)) h))

private theorem d3z_pksmFrom830_sub_afterKyber (xBytes ik msg : List (BitVec 8))
    {evs : List AllocEvent}
    (h : SeqEnv (PksmFrom830PreEnv xBytes ik msg) FreeOnlyEvs evs) :
    PksmAfterKyberOkEnv xBytes ⟨0#64, msg, 0#64⟩ evs := by
  unfold PksmFrom830PreEnv at h
  cases hik : PublicKey.deserialize ik with
  | error _ =>
    rw [hik] at h
    exact Or.inl (d3z_seqEnv_nil_freeOnly_sub h)
  | ok _ =>
    rw [hik] at h
    exact d3z_pksmFrom864_sub_afterKyber xBytes msg h

private theorem d3z_pksmFrom5b4_sub_postBounded (vb : BitVec 8) (xBytes bk ik msg : List (BitVec 8))
    (kpkOpt : Option (BitVec 32)) (kyberOpt : Option (List (BitVec 8)))
    {evs : List AllocEvent}
    (h : SeqEnv (PksmFrom5b4PreEnv vb xBytes bk ik msg kpkOpt kyberOpt) FreeOnlyEvs evs) :
    PksmPostBoundedEnv xBytes kyberOpt ⟨0#64, msg, 0#64⟩ evs := by
  unfold PksmFrom5b4PreEnv at h
  cases hbk : PublicKey.deserialize bk with
  | error _ =>
    rw [hbk] at h
    exact Or.inl (d3z_seqEnv_nil_freeOnly_sub h)
  | ok _ =>
    rw [hbk] at h
    unfold PksmFrom684PreEnv at h
    by_cases h1 : (kpkOpt.isSome != kyberOpt.isSome) = true
    · simp only [h1, ↓reduceIte] at h
      exact Or.inr (Or.inl (d3z_seqEnv_mono (fun _ he => Or.inl he) (fun _ hf => hf) h))
    · simp only [h1, Bool.false_eq_true, ↓reduceIte] at h
      by_cases h2 : kpkOpt = none ∧ kyberOpt = none ∧ 0x40 ≤ vb.toNat
      · simp only [h2, and_self, ↓reduceIte] at h
        exact Or.inr (Or.inl (d3z_seqEnv_mono (fun _ he => Or.inr he) (fun _ hf => hf) h))
      · simp only [h2, ↓reduceIte] at h
        have hbox :=
          d3z_seqEnv_mono (fun _ hb => d3z_intoBoxedOpt_concrete_sub_msg hb) (fun _ hq => hq)
            (d3z_seqEnv_push_free_right (fun _ hf => Or.inl hf)
              (fun _ hp => d3z_pksmFrom830_sub_afterKyber xBytes ik msg hp) h)
        exact Or.inr (Or.inr (Or.inr ⟨[], evs, rfl, d3z_freeOnlyEvs_nil, hbox⟩))

private theorem d3z_pksmAfterLoop_sub_free_post (x : PksmGhost) (vb b1 : BitVec 8)
    (bs1 : List (BitVec 8)) (hx : x.bytes = vb :: b1 :: bs1) {evs₂ : List AllocEvent}
    (h : PksmAfterLoopEnv vb x.bytes (decodeProto (b1 :: bs1)) evs₂) :
    SeqEnv FreeOnlyEvs
      (PksmPostBoundedEnv x.bytes (pksmDecodedKyberOpt x.bytes) (pksmInnerGhost x)) evs₂ := by
  cases hd : decodeProto (b1 :: bs1) with
  | none =>
    rw [hd] at h
    exact Or.inl h
  | some m =>
    rw [hd] at h
    unfold PksmAfterLoopEnv PksmPostEnv PksmPostPreEnv at h
    rcases hbk : m.baseKey with _ | bk <;>
      rcases hik : m.identityKey with _ | ik <;>
      rcases hmsg : m.message with _ | msg <;>
      rcases hsid : m.signedPreKeyId with _ | sid
    all_goals simp only [hbk, hik, hmsg, hsid] at h
    case some.some.some.some =>
      have hky : pksmDecodedKyberOpt x.bytes = m.kyberCiphertext := by
        rw [hx]; simp [pksmDecodedKyberOpt, hd]
      have hin : pksmInnerGhost x = ⟨0#64, msg, 0#64⟩ := by
        unfold pksmInnerGhost
        rw [hx]
        simp [pksmDecodedInnerBytes, hd, hmsg]
      rw [hky, hin]
      exact d3z_seqEnv_free_left_right
        (fun _ hs => d3z_pksmFrom5b4_sub_postBounded vb x.bytes bk ik msg m.kyberPreKeyId
          m.kyberCiphertext hs) h
    all_goals exact Or.inl (d3z_seqEnv_nil_freeOnly_sub h)

private theorem d3z_pksmTryFromEnv_sub_wide (x : PksmGhost) {evs : List AllocEvent}
    (h : PksmTryFromEnv x evs) : d3z_PksmTryFromWideEnv x evs := by
  cases h with
  | nil =>
    exact Or.inl rfl
  | loopOnly _ _ _ hloop =>
    exact Or.inr (Or.inl (d3z_sigLoop_concrete_sub_pksmLoop hloop))
  | loopAfter hx _ _ hloop hafter =>
    exact Or.inr (Or.inr ⟨_, _, rfl, d3z_sigLoop_concrete_sub_pksmLoop hloop,
      d3z_pksmAfterLoop_sub_free_post x _ _ _ hx hafter⟩)

private theorem d3z_pksmTryFromWide_phaseCredit (x : PksmGhost) :
    PhaseCreditSpec fineCostModel (d3z_PksmTryFromWideEnv x)
      (pksmTryFromDeltaCum x) (pksmTryFromDeltaLive x)
      (pksmTryFromDeltaPeak x) (pksmTryFromMaxReq x) := by
  have hLoop :=
    phaseCreditSpec_protoLoop4_S fineCostModel_modelHyps fineCostModel_wireLowInterceptHyps
      fineCostModel_wireLowInterceptHyps.hSmallMaxEq (by decide) x.bytes.length
      (phaseCreditSpec_pksmLoopTail_S fineCostModel_modelHyps
        fineCostModel_wireLowInterceptHyps.hSmallMaxEq (by decide))
  have hFree : PhaseCreditSpec fineCostModel FreeOnlyEvs 0 0 0 0 :=
    PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps
  have hPost0 :=
    phaseCreditSpec_pksmPost_blackbox fineCostModel_modelHyps fineCostModel_wireLowInterceptHyps
      x.bytes (pksmDecodedKyberOpt x.bytes) (pksmInnerGhost x)
      (pksmDecodedKyberOpt_length_le x.bytes)
  have hPost :
      PhaseCreditSpec fineCostModel
        (SeqEnv FreeOnlyEvs
          (PksmPostBoundedEnv x.bytes (pksmDecodedKyberOpt x.bytes) (pksmInnerGhost x)))
        (4 * min x.bytes.length 135167 + 19078 + sigTryFromDeltaCum (pksmInnerGhost x))
        (2 * x.bytes.length + 16390 + sigTryFromDeltaLive (pksmInnerGhost x))
        (2 * x.bytes.length + 16390 + sigTryFromDeltaLive (pksmInnerGhost x) +
          sigTryFromDeltaPeak (pksmInnerGhost x))
        (max 68 (max x.bytes.length (sigTryFromMaxReq (pksmInnerGhost x)))) :=
    (hFree.seq hPost0).mono (by omega) (by omega) (by omega) (by omega)
  have hNil := PhaseCreditSpec.nil fineCostModel
  unfold pksmTryFromDeltaCum pksmTryFromDeltaLive pksmTryFromDeltaPeak pksmTryFromMaxReq
  exact ((hNil.or (hLoop.seq hPost)).of_imp (fun _ he => he)).mono
    (by omega) (by omega) (by omega) (by omega)

private theorem d3z_pksmTryFromWide_phaseGroup (x : PksmGhost) :
    PhaseGroupSpec fineCostModel (d3z_PksmTryFromWideEnv x) (pksmTryFromDeltaGrpS x) := by
  have hLoop := pksmTryFromLoop_phaseGroup fineCostModel_wireGroupHyps x.bytes.length
  unfold pksmTryFromLoopDeltaGrpS at hLoop
  have hFree : PhaseGroupSpec fineCostModel FreeOnlyEvs 0 :=
    PhaseGroupSpec.freeOnly fineCostModel
  have hPost :
      PhaseGroupSpec fineCostModel
        (SeqEnv FreeOnlyEvs
          (PksmPostBoundedEnv x.bytes (pksmDecodedKyberOpt x.bytes) (pksmInnerGhost x)))
        (280022 + sigTryFromDeltaGrpS (pksmInnerGhost x)) :=
    (hFree.seq
      (phaseGroupSpec_pksmPost_blackbox fineCostModel_wireGroupHyps x.bytes
        (pksmDecodedKyberOpt x.bytes) (pksmInnerGhost x))).mono (by omega)
  have hNil := PhaseGroupSpec.nil fineCostModel
  unfold pksmTryFromDeltaGrpS
  exact ((hNil.or (hLoop.seq hPost)).of_imp (fun _ he => he)).mono (by omega)

/-- `fineCostModel` `PhaseCreditSpec` for `PksmTryFromWireSliceEnv` matching `PksmTryFromSliceEnv`. -/
theorem pksmTryFromWireSlice_phaseCredit {rest : List (BitVec 8)}
    (hlen : rest.length ≤ msgCapBytes) :
    PhaseCreditSpec fineCostModel (PksmTryFromWireSliceEnv rest)
      (pksmSliceCum msgCapBytes) (pksmSliceLive msgCapBytes)
      (pksmSlicePeak msgCapBytes) (pksmSliceMaxReq msgCapBytes) := by
  have hWide :=
    (d3z_pksmTryFromWide_phaseCredit ⟨0#64, rest, 0#64⟩).of_imp
      (fun _ he => d3z_pksmTryFromEnv_sub_wide ⟨0#64, rest, 0#64⟩ he)
  exact hWide.mono
    (pksmTryFromDeltaCum_le_cap hlen)
    (pksmTryFromDeltaLive_le_cap hlen)
    (pksmTryFromDeltaPeak_le_cap hlen)
    (pksmTryFromMaxReq_le_cap hlen)

/-- `fineCostModel` `PhaseGroupSpec` for `PksmTryFromWireSliceEnv` matching `PksmTryFromSliceEnv`. -/
theorem pksmTryFromWireSlice_fine_groupSpec {rest : List (BitVec 8)}
    (hlen : rest.length ≤ msgCapBytes) :
    PhaseGroupSpec fineCostModel (PksmTryFromWireSliceEnv rest)
      (pksmTryFromCapDeltaGrpS msgCapBytes) := by
  have hWide :=
    (d3z_pksmTryFromWide_phaseGroup ⟨0#64, rest, 0#64⟩).of_imp
      (fun _ he => d3z_pksmTryFromEnv_sub_wide ⟨0#64, rest, 0#64⟩ he)
  exact hWide.mono (pksmTryFromDeltaGrpS_le_cap hlen)

/-! ## 2. Closed-Form D3 Whole-`main` Arithmetic and Cap-Parametric `FitsEnv` -/

/-- Slot-parametric D3 `CliRunCalleeEnvs` bundle using `PksmTryFromWireSliceEnv` on `pksmEnv`,
`mkBinaryKitRealCalleeEnvsSlotOf EncSlot DecSigSlot` on `initEnv` / `encEnv` / `decSigEnv`, and
parametric `decPkEnv`. -/
noncomputable def mkD3BinaryKitCalleeEnvsSlotOf [LibsignalPlacement]
    (EncSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → EncGhost → List AllocEvent → Prop)
    (DecSigSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → DecSigGhost → List AllocEvent → Prop)
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (decPkEnv : RunCall → List AllocEvent → Prop) (g : RunCall) : CliRunCalleeEnvs :=
  { mkBinaryKitRealCalleeEnvsSlotOf EncSlot DecSigSlot img S X W g with
    pksmEnv := PksmTryFromWireSliceEnv
    decPkEnv := decPkEnv g }

/-- Parametric D3 whole-`main` `Δcum` from custom slot caps (`PksmTryFromWireSliceEnv` +
`w3InitExact*`). -/
def d3SlotMainCumOf (encCum decSigCum decPkCum : Nat) : Nat :=
  let runCum := cliRunBinary1MiBCustomPksmCum
    (pksmSliceCum msgCapBytes) w3InitExactCum encCum decSigCum decPkCum
  123250 + m3PhaseDeltaCum_tight + runCum +
    cliMaxDirtyEntries *
      (10 * max (4 * cliMaxDirPathBytes + cliMaxAddrTextBytes + 16) 16 + 4 * 9539) +
    m6DeltaCum

/-- Parametric D3 whole-`main` `Δlive` from custom slot caps. -/
def d3SlotMainLiveOf (encLive decSigLive decPkLive : Nat) : Nat :=
  cliMainTightLiveOf
    (cliRun1MiBCustomPksmLive
      (pksmSliceLive msgCapBytes) w3InitExactLive encLive decSigLive decPkLive)

/-- Parametric D3 whole-`main` `Δpeak` keeping `decSigLive` and `decPkLive` independent of `Peak`. -/
def d3SlotMainPeakGenOf
    (encLive encPeak decSigLive decSigPeak decPkLive decPkPeak : Nat) : Nat :=
  cliMainTightPeakOf
    (cliRun1MiBCustomPksmLive
      (pksmSliceLive msgCapBytes) w3InitExactLive encLive decSigLive decPkLive)
    (cliRun1MiBCustomPksmPeak
      (pksmSliceLive msgCapBytes) (pksmSlicePeak msgCapBytes)
      w3InitExactPeak encLive encPeak decSigPeak decPkPeak)

/-- Parametric D3 whole-`main` `maxReq` from custom slot caps. -/
def d3SlotMainReqOf (encMaxReq decSigMaxReq decPkMaxReq : Nat) : Nat :=
  max (max (16 * 2048) 16384)
    (cliMainTightReqOf
      (cliRunBinary1MiBCustomPksmMaxReq
        (pksmSliceMaxReq msgCapBytes) w3InitExactMaxReq encMaxReq decSigMaxReq decPkMaxReq))

/-- Parametric D3 whole-`main` scaled group count `grpS` from custom slot caps. -/
def d3SlotMainGrpSOf (encGrpS decSigGrpS decPkGrpS : Nat) : Nat :=
  let runGrpS := cliRunOpenedCustomPksmGrpS msgCapBytes
    (pksmTryFromCapDeltaGrpS msgCapBytes) w3InitExactGrpS encGrpS decSigGrpS decPkGrpS +
    27 * FineScale
  cliMainWidenedSetupFineGrpS + runGrpS +
    cliMaxDirtyEntries * (12 * FineScale) + 3 * FineScale

/-- Decidable arithmetic predicate for D3 whole-`main` `1 GiB` physical RAM and `2 ^ 48` VA closure at `(enc*, decSig*, decPk*)`. -/
def d3SlotMainFitsOneGiBOf
    (encCum encLive encPeak encMaxReq encGrpS
     decSigCum decSigLive decSigPeak decSigMaxReq decSigGrpS
     decPkCum decPkLive decPkPeak decPkMaxReq decPkGrpS : Nat) : Prop :=
  let rGrpS := cliRunOpenedCustomPksmGrpS msgCapBytes
    (pksmTryFromCapDeltaGrpS msgCapBytes) w3InitExactGrpS
    encGrpS decSigGrpS decPkGrpS
  let mCum := d3SlotMainCumOf encCum decSigCum decPkCum
  let mPeak := d3SlotMainPeakGenOf encLive encPeak decSigLive decSigPeak decPkLive decPkPeak
  let mReq := d3SlotMainReqOf encMaxReq decSigMaxReq decPkMaxReq
  let mGrpS := d3SlotMainGrpSOf encGrpS decSigGrpS decPkGrpS
  15 * FineScale ≤ rGrpS ∧
  234 * FineScale + w3InitExactGrpS ≤ rGrpS - 15 * FineScale ∧
  cliDecoupledRamNeed cliDefaultStaticBytes mCum mPeak mReq
    ((mGrpS + FineScale - 1) / FineScale) ≤ cliOneGiB ∧
  cliDecoupledVaNeed cliDefaultStaticBytes cliDefaultStaticCount mCum mPeak mReq
    ((mGrpS + FineScale - 1) / FineScale) ≤ 2 ^ 48

private theorem d3z_max_mono {a1 a2 b1 b2 : Nat} (ha : a1 ≤ a2) (hb : b1 ≤ b2) :
    max a1 b1 ≤ max a2 b2 :=
  Nat.max_le.mpr ⟨Nat.le_trans ha (Nat.le_max_left _ _), Nat.le_trans hb (Nat.le_max_right _ _)⟩

private theorem d3z_optStage_phaseCredit {P : List AllocEvent → Prop} {c l p r : Nat}
    (h : PhaseCreditSpec fineCostModel P c l p r) :
    PhaseCreditSpec fineCostModel (OptStageEnv P) c l p r :=
  phaseCredit_or_freeOnly_left fineCostModel_modelHyps (fun _ hf => hf) h

private theorem d3z_optStage_groupSpec {P : List AllocEvent → Prop} {g : Nat}
    (h : PhaseGroupSpec fineCostModel P g) :
    PhaseGroupSpec fineCostModel (OptStageEnv P) g :=
  ((PhaseGroupSpec.freeOnly fineCostModel).or h).mono
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)

private theorem d3z_exists_cliPqxdhInputs_same_argv_runFiles {P : PEParams} {g : RunCall}
    (hi : CliPqOrD3RecvInputs P g.i) :
    ∃ g₀ : RunCall, CliPqxdhInputs P g₀.i ∧ g₀.c = g.c ∧
      g₀.i.argv = g.i.argv ∧ runFiles g₀.i = runFiles g.i := by
  rcases hi with hi_pq | ⟨st, ct, rc, hwf, hgi⟩
  · exact ⟨g, hi_pq, rfl, rfl, rfl⟩
  · exact ⟨{ g with i := pqRecvInputs P st [] rc },
      cliPqxdhInputs_pqRecvInputs_nil hwf rc, rfl,
      by rw [hgi]; rfl,
      by rw [hgi]; rfl⟩

private theorem d3z_parseArgs_pqRecvInputs_is_recv {P : PEParams} {st : PqParty}
    {ct : List (BitVec 8)} {rc : BitVec 256} {c : CallV}
    (hp : parseArgs uuidTryParse ((pqRecvInputs P st ct rc).argv.map bytesOfString) = some c) :
    ∃ peerV : AddrV, c = .recv peerV := by
  have ha : (pqRecvInputs P st ct rc).argv = (Cmd.recv (partyAddress st.party.other)).argv := rfl
  rw [ha, parseArgs_recv] at hp
  injection hp with hc
  exact ⟨_, hc.symm⟩

private theorem d3z_non_recv_is_cliPqxdhInputs {P : PEParams} {g : RunCall}
    (hi : CliPqOrD3RecvInputs P g.i)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c)
    (hnot_recv : ∀ peerV, g.c ≠ .recv peerV) :
    CliPqxdhInputs P g.i := by
  rcases hi with hpq | ⟨st, ct, rc, _, hgi⟩
  · exact hpq
  · obtain ⟨peerV, hc_recv⟩ := d3z_parseArgs_pqRecvInputs_is_recv (hgi ▸ hparse)
    exact False.elim (hnot_recv peerV hc_recv)

private theorem d3z_slotInit_credit [LibsignalPlacement]
    (EncSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → EncGhost → List AllocEvent → Prop)
    (DecSigSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → DecSigGhost → List AllocEvent → Prop)
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (g : RunCall)
    (hi_g : CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c) :
    PhaseCreditSpec fineCostModel
      ((mkBinaryKitRealCalleeEnvsSlotOf EncSlot DecSigSlot img S X W g).initEnv)
      w3InitExactCum w3InitExactLive w3InitExactPeak w3InitExactMaxReq := by
  rcases hi_g with hi_pq | ⟨st, ct, rc, _, hgi⟩
  · exact binaryKitSlotInit_credit EncSlot DecSigSlot img S X W g hi_pq
  · obtain ⟨peerV, hgc⟩ := d3z_parseArgs_pqRecvInputs_is_recv (hgi ▸ hparse)
    rcases g with ⟨gi, gc, ga, gres, gcall, gstores, ginp, gcoins⟩
    dsimp only at hgc
    subst hgc
    exact (PhaseCreditSpec.nil fineCostModel).of_imp (fun _ h => False.elim h)
      |>.mono (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)

private theorem d3z_slotInit_groups [LibsignalPlacement]
    (EncSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → EncGhost → List AllocEvent → Prop)
    (DecSigSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → DecSigGhost → List AllocEvent → Prop)
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (g : RunCall)
    (hi_g : CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c) :
    PhaseGroupSpec fineCostModel
      ((mkBinaryKitRealCalleeEnvsSlotOf EncSlot DecSigSlot img S X W g).initEnv)
      w3InitExactGrpS := by
  rcases hi_g with hi_pq | ⟨st, ct, rc, _, hgi⟩
  · exact binaryKitSlotInit_groups EncSlot DecSigSlot img S X W g hi_pq
  · obtain ⟨peerV, hgc⟩ := d3z_parseArgs_pqRecvInputs_is_recv (hgi ▸ hparse)
    rcases g with ⟨gi, gc, ga, gres, gcall, gstores, ginp, gcoins⟩
    dsimp only at hgc
    subst hgc
    exact (PhaseGroupSpec.nil fineCostModel).of_imp (fun _ h => False.elim h)
      |>.mono (Nat.zero_le _)

private theorem d3z_w3InitExact_lp : w3InitExactLive ≤ w3InitExactPeak := by
  decide

private def d3z_d3SlotCalleeFineSpecs [LibsignalPlacement]
    (EncSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → EncGhost → List AllocEvent → Prop)
    (DecSigSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → DecSigGhost → List AllocEvent → Prop)
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    {decPkEnv : RunCall → List AllocEvent → Prop}
    {g : RunCall}
    (Senc : SingleSlotFineSpec
      ((mkD3BinaryKitCalleeEnvsSlotOf EncSlot DecSigSlot img S X W decPkEnv g).encEnv))
    (Sds : SingleSlotFineSpec
      ((mkD3BinaryKitCalleeEnvsSlotOf EncSlot DecSigSlot img S X W decPkEnv g).decSigEnv))
    (Spk : SingleSlotFineSpec
      ((mkD3BinaryKitCalleeEnvsSlotOf EncSlot DecSigSlot img S X W decPkEnv g).decPkEnv))
    (hi_g : CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c) :
    CliRealCalleeFineSpecs
      (mkD3BinaryKitCalleeEnvsSlotOf EncSlot DecSigSlot img S X W decPkEnv g) where
  initCum := w3InitExactCum
  initLive := w3InitExactLive
  initPeak := w3InitExactPeak
  initMaxReq := w3InitExactMaxReq
  initGrpS := w3InitExactGrpS
  init_spec := d3z_slotInit_credit EncSlot DecSigSlot img S X W g hi_g hparse
  init_lp := d3z_w3InitExact_lp
  init_grp := d3z_slotInit_groups EncSlot DecSigSlot img S X W g hi_g hparse
  encCum := Senc.cum
  encLive := Senc.live
  encPeak := Senc.peak
  encMaxReq := Senc.maxReq
  encGrpS := Senc.grpS
  enc_spec := Senc.credit
  enc_lp := Senc.live_le_peak
  enc_grp := Senc.groups
  decSigCum := Sds.cum
  decSigLive := Sds.live
  decSigPeak := Sds.peak
  decSigMaxReq := Sds.maxReq
  decSigGrpS := Sds.grpS
  decSig_spec := Sds.credit
  decSig_lp := Sds.live_le_peak
  decSig_grp := Sds.groups
  pksmCum := pksmSliceCum msgCapBytes
  pksmLive := pksmSliceLive msgCapBytes
  pksmPeak := pksmSlicePeak msgCapBytes
  pksmMaxReq := pksmSliceMaxReq msgCapBytes
  pksmGrpS := pksmTryFromCapDeltaGrpS msgCapBytes
  pksm_spec := fun _ hrest => pksmTryFromWireSlice_phaseCredit hrest
  pksm_lp := pksmSliceLive_le_peak msgCapBytes
  pksm_grp := fun _ hrest => pksmTryFromWireSlice_fine_groupSpec hrest
  decPkCum := Spk.cum
  decPkLive := Spk.live
  decPkPeak := Spk.peak
  decPkMaxReq := Spk.maxReq
  decPkGrpS := Spk.grpS
  decPk_spec := Spk.credit
  decPk_lp := Spk.live_le_peak
  decPk_grp := Spk.groups

private theorem d3z_d3SlotCalleeFineSpecs_bounds [LibsignalPlacement]
    (EncSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → EncGhost → List AllocEvent → Prop)
    (DecSigSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → DecSigGhost → List AllocEvent → Prop)
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    {decPkEnv : RunCall → List AllocEvent → Prop}
    {g : RunCall}
    (Senc : SingleSlotFineSpec
      ((mkD3BinaryKitCalleeEnvsSlotOf EncSlot DecSigSlot img S X W decPkEnv g).encEnv))
    (Sds : SingleSlotFineSpec
      ((mkD3BinaryKitCalleeEnvsSlotOf EncSlot DecSigSlot img S X W decPkEnv g).decSigEnv))
    (Spk : SingleSlotFineSpec
      ((mkD3BinaryKitCalleeEnvsSlotOf EncSlot DecSigSlot img S X W decPkEnv g).decPkEnv))
    {encCum encLive encPeak encMaxReq encGrpS
     decSigCum decSigLive decSigPeak decSigMaxReq decSigGrpS
     decPkCum decPkLive decPkPeak decPkMaxReq decPkGrpS : Nat}
    (hEnc : Senc.cum ≤ encCum ∧ Senc.live ≤ encLive ∧ Senc.peak ≤ encPeak ∧
      Senc.maxReq ≤ encMaxReq ∧ Senc.grpS ≤ encGrpS)
    (hDs : Sds.cum ≤ decSigCum ∧ Sds.live ≤ decSigLive ∧ Sds.peak ≤ decSigPeak ∧
      Sds.maxReq ≤ decSigMaxReq ∧ Sds.grpS ≤ decSigGrpS)
    (hPk : Spk.cum ≤ decPkCum ∧ Spk.live ≤ decPkLive ∧ Spk.peak ≤ decPkPeak ∧
      Spk.maxReq ≤ decPkMaxReq ∧ Spk.grpS ≤ decPkGrpS)
    (hi_g : CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c) :
    let SE := d3z_d3SlotCalleeFineSpecs EncSlot DecSigSlot img S X W Senc Sds Spk hi_g hparse
    cliRunBinary1MiBCustomPksmCum
      SE.pksmCum SE.initCum SE.encCum SE.decSigCum SE.decPkCum ≤
      cliRunBinary1MiBCustomPksmCum
        (pksmSliceCum msgCapBytes) w3InitExactCum encCum decSigCum decPkCum ∧
    cliRun1MiBCustomPksmLive
      SE.pksmLive SE.initLive SE.encLive SE.decSigLive SE.decPkLive ≤
      cliRun1MiBCustomPksmLive
        (pksmSliceLive msgCapBytes) w3InitExactLive encLive decSigLive decPkLive ∧
    cliRun1MiBCustomPksmPeak
      SE.pksmLive SE.pksmPeak SE.initPeak SE.encLive SE.encPeak SE.decSigPeak SE.decPkPeak ≤
      cliRun1MiBCustomPksmPeak
        (pksmSliceLive msgCapBytes) (pksmSlicePeak msgCapBytes)
        w3InitExactPeak encLive encPeak decSigPeak decPkPeak ∧
    cliRunBinary1MiBCustomPksmMaxReq
      SE.pksmMaxReq SE.initMaxReq SE.encMaxReq SE.decSigMaxReq SE.decPkMaxReq ≤
      cliRunBinary1MiBCustomPksmMaxReq
        (pksmSliceMaxReq msgCapBytes) w3InitExactMaxReq encMaxReq decSigMaxReq decPkMaxReq ∧
    cliRunOpenedCustomPksmGrpS msgCapBytes
      SE.pksmGrpS SE.initGrpS SE.encGrpS SE.decSigGrpS SE.decPkGrpS ≤
      cliRunOpenedCustomPksmGrpS msgCapBytes
        (pksmTryFromCapDeltaGrpS msgCapBytes) w3InitExactGrpS encGrpS decSigGrpS decPkGrpS := by
  rcases hEnc with ⟨hec, hel, hep, her, heg⟩
  rcases hDs with ⟨hdc, hdl, hdp, hdr, hdg⟩
  rcases hPk with ⟨hpc, hpl, hpp, hpr, hpg⟩
  dsimp only [d3z_d3SlotCalleeFineSpecs]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold cliRunBinary1MiBCustomPksmCum
    exact Nat.add_le_add (Nat.le_refl _)
      (d3z_max_mono (Nat.le_refl _)
        (d3z_max_mono (Nat.add_le_add hec (Nat.le_refl _))
          (d3z_max_mono (Nat.add_le_add (Nat.le_refl _) hdc)
            (Nat.add_le_add (Nat.le_refl _) hpc))))
  · unfold cliRun1MiBCustomPksmLive
    have hr2l :
        CliRunArmsPeak.r2DeltaLive fineCostModel Senc.live sessionCapBytes ≤
          CliRunArmsPeak.r2DeltaLive fineCostModel encLive sessionCapBytes := by
      unfold CliRunArmsPeak.r2DeltaLive
      exact Nat.add_le_add hel (Nat.le_refl _)
    exact Nat.add_le_add (Nat.le_refl _)
      (d3z_max_mono (Nat.le_refl _)
        (d3z_max_mono hr2l
          (d3z_max_mono (Nat.add_le_add (Nat.le_refl _) hdl)
            (Nat.add_le_add (Nat.le_refl _) hpl))))
  · unfold cliRun1MiBCustomPksmPeak
    have hr2p :
        CliRunArmsPeak.r2DeltaPeak fineCostModel Senc.live Senc.peak sessionCapBytes ≤
          CliRunArmsPeak.r2DeltaPeak fineCostModel encLive encPeak sessionCapBytes := by
      unfold CliRunArmsPeak.r2DeltaPeak
      exact d3z_max_mono hep (Nat.add_le_add hel (Nat.le_refl _))
    exact d3z_max_mono (Nat.le_refl _)
      (Nat.add_le_add (Nat.le_refl _)
        (d3z_max_mono (Nat.le_refl _)
          (d3z_max_mono hr2p
            (d3z_max_mono (d3z_max_mono (Nat.le_refl _) (Nat.add_le_add (Nat.le_refl _) hdp))
              (d3z_max_mono (Nat.le_refl _) (Nat.add_le_add (Nat.le_refl _) hpp))))))
  · unfold cliRunBinary1MiBCustomPksmMaxReq
    have hr2r :
        CliRunArmsPeak.r2MaxReq Senc.maxReq sessionCapBytes ≤
          CliRunArmsPeak.r2MaxReq encMaxReq sessionCapBytes := by
      unfold CliRunArmsPeak.r2MaxReq
      exact d3z_max_mono her (Nat.le_refl _)
    exact d3z_max_mono (Nat.le_refl _)
      (d3z_max_mono (Nat.le_refl _)
        (d3z_max_mono hr2r
          (d3z_max_mono (d3z_max_mono (Nat.le_refl _) hdr)
            (d3z_max_mono (Nat.le_refl _) hpr))))
  · unfold cliRunOpenedCustomPksmGrpS
    exact Nat.add_le_add (Nat.le_refl _)
      (d3z_max_mono (Nat.le_refl _)
        (d3z_max_mono (Nat.add_le_add heg (Nat.le_refl _))
          (d3z_max_mono (Nat.add_le_add (Nat.le_refl _) hdg)
            (Nat.add_le_add (Nat.le_refl _) hpg))))

/-- Cap-parametric whole-`main` `FitsEnv fineCostModel` on `CliPqOrD3RecvInputs ⟨W.C, W.Q⟩` for `mkD3BinaryKitCalleeEnvsSlotOf`. -/
theorem realCliMainD3RecvSlot_fitsEnv_of_caps [LibsignalPlacement]
    {lim : BudgetLimits}
    (henf : lim.enforced = true)
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes)
    (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap1G : cliOneGiB ≤ lim.physCap)
    (EncSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → EncGhost → List AllocEvent → Prop)
    (DecSigSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → DecSigGhost → List AllocEvent → Prop)
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (decPkEnv : RunCall → List AllocEvent → Prop)
    {encCum encLive encPeak encMaxReq encGrpS
     decSigCum decSigLive decSigPeak decSigMaxReq decSigGrpS
     decPkCum decPkLive decPkPeak decPkMaxReq decPkGrpS : Nat}
    (S_enc : ∀ (g : RunCall),
      CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i →
      g.i.stdin.length ≤ msgCapBytes →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      SingleSlotFineSpec
        ((mkD3BinaryKitCalleeEnvsSlotOf EncSlot DecSigSlot img S X W decPkEnv g).encEnv))
    (S_decSig : ∀ (g : RunCall),
      CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i →
      g.i.stdin.length ≤ msgCapBytes →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      SingleSlotFineSpec
        ((mkD3BinaryKitCalleeEnvsSlotOf EncSlot DecSigSlot img S X W decPkEnv g).decSigEnv))
    (S_decPk : ∀ (g : RunCall),
      CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i →
      g.i.stdin.length ≤ msgCapBytes →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      SingleSlotFineSpec (decPkEnv g))
    (hEncCaps : ∀ (g : RunCall)
      (hi_g : CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i)
      (hstdin : g.i.stdin.length ≤ msgCapBytes)
      (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c),
      let se := S_enc g hi_g hstdin hparse
      se.cum ≤ encCum ∧ se.live ≤ encLive ∧ se.peak ≤ encPeak ∧
      se.maxReq ≤ encMaxReq ∧ se.grpS ≤ encGrpS)
    (hDecSigCaps : ∀ (g : RunCall)
      (hi_g : CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i)
      (hstdin : g.i.stdin.length ≤ msgCapBytes)
      (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c),
      let sd := S_decSig g hi_g hstdin hparse
      sd.cum ≤ decSigCum ∧ sd.live ≤ decSigLive ∧ sd.peak ≤ decSigPeak ∧
      sd.maxReq ≤ decSigMaxReq ∧ sd.grpS ≤ decSigGrpS)
    (hDecPkCaps : ∀ (g : RunCall)
      (hi_g : CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i)
      (hstdin : g.i.stdin.length ≤ msgCapBytes)
      (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c),
      let sp := S_decPk g hi_g hstdin hparse
      sp.cum ≤ decPkCum ∧ sp.live ≤ decPkLive ∧ sp.peak ≤ decPkPeak ∧
      sp.maxReq ≤ decPkMaxReq ∧ sp.grpS ≤ decPkGrpS)
    (hFits : d3SlotMainFitsOneGiBOf
      encCum encLive encPeak encMaxReq encGrpS
      decSigCum decSigLive decSigPeak decSigMaxReq decSigGrpS
      decPkCum decPkLive decPkPeak decPkMaxReq decPkGrpS) :
    ∀ i : Inputs, CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ i →
      FitsEnv fineCostModel lim fineCostModel.init
        (RealCliMainBinaryEnvOf
          (mkD3BinaryKitCalleeEnvsSlotOf EncSlot DecSigSlot img S X W decPkEnv) i) := by
  obtain ⟨h15_grp, hinit_grp, hram0, hva0⟩ := hFits
  let rCum := cliRunBinary1MiBCustomPksmCum
    (pksmSliceCum msgCapBytes) w3InitExactCum encCum decSigCum decPkCum
  let rLive := cliRun1MiBCustomPksmLive
    (pksmSliceLive msgCapBytes) w3InitExactLive encLive decSigLive decPkLive
  let rPeak := cliRun1MiBCustomPksmPeak
    (pksmSliceLive msgCapBytes) (pksmSlicePeak msgCapBytes)
    w3InitExactPeak encLive encPeak decSigPeak decPkPeak
  let rReq := cliRunBinary1MiBCustomPksmMaxReq
    (pksmSliceMaxReq msgCapBytes) w3InitExactMaxReq encMaxReq decSigMaxReq decPkMaxReq
  let rGrpS := cliRunOpenedCustomPksmGrpS msgCapBytes
    (pksmTryFromCapDeltaGrpS msgCapBytes) w3InitExactGrpS encGrpS decSigGrpS decPkGrpS
  have hram :
      cliDecoupledRamNeed lim.staticBytes
        (d3SlotMainCumOf encCum decSigCum decPkCum)
        (d3SlotMainPeakGenOf encLive encPeak decSigLive decSigPeak decPkLive decPkPeak)
        (d3SlotMainReqOf encMaxReq decSigMaxReq decPkMaxReq)
        ((d3SlotMainGrpSOf encGrpS decSigGrpS decPkGrpS + FineScale - 1) / FineScale) ≤
        lim.physCap :=
    Nat.le_trans
      (cliDecoupledRamNeed_mono hsb
        (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
      (Nat.le_trans hram0 hcap1G)
  have hva :
      cliDecoupledVaNeed lim.staticBytes lim.staticCount
        (d3SlotMainCumOf encCum decSigCum decPkCum)
        (d3SlotMainPeakGenOf encLive encPeak decSigLive decSigPeak decPkLive decPkPeak)
        (d3SlotMainReqOf encMaxReq decSigMaxReq decPkMaxReq)
        ((d3SlotMainGrpSOf encGrpS decSigGrpS decPkGrpS + FineScale - 1) / FineScale) ≤ 2 ^ 48 :=
    Nat.le_trans
      (cliDecoupledVaNeed_mono hsb hsc
        (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
      hva0
  intro i hi
  have hsm1024 : 1024 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have hw (w : ValidPostSetupWitness i) : PhaseCreditSpec fineCostModel
      (SeqEnv
        (CliRunBinaryEnv cliIo.rd
          (mkD3BinaryKitCalleeEnvsSlotOf EncSlot DecSigSlot img S X W decPkEnv w.g)
          sessionCapBytes w.g)
        (SeqEnv (M5PhaseEnv w.dirs) (M6Env w.ok)))
      (rCum + cliMaxDirtyEntries *
        (10 * max (4 * cliMaxDirPathBytes + cliMaxAddrTextBytes + 16) 16 + 4 * 9539) + m6DeltaCum)
      rLive
      (max rPeak (rLive + m5DirStepDeltaPeak cliMaxDirPathBytes cliMaxAddrTextBytes))
      (max rReq (max 1024 (m5DirStepMaxReq cliMaxDirPathBytes cliMaxAddrTextBytes))) := by
    have hi_g : CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ w.g.i := w.g_i.symm ▸ hi
    let Senc := S_enc w.g hi_g w.stdin_le w.parse_ok
    let Sds := S_decSig w.g hi_g w.stdin_le w.parse_ok
    let Spk := S_decPk w.g hi_g w.stdin_le w.parse_ok
    let SE := d3z_d3SlotCalleeFineSpecs EncSlot DecSigSlot img S X W Senc Sds Spk hi_g w.parse_ok
    obtain ⟨h1_cum, h2, h3, h1_req, _⟩ :=
      d3z_d3SlotCalleeFineSpecs_bounds EncSlot DecSigSlot img S X W Senc Sds Spk
        (hEncCaps w.g hi_g w.stdin_le w.parse_ok)
        (hDecSigCaps w.g hi_g w.stdin_le w.parse_ok)
        (hDecPkCaps w.g hi_g w.stdin_le w.parse_ok)
        hi_g w.parse_ok
    have hrun :=
      (cliRunBinaryEnv_real_1MiB_fine_phaseCredit_of_pqOrD3Recv SE hi_g w.stdin_le
        w.parse_ok).mono h1_cum h2 h3 h1_req
    refine (hrun.seq ((m5Phase_Bounded_phaseCredit_fine w.dirs_sum_le w.dirs_bounds).seq
      (m6_phaseCredit_small1024 fineCostModel_modelHyps hsm1024 w.ok))).mono ?_ ?_ ?_ ?_
    · rw [Nat.add_assoc]; exact Nat.le_refl _
    · simp only [Nat.add_zero]; exact Nat.le_refl _
    · exact d3z_max_mono (Nat.le_refl _)
        (Nat.add_le_add_left (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.zero_le _⟩) _)
    · exact d3z_max_mono (Nat.le_refl _) (Nat.le_of_eq (Nat.max_comm _ _))
  have hex : PhaseCreditSpec fineCostModel
      (fun evs' => ∃ w : ValidPostSetupWitness i, w.g.i = i ∧
        SeqEnv
          (CliRunBinaryEnv cliIo.rd
            (mkD3BinaryKitCalleeEnvsSlotOf EncSlot DecSigSlot img S X W decPkEnv w.g)
            sessionCapBytes w.g)
          (SeqEnv (M5PhaseEnv w.dirs) (M6Env w.ok)) evs')
      (rCum + cliMaxDirtyEntries *
        (10 * max (4 * cliMaxDirPathBytes + cliMaxAddrTextBytes + 16) 16 + 4 * 9539) + m6DeltaCum)
      rLive
      (max rPeak (rLive + m5DirStepDeltaPeak cliMaxDirPathBytes cliMaxAddrTextBytes))
      (max rReq (max 1024 (m5DirStepMaxReq cliMaxDirPathBytes cliMaxAddrTextBytes))) :=
    { req_align := fun evs ⟨w, _, hseq⟩ ev hev => (hw w).req_align evs hseq ev hev
      credit_le := fun st0 {_} ⟨w, _, hseq⟩ => (hw w).credit_le st0 hseq }
  have hcr : PhaseCreditSpec fineCostModel
      (RealCliMainBinaryEnvOf
        (mkD3BinaryKitCalleeEnvsSlotOf EncSlot DecSigSlot img S X W decPkEnv) i)
      (d3SlotMainCumOf encCum decSigCum decPkCum)
      (d3SlotMainLiveOf encLive decSigLive decPkLive)
      (d3SlotMainPeakGenOf encLive encPeak decSigLive decSigPeak decPkLive decPkPeak)
      (d3SlotMainReqOf encMaxReq decSigMaxReq decPkMaxReq) := by
    refine ((cliMainBoundedSetup_phaseCredit_fine
        (argv_length_le_3_of_pqOrD3Recv hi)).seq
      (d3z_optStage_phaseCredit hex)).mono ?_ ?_ ?_ ?_
    · unfold d3SlotMainCumOf
      dsimp only [rCum]
      simp only [Nat.add_assoc]
      exact Nat.le_refl _
    · unfold d3SlotMainLiveOf cliMainTightLiveOf cliMainDeltaLive_tight
      exact Nat.le_refl _
    · unfold d3SlotMainPeakGenOf cliMainTightPeakOf cliMainDeltaPeak_tight
      exact Nat.le_refl _
    · unfold d3SlotMainReqOf cliMainTightReqOf cliMainMaxReq
      have h16k : max 16384 (m3PhaseMaxReq msgCapBytes sessionCapBytes) =
          m3PhaseMaxReq msgCapBytes sessionCapBytes := by
        unfold m3PhaseMaxReq msgCapBytes sessionCapBytes; decide
      rw [h16k]
      exact Nat.le_max_right _ _
  have hex_grp : PhaseGroupSpec fineCostModel
      (fun evs' => ∃ w : ValidPostSetupWitness i, w.g.i = i ∧
        SeqEnv
          (CliRunBinaryEnv cliIo.rd
            (mkD3BinaryKitCalleeEnvsSlotOf EncSlot DecSigSlot img S X W decPkEnv w.g)
            sessionCapBytes w.g)
          (SeqEnv (M5PhaseEnv w.dirs) (M6Env w.ok)) evs')
      ((rGrpS + 27 * FineScale) + cliMaxDirtyEntries * (12 * FineScale) + 3 * FineScale) :=
    { groups_le := fun st0 {_} ⟨w, _, hseq⟩ => by
        have hi_g : CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ w.g.i := w.g_i.symm ▸ hi
        let Senc := S_enc w.g hi_g w.stdin_le w.parse_ok
        let Sds := S_decSig w.g hi_g w.stdin_le w.parse_ok
        let Spk := S_decPk w.g hi_g w.stdin_le w.parse_ok
        let SE := d3z_d3SlotCalleeFineSpecs EncSlot DecSigSlot img S X W Senc Sds Spk hi_g
          w.parse_ok
        obtain ⟨_, _, _, _, h5⟩ :=
          d3z_d3SlotCalleeFineSpecs_bounds EncSlot DecSigSlot img S X W Senc Sds Spk
            (hEncCaps w.g hi_g w.stdin_le w.parse_ok)
            (hDecSigCaps w.g hi_g w.stdin_le w.parse_ok)
            (hDecPkCaps w.g hi_g w.stdin_le w.parse_ok)
            hi_g w.parse_ok
        have hrun := cliRunBinaryEnv_fine_groupSpec_of_cap SE w.stdin_le h15_grp hinit_grp h5
        have hm5 := (m5PhaseEnv_groupSpec fineCostModel w.dirs).mono
          (Nat.mul_le_mul_right (12 * FineScale) w.dirs_sum_le)
        have htot : PhaseGroupSpec fineCostModel
            (SeqEnv
              (CliRunBinaryEnv cliIo.rd
                (mkD3BinaryKitCalleeEnvsSlotOf EncSlot DecSigSlot img S X W decPkEnv w.g)
                sessionCapBytes w.g)
              (SeqEnv (M5PhaseEnv w.dirs) (M6Env w.ok)))
            ((rGrpS + 27 * FineScale) + cliMaxDirtyEntries * (12 * FineScale) + 3 * FineScale) :=
          (hrun.seq (hm5.seq (m6Env_groupSpec fineCostModel w.ok))).mono
            (by generalize FineScale = fs; omega)
        exact htot.groups_le st0 hseq }
  have hgrp : PhaseGroupSpec fineCostModel
      (RealCliMainBinaryEnvOf
        (mkD3BinaryKitCalleeEnvsSlotOf EncSlot DecSigSlot img S X W decPkEnv) i)
      (d3SlotMainGrpSOf encGrpS decSigGrpS decPkGrpS) :=
    ((cliMainBoundedSetup_fine_groupSpec
        (argv_length_le_3_of_pqOrD3Recv hi)).seq
      (d3z_optStage_groupSpec hex_grp)).mono
      (by unfold d3SlotMainGrpSOf
          dsimp only [rGrpS]
          generalize FineScale = fs; omega)
  have hlp :
      d3SlotMainLiveOf encLive decSigLive decPkLive ≤
      d3SlotMainPeakGenOf encLive encPeak decSigLive decSigPeak decPkLive decPkPeak := by
    unfold d3SlotMainLiveOf d3SlotMainPeakGenOf
      cliMainTightLiveOf cliMainTightPeakOf cliMainDeltaLive_tight cliMainDeltaPeak_tight
    exact Nat.le_trans
      (Nat.add_le_add_left (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_max_right _ _)) _)
      (Nat.le_max_right _ _)
  exact fitsEnv_fineCostModel_of_group_literal_bounds hcr hgrp
    (Nat.le_refl _) hlp (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) henf hram hva

/-! ## 3. End-to-End `pqD3ScopedRun` `MainEntryBudgetFitsCapOf` -/

private def d3z_decPkEnvOf
    (S : RunSem) (DecPkSlotEnv : DecPkGhost → List AllocEvent → Prop)
    (W : CliHooks) (g : RunCall) : List AllocEvent → Prop :=
  match g.c with
  | .recv peerV => fun evs =>
    ∃ (meV : AddrV) (rest : List (BitVec 8)) (pm : PreKeySignalMessage),
      CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i ∧
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) ∧
      (inputOf g.i (.recv peerV)).length ≤ stdinCapBytes ∧
      g.i.stdin = 3#8 :: rest ∧
      S.pksmParse rest = some pm ∧
      DecPkSlotEnv (r3bDecPkGhost g meV peerV pm) evs
  | _ => fun _ => False

private theorem d3z_w2BinaryWhisperDom_of_same_runFiles {c : CallV} {i i₀ : Inputs}
    {R : W2BinaryWhisperParams} (hfiles : runFiles i₀ = runFiles i)
    (h : W2BinaryWhisperDom c i R) :
    W2BinaryWhisperDom c i₀ R := by
  intro peerAddr hc
  obtain ⟨h1, h2, h3, h4, h5⟩ := h peerAddr hc
  exact ⟨h1, h2, h3, h4, h5.trans hfiles.symm⟩

private theorem d3z_w2_decSigSlot_sub_d3SlotOf [LibsignalPlacement] {M : AllocCostModel}
    (EncSlot : ∀ {M' : AllocCostModel},
      RustCliAllocBudget M' → RunBudgets → EncGhost → List AllocEvent → Prop)
    (DecSigSlot : ∀ {M' : AllocCostModel},
      RustCliAllocBudget M' → RunBudgets → DecSigGhost → List AllocEvent → Prop)
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (decPkEnv : RunCall → List AllocEvent → Prop)
    (A : RustCliAllocBudget M) (B : RunBudgets)
    (g : RunCall) (meG : AddrGhost) (peerV : AddrV) (rest : List (BitVec 8)) (m : SignalMessage)
    (hin : (inputOf g.i g.c).length ≤ stdinCapBytes)
    (hc : g.c = .recv peerV)
    (hst : g.i.stdin = 2#8 :: rest)
    (htr : SignalMessage.tryFrom protoSignalCodec rest = .ok m)
    {evs : List AllocEvent}
    (hevs : DecSigSlot A B (r3aDecSigGhost0 g peerV meG m) evs) :
    (mkD3BinaryKitCalleeEnvsSlotOf EncSlot DecSigSlot img S X W decPkEnv g).decSigEnv evs := by
  let x := r3aDecSigGhost0 g peerV meG m
  let w2R : W2BinaryWhisperParams := ⟨A.repAlloc, B, x.peer, x⟩
  have hct_rest : m.ciphertext.length ≤ rest.length :=
    (signalMessage_tryFrom_lengths_le htr).2.1
  have hrest_cap : rest.length ≤ msgCapBytes :=
    recv_rest_length_le_msgCapBytes hin hc hst
  have hct_cap : m.ciphertext.length ≤ msgCapBytes :=
    Nat.le_trans hct_rest hrest_cap
  have hdom : W2BinaryWhisperDom g.c g.i w2R := by
    intro pAddr hpAddr
    rw [hc] at hpAddr
    injection hpAddr with hpEq
    subst hpEq
    exact ⟨rfl, rfl, rfl, hct_cap, rfl⟩
  dsimp only [mkD3BinaryKitCalleeEnvsSlotOf, mkBinaryKitRealCalleeEnvsSlotOf]
  rw [hc]
  exact ⟨M, A, w2R, rfl, hc ▸ hdom, hevs⟩

/-- Cap-parametric `MainEntryBudgetFitsCapOf` at `cliBudgetLimits` (`1 GiB`) for `pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel S)` under `d3SlotMainFitsOneGiBOf`. -/
theorem mainEntryBudgetFitsCapOf_pqD3Recv_slot_of_caps [LibsignalPlacement]
    {M : AllocCostModel}
    (EncSlot : ∀ {M' : AllocCostModel},
      RustCliAllocBudget M' → RunBudgets → EncGhost → List AllocEvent → Prop)
    (DecSigSlot : ∀ {M' : AllocCostModel},
      RustCliAllocBudget M' → RunBudgets → DecSigGhost → List AllocEvent → Prop)
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (A : RustCliAllocBudget M) (B : RunBudgets)
    (DecPkSlotEnv : DecPkGhost → List AllocEvent → Prop)
    (encCum encLive encPeak encMaxReq encGrpS
     decSigCum decSigLive decSigPeak decSigMaxReq decSigGrpS
     w4Cum w4Live w4Peak w4MaxReq w4GrpS : Nat)
    (hNwDom : ∀ (i : Inputs) (nw : List (String × List (BitVec 8))) (out : List (BitVec 8)),
      CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ i →
      runAns S i = some (some (nw, out)) →
      nw.length ≤ 4 ∧ ∀ pw ∈ nw, pw.1.length ≤ 64)
    (hEncCredit : ∀ (g : RunCall) (peerV : AddrV) (M' : AllocCostModel)
      (A' : RustCliAllocBudget M') (w1R : W1BinarySendParams),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.send peerV) →
      g.c = .send peerV →
      w1R.repAlloc = A'.repAlloc →
      W1BinarySendDom (.send peerV) g.i w1R →
      PhaseCreditSpec fineCostModel (EncSlot A' w1R.B w1R.x)
        encCum encLive encPeak encMaxReq)
    (hEncLp : encLive ≤ encPeak)
    (hEncGrp : ∀ (g : RunCall) (peerV : AddrV) (M' : AllocCostModel)
      (A' : RustCliAllocBudget M') (w1R : W1BinarySendParams),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.send peerV) →
      g.c = .send peerV →
      w1R.repAlloc = A'.repAlloc →
      W1BinarySendDom (.send peerV) g.i w1R →
      PhaseGroupSpec fineCostModel (EncSlot A' w1R.B w1R.x) encGrpS)
    (hDecSigCredit : ∀ (g : RunCall) (peerV : AddrV) (M' : AllocCostModel)
      (A' : RustCliAllocBudget M') (w2R : W2BinaryWhisperParams),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
      g.c = .recv peerV →
      w2R.repAlloc = A'.repAlloc →
      W2BinaryWhisperDom (.recv peerV) g.i w2R →
      PhaseCreditSpec fineCostModel (DecSigSlot A' w2R.B w2R.x)
        decSigCum decSigLive decSigPeak decSigMaxReq)
    (hDecSigLp : decSigLive ≤ decSigPeak)
    (hDecSigGrp : ∀ (g : RunCall) (peerV : AddrV) (M' : AllocCostModel)
      (A' : RustCliAllocBudget M') (w2R : W2BinaryWhisperParams),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
      g.c = .recv peerV →
      w2R.repAlloc = A'.repAlloc →
      W2BinaryWhisperDom (.recv peerV) g.i w2R →
      PhaseGroupSpec fineCostModel (DecSigSlot A' w2R.B w2R.x) decSigGrpS)
    (hDecPkCredit : ∀ (g : RunCall) (meV peerV : AddrV)
      (rest : List (BitVec 8)) (pm : PreKeySignalMessage),
      CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
      (inputOf g.i g.c).length ≤ stdinCapBytes →
      g.c = .recv peerV →
      g.i.stdin = 3#8 :: rest →
      S.pksmParse rest = some pm →
      PhaseCreditSpec fineCostModel (DecPkSlotEnv (r3bDecPkGhost g meV peerV pm))
        w4Cum w4Live w4Peak w4MaxReq)
    (hDecPkLp : w4Live ≤ w4Peak)
    (hDecPkGrp : ∀ (g : RunCall) (meV peerV : AddrV)
      (rest : List (BitVec 8)) (pm : PreKeySignalMessage),
      CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
      (inputOf g.i g.c).length ≤ stdinCapBytes →
      g.c = .recv peerV →
      g.i.stdin = 3#8 :: rest →
      S.pksmParse rest = some pm →
      PhaseGroupSpec fineCostModel (DecPkSlotEnv (r3bDecPkGhost g meV peerV pm))
        w4GrpS)
    (hFits : d3SlotMainFitsOneGiBOf
      encCum encLive encPeak encMaxReq encGrpS
      decSigCum decSigLive decSigPeak decSigMaxReq decSigGrpS
      w4Cum w4Live w4Peak w4MaxReq w4GrpS)
    (hS_enc : S.encrypt = encDef ⟨W.C, W.Q⟩ scopeIn := by rfl) :
    MainEntryBudgetFitsCapOf fineCostModel cliBudgetLimits fineCostModel.init cliIo
      (ReadFileRuleEnvFixed cliIo.rd) uuidTryParse
      (RunEnv
        (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          (hmx_binaryKitRunSlotEnvsSlotOf EncSlot DecSigSlot A B
            (realCliInitBinarySlotEnvFixed W) DecPkSlotEnv)
          PksmTryFromEnv S))
      (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel S)) := by
  let decPkEnv := d3z_decPkEnvOf S DecPkSlotEnv W
  let E := mkD3BinaryKitCalleeEnvsSlotOf EncSlot DecSigSlot img S X W decPkEnv
  let S_enc (g : RunCall)
      (hi_g : CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i)
      (_hstdin : g.i.stdin.length ≤ msgCapBytes)
      (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c) :
      SingleSlotFineSpec ((E g).encEnv) :=
    { cum := encCum
      live := encLive
      peak := encPeak
      maxReq := encMaxReq
      grpS := encGrpS
      credit := by
        dsimp only [E, mkD3BinaryKitCalleeEnvsSlotOf, mkBinaryKitRealCalleeEnvsSlotOf]
        cases hgc : g.c with
        | keygen _ _ | init _ _ | recv _ =>
          exact (PhaseCreditSpec.nil fineCostModel).of_imp (fun _ h => False.elim h)
            |>.mono (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
        | send peerV =>
          have hi_pq : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i :=
            d3z_non_recv_is_cliPqxdhInputs hi_g hparse
              (fun _ hc => by rw [hgc] at hc; cases hc)
          have hp : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.send peerV) :=
            hgc ▸ hparse
          exact
            { req_align := fun evs ⟨M', A', w1R, hrep, hdom, he⟩ =>
                (hEncCredit g peerV M' A' w1R hi_pq hp hgc hrep hdom).req_align evs he
              credit_le := fun st0 {_} ⟨M', A', w1R, hrep, hdom, he⟩ =>
                (hEncCredit g peerV M' A' w1R hi_pq hp hgc hrep hdom).credit_le st0 he }
      live_le_peak := hEncLp
      groups := by
        dsimp only [E, mkD3BinaryKitCalleeEnvsSlotOf, mkBinaryKitRealCalleeEnvsSlotOf]
        cases hgc : g.c with
        | keygen _ _ | init _ _ | recv _ =>
          exact (PhaseGroupSpec.nil fineCostModel).of_imp (fun _ h => False.elim h)
            |>.mono (Nat.zero_le _)
        | send peerV =>
          have hi_pq : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i :=
            d3z_non_recv_is_cliPqxdhInputs hi_g hparse
              (fun _ hc => by rw [hgc] at hc; cases hc)
          have hp : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.send peerV) :=
            hgc ▸ hparse
          exact
            { groups_le := fun st0 {_} ⟨M', A', w1R, hrep, hdom, he⟩ =>
                (hEncGrp g peerV M' A' w1R hi_pq hp hgc hrep hdom).groups_le st0 he } }
  let S_decSig (g : RunCall)
      (hi_g : CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i)
      (_hstdin : g.i.stdin.length ≤ msgCapBytes)
      (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c) :
      SingleSlotFineSpec ((E g).decSigEnv) :=
    { cum := decSigCum
      live := decSigLive
      peak := decSigPeak
      maxReq := decSigMaxReq
      grpS := decSigGrpS
      credit := by
        dsimp only [E, mkD3BinaryKitCalleeEnvsSlotOf, mkBinaryKitRealCalleeEnvsSlotOf]
        cases hgc : g.c with
        | keygen _ _ | init _ _ | send _ =>
          exact (PhaseCreditSpec.nil fineCostModel).of_imp (fun _ h => False.elim h)
            |>.mono (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
        | recv peerV =>
          obtain ⟨g₀, hi₀, hgc₀, hargv₀, hfiles₀⟩ :=
            d3z_exists_cliPqxdhInputs_same_argv_runFiles hi_g
          have hp₀ : parseArgs uuidTryParse (g₀.i.argv.map bytesOfString) = some (.recv peerV) := by
            rw [hargv₀]; exact hgc ▸ hparse
          have hc₀ : g₀.c = .recv peerV := hgc₀.trans hgc
          exact
            { req_align := fun evs ⟨M', A', w2R, hrep, hdom, he⟩ =>
                (hDecSigCredit g₀ peerV M' A' w2R hi₀ hp₀ hc₀ hrep
                  (d3z_w2BinaryWhisperDom_of_same_runFiles hfiles₀ hdom)).req_align evs he
              credit_le := fun st0 {_} ⟨M', A', w2R, hrep, hdom, he⟩ =>
                (hDecSigCredit g₀ peerV M' A' w2R hi₀ hp₀ hc₀ hrep
                  (d3z_w2BinaryWhisperDom_of_same_runFiles hfiles₀ hdom)).credit_le st0 he }
      live_le_peak := hDecSigLp
      groups := by
        dsimp only [E, mkD3BinaryKitCalleeEnvsSlotOf, mkBinaryKitRealCalleeEnvsSlotOf]
        cases hgc : g.c with
        | keygen _ _ | init _ _ | send _ =>
          exact (PhaseGroupSpec.nil fineCostModel).of_imp (fun _ h => False.elim h)
            |>.mono (Nat.zero_le _)
        | recv peerV =>
          obtain ⟨g₀, hi₀, hgc₀, hargv₀, hfiles₀⟩ :=
            d3z_exists_cliPqxdhInputs_same_argv_runFiles hi_g
          have hp₀ : parseArgs uuidTryParse (g₀.i.argv.map bytesOfString) = some (.recv peerV) := by
            rw [hargv₀]; exact hgc ▸ hparse
          have hc₀ : g₀.c = .recv peerV := hgc₀.trans hgc
          exact
            { groups_le := fun st0 {_} ⟨M', A', w2R, hrep, hdom, he⟩ =>
                (hDecSigGrp g₀ peerV M' A' w2R hi₀ hp₀ hc₀ hrep
                  (d3z_w2BinaryWhisperDom_of_same_runFiles hfiles₀ hdom)).groups_le st0 he } }
  let S_decPk (g : RunCall)
      (_hi_g : CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i)
      (_hstdin : g.i.stdin.length ≤ msgCapBytes)
      (_hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c) :
      SingleSlotFineSpec (decPkEnv g) :=
    { cum := w4Cum
      live := w4Live
      peak := w4Peak
      maxReq := w4MaxReq
      grpS := w4GrpS
      credit := by
        dsimp only [decPkEnv, d3z_decPkEnvOf]
        cases hgc : g.c with
        | keygen _ _ | init _ _ | send _ =>
          exact (PhaseCreditSpec.nil fineCostModel).of_imp (fun _ h => False.elim h)
            |>.mono (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
        | recv peerV =>
          exact
            { req_align := fun evs ⟨meV, rest, pm, hi', hp', hin', hst, hpk, hd⟩ =>
                (hDecPkCredit g meV peerV rest pm hi' hp' (hgc.symm ▸ hin') hgc hst hpk).req_align
                  evs hd
              credit_le := fun st0 {_} ⟨meV, rest, pm, hi', hp', hin', hst, hpk, hd⟩ =>
                (hDecPkCredit g meV peerV rest pm hi' hp' (hgc.symm ▸ hin') hgc hst hpk).credit_le
                  st0 hd }
      live_le_peak := hDecPkLp
      groups := by
        dsimp only [decPkEnv, d3z_decPkEnvOf]
        cases hgc : g.c with
        | keygen _ _ | init _ _ | send _ =>
          exact (PhaseGroupSpec.nil fineCostModel).of_imp (fun _ h => False.elim h)
            |>.mono (Nat.zero_le _)
        | recv peerV =>
          exact
            { groups_le := fun st0 {_} ⟨meV, rest, pm, hi', hp', hin', hst, hpk, hd⟩ =>
                (hDecPkGrp g meV peerV rest pm hi' hp' (hgc.symm ▸ hin') hgc hst hpk).groups_le
                  st0 hd } }
  have hMain := realCliMainD3RecvSlot_fitsEnv_of_caps (lim := cliBudgetLimits)
    rfl (Nat.le_refl _) (Nat.le_refl _) (by unfold cliBudgetLimits cliOneGiB; decide)
    EncSlot DecSigSlot img S X W decPkEnv S_enc S_decSig S_decPk
    (fun _ _ _ _ => ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩)
    (fun _ _ _ _ => ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩)
    (fun _ _ _ _ => ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩)
    hFits
  exact mainEntryBudgetFitsCapOf_domScopedRun_cliBudgetLimits_of_kitEnvFits
    boundedReadFileEnv_of_readFileRuleEnvFixed_cliIo
    hMain
    (fun i c hi hp hin => by
      rcases hi with hi_pq | ⟨st, ct, rc, _, rfl⟩
      · exact stdin_le_msgCapBytes_of_pqInputs_and_inputOf hi_pq hp hin
      · exact stdin_le_msgCapBytes_of_pqRecvInputs_and_inputOf hp hin)
    hNwDom
    (fun g hi hparse hin _hrel evs hrun => by
      cases hcmd : g.c with
      | keygen _ _ | init _ _ | send _ =>
        have hi_pq : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i :=
          d3z_non_recv_is_cliPqxdhInputs hi hparse
            (fun _ hc => by rw [hcmd] at hc; cases hc)
        have hkit := hmx_runEnvSlotOf_sub_runBinaryKitEnvOfSlot_of_slots
          EncSlot DecSigSlot img S X W A B hi_pq hin
          (fun peerV dir d2 _ hc _ hpv hpval _ _ _ ⟨w, hx, hF, hspqr, hgv, halice, hslotF⟩ =>
            w3_realCliInitBinarySlotEnv_sub_binaryKit img S X W g peerV dir d2
              hparse hc hpv hpval
              ⟨w, hx, hF, hspqr, hgv, halice,
                Eq.mp (congrFun (w3InitBinaryKitSlotEnvFixed_eq_plain hi_pq (congrArg (·.F) hx)) _)
                  hslotF⟩)
          (fun _ _ _ hc => by rw [hcmd] at hc; cases hc)
          (fun _ _ _ _ _ _ hc => by rw [hcmd] at hc; cases hc)
          hS_enc evs hrun
        unfold realCliRunBinaryKitEnvOfSlot at hkit
        unfold CliRunBinaryEnv at hkit ⊢
        rcases hkit with hf | hr0
        · exact Or.inl hf
        · right
          refine d3z_seqEnv_mono (fun _ h => h)
            (fun _ hseq => d3z_seqEnv_mono (fun _ harm => ?_) (fun _ hj => hj) hseq) hr0
          unfold RunArmBinaryEnv at harm ⊢
          dsimp only [E, mkD3BinaryKitCalleeEnvsSlotOf]
          simp only [hcmd] at harm ⊢
          exact harm
      | recv peerV₀ =>
        obtain ⟨g₀, hi₀, _, _, hfiles₀⟩ := d3z_exists_cliPqxdhInputs_same_argv_runFiles hi
        have hpeq : PreEnv (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd)) g =
            PreEnv (cliRunCalleesEnvs (ReadFileRuleEnv cliIo.rd)) g := by
          funext e
          unfold PreEnv cliRunCalleesEnvs
          dsimp only
          rw [← hfiles₀, dirGetEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_own_address hi₀)]
        exact runEnv_to_cliRunBinaryEnv_of_slots (E := E g)
          (fun _ hp =>
            preEnv_sub_r0BinaryEnv (cEnvs := cliRunCalleesEnvs (ReadFileRuleEnv cliIo.rd)) rfl g
              (Eq.mp (congrFun hpeq _) hp))
          (fun _ _ _ _ hc => by rw [hcmd] at hc; cases hc)
          (fun _ _ _ _ hc => by rw [hcmd] at hc; cases hc)
          (fun _ _ _ _ hc => by rw [hcmd] at hc; cases hc)
          (fun _ _ _ hc => by rw [hcmd] at hc; cases hc)
          (fun _ peerV rest _ hc hst hrw =>
            r3aRecvWEnv_sub_r3aBinaryEnv
              (fun _ meG m _e _hme htr hd =>
                d3z_w2_decSigSlot_sub_d3SlotOf EncSlot DecSigSlot img S X W decPkEnv A B
                  g meG peerV rest m hin hc hst htr hd)
              hrw)
          (fun _ peerV rest _ hc hst hrp =>
            r3bRecvPEnv_sub_r3bEnv
              (fun _ hpk => hpk)
              (fun meV _meG pm _e _hme hp hd => by
                dsimp only [E, mkD3BinaryKitCalleeEnvsSlotOf, decPkEnv, d3z_decPkEnvOf]
                rw [hc]
                exact ⟨meV, rest, pm, hi, hc ▸ hparse, hc ▸ hin, hst, hp, hd⟩)
              hrp)
          evs hrun)

/-- `MainEntryBudgetFitsCapOf` at `cliBudgetLimits` (`1 GiB`) for `pqD3ScopedRun` at `w1EncExact*`, `w2DecSigExact*`, and any `(w4Cum, w4Live, w4Peak, w4MaxReq, w4GrpS)` satisfying `d3SlotMainFitsOneGiBOf`. -/
theorem mainEntryBudgetFitsCapOf_pqD3Recv_dom0 [LibsignalPlacement]
    {M : AllocCostModel}
    (EncSlot : ∀ {M' : AllocCostModel},
      RustCliAllocBudget M' → RunBudgets → EncGhost → List AllocEvent → Prop)
    (DecSigSlot : ∀ {M' : AllocCostModel},
      RustCliAllocBudget M' → RunBudgets → DecSigGhost → List AllocEvent → Prop)
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (A : RustCliAllocBudget M) (B : RunBudgets)
    (DecPkSlotEnv : DecPkGhost → List AllocEvent → Prop)
    (w4Cum w4Live w4Peak w4MaxReq w4GrpS : Nat)
    (hNwDom : ∀ (i : Inputs) (nw : List (String × List (BitVec 8))) (out : List (BitVec 8)),
      CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ i →
      runAns S i = some (some (nw, out)) →
      nw.length ≤ 4 ∧ ∀ pw ∈ nw, pw.1.length ≤ 64)
    (hEncCredit : ∀ (g : RunCall) (peerV : AddrV) (M' : AllocCostModel)
      (A' : RustCliAllocBudget M') (w1R : W1BinarySendParams),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.send peerV) →
      g.c = .send peerV →
      w1R.repAlloc = A'.repAlloc →
      W1BinarySendDom (.send peerV) g.i w1R →
      PhaseCreditSpec fineCostModel (EncSlot A' w1R.B w1R.x)
        w1EncExactCum w1EncExactLive w1EncExactPeak w1EncExactMaxReq)
    (hEncGrp : ∀ (g : RunCall) (peerV : AddrV) (M' : AllocCostModel)
      (A' : RustCliAllocBudget M') (w1R : W1BinarySendParams),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.send peerV) →
      g.c = .send peerV →
      w1R.repAlloc = A'.repAlloc →
      W1BinarySendDom (.send peerV) g.i w1R →
      PhaseGroupSpec fineCostModel (EncSlot A' w1R.B w1R.x) w1EncExactGrpS)
    (hDecSigCredit : ∀ (g : RunCall) (peerV : AddrV) (M' : AllocCostModel)
      (A' : RustCliAllocBudget M') (w2R : W2BinaryWhisperParams),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
      g.c = .recv peerV →
      w2R.repAlloc = A'.repAlloc →
      W2BinaryWhisperDom (.recv peerV) g.i w2R →
      PhaseCreditSpec fineCostModel (DecSigSlot A' w2R.B w2R.x)
        w2DecSigExactCum w2DecSigExactLive w2DecSigExactPeak w2DecSigExactMaxReq)
    (hDecSigGrp : ∀ (g : RunCall) (peerV : AddrV) (M' : AllocCostModel)
      (A' : RustCliAllocBudget M') (w2R : W2BinaryWhisperParams),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
      g.c = .recv peerV →
      w2R.repAlloc = A'.repAlloc →
      W2BinaryWhisperDom (.recv peerV) g.i w2R →
      PhaseGroupSpec fineCostModel (DecSigSlot A' w2R.B w2R.x) w2DecSigExactGrpS)
    (hDecPkCredit : ∀ (g : RunCall) (meV peerV : AddrV)
      (rest : List (BitVec 8)) (pm : PreKeySignalMessage),
      CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
      (inputOf g.i g.c).length ≤ stdinCapBytes →
      g.c = .recv peerV →
      g.i.stdin = 3#8 :: rest →
      S.pksmParse rest = some pm →
      PhaseCreditSpec fineCostModel (DecPkSlotEnv (r3bDecPkGhost g meV peerV pm))
        w4Cum w4Live w4Peak w4MaxReq)
    (hDecPkLp : w4Live ≤ w4Peak)
    (hDecPkGrp : ∀ (g : RunCall) (meV peerV : AddrV)
      (rest : List (BitVec 8)) (pm : PreKeySignalMessage),
      CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
      (inputOf g.i g.c).length ≤ stdinCapBytes →
      g.c = .recv peerV →
      g.i.stdin = 3#8 :: rest →
      S.pksmParse rest = some pm →
      PhaseGroupSpec fineCostModel (DecPkSlotEnv (r3bDecPkGhost g meV peerV pm))
        w4GrpS)
    (hFits : d3SlotMainFitsOneGiBOf
      w1EncExactCum w1EncExactLive w1EncExactPeak w1EncExactMaxReq w1EncExactGrpS
      w2DecSigExactCum w2DecSigExactLive w2DecSigExactPeak w2DecSigExactMaxReq w2DecSigExactGrpS
      w4Cum w4Live w4Peak w4MaxReq w4GrpS)
    (hS_enc : S.encrypt = encDef ⟨W.C, W.Q⟩ scopeIn := by rfl) :
    MainEntryBudgetFitsCapOf fineCostModel cliBudgetLimits fineCostModel.init cliIo
      (ReadFileRuleEnvFixed cliIo.rd) uuidTryParse
      (RunEnv
        (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          (hmx_binaryKitRunSlotEnvsSlotOf EncSlot DecSigSlot A B
            (realCliInitBinarySlotEnvFixed W) DecPkSlotEnv)
          PksmTryFromEnv S))
      (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel S)) :=
  mainEntryBudgetFitsCapOf_pqD3Recv_slot_of_caps
    EncSlot DecSigSlot img S X W A B DecPkSlotEnv
    w1EncExactCum w1EncExactLive w1EncExactPeak w1EncExactMaxReq w1EncExactGrpS
    w2DecSigExactCum w2DecSigExactLive w2DecSigExactPeak w2DecSigExactMaxReq w2DecSigExactGrpS
    w4Cum w4Live w4Peak w4MaxReq w4GrpS
    hNwDom hEncCredit (Nat.le_refl _) hEncGrp
    hDecSigCredit (Nat.le_refl _) hDecSigGrp
    hDecPkCredit hDecPkLp hDecPkGrp hFits hS_enc

/-- `SingleSlotFineSpec` companion to `mainEntryBudgetFitsCapOf_pqD3Recv_dom0`. -/
theorem mainEntryBudgetFitsCapOf_pqD3Recv_dom0_of_singleSlot [LibsignalPlacement]
    {M : AllocCostModel}
    (EncSlot : ∀ {M' : AllocCostModel},
      RustCliAllocBudget M' → RunBudgets → EncGhost → List AllocEvent → Prop)
    (DecSigSlot : ∀ {M' : AllocCostModel},
      RustCliAllocBudget M' → RunBudgets → DecSigGhost → List AllocEvent → Prop)
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (A : RustCliAllocBudget M) (B : RunBudgets)
    (DecPkSlotEnv : DecPkGhost → List AllocEvent → Prop)
    (w4Cum w4Live w4Peak w4MaxReq w4GrpS : Nat)
    (hNwDom : ∀ (i : Inputs) (nw : List (String × List (BitVec 8))) (out : List (BitVec 8)),
      CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ i →
      runAns S i = some (some (nw, out)) →
      nw.length ≤ 4 ∧ ∀ pw ∈ nw, pw.1.length ≤ 64)
    (hEncCredit : ∀ (g : RunCall) (peerV : AddrV) (M' : AllocCostModel)
      (A' : RustCliAllocBudget M') (w1R : W1BinarySendParams),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.send peerV) →
      g.c = .send peerV →
      w1R.repAlloc = A'.repAlloc →
      W1BinarySendDom (.send peerV) g.i w1R →
      PhaseCreditSpec fineCostModel (EncSlot A' w1R.B w1R.x)
        w1EncExactCum w1EncExactLive w1EncExactPeak w1EncExactMaxReq)
    (hEncGrp : ∀ (g : RunCall) (peerV : AddrV) (M' : AllocCostModel)
      (A' : RustCliAllocBudget M') (w1R : W1BinarySendParams),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.send peerV) →
      g.c = .send peerV →
      w1R.repAlloc = A'.repAlloc →
      W1BinarySendDom (.send peerV) g.i w1R →
      PhaseGroupSpec fineCostModel (EncSlot A' w1R.B w1R.x) w1EncExactGrpS)
    (hDecSigCredit : ∀ (g : RunCall) (peerV : AddrV) (M' : AllocCostModel)
      (A' : RustCliAllocBudget M') (w2R : W2BinaryWhisperParams),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
      g.c = .recv peerV →
      w2R.repAlloc = A'.repAlloc →
      W2BinaryWhisperDom (.recv peerV) g.i w2R →
      PhaseCreditSpec fineCostModel (DecSigSlot A' w2R.B w2R.x)
        w2DecSigExactCum w2DecSigExactLive w2DecSigExactPeak w2DecSigExactMaxReq)
    (hDecSigGrp : ∀ (g : RunCall) (peerV : AddrV) (M' : AllocCostModel)
      (A' : RustCliAllocBudget M') (w2R : W2BinaryWhisperParams),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
      g.c = .recv peerV →
      w2R.repAlloc = A'.repAlloc →
      W2BinaryWhisperDom (.recv peerV) g.i w2R →
      PhaseGroupSpec fineCostModel (DecSigSlot A' w2R.B w2R.x) w2DecSigExactGrpS)
    (S_decPk : ∀ (g : RunCall) (meV peerV : AddrV)
      (rest : List (BitVec 8)) (pm : PreKeySignalMessage),
      CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
      (inputOf g.i g.c).length ≤ stdinCapBytes →
      g.c = .recv peerV →
      g.i.stdin = 3#8 :: rest →
      S.pksmParse rest = some pm →
      SingleSlotFineSpec (DecPkSlotEnv (r3bDecPkGhost g meV peerV pm)))
    (hDecPkCaps : ∀ (g : RunCall) (meV peerV : AddrV)
      (rest : List (BitVec 8)) (pm : PreKeySignalMessage)
      (hi_g : CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i)
      (hp : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV))
      (hin : (inputOf g.i g.c).length ≤ stdinCapBytes)
      (hc : g.c = .recv peerV)
      (hst : g.i.stdin = 3#8 :: rest)
      (hpk : S.pksmParse rest = some pm),
      let sp := S_decPk g meV peerV rest pm hi_g hp hin hc hst hpk
      sp.cum ≤ w4Cum ∧ sp.live ≤ w4Live ∧ sp.peak ≤ w4Peak ∧
      sp.maxReq ≤ w4MaxReq ∧ sp.grpS ≤ w4GrpS)
    (hDecPkLp : w4Live ≤ w4Peak)
    (hFits : d3SlotMainFitsOneGiBOf
      w1EncExactCum w1EncExactLive w1EncExactPeak w1EncExactMaxReq w1EncExactGrpS
      w2DecSigExactCum w2DecSigExactLive w2DecSigExactPeak w2DecSigExactMaxReq w2DecSigExactGrpS
      w4Cum w4Live w4Peak w4MaxReq w4GrpS)
    (hS_enc : S.encrypt = encDef ⟨W.C, W.Q⟩ scopeIn := by rfl) :
    MainEntryBudgetFitsCapOf fineCostModel cliBudgetLimits fineCostModel.init cliIo
      (ReadFileRuleEnvFixed cliIo.rd) uuidTryParse
      (RunEnv
        (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          (hmx_binaryKitRunSlotEnvsSlotOf EncSlot DecSigSlot A B
            (realCliInitBinarySlotEnvFixed W) DecPkSlotEnv)
          PksmTryFromEnv S))
      (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel S)) :=
  mainEntryBudgetFitsCapOf_pqD3Recv_dom0
    EncSlot DecSigSlot img S X W A B DecPkSlotEnv
    w4Cum w4Live w4Peak w4MaxReq w4GrpS
    hNwDom hEncCredit hEncGrp hDecSigCredit hDecSigGrp
    (fun g meV peerV rest pm hi_g hp hin hc hst hpk => by
      obtain ⟨hc1, hl1, hp1, hr1, _⟩ := hDecPkCaps g meV peerV rest pm hi_g hp hin hc hst hpk
      exact (S_decPk g meV peerV rest pm hi_g hp hin hc hst hpk).credit.mono hc1 hl1 hp1 hr1)
    hDecPkLp
    (fun g meV peerV rest pm hi_g hp hin hc hst hpk => by
      obtain ⟨_, _, _, _, hg1⟩ := hDecPkCaps g meV peerV rest pm hi_g hp hin hc hst hpk
      exact (S_decPk g meV peerV rest pm hi_g hp hin hc hst hpk).groups.mono hg1)
    hFits hS_enc

end LibsignalBinary.Proofs.PeakBudget.D3MainEntryBudgetFitsCapDom0
