/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.CliKitW1IntoPbAuxR2
public import LibsignalBinary.Proofs.PeakBudget.CliKitW1SpqrSendStage1AuxR2
public import LibsignalBinary.Proofs.PeakBudget.CliKitW1W2ExactSlotSpecR2
public import LibsignalBinary.Proofs.PeakBudget.SpqrSendTightSpec
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbState
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.BraidCodec
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.BraidPhi
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.BraidSendClosed
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.TopSend
import LibsignalBinary.Proofs.SpqrV1Sync.TopSize

/-!
# `@109` `spqr::send::<Coins>` Tight Inclusion, Credit, and Group Specs

**Checked by Lean.**

Proves that under `SpqrStateTight640 F K stBs`, `ckx2_SpqrSendCoinsOfDecodeFromPbBytesEnv` at
`ckx2_DecodeStateTightEnvOf maxOps` and `StatesFromPbTightEnv` is contained in
`ckx2_SpqrSendTightCapEnvOf maxOps`, and establishes `PhaseCreditSpec`, `fineCredit` delta,
`evalLog` footprint, `NonFreeBound`, and `PhaseGroupSpec` at `maxOps = 109` (`4374` groups).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.CliKitW1SpqrSendAuxR2

open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.LibsignalSpqrV1
  (Bytes Chain ChainEpoch ChainEpochDirection ChainPB ChainResult Direction
   EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH Epoch EpochSecret HkdfFn MlKem PqRatchetState States
   StatesError V1Send V1State Version VersionNegotiationPB pbToPqRatchetState spqrAuthApi
   spqrHkdfWith spqrPolyApi)
open CryptoVerification.LibsignalSpqrV1.Proto (encodeState spqrDecodeState)
open CryptoVerification.SpqrV1.Drop (chunkedKeysSampledToCt1Received)
open CryptoVerification.SpqrV1.Prost.EncodeToVec
  (pqRatchetStatePBEncodedLen pqRatchetStatePBEncodedLen_eq_proto)
open CryptoVerification.SpqrV1.States.IntoPb (StatesIntoPbGhost)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget (nonFreeCount)
open CryptoVerification.SpqrV1.Top.Send (sendChainPhase sendResolveChain sendStepChain)
open CryptoVerification.SpqrV1.Top.StateSize
  (optRaw optRaw_none optRaw_some rawChain rawV1State rawVN)
open CryptoVerification.SpqrV1Sync.ChainSync (ChainOk chainOk_congr sendKey_ok)
open CryptoVerification.SpqrV1Sync.Codec (spqrDecodeState_encodeState)
open CryptoVerification.SpqrV1Sync.SendTotal
  (BOkTight RecvSmallTight chainCur_le_phiB freshB phiB st_bCodec st_bSendClosed_tight
   st_bSize_tight st_recvSmallAdd_tight st_recvSmallSend_tight tsnd_addEpoch_opt
   tsnd_send_addEpoch tsz_rawChain_tight_le)
open CryptoVerification.SpqrV1Sync.TopSync
  (chainCur chainCur_send_key chain_fromPb_intoPb epoch_sub_one_le_chainCur sendKey_sendPrevNil
   send_facts topBytes topBytes_length_le topPb vnOf)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent FreeOnlyEvs SeqEnv rustAllocEvents)
open LibsignalBinary.Heap.Fine (FineScale fineCostModel)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesBridge1PlacedBudgetAux
  (ChainIntoPbForEnv SendChainPhaseEnv SendKeyFirstEnv SendKeyIntoPbEnv SendStepChainEnv)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendDispatchPlacedBudgetAux
  (StatesSendEnvOfEnv StatesSendTightEnv)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.TopPhase3PlacedBudget
  (SendFrom317fcEnvOfEnv SendPhase3EnvOfEnv)
open LibsignalBinary.Proofs.PeakBudget.CliGroupBounds (spqrNonFreeCount_eq)
open LibsignalBinary.Proofs.PeakBudget.CliKitW1IntoPbAuxR2
  (ckx2_StatesIntoPbTightDom ckx2_statesIntoPbExactEnv_tight
   ckx2_topStateTight_from_pb_statesIntoPbTightDom ckx2_topStateTight_send_statesIntoPbTightDom)
open LibsignalBinary.Proofs.PeakBudget.CliKitW1SpqrSendStage1AuxR2
  (ckx2_chainAddEpochEnv_sub_tight4 ckx2_headerReceived1aEnv_sub_rodataTight
   ckx2_instDecidableFineSmallEvs ckx2_messageSerializeEnv_sub_tight
   ckx2_statesSendTightEnv_sub_rodataTight)
open LibsignalBinary.Proofs.PeakBudget.CliKitW1W2ExactSlotSpecR2
  (ckx2_DecodeStateTightEnv ckx2_DecodeStateTightEnvOf ckx2_SpqrSendCoinsOfDecodeFromPbBytesEnv)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit
  (HasFineGroupCredit NonFreeBound PhaseGroupSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (PhaseCreditSpec)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit
  (HasFineReallocCredit)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit
  (StatesIntoPbTightEnv spqrTightEvs_fine_phaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec
  (StatesFromPbTightEnv statesFromPbTightEnv_nonFreeCount_le
   statesFromPb_fine_phaseCreditSpec_tight statesIntoPbTightEnv_nonFreeCount_le
   statesIntoPb_fine_phaseCreditSpec_tight)
open LibsignalBinary.Proofs.PeakBudget.SpqrSendPeakSpec
  (fineCredit spqrSendTightDeltaCum spqrSendTightDeltaLive spqrSendTightDeltaPeak
   spqrSendTightFineCreditCap spqrSendTightLargeDeltaCum spqrSendTightMaxReq)
open LibsignalBinary.Proofs.PeakBudget.SpqrSendRodataCaps
  (PqEncodeCapTightEnv PqEncodeLargeTightEnv SpqrSendPartsTightGenEnv
   pqEncodeCapTight_fine_phaseCreditSpec pqEncodeCapTight_nonFreeCount_le
   pqEncodeLargeTight_fine_phaseCreditSpec
   pqRatchetStateEncodeToVecEnv_to_capTight spqrSendPartsTightGenEnv_or_pq
   spqrSendPartsTightGen_nonFreeCount_le spqrSendPartsTightGen_phaseCreditSpec
   statesRodataValid_of_bOk)
open LibsignalBinary.Proofs.PeakBudget.SpqrSendTightBuckets
  (FineSmallEvs fineSmallEvs_phaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrSendTightHelpers
  (ChainAddEpochTight4Env ChainFromTightEnv ChainIntoPbTight4Env ChainSendKeyTightEnv
   MessageSerializeTightEnv StatesRodataValid StatesSendRodataTightEnv
   chainAddEpochTight4_fine_phaseCreditSpec chainFromEnv_to_tight chainFromTight_fine_phaseCreditSpec
   chainIntoPbTight4_fine_phaseCreditSpec chainSendKeyEnv_to_tight
   chainSendKeyTight_fine_phaseCreditSpec messageSerializeTight_fine_phaseCreditSpec
   statesSendRodataTight_fine_phaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux
  (SpqrStateTight640 TopStateTight topStateTightW_links_le_three topStateTight_to_tightValid640)
open LibsignalBinary.Proofs.SpqrV1.Chain.SendKeyHelpersBudget (ChainSendKeyAllocEnv ChainSendKeyEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.MessageSerializeBudget (MessageSerializeEnv)
open LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget (SpqrSendBudgetEnv)

/-! ## `maxOps`-Parametric Tight Cap Envelopes and Credit / Group Specs -/

def ckx2_SpqrSendTightCapGenEnv (Edec : List AllocEvent → Prop) : SpqrSendBudgetEnv :=
  fun _ _ =>
    SpqrSendPartsTightGenEnv Edec StatesFromPbTightEnv
      StatesSendRodataTightEnv ChainFromTightEnv ChainAddEpochTight4Env ChainSendKeyTightEnv
      ChainIntoPbTight4Env MessageSerializeTightEnv StatesIntoPbTightEnv
      (PqEncodeCapTightEnv 286196)

def ckx2_SpqrSendTightCapEnvOf (maxOps : Nat) : SpqrSendBudgetEnv :=
  ckx2_SpqrSendTightCapGenEnv (ckx2_DecodeStateTightEnvOf maxOps)

abbrev ckx2_SpqrSendTightCapEnv109 : SpqrSendBudgetEnv :=
  ckx2_SpqrSendTightCapEnvOf 109

def ckx2_SpqrSendTightLargeGenEnv (Edec : List AllocEvent → Prop) : SpqrSendBudgetEnv :=
  fun _ _ =>
    SpqrSendPartsTightGenEnv Edec StatesFromPbTightEnv
      StatesSendRodataTightEnv ChainFromTightEnv ChainAddEpochTight4Env ChainSendKeyTightEnv
      ChainIntoPbTight4Env MessageSerializeTightEnv StatesIntoPbTightEnv
      (PqEncodeLargeTightEnv 286196)

def ckx2_SpqrSendTightLargeEnvOf (maxOps : Nat) : SpqrSendBudgetEnv :=
  ckx2_SpqrSendTightLargeGenEnv (ckx2_DecodeStateTightEnvOf maxOps)

def ckx2_spqrSendTightMaxNonFreeOf (maxOps : Nat) : Nat := maxOps + 1349

def ckx2_spqrSendTightGroupSOf (maxOps : Nat) : Nat := 3 * FineScale * (maxOps + 1349)

private theorem ckx2_decodeStateTightEnvOf_fine_phaseCreditSpec (maxOps : Nat) :
    PhaseCreditSpec fineCostModel (ckx2_DecodeStateTightEnvOf maxOps) 1307216 0 0 79236 :=
  spqrTightEvs_fine_phaseCreditSpec maxOps 1307216 (Nat.le_refl 79236)

theorem ckx2_spqrSendTightCapEnvOf_phaseCreditSpec (maxOps : Nat) (stBytes ptext : Bytes) :
    PhaseCreditSpec fineCostModel (ckx2_SpqrSendTightCapEnvOf maxOps stBytes ptext)
      spqrSendTightDeltaCum spqrSendTightDeltaLive spqrSendTightDeltaPeak spqrSendTightMaxReq :=
  (spqrSendPartsTightGen_phaseCreditSpec
    (ckx2_decodeStateTightEnvOf_fine_phaseCreditSpec maxOps)
    statesFromPb_fine_phaseCreditSpec_tight
    statesSendRodataTight_fine_phaseCreditSpec
    chainFromTight_fine_phaseCreditSpec
    chainAddEpochTight4_fine_phaseCreditSpec
    chainSendKeyTight_fine_phaseCreditSpec
    chainIntoPbTight4_fine_phaseCreditSpec
    messageSerializeTight_fine_phaseCreditSpec
    statesIntoPb_fine_phaseCreditSpec_tight
    (pqEncodeCapTight_fine_phaseCreditSpec 286196)
    (Nat.le_refl spqrSendTightDeltaLive)).mono
    (by decide) (Nat.le_refl _) (Nat.le_refl _) (by decide)

theorem ckx2_spqrSendTightLargeEnvOf_phaseCreditSpec (maxOps : Nat) (stBytes ptext : Bytes) :
    PhaseCreditSpec fineCostModel (ckx2_SpqrSendTightLargeEnvOf maxOps stBytes ptext)
      spqrSendTightLargeDeltaCum spqrSendTightDeltaLive spqrSendTightDeltaPeak
      spqrSendTightMaxReq :=
  (spqrSendPartsTightGen_phaseCreditSpec
    (ckx2_decodeStateTightEnvOf_fine_phaseCreditSpec maxOps)
    statesFromPb_fine_phaseCreditSpec_tight
    statesSendRodataTight_fine_phaseCreditSpec
    chainFromTight_fine_phaseCreditSpec
    chainAddEpochTight4_fine_phaseCreditSpec
    chainSendKeyTight_fine_phaseCreditSpec
    chainIntoPbTight4_fine_phaseCreditSpec
    messageSerializeTight_fine_phaseCreditSpec
    statesIntoPb_fine_phaseCreditSpec_tight
    (pqEncodeLargeTight_fine_phaseCreditSpec 286196)
    (Nat.le_refl spqrSendTightDeltaLive)).mono
    (by decide) (Nat.le_refl _) (Nat.le_refl _) (by decide)

private theorem ckx2_fineCredit_le_of_spec {E : List AllocEvent → Prop} {c p r : Nat}
    (hSpec : PhaseCreditSpec fineCostModel E c p p r)
    (s0 : fineCostModel.σ) {evs : List AllocEvent} (hevs : E evs) {cap : Nat}
    (hcap : c + p ≤ cap) :
    fineCredit fineCostModel (fineCostModel.stepEvents evs s0) ≤
      fineCredit fineCostModel s0 + cap := by
  unfold fineCredit
  obtain ⟨hc, hl, hp⟩ := hSpec.credit_le s0 hevs
  have hmax :
      max (LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit.HasFineReallocCredit.liveLarge
            (fineCostModel.stepEvents evs s0))
          (LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit.HasFineReallocCredit.peakLarge
            (fineCostModel.stepEvents evs s0)) ≤
        max (LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit.HasFineReallocCredit.liveLarge s0)
            (LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit.HasFineReallocCredit.peakLarge s0) + p :=
    Nat.max_le.mpr
      ⟨Nat.le_trans hl (Nat.add_le_add_right (Nat.le_max_left _ _) p),
       Nat.le_trans hp (Nat.max_le.mpr
         ⟨Nat.le_trans (Nat.le_max_right _ _) (Nat.le_add_right _ p),
          Nat.add_le_add_right (Nat.le_max_left _ _) p⟩)⟩
  have hadd := Nat.add_le_add hc hmax
  have hreord :
      (LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit.HasFineReallocCredit.cumSmall s0 + c) +
        (max (LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit.HasFineReallocCredit.liveLarge s0)
             (LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit.HasFineReallocCredit.peakLarge s0) + p) =
      (LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit.HasFineReallocCredit.cumSmall s0 +
        max (LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit.HasFineReallocCredit.liveLarge s0)
            (LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit.HasFineReallocCredit.peakLarge s0)) + (c + p) := by
    simp only [← Nat.add_assoc]
    simp only [Nat.add_assoc, Nat.add_left_comm c]
  rw [hreord] at hadd
  exact Nat.le_trans hadd (Nat.add_le_add_left hcap _)

theorem ckx2_spqrSendTightCapEnvOf_fineCredit_le (maxOps : Nat) {stBytes ptext : Bytes}
    (s0 : fineCostModel.σ) {evs : List AllocEvent}
    (hevs : ckx2_SpqrSendTightCapEnvOf maxOps stBytes ptext evs) :
    fineCredit fineCostModel (fineCostModel.stepEvents evs s0) ≤
      fineCredit fineCostModel s0 + spqrSendTightFineCreditCap := by
  rcases spqrSendPartsTightGenEnv_or_pq hevs with hSmall | hLarge
  · have hSmSpec := spqrSendPartsTightGen_phaseCreditSpec
      (ckx2_decodeStateTightEnvOf_fine_phaseCreditSpec maxOps)
      statesFromPb_fine_phaseCreditSpec_tight
      statesSendRodataTight_fine_phaseCreditSpec
      chainFromTight_fine_phaseCreditSpec
      chainAddEpochTight4_fine_phaseCreditSpec
      chainSendKeyTight_fine_phaseCreditSpec
      chainIntoPbTight4_fine_phaseCreditSpec
      messageSerializeTight_fine_phaseCreditSpec
      statesIntoPb_fine_phaseCreditSpec_tight
      (fineSmallEvs_phaseCreditSpec 1 143484 (Nat.min_le_right 286196 135167))
      (Nat.le_refl 0)
    exact ckx2_fineCredit_le_of_spec hSmSpec s0 hSmall (by decide)
  · exact ckx2_fineCredit_le_of_spec
      (ckx2_spqrSendTightLargeEnvOf_phaseCreditSpec maxOps stBytes ptext)
      s0 hLarge (by decide)

theorem ckx2_spqrSendTightCapEnvOf_evalLog_footprint_le (maxOps : Nat) {stBytes ptext : Bytes}
    {evs : List AllocEvent}
    (hevs : ckx2_SpqrSendTightCapEnvOf maxOps stBytes ptext evs) :
    fineCostModel.footprint (fineCostModel.evalLog evs) ≤
      LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit.HasFineReallocCredit.baseFine
        (M := fineCostModel) + spqrSendTightFineCreditCap := by
  rcases spqrSendPartsTightGenEnv_or_pq hevs with hSmall | hLarge
  · have hSmSpec := spqrSendPartsTightGen_phaseCreditSpec
      (ckx2_decodeStateTightEnvOf_fine_phaseCreditSpec maxOps)
      statesFromPb_fine_phaseCreditSpec_tight
      statesSendRodataTight_fine_phaseCreditSpec
      chainFromTight_fine_phaseCreditSpec
      chainAddEpochTight4_fine_phaseCreditSpec
      chainSendKeyTight_fine_phaseCreditSpec
      chainIntoPbTight4_fine_phaseCreditSpec
      messageSerializeTight_fine_phaseCreditSpec
      statesIntoPb_fine_phaseCreditSpec_tight
      (fineSmallEvs_phaseCreditSpec 1 143484 (Nat.min_le_right 286196 135167))
      (Nat.le_refl 0)
    have hfp := hSmSpec.evalLog_footprint_le_of_live_le_peak (Nat.le_refl 0) hSmall
    rw [Nat.add_zero] at hfp
    exact Nat.le_trans hfp (Nat.add_le_add_left
      (show _ ≤ spqrSendTightFineCreditCap by decide) _)
  · have hLgSpec := ckx2_spqrSendTightLargeEnvOf_phaseCreditSpec maxOps stBytes ptext
    have hfp := hLgSpec.evalLog_footprint_le_of_live_le_peak
      (Nat.le_refl spqrSendTightDeltaLive) hLarge
    exact Nat.le_trans hfp (Nat.add_le_add_left
      (show spqrSendTightLargeDeltaCum + spqrSendTightDeltaPeak ≤ spqrSendTightFineCreditCap by
        decide) _)

theorem ckx2_spqrSendTightCapEnvOf_nonFreeCount_le (maxOps : Nat) {stBytes ptext : Bytes}
    {evs : List AllocEvent}
    (hEnv : ckx2_SpqrSendTightCapEnvOf maxOps stBytes ptext evs) :
    nonFreeCount evs ≤ ckx2_spqrSendTightMaxNonFreeOf maxOps := by
  have hc := spqrSendPartsTightGen_nonFreeCount_le
    (fun _ hd => hd.1)
    (fun _ hf => statesFromPbTightEnv_nonFreeCount_le hf)
    (fun _ hs => hs.1)
    (fun _ hcf => hcf.1)
    (fun _ ha => ha.1)
    (fun _ hsk => hsk.1)
    (fun _ hci => hci.1)
    (fun _ hm => hm.1)
    (fun _ hsi => statesIntoPbTightEnv_nonFreeCount_le hsi)
    (fun _ hpq => pqEncodeCapTight_nonFreeCount_le hpq)
    hEnv
  unfold ckx2_spqrSendTightMaxNonFreeOf
  omega

theorem ckx2_spqrSendTightCapEnvOf_nonFreeBound (maxOps : Nat) (stBytes ptext : Bytes) :
    NonFreeBound (ckx2_SpqrSendTightCapEnvOf maxOps stBytes ptext)
      (ckx2_spqrSendTightMaxNonFreeOf maxOps) :=
  fun _ h => by
    rw [← spqrNonFreeCount_eq]
    exact ckx2_spqrSendTightCapEnvOf_nonFreeCount_le maxOps h

theorem ckx2_spqrSendTightCapEnvOf_phaseGroupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    (maxOps : Nat) (stBytes ptext : Bytes) :
    PhaseGroupSpec M (ckx2_SpqrSendTightCapEnvOf maxOps stBytes ptext)
      (ckx2_spqrSendTightGroupSOf maxOps) :=
  PhaseGroupSpec.of_nonFreeBound M (ckx2_spqrSendTightCapEnvOf_nonFreeBound maxOps stBytes ptext)

/-! ## Full 10-Stage Inclusion under `SpqrStateTight640` -/

private instance ckx2_instDecidableChainIntoPbTight4Env (evs : List AllocEvent) :
    Decidable (ChainIntoPbTight4Env evs) :=
  ckx2_instDecidableFineSmallEvs 1 8186 448 evs

private theorem ckx2_statesSendTightEnv_eq_nil_of_send_error {F : ShaCompress} {K : MlKem}
    {st0 : States spqrPolyApi (spqrAuthApi F)} {tape : Bytes}
    {err : StatesError} {evs : List AllocEvent}
    (hSend : st0.send K tape = .error err)
    (hEnv : StatesSendTightEnv F K st0 tape evs) :
    evs = [] := by
  unfold StatesSendTightEnv StatesSendEnvOfEnv at hEnv
  unfold States.send at hSend
  cases st0 with
  | keysUnsampled st =>
    dsimp only at hEnv hSend
    split at hEnv
    · rename_i hok
      simp [hok, CryptoVerification.LibsignalSpqrV1.StatesResult.ofPanic,
        Bind.bind, Except.bind] at hSend
    · exact hEnv
  | keysSampled st =>
    dsimp only [chunkedKeysSampledToCt1Received,
      CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.Ct1Received.send_ek_chunk,
      CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.KeysSampled.send_hdr_chunk,
      Bind.bind, Except.bind] at hEnv hSend
    cases hnc : spqrPolyApi.next_chunk st.sending_hdr with
    | error _ =>
      simp [hnc, liftM, monadLift, MonadLift.monadLift] at hEnv
      exact hEnv
    | ok p =>
      rcases p with ⟨_, _⟩
      simp [hnc, liftM, monadLift, MonadLift.monadLift,
        CryptoVerification.LibsignalSpqrV1.liftSpqrPanic,
        CryptoVerification.LibsignalSpqrV1.StatesResult.ofPanic] at hSend
  | headerSent st =>
    dsimp only [CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.HeaderSent.send_ek_chunk,
      Bind.bind, Except.bind] at hEnv hSend
    cases hnc : spqrPolyApi.next_chunk st.sending_ek with
    | error _ =>
      simp [hnc, liftM, monadLift, MonadLift.monadLift] at hEnv
      exact hEnv
    | ok p =>
      rcases p with ⟨_, _⟩
      simp [hnc, liftM, monadLift, MonadLift.monadLift,
        CryptoVerification.LibsignalSpqrV1.liftSpqrPanic,
        CryptoVerification.LibsignalSpqrV1.StatesResult.ofPanic] at hSend
  | ct1Received st =>
    dsimp only [CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.Ct1Received.send_ek_chunk,
      Bind.bind, Except.bind] at hEnv hSend
    cases hnc : spqrPolyApi.next_chunk st.sending_ek with
    | error _ =>
      simp [hnc, liftM, monadLift, MonadLift.monadLift] at hEnv
      exact hEnv
    | ok p =>
      rcases p with ⟨_, _⟩
      simp [hnc, liftM, monadLift, MonadLift.monadLift,
        CryptoVerification.LibsignalSpqrV1.liftSpqrPanic,
        CryptoVerification.LibsignalSpqrV1.StatesResult.ofPanic] at hSend
  | ekSentCt1Received _ => exact hEnv
  | noHeaderReceived _ => exact hEnv
  | headerReceived st =>
    dsimp only at hEnv hSend
    split at hEnv
    · rename_i hok
      simp [hok, CryptoVerification.LibsignalSpqrV1.StatesResult.ofPanic,
        Bind.bind, Except.bind] at hSend
    · exact hEnv
  | ct1Sampled st =>
    dsimp only [CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.Ct1Sampled.send_ct1_chunk,
      Bind.bind, Except.bind] at hEnv hSend
    cases hnc : spqrPolyApi.next_chunk st.sending_ct1 with
    | error _ =>
      simp [hnc, liftM, monadLift, MonadLift.monadLift] at hEnv
      exact hEnv
    | ok p =>
      rcases p with ⟨_, _⟩
      simp [hnc, liftM, monadLift, MonadLift.monadLift,
        CryptoVerification.LibsignalSpqrV1.liftSpqrPanic,
        CryptoVerification.LibsignalSpqrV1.StatesResult.ofPanic] at hSend
  | ekReceivedCt1Sampled st =>
    dsimp only [CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.EkReceivedCt1Sampled.send_ct1_chunk,
      Bind.bind, Except.bind] at hEnv hSend
    cases hnc : spqrPolyApi.next_chunk st.sending_ct1 with
    | error _ =>
      simp [hnc, liftM, monadLift, MonadLift.monadLift] at hEnv
      exact hEnv
    | ok p =>
      rcases p with ⟨_, _⟩
      simp [hnc, liftM, monadLift, MonadLift.monadLift,
        CryptoVerification.LibsignalSpqrV1.liftSpqrPanic,
        CryptoVerification.LibsignalSpqrV1.StatesResult.ofPanic] at hSend
  | ct1Acknowledged _ => exact hEnv
  | ct2Sampled st =>
    dsimp only [CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.Ct2Sampled.send_ct2_chunk,
      Bind.bind, Except.bind] at hEnv hSend
    cases hnc : spqrPolyApi.next_chunk st.sending_ct2 with
    | error _ =>
      simp [hnc, liftM, monadLift, MonadLift.monadLift] at hEnv
      exact hEnv
    | ok p =>
      rcases p with ⟨_, _⟩
      simp [hnc, liftM, monadLift, MonadLift.monadLift,
        CryptoVerification.LibsignalSpqrV1.liftSpqrPanic,
        CryptoVerification.LibsignalSpqrV1.StatesResult.ofPanic] at hSend

private theorem ckx2_chain_addEpoch_links_eq {hkdf : HkdfFn} {c0 c1 : Chain} {es : EpochSecret}
    (h : Chain.addEpoch hkdf c0 es = .ok c1) :
    c1.links.length = c0.links.length + 1 := by
  unfold Chain.addEpoch at h
  split at h <;> [contradiction; skip]
  split at h <;> [contradiction; skip]
  injection h with hc1
  subst hc1
  simp

private theorem ckx2_chain_sendKey_links_le {hkdf : HkdfFn} {c1 c2 : Chain} {ep : Epoch}
    {out : BitVec 32 × Bytes} (h : Chain.sendKey hkdf c1 ep = .ok (c2, out)) :
    c2.links.length ≤ c1.links.length := by
  unfold Chain.sendKey at h
  split at h <;> [contradiction; skip]
  cases hep : c1.epochIdx ep with
  | error _ => simp [hep, ChainResult.ofError, Bind.bind, Except.bind] at h
  | ok idx0 =>
    simp only [hep, ChainResult.ofError, Bind.bind, Except.bind] at h
    by_cases hne : (c1.sendEpoch != ep) = true
    · simp only [hne, ↓reduceIte] at h
      split at h <;> [contradiction; skip]
      split at h <;> [contradiction; skip]
      simp only [Pure.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨hc2, _⟩ := h
      subst hc2
      simp [List.length_set, List.length_drop]
    · simp only [hne, Bool.false_eq_true, ↓reduceIte] at h
      split at h <;> [contradiction; skip]
      split at h <;> [contradiction; skip]
      simp only [Pure.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨hc2, _⟩ := h
      subst hc2
      simp [List.length_set]

private theorem ckx2_getElem?_clearSendNextPrefix_self :
    ∀ (n : Nat) (xs : List ChainEpoch),
      (Chain.clearSendNextPrefix n xs)[n]? = xs[n]?
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | n + 1, _ :: xs => ckx2_getElem?_clearSendNextPrefix_self n xs

private theorem ckx2_nextKey_ctr_lt {hkdf : HkdfFn} {d : ChainEpochDirection}
    {v : ChainEpochDirection × (BitVec 32 × Bytes)}
    (h : ChainResult.ofPanic (d.nextKey hkdf) = .ok v) :
    d.ctr.toNat + 1 < 2 ^ 32 := by
  cases hnk : d.nextKey hkdf with
  | error _ => simp [hnk, ChainResult.ofPanic] at h
  | ok r =>
    unfold ChainEpochDirection.nextKey ChainEpochDirection.nextKeyInternal at hnk
    split at hnk <;> [contradiction; skip]
    split at hnk
    · contradiction
    · rename_i hctr_ne
      have hne : d.ctr ≠ 0xffffffff#32 := by simpa using hctr_ne
      have hlt := d.ctr.isLt
      have hnat_ne : d.ctr.toNat ≠ 4294967295 :=
        fun heq => hne (BitVec.eq_of_toNat_eq heq)
      omega

private theorem ckx2_sendKey_ctr_lt {F : ShaCompress} {authKey : Bytes} {dir : Direction}
    {secret : Nat → Bytes} {sendCtr : Nat → Nat} {recvSet : Nat → Finset Nat}
    {ch ch' : Chain} {e : Epoch} {out : BitVec 32 × Bytes}
    (hok : ChainOk F authKey dir secret sendCtr recvSet ch)
    (hlo : ch.sendEpoch.toNat ≤ e.toNat) (hhi : e.toNat ≤ ch.currentEpoch.toNat)
    (hsk : ch.sendKey (spqrHkdfWith F) e = .ok (ch', out)) :
    sendCtr e.toNat + 1 < 2 ^ 32 := by
  obtain ⟨link0, hlink0, hsendOk⟩ := hok.hsendDir e.toNat hlo hhi
  unfold Chain.sendKey at hsk
  split at hsk <;> [contradiction; skip]
  cases hep : ch.epochIdx e with
  | error _ => simp [hep, ChainResult.ofError, Bind.bind, Except.bind] at hsk
  | ok idx0 =>
    have hidx0 : idx0 = e.toNat - (ch.sendEpoch.toNat - 1) := by
      unfold Chain.epochIdx at hep
      split at hep <;> [contradiction; skip]
      dsimp only at hep
      split at hep <;> [contradiction; skip]
      have hinj := Except.ok.inj hep
      have hsub : (ch.currentEpoch - e).toNat = ch.currentEpoch.toNat - e.toNat :=
        BitVec.toNat_sub_of_le hhi
      have hlen := hok.hlen
      omega
    simp only [hep, ChainResult.ofError, Bind.bind, Except.bind] at hsk
    by_cases hne : (ch.sendEpoch != e) = true
    · simp only [hne, ↓reduceIte, ckx2_getElem?_clearSendNextPrefix_self, List.getElem?_drop] at hsk
      have hadd :
          idx0 - EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH +
            (idx0 - (idx0 - EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH)) = idx0 := by
        unfold EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH; omega
      rw [hadd, hidx0, hlink0] at hsk
      dsimp only at hsk
      cases hnk : ChainResult.ofPanic (link0.send.nextKey (spqrHkdfWith F)) with
      | error _ => rw [hnk] at hsk; contradiction
      | ok v =>
        have hlt := ckx2_nextKey_ctr_lt hnk
        rw [hsendOk.hctr] at hlt
        exact hlt
    · simp only [hne, Bool.false_eq_true, ↓reduceIte, hidx0, hlink0] at hsk
      cases hnk : ChainResult.ofPanic (link0.send.nextKey (spqrHkdfWith F)) with
      | error _ => rw [hnk] at hsk; contradiction
      | ok v =>
        have hlt := ckx2_nextKey_ctr_lt hnk
        rw [hsendOk.hctr] at hlt
        exact hlt

private theorem ckx2_pqRatchetStatePBEncodedLen_send_le_286196 {F : ShaCompress} {K : MlKem}
    {stBytes tape tape' : Bytes} {pq : PqRatchetState} {v1 : V1State}
    {st0 : States spqrPolyApi (spqrAuthApi F)} {sOut : V1Send spqrPolyApi (spqrAuthApi F)}
    {idx : BitVec 32} {msgKey : Bytes} {chainPb : Option ChainPB}
    (hTop : TopStateTight F K stBytes)
    (hDec : spqrDecodeState stBytes = .ok pq)
    (hV1 : pq.inner = some (.v1 v1))
    (hFromPb : States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .ok st0)
    (hSendB : st0.send K tape = .ok (sOut, tape'))
    (hCh : sendChainPhase (spqrHkdfWith F) pq.chain pq.versionNegotiation
      sOut.key sOut.msg.epoch = .ok (idx, msgKey, chainPb)) :
    pqRatchetStatePBEncodedLen
      { versionNegotiation := pq.versionNegotiation
        chain := chainPb
        inner := some (.v1 sOut.state.into_pb) } ≤ 286196 := by
  obtain ⟨_, _, hlt31⟩ := topStateTight_to_tightValid640 hTop
  have hsize : stBytes.length < 2 ^ 64 := Nat.lt_trans hlt31 (by decide)
  obtain ⟨authKey, dir, secret, st, _sendEp, sendCtr, recvSet, vn?, ch?, chE, hw⟩ := hTop
  have hdec_eq : spqrDecodeState stBytes = .ok (pbToPqRatchetState (topPb st vn? ch?)) := by
    have hbeq := hw.htop.hbytes
    rw [hbeq] at hsize ⊢
    exact spqrDecodeState_encodeState (pbToPqRatchetState (topPb st vn? ch?)) hsize
  rw [hdec_eq] at hDec
  have hpq := Except.ok.inj hDec
  subst hpq
  simp only [pbToPqRatchetState, topPb, Option.map] at hV1
  cases hV1
  have hcodec : States.from_pb spqrPolyApi (spqrAuthApi F) st.into_pb = .ok st :=
    st_bCodec F st hw.hbok.1
  rw [hcodec] at hFromPb
  have hst0 := Except.ok.inj hFromPb
  subst hst0
  rcases sOut with ⟨m, key, st'⟩
  have hep_pos : 1 ≤ st.epoch.toNat := by have := hw.htop.hsendLe; omega
  obtain ⟨hm_ep, hst'_ep, -, -⟩ := send_facts F K st st' tape tape' m key hSendB
  let secret' : Nat → Bytes :=
    match key with
    | none => secret
    | some es => Function.update secret (chainCur st + 1) es.secret
  have hok' : ChainOk F authKey dir secret' sendCtr recvSet chE := by
    refine chainOk_congr F authKey dir secret secret' sendCtr recvSet chE hw.htop.hok ?_
    intro e _ he
    have hcur := hw.htop.hcur
    cases key with
    | none => rfl
    | some es => exact Function.update_of_ne (by omega) _ _
  have hsec : ∀ es, key = some es → es.secret = secret' es.epoch.toNat := by
    intro es hk
    subst hk
    obtain ⟨hes_ep, -⟩ := chainCur_send_key F K st st' tape tape' m es hep_pos hSendB
    change es.secret = Function.update secret (chainCur st + 1) es.secret es.epoch.toNat
    rw [hes_ep, Function.update_self]
  obtain ⟨chain1, hadd, hok1, hcur1, hsend1, hle1⟩ :=
    tsnd_send_addEpoch F K authKey dir secret' st st' sendCtr recvSet chE hok'
      hw.htop.hcur hep_pos tape tape' m key hSendB hsec
  have he_ne0 : (m.epoch == 0#64) = false := by
    rw [beq_eq_false_iff_ne]
    intro h0
    have : m.epoch.toNat = 0 := congrArg BitVec.toNat h0
    rw [hm_ep] at this
    omega
  have hebv_nat : (m.epoch - 1#64).toNat = st.epoch.toNat - 1 := by
    rw [hm_ep, BitVec.toNat_sub_of_le]
    · rfl
    · show 1 ≤ st.epoch.toNat; exact hep_pos
  have hlo : chain1.sendEpoch.toNat ≤ (m.epoch - 1#64).toNat := by
    rw [hsend1, hw.htop.hsendEp, hebv_nat]
    have := hw.htop.hsendLe
    omega
  have hhi : (m.epoch - 1#64).toNat ≤ chain1.currentEpoch.toNat := by
    rw [hebv_nat]
    exact (epoch_sub_one_le_chainCur st).trans hle1
  have hfp := chain_fromPb_intoPb F authKey dir secret sendCtr recvSet chE hw.htop.hok
  have hslt : BitVec.slt Version.v0.toI32 (vnOf dir authKey).minVersion = true := rfl
  have hres_ch :
      sendResolveChain (spqrHkdfWith F)
        (pbToPqRatchetState (topPb st vn? ch?)).chain
        (pbToPqRatchetState (topPb st vn? ch?)).versionNegotiation = .ok (some chE) := by
    rcases hw.htop.hch with rfl | ⟨rfl, rfl, hvnE⟩
    · simp [sendResolveChain, pbToPqRatchetState, topPb, hfp,
        CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofError, Bind.bind, Except.bind,
        Pure.pure, Except.pure]
    · simp [sendResolveChain, pbToPqRatchetState, topPb, hslt, hvnE,
        CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofError, Bind.bind, Except.bind,
        Pure.pure, Except.pure]
  have hsk_ex : ∃ c2,
      chain1.sendKey (spqrHkdfWith F) (m.epoch - 1#64) = .ok (c2, (idx, msgKey)) ∧
      chainPb = some c2.intoPb := by
    unfold sendChainPhase at hCh
    rw [hres_ch] at hCh
    dsimp only [Bind.bind, Except.bind] at hCh
    unfold sendStepChain at hCh
    dsimp only at hCh
    have hCh1 :
        (if (m.epoch == 0#64) = true then
           Except.error
             (CryptoVerification.LibsignalSpqrV1.SpqrApiError.panic
               CryptoVerification.LibsignalSpqrV1.SpqrApiPanic.sendEpochUnderflow)
         else do
           let __x ←
             CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofChainResult
               (Chain.sendKey (spqrHkdfWith F) chain1 (m.epoch - 1#64))
           pure (__x.2.1, __x.2.2, some __x.1.intoPb)) =
          Except.ok (idx, msgKey, chainPb) := by
      cases key with
      | none =>
        cases hadd
        simpa [Pure.pure, Except.pure, Bind.bind, Except.bind] using hCh
      | some es =>
        dsimp only at hadd
        simpa [hadd, CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofChainPanic,
          Bind.bind, Except.bind] using hCh
    rw [he_ne0] at hCh1
    simp only [Bool.false_eq_true, ↓reduceIte] at hCh1
    cases hsk_raw : chain1.sendKey (spqrHkdfWith F) (m.epoch - 1#64) with
    | error err =>
      rcases err with _ | _ <;>
        simp [hsk_raw, CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofChainResult,
          Bind.bind, Except.bind] at hCh1
    | ok p =>
      rcases p with ⟨c2, idx', mk'⟩
      simp only [hsk_raw, CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofChainResult,
        Bind.bind, Except.bind, Pure.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hCh1
      exact ⟨c2, by rw [hCh1.1, hCh1.2.1], hCh1.2.2.symm⟩
  obtain ⟨c2, hsk_c2, hpb_eq⟩ := hsk_ex
  have hctr_lt : sendCtr (m.epoch - 1#64).toNat + 1 < 2 ^ 32 :=
    ckx2_sendKey_ctr_lt hok1 hlo hhi hsk_c2
  obtain ⟨chain2, hsk, hcur2, hsend2, hok2⟩ :=
    sendKey_ok F authKey dir secret' sendCtr recvSet chain1 hok1 (m.epoch - 1#64) hlo hhi hctr_lt
  have hc2_eq : c2 = chain2 := by
    rw [hsk] at hsk_c2
    exact (Prod.mk.inj (Except.ok.inj hsk_c2)).1.symm
  rw [hc2_eq] at hpb_eq
  subst hpb_eq
  rw [hebv_nat] at hsk hok2
  have hsp1 := tsnd_addEpoch_opt (spqrHkdfWith F) chE chain1 key hw.htop.hsendPrev hadd
  have hsp2 := sendKey_sendPrevNil (spqrHkdfWith F) chain1 chain2 _ _ hsp1 hsk
  have hsmall1 : RecvSmallTight chain1 := by
    cases key with
    | none => cases hadd; exact hw.hsmall
    | some es => exact st_recvSmallAdd_tight hw.hsmall hadd
  have hsmall2 : RecvSmallTight chain2 := st_recvSmallSend_tight hsmall1 hsk
  have hbok' : BOkTight st' := st_bSendClosed_tight F K hw.hbok hSendB
  have hphi' : phiB st' ≤ (st.epoch.toNat - 1) + 1 := by
    unfold phiB
    rw [hst'_ep]
    cases freshB st' <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  have hlinks2 : chain2.links.length ≤ 3 := by
    have hlen2 := hok2.hlen
    have hc_le := chainCur_le_phiB st'
    rw [hcur2, hcur1, hsend2, hebv_nat] at hlen2
    omega
  have hvn_eq : (pbToPqRatchetState (topPb st vn? ch?)).versionNegotiation = vn? := rfl
  rw [hvn_eq]
  have hpq'_eq :
      ({ versionNegotiation := vn?, chain := some chain2.intoPb,
         inner := some (.v1 st'.into_pb) } : PqRatchetState) =
        pbToPqRatchetState (topPb st' vn? (some chain2)) := rfl
  rw [hpq'_eq, ← pqRatchetStatePBEncodedLen_eq_proto]
  have htb_eq : PqRatchetState.encodeRaw (pbToPqRatchetState (topPb st' vn? (some chain2))) =
      topBytes F K st' vn? (some chain2) := rfl
  rw [htb_eq]
  have htop_le := topBytes_length_le F K st' vn? (some chain2)
  have hvn_le : optRaw rawVN vn? ≤ 32 := by
    rcases hw.htop.hvn with rfl | rfl
    · simp [optRaw_none]
    · simp [optRaw_some, rawVN, vnOf, hw.hauth]
  have hch_le : optRaw rawChain ((some chain2).map Chain.intoPb) ≤ 238532 := by
    simp only [Option.map, optRaw_some]
    exact tsz_rawChain_tight_le F authKey dir secret'
      (Function.update sendCtr (st.epoch.toNat - 1) (sendCtr (st.epoch.toNat - 1) + 1))
      recvSet chain2 hok2 hsp2 hsmall2 hlinks2
  have hv1_le : rawV1State st'.into_pb ≤ 46880 := st_bSize_tight F st' hbok'
  omega

private theorem ckx2_seqEnv_mono {P₁ P₂ Q₁ Q₂ : List AllocEvent → Prop} {evs : List AllocEvent}
    (hP : ∀ e, P₁ e → P₂ e) (hQ : ∀ e, Q₁ e → Q₂ e) (h : SeqEnv P₁ Q₁ evs) :
    SeqEnv P₂ Q₂ evs := by
  rcases h with hp | ⟨x1, x2, rfl, hp, hq⟩
  · exact Or.inl (hP evs hp)
  · exact Or.inr ⟨x1, x2, rfl, hP x1 hp, hQ x2 hq⟩

private abbrev ckx2_Stages8To10TightEnv : List AllocEvent → Prop :=
  SeqEnv MessageSerializeTightEnv
    (SeqEnv StatesIntoPbTightEnv
      (SeqEnv (PqEncodeCapTightEnv 286196) FreeOnlyEvs))

private abbrev ckx2_Stage7To10Env (e₆ : List AllocEvent) : Prop :=
  FreeOnlyEvs e₆ ∨ SeqEnv ChainIntoPbTight4Env ckx2_Stages8To10TightEnv e₆

private abbrev ckx2_Stage6To10Env (e₅ : List AllocEvent) : Prop :=
  FreeOnlyEvs e₅ ∨ SeqEnv ChainSendKeyTightEnv ckx2_Stage7To10Env e₅

private abbrev ckx2_Stage5To10Env (e₄ : List AllocEvent) : Prop :=
  FreeOnlyEvs e₄ ∨ SeqEnv ChainAddEpochTight4Env ckx2_Stage6To10Env e₄

private abbrev ckx2_Stage4To10Env (e₃ : List AllocEvent) : Prop :=
  FreeOnlyEvs e₃ ∨ SeqEnv ChainFromTightEnv ckx2_Stage5To10Env e₃

private def ckx2_ChainStagesTightEnv : List AllocEvent → Prop :=
  SeqEnv ChainFromTightEnv
    (SeqEnv ChainAddEpochTight4Env
      (SeqEnv ChainSendKeyTightEnv ChainIntoPbTight4Env))

private theorem ckx2_fineSmallEvs_append_freeOnly {o c r : Nat} {x f : List AllocEvent}
    (hx : FineSmallEvs o c r x) (hf : FreeOnlyEvs f) :
    FineSmallEvs o c r (x ++ f) :=
  (hx.append (FineSmallEvs.of_freeOnly 0 0 r hf)).mono
    (by omega) (by omega) (by simp)

private theorem ckx2_seqEnv_append_freeOnly {P Q : List AllocEvent → Prop}
    (hP : ∀ x f, P x → FreeOnlyEvs f → P (x ++ f))
    (hQ : ∀ x f, Q x → FreeOnlyEvs f → Q (x ++ f))
    {x f : List AllocEvent} (h : SeqEnv P Q x) (hf : FreeOnlyEvs f) :
    SeqEnv P Q (x ++ f) := by
  rcases h with hp | ⟨x1, x2, rfl, hp, hq⟩
  · exact Or.inl (hP x f hp hf)
  · rw [List.append_assoc]
    exact Or.inr ⟨x1, x2 ++ f, rfl, hp, hQ x2 f hq hf⟩

private theorem ckx2_chainStagesTightEnv_append_freeOnly {x f : List AllocEvent}
    (hx : ckx2_ChainStagesTightEnv x) (hf : FreeOnlyEvs f) :
    ckx2_ChainStagesTightEnv (x ++ f) :=
  ckx2_seqEnv_append_freeOnly
    (fun _ _ => ckx2_fineSmallEvs_append_freeOnly)
    (fun _ _ => ckx2_seqEnv_append_freeOnly
      (fun _ _ => ckx2_fineSmallEvs_append_freeOnly)
      (fun _ _ => ckx2_seqEnv_append_freeOnly
        (fun _ _ => ckx2_fineSmallEvs_append_freeOnly)
        (fun _ _ => ckx2_fineSmallEvs_append_freeOnly)))
    hx hf

private theorem ckx2_chainStagesTightEnv_sub_stage4To10 {evs : List AllocEvent}
    (h : ckx2_ChainStagesTightEnv evs) :
    ckx2_Stage4To10Env evs := by
  refine Or.inr (ckx2_seqEnv_mono (fun _ => id) (fun e4 h4 => Or.inr (ckx2_seqEnv_mono (fun _ => id)
    (fun e5 h5 => Or.inr (ckx2_seqEnv_mono (fun _ => id) (fun _ h6 => Or.inr (Or.inl h6)) h5)) h4)) h)

private theorem ckx2_chainStagesTightEnv_seq_stages8To10_sub_stage4To10 {evs : List AllocEvent}
    (h : SeqEnv ckx2_ChainStagesTightEnv ckx2_Stages8To10TightEnv evs) :
    ckx2_Stage4To10Env evs := by
  rcases h with hc | ⟨x, tail, rfl, hc, htail⟩
  · exact ckx2_chainStagesTightEnv_sub_stage4To10 hc
  · have ht7 : ckx2_Stage7To10Env tail :=
      Or.inr (Or.inr ⟨[], tail, rfl, FineSmallEvs.nil 1 8186 448, htail⟩)
    have ht6 : ckx2_Stage6To10Env tail :=
      Or.inr (Or.inr ⟨[], tail, rfl, FineSmallEvs.nil 2 1476 35, ht7⟩)
    have ht5 : ckx2_Stage5To10Env tail :=
      Or.inr (Or.inr ⟨[], tail, rfl, FineSmallEvs.nil 6 14641 896, ht6⟩)
    rcases hc with h4 | ⟨u4, r4, rfl, h4, hr4⟩
    · exact Or.inr (Or.inr ⟨x, tail, rfl, h4, ht5⟩)
    · rw [List.append_assoc]
      refine Or.inr (Or.inr ⟨u4, r4 ++ tail, rfl, h4, ?_⟩)
      rcases hr4 with h5 | ⟨u5, r5, rfl, h5, hr5⟩
      · exact Or.inr (Or.inr ⟨r4, tail, rfl, h5, ht6⟩)
      · rw [List.append_assoc]
        refine Or.inr (Or.inr ⟨u5, r5 ++ tail, rfl, h5, ?_⟩)
        rcases hr5 with h6 | ⟨u6, r6, rfl, h6, h7⟩
        · exact Or.inr (Or.inr ⟨r5, tail, rfl, h6, ht7⟩)
        · rw [List.append_assoc]
          exact Or.inr (Or.inr ⟨u6, r6 ++ tail, rfl, h6,
            Or.inr (Or.inr ⟨r6, tail, rfl, h7, htail⟩)⟩)

private theorem ckx2_sendKeyFirstEnv_sub_tight (hkdf : HkdfFn) (c1 : Chain) (msgEpoch : Epoch)
    {evs : List AllocEvent} (h : SendKeyFirstEnv hkdf c1 msgEpoch evs) :
    ChainSendKeyTightEnv evs := by
  obtain ⟨x, _, _, halloc⟩ := h
  unfold ChainSendKeyAllocEnv at halloc
  cases hsk : Chain.sendKey hkdf x.self x.epoch with
  | ok _ =>
    rw [hsk] at halloc
    exact chainSendKeyEnv_to_tight hkdf x (by unfold ChainSendKeyEnv; rw [hsk]; exact halloc)
  | error _ =>
    rw [hsk] at halloc
    subst halloc
    exact FineSmallEvs.nil 2 1476 35

private theorem ckx2_chainIntoPbForEnv_sub_tight4 {c2 : Chain} (hlinks : c2.links.length ≤ 4)
    {evs : List AllocEvent} (h : ChainIntoPbForEnv c2 evs) :
    ChainIntoPbTight4Env evs := by
  unfold ChainIntoPbForEnv at h
  split at h
  · exact FineSmallEvs.of_freeOnly 1 8186 448 h
  · obtain ⟨evs_f, hf, rfl⟩ := h
    have ha : FineSmallEvs 1 8186 448 (rustAllocEvents (c2.links.length * 112) 8) := by
      have hk : c2.links.length = 0 ∨ c2.links.length = 1 ∨
          c2.links.length = 2 ∨ c2.links.length = 3 ∨
          c2.links.length = 4 := by omega
      rcases hk with h0 | h1 | h2 | h3 | h4 <;>
        first
        | (rw [h0]; decide)
        | (rw [h1]; decide)
        | (rw [h2]; decide)
        | (rw [h3]; decide)
        | (rw [h4]; decide)
    exact (ha.append (FineSmallEvs.of_freeOnly 0 0 448 hf)).mono
      (by decide) (by decide) (by decide)

private theorem ckx2_sendKeyIntoPbEnv_sub_tight (hkdf : HkdfFn) {c1 : Chain}
    (hlinks : c1.links.length ≤ 4) (msgEpoch : Epoch) {evs : List AllocEvent}
    (h : SendKeyIntoPbEnv hkdf c1 msgEpoch evs) :
    SeqEnv ChainSendKeyTightEnv ChainIntoPbTight4Env evs := by
  unfold SendKeyIntoPbEnv at h
  split at h
  · subst h; exact Or.inl (FineSmallEvs.nil 2 1476 35)
  · cases hsk : Chain.sendKey hkdf c1 (msgEpoch - 1#64) with
    | error _ =>
      rw [hsk] at h
      exact Or.inl (FineSmallEvs.of_freeOnly 2 1476 35 h)
    | ok p =>
      rcases p with ⟨c2, _idx, _mk⟩
      rw [hsk] at h
      have hc2 : c2.links.length ≤ 4 :=
        Nat.le_trans (ckx2_chain_sendKey_links_le hsk) hlinks
      exact ckx2_seqEnv_mono (fun _ => ckx2_sendKeyFirstEnv_sub_tight hkdf c1 msgEpoch)
        (fun _ => ckx2_chainIntoPbForEnv_sub_tight4 hc2) h

private theorem ckx2_sendStepChainEnv_some_sub_tight (hkdf : HkdfFn) {c0 : Chain}
    (hlinks : c0.links.length ≤ 3) (key : Option EpochSecret) (msgEpoch : Epoch)
    {evs : List AllocEvent} (h : SendStepChainEnv hkdf (some c0) key msgEpoch evs) :
    SeqEnv ChainAddEpochTight4Env (SeqEnv ChainSendKeyTightEnv ChainIntoPbTight4Env) evs := by
  unfold SendStepChainEnv at h
  cases key with
  | none =>
    exact Or.inr ⟨[], evs, rfl, FineSmallEvs.nil 6 14641 896,
      ckx2_sendKeyIntoPbEnv_sub_tight hkdf (Nat.le_trans hlinks (by decide)) msgEpoch h⟩
  | some es =>
    dsimp only at h
    cases hadd : Chain.addEpoch hkdf c0 es with
    | error _ =>
      rw [hadd] at h
      subst h
      exact Or.inl (FineSmallEvs.nil 6 14641 896)
    | ok c1 =>
      rw [hadd] at h
      have hc1 : c1.links.length ≤ 4 := by
        have heq := ckx2_chain_addEpoch_links_eq hadd
        omega
      refine ckx2_seqEnv_mono ?_ (fun _ => ckx2_sendKeyIntoPbEnv_sub_tight hkdf hc1 msgEpoch) h
      intro e ⟨x, hx_self, _, _, hx_env⟩
      exact ckx2_chainAddEpochEnv_sub_tight4 hkdf x
        (by rw [hx_self]; exact Nat.le_trans hlinks (by decide)) hx_env

private theorem ckx2_sendChainPhaseEnv_sub_chainStagesTight {F : ShaCompress} {K : MlKem}
    {stBytes : Bytes} {pq : PqRatchetState}
    (hTop : TopStateTight F K stBytes)
    (hDec : spqrDecodeState stBytes = .ok pq)
    (key : Option EpochSecret) (msgEpoch : Epoch) {evs : List AllocEvent}
    (h : SendChainPhaseEnv (spqrHkdfWith F) pq.chain pq.versionNegotiation key msgEpoch evs) :
    ckx2_ChainStagesTightEnv evs := by
  obtain ⟨_, _, hlt31⟩ := topStateTight_to_tightValid640 hTop
  have hsize : stBytes.length < 2 ^ 64 := Nat.lt_trans hlt31 (by decide)
  obtain ⟨authKey, dir, secret, st, _sendEp, sendCtr, recvSet, vn?, ch?, chE, hw⟩ := hTop
  have hdec_eq : spqrDecodeState stBytes = .ok (pbToPqRatchetState (topPb st vn? ch?)) := by
    have hbeq := hw.htop.hbytes
    rw [hbeq] at hsize ⊢
    exact spqrDecodeState_encodeState (pbToPqRatchetState (topPb st vn? ch?)) hsize
  rw [hdec_eq] at hDec
  have hpq := Except.ok.inj hDec
  subst hpq
  have hlinks3 : chE.links.length ≤ 3 := topStateTightW_links_le_three hw
  have hfp := chain_fromPb_intoPb F authKey dir secret sendCtr recvSet chE hw.htop.hok
  have hslt : BitVec.slt 0#32 (vnOf dir authKey).minVersion = true := rfl
  unfold SendChainPhaseEnv at h
  rcases hw.htop.hch with rfl | ⟨rfl, rfl, hvnE⟩
  · simp only [pbToPqRatchetState, topPb, Option.map, hfp] at h
    exact ckx2_seqEnv_mono (fun _ hf => FineSmallEvs.of_freeOnly 6 10919 448 hf)
      (fun _ => ckx2_sendStepChainEnv_some_sub_tight (spqrHkdfWith F) hlinks3 key msgEpoch) h
  · simp only [pbToPqRatchetState, topPb, Option.map, hslt, ↓reduceIte, hvnE] at h
    exact ckx2_seqEnv_mono (fun _ hvn => chainFromEnv_to_tight none (some (vnOf dir authKey)) hvn)
      (fun _ => ckx2_sendStepChainEnv_some_sub_tight (spqrHkdfWith F) hlinks3 key msgEpoch) h

private theorem ckx2_sendFrom317fcEnvOfEnv_sub_stages8To10 {F : ShaCompress}
    {IntoPbEnv : StatesIntoPbGhost F → List AllocEvent → Prop}
    {sp : BitVec 64} {idx : BitVec 32}
    {vn : Option VersionNegotiationPB} {chainPb : Option ChainPB}
    {st1 : States spqrPolyApi (spqrAuthApi F)}
    {msg : CryptoVerification.LibsignalSpqrV1.Message spqrPolyApi}
    (hDom : ckx2_StatesIntoPbTightDom st1)
    (hIntoPb : ∀ g e, ckx2_StatesIntoPbTightDom g.st → IntoPbEnv g e → StatesIntoPbTightEnv e)
    (hLen : pqRatchetStatePBEncodedLen
      { versionNegotiation := vn, chain := chainPb, inner := some (.v1 st1.into_pb) } ≤ 286196)
    {evs : List AllocEvent}
    (h : SendFrom317fcEnvOfEnv (MessageSerializeEnv spqrPolyApi) IntoPbEnv sp idx vn chainPb st1 msg evs) :
    ckx2_Stages8To10TightEnv evs := by
  refine ckx2_seqEnv_mono (fun _ => ckx2_messageSerializeEnv_sub_tight _) (fun _ h2 => ?_) h
  refine ckx2_seqEnv_mono (fun _ hi => hIntoPb _ _ hDom hi) (fun _ h3 => ?_) h2
  refine ckx2_seqEnv_mono (fun e he => ?_) (fun _ => id) h3
  subst he
  let pq' : PqRatchetState :=
    { versionNegotiation := vn, chain := chainPb, inner := some (.v1 st1.into_pb) }
  by_cases h0 : pqRatchetStatePBEncodedLen pq' = 0
  · rw [h0]
    exact Or.inl (by decide)
  · exact pqRatchetStateEncodeToVecEnv_to_capTight hLen (Or.inr ⟨Nat.pos_of_ne_zero h0, rfl⟩)

private theorem ckx2_sendPhase3EnvOfEnv_sub_stage4To10 {F : ShaCompress} {K : MlKem}
    {IntoPbEnv : StatesIntoPbGhost F → List AllocEvent → Prop}
    {stBytes tape tape' : Bytes} {pq : PqRatchetState} {v1 : V1State}
    {st0 : States spqrPolyApi (spqrAuthApi F)} {sOut : V1Send spqrPolyApi (spqrAuthApi F)}
    (hTop : TopStateTight F K stBytes)
    (hDec : spqrDecodeState stBytes = .ok pq)
    (hV1 : pq.inner = some (.v1 v1))
    (hFromPb : States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .ok st0)
    (hSendB : st0.send K tape = .ok (sOut, tape'))
    (hIntoPb : ∀ g e, ckx2_StatesIntoPbTightDom g.st → IntoPbEnv g e → StatesIntoPbTightEnv e)
    {evs : List AllocEvent}
    (h : SendPhase3EnvOfEnv (MessageSerializeEnv spqrPolyApi) IntoPbEnv 0#64 pq sOut evs) :
    ckx2_Stage4To10Env evs := by
  unfold SendPhase3EnvOfEnv at h
  cases hCh : sendChainPhase (spqrHkdfWith F) pq.chain pq.versionNegotiation sOut.key sOut.msg.epoch with
  | ok res =>
    rcases res with ⟨idx, msgKey, chainPb⟩
    rw [hCh] at h
    dsimp only at h
    have hDom : ckx2_StatesIntoPbTightDom sOut.state :=
      ckx2_topStateTight_send_statesIntoPbTightDom hTop hDec hV1 hFromPb hSendB
    have hLen := ckx2_pqRatchetStatePBEncodedLen_send_le_286196 hTop hDec hV1 hFromPb hSendB hCh
    exact ckx2_chainStagesTightEnv_seq_stages8To10_sub_stage4To10
      (ckx2_seqEnv_mono
        (fun _ => ckx2_sendChainPhaseEnv_sub_chainStagesTight hTop hDec sOut.key sOut.msg.epoch)
        (fun _ => ckx2_sendFrom317fcEnvOfEnv_sub_stages8To10 hDom hIntoPb hLen) h)
  | error err =>
    rcases err with _e | _p
    · rw [hCh] at h
      dsimp only at h
      rcases h with h1 | ⟨x1, x2, rfl, h1, h2⟩
      · exact ckx2_chainStagesTightEnv_sub_stage4To10
          (ckx2_sendChainPhaseEnv_sub_chainStagesTight hTop hDec sOut.key sOut.msg.epoch h1)
      · exact ckx2_chainStagesTightEnv_sub_stage4To10
          (ckx2_chainStagesTightEnv_append_freeOnly
            (ckx2_sendChainPhaseEnv_sub_chainStagesTight hTop hDec sOut.key sOut.msg.epoch h1) h2)
    · rw [hCh] at h
      dsimp only at h
      exact ckx2_chainStagesTightEnv_sub_stage4To10
        (ckx2_sendChainPhaseEnv_sub_chainStagesTight hTop hDec sOut.key sOut.msg.epoch h)

/-- Inclusion of `ckx2_SpqrSendCoinsOfDecodeFromPbBytesEnv` at `ckx2_DecodeStateTightEnvOf maxOps`
and `StatesFromPbTightEnv` into `ckx2_SpqrSendTightCapEnvOf maxOps` under `SpqrStateTight640`. -/
theorem ckx2_spqrSendCoinsOfDecodeFromPb_sub_tightCapEnvOf
    {F : ShaCompress} {K : MlKem} (maxOps : Nat)
    {stBs rest : Bytes} {evs : List AllocEvent}
    (hSt : SpqrStateTight640 F K stBs)
    (hEnv : ckx2_SpqrSendCoinsOfDecodeFromPbBytesEnv F K
      (fun _ => ckx2_DecodeStateTightEnvOf maxOps)
      (fun _ => StatesFromPbTightEnv) stBs rest evs) :
    ckx2_SpqrSendTightCapEnvOf maxOps stBs rest evs := by
  unfold ckx2_SpqrSendCoinsOfDecodeFromPbBytesEnv at hEnv
  dsimp only at hEnv
  cases hDecRes : CryptoVerification.LibsignalSpqrV1.spqrDecodeState stBs with
  | error _ =>
    rw [hDecRes] at hEnv
    dsimp only at hEnv
    exact Or.inr (Or.inl hEnv)
  | ok pq =>
    have hDecResP : spqrDecodeState stBs = .ok pq := hDecRes
    rw [hDecRes] at hEnv
    dsimp only at hEnv
    cases hInner : pq.inner with
    | none =>
      rw [hInner] at hEnv
      dsimp only at hEnv
      exact Or.inr (ckx2_seqEnv_mono (fun _ => id) (fun _ hf => Or.inl hf) hEnv)
    | some innerVal =>
      rcases innerVal with ⟨v1⟩
      rw [hInner] at hEnv
      dsimp only at hEnv
      rcases hSt with hNil | hTop
      · have hDecNil : CryptoVerification.LibsignalSpqrV1.spqrDecodeState ([] : Bytes) = .ok default :=
          spqrDecodeState_encodeState (default : PqRatchetState) (by decide)
        rw [hNil, hDecNil] at hDecRes
        have hpq := Except.ok.inj hDecRes
        subst hpq
        cases hInner
      · refine Or.inr (ckx2_seqEnv_mono (fun _ => id) (fun e1 he1 => Or.inr ?_) hEnv)
        cases hFromRes : States.from_pb spqrPolyApi (spqrAuthApi F) v1 with
        | error e =>
          rcases e with _err | _pan
          · rw [hFromRes] at he1
            dsimp only at he1
            exact ckx2_seqEnv_mono (fun _ => id) (fun _ hf => Or.inl hf) he1
          · rw [hFromRes] at he1
            dsimp only at he1
            exact Or.inl he1
        | ok st_states =>
          rw [hFromRes] at he1
          dsimp only at he1
          have hRod : StatesRodataValid st_states :=
            statesRodataValid_of_bOk
              (ckx2_topStateTight_from_pb_statesIntoPbTightDom hTop hDecResP hInner hFromRes).1.1
          refine ckx2_seqEnv_mono (fun _ => id) (fun e2 he2 => Or.inr ?_) he1
          cases hSendRes : st_states.send K rest with
          | ok sOutP =>
            rcases sOutP with ⟨sOut, tape'⟩
            rw [hSendRes] at he2
            dsimp only at he2
            exact ckx2_seqEnv_mono (fun _ => ckx2_statesSendTightEnv_sub_rodataTight hRod)
              (fun _ => ckx2_sendPhase3EnvOfEnv_sub_stage4To10 hTop hDecResP hInner hFromRes
                hSendRes (fun _ _ hDom hi => ckx2_statesIntoPbExactEnv_tight hDom hi)) he2
          | error sErr =>
            rcases sErr with _sE | _sP
            · rw [hSendRes] at he2
              dsimp only at he2
              exact ckx2_seqEnv_mono (fun _ => ckx2_statesSendTightEnv_sub_rodataTight hRod)
                (fun _ hf => Or.inl hf) he2
            · rw [hSendRes] at he2
              dsimp only at he2
              rcases he2 with hs | ⟨u1, u2, rfl, hs, hh⟩
              · exact Or.inl (ckx2_statesSendTightEnv_sub_rodataTight hRod hs)
              · have hu1 := ckx2_statesSendTightEnv_eq_nil_of_send_error hSendRes hs
                subst hu1
                rw [List.nil_append]
                exact Or.inl (ckx2_headerReceived1aEnv_sub_rodataTight hh)

/-! ## `@109` Corollaries under `SpqrStateTight640` -/

theorem ckx2_spqrSendCoins109_phaseCredit_of_stateTight640 {F : ShaCompress} {K : MlKem}
    {stBs rest : Bytes} (hSt : SpqrStateTight640 F K stBs) :
    PhaseCreditSpec fineCostModel
      (ckx2_SpqrSendCoinsOfDecodeFromPbBytesEnv F K
        (fun _ => ckx2_DecodeStateTightEnv) (fun _ => StatesFromPbTightEnv) stBs rest)
      spqrSendTightDeltaCum spqrSendTightDeltaLive spqrSendTightDeltaPeak spqrSendTightMaxReq := by
  have hBase := ckx2_spqrSendTightCapEnvOf_phaseCreditSpec 109 stBs rest
  exact
    { req_align := fun evs he =>
        hBase.req_align evs (ckx2_spqrSendCoinsOfDecodeFromPb_sub_tightCapEnvOf 109 hSt he)
      credit_le := fun s0 {_} he =>
        hBase.credit_le s0 (ckx2_spqrSendCoinsOfDecodeFromPb_sub_tightCapEnvOf 109 hSt he) }

theorem ckx2_spqrSendCoins109_fineCredit_le_of_stateTight640 {F : ShaCompress} {K : MlKem}
    {stBs rest : Bytes} (hSt : SpqrStateTight640 F K stBs)
    (s0 : fineCostModel.σ) {evs : List AllocEvent}
    (hevs : ckx2_SpqrSendCoinsOfDecodeFromPbBytesEnv F K
      (fun _ => ckx2_DecodeStateTightEnv) (fun _ => StatesFromPbTightEnv) stBs rest evs) :
    fineCredit fineCostModel (fineCostModel.stepEvents evs s0) ≤
      fineCredit fineCostModel s0 + spqrSendTightFineCreditCap :=
  ckx2_spqrSendTightCapEnvOf_fineCredit_le 109 s0
    (ckx2_spqrSendCoinsOfDecodeFromPb_sub_tightCapEnvOf 109 hSt hevs)

theorem ckx2_spqrSendCoins109_evalLog_footprint_le_of_stateTight640 {F : ShaCompress} {K : MlKem}
    {stBs rest : Bytes} (hSt : SpqrStateTight640 F K stBs)
    {evs : List AllocEvent}
    (hevs : ckx2_SpqrSendCoinsOfDecodeFromPbBytesEnv F K
      (fun _ => ckx2_DecodeStateTightEnv) (fun _ => StatesFromPbTightEnv) stBs rest evs) :
    fineCostModel.footprint (fineCostModel.evalLog evs) ≤
      LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit.HasFineReallocCredit.baseFine
        (M := fineCostModel) + spqrSendTightFineCreditCap :=
  ckx2_spqrSendTightCapEnvOf_evalLog_footprint_le 109
    (ckx2_spqrSendCoinsOfDecodeFromPb_sub_tightCapEnvOf 109 hSt hevs)

theorem ckx2_spqrSendCoins109_phaseGroupSpec_of_stateTight640 {F : ShaCompress} {K : MlKem}
    {stBs rest : Bytes} (hSt : SpqrStateTight640 F K stBs) :
    PhaseGroupSpec fineCostModel
      (ckx2_SpqrSendCoinsOfDecodeFromPbBytesEnv F K
        (fun _ => ckx2_DecodeStateTightEnv) (fun _ => StatesFromPbTightEnv) stBs rest)
      (ckx2_spqrSendTightGroupSOf 109) := by
  have hBase := ckx2_spqrSendTightCapEnvOf_phaseGroupSpec fineCostModel 109 stBs rest
  exact hBase.of_imp (fun _ he => ckx2_spqrSendCoinsOfDecodeFromPb_sub_tightCapEnvOf 109 hSt he)

end LibsignalBinary.Proofs.PeakBudget.CliKitW1SpqrSendAuxR2
