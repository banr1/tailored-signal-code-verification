/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
public import LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.W4ArchiveCancelPeak
public import LibsignalBinary.Proofs.PeakBudget.W4InitBobPeak
public import LibsignalBinary.Proofs.PeakBudget.W4InnerHelpers
public import LibsignalBinary.Proofs.PeakBudget.W4PrevDecPeak
public import LibsignalBinary.Proofs.PeakBudget.W4TryDecryptPqPeak

/-!
# W4 Inner Handshake Family Peak Live-Heap Interface

Top-level interface for the W4 inner handshake family, re-exporting `W4PrevDecPeak` (`PrevDec`
inlined `SessionStructure::decode`), `W4ArchiveCancelPeak` (`≤ 4` archive/clone cancellation),
`W4InitBobPeak` (`init_bob`), and `W4TryDecryptPqPeak` (`try_decrypt_pq`), with callee instantiations
from `SerCloneStorePeakSpec` and `SpqrCodecPeakSpec`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.W4InnerPeakSpec

open CryptoGames.LibsignalSession (SessionState ShaCompress)
open CryptoGames.LibsignalSessionApi (Session SessionRecord)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost)
open CryptoVerification.LibsignalTripleRatchet (DoReserveCall reserveCap)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open LibsignalBinary.Heap (AllocCostModel AllocEvent)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseDefsBudget (
  SerializePrev1Env encodeRecordPrev1Mem
)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (ModelHyps PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec (
  RecordSerializeCancelEnv dropClonedSessionEvents
  sessionClone_drop_cancel_phaseCredit sessionClone_phaseCredit serialize_phaseCredit
)
open LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit (
  segCloneCum segCloneLarge segCloneMaxReq
)
open LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit (
  recordSerializeCum recordSerializeMaxReq recordSerializeOutLarge recordSerializePeak
)
open LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec (initialState_phaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.W4ArchiveCancelPeak (
  ArchivedTrialIterEnv PromoteStateArchiveEnv
  phaseCredit_archivedTrialIter_cancel phaseCredit_archivedTrialLoop_le4
  phaseCredit_chainCloneFull_body_free_cancel phaseCredit_fifo_two_clones_cancel
  phaseCredit_promoteStateArchive phaseCredit_serializePrev1Env_seqFree
)
open LibsignalBinary.Proofs.PeakBudget.W4InitBobPeak (
  W4BobSessionBuildEnv W4BoundedEvs W4InitBobEnv W4InitBobSpqrEnv
  W4PqxdhAcceptEnv W4PqxdhAcceptOkEnv W4StageP2OverBobEnv
  phaseCredit_seq_freeOnly phaseCredit_w4BoundedEvs_aff phaseCredit_w4BoundedEvs_small
  phaseCredit_w4InitBob_aff phaseCredit_w4InitBob_small phaseCredit_w4PqxdhAccept_small
  phaseCredit_w4StageP2OverBob_small w4InitBobOuterCum w4PqxdhAcceptCum
)
open LibsignalBinary.Proofs.PeakBudget.W4TryDecryptPqPeak (
  W4AesDecEnv W4AesDecErrEnv W4ApplySetStateEnv W4DhStepS3Env W4TryDecryptCloneFailEnv
  phaseCredit_chainCloneEnv phaseCredit_dhCommitStep3_aff phaseCredit_dhCommitStep3_lt5_small
  phaseCredit_dhCommitStep3_small phaseCredit_fromS1GenEnv phaseCredit_fromS2GenEnv
  phaseCredit_fromS3GenEnv phaseCredit_fromS4GenEnv phaseCredit_fromS5GenEnv
  phaseCredit_fromS6GenEnv phaseCredit_fromS7GenEnv phaseCredit_fromS8GenEnv
  phaseCredit_senderChainCloneEnv phaseCredit_verifyMacWithAddresses_aff
  phaseCredit_verifyMacWithAddresses_small phaseCredit_w4AesDecErr_cancel
  phaseCredit_w4AesDec_aff phaseCredit_w4ApplySetState_small phaseCredit_w4CmkGrow104Chain_aff
  phaseCredit_w4DhStepS3_lt5_small phaseCredit_w4TryDecryptCloneFail_cancel
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (SegCloneEnv)

/-! ## 1. Re-Exports and Theorem Aliases -/

export W4InnerHelpers (OptRustAllocEnv OptRustDeallocEnv)
export W4ArchiveCancelPeak (ArchivedTrialIterEnv PromoteStateArchiveEnv chainCloneFullEvents)
export W4InitBobPeak (
  W4BoundedEvs W4PqxdhAcceptEnv W4BobSessionBuildEnv W4InitBobEnv W4StageP2OverBobEnv
)
export W4TryDecryptPqPeak (
  W4DhStepS3Env W4AesDecEnv W4AesDecErrEnv W4ApplySetStateEnv W4TryDecryptCloneFailEnv
)

abbrev phaseCredit_optRustAllocBodyDealloc_cancel :=
  @W4InnerHelpers.phaseCredit_optRustAllocBodyDealloc_cancel
abbrev phaseCredit_vecVecClone1 := @W4InnerHelpers.phaseCredit_vecVecClone1
abbrev phaseCredit_vecVecClone1_body_free_cancel :=
  @W4InnerHelpers.phaseCredit_vecVecClone1_body_free_cancel
abbrev phaseCredit_iter_zero_live_le := @W4InnerHelpers.phaseCredit_iter_zero_live_le
abbrev phaseCredit_chainCloneMk_body_free_cancel :=
  @W4InnerHelpers.phaseCredit_chainCloneMk_body_free_cancel

abbrev phaseCredit_bytesMergeProto_aff := @W4PrevDecPeak.phaseCredit_bytesMergeProto_aff
abbrev phaseCredit_bytesMerge_aff := @W4PrevDecPeak.phaseCredit_bytesMerge_aff
abbrev phaseCredit_finishGrow1 := @W4PrevDecPeak.phaseCredit_finishGrow1
abbrev phaseCredit_growOne104_small := @W4PrevDecPeak.phaseCredit_growOne104_small
abbrev phaseCredit_dropDecodeError := @W4PrevDecPeak.phaseCredit_dropDecodeError
abbrev phaseCredit_decodeVarintSlice_small := @W4PrevDecPeak.phaseCredit_decodeVarintSlice_small
abbrev phaseCredit_int32Merge_small := @W4PrevDecPeak.phaseCredit_int32Merge_small
abbrev phaseCredit_skipField_small := @W4PrevDecPeak.phaseCredit_skipField_small
abbrev phaseCredit_prevDecFields := @W4PrevDecPeak.phaseCredit_prevDecFields

abbrev phaseCredit_fifo_two_clones_cancel :=
  @W4ArchiveCancelPeak.phaseCredit_fifo_two_clones_cancel
abbrev phaseCredit_serializePrev1Env_seqFree :=
  @W4ArchiveCancelPeak.phaseCredit_serializePrev1Env_seqFree
abbrev phaseCredit_chainCloneFull_body_free_cancel :=
  @W4ArchiveCancelPeak.phaseCredit_chainCloneFull_body_free_cancel
abbrev phaseCredit_archivedTrialIter_cancel :=
  @W4ArchiveCancelPeak.phaseCredit_archivedTrialIter_cancel
abbrev phaseCredit_archivedTrialLoop_le4 :=
  @W4ArchiveCancelPeak.phaseCredit_archivedTrialLoop_le4
abbrev phaseCredit_promoteStateArchive := @W4ArchiveCancelPeak.phaseCredit_promoteStateArchive

abbrev phaseCredit_seq_freeOnly := @W4InitBobPeak.phaseCredit_seq_freeOnly
abbrev phaseCredit_w4BoundedEvs_small := @W4InitBobPeak.phaseCredit_w4BoundedEvs_small
abbrev phaseCredit_w4BoundedEvs_aff := @W4InitBobPeak.phaseCredit_w4BoundedEvs_aff
abbrev phaseCredit_w4PqxdhAccept_small := @W4InitBobPeak.phaseCredit_w4PqxdhAccept_small
abbrev phaseCredit_w4InitBob_small := @W4InitBobPeak.phaseCredit_w4InitBob_small
abbrev phaseCredit_w4InitBob_aff := @W4InitBobPeak.phaseCredit_w4InitBob_aff
abbrev phaseCredit_w4StageP2OverBob_small := @W4InitBobPeak.phaseCredit_w4StageP2OverBob_small

abbrev phaseCredit_senderChainCloneEnv := @W4TryDecryptPqPeak.phaseCredit_senderChainCloneEnv
abbrev phaseCredit_chainCloneEnv := @W4TryDecryptPqPeak.phaseCredit_chainCloneEnv
abbrev phaseCredit_dhCommitStep3_lt5_small :=
  @W4TryDecryptPqPeak.phaseCredit_dhCommitStep3_lt5_small
abbrev phaseCredit_dhCommitStep3_small := @W4TryDecryptPqPeak.phaseCredit_dhCommitStep3_small
abbrev phaseCredit_w4DhStepS3_lt5_small := @W4TryDecryptPqPeak.phaseCredit_w4DhStepS3_lt5_small
abbrev phaseCredit_w4CmkGrow104Chain_aff :=
  @W4TryDecryptPqPeak.phaseCredit_w4CmkGrow104Chain_aff
abbrev phaseCredit_verifyMacWithAddresses_aff :=
  @W4TryDecryptPqPeak.phaseCredit_verifyMacWithAddresses_aff
abbrev phaseCredit_verifyMacWithAddresses_small :=
  @W4TryDecryptPqPeak.phaseCredit_verifyMacWithAddresses_small
abbrev phaseCredit_w4AesDec_aff := @W4TryDecryptPqPeak.phaseCredit_w4AesDec_aff
abbrev phaseCredit_w4AesDecErr_cancel := @W4TryDecryptPqPeak.phaseCredit_w4AesDecErr_cancel
abbrev phaseCredit_w4ApplySetState_small :=
  @W4TryDecryptPqPeak.phaseCredit_w4ApplySetState_small
abbrev phaseCredit_fromS4GenEnv := @W4TryDecryptPqPeak.phaseCredit_fromS4GenEnv
abbrev phaseCredit_fromS1GenEnv := @W4TryDecryptPqPeak.phaseCredit_fromS1GenEnv
abbrev phaseCredit_w4TryDecryptCloneFail_cancel :=
  @W4TryDecryptPqPeak.phaseCredit_w4TryDecryptCloneFail_cancel

/-! ## 2. Callee-Instantiated Corollaries -/

/-- `SerializePrev1Env` instantiated with `SerCloneStorePeakSpec.sessionClone_phaseCredit`. -/
theorem serializePrev1Env_c04_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {G : SessionGhost} {sess : Session (List (BitVec 8))}
    {enc : List (BitVec 8)} {encCap outCap : Nat}
    (hSmall24 : 24 ≤ HasFineReallocCredit.smallMaxReq M)
    (henc : enc.length ≤ encCap)
    (hout : (encodeRecordPrev1Mem G sess enc).length ≤ outCap) :
    PhaseCreditSpec M (SerializePrev1Env G sess enc)
      (segCloneCum G sess.state + (9587 + (2 * encCap + 9539)) + (2 * outCap + 9539))
      (segCloneLarge M G sess.state + (encCap + 8195) + (outCap + 8195))
      (max (segCloneLarge M G sess.state)
        (segCloneLarge M G sess.state + (encCap + 8195) + (outCap + 8195)))
      (max (segCloneMaxReq G sess.state) (max 24 (max encCap outCap))) :=
  phaseCredit_serializePrev1Env_seqFree hM hSmall24 henc hout
    (sessionClone_phaseCredit hM G sess.state)

/-- `PromoteStateArchiveEnv` instantiated with `SerCloneStorePeakSpec.serialize_phaseCredit`. -/
theorem promoteStateArchive_c04_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (g : RecordGhost) (r : SessionRecord (List (BitVec 8)))
    {VecPushEnv : List AllocEvent → Prop} {c_push r_push : Nat}
    (hPush : PhaseCreditSpec M VecPushEnv c_push 0 0 r_push) :
    PhaseCreditSpec M (PromoteStateArchiveEnv (RecordSerializeCancelEnv g r) VecPushEnv)
      (recordSerializeCum g r + c_push)
      (recordSerializeOutLarge M g r)
      (max (recordSerializePeak M g r) (recordSerializeOutLarge M g r))
      (max (recordSerializeMaxReq g r) r_push) :=
  phaseCredit_promoteStateArchive hM (serialize_phaseCredit hM g r) hPush

/-- Failed cloned-session `try_decrypt_pq` trial instantiated with `sessionClone_drop_cancel_phaseCredit` (`Δlive = 0`).
-/
theorem tryDecryptCloneFail_c04_cancel_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    {TrialFailEnv : List AllocEvent → Prop} {c_tr p_tr r_tr : Nat}
    (hSmall192 : 192 ≤ HasFineReallocCredit.smallMaxReq M)
    (hTrialFail : PhaseCreditSpec M TrialFailEnv c_tr 0 p_tr r_tr) :
    PhaseCreditSpec M
      (W4TryDecryptCloneFailEnv (SegCloneEnv G st) TrialFailEnv
        (· = dropClonedSessionEvents G st))
      (segCloneCum G st + c_tr + 9923)
      0
      (segCloneLarge M G st + p_tr)
      (max (max (segCloneMaxReq G st) r_tr) 192) :=
  phaseCredit_w4TryDecryptCloneFail_cancel hM hSmall192 hTrialFail
    (fun hB => sessionClone_drop_cancel_phaseCredit hM G st hB)

/-- Small-regime `W4InitBobSpqrEnv` instantiated with `SpqrCodecPeakSpec.initialState_phaseCreditSpec`.
-/
theorem w4InitBob_c07_small_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (F : ShaCompress) {x_res : DoReserveCall} {hasOpk : Bool}
    (x_spqr : InitialStateGhost) {ikmCap : Nat}
    (hold : x_res.cap.toNat ≤ ikmCap)
    (hnew : reserveCap x_res.cap.toNat x_res.bs.length x_res.additional ≤ ikmCap)
    (hSmall : max ikmCap 1569 ≤ HasFineReallocCredit.smallMaxReq M) :
    let R := 4 * x_spqr.p.authKey.length + 4096
    PhaseCreditSpec M (W4InitBobSpqrEnv F x_res hasOpk x_spqr)
      (w4InitBobOuterCum ikmCap + 128 * (2 * R + 9539))
      (128 * (R + 8195))
      (128 * (R + 8195))
      (max (max ikmCap 1569) (max R 68)) := by
  dsimp only
  have h := phaseCredit_w4InitBob_small hM (hasOpk := hasOpk) hold hnew hSmall
    (initialState_phaseCreditSpec hM F x_spqr)
  exact h.mono (Nat.le_refl _) (Nat.le_refl _)
    (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩) (Nat.le_refl _)

/-- Stage P2 `Over`-path responder bound (`W4StageP2OverBobEnv`) instantiated with `serialize_phaseCredit` and `initialState_phaseCreditSpec`.
-/
theorem w4StageP2OverBob_c04_c07_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (F : ShaCompress)
    (g : RecordGhost) (r : SessionRecord (List (BitVec 8)))
    {VecPushEnv : List AllocEvent → Prop} {c_push r_push : Nat}
    {x_res : DoReserveCall} {hasOpk : Bool} (x_spqr : InitialStateGhost) {ikmCap : Nat}
    (hPush : PhaseCreditSpec M VecPushEnv c_push 0 0 r_push)
    (hold : x_res.cap.toNat ≤ ikmCap)
    (hnew : reserveCap x_res.cap.toNat x_res.bs.length x_res.additional ≤ ikmCap)
    (hSmall : max ikmCap 1569 ≤ HasFineReallocCredit.smallMaxReq M) :
    let R := 4 * x_spqr.p.authKey.length + 4096
    PhaseCreditSpec M
      (W4StageP2OverBobEnv (RecordSerializeCancelEnv g r) VecPushEnv x_res hasOpk
        (SpqrV1.Top.InitialState.DefsPlacedBudget.InitialStateEnv F x_spqr))
      (recordSerializeCum g r + c_push + w4InitBobOuterCum ikmCap + 128 * (2 * R + 9539))
      (recordSerializeOutLarge M g r + 128 * (R + 8195))
      (max (recordSerializePeak M g r)
        (recordSerializeOutLarge M g r + 128 * (R + 8195)))
      (max (max (recordSerializeMaxReq g r) r_push) (max (max ikmCap 1569) (max R 68))) := by
  dsimp only
  have h := W4InitBobPeak.phaseCredit_w4StageP2OverBob_small hM (hasOpk := hasOpk)
    (serialize_phaseCredit hM g r) hPush hold hnew hSmall
    (initialState_phaseCreditSpec hM F x_spqr)
  have hp_le :
      max (recordSerializePeak M g r)
        (recordSerializeOutLarge M g r +
          max (128 * ((4 * x_spqr.p.authKey.length + 4096) + 8195))
            (128 * ((4 * x_spqr.p.authKey.length + 4096) + 8195))) ≤
      max (recordSerializePeak M g r)
        (recordSerializeOutLarge M g r +
          128 * ((4 * x_spqr.p.authKey.length + 4096) + 8195)) :=
    Nat.max_le.mpr ⟨Nat.le_max_left _ _,
      Nat.le_trans
        (Nat.add_le_add_left (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩) _)
        (Nat.le_max_right _ _)⟩
  exact h.mono (Nat.le_refl _) (Nat.le_refl _) hp_le (Nat.le_refl _)

end LibsignalBinary.Proofs.PeakBudget.W4InnerPeakSpec
