/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightBranches

/-!
# Tight `fineCostModel` Credit Specification for SPQR `spqr::recv`

Composes the tight branch and codec credit specs from `SpqrRecvTightBranches` with the
`Ordering::Equal` (`V1RatchetTail`) branch to establish closed `fineCostModel` `PhaseCreditSpec`,
`fineCredit`, and `evalLog` footprint bounds for `SpqrRecvTightEnv` and `SpqrRecvC07TightEnv`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightSpec

open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.LibsignalSpqrV1
  (Bytes Chain Message MlKem PqRatchetState States V1Recv V1State VersionNegotiationPB
   spqrAuthApi spqrHkdfWith spqrPolyApi)
open CryptoVerification.LibsignalSpqrV1.Proto (spqrDecodeState)
open CryptoVerification.SpqrV1.ChainProofs
  (ChainAddEpochGhost ChainIntoPbCall ChainNewGhost ChainRecvKeyGhost)
open CryptoVerification.SpqrV1.Prost.EncodeToVec (pqRatchetStatePBEncodedLen)
open CryptoVerification.SpqrV1.States.IntoPb (StatesIntoPbGhost)
open CryptoVerification.SpqrV1.Top.InitInner (InitInnerGhost)
open CryptoVerification.SpqrV1.Top.StateSize (rawV1State)
open CryptoVerification.SpqrV1Sync.SendTotal (RecvSmallTight)
open LibsignalBinary.Heap (AllocEvent FreeOnlyEvs SeqEnv)
open LibsignalBinary.Heap.Fine (fineCostModel)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCaps (StatesDecPtsNeededBound)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (spqrStateTightCapBytes)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvPeakSpec
  (SpqrRecvGreaterCallEnv SpqrRecvLessCallEnv fineCredit fineCredit_le_of_phaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightBranches
  (C07TightCreditSpec SpqrRecvC07TightEnv SpqrRecvEqualC07TightEnv SpqrRecvEqualTightEnv
   SpqrRecvTightDomain SpqrRecvTightEnv StatesRecvTightCreditSpec V1ChainAndEncodeC07TightEnv
   V1ChainAndEncodeTightEnv c07ActualCodecSum c07ActualDecodeCum c07ActualFromPbCum
   c07ActualIntoPbCum c07TightCreditSpec_inst c07TightDecodeCum c07TightFromPbCum
   c07TightIntoPbCum c09aTightStatesRecvAnyKCum c09aTightStatesRecvCum chainFrom_links_length_le_4
   cliRecv_peerSpqrTightValid640 phaseCreditSpec_of_false_fine phaseCreditSpec_or_freeOnly_fine
   phaseCreditSpec_seq_freeOnly_left_fine phaseCreditSpec_seq_zero_left_fine
   spqrRecvC07TightEnv_nil spqrRecvOrderingGreater_phaseCreditSpec_tight
   spqrRecvOrderingGreater_phaseCreditSpec_tight_smallHist
   spqrRecvOrderingLess_phaseCreditSpec_tight spqrRecvTightCumCap
   spqrRecvTightEnv_eq_spqrRecvPartsEnv spqrRecvTightEnv_nil spqrRecvTightLiveCap
   spqrRecvTightUncondLiveCap spqrRecvTightUncondPeakCap
   v1ChainAndEncode_c07_phaseCreditSpec_tight v1ChainAndEncode_c07_phaseCreditSpec_tight_smallHist
   v1ChainAndEncode_phaseCreditSpec_tight v1ChainAndEncode_phaseCreditSpec_tight_smallHist)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightRecvKey (KeyHistorySmallOrReserved)
open LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvRaw (states_recv_raw_le_2976)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightCaps (ValidChainParamsPB ValidEncoderPts640)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightCapsAux
  (StatesPtsBoundedAt ValidPqPtsAt ValidV1PtsAt statesPtsBoundedAt_of_from_pb
   statesPtsBoundedAt_of_recv validV1PtsAt_states_into_pb)

export LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightBranches
  (C07TightCreditSpec SpqrRecvEqualTightEnv SpqrRecvTightDomain SpqrRecvTightEnv)
export LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightBranches
  (StatesRecvTightCreditSpec V1ChainAndEncodeTightEnv c07TightDecodeCum c07TightFromPbCum)
export LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightBranches
  (c07TightIntoPbCum c09aTightStatesRecvAnyKCum c09aTightStatesRecvCum chainFrom_links_length_le_4)
export LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightBranches
  (cliRecv_peerSpqrTightValid640 spqrRecvOrderingGreater_phaseCreditSpec_tight)
export LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightBranches
  (spqrRecvOrderingGreater_phaseCreditSpec_tight_smallHist
   spqrRecvOrderingLess_phaseCreditSpec_tight spqrRecvTightCumCap)
export LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightBranches
  (spqrRecvTightEnv_eq_spqrRecvPartsEnv spqrRecvTightEnv_nil spqrRecvTightLiveCap)
export LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightBranches
  (spqrRecvTightUncondLiveCap spqrRecvTightUncondPeakCap v1ChainAndEncode_phaseCreditSpec_tight
   v1ChainAndEncode_phaseCreditSpec_tight_smallHist)
export LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightBranches
  (c07ActualDecodeCum c07ActualFromPbCum c07ActualIntoPbCum c07ActualCodecSum
   c07TightCreditSpec_inst)
export LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightBranches
  (V1ChainAndEncodeC07TightEnv SpqrRecvEqualC07TightEnv SpqrRecvC07TightEnv spqrRecvC07TightEnv_nil)
export LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightBranches
  (v1ChainAndEncode_c07_phaseCreditSpec_tight v1ChainAndEncode_c07_phaseCreditSpec_tight_smallHist)

/-! ## Tight `Ordering::Equal` `PhaseCreditSpec` Bounds -/

/-- `Ordering::Equal` `PhaseCreditSpec` on `fineCostModel`, independent of `xRk.G`. -/
theorem spqrRecvOrderingEqual_phaseCreditSpec_tight
    (F : ShaCompress) (K : MlKem)
    {DecodeStateEnv : Bytes → List AllocEvent → Prop}
    {StatesFromPbEnv : V1State → List AllocEvent → Prop}
    {StatesIntoPbEnv' : StatesIntoPbGhost F → List AllocEvent → Prop}
    {StatesRecvEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    {cDec rDec cFrom rFrom cInto rInto cRecv rRecv : Nat}
    (C07 : C07TightCreditSpec F DecodeStateEnv StatesFromPbEnv StatesIntoPbEnv'
      cDec rDec cFrom rFrom cInto rInto)
    (C09a : StatesRecvTightCreditSpec F StatesRecvEnv cRecv rRecv)
    {pre_pb : PqRatchetState} {pb : V1State}
    {st0 : States spqrPolyApi (spqrAuthApi F)} {sckaMsg : Message spqrPolyApi}
    {v : V1Recv spqrPolyApi (spqrAuthApi F)}
    {xAdd : ChainAddEpochGhost} {xRk : ChainRecvKeyGhost}
    {xSInto : StatesIntoPbGhost F} {xCInto : ChainIntoPbCall}
    (hv1Pts : ValidV1PtsAt 640 pb)
    (hv1Raw : rawV1State pb ≤ 46880)
    (hAddLinks : xAdd.self.links.length ≤ 4)
    (hRkLinks : xRk.self.links.length ≤ 4)
    (hParams : ValidChainParamsPB xRk.self.params)
    (hPrev : RecvSmallTight xRk.self)
    (hOutCap : ∀ c : Chain,
      States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0 →
      States.recv K st0 sckaMsg = .ok v →
      (∃ rawKey, xRk.self.recvKey (spqrHkdfWith F) xRk.epoch xRk.index = .ok (c, rawKey)) →
      pqRatchetStatePBEncodedLen
        { versionNegotiation := none
          chain := some c.intoPb
          inner := some (.v1 v.state.into_pb) } ≤ spqrStateTightCapBytes) :
    PhaseCreditSpec fineCostModel
      (SpqrRecvEqualTightEnv F K StatesFromPbEnv StatesIntoPbEnv' StatesRecvEnv
        pre_pb pb st0 sckaMsg v xAdd xRk xSInto xCInto)
      (cFrom + cRecv + (19369995 + cInto)) 605066 621350
      (max rFrom (max rRecv (max 302480 rInto))) := by
  have hFrom := C07.fromPb_spec pb hv1Pts hv1Raw
  have hAfterFromOk : PhaseCreditSpec fineCostModel
      (fun evsAfterFrom =>
        States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0 ∧
          SeqEnv (StatesRecvEnv st0 sckaMsg)
            (fun evsAfterRecv =>
              FreeOnlyEvs evsAfterRecv ∨
                (States.recv K st0 sckaMsg = .ok v ∧
                  xSInto.st = v.state ∧
                  V1ChainAndEncodeTightEnv F StatesIntoPbEnv' pre_pb v.key
                    xAdd xRk xSInto xCInto evsAfterRecv)) evsAfterFrom)
      (cRecv + (19369995 + cInto)) 605066 621350 (max rRecv (max 302480 rInto)) := by
    by_cases hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0
    · have hpts : StatesDecPtsNeededBound st0 := StatesDecPtsNeededBound.of_from_pb hfrom
      have hpts640 : StatesPtsBoundedAt 640 st0 := statesPtsBoundedAt_of_from_pb hv1Pts hfrom
      have hst0_raw : rawV1State st0.into_pb ≤ 46880 :=
        Nat.le_trans (CryptoVerification.SpqrV1.Top.StateSize.States.from_pb_raw_le hfrom).1 hv1Raw
      have hRecv := C09a.recv_spec st0 sckaMsg hpts hpts640 hst0_raw
      have hAfterRecvOk : PhaseCreditSpec fineCostModel
          (fun evsAfterRecv =>
            States.recv K st0 sckaMsg = .ok v ∧
              xSInto.st = v.state ∧
              V1ChainAndEncodeTightEnv F StatesIntoPbEnv' pre_pb v.key
                xAdd xRk xSInto xCInto evsAfterRecv)
          (19369995 + cInto) 605066 621350 (max 302480 rInto) := by
        by_cases hrv : States.recv K st0 sckaMsg = .ok v ∧ xSInto.st = v.state
        · obtain ⟨hrecv_ok, hst_eq⟩ := hrv
          have hv_pts640 : StatesPtsBoundedAt 640 xSInto.st :=
            hst_eq ▸ statesPtsBoundedAt_of_recv (by decide : 576 ≤ 640) hpts640 hrecv_ok
          have hv_into_pts : ValidV1PtsAt 640 xSInto.st.into_pb :=
            validV1PtsAt_states_into_pb hv_pts640
          have hv_raw : rawV1State xSInto.st.into_pb ≤ 49856 := by
            rw [hst_eq]
            exact Nat.le_trans
              (states_recv_raw_le_2976 hpts.toStatesPtsNeededBound hrecv_ok)
              (Nat.le_trans (Nat.add_le_add_right hst0_raw 2976) (by decide))
          have hSInto := C07.intoPb_spec xSInto hv_pts640 hv_into_pts hv_raw
          exact (v1ChainAndEncode_phaseCreditSpec_tight F hSInto hAddLinks hRkLinks
            hParams hPrev (fun c hc => hst_eq.symm ▸ hOutCap c hfrom hrecv_ok hc)).of_imp
            fun _ h => h.2.2
        · exact phaseCreditSpec_of_false_fine _ _ _ _ fun _ h => absurd ⟨h.1, h.2.1⟩ hrv
      have hAfterRecv := phaseCreditSpec_or_freeOnly_fine hAfterRecvOk
      exact (phaseCreditSpec_seq_zero_left_fine hRecv hAfterRecv).of_imp fun _ h => h.2
    · exact phaseCreditSpec_of_false_fine _ _ _ _ fun _ h => absurd h.1 hfrom
  have hAfterFrom := phaseCreditSpec_or_freeOnly_fine hAfterFromOk
  have hAfterMd := phaseCreditSpec_or_freeOnly_fine (phaseCreditSpec_seq_zero_left_fine hFrom hAfterFrom)
  have hFull := phaseCreditSpec_seq_freeOnly_left_fine hAfterMd
  unfold SpqrRecvEqualTightEnv
  exact hFull.mono
    (by simp only [Nat.add_assoc]; exact Nat.le_refl _)
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)

/-- `Ordering::Equal` `PhaseCreditSpec` on `fineCostModel` under `KeyHistorySmallOrReserved xRk` (`Δlive = Δpeak = 294,391`).
-/
theorem spqrRecvOrderingEqual_phaseCreditSpec_tight_smallHist
    (F : ShaCompress) (K : MlKem)
    {DecodeStateEnv : Bytes → List AllocEvent → Prop}
    {StatesFromPbEnv : V1State → List AllocEvent → Prop}
    {StatesIntoPbEnv' : StatesIntoPbGhost F → List AllocEvent → Prop}
    {StatesRecvEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    {cDec rDec cFrom rFrom cInto rInto cRecv rRecv : Nat}
    (C07 : C07TightCreditSpec F DecodeStateEnv StatesFromPbEnv StatesIntoPbEnv'
      cDec rDec cFrom rFrom cInto rInto)
    (C09a : StatesRecvTightCreditSpec F StatesRecvEnv cRecv rRecv)
    {pre_pb : PqRatchetState} {pb : V1State}
    {st0 : States spqrPolyApi (spqrAuthApi F)} {sckaMsg : Message spqrPolyApi}
    {v : V1Recv spqrPolyApi (spqrAuthApi F)}
    {xAdd : ChainAddEpochGhost} {xRk : ChainRecvKeyGhost}
    {xSInto : StatesIntoPbGhost F} {xCInto : ChainIntoPbCall}
    (hv1Pts : ValidV1PtsAt 640 pb)
    (hv1Raw : rawV1State pb ≤ 46880)
    (hAddLinks : xAdd.self.links.length ≤ 4)
    (hRkLinks : xRk.self.links.length ≤ 4)
    (hParams : ValidChainParamsPB xRk.self.params)
    (hHist : KeyHistorySmallOrReserved xRk)
    (hOutCap : ∀ c : Chain,
      States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0 →
      States.recv K st0 sckaMsg = .ok v →
      (∃ rawKey, xRk.self.recvKey (spqrHkdfWith F) xRk.epoch xRk.index = .ok (c, rawKey)) →
      pqRatchetStatePBEncodedLen
        { versionNegotiation := none
          chain := some c.intoPb
          inner := some (.v1 v.state.into_pb) } ≤ spqrStateTightCapBytes) :
    PhaseCreditSpec fineCostModel
      (SpqrRecvEqualTightEnv F K StatesFromPbEnv StatesIntoPbEnv' StatesRecvEnv
        pre_pb pb st0 sckaMsg v xAdd xRk xSInto xCInto)
      (cFrom + cRecv + (19360456 + cInto)) 294391 294391
      (max rFrom (max rRecv (max 286196 rInto))) := by
  have hFrom := C07.fromPb_spec pb hv1Pts hv1Raw
  have hAfterFromOk : PhaseCreditSpec fineCostModel
      (fun evsAfterFrom =>
        States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0 ∧
          SeqEnv (StatesRecvEnv st0 sckaMsg)
            (fun evsAfterRecv =>
              FreeOnlyEvs evsAfterRecv ∨
                (States.recv K st0 sckaMsg = .ok v ∧
                  xSInto.st = v.state ∧
                  V1ChainAndEncodeTightEnv F StatesIntoPbEnv' pre_pb v.key
                    xAdd xRk xSInto xCInto evsAfterRecv)) evsAfterFrom)
      (cRecv + (19360456 + cInto)) 294391 294391 (max rRecv (max 286196 rInto)) := by
    by_cases hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0
    · have hpts : StatesDecPtsNeededBound st0 := StatesDecPtsNeededBound.of_from_pb hfrom
      have hpts640 : StatesPtsBoundedAt 640 st0 := statesPtsBoundedAt_of_from_pb hv1Pts hfrom
      have hst0_raw : rawV1State st0.into_pb ≤ 46880 :=
        Nat.le_trans (CryptoVerification.SpqrV1.Top.StateSize.States.from_pb_raw_le hfrom).1 hv1Raw
      have hRecv := C09a.recv_spec st0 sckaMsg hpts hpts640 hst0_raw
      have hAfterRecvOk : PhaseCreditSpec fineCostModel
          (fun evsAfterRecv =>
            States.recv K st0 sckaMsg = .ok v ∧
              xSInto.st = v.state ∧
              V1ChainAndEncodeTightEnv F StatesIntoPbEnv' pre_pb v.key
                xAdd xRk xSInto xCInto evsAfterRecv)
          (19360456 + cInto) 294391 294391 (max 286196 rInto) := by
        by_cases hrv : States.recv K st0 sckaMsg = .ok v ∧ xSInto.st = v.state
        · obtain ⟨hrecv_ok, hst_eq⟩ := hrv
          have hv_pts640 : StatesPtsBoundedAt 640 xSInto.st :=
            hst_eq ▸ statesPtsBoundedAt_of_recv (by decide : 576 ≤ 640) hpts640 hrecv_ok
          have hv_into_pts : ValidV1PtsAt 640 xSInto.st.into_pb :=
            validV1PtsAt_states_into_pb hv_pts640
          have hv_raw : rawV1State xSInto.st.into_pb ≤ 49856 := by
            rw [hst_eq]
            exact Nat.le_trans
              (states_recv_raw_le_2976 hpts.toStatesPtsNeededBound hrecv_ok)
              (Nat.le_trans (Nat.add_le_add_right hst0_raw 2976) (by decide))
          have hSInto := C07.intoPb_spec xSInto hv_pts640 hv_into_pts hv_raw
          exact (v1ChainAndEncode_phaseCreditSpec_tight_smallHist F hSInto hAddLinks hRkLinks
            hParams hHist (fun c hc => hst_eq.symm ▸ hOutCap c hfrom hrecv_ok hc)).of_imp
            fun _ h => h.2.2
        · exact phaseCreditSpec_of_false_fine _ _ _ _ fun _ h => absurd ⟨h.1, h.2.1⟩ hrv
      have hAfterRecv := phaseCreditSpec_or_freeOnly_fine hAfterRecvOk
      exact (phaseCreditSpec_seq_zero_left_fine hRecv hAfterRecv).of_imp fun _ h => h.2
    · exact phaseCreditSpec_of_false_fine _ _ _ _ fun _ h => absurd h.1 hfrom
  have hAfterFrom := phaseCreditSpec_or_freeOnly_fine hAfterFromOk
  have hAfterMd := phaseCreditSpec_or_freeOnly_fine (phaseCreditSpec_seq_zero_left_fine hFrom hAfterFrom)
  have hFull := phaseCreditSpec_seq_freeOnly_left_fine hAfterMd
  unfold SpqrRecvEqualTightEnv
  exact hFull.mono
    (by simp only [Nat.add_assoc]; exact Nat.le_refl _)
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)

/-! ## Parametric Tight `spqr::recv` Credit Bounds -/

private theorem validV1PtsAt640_of_validEncoderPts640 {stBytes : Bytes} {pre_pb : PqRatchetState}
    {pb : V1State} (hPts : ValidEncoderPts640 stBytes)
    (hdec : spqrDecodeState stBytes = .ok pre_pb)
    (hinner : pre_pb.inner = some (.v1 pb)) :
    ValidV1PtsAt 640 pb := by
  have hpq : ValidPqPtsAt 640 pre_pb := by
    unfold ValidEncoderPts640 SpqrTightCapsAux.ValidEncoderPtsAt at hPts
    rw [hdec] at hPts
    exact hPts
  unfold ValidPqPtsAt at hpq
  rw [hinner] at hpq
  exact hpq

/-- Parametric `PhaseCreditSpec` for `SpqrRecvTightEnv` independent of `xRk.G` (`Δlive = 605,066`, `Δpeak = 621,350`).
-/
theorem spqrRecvParts_phaseCreditSpec_tight_of_caps
    (F : ShaCompress) (K : MlKem)
    {DecodeStateEnv : Bytes → List AllocEvent → Prop}
    {StatesFromPbEnv : V1State → List AllocEvent → Prop}
    {StatesIntoPbEnv' : StatesIntoPbGhost F → List AllocEvent → Prop}
    {StatesRecvEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    {cDec rDec cFrom rFrom cInto rInto cRecv rRecv : Nat}
    (C07 : C07TightCreditSpec F DecodeStateEnv StatesFromPbEnv StatesIntoPbEnv'
      cDec rDec cFrom rFrom cInto rInto)
    (C09a : StatesRecvTightCreditSpec F StatesRecvEnv cRecv rRecv)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hDom : SpqrRecvTightDomain F K stBytes xAdd xRk) :
    PhaseCreditSpec fineCostModel
      (SpqrRecvTightEnv F K DecodeStateEnv StatesFromPbEnv StatesIntoPbEnv' StatesRecvEnv
        stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
      (cDec + (cFrom + cRecv + (19369995 + cInto)))
      605066 621350
      (max rDec (max rFrom (max rRecv (max 302480 rInto)))) := by
  have hDec := C07.decode_spec stBytes hDom.hLen hDom.hPts hDom.hChainParams
  have hAfterDecOk : PhaseCreditSpec fineCostModel
      (fun evsAfterDec =>
        spqrDecodeState stBytes = .ok pre_pb ∧
          ((pre_pb.versionNegotiation = some vn ∧ xInit.authKey = vn.authKey ∧
              SpqrRecvLessCallEnv F pre_pb vn xInit xCInto evsAfterDec) ∨
            (pre_pb.versionNegotiation = some vn ∧ pre_pb.inner = some (.v1 pb) ∧
              SpqrRecvGreaterCallEnv F pre_pb vn pb xNew xRk xCInto evsAfterDec) ∨
            (pre_pb.inner = some (.v1 pb) ∧
              SpqrRecvEqualTightEnv F K StatesFromPbEnv StatesIntoPbEnv' StatesRecvEnv
                pre_pb pb st0 sckaMsg v xAdd xRk xSInto xCInto evsAfterDec)))
      (cFrom + cRecv + (19369995 + cInto))
      605066 621350
      (max rFrom (max rRecv (max 302480 rInto))) := by
    by_cases hdec_ok : spqrDecodeState stBytes = .ok pre_pb
    · obtain ⟨hvn32, hcLinks, hv1Raw, hAddL, hRkL, hPrev, hParams, hOutG, hOutE⟩ :=
        hDom.hDecoded pre_pb hdec_ok
      have hLess : PhaseCreditSpec fineCostModel
          (fun ev => pre_pb.versionNegotiation = some vn ∧ xInit.authKey = vn.authKey ∧
            SpqrRecvLessCallEnv F pre_pb vn xInit xCInto ev)
          1348326 0 0 2112 := by
        by_cases hL : pre_pb.versionNegotiation = some vn ∧ xInit.authKey = vn.authKey
        · exact (spqrRecvOrderingLess_phaseCreditSpec_tight F hL.2 (hvn32 vn hL.1)
            hcLinks).of_imp fun _ h => h.2.2
        · exact phaseCreditSpec_of_false_fine _ _ _ _ fun _ h => absurd ⟨h.1, h.2.1⟩ hL
      have hGreater : PhaseCreditSpec fineCostModel
          (fun ev => pre_pb.versionNegotiation = some vn ∧ pre_pb.inner = some (.v1 pb) ∧
            SpqrRecvGreaterCallEnv F pre_pb vn pb xNew xRk xCInto ev)
          19352456 605066 621350 302480 := by
        by_cases hG : pre_pb.versionNegotiation = some vn ∧ pre_pb.inner = some (.v1 pb)
        · exact (spqrRecvOrderingGreater_phaseCreditSpec_tight F hParams hPrev hRkL
            (fun c hc => hOutG vn pb c hG.1 hG.2 hc)).of_imp fun _ h => h.2.2
        · exact phaseCreditSpec_of_false_fine _ _ _ _ fun _ h => absurd ⟨h.1, h.2.1⟩ hG
      have hEqual : PhaseCreditSpec fineCostModel
          (fun ev => pre_pb.inner = some (.v1 pb) ∧
            SpqrRecvEqualTightEnv F K StatesFromPbEnv StatesIntoPbEnv' StatesRecvEnv
              pre_pb pb st0 sckaMsg v xAdd xRk xSInto xCInto ev)
          (cFrom + cRecv + (19369995 + cInto)) 605066 621350
          (max rFrom (max rRecv (max 302480 rInto))) := by
        by_cases hE : pre_pb.inner = some (.v1 pb)
        · exact (spqrRecvOrderingEqual_phaseCreditSpec_tight F K C07 C09a
            (validV1PtsAt640_of_validEncoderPts640 hDom.hPts hdec_ok hE)
            (hv1Raw pb hE) hAddL hRkL hParams hPrev
            (fun c hfrom hrecv hc => hOutE pb st0 sckaMsg v c hE hfrom hrecv hc)).of_imp
            fun _ h => h.2
        · exact phaseCreditSpec_of_false_fine _ _ _ _ fun _ h => absurd h.1 hE
      have hOr := hLess.or (hGreater.or hEqual)
      have hL_le : 1348326 ≤ cFrom + cRecv + (19369995 + cInto) :=
        Nat.le_trans (by decide : 1348326 ≤ 19369995)
          (Nat.le_trans (Nat.le_add_right 19369995 cInto) (Nat.le_add_left _ _))
      have hG_le : 19352456 ≤ cFrom + cRecv + (19369995 + cInto) :=
        Nat.le_trans (by decide : 19352456 ≤ 19369995)
          (Nat.le_trans (Nat.le_add_right 19369995 cInto) (Nat.le_add_left _ _))
      have hr2112 : 2112 ≤ max rFrom (max rRecv (max 302480 rInto)) :=
        Nat.le_trans (by decide : 2112 ≤ 302480)
          (Nat.le_trans (Nat.le_max_left 302480 rInto)
            (Nat.le_trans (Nat.le_max_right rRecv _) (Nat.le_max_right rFrom _)))
      have hr302 : 302480 ≤ max rFrom (max rRecv (max 302480 rInto)) :=
        Nat.le_trans (Nat.le_max_left 302480 rInto)
          (Nat.le_trans (Nat.le_max_right rRecv _) (Nat.le_max_right rFrom _))
      exact (hOr.of_imp fun _ h => h.2).mono
        (Nat.max_le.mpr ⟨hL_le, Nat.max_le.mpr ⟨hG_le, Nat.le_refl _⟩⟩)
        (by decide) (by decide)
        (Nat.max_le.mpr ⟨hr2112, Nat.max_le.mpr ⟨hr302, Nat.le_refl _⟩⟩)
    · exact phaseCreditSpec_of_false_fine _ _ _ _ fun _ h => absurd h.1 hdec_ok
  unfold SpqrRecvTightEnv
  exact phaseCreditSpec_or_freeOnly_fine
    (phaseCreditSpec_seq_zero_left_fine hDec (phaseCreditSpec_or_freeOnly_fine hAfterDecOk))

/-- Parametric `PhaseCreditSpec` for `SpqrRecvTightEnv` under `KeyHistorySmallOrReserved xRk` (`Δlive = Δpeak = 294,391`).
-/
theorem spqrRecvParts_phaseCreditSpec_tight_smallHist_of_caps
    (F : ShaCompress) (K : MlKem)
    {DecodeStateEnv : Bytes → List AllocEvent → Prop}
    {StatesFromPbEnv : V1State → List AllocEvent → Prop}
    {StatesIntoPbEnv' : StatesIntoPbGhost F → List AllocEvent → Prop}
    {StatesRecvEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    {cDec rDec cFrom rFrom cInto rInto cRecv rRecv : Nat}
    (C07 : C07TightCreditSpec F DecodeStateEnv StatesFromPbEnv StatesIntoPbEnv'
      cDec rDec cFrom rFrom cInto rInto)
    (C09a : StatesRecvTightCreditSpec F StatesRecvEnv cRecv rRecv)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hDom : SpqrRecvTightDomain F K stBytes xAdd xRk)
    (hHist : KeyHistorySmallOrReserved xRk) :
    PhaseCreditSpec fineCostModel
      (SpqrRecvTightEnv F K DecodeStateEnv StatesFromPbEnv StatesIntoPbEnv' StatesRecvEnv
        stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
      (cDec + (cFrom + cRecv + (19360456 + cInto)))
      294391 294391
      (max rDec (max rFrom (max rRecv (max 286196 rInto)))) := by
  have hDec := C07.decode_spec stBytes hDom.hLen hDom.hPts hDom.hChainParams
  have hAfterDecOk : PhaseCreditSpec fineCostModel
      (fun evsAfterDec =>
        spqrDecodeState stBytes = .ok pre_pb ∧
          ((pre_pb.versionNegotiation = some vn ∧ xInit.authKey = vn.authKey ∧
              SpqrRecvLessCallEnv F pre_pb vn xInit xCInto evsAfterDec) ∨
            (pre_pb.versionNegotiation = some vn ∧ pre_pb.inner = some (.v1 pb) ∧
              SpqrRecvGreaterCallEnv F pre_pb vn pb xNew xRk xCInto evsAfterDec) ∨
            (pre_pb.inner = some (.v1 pb) ∧
              SpqrRecvEqualTightEnv F K StatesFromPbEnv StatesIntoPbEnv' StatesRecvEnv
                pre_pb pb st0 sckaMsg v xAdd xRk xSInto xCInto evsAfterDec)))
      (cFrom + cRecv + (19360456 + cInto))
      294391 294391
      (max rFrom (max rRecv (max 286196 rInto))) := by
    by_cases hdec_ok : spqrDecodeState stBytes = .ok pre_pb
    · obtain ⟨hvn32, hcLinks, hv1Raw, hAddL, hRkL, _, hParams, hOutG, hOutE⟩ :=
        hDom.hDecoded pre_pb hdec_ok
      have hLess : PhaseCreditSpec fineCostModel
          (fun ev => pre_pb.versionNegotiation = some vn ∧ xInit.authKey = vn.authKey ∧
            SpqrRecvLessCallEnv F pre_pb vn xInit xCInto ev)
          1348326 0 0 2112 := by
        by_cases hL : pre_pb.versionNegotiation = some vn ∧ xInit.authKey = vn.authKey
        · exact (spqrRecvOrderingLess_phaseCreditSpec_tight F hL.2 (hvn32 vn hL.1)
            hcLinks).of_imp fun _ h => h.2.2
        · exact phaseCreditSpec_of_false_fine _ _ _ _ fun _ h => absurd ⟨h.1, h.2.1⟩ hL
      have hGreater : PhaseCreditSpec fineCostModel
          (fun ev => pre_pb.versionNegotiation = some vn ∧ pre_pb.inner = some (.v1 pb) ∧
            SpqrRecvGreaterCallEnv F pre_pb vn pb xNew xRk xCInto ev)
          19342917 294391 294391 286196 := by
        by_cases hG : pre_pb.versionNegotiation = some vn ∧ pre_pb.inner = some (.v1 pb)
        · exact (spqrRecvOrderingGreater_phaseCreditSpec_tight_smallHist F hParams hHist hRkL
            (fun c hc => hOutG vn pb c hG.1 hG.2 hc)).of_imp fun _ h => h.2.2
        · exact phaseCreditSpec_of_false_fine _ _ _ _ fun _ h => absurd ⟨h.1, h.2.1⟩ hG
      have hEqual : PhaseCreditSpec fineCostModel
          (fun ev => pre_pb.inner = some (.v1 pb) ∧
            SpqrRecvEqualTightEnv F K StatesFromPbEnv StatesIntoPbEnv' StatesRecvEnv
              pre_pb pb st0 sckaMsg v xAdd xRk xSInto xCInto ev)
          (cFrom + cRecv + (19360456 + cInto)) 294391 294391
          (max rFrom (max rRecv (max 286196 rInto))) := by
        by_cases hE : pre_pb.inner = some (.v1 pb)
        · exact (spqrRecvOrderingEqual_phaseCreditSpec_tight_smallHist F K C07 C09a
            (validV1PtsAt640_of_validEncoderPts640 hDom.hPts hdec_ok hE)
            (hv1Raw pb hE) hAddL hRkL hParams hHist
            (fun c hfrom hrecv hc => hOutE pb st0 sckaMsg v c hE hfrom hrecv hc)).of_imp
            fun _ h => h.2
        · exact phaseCreditSpec_of_false_fine _ _ _ _ fun _ h => absurd h.1 hE
      have hOr := hLess.or (hGreater.or hEqual)
      have hL_le : 1348326 ≤ cFrom + cRecv + (19360456 + cInto) :=
        Nat.le_trans (by decide : 1348326 ≤ 19360456)
          (Nat.le_trans (Nat.le_add_right 19360456 cInto) (Nat.le_add_left _ _))
      have hG_le : 19342917 ≤ cFrom + cRecv + (19360456 + cInto) :=
        Nat.le_trans (by decide : 19342917 ≤ 19360456)
          (Nat.le_trans (Nat.le_add_right 19360456 cInto) (Nat.le_add_left _ _))
      have hr2112 : 2112 ≤ max rFrom (max rRecv (max 286196 rInto)) :=
        Nat.le_trans (by decide : 2112 ≤ 286196)
          (Nat.le_trans (Nat.le_max_left 286196 rInto)
            (Nat.le_trans (Nat.le_max_right rRecv _) (Nat.le_max_right rFrom _)))
      have hr286 : 286196 ≤ max rFrom (max rRecv (max 286196 rInto)) :=
        Nat.le_trans (Nat.le_max_left 286196 rInto)
          (Nat.le_trans (Nat.le_max_right rRecv _) (Nat.le_max_right rFrom _))
      exact (hOr.of_imp fun _ h => h.2).mono
        (Nat.max_le.mpr ⟨hL_le, Nat.max_le.mpr ⟨hG_le, Nat.le_refl _⟩⟩)
        (by decide) (by decide)
        (Nat.max_le.mpr ⟨hr2112, Nat.max_le.mpr ⟨hr286, Nat.le_refl _⟩⟩)
    · exact phaseCreditSpec_of_false_fine _ _ _ _ fun _ h => absurd h.1 hdec_ok
  unfold SpqrRecvTightEnv
  exact phaseCreditSpec_or_freeOnly_fine
    (phaseCreditSpec_seq_zero_left_fine hDec (phaseCreditSpec_or_freeOnly_fine hAfterDecOk))

/-- Closed `PhaseCreditSpec` (`Δcum = 23,313,687`, `Δlive = Δpeak = 294,391`) when `cDec + cFrom + cRecv + cInto ≤ 3,953,231`.
-/
theorem spqrRecvParts_phaseCreditSpec_tight
    (F : ShaCompress) (K : MlKem)
    {DecodeStateEnv : Bytes → List AllocEvent → Prop}
    {StatesFromPbEnv : V1State → List AllocEvent → Prop}
    {StatesIntoPbEnv' : StatesIntoPbGhost F → List AllocEvent → Prop}
    {StatesRecvEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    {cDec rDec cFrom rFrom cInto rInto cRecv rRecv : Nat}
    (C07 : C07TightCreditSpec F DecodeStateEnv StatesFromPbEnv StatesIntoPbEnv'
      cDec rDec cFrom rFrom cInto rInto)
    (C09a : StatesRecvTightCreditSpec F StatesRecvEnv cRecv rRecv)
    (hBudgets : cDec + cFrom + cRecv + cInto ≤ 3953231)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hDom : SpqrRecvTightDomain F K stBytes xAdd xRk)
    (hHist : KeyHistorySmallOrReserved xRk) :
    PhaseCreditSpec fineCostModel
      (SpqrRecvTightEnv F K DecodeStateEnv StatesFromPbEnv StatesIntoPbEnv' StatesRecvEnv
        stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
      23313687 294391 294391
      (max rDec (max rFrom (max rRecv (max 286196 rInto)))) := by
  have hBase := spqrRecvParts_phaseCreditSpec_tight_smallHist_of_caps
    F K C07 C09a stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hDom hHist
  have hcum : cDec + (cFrom + cRecv + (19360456 + cInto)) ≤ 23313687 := by
    have heq : cDec + (cFrom + cRecv + (19360456 + cInto)) =
        (cDec + cFrom + cRecv + cInto) + 19360456 := by
      simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    exact heq ▸ Nat.le_trans (Nat.add_le_add_right hBudgets 19360456)
      (by decide : 3953231 + 19360456 ≤ 23313687)
  exact hBase.mono hcum (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)

theorem spqrRecvParts_phaseCreditSpec_tight_card
    (F : ShaCompress) (K : MlKem)
    {DecodeStateEnv : Bytes → List AllocEvent → Prop}
    {StatesFromPbEnv : V1State → List AllocEvent → Prop}
    {StatesIntoPbEnv' : StatesIntoPbGhost F → List AllocEvent → Prop}
    {StatesRecvEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    {rDec rFrom rInto rRecv : Nat}
    (C07 : C07TightCreditSpec F DecodeStateEnv StatesFromPbEnv StatesIntoPbEnv'
      939633 rDec 155757 rFrom 164351 rInto)
    (C09a : StatesRecvTightCreditSpec F StatesRecvEnv 1647247 rRecv)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hDom : SpqrRecvTightDomain F K stBytes xAdd xRk)
    (hHist : KeyHistorySmallOrReserved xRk) :
    PhaseCreditSpec fineCostModel
      (SpqrRecvTightEnv F K DecodeStateEnv StatesFromPbEnv StatesIntoPbEnv' StatesRecvEnv
        stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
      23313687 294391 294391
      (max rDec (max rFrom (max rRecv (max 286196 rInto)))) :=
  spqrRecvParts_phaseCreditSpec_tight F K C07 C09a (by decide)
    stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hDom hHist

/-- Unconditional-`xRk.G` `PhaseCreditSpec` (`Δcum = 23,313,687`, `Δlive = 605,066`, `Δpeak = 621,350`) when `cDec + cFrom + cRecv + cInto ≤ 3,943,692`.
-/
theorem spqrRecvParts_phaseCreditSpec_tight_uncondHist
    (F : ShaCompress) (K : MlKem)
    {DecodeStateEnv : Bytes → List AllocEvent → Prop}
    {StatesFromPbEnv : V1State → List AllocEvent → Prop}
    {StatesIntoPbEnv' : StatesIntoPbGhost F → List AllocEvent → Prop}
    {StatesRecvEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    {cDec rDec cFrom rFrom cInto rInto cRecv rRecv : Nat}
    (C07 : C07TightCreditSpec F DecodeStateEnv StatesFromPbEnv StatesIntoPbEnv'
      cDec rDec cFrom rFrom cInto rInto)
    (C09a : StatesRecvTightCreditSpec F StatesRecvEnv cRecv rRecv)
    (hBudgets : cDec + cFrom + cRecv + cInto ≤ 3943692)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hDom : SpqrRecvTightDomain F K stBytes xAdd xRk) :
    PhaseCreditSpec fineCostModel
      (SpqrRecvTightEnv F K DecodeStateEnv StatesFromPbEnv StatesIntoPbEnv' StatesRecvEnv
        stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
      23313687 605066 621350
      (max rDec (max rFrom (max rRecv (max 302480 rInto)))) := by
  have hBase := spqrRecvParts_phaseCreditSpec_tight_of_caps
    F K C07 C09a stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hDom
  have hcum : cDec + (cFrom + cRecv + (19369995 + cInto)) ≤ 23313687 := by
    have heq : cDec + (cFrom + cRecv + (19369995 + cInto)) =
        (cDec + cFrom + cRecv + cInto) + 19369995 := by
      simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    exact heq ▸ Nat.le_trans (Nat.add_le_add_right hBudgets 19369995)
      (by decide : 3943692 + 19369995 ≤ 23313687)
  exact hBase.mono hcum (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)

/-- Affine `fineCredit fineCostModel` bound for `SpqrRecvTightEnv`. -/
theorem spqrRecv_fineCredit_le_tight
    (F : ShaCompress) (K : MlKem)
    {DecodeStateEnv : Bytes → List AllocEvent → Prop}
    {StatesFromPbEnv : V1State → List AllocEvent → Prop}
    {StatesIntoPbEnv' : StatesIntoPbGhost F → List AllocEvent → Prop}
    {StatesRecvEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    {cDec rDec cFrom rFrom cInto rInto cRecv rRecv : Nat}
    (C07 : C07TightCreditSpec F DecodeStateEnv StatesFromPbEnv StatesIntoPbEnv'
      cDec rDec cFrom rFrom cInto rInto)
    (C09a : StatesRecvTightCreditSpec F StatesRecvEnv cRecv rRecv)
    (hBudgets : cDec + cFrom + cRecv + cInto ≤ 3953231)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hDom : SpqrRecvTightDomain F K stBytes xAdd xRk)
    (hHist : KeyHistorySmallOrReserved xRk)
    (s0 : fineCostModel.σ) {evs : List AllocEvent}
    (hevs : SpqrRecvTightEnv F K DecodeStateEnv StatesFromPbEnv StatesIntoPbEnv' StatesRecvEnv
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs) :
    fineCredit fineCostModel (fineCostModel.stepEvents evs s0) ≤
      fineCredit fineCostModel s0 + 23313687 + 294391 :=
  fineCredit_le_of_phaseCreditSpec
    (spqrRecvParts_phaseCreditSpec_tight F K C07 C09a hBudgets
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hDom hHist)
    (Nat.le_refl 294391) s0 hevs

theorem spqrRecv_evalLog_footprint_le_tight
    (F : ShaCompress) (K : MlKem)
    {DecodeStateEnv : Bytes → List AllocEvent → Prop}
    {StatesFromPbEnv : V1State → List AllocEvent → Prop}
    {StatesIntoPbEnv' : StatesIntoPbGhost F → List AllocEvent → Prop}
    {StatesRecvEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    {cDec rDec cFrom rFrom cInto rInto cRecv rRecv : Nat}
    (C07 : C07TightCreditSpec F DecodeStateEnv StatesFromPbEnv StatesIntoPbEnv'
      cDec rDec cFrom rFrom cInto rInto)
    (C09a : StatesRecvTightCreditSpec F StatesRecvEnv cRecv rRecv)
    (hBudgets : cDec + cFrom + cRecv + cInto ≤ 3953231)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hDom : SpqrRecvTightDomain F K stBytes xAdd xRk)
    (hHist : KeyHistorySmallOrReserved xRk)
    {evs : List AllocEvent}
    (hevs : SpqrRecvTightEnv F K DecodeStateEnv StatesFromPbEnv StatesIntoPbEnv' StatesRecvEnv
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs) :
    fineCostModel.footprint (fineCostModel.evalLog evs) ≤
      HasFineReallocCredit.baseFine (M := fineCostModel) + 23313687 + 294391 :=
  (spqrRecvParts_phaseCreditSpec_tight F K C07 C09a hBudgets
    stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hDom hHist
  ).evalLog_footprint_le_of_live_le_peak (Nat.le_refl 294391) hevs

/-! ## Codec-Instantiated `spqr::recv` Tight Credit Specs -/

/-- Codec-instantiated `Ordering::Equal` `PhaseCreditSpec` independent of `xRk.G` (`Δcum = 20,105,811 + cRecv`).
-/
theorem spqrRecvOrderingEqual_c07_phaseCreditSpec_tight
    (F : ShaCompress) (K : MlKem)
    {StatesRecvEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    {cRecv rRecv : Nat}
    (C09a : StatesRecvTightCreditSpec F StatesRecvEnv cRecv rRecv)
    {pre_pb : PqRatchetState} {pb : V1State}
    {st0 : States spqrPolyApi (spqrAuthApi F)} {sckaMsg : Message spqrPolyApi}
    {v : V1Recv spqrPolyApi (spqrAuthApi F)}
    {xAdd : ChainAddEpochGhost} {xRk : ChainRecvKeyGhost}
    {xSInto : StatesIntoPbGhost F} {xCInto : ChainIntoPbCall}
    (hv1Pts : ValidV1PtsAt 640 pb)
    (hv1Raw : rawV1State pb ≤ 46880)
    (hAddLinks : xAdd.self.links.length ≤ 4)
    (hRkLinks : xRk.self.links.length ≤ 4)
    (hParams : ValidChainParamsPB xRk.self.params)
    (hPrev : RecvSmallTight xRk.self)
    (hOutCap : ∀ c : Chain,
      States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0 →
      States.recv K st0 sckaMsg = .ok v →
      (∃ rawKey, xRk.self.recvKey (spqrHkdfWith F) xRk.epoch xRk.index = .ok (c, rawKey)) →
      pqRatchetStatePBEncodedLen
        { versionNegotiation := none
          chain := some c.intoPb
          inner := some (.v1 v.state.into_pb) } ≤ spqrStateTightCapBytes) :
    PhaseCreditSpec fineCostModel
      (SpqrRecvEqualC07TightEnv F K StatesRecvEnv pre_pb pb st0 sckaMsg v xAdd xRk xSInto xCInto)
      (20105811 + cRecv) 605066 621350 (max rRecv 302480) := by
  unfold SpqrRecvEqualC07TightEnv
  exact (spqrRecvOrderingEqual_phaseCreditSpec_tight F K (c07TightCreditSpec_inst F) C09a
    hv1Pts hv1Raw hAddLinks hRkLinks hParams hPrev hOutCap).mono
    (by omega) (Nat.le_refl _) (Nat.le_refl _)
    (Nat.max_le.mpr
      ⟨Nat.le_trans (by decide : 2560 ≤ 302480) (Nat.le_max_right rRecv 302480),
       Nat.max_le.mpr
         ⟨Nat.le_max_left rRecv 302480,
          Nat.max_le.mpr
            ⟨Nat.le_max_right rRecv 302480,
             Nat.le_trans (by decide : 2400 ≤ 302480) (Nat.le_max_right rRecv 302480)⟩⟩⟩)

/-- Codec-instantiated `Ordering::Equal` `PhaseCreditSpec` under `KeyHistorySmallOrReserved xRk` (`Δcum = 20,096,272 + cRecv`, `Δlive = Δpeak = 294,391`).
-/
theorem spqrRecvOrderingEqual_c07_phaseCreditSpec_tight_smallHist
    (F : ShaCompress) (K : MlKem)
    {StatesRecvEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    {cRecv rRecv : Nat}
    (C09a : StatesRecvTightCreditSpec F StatesRecvEnv cRecv rRecv)
    {pre_pb : PqRatchetState} {pb : V1State}
    {st0 : States spqrPolyApi (spqrAuthApi F)} {sckaMsg : Message spqrPolyApi}
    {v : V1Recv spqrPolyApi (spqrAuthApi F)}
    {xAdd : ChainAddEpochGhost} {xRk : ChainRecvKeyGhost}
    {xSInto : StatesIntoPbGhost F} {xCInto : ChainIntoPbCall}
    (hv1Pts : ValidV1PtsAt 640 pb)
    (hv1Raw : rawV1State pb ≤ 46880)
    (hAddLinks : xAdd.self.links.length ≤ 4)
    (hRkLinks : xRk.self.links.length ≤ 4)
    (hParams : ValidChainParamsPB xRk.self.params)
    (hHist : KeyHistorySmallOrReserved xRk)
    (hOutCap : ∀ c : Chain,
      States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0 →
      States.recv K st0 sckaMsg = .ok v →
      (∃ rawKey, xRk.self.recvKey (spqrHkdfWith F) xRk.epoch xRk.index = .ok (c, rawKey)) →
      pqRatchetStatePBEncodedLen
        { versionNegotiation := none
          chain := some c.intoPb
          inner := some (.v1 v.state.into_pb) } ≤ spqrStateTightCapBytes) :
    PhaseCreditSpec fineCostModel
      (SpqrRecvEqualC07TightEnv F K StatesRecvEnv pre_pb pb st0 sckaMsg v xAdd xRk xSInto xCInto)
      (20096272 + cRecv) 294391 294391 (max rRecv 286196) := by
  unfold SpqrRecvEqualC07TightEnv
  exact (spqrRecvOrderingEqual_phaseCreditSpec_tight_smallHist F K (c07TightCreditSpec_inst F) C09a
    hv1Pts hv1Raw hAddLinks hRkLinks hParams hHist hOutCap).mono
    (by omega) (Nat.le_refl _) (Nat.le_refl _)
    (Nat.max_le.mpr
      ⟨Nat.le_trans (by decide : 2560 ≤ 286196) (Nat.le_max_right rRecv 286196),
       Nat.max_le.mpr
         ⟨Nat.le_max_left rRecv 286196,
          Nat.max_le.mpr
            ⟨Nat.le_max_right rRecv 286196,
             Nat.le_trans (by decide : 2400 ≤ 286196) (Nat.le_max_right rRecv 286196)⟩⟩⟩)

/-- Exact codec-instantiated `PhaseCreditSpec` for `SpqrRecvC07TightEnv` under `KeyHistorySmallOrReserved xRk` (`Δcum = 21,403,488 + cRecv`).
-/
theorem spqrRecvParts_c07_phaseCreditSpec_tight_exact
    (F : ShaCompress) (K : MlKem)
    {StatesRecvEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    {cRecv rRecv : Nat}
    (C09a : StatesRecvTightCreditSpec F StatesRecvEnv cRecv rRecv)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hDom : SpqrRecvTightDomain F K stBytes xAdd xRk)
    (hHist : KeyHistorySmallOrReserved xRk) :
    PhaseCreditSpec fineCostModel
      (SpqrRecvC07TightEnv F K StatesRecvEnv
        stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
      (21403488 + cRecv) 294391 294391 (max rRecv 286196) := by
  unfold SpqrRecvC07TightEnv
  exact (spqrRecvParts_phaseCreditSpec_tight_smallHist_of_caps
    F K (c07TightCreditSpec_inst F) C09a
    stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hDom hHist).mono
    (by omega) (Nat.le_refl _) (Nat.le_refl _)
    (Nat.max_le.mpr
      ⟨Nat.le_trans (by decide : 79236 ≤ 286196) (Nat.le_max_right rRecv 286196),
       Nat.max_le.mpr
         ⟨Nat.le_trans (by decide : 2560 ≤ 286196) (Nat.le_max_right rRecv 286196),
          Nat.max_le.mpr
            ⟨Nat.le_max_left rRecv 286196,
             Nat.max_le.mpr
               ⟨Nat.le_max_right rRecv 286196,
                Nat.le_trans (by decide : 2400 ≤ 286196) (Nat.le_max_right rRecv 286196)⟩⟩⟩⟩)

/-- Codec-instantiated `PhaseCreditSpec` (`Δcum = 23,313,687`, `Δlive = Δpeak = 294,391`) for `SpqrRecvC07TightEnv` whenever `cRecv ≤ 1,910,199`.
-/
theorem spqrRecvParts_c07_phaseCreditSpec_tight
    (F : ShaCompress) (K : MlKem)
    {StatesRecvEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    {cRecv rRecv : Nat}
    (C09a : StatesRecvTightCreditSpec F StatesRecvEnv cRecv rRecv)
    (hcRecv : cRecv ≤ 1910199)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hDom : SpqrRecvTightDomain F K stBytes xAdd xRk)
    (hHist : KeyHistorySmallOrReserved xRk) :
    PhaseCreditSpec fineCostModel
      (SpqrRecvC07TightEnv F K StatesRecvEnv
        stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
      23313687 294391 294391 (max rRecv 286196) :=
  (spqrRecvParts_c07_phaseCreditSpec_tight_exact F K C09a
    stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hDom hHist).mono
    (by omega) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)

theorem spqrRecvParts_c07_phaseCreditSpec_tight_c09a
    (F : ShaCompress) (K : MlKem)
    {StatesRecvEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    {rRecv : Nat}
    (C09a : StatesRecvTightCreditSpec F StatesRecvEnv 1647247 rRecv)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hDom : SpqrRecvTightDomain F K stBytes xAdd xRk)
    (hHist : KeyHistorySmallOrReserved xRk) :
    PhaseCreditSpec fineCostModel
      (SpqrRecvC07TightEnv F K StatesRecvEnv
        stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
      23313687 294391 294391 (max rRecv 286196) :=
  spqrRecvParts_c07_phaseCreditSpec_tight F K C09a (by decide)
    stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hDom hHist

/-- Unconditional-`xRk.G` `PhaseCreditSpec` (`Δcum = 23,313,687`, `Δlive = 605,066`, `Δpeak = 621,350`) for `SpqrRecvC07TightEnv` whenever `cRecv ≤ 1,900,660`.
-/
theorem spqrRecvParts_c07_phaseCreditSpec_tight_uncondHist
    (F : ShaCompress) (K : MlKem)
    {StatesRecvEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    {cRecv rRecv : Nat}
    (C09a : StatesRecvTightCreditSpec F StatesRecvEnv cRecv rRecv)
    (hcRecv : cRecv ≤ 1900660)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hDom : SpqrRecvTightDomain F K stBytes xAdd xRk) :
    PhaseCreditSpec fineCostModel
      (SpqrRecvC07TightEnv F K StatesRecvEnv
        stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
      23313687 605066 621350 (max rRecv 302480) := by
  unfold SpqrRecvC07TightEnv
  exact (spqrRecvParts_phaseCreditSpec_tight_uncondHist
    F K (c07TightCreditSpec_inst F) C09a (by omega)
    stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hDom).mono
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
    (Nat.max_le.mpr
      ⟨Nat.le_trans (by decide : 79236 ≤ 302480) (Nat.le_max_right rRecv 302480),
       Nat.max_le.mpr
         ⟨Nat.le_trans (by decide : 2560 ≤ 302480) (Nat.le_max_right rRecv 302480),
          Nat.max_le.mpr
            ⟨Nat.le_max_left rRecv 302480,
             Nat.max_le.mpr
               ⟨Nat.le_max_right rRecv 302480,
                Nat.le_trans (by decide : 2400 ≤ 302480) (Nat.le_max_right rRecv 302480)⟩⟩⟩⟩)

theorem spqrRecv_c07_fineCredit_le_tight
    (F : ShaCompress) (K : MlKem)
    {StatesRecvEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    {cRecv rRecv : Nat}
    (C09a : StatesRecvTightCreditSpec F StatesRecvEnv cRecv rRecv)
    (hcRecv : cRecv ≤ 1910199)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hDom : SpqrRecvTightDomain F K stBytes xAdd xRk)
    (hHist : KeyHistorySmallOrReserved xRk)
    (s0 : fineCostModel.σ) {evs : List AllocEvent}
    (hevs : SpqrRecvC07TightEnv F K StatesRecvEnv
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs) :
    fineCredit fineCostModel (fineCostModel.stepEvents evs s0) ≤
      fineCredit fineCostModel s0 + 23313687 + 294391 :=
  fineCredit_le_of_phaseCreditSpec
    (spqrRecvParts_c07_phaseCreditSpec_tight F K C09a hcRecv
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hDom hHist)
    (Nat.le_refl 294391) s0 hevs

theorem spqrRecv_c07_evalLog_footprint_le_tight
    (F : ShaCompress) (K : MlKem)
    {StatesRecvEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    {cRecv rRecv : Nat}
    (C09a : StatesRecvTightCreditSpec F StatesRecvEnv cRecv rRecv)
    (hcRecv : cRecv ≤ 1910199)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hDom : SpqrRecvTightDomain F K stBytes xAdd xRk)
    (hHist : KeyHistorySmallOrReserved xRk)
    {evs : List AllocEvent}
    (hevs : SpqrRecvC07TightEnv F K StatesRecvEnv
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs) :
    fineCostModel.footprint (fineCostModel.evalLog evs) ≤
      HasFineReallocCredit.baseFine (M := fineCostModel) + 23313687 + 294391 :=
  (spqrRecvParts_c07_phaseCreditSpec_tight F K C09a hcRecv
    stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hDom hHist
  ).evalLog_footprint_le_of_live_le_peak (Nat.le_refl 294391) hevs

end LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightSpec
