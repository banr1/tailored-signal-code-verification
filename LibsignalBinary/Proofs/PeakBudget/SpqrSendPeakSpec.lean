/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
public import LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit
public import LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.SpqrDomainCaps
public import LibsignalBinary.Proofs.PeakBudget.SpqrSendRodataCaps
public import LibsignalBinary.Proofs.PeakBudget.SpqrSendTightBuckets
public import LibsignalBinary.Proofs.PeakBudget.SpqrSendTightHelpers
public import LibsignalBinary.Proofs.PeakBudget.SpqrTightCaps
public import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget

/-!
# Peak Live-Heap Specification for SPQR `spqr::send::<Coins>`

Establishes `PhaseCreditSpec M` and affine `fineCredit M` bounds for `spqr::send::<Coins>`
(`Block 124` / `427`) in binary call order, both in parametric cost-model form (`SpqrSendCappedEnv`,
`SpqrSendPartsBoundedEnv`) and specialized to `fineCostModel` with tight small-class codec and
`.rodata` encoder bounds (`Δcum = 4,355,111`, `Δlive = Δpeak = 294,391`, `maxReq = 286,196`,
`nonFreeCount ≤ 1,432`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.SpqrSendPeakSpec

open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.LibsignalSpqrV1
  (Bytes ChainPB PqRatchetState States V1State VersionNegotiationPB spqrAuthApi spqrHkdfWith
   spqrPolyApi)
open CryptoVerification.SpqrV1.ChainProofs
  (ChainAddEpochGhost ChainIntoPbCall ChainSendKeyGhost)
open CryptoVerification.SpqrV1.Prost.EncodeToVec (pqRatchetStatePBEncodedLen)
open CryptoVerification.SpqrV1.States.IntoPb (StatesIntoPbGhost)
open CryptoVerification.SpqrV1.Top.StateSize (rawV1State)
open LibsignalBinary.Heap (AllocCostModel AllocEvent FreeOnlyEvs SeqEnv)
open LibsignalBinary.Heap.Fine (fineCostModel)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbHelpersBudget (ChainIntoPbEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsBudget (PqRatchetStateEncodeToVecEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.DefsBudget (ChainFromEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
  (SpqrBoundedEvs nonFreeCount nonFreeCount_eq_zero_of_freeOnly)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (ModelHyps PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas (fineCostModel_modelHyps)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit
  (SpqrBoundedTotalEvs SpqrLowInterceptHyps StatesIntoPbTightEnv spqrBoundedEvs_phaseCreditSpec
   spqrBoundedTotalEvs_phaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec
  (DecodeStateLinearBoundedEnv DecodeStateTightEnv StatesFromPbTightEnv decodeStateDeltaLive
   decodeStateDeltaPeak decodeStateLinearDeltaCum decodeStateLinear_phaseCreditSpec
   decodeStateMaxReq decodeStateTightEnv_nonFreeCount_le decodeState_fine_phaseCreditSpec_tight
   statesFromPbTightEnv_nonFreeCount_le statesFromPb_fine_phaseCreditSpec_tight
   statesIntoPbTightEnv_nonFreeCount_le statesIntoPb_fine_phaseCreditSpec_tight)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCaps (ValidEncoderPts spqrStateTightCapBytes)
open LibsignalBinary.Proofs.PeakBudget.SpqrSendRodataCaps
  (PqEncodeCapTightEnv PqEncodeLargeTightEnv SpqrSendPartsTightGenEnv SpqrSendTightDomain
   SpqrSendTightDomain707 pqEncodeCapTight_fine_phaseCreditSpec pqEncodeCapTight_nonFreeCount_le
   pqEncodeLargeTight_fine_phaseCreditSpec pqEncodeLargeTight_nonFreeCount_le
   pqRatchetStateEncodeToVecEnv_to_capTight pqRatchetStateEncodeToVecEnv_to_largeTight
   spqrSendPartsTightGenEnv_nil spqrSendPartsTightGenEnv_or_pq
   spqrSendPartsTightGen_nonFreeCount_le spqrSendPartsTightGen_phaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrSendTightBuckets
  (FineSmallEvs fineSmallEvs_phaseCreditSpec smallAllocCost_le_143484_of_le_135167)
open LibsignalBinary.Proofs.PeakBudget.SpqrSendTightHelpers
  (ChainAddEpochTight4Env ChainFromTightEnv ChainIntoPbTight4Env ChainIntoPbTight79236Env
   ChainSendKeyTightEnv MessageSerializeTightEnv OptChainAddEpochEnv OptChainSendKeyEnv
   StatesSendRodataEnv StatesSendRodataTightEnv chainAddEpochTight4_fine_phaseCreditSpec
   chainFromTight_fine_phaseCreditSpec chainFrom_fine_phaseCreditSpec chainFrom_nonFreeCount_le
   chainIntoPbEnv_to_tight4 chainIntoPbEnv_to_tight79236 chainIntoPbTight4_fine_phaseCreditSpec
   chainIntoPbTight79236_fine_phaseCreditSpec chainSendKeyTight_fine_phaseCreditSpec
   messageSerializeTight_fine_phaseCreditSpec messageSerializeTight_nonFreeCount_le
   optChainAddEpoch_fine_4_phaseCreditSpec optChainAddEpoch_nonFreeCount_le
   optChainSendKey_fine_phaseCreditSpec optChainSendKey_nonFreeCount_le
   statesSendRodataTight_fine_phaseCreditSpec statesSendRodata_fine_phaseCreditSpec
   statesSendRodata_nonFreeCount_le)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightCaps
  (ValidChainParams ValidEncoderPts640 ValidEncoderPtsAt spqrEncTightPtsCap)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightCapsAux (StatesPtsBoundedAt ValidV1PtsAt)

/-! ## Envelope Monotonicity Helpers -/

theorem spqrBoundedTotalEvs_mono {a₁ a₂ r₁ r₂ t₁ t₂ m₁ m₂ : Nat} {evs : List AllocEvent}
    (ha : a₁ ≤ a₂) (hr : r₁ ≤ r₂) (ht : t₁ ≤ t₂) (hm : m₁ ≤ m₂)
    (h : SpqrBoundedTotalEvs a₁ r₁ t₁ m₁ evs) :
    SpqrBoundedTotalEvs a₂ r₂ t₂ m₂ evs :=
  ⟨Nat.le_trans h.1 ha,
   Nat.le_trans h.2.1 hr,
   Nat.le_trans h.2.2.1 ht,
   fun ev hev => ⟨Nat.le_trans (h.2.2.2 ev hev).1 hm, (h.2.2.2 ev hev).2⟩⟩

theorem decodeStateLinearBoundedEnv_mono {bs₁ bs₂ : Nat} {evs : List AllocEvent}
    (hbs : bs₁ ≤ bs₂) (h : DecodeStateLinearBoundedEnv bs₁ evs) :
    DecodeStateLinearBoundedEnv bs₂ evs :=
  spqrBoundedTotalEvs_mono
    (by omega)
    (Nat.add_le_add_right (Nat.div_le_div_right hbs) 128)
    (by omega)
    (by omega)
    h

private theorem seqEnv_mono {A₁ A₂ B₁ B₂ : List AllocEvent → Prop} {evs : List AllocEvent}
    (hA : ∀ e, A₁ e → A₂ e) (hB : ∀ e, B₁ e → B₂ e) (h : SeqEnv A₁ B₁ evs) :
    SeqEnv A₂ B₂ evs := by
  rcases h with h1 | ⟨e₁, e₂, rfl, h1, h2⟩
  · exact Or.inl (hA evs h1)
  · exact Or.inr ⟨e₁, e₂, rfl, hA e₁ h1, hB e₂ h2⟩

/-! ## Coarse `SpqrBoundedEvs 512` Envelope (`SpqrSendBoundedEnv`) -/

/-- Coarse bounded-allocation envelope for `spqr::send::<Coins>` (`≤ 512` non-free events, `maxReq = 4 * |st| + 4 * |pt| + 16,384`).
-/
def SpqrSendBoundedEnv (stBytes ptext : Bytes) (evs : List AllocEvent) : Prop :=
  SpqrBoundedEvs 512 (4 * stBytes.length + 4 * ptext.length + 16384) evs

theorem spqrSendBoundedEnv_nil (stBytes ptext : Bytes) :
    SpqrSendBoundedEnv stBytes ptext [] :=
  ⟨Nat.zero_le 512, fun _ h => nomatch h⟩

theorem spqrSendBoundedEnv_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (stBytes ptext : Bytes) :
    let R := 4 * stBytes.length + 4 * ptext.length + 16384
    PhaseCreditSpec M (SpqrSendBoundedEnv stBytes ptext)
      (512 * (2 * R + 9539)) (512 * (R + 8195)) (512 * (R + 8195)) R :=
  spqrBoundedEvs_phaseCreditSpec hM 512 (4 * stBytes.length + 4 * ptext.length + 16384)

/-! ## `spqr::send::<Coins>` Parts Envelopes and Credit Formulas -/

/-- Post-`decode_state` send-ratchet tail envelope parameterized by decoded raw-state cap `rawCap`, `ptextCap`, and point cap `K`.
-/
def SpqrSendRawTailEnv (rawCap ptextCap K : Nat) (evs : List AllocEvent) : Prop :=
  SpqrBoundedTotalEvs
    (rawCap + 16 * K + 512)
    192
    (12 * (rawCap + ptextCap) + 64 * K + 65536)
    (4 * (rawCap + ptextCap) + 32 * K + 16384)
    evs

def SpqrSendTailBoundedEnv (bsCap ptextCap K : Nat) (evs : List AllocEvent) : Prop :=
  SpqrSendRawTailEnv (201 * bsCap) ptextCap K evs

/-- Capped `spqr::send::<Coins>` envelope composing `DecodeStateLinearBoundedEnv bsCap`, `SpqrSendTailBoundedEnv`, and `FreeOnlyEvs`.
-/
def SpqrSendCappedEnv (bsCap ptextCap K : Nat) (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨
    SeqEnv (DecodeStateLinearBoundedEnv bsCap)
      (SeqEnv (SpqrSendTailBoundedEnv bsCap ptextCap K) FreeOnlyEvs) evs

/-- Input-exact `spqr::send::<Coins>` parts envelope parameterized by encoder point cap `K`. -/
def SpqrSendPartsBoundedEnv (K : Nat) (stBytes ptext : Bytes) (evs : List AllocEvent) : Prop :=
  SpqrSendCappedEnv stBytes.length ptext.length K evs

/-- Tight (`K = 640`, `ValidEncoderPts640`) `spqr::send::<Coins>` parts envelope. -/
abbrev SpqrSendTightEnv (stBytes ptext : Bytes) (evs : List AllocEvent) : Prop :=
  SpqrSendPartsBoundedEnv spqrEncTightPtsCap stBytes ptext evs

/-- General (`K = 524,288`, `ValidEncoderPts`) `spqr::send::<Coins>` parts envelope. -/
abbrev SpqrSendEnv (stBytes ptext : Bytes) (evs : List AllocEvent) : Prop :=
  SpqrSendPartsBoundedEnv 524288 stBytes ptext evs

theorem spqrSendCappedEnv_nil (bsCap ptextCap K : Nat) :
    SpqrSendCappedEnv bsCap ptextCap K [] :=
  Or.inl fun _ h => nomatch h

theorem spqrSendPartsBoundedEnv_nil (K : Nat) (stBytes ptext : Bytes) :
    SpqrSendPartsBoundedEnv K stBytes ptext [] :=
  spqrSendCappedEnv_nil stBytes.length ptext.length K

theorem spqrSendCappedEnv_mono {bs₁ bs₂ pt₁ pt₂ K₁ K₂ : Nat} {evs : List AllocEvent}
    (hbs : bs₁ ≤ bs₂) (hpt : pt₁ ≤ pt₂) (hK : K₁ ≤ K₂)
    (h : SpqrSendCappedEnv bs₁ pt₁ K₁ evs) :
    SpqrSendCappedEnv bs₂ pt₂ K₂ evs := by
  rcases h with hf | hseq
  · exact Or.inl hf
  · refine Or.inr (seqEnv_mono (fun _ => decodeStateLinearBoundedEnv_mono hbs) ?_ hseq)
    exact fun _ => seqEnv_mono
      (fun _ ht => spqrBoundedTotalEvs_mono (by omega) (Nat.le_refl 192) (by omega) (by omega) ht)
      (fun _ hf => hf)

def spqrSendRawTailDeltaCum (rawCap ptextCap K : Nat) : Nat :=
  77 * (12 * (rawCap + ptextCap) + 64 * K + 65536) +
    188 * (rawCap + 16 * K + 512) + 9539 * 192

def spqrSendRawTailDeltaLive (rawCap ptextCap K : Nat) : Nat :=
  2 * (12 * (rawCap + ptextCap) + 64 * K + 65536)

def spqrSendRawTailDeltaPeak (rawCap ptextCap K : Nat) : Nat :=
  2 * (12 * (rawCap + ptextCap) + 64 * K + 65536)

def spqrSendRawTailMaxReq (rawCap ptextCap K : Nat) : Nat :=
  4 * (rawCap + ptextCap) + 32 * K + 16384

def spqrSendDeltaCum (bsCap ptextCap K : Nat) : Nat :=
  decodeStateLinearDeltaCum bsCap + spqrSendRawTailDeltaCum (201 * bsCap) ptextCap K

def spqrSendDeltaLive (bsCap ptextCap K : Nat) : Nat :=
  decodeStateDeltaLive bsCap + spqrSendRawTailDeltaLive (201 * bsCap) ptextCap K

def spqrSendDeltaPeak (bsCap ptextCap K : Nat) : Nat :=
  max (decodeStateDeltaPeak bsCap)
    (decodeStateDeltaLive bsCap + spqrSendRawTailDeltaPeak (201 * bsCap) ptextCap K)

def spqrSendMaxReq (bsCap ptextCap K : Nat) : Nat :=
  max (decodeStateMaxReq bsCap) (spqrSendRawTailMaxReq (201 * bsCap) ptextCap K)

abbrev spqrSendCum := spqrSendDeltaCum
abbrev spqrSendLive := spqrSendDeltaLive
abbrev spqrSendPeak := spqrSendDeltaPeak

theorem spqrSendDeltaLive_le_spqrSendDeltaPeak (bsCap ptextCap K : Nat) :
    spqrSendDeltaLive bsCap ptextCap K ≤ spqrSendDeltaPeak bsCap ptextCap K :=
  Nat.le_max_right (decodeStateDeltaPeak bsCap)
    (decodeStateDeltaLive bsCap + spqrSendRawTailDeltaPeak (201 * bsCap) ptextCap K)

/-! ## Parametric `PhaseCreditSpec M` and `fineCredit M` Bounds -/

theorem spqrSendRawTail_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : SpqrLowInterceptHyps M) (rawCap ptextCap K : Nat) :
    PhaseCreditSpec M (SpqrSendRawTailEnv rawCap ptextCap K)
      (spqrSendRawTailDeltaCum rawCap ptextCap K)
      (spqrSendRawTailDeltaLive rawCap ptextCap K)
      (spqrSendRawTailDeltaPeak rawCap ptextCap K)
      (spqrSendRawTailMaxReq rawCap ptextCap K) :=
  spqrBoundedTotalEvs_phaseCreditSpec hM hLow
    (rawCap + 16 * K + 512) 192
    (12 * (rawCap + ptextCap) + 64 * K + 65536)
    (4 * (rawCap + ptextCap) + 32 * K + 16384)

theorem spqrSendCapped_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : SpqrLowInterceptHyps M) (bsCap ptextCap K : Nat) :
    PhaseCreditSpec M (SpqrSendCappedEnv bsCap ptextCap K)
      (spqrSendDeltaCum bsCap ptextCap K)
      (spqrSendDeltaLive bsCap ptextCap K)
      (spqrSendDeltaPeak bsCap ptextCap K)
      (spqrSendMaxReq bsCap ptextCap K) := by
  have hFree := PhaseCreditSpec.freeOnly_of_hyps hM
  have hDec := decodeStateLinear_phaseCreditSpec hM hLow bsCap
  have hTail : PhaseCreditSpec M (SeqEnv (SpqrSendTailBoundedEnv bsCap ptextCap K) FreeOnlyEvs)
      (spqrSendRawTailDeltaCum (201 * bsCap) ptextCap K)
      (spqrSendRawTailDeltaLive (201 * bsCap) ptextCap K)
      (spqrSendRawTailDeltaPeak (201 * bsCap) ptextCap K)
      (spqrSendRawTailMaxReq (201 * bsCap) ptextCap K) := by
    have h0 := (spqrSendRawTail_phaseCreditSpec hM hLow (201 * bsCap) ptextCap K).seq hFree
    refine h0.mono (Nat.le_of_eq (Nat.add_zero _)) (Nat.le_of_eq (Nat.add_zero _)) ?_
      (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.zero_le _⟩)
    unfold spqrSendRawTailDeltaLive spqrSendRawTailDeltaPeak
    omega
  have hActive := hDec.seq hTail
  exact (hFree.or hActive).mono
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)

theorem spqrSendPartsBounded_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : SpqrLowInterceptHyps M)
    (K : Nat) (stBytes ptext : Bytes) :
    PhaseCreditSpec M (SpqrSendPartsBoundedEnv K stBytes ptext)
      (spqrSendDeltaCum stBytes.length ptext.length K)
      (spqrSendDeltaLive stBytes.length ptext.length K)
      (spqrSendDeltaPeak stBytes.length ptext.length K)
      (spqrSendMaxReq stBytes.length ptext.length K) :=
  spqrSendCapped_phaseCreditSpec hM hLow stBytes.length ptext.length K

/-- Capped `PhaseCreditSpec M` for `SpqrSendPartsBoundedEnv K₀ stBytes ptext` when `stBytes.length ≤ bsCap`, `ptext.length ≤ ptextCap`, and `K₀ ≤ K`.
-/
theorem spqrSend_phaseCreditSpec_capped {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : SpqrLowInterceptHyps M)
    {K₀ K bsCap ptextCap : Nat} {stBytes ptext : Bytes}
    (hbs : stBytes.length ≤ bsCap) (hpt : ptext.length ≤ ptextCap) (hK : K₀ ≤ K) :
    PhaseCreditSpec M (SpqrSendPartsBoundedEnv K₀ stBytes ptext)
      (spqrSendDeltaCum bsCap ptextCap K)
      (spqrSendDeltaLive bsCap ptextCap K)
      (spqrSendDeltaPeak bsCap ptextCap K)
      (spqrSendMaxReq bsCap ptextCap K) :=
  (spqrSendCapped_phaseCreditSpec hM hLow bsCap ptextCap K).of_imp
    fun _ => spqrSendCappedEnv_mono hbs hpt hK

theorem spqrSend_phaseCreditSpec_of_ptsCap {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : SpqrLowInterceptHyps M)
    {K bsCap ptextCap : Nat} {stBytes ptext : Bytes}
    (_hPts : ValidEncoderPtsAt K stBytes)
    (hbs : stBytes.length ≤ bsCap) (hpt : ptext.length ≤ ptextCap) :
    PhaseCreditSpec M (SpqrSendPartsBoundedEnv K stBytes ptext)
      (spqrSendDeltaCum bsCap ptextCap K)
      (spqrSendDeltaLive bsCap ptextCap K)
      (spqrSendDeltaPeak bsCap ptextCap K)
      (spqrSendMaxReq bsCap ptextCap K) :=
  spqrSend_phaseCreditSpec_capped hM hLow hbs hpt (Nat.le_refl K)

theorem spqrSend_phaseCreditSpec_tight640 {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : SpqrLowInterceptHyps M)
    {bsCap ptextCap : Nat} {stBytes ptext : Bytes}
    (_hPts : ValidEncoderPts640 stBytes)
    (hbs : stBytes.length ≤ bsCap) (hpt : ptext.length ≤ ptextCap) :
    PhaseCreditSpec M (SpqrSendTightEnv stBytes ptext)
      (spqrSendDeltaCum bsCap ptextCap spqrEncTightPtsCap)
      (spqrSendDeltaLive bsCap ptextCap spqrEncTightPtsCap)
      (spqrSendDeltaPeak bsCap ptextCap spqrEncTightPtsCap)
      (spqrSendMaxReq bsCap ptextCap spqrEncTightPtsCap) :=
  spqrSend_phaseCreditSpec_capped hM hLow hbs hpt (Nat.le_refl spqrEncTightPtsCap)

/-- `PhaseCreditSpec M` for `SpqrSendEnv stBytes ptext` under `ValidEncoderPts stBytes` and `stBytes.length < 2 ^ 31`.
-/
theorem spqrSend_phaseCreditSpec_valid {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : SpqrLowInterceptHyps M)
    {stBytes ptext : Bytes}
    (_hPts : ValidEncoderPts stBytes) (hlt : stBytes.length < 2 ^ 31) :
    PhaseCreditSpec M (SpqrSendEnv stBytes ptext)
      (spqrSendDeltaCum 2147483647 ptext.length 524288)
      (spqrSendDeltaLive 2147483647 ptext.length 524288)
      (spqrSendDeltaPeak 2147483647 ptext.length 524288)
      (spqrSendMaxReq 2147483647 ptext.length 524288) :=
  spqrSend_phaseCreditSpec_capped hM hLow (by omega) (Nat.le_refl ptext.length) (Nat.le_refl 524288)

def fineCredit (M : AllocCostModel) [HasFineReallocCredit M] (s : M.σ) : Nat :=
  HasFineReallocCredit.cumSmall s +
    max (HasFineReallocCredit.liveLarge s) (HasFineReallocCredit.peakLarge s)

theorem spqrSend_fineCredit_le {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : SpqrLowInterceptHyps M)
    (K : Nat) (stBytes ptext : Bytes) (s0 : M.σ) {evs : List AllocEvent}
    (hevs : SpqrSendPartsBoundedEnv K stBytes ptext evs) :
    fineCredit M (M.stepEvents evs s0) ≤
      fineCredit M s0 +
        spqrSendDeltaCum stBytes.length ptext.length K +
        spqrSendDeltaPeak stBytes.length ptext.length K := by
  unfold fineCredit
  obtain ⟨hc, hl, hp⟩ :=
    (spqrSendPartsBounded_phaseCreditSpec hM hLow K stBytes ptext).credit_le s0 hevs
  have hlp := spqrSendDeltaLive_le_spqrSendDeltaPeak stBytes.length ptext.length K
  omega

theorem spqrSend_evalLog_footprint_le {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : SpqrLowInterceptHyps M)
    (K : Nat) (stBytes ptext : Bytes) {evs : List AllocEvent}
    (hevs : SpqrSendPartsBoundedEnv K stBytes ptext evs) :
    M.footprint (M.evalLog evs) ≤
      HasFineReallocCredit.baseFine (M := M) +
        spqrSendDeltaCum stBytes.length ptext.length K +
        spqrSendDeltaPeak stBytes.length ptext.length K :=
  (spqrSendPartsBounded_phaseCreditSpec hM hLow K stBytes ptext).evalLog_footprint_le_of_live_le_peak
    (spqrSendDeltaLive_le_spqrSendDeltaPeak stBytes.length ptext.length K) hevs

/-! ## Tight `fineCostModel` Envelopes and Codec-Instantiated Credit Specs -/

/-- Small-class (`sc < 48`, `Δlive = Δpeak = 0`) `fineCostModel` `PhaseCreditSpec` bundle for `spqr::decode_state`, `<States>::from_pb`, and `<States>::into_pb`.
-/
structure C07TightCreditSpec (F : ShaCompress)
    (DecodeStateEnv : Bytes → List AllocEvent → Prop)
    (StatesFromPbEnv : V1State → List AllocEvent → Prop)
    (StatesIntoPbEnv' : StatesIntoPbGhost F → List AllocEvent → Prop)
    (cDec rDec cFrom rFrom cInto rInto : Nat) : Prop where
  decode_spec :
    ∀ stBytes : Bytes,
      stBytes.length ≤ spqrStateTightCapBytes →
      ValidEncoderPts640 stBytes →
      ValidChainParams stBytes →
      PhaseCreditSpec fineCostModel (DecodeStateEnv stBytes) cDec 0 0 rDec
  fromPb_spec :
    ∀ pb : V1State,
      ValidV1PtsAt 640 pb →
      rawV1State pb ≤ 46880 →
      PhaseCreditSpec fineCostModel (StatesFromPbEnv pb) cFrom 0 0 rFrom
  intoPb_spec :
    ∀ xSInto : StatesIntoPbGhost F,
      StatesPtsBoundedAt 640 xSInto.st →
      ValidV1PtsAt 640 xSInto.st.into_pb →
      rawV1State xSInto.st.into_pb ≤ 49856 →
      PhaseCreditSpec fineCostModel (StatesIntoPbEnv' xSInto) cInto 0 0 rInto

/-- Instantiates `C07TightCreditSpec` at `DecodeStateTightEnv`, `StatesFromPbTightEnv`, and `StatesIntoPbTightEnv`.
-/
theorem c07TightCreditSpec_inst (F : ShaCompress) :
    C07TightCreditSpec F
      (fun _ : Bytes => DecodeStateTightEnv)
      (fun _ : V1State => StatesFromPbTightEnv)
      (fun _ : StatesIntoPbGhost F => StatesIntoPbTightEnv)
      1307216 79236 359623 2560 376193 2400 :=
  ⟨fun _ _ _ _ => decodeState_fine_phaseCreditSpec_tight,
   fun _ _ _ => statesFromPb_fine_phaseCreditSpec_tight,
   fun _ _ _ _ => statesIntoPb_fine_phaseCreditSpec_tight⟩

/-- Ghost-parameterized binary-order `spqr::send` envelope parametric in the three codec envelopes and `PqEncodeEnv`.
-/
def SpqrSendPartsTightParamEnv (F : ShaCompress)
    (DecodeStateEnv : Bytes → List AllocEvent → Prop)
    (StatesFromPbEnv : V1State → List AllocEvent → Prop)
    (StatesIntoPbEnv' : StatesIntoPbGhost F → List AllocEvent → Prop)
    (PqEncodeEnv : List AllocEvent → Prop)
    (stBytes : Bytes) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F))
    (chainPb : Option ChainPB) (vn : Option VersionNegotiationPB)
    (xAdd : ChainAddEpochGhost) (xSk : ChainSendKeyGhost)
    (xCInto : ChainIntoPbCall) (xSInto : StatesIntoPbGhost F)
    (evs : List AllocEvent) : Prop :=
  SpqrSendPartsTightGenEnv
    (DecodeStateEnv stBytes)
    (StatesFromPbEnv pb)
    (StatesSendRodataEnv F st0)
    (ChainFromEnv chainPb vn)
    (OptChainAddEpochEnv (spqrHkdfWith F) xAdd)
    (OptChainSendKeyEnv (spqrHkdfWith F) xSk)
    (ChainIntoPbEnv xCInto)
    MessageSerializeTightEnv
    (StatesIntoPbEnv' xSInto)
    PqEncodeEnv
    evs

abbrev SpqrSendPartsTightEnv (F : ShaCompress)
    (DecodeStateEnv : Bytes → List AllocEvent → Prop)
    (StatesFromPbEnv : V1State → List AllocEvent → Prop)
    (StatesIntoPbEnv' : StatesIntoPbGhost F → List AllocEvent → Prop)
    (stBytes : Bytes) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F))
    (chainPb : Option ChainPB) (vn : Option VersionNegotiationPB)
    (xAdd : ChainAddEpochGhost) (xSk : ChainSendKeyGhost)
    (xCInto : ChainIntoPbCall) (xSInto : StatesIntoPbGhost F)
    (postSt : PqRatchetState) (evs : List AllocEvent) : Prop :=
  SpqrSendPartsTightParamEnv F DecodeStateEnv StatesFromPbEnv StatesIntoPbEnv'
    (PqRatchetStateEncodeToVecEnv postSt)
    stBytes pb st0 chainPb vn xAdd xSk xCInto xSInto evs

/-- Codec-instantiated ghost-parameterized `spqr::send` envelope. -/
abbrev SpqrSendC07TightEnv (F : ShaCompress)
    (stBytes : Bytes) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F))
    (chainPb : Option ChainPB) (vn : Option VersionNegotiationPB)
    (xAdd : ChainAddEpochGhost) (xSk : ChainSendKeyGhost)
    (xCInto : ChainIntoPbCall) (xSInto : StatesIntoPbGhost F)
    (postSt : PqRatchetState) (evs : List AllocEvent) : Prop :=
  SpqrSendPartsTightEnv F
    (fun _ => DecodeStateTightEnv)
    (fun _ => StatesFromPbTightEnv)
    (fun _ => StatesIntoPbTightEnv)
    stBytes pb st0 chainPb vn xAdd xSk xCInto xSInto postSt evs

/-- Witness-free tight `spqr::send` envelope (`links ≤ 4`, `0 ≤ stLen' ≤ 286,196`). -/
def SpqrSendTightCapEnv (_stBytes _ptext : Bytes) (evs : List AllocEvent) : Prop :=
  SpqrSendPartsTightGenEnv
    DecodeStateTightEnv
    StatesFromPbTightEnv
    StatesSendRodataTightEnv
    ChainFromTightEnv
    ChainAddEpochTight4Env
    ChainSendKeyTightEnv
    ChainIntoPbTight4Env
    MessageSerializeTightEnv
    StatesIntoPbTightEnv
    (PqEncodeCapTightEnv 286196)
    evs

/-- Witness-free tight `spqr::send` envelope for large post-send states (`links ≤ 4`, `135,167 < stLen' ≤ 286,196`).
-/
def SpqrSendTightLargeEnv (_stBytes _ptext : Bytes) (evs : List AllocEvent) : Prop :=
  SpqrSendPartsTightGenEnv
    DecodeStateTightEnv
    StatesFromPbTightEnv
    StatesSendRodataTightEnv
    ChainFromTightEnv
    ChainAddEpochTight4Env
    ChainSendKeyTightEnv
    ChainIntoPbTight4Env
    MessageSerializeTightEnv
    StatesIntoPbTightEnv
    (PqEncodeLargeTightEnv 286196)
    evs

/-- Witness-free tight `spqr::send` envelope for `links ≤ 707` (`ChainIntoPbTight79236Env`) and `0 ≤ stLen' ≤ 286,196`.
-/
def SpqrSendTightCap79236Env (_stBytes _ptext : Bytes) (evs : List AllocEvent) : Prop :=
  SpqrSendPartsTightGenEnv
    DecodeStateTightEnv
    StatesFromPbTightEnv
    StatesSendRodataTightEnv
    ChainFromTightEnv
    ChainAddEpochTight4Env
    ChainSendKeyTightEnv
    ChainIntoPbTight79236Env
    MessageSerializeTightEnv
    StatesIntoPbTightEnv
    (PqEncodeCapTightEnv 286196)
    evs

def SpqrSendTightLarge79236Env (_stBytes _ptext : Bytes) (evs : List AllocEvent) : Prop :=
  SpqrSendPartsTightGenEnv
    DecodeStateTightEnv
    StatesFromPbTightEnv
    StatesSendRodataTightEnv
    ChainFromTightEnv
    ChainAddEpochTight4Env
    ChainSendKeyTightEnv
    ChainIntoPbTight79236Env
    MessageSerializeTightEnv
    StatesIntoPbTightEnv
    (PqEncodeLargeTightEnv 286196)
    evs

theorem spqrSendTightCapEnv_nil (stBytes ptext : Bytes) :
    SpqrSendTightCapEnv stBytes ptext [] :=
  spqrSendPartsTightGenEnv_nil _ _ _ _ _ _ _ _ _ _

theorem spqrSendTightLargeEnv_nil (stBytes ptext : Bytes) :
    SpqrSendTightLargeEnv stBytes ptext [] :=
  spqrSendPartsTightGenEnv_nil _ _ _ _ _ _ _ _ _ _

def spqrSendTightDeltaLive : Nat := 294391
def spqrSendTightDeltaPeak : Nat := 294391
def spqrSendTightMaxReq : Nat := 286196

/-- Tight `Δcum` (`4,211,749` bytes) at `links ≤ 4` when `135,167 < stLen' ≤ 286,196`. -/
def spqrSendTightLargeDeltaCum : Nat := 4211749

/-- Tight `Δcum` (`4,355,111` bytes) at `links ≤ 4` across all `0 ≤ stLen' ≤ 286,196`. -/
def spqrSendTightDeltaCum : Nat := 4355111

def spqrSendTightLarge79236DeltaCum : Nat := 4293797

def spqrSendTight79236DeltaCum : Nat := 4437159

/-- Single-branch `fineCredit` increment (`4,506,140` bytes) on `SpqrSendTightCapEnv` (`links ≤ 4`).
-/
def spqrSendTightFineCreditCap : Nat := 4506140

def spqrSendTight79236FineCreditCap : Nat := 4588188

private theorem sum_ten_reorder
    (cDec cFrom cInto cSend cCfrom cAdd cSk cCinto cMsg cPq cap : Nat)
    (hsum : cSend + (cCfrom + (cAdd + (cSk + (cCinto + (cMsg + cPq))))) ≤ cap) :
    cDec + (cFrom + (cSend + (cCfrom + (cAdd + (cSk + (cCinto + (cMsg + (cInto + cPq)))))))) ≤
      cDec + cFrom + cInto + cap := by
  have hcomm :
      cSend + (cCfrom + (cAdd + (cSk + (cCinto + (cMsg + (cInto + cPq)))))) =
        cInto + (cSend + (cCfrom + (cAdd + (cSk + (cCinto + (cMsg + cPq)))))) := by
    simp only [← Nat.add_assoc]
    simp only [Nat.add_assoc, Nat.add_left_comm cInto]
  rw [hcomm]
  simp only [Nat.add_assoc]
  exact Nat.add_le_add_left
    (Nat.add_le_add_left (Nat.add_le_add_left hsum cInto) cFrom) cDec

/-- Parametric `PhaseCreditSpec` for `SpqrSendPartsTightEnv` (`links ≤ 4`, `0 ≤ postSt ≤ 286,196`).
-/
theorem spqrSendParts_phaseCreditSpec_of_c07 (F : ShaCompress)
    {DecodeStateEnv : Bytes → List AllocEvent → Prop}
    {StatesFromPbEnv : V1State → List AllocEvent → Prop}
    {StatesIntoPbEnv' : StatesIntoPbGhost F → List AllocEvent → Prop}
    {cDec rDec cFrom rFrom cInto rInto : Nat}
    (C07 : C07TightCreditSpec F DecodeStateEnv StatesFromPbEnv StatesIntoPbEnv'
      cDec rDec cFrom rFrom cInto rInto)
    {stBytes : Bytes} {pb : V1State} {st0 : States spqrPolyApi (spqrAuthApi F)}
    {chainPb : Option ChainPB} {vn : Option VersionNegotiationPB}
    {xAdd : ChainAddEpochGhost} {xSk : ChainSendKeyGhost}
    {xCInto : ChainIntoPbCall} {xSInto : StatesIntoPbGhost F}
    {postSt : PqRatchetState}
    (dom : SpqrSendTightDomain F stBytes pb st0 xAdd xSInto xCInto postSt) :
    PhaseCreditSpec fineCostModel
      (SpqrSendPartsTightEnv F DecodeStateEnv StatesFromPbEnv StatesIntoPbEnv'
        stBytes pb st0 chainPb vn xAdd xSk xCInto xSInto postSt)
      (cDec + cFrom + cInto + 2312079)
      spqrSendTightDeltaLive spqrSendTightDeltaPeak
      (max rDec (max rFrom (max rInto 286196))) := by
  have hCinto : PhaseCreditSpec fineCostModel (ChainIntoPbEnv xCInto) 8186 0 0 448 :=
    chainIntoPbTight4_fine_phaseCreditSpec.of_imp fun _ => chainIntoPbEnv_to_tight4 dom.hCIntoLinks
  have hPq : PhaseCreditSpec fineCostModel (PqRatchetStateEncodeToVecEnv postSt)
      143484 spqrSendTightDeltaLive spqrSendTightDeltaPeak 286196 :=
    (pqEncodeCapTight_fine_phaseCreditSpec 286196).of_imp
      fun _ => pqRatchetStateEncodeToVecEnv_to_capTight dom.hPostLen
  have hgen := spqrSendPartsTightGen_phaseCreditSpec
    (C07.decode_spec stBytes dom.hLen dom.hPts dom.hChainParams)
    (C07.fromPb_spec pb dom.hV1Pts dom.hV1Raw)
    (statesSendRodata_fine_phaseCreditSpec F dom.hRodata)
    (chainFrom_fine_phaseCreditSpec chainPb vn)
    (optChainAddEpoch_fine_4_phaseCreditSpec (spqrHkdfWith F) xAdd dom.hAddLinks)
    (optChainSendKey_fine_phaseCreditSpec (spqrHkdfWith F) xSk)
    hCinto
    messageSerializeTight_fine_phaseCreditSpec
    (C07.intoPb_spec xSInto dom.hSIntoPts dom.hSIntoV1Pts dom.hSIntoRaw)
    hPq
    (Nat.le_refl spqrSendTightDeltaLive)
  refine hgen.mono
    (sum_ten_reorder cDec cFrom cInto 2124238 10919 14641 1476 8186 9135 143484 2312079
      (by decide))
    (Nat.le_refl _) (Nat.le_refl _) ?_
  have hr286 : ∀ {r : Nat}, r ≤ 286196 →
      r ≤ max rDec (max rFrom (max rInto 286196)) := fun hr =>
    Nat.le_trans hr (Nat.le_trans (Nat.le_max_right rInto 286196)
      (Nat.le_trans (Nat.le_max_right rFrom _) (Nat.le_max_right rDec _)))
  exact Nat.max_le.mpr ⟨Nat.le_max_left _ _,
    Nat.max_le.mpr ⟨Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _),
      Nat.max_le.mpr ⟨hr286 (by decide), Nat.max_le.mpr ⟨hr286 (by decide),
        Nat.max_le.mpr ⟨hr286 (by decide), Nat.max_le.mpr ⟨hr286 (by decide),
          Nat.max_le.mpr ⟨hr286 (by decide), Nat.max_le.mpr ⟨hr286 (by decide),
            Nat.max_le.mpr ⟨Nat.le_trans (Nat.le_max_left _ _)
              (Nat.le_trans (Nat.le_max_right rFrom _) (Nat.le_max_right rDec _)),
              hr286 (Nat.le_refl 286196)⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem spqrSendParts_largeEncode_phaseCreditSpec_of_c07 (F : ShaCompress)
    {DecodeStateEnv : Bytes → List AllocEvent → Prop}
    {StatesFromPbEnv : V1State → List AllocEvent → Prop}
    {StatesIntoPbEnv' : StatesIntoPbGhost F → List AllocEvent → Prop}
    {cDec rDec cFrom rFrom cInto rInto : Nat}
    (C07 : C07TightCreditSpec F DecodeStateEnv StatesFromPbEnv StatesIntoPbEnv'
      cDec rDec cFrom rFrom cInto rInto)
    {stBytes : Bytes} {pb : V1State} {st0 : States spqrPolyApi (spqrAuthApi F)}
    {chainPb : Option ChainPB} {vn : Option VersionNegotiationPB}
    {xAdd : ChainAddEpochGhost} {xSk : ChainSendKeyGhost}
    {xCInto : ChainIntoPbCall} {xSInto : StatesIntoPbGhost F}
    {postSt : PqRatchetState}
    (dom : SpqrSendTightDomain F stBytes pb st0 xAdd xSInto xCInto postSt)
    (hLarge : 135167 < pqRatchetStatePBEncodedLen postSt) :
    PhaseCreditSpec fineCostModel
      (SpqrSendPartsTightEnv F DecodeStateEnv StatesFromPbEnv StatesIntoPbEnv'
        stBytes pb st0 chainPb vn xAdd xSk xCInto xSInto postSt)
      (cDec + cFrom + cInto + 2168717)
      spqrSendTightDeltaLive spqrSendTightDeltaPeak
      (max rDec (max rFrom (max rInto 286196))) := by
  have hCinto : PhaseCreditSpec fineCostModel (ChainIntoPbEnv xCInto) 8186 0 0 448 :=
    chainIntoPbTight4_fine_phaseCreditSpec.of_imp fun _ => chainIntoPbEnv_to_tight4 dom.hCIntoLinks
  have hPq : PhaseCreditSpec fineCostModel (PqRatchetStateEncodeToVecEnv postSt)
      122 spqrSendTightDeltaLive spqrSendTightDeltaPeak 286196 :=
    (pqEncodeLargeTight_fine_phaseCreditSpec 286196).of_imp
      fun _ => pqRatchetStateEncodeToVecEnv_to_largeTight hLarge dom.hPostLen
  have hgen := spqrSendPartsTightGen_phaseCreditSpec
    (C07.decode_spec stBytes dom.hLen dom.hPts dom.hChainParams)
    (C07.fromPb_spec pb dom.hV1Pts dom.hV1Raw)
    (statesSendRodata_fine_phaseCreditSpec F dom.hRodata)
    (chainFrom_fine_phaseCreditSpec chainPb vn)
    (optChainAddEpoch_fine_4_phaseCreditSpec (spqrHkdfWith F) xAdd dom.hAddLinks)
    (optChainSendKey_fine_phaseCreditSpec (spqrHkdfWith F) xSk)
    hCinto
    messageSerializeTight_fine_phaseCreditSpec
    (C07.intoPb_spec xSInto dom.hSIntoPts dom.hSIntoV1Pts dom.hSIntoRaw)
    hPq
    (Nat.le_refl spqrSendTightDeltaLive)
  refine hgen.mono
    (sum_ten_reorder cDec cFrom cInto 2124238 10919 14641 1476 8186 9135 122 2168717
      (by decide))
    (Nat.le_refl _) (Nat.le_refl _) ?_
  have hr286 : ∀ {r : Nat}, r ≤ 286196 →
      r ≤ max rDec (max rFrom (max rInto 286196)) := fun hr =>
    Nat.le_trans hr (Nat.le_trans (Nat.le_max_right rInto 286196)
      (Nat.le_trans (Nat.le_max_right rFrom _) (Nat.le_max_right rDec _)))
  exact Nat.max_le.mpr ⟨Nat.le_max_left _ _,
    Nat.max_le.mpr ⟨Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _),
      Nat.max_le.mpr ⟨hr286 (by decide), Nat.max_le.mpr ⟨hr286 (by decide),
        Nat.max_le.mpr ⟨hr286 (by decide), Nat.max_le.mpr ⟨hr286 (by decide),
          Nat.max_le.mpr ⟨hr286 (by decide), Nat.max_le.mpr ⟨hr286 (by decide),
            Nat.max_le.mpr ⟨Nat.le_trans (Nat.le_max_left _ _)
              (Nat.le_trans (Nat.le_max_right rFrom _) (Nat.le_max_right rDec _)),
              hr286 (Nat.le_refl 286196)⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- Closed `PhaseCreditSpec` for `SpqrSendC07TightEnv` (`Δcum = 4,355,111`, `Δlive = Δpeak = 294,391`, `maxReq = 286,196`).
-/
theorem spqrSendParts_c07_phaseCreditSpec_tight (F : ShaCompress)
    {stBytes : Bytes} {pb : V1State} {st0 : States spqrPolyApi (spqrAuthApi F)}
    {chainPb : Option ChainPB} {vn : Option VersionNegotiationPB}
    {xAdd : ChainAddEpochGhost} {xSk : ChainSendKeyGhost}
    {xCInto : ChainIntoPbCall} {xSInto : StatesIntoPbGhost F}
    {postSt : PqRatchetState}
    (dom : SpqrSendTightDomain F stBytes pb st0 xAdd xSInto xCInto postSt) :
    PhaseCreditSpec fineCostModel
      (SpqrSendC07TightEnv F stBytes pb st0 chainPb vn xAdd xSk xCInto xSInto postSt)
      spqrSendTightDeltaCum spqrSendTightDeltaLive spqrSendTightDeltaPeak spqrSendTightMaxReq :=
  (spqrSendParts_phaseCreditSpec_of_c07 F (c07TightCreditSpec_inst F) dom).mono
    (by decide) (Nat.le_refl _) (Nat.le_refl _) (by decide)

theorem spqrSendParts_c07_phaseCreditSpec_tight_largeEncode (F : ShaCompress)
    {stBytes : Bytes} {pb : V1State} {st0 : States spqrPolyApi (spqrAuthApi F)}
    {chainPb : Option ChainPB} {vn : Option VersionNegotiationPB}
    {xAdd : ChainAddEpochGhost} {xSk : ChainSendKeyGhost}
    {xCInto : ChainIntoPbCall} {xSInto : StatesIntoPbGhost F}
    {postSt : PqRatchetState}
    (dom : SpqrSendTightDomain F stBytes pb st0 xAdd xSInto xCInto postSt)
    (hLarge : 135167 < pqRatchetStatePBEncodedLen postSt) :
    PhaseCreditSpec fineCostModel
      (SpqrSendC07TightEnv F stBytes pb st0 chainPb vn xAdd xSk xCInto xSInto postSt)
      spqrSendTightLargeDeltaCum spqrSendTightDeltaLive spqrSendTightDeltaPeak
      spqrSendTightMaxReq :=
  (spqrSendParts_largeEncode_phaseCreditSpec_of_c07 F (c07TightCreditSpec_inst F) dom hLarge).mono
    (by decide) (Nat.le_refl _) (Nat.le_refl _) (by decide)

theorem spqrSendParts_c07_nonFreeCount_le (F : ShaCompress)
    {stBytes : Bytes} {pb : V1State} {st0 : States spqrPolyApi (spqrAuthApi F)}
    {chainPb : Option ChainPB} {vn : Option VersionNegotiationPB}
    {xAdd : ChainAddEpochGhost} {xSk : ChainSendKeyGhost}
    {xCInto : ChainIntoPbCall} {xSInto : StatesIntoPbGhost F}
    {postSt : PqRatchetState} {evs : List AllocEvent}
    (dom : SpqrSendTightDomain707 F stBytes pb st0 xAdd xSInto xCInto postSt)
    (h : SpqrSendC07TightEnv F stBytes pb st0 chainPb vn xAdd xSk xCInto xSInto postSt evs) :
    nonFreeCount evs ≤ 1432 := by
  have hc := spqrSendPartsTightGen_nonFreeCount_le
    (fun _ hd => decodeStateTightEnv_nonFreeCount_le hd)
    (fun _ hf => statesFromPbTightEnv_nonFreeCount_le hf)
    (fun _ hs => statesSendRodata_nonFreeCount_le F dom.hRodata hs)
    (fun _ hcf => chainFrom_nonFreeCount_le chainPb vn hcf)
    (fun _ ha => optChainAddEpoch_nonFreeCount_le (spqrHkdfWith F) xAdd ha)
    (fun _ hsk => optChainSendKey_nonFreeCount_le (spqrHkdfWith F) xSk hsk)
    (fun _ hci => (chainIntoPbEnv_to_tight79236 dom.hCIntoLinks hci).1)
    (fun _ hm => messageSerializeTight_nonFreeCount_le hm)
    (fun _ hsi => statesIntoPbTightEnv_nonFreeCount_le hsi)
    (fun _ hpq => pqEncodeCapTight_nonFreeCount_le
      (pqRatchetStateEncodeToVecEnv_to_capTight dom.hPostLen hpq))
    h
  exact Nat.le_trans hc (by decide)

/-- Witness-free tight `PhaseCreditSpec` for `spqr::send` under `ValidEncoderPts640` and `ValidChainParams` (`Δcum = 4,355,111`, `Δlive = Δpeak = 294,391`).
-/
theorem spqrSend_phaseCreditSpec_tight
    {stBytes ptext : Bytes}
    (_hPts : ValidEncoderPts640 stBytes)
    (_hChain : ValidChainParams stBytes) :
    PhaseCreditSpec fineCostModel (SpqrSendTightCapEnv stBytes ptext)
      spqrSendTightDeltaCum spqrSendTightDeltaLive spqrSendTightDeltaPeak spqrSendTightMaxReq :=
  (spqrSendPartsTightGen_phaseCreditSpec
    decodeState_fine_phaseCreditSpec_tight
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

theorem spqrSend_phaseCreditSpec_tight_largeEncode
    {stBytes ptext : Bytes}
    (_hPts : ValidEncoderPts640 stBytes)
    (_hChain : ValidChainParams stBytes) :
    PhaseCreditSpec fineCostModel (SpqrSendTightLargeEnv stBytes ptext)
      spqrSendTightLargeDeltaCum spqrSendTightDeltaLive spqrSendTightDeltaPeak
      spqrSendTightMaxReq :=
  (spqrSendPartsTightGen_phaseCreditSpec
    decodeState_fine_phaseCreditSpec_tight
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

/-- Witness-free tight `PhaseCreditSpec` for `spqr::send` at `links ≤ 707` (`Δcum = 4,437,159`, `Δlive = Δpeak = 294,391`).
-/
theorem spqrSend_phaseCreditSpec_tight_79236
    {stBytes ptext : Bytes}
    (_hPts : ValidEncoderPts640 stBytes)
    (_hChain : ValidChainParams stBytes) :
    PhaseCreditSpec fineCostModel (SpqrSendTightCap79236Env stBytes ptext)
      spqrSendTight79236DeltaCum spqrSendTightDeltaLive spqrSendTightDeltaPeak
      spqrSendTightMaxReq :=
  (spqrSendPartsTightGen_phaseCreditSpec
    decodeState_fine_phaseCreditSpec_tight
    statesFromPb_fine_phaseCreditSpec_tight
    statesSendRodataTight_fine_phaseCreditSpec
    chainFromTight_fine_phaseCreditSpec
    chainAddEpochTight4_fine_phaseCreditSpec
    chainSendKeyTight_fine_phaseCreditSpec
    chainIntoPbTight79236_fine_phaseCreditSpec
    messageSerializeTight_fine_phaseCreditSpec
    statesIntoPb_fine_phaseCreditSpec_tight
    (pqEncodeCapTight_fine_phaseCreditSpec 286196)
    (Nat.le_refl spqrSendTightDeltaLive)).mono
    (by decide) (Nat.le_refl _) (Nat.le_refl _) (by decide)

theorem spqrSend_phaseCreditSpec_tight_largeEncode_79236
    {stBytes ptext : Bytes}
    (_hPts : ValidEncoderPts640 stBytes)
    (_hChain : ValidChainParams stBytes) :
    PhaseCreditSpec fineCostModel (SpqrSendTightLarge79236Env stBytes ptext)
      spqrSendTightLarge79236DeltaCum spqrSendTightDeltaLive spqrSendTightDeltaPeak
      spqrSendTightMaxReq :=
  (spqrSendPartsTightGen_phaseCreditSpec
    decodeState_fine_phaseCreditSpec_tight
    statesFromPb_fine_phaseCreditSpec_tight
    statesSendRodataTight_fine_phaseCreditSpec
    chainFromTight_fine_phaseCreditSpec
    chainAddEpochTight4_fine_phaseCreditSpec
    chainSendKeyTight_fine_phaseCreditSpec
    chainIntoPbTight79236_fine_phaseCreditSpec
    messageSerializeTight_fine_phaseCreditSpec
    statesIntoPb_fine_phaseCreditSpec_tight
    (pqEncodeLargeTight_fine_phaseCreditSpec 286196)
    (Nat.le_refl spqrSendTightDeltaLive)).mono
    (by decide) (Nat.le_refl _) (Nat.le_refl _) (by decide)

theorem spqrSend_nonFreeCount_le_tight {stBytes ptext : Bytes} {evs : List AllocEvent}
    (h : SpqrSendTightCapEnv stBytes ptext evs) :
    nonFreeCount evs ≤ 1432 := by
  have hc := spqrSendPartsTightGen_nonFreeCount_le
    (fun _ hd => decodeStateTightEnv_nonFreeCount_le hd)
    (fun _ hf => statesFromPbTightEnv_nonFreeCount_le hf)
    (fun _ hs => hs.1)
    (fun _ hcf => hcf.1)
    (fun _ ha => ha.1)
    (fun _ hsk => hsk.1)
    (fun _ hci => hci.1)
    (fun _ hm => hm.1)
    (fun _ hsi => statesIntoPbTightEnv_nonFreeCount_le hsi)
    (fun _ hpq => pqEncodeCapTight_nonFreeCount_le hpq)
    h
  exact Nat.le_trans hc (by decide)

theorem spqrSendLarge_nonFreeCount_le_tight {stBytes ptext : Bytes} {evs : List AllocEvent}
    (h : SpqrSendTightLargeEnv stBytes ptext evs) :
    nonFreeCount evs ≤ 1432 := by
  have hc := spqrSendPartsTightGen_nonFreeCount_le
    (fun _ hd => decodeStateTightEnv_nonFreeCount_le hd)
    (fun _ hf => statesFromPbTightEnv_nonFreeCount_le hf)
    (fun _ hs => hs.1)
    (fun _ hcf => hcf.1)
    (fun _ ha => ha.1)
    (fun _ hsk => hsk.1)
    (fun _ hci => hci.1)
    (fun _ hm => hm.1)
    (fun _ hsi => statesIntoPbTightEnv_nonFreeCount_le hsi)
    (fun _ hpq => pqEncodeLargeTight_nonFreeCount_le hpq)
    h
  exact Nat.le_trans hc (by decide)

private theorem fineCredit_le_of_spec {E : List AllocEvent → Prop} {c p r : Nat}
    (hSpec : PhaseCreditSpec fineCostModel E c p p r)
    (s0 : fineCostModel.σ) {evs : List AllocEvent} (hevs : E evs) {cap : Nat}
    (hcap : c + p ≤ cap) :
    fineCredit fineCostModel (fineCostModel.stepEvents evs s0) ≤
      fineCredit fineCostModel s0 + cap := by
  unfold fineCredit
  obtain ⟨hc, hl, hp⟩ := hSpec.credit_le s0 hevs
  have hmax :
      max (HasFineReallocCredit.liveLarge (fineCostModel.stepEvents evs s0))
          (HasFineReallocCredit.peakLarge (fineCostModel.stepEvents evs s0)) ≤
        max (HasFineReallocCredit.liveLarge s0) (HasFineReallocCredit.peakLarge s0) + p :=
    Nat.max_le.mpr
      ⟨Nat.le_trans hl (Nat.add_le_add_right (Nat.le_max_left _ _) p),
       Nat.le_trans hp (Nat.max_le.mpr
         ⟨Nat.le_trans (Nat.le_max_right _ _) (Nat.le_add_right _ p),
          Nat.add_le_add_right (Nat.le_max_left _ _) p⟩)⟩
  have hadd := Nat.add_le_add hc hmax
  have hreord :
      (HasFineReallocCredit.cumSmall s0 + c) +
        (max (HasFineReallocCredit.liveLarge s0) (HasFineReallocCredit.peakLarge s0) + p) =
      (HasFineReallocCredit.cumSmall s0 +
        max (HasFineReallocCredit.liveLarge s0) (HasFineReallocCredit.peakLarge s0)) + (c + p) := by
    simp only [← Nat.add_assoc]
    simp only [Nat.add_assoc, Nat.add_left_comm c]
  rw [hreord] at hadd
  exact Nat.le_trans hadd (Nat.add_le_add_left hcap _)

/-- Single-branch `fineCredit` bound (`+ 4,506,140` bytes) on `SpqrSendTightCapEnv`. -/
theorem spqrSend_fineCredit_le_tight
    {stBytes ptext : Bytes}
    (hPts : ValidEncoderPts640 stBytes) (hChain : ValidChainParams stBytes)
    (s0 : fineCostModel.σ) {evs : List AllocEvent}
    (hevs : SpqrSendTightCapEnv stBytes ptext evs) :
    fineCredit fineCostModel (fineCostModel.stepEvents evs s0) ≤
      fineCredit fineCostModel s0 + spqrSendTightFineCreditCap := by
  rcases spqrSendPartsTightGenEnv_or_pq hevs with hSmall | hLarge
  · have hSmSpec := spqrSendPartsTightGen_phaseCreditSpec
      decodeState_fine_phaseCreditSpec_tight
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
    exact fineCredit_le_of_spec hSmSpec s0 hSmall (by decide)
  · exact fineCredit_le_of_spec
      (spqrSend_phaseCreditSpec_tight_largeEncode (ptext := ptext) hPts hChain)
      s0 hLarge (by decide)

/-- Whole-trace `evalLog` footprint bound (`baseFine + 4,506,140` bytes) on `SpqrSendTightCapEnv`.
-/
theorem spqrSend_evalLog_footprint_le_tight
    {stBytes ptext : Bytes}
    (hPts : ValidEncoderPts640 stBytes) (hChain : ValidChainParams stBytes)
    {evs : List AllocEvent}
    (hevs : SpqrSendTightCapEnv stBytes ptext evs) :
    fineCostModel.footprint (fineCostModel.evalLog evs) ≤
      HasFineReallocCredit.baseFine (M := fineCostModel) + spqrSendTightFineCreditCap := by
  rcases spqrSendPartsTightGenEnv_or_pq hevs with hSmall | hLarge
  · have hSmSpec := spqrSendPartsTightGen_phaseCreditSpec
      decodeState_fine_phaseCreditSpec_tight
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
    exact Nat.le_trans hfp (Nat.add_le_add_left (by decide) _)
  · have hfp :=
      (spqrSend_phaseCreditSpec_tight_largeEncode (ptext := ptext)
        hPts hChain).evalLog_footprint_le_of_live_le_peak
        (Nat.le_refl spqrSendTightDeltaLive) hLarge
    rw [Nat.add_assoc] at hfp
    exact Nat.le_trans hfp (Nat.add_le_add_left (by decide) _)

theorem spqrSendParts_c07_fineCredit_le_tight (F : ShaCompress)
    {stBytes : Bytes} {pb : V1State} {st0 : States spqrPolyApi (spqrAuthApi F)}
    {chainPb : Option ChainPB} {vn : Option VersionNegotiationPB}
    {xAdd : ChainAddEpochGhost} {xSk : ChainSendKeyGhost}
    {xCInto : ChainIntoPbCall} {xSInto : StatesIntoPbGhost F}
    {postSt : PqRatchetState}
    (dom : SpqrSendTightDomain F stBytes pb st0 xAdd xSInto xCInto postSt)
    (s0 : fineCostModel.σ) {evs : List AllocEvent}
    (hevs : SpqrSendC07TightEnv F stBytes pb st0 chainPb vn xAdd xSk xCInto xSInto postSt evs) :
    fineCredit fineCostModel (fineCostModel.stepEvents evs s0) ≤
      fineCredit fineCostModel s0 + spqrSendTightFineCreditCap := by
  by_cases hLarge : 135167 < pqRatchetStatePBEncodedLen postSt
  · exact fineCredit_le_of_spec
      (spqrSendParts_c07_phaseCreditSpec_tight_largeEncode F dom hLarge) s0 hevs (by decide)
  · have hSm : ∀ e, PqRatchetStateEncodeToVecEnv postSt e →
        FineSmallEvs 1 143484 (min 286196 135167) e := fun e he => by
      have hsm_len : pqRatchetStatePBEncodedLen postSt ≤ 135167 := Nat.le_of_not_lt hLarge
      rcases he with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact FineSmallEvs.nil 1 143484 (min 286196 135167)
      · exact FineSmallEvs.rustAlloc (by decide) (Nat.le_min.mpr ⟨dom.hPostLen, hsm_len⟩)
          (smallAllocCost_le_143484_of_le_135167 hsm_len)
    have hCinto : PhaseCreditSpec fineCostModel (ChainIntoPbEnv xCInto) 8186 0 0 448 :=
      chainIntoPbTight4_fine_phaseCreditSpec.of_imp
        fun _ => chainIntoPbEnv_to_tight4 dom.hCIntoLinks
    have hPqSm : PhaseCreditSpec fineCostModel (PqRatchetStateEncodeToVecEnv postSt)
        143484 0 0 (min 286196 135167) :=
      (fineSmallEvs_phaseCreditSpec 1 143484 (Nat.min_le_right 286196 135167)).of_imp hSm
    have hSmSpec := spqrSendPartsTightGen_phaseCreditSpec
      decodeState_fine_phaseCreditSpec_tight
      statesFromPb_fine_phaseCreditSpec_tight
      (statesSendRodata_fine_phaseCreditSpec F dom.hRodata)
      (chainFrom_fine_phaseCreditSpec chainPb vn)
      (optChainAddEpoch_fine_4_phaseCreditSpec (spqrHkdfWith F) xAdd dom.hAddLinks)
      (optChainSendKey_fine_phaseCreditSpec (spqrHkdfWith F) xSk)
      hCinto
      messageSerializeTight_fine_phaseCreditSpec
      statesIntoPb_fine_phaseCreditSpec_tight
      hPqSm
      (Nat.le_refl 0)
    exact fineCredit_le_of_spec hSmSpec s0 hevs (by decide)

end LibsignalBinary.Proofs.PeakBudget.SpqrSendPeakSpec
