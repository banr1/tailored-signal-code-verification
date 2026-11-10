/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit
public import LibsignalBinary.Proofs.PeakBudget.SpqrDomainCaps
public import LibsignalBinary.Proofs.PeakBudget.SpqrLeafCodecCredit
public import LibsignalBinary.Proofs.PeakBudget.SpqrPolyBounds
public import LibsignalBinary.Proofs.PeakBudget.SpqrTightCaps
public import LibsignalBinary.Proofs.PeakBudget.SpqrTightCapsAux

/-!
# Peak Live-Heap Interface for SPQR V1 Codecs, `initial_state`, and Polynomials

Re-exports `SpqrPolyBounds`, `SpqrBoundedCredit`, and `SpqrLeafCodecCredit`, and proves top-level
`spqr::decode_state` (`DecodeStateBoundedEnv`, `DecodeStateTightEnv`) and `<States>::from_pb`
(`StatesFromPbBoundedEnv`, `StatesFromPbTightEnv`) `PhaseCreditSpec` bounds.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec

open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.LibsignalSpqrV1
  (ChainParamsPB ProtoAuthenticator ProtoPolynomialDecoder ProtoPolynomialEncoder V1State
   spqrAuthApi)
open CryptoVerification.SpqrV1.Top.StateSize (rawV1State)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent FreeOnlyEvs SeqEnv rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Heap.Fine (fineCostModel)
open LibsignalBinary.Proofs.SpqrV1.Auth.FromPbBudget
  (AuthFromPbEnv authFromPbEvents authKeyCloneEvents)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbDefsBudget
  (FromPbDecAllocEnv FromPbDecEnv fromPbDecLoopAllocEvents fromPbDecSlotEvents)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.DefsBudget
  (EncoderFromPbAllocEnv EncoderFromPbEnv encoderFromPbPolysInitEvents
   encoderFromPbPolysLoopEvents encoderFromPbPolysSlotEvents encoderFromPbPtsLoopEvents
   encoderFromPbPtsSlotEvents)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget (nonFreeCount)
open LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBaseBudget
  (Ct1SentFromPbPostEnv EkSentCt1ReceivedFromPbPostEnv PbCt1Sent PbEkSentCt1Received
   authFromPbAllocEvents ct1SentFromPb ct1SentFromPbAllocEvents ekSentCt1ReceivedFromPb
   ekSentCt1ReceivedFromPbAllocEvents)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (ModelHyps PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas (fineCostModel_modelHyps)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit
  (SpqrBoundedTotalEvs SpqrLowInterceptHyps SpqrTightEvs SpqrTightHyps StatesIntoPbTightEnv
   fineCostModel_spqrTightHyps spqrTightEvs_fine_phaseCreditSpec spqrTightEvs_phaseCreditSpec
   statesIntoPbTightDeltaCum statesIntoPbTightDeltaLive statesIntoPbTightDeltaPeak
   statesIntoPbTightMaxReq)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightCapsAux
  (ValidChainParamsPB validChainParamsPB_trimSize_le)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)

/-! ## 1. Re-Exported Polynomial & Encoding Size Bounds (`SpqrPolyBounds`) -/

abbrev decodePbPolysTotal_len_and_sum := SpqrPolyBounds.decodePbPolysTotal_len_and_sum
abbrev pqRatchetStateEncodeToVec_len_le := SpqrPolyBounds.pqRatchetStateEncodeToVec_len_le
abbrev v1StateEncodeRaw_len_le := SpqrPolyBounds.v1StateEncodeRaw_len_le

/-! ## 2. Re-Exported Bounded-Event & Top-Level State Codec Specs (`SpqrBoundedCredit`) -/

export SpqrBoundedCredit
  (SpqrBoundedTotalEvs SpqrLowInterceptHyps fineCostModel_spqrLowInterceptHyps
   spqrBoundedEvs_phaseCreditSpec spqrBoundedTotalEvs_phaseCreditSpec)

abbrev statesIntoPb_phaseCreditSpec := @SpqrBoundedCredit.statesIntoPb_phaseCreditSpec
abbrev statesIntoPb_raw_phaseCreditSpec := @SpqrBoundedCredit.statesIntoPb_raw_phaseCreditSpec
abbrev initInner_phaseCreditSpec := @SpqrBoundedCredit.initInner_phaseCreditSpec
abbrev initialState_phaseCreditSpec := @SpqrBoundedCredit.initialState_phaseCreditSpec
abbrev pqRatchetStateEncodeToVec_phaseCreditSpec :=
  @SpqrBoundedCredit.pqRatchetStateEncodeToVec_phaseCreditSpec
abbrev pqRatchetStateEncodeToVec_raw_phaseCreditSpec :=
  @SpqrBoundedCredit.pqRatchetStateEncodeToVec_raw_phaseCreditSpec

/-! ## 3. Re-Exported Leaf Codec, Polynomial, & Chain Specs (`SpqrLeafCodecCredit`) -/

abbrev authFromPb_phaseCreditSpec := @SpqrLeafCodecCredit.authFromPb_phaseCreditSpec
abbrev authFromPb_raw_phaseCreditSpec := @SpqrLeafCodecCredit.authFromPb_raw_phaseCreditSpec
abbrev ct1SentFromPb_phaseCreditSpec := @SpqrLeafCodecCredit.ct1SentFromPb_phaseCreditSpec
abbrev ekSentCt1ReceivedFromPb_phaseCreditSpec :=
  @SpqrLeafCodecCredit.ekSentCt1ReceivedFromPb_phaseCreditSpec
abbrev encoderFromPbAlloc_phaseCreditSpec := @SpqrLeafCodecCredit.encoderFromPbAlloc_phaseCreditSpec
abbrev encoderFromPb_phaseCreditSpec := @SpqrLeafCodecCredit.encoderFromPb_phaseCreditSpec
abbrev encoderIntoPbAlloc_phaseCreditSpec := @SpqrLeafCodecCredit.encoderIntoPbAlloc_phaseCreditSpec
abbrev encoderIntoPb_phaseCreditSpec := @SpqrLeafCodecCredit.encoderIntoPb_phaseCreditSpec
abbrev decoderFromPbAlloc_phaseCreditSpec := @SpqrLeafCodecCredit.decoderFromPbAlloc_phaseCreditSpec
abbrev decoderFromPb_phaseCreditSpec := @SpqrLeafCodecCredit.decoderFromPb_phaseCreditSpec
abbrev decoderIntoPbAlloc_phaseCreditSpec := @SpqrLeafCodecCredit.decoderIntoPbAlloc_phaseCreditSpec
abbrev decoderIntoPb_phaseCreditSpec := @SpqrLeafCodecCredit.decoderIntoPb_phaseCreditSpec
abbrev chainIntoPb_phaseCreditSpec := @SpqrLeafCodecCredit.chainIntoPb_phaseCreditSpec
abbrev chainFromVN_phaseCreditSpec := @SpqrLeafCodecCredit.chainFromVN_phaseCreditSpec
abbrev chainFrom_phaseCreditSpec := @SpqrLeafCodecCredit.chainFrom_phaseCreditSpec
abbrev encodeBytes_phaseCreditSpec := @SpqrLeafCodecCredit.encodeBytes_phaseCreditSpec
abbrev hkdfToVec_phaseCreditSpec := @SpqrLeafCodecCredit.hkdfToVec_phaseCreditSpec
abbrev lagrangePrepare_phaseCreditSpec := @SpqrLeafCodecCredit.lagrangePrepare_phaseCreditSpec

/-! ## 4. Top-Level `spqr::decode_state` & `<States>::from_pb` Bounded Envelopes -/

/-- Slice-linear total-request bounded envelope for `spqr::decode_state` on an input slice of
length `bsLen` (`≤ 2 MiB`): linear total bytes (`8 * bsLen + 16384`), linear fresh small allocs
(`2 * bsLen + 64`), and logarithmic `Vec` doubling reallocs (`≤ 128`). -/
def DecodeStateBoundedEnv (bsLen : Nat) (evs : List AllocEvent) : Prop :=
  SpqrBoundedTotalEvs (2 * bsLen + 64) 128 (8 * bsLen + 16384) (2 * bsLen + 4096) evs

def decodeStateDeltaCum (bsLen : Nat) : Nat :=
  77 * (8 * bsLen + 16384) + 188 * (2 * bsLen + 64) + 9539 * 128

def decodeStateDeltaLive (bsLen : Nat) : Nat :=
  2 * (8 * bsLen + 16384)

def decodeStateDeltaPeak (bsLen : Nat) : Nat :=
  2 * (8 * bsLen + 16384)

def decodeStateMaxReq (bsLen : Nat) : Nat :=
  2 * bsLen + 4096

theorem decodeState_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : SpqrLowInterceptHyps M) (bsLen : Nat) :
    PhaseCreditSpec M (DecodeStateBoundedEnv bsLen)
      (decodeStateDeltaCum bsLen) (decodeStateDeltaLive bsLen)
      (decodeStateDeltaPeak bsLen) (decodeStateMaxReq bsLen) :=
  spqrBoundedTotalEvs_phaseCreditSpec hM hLow
    (2 * bsLen + 64) 128 (8 * bsLen + 16384) (2 * bsLen + 4096)

/-- Linear-realloc generalization of `DecodeStateBoundedEnv` (`maxReallocs = bsLen / 18 + 128`)
accommodating repeated inner `Vec` growth across wire sub-messages of length `≥ 18` B. -/
def DecodeStateLinearBoundedEnv (bsLen : Nat) (evs : List AllocEvent) : Prop :=
  SpqrBoundedTotalEvs (2 * bsLen + 64) (bsLen / 18 + 128) (8 * bsLen + 16384) (2 * bsLen + 4096) evs

def decodeStateLinearDeltaCum (bsLen : Nat) : Nat :=
  77 * (8 * bsLen + 16384) + 188 * (2 * bsLen + 64) + 9539 * (bsLen / 18 + 128)

theorem decodeStateLinearBoundedEnv_of_boundedEnv {bsLen : Nat} {evs : List AllocEvent}
    (h : DecodeStateBoundedEnv bsLen evs) :
    DecodeStateLinearBoundedEnv bsLen evs := by
  obtain ⟨ha, hr, ht, hall⟩ := h
  exact ⟨ha, by omega, ht, hall⟩

theorem decodeStateLinear_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : SpqrLowInterceptHyps M) (bsLen : Nat) :
    PhaseCreditSpec M (DecodeStateLinearBoundedEnv bsLen)
      (decodeStateLinearDeltaCum bsLen) (decodeStateDeltaLive bsLen)
      (decodeStateDeltaPeak bsLen) (decodeStateMaxReq bsLen) :=
  spqrBoundedTotalEvs_phaseCreditSpec hM hLow
    (2 * bsLen + 64) (bsLen / 18 + 128) (8 * bsLen + 16384) (2 * bsLen + 4096)

/-- Bounded envelope for `<States>::from_pb` (`Block 333`) parameterized by `pb : V1State`. -/
def StatesFromPbBoundedEnv (pb : V1State) (evs : List AllocEvent) : Prop :=
  let raw := rawV1State pb
  SpqrBoundedTotalEvs (raw + 64) 64 (4 * raw + 16384) (2 * raw + 4096) evs

def statesFromPbDeltaCum (pb : V1State) : Nat :=
  let raw := rawV1State pb
  77 * (4 * raw + 16384) + 188 * (raw + 64) + 9539 * 64

def statesFromPbDeltaLive (pb : V1State) : Nat :=
  2 * (4 * rawV1State pb + 16384)

def statesFromPbDeltaPeak (pb : V1State) : Nat :=
  2 * (4 * rawV1State pb + 16384)

def statesFromPbMaxReq (pb : V1State) : Nat :=
  2 * rawV1State pb + 4096

theorem statesFromPb_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : SpqrLowInterceptHyps M) (pb : V1State) :
    PhaseCreditSpec M (StatesFromPbBoundedEnv pb)
      (statesFromPbDeltaCum pb) (statesFromPbDeltaLive pb)
      (statesFromPbDeltaPeak pb) (statesFromPbMaxReq pb) :=
  spqrBoundedTotalEvs_phaseCreditSpec hM hLow
    (rawV1State pb + 64) 64 (4 * rawV1State pb + 16384) (2 * rawV1State pb + 4096)

/-! ## 5. Tight Small-Class Codec Specs (`Δlive = 0`, `Δpeak = 0`) -/

abbrev spqrBoundedEvs_small_phaseCreditSpec :=
  @SpqrBoundedCredit.spqrBoundedEvs_small_phaseCreditSpec
abbrev statesIntoPb_small_phaseCreditSpec :=
  @SpqrBoundedCredit.statesIntoPb_small_phaseCreditSpec
abbrev statesIntoPb_raw_small_phaseCreditSpec :=
  @SpqrBoundedCredit.statesIntoPb_raw_small_phaseCreditSpec
abbrev initInner_small_phaseCreditSpec :=
  @SpqrBoundedCredit.initInner_small_phaseCreditSpec
abbrev initialState_small_phaseCreditSpec :=
  @SpqrBoundedCredit.initialState_small_phaseCreditSpec
abbrev statesIntoPb_phaseCreditSpec_tight :=
  @SpqrBoundedCredit.statesIntoPb_phaseCreditSpec_tight
abbrev statesIntoPb_fine_phaseCreditSpec_tight :=
  @SpqrBoundedCredit.statesIntoPb_fine_phaseCreditSpec_tight
abbrev statesIntoPbTightEnv_nonFreeCount_le :=
  @SpqrBoundedCredit.statesIntoPbTightEnv_nonFreeCount_le
abbrev encoderIntoPbAllocEnv_tight :=
  @SpqrBoundedCredit.encoderIntoPbAllocEnv_tight
abbrev encoderIntoPbEnv_tight :=
  @SpqrBoundedCredit.encoderIntoPbEnv_tight
abbrev decoderIntoPbAllocEnv_tight :=
  @SpqrBoundedCredit.decoderIntoPbAllocEnv_tight
abbrev decoderIntoPbEnv_tight :=
  @SpqrBoundedCredit.decoderIntoPbEnv_tight

/-- Under `ValidChainParamsPB p` (`trimSize ≤ 2,201`), each serialized `KeyHistory.prev` buffer has
capacity `36 * p.trimSize ≤ 79,236` B (`< smallMaxReq fineCostModel = 135,167` B). -/
theorem prev_cap_le_79236_of_validChainParamsPB {p : ChainParamsPB} (h : ValidChainParamsPB p) :
    36 * p.trimSize ≤ 79236 := by
  have ht := validChainParamsPB_trimSize_le h
  omega

/-- Tight `spqr::decode_state` envelope under `PeerSpqrTightValid640` (`ValidV1PtsAt 640`,
`ValidChainParamsPB`, and `StatesDecPtsNeededBound`): `≤ 83` non-free small-class ops,
`cumSmall ≤ 1,307,216` B, `Δlive = 0`, `Δpeak = 0`, and `maxReq = 79,236` B. -/
def DecodeStateTightEnv (evs : List AllocEvent) : Prop :=
  SpqrTightEvs 83 1307216 79236 evs

def decodeStateTightDeltaCum : Nat := 1307216
def decodeStateTightDeltaLive : Nat := 0
def decodeStateTightDeltaPeak : Nat := 0
def decodeStateTightMaxReq : Nat := 79236

theorem decodeStateTightEnv_nonFreeCount_le {evs : List AllocEvent}
    (h : DecodeStateTightEnv evs) :
    nonFreeCount evs ≤ 83 :=
  h.1

theorem decodeStateTightEnv_nonFreeCount_le_128 {evs : List AllocEvent}
    (h : DecodeStateTightEnv evs) :
    nonFreeCount evs ≤ 128 :=
  Nat.le_trans h.1 (by decide)

theorem decodeState_phaseCreditSpec_tight {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hT : SpqrTightHyps M) :
    PhaseCreditSpec M DecodeStateTightEnv
      decodeStateTightDeltaCum decodeStateTightDeltaLive
      decodeStateTightDeltaPeak decodeStateTightMaxReq :=
  spqrTightEvs_phaseCreditSpec hM hT 83 1307216 (Nat.le_refl 79236)

theorem decodeState_fine_phaseCreditSpec_tight :
    PhaseCreditSpec fineCostModel DecodeStateTightEnv
      decodeStateTightDeltaCum decodeStateTightDeltaLive
      decodeStateTightDeltaPeak decodeStateTightMaxReq :=
  spqrTightEvs_fine_phaseCreditSpec 83 1307216 (Nat.le_refl 79236)

/-- Tight `<States>::from_pb` (`Block 333`) envelope under `ValidV1PtsAt 640` and
`StatesDecPtsNeededBound`: `≤ 56` small allocations, `cumSmall ≤ 359,623` B, `Δlive = 0`,
`Δpeak = 0`, and `maxReq = 2,560` B. -/
def StatesFromPbTightEnv (evs : List AllocEvent) : Prop :=
  SpqrTightEvs 56 359623 2560 evs

def statesFromPbTightDeltaCum : Nat := 359623
def statesFromPbTightDeltaLive : Nat := 0
def statesFromPbTightDeltaPeak : Nat := 0
def statesFromPbTightMaxReq : Nat := 2560

theorem statesFromPbTightEnv_nonFreeCount_le {evs : List AllocEvent}
    (h : StatesFromPbTightEnv evs) :
    nonFreeCount evs ≤ 56 :=
  h.1

theorem statesFromPbTightEnv_nonFreeCount_le_128 {evs : List AllocEvent}
    (h : StatesFromPbTightEnv evs) :
    nonFreeCount evs ≤ 128 :=
  Nat.le_trans h.1 (by decide)

theorem statesIntoPbTightEnv_nonFreeCount_le_128 {evs : List AllocEvent}
    (h : StatesIntoPbTightEnv evs) :
    nonFreeCount evs ≤ 128 :=
  Nat.le_trans h.1 (by decide)

theorem statesFromPb_phaseCreditSpec_tight {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hT : SpqrTightHyps M) :
    PhaseCreditSpec M StatesFromPbTightEnv
      statesFromPbTightDeltaCum statesFromPbTightDeltaLive
      statesFromPbTightDeltaPeak statesFromPbTightMaxReq :=
  spqrTightEvs_phaseCreditSpec hM hT 56 359623 (by decide)

theorem statesFromPb_fine_phaseCreditSpec_tight :
    PhaseCreditSpec fineCostModel StatesFromPbTightEnv
      statesFromPbTightDeltaCum statesFromPbTightDeltaLive
      statesFromPbTightDeltaPeak statesFromPbTightMaxReq :=
  spqrTightEvs_fine_phaseCreditSpec 56 359623 (by decide)

/-! ### Tight Leaf Codec Bridges for `<States>::from_pb` -/

private theorem mem_of_mem_takeWhile {α : Type} {p : α → Bool} :
    ∀ {xs : List α} {x : α}, x ∈ xs.takeWhile p → x ∈ xs
  | [], _, h => nomatch h
  | y :: ys, x, h => by
    simp only [List.takeWhile] at h
    split at h
    · rcases List.mem_cons.mp h with rfl | htl
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem y (mem_of_mem_takeWhile htl)
    · nomatch h

private theorem length_takeWhile_le {α : Type} (p : α → Bool) :
    ∀ (xs : List α), (xs.takeWhile p).length ≤ xs.length
  | [] => Nat.le_refl 0
  | _ :: xs => by
    simp only [List.takeWhile]
    split
    · simp only [List.length_cons]
      have ih := length_takeWhile_le p xs
      omega
    · exact Nat.zero_le _

/-- Tight bridge for `<Authenticator>::from_pb` (`AuthFromPbEnv pb`) under 32-byte keys. -/
theorem authFromPbEnv_tight {pb : ProtoAuthenticator} {evs : List AllocEvent}
    (hRoot : pb.rootKey.length ≤ 32) (hMac : pb.macKey.length ≤ 32)
    (hEnv : AuthFromPbEnv pb evs) :
    SpqrTightEvs 2 1476 32 evs := by
  rw [hEnv]
  unfold authFromPbEvents
  have hk₁ : SpqrTightEvs 1 738 32 (authKeyCloneEvents pb.rootKey) := by
    unfold authKeyCloneEvents
    split
    · exact SpqrTightEvs.nil 1 738 32
    · exact (SpqrTightEvs.rustAlloc hRoot (by decide)).mono
        (Nat.le_refl 1) (by decide) (Nat.le_refl 32)
  have hk₂ : SpqrTightEvs 1 738 32 (authKeyCloneEvents pb.macKey) := by
    unfold authKeyCloneEvents
    split
    · exact SpqrTightEvs.nil 1 738 32
    · exact (SpqrTightEvs.rustAlloc hMac (by decide)).mono
        (Nat.le_refl 1) (by decide) (Nat.le_refl 32)
  exact (hk₁.append hk₂).mono (by decide) (by decide) (by decide)

private theorem authFromPbAllocEvents_tight {auth : ProtoAuthenticator}
    (hRoot : auth.rootKey.length ≤ 32) (hMac : auth.macKey.length ≤ 32) :
    SpqrTightEvs 2 1476 32 (authFromPbAllocEvents auth) := by
  unfold authFromPbAllocEvents
  have hk₁ : SpqrTightEvs 1 738 32
      (if auth.rootKey = [] then [] else rustAllocEvents auth.rootKey.length 1) := by
    split
    · exact SpqrTightEvs.nil 1 738 32
    · exact (SpqrTightEvs.rustAlloc hRoot (by decide)).mono
        (Nat.le_refl 1) (by decide) (Nat.le_refl 32)
  have hk₂ : SpqrTightEvs 1 738 32
      (if auth.macKey = [] then [] else rustAllocEvents auth.macKey.length 1) := by
    split
    · exact SpqrTightEvs.nil 1 738 32
    · exact (SpqrTightEvs.rustAlloc hMac (by decide)).mono
        (Nat.le_refl 1) (by decide) (Nat.le_refl 32)
  exact (hk₁.append hk₂).mono (by decide) (by decide) (by decide)

/-- Tight bridge for `<Ct1Sent>::from_pb` (`Ct1SentFromPbPostEnv F pb`) under 32-byte auth keys. -/
theorem ct1SentFromPbPostEnv_tight {F : ShaCompress} {pb : PbCt1Sent} {evs : List AllocEvent}
    (hAuth : ∀ auth, pb.auth = some auth → auth.rootKey.length ≤ 32 ∧ auth.macKey.length ≤ 32)
    (hEnv : Ct1SentFromPbPostEnv F pb evs) :
    SpqrTightEvs 2 1476 32 evs := by
  obtain ⟨evsFree, hFree, rfl⟩ := hEnv
  have halloc : SpqrTightEvs 2 1476 32 (ct1SentFromPbAllocEvents F pb) := by
    unfold ct1SentFromPbAllocEvents
    cases ct1SentFromPb (spqrAuthApi F) pb with
    | error _ => exact SpqrTightEvs.nil 2 1476 32
    | ok _ =>
      cases ha : pb.auth with
      | none => exact SpqrTightEvs.nil 2 1476 32
      | some auth =>
        obtain ⟨hr, hm⟩ := hAuth auth ha
        exact authFromPbAllocEvents_tight hr hm
  exact (halloc.append (SpqrTightEvs.of_freeOnly hFree)).mono (by decide) (by decide) (by decide)

/-- Tight bridge for `<EkSentCt1Received>::from_pb` (`EkSentCt1ReceivedFromPbPostEnv F pb`)
under 32-byte auth keys. -/
theorem ekSentCt1ReceivedFromPbPostEnv_tight {F : ShaCompress} {pb : PbEkSentCt1Received}
    {evs : List AllocEvent}
    (hAuth : ∀ auth, pb.auth = some auth → auth.rootKey.length ≤ 32 ∧ auth.macKey.length ≤ 32)
    (hEnv : EkSentCt1ReceivedFromPbPostEnv F pb evs) :
    SpqrTightEvs 2 1476 32 evs := by
  obtain ⟨evsFree, hFree, rfl⟩ := hEnv
  have halloc : SpqrTightEvs 2 1476 32 (ekSentCt1ReceivedFromPbAllocEvents F pb) := by
    unfold ekSentCt1ReceivedFromPbAllocEvents
    cases ekSentCt1ReceivedFromPb (spqrAuthApi F) pb with
    | error _ => exact SpqrTightEvs.nil 2 1476 32
    | ok _ =>
      cases ha : pb.auth with
      | none => exact SpqrTightEvs.nil 2 1476 32
      | some auth =>
        obtain ⟨hr, hm⟩ := hAuth auth ha
        exact authFromPbAllocEvents_tight hr hm
  exact (halloc.append (SpqrTightEvs.of_freeOnly hFree)).mono (by decide) (by decide) (by decide)

private theorem encoderFromPbPolysInit_tight :
    SpqrTightEvs 16 3008 2 encoderFromPbPolysInitEvents := by
  unfold encoderFromPbPolysInitEvents
  have hrep : ∀ n : Nat,
      SpqrTightEvs n (n * 188) 2 ((List.replicate n (rustAllocEvents 2 2)).flatten) := by
    intro n
    induction n with
    | zero => exact SpqrTightEvs.nil 0 0 2
    | succ k ih =>
      simp only [List.replicate_succ, List.flatten_cons]
      have h2 : SpqrTightEvs 1 188 2 (rustAllocEvents 2 2) :=
        SpqrTightEvs.rustAlloc (Nat.le_refl 2) (by decide)
      exact (h2.append ih).mono (by omega) (by rw [Nat.succ_mul]; omega) (by decide)
  exact (hrep 16).mono (Nat.le_refl 16) (by decide) (Nat.le_refl 2)

/-- Tight bridge for `<PolyEncoder>::from_pb` (`EncoderFromPbAllocEnv pb`) under
`∀ bs ∈ pb.pts, bs.length ≤ 1,280` (`2 * bs.length ≤ 2,560`) and
`∀ bs ∈ pb.polys, bs.length ≤ 2,560` on `.polys`. -/
theorem encoderFromPbAllocEnv_tight {pb : ProtoPolynomialEncoder} {evs : List AllocEvent}
    (hPts : ∀ bs ∈ pb.pts, bs.length ≤ 1280)
    (hPolys : ∀ bs ∈ pb.polys, bs.length ≤ 2560)
    (hEnv : EncoderFromPbAllocEnv pb evs) :
    SpqrTightEvs 32 159632 2560 evs := by
  rcases hEnv with rfl | ⟨hlen, _, rfl⟩ | ⟨_, hlen, rfl⟩
  · exact SpqrTightEvs.nil 32 159632 2560
  · unfold encoderFromPbPtsLoopEvents
    have htw_len : (pb.pts.takeWhile (fun bs => bs.length % 2 == 0)).length ≤ 16 := by
      have hle := length_takeWhile_le (fun bs => bs.length % 2 == 0) pb.pts
      omega
    have hloop : SpqrTightEvs
        ((pb.pts.takeWhile (fun bs => bs.length % 2 == 0)).length * 1)
        ((pb.pts.takeWhile (fun bs => bs.length % 2 == 0)).length * 9789)
        2560
        ((pb.pts.takeWhile (fun bs => bs.length % 2 == 0)).flatMap encoderFromPbPtsSlotEvents) := by
      refine SpqrTightEvs.flatMap_const fun bs hbs => ?_
      unfold encoderFromPbPtsSlotEvents
      split
      · exact SpqrTightEvs.nil 1 9789 2560
      · have hbs_mem := mem_of_mem_takeWhile hbs
        have h2 : 2 * bs.length ≤ 2560 := by have := hPts bs hbs_mem; omega
        exact SpqrTightEvs.rustAlloc h2 (by decide)
    exact hloop.mono (by omega) (by omega) (Nat.le_refl 2560)
  · have htw_len :
        (pb.polys.takeWhile (fun bs => !bs.isEmpty && (bs.length % 2 == 0))).length ≤ 16 := by
      have hle := length_takeWhile_le (fun bs => !bs.isEmpty && (bs.length % 2 == 0)) pb.polys
      omega
    have hloop : SpqrTightEvs
        ((pb.polys.takeWhile (fun bs => !bs.isEmpty && (bs.length % 2 == 0))).length * 1)
        ((pb.polys.takeWhile (fun bs => !bs.isEmpty && (bs.length % 2 == 0))).length * 9789)
        2560
        (encoderFromPbPolysLoopEvents pb.polys) := by
      unfold encoderFromPbPolysLoopEvents
      refine SpqrTightEvs.flatMap_const fun bs hbs => ?_
      unfold encoderFromPbPolysSlotEvents
      have hbs_mem := mem_of_mem_takeWhile hbs
      have halloc : SpqrTightEvs 1 9789 2560 (rustAllocEvents bs.length 2) :=
        SpqrTightEvs.rustAlloc (hPolys bs hbs_mem) (by decide)
      exact (halloc.append (SpqrTightEvs.rustDealloc 2 2)).mono
        (by decide) (by decide) (by decide)
    exact (encoderFromPbPolysInit_tight.append hloop).mono
      (by omega) (by omega) (by decide)

/-- Tight postcondition bridge for `<PolyEncoder>::from_pb` (`EncoderFromPbEnv pb`). -/
theorem encoderFromPbEnv_tight {pb : ProtoPolynomialEncoder} {evs : List AllocEvent}
    (hPts : ∀ bs ∈ pb.pts, bs.length ≤ 1280)
    (hPolys : ∀ bs ∈ pb.polys, bs.length ≤ 2560)
    (hEnv : EncoderFromPbEnv pb evs) :
    SpqrTightEvs 32 159632 2560 evs := by
  obtain ⟨evs_a, evs_f, rfl, ha, hf⟩ := hEnv
  exact ((encoderFromPbAllocEnv_tight hPts hPolys ha).append (SpqrTightEvs.of_freeOnly hf)).mono
    (by omega) (by omega) (by decide)

/-- Tight bridge for `<PolyDecoder>::from_pb` (`FromPbDecAllocEnv pb`) under
`∀ bs ∈ pb.pts, bs.length ≤ 2,560` (`4 * 576 = 2,304 ≤ 2,560`). -/
theorem decoderFromPbAllocEnv_tight {pb : ProtoPolynomialDecoder} {evs : List AllocEvent}
    (hPts : ∀ bs ∈ pb.pts, bs.length ≤ 2560)
    (hEnv : FromPbDecAllocEnv pb evs) :
    SpqrTightEvs 16 156624 2560 evs := by
  rcases hEnv with rfl | ⟨hlen, rfl⟩
  · exact SpqrTightEvs.nil 16 156624 2560
  · unfold fromPbDecLoopAllocEvents
    have htw_len : (pb.pts.takeWhile (fun bs => bs.length % 4 == 0)).length ≤ 16 := by
      have hle := length_takeWhile_le (fun bs => bs.length % 4 == 0) pb.pts
      omega
    have hloop : SpqrTightEvs
        ((pb.pts.takeWhile (fun bs => bs.length % 4 == 0)).length * 1)
        ((pb.pts.takeWhile (fun bs => bs.length % 4 == 0)).length * 9789)
        2560
        ((pb.pts.takeWhile (fun bs => bs.length % 4 == 0)).flatMap fromPbDecSlotEvents) := by
      refine SpqrTightEvs.flatMap_const fun bs hbs => ?_
      unfold fromPbDecSlotEvents
      split
      · exact SpqrTightEvs.nil 1 9789 2560
      · exact SpqrTightEvs.rustAlloc (hPts bs (mem_of_mem_takeWhile hbs)) (by decide)
    exact hloop.mono (by omega) (by omega) (Nat.le_refl 2560)

/-- Tight postcondition bridge for `<PolyDecoder>::from_pb` (`FromPbDecEnv pb`). -/
theorem decoderFromPbEnv_tight {pb : ProtoPolynomialDecoder} {evs : List AllocEvent}
    (hPts : ∀ bs ∈ pb.pts, bs.length ≤ 2560)
    (hEnv : FromPbDecEnv pb evs) :
    SpqrTightEvs 16 156624 2560 evs := by
  obtain ⟨evs_a, evs_f, rfl, ha, hf⟩ := hEnv
  exact ((decoderFromPbAllocEnv_tight hPts ha).append (SpqrTightEvs.of_freeOnly hf)).mono
    (by omega) (by omega) (by decide)

end LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec
