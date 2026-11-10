/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.PeakBudget.GroupCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
public import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedBudget

/-!
# Sub-Phase `PhaseCreditSpec` Helpers for SPQR `<States>::recv`

Exact-call-order `PhaseCreditSpec` and `NonFreeBound` lemmas for the sub-phases of
`<spqr::v1::chunked::states::States>::recv`: `<PolyDecoder>::add_chunk`, `<Poly>::compute_at`,
inlined `Poly::lagrange_interpolate` with 16-slot polynomial cache-miss accounting for
`<PolyDecoder>::decoded_message`, `libcruxHmacSha256Events`, and `<Ct1SentEkReceived>::send_ct2`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvCreditHelpers

open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.LibsignalSpqrV1 (Bytes GF16 Poly PolyDecoder Pt SortedSetPt)
open CryptoVerification.LibsignalTripleRatchet (reserveCap)
open CryptoVerification.SpqrV1.Poly.AddChunk (AddChunkGhost)
open CryptoVerification.SpqrV1.Poly.DecodedMessage
  (collectPointsVecsTotal collectPointsVecsTotal_of_fst_false collectedSlices
   collectedSlices_getElem collectedSlices_length lagrangeInterpolateTotal
   lagrangeInterpolateTotal_length necessaryPoints_le)
open CryptoVerification.SpqrV1.States.Leaves (UnchunkedSendCt2Ghost)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent FreeOnlyEvs SeqEnv
   rustAllocEvents rustDeallocEvents rustReallocEvents)
open LibsignalBinary.Heap.Fine (fineCostModel fineSmallAllocCost fineSmallReallocCost)
open LibsignalBinary.Heap.Fine.ClientBounds
  (eventStepAlign eventStepReq fineCostModel_smallMaxReq_eq smallAllocCost_eq_188_of_le_12
   smallAllocCost_le_488_of_le_28 smallAllocCost_le_738_of_le_44 smallReallocCost_le_add_26365
   smallReallocCost_le_two_mul_add)
open LibsignalBinary.Heap.SpecBudget (LibcruxHmacEnv libcruxHmacSha256Events)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit (NonFreeBound PhaseGroupSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
  (ConcatEnv IterSeqEnv ModelHyps PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas (fineCostModel_modelHyps)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.DefsBudget
  (AddChunkEnv AddChunkSlotEnv AddChunkSlotsEnv growOnePtEvents)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DefsBudget
  (ComputeAtCallEnv DecodedMessageEnv DecodedMessageLoopEnv
   LagrangeInterpolateInlinedEnv LagrangeInterpolateMissEnv computeAtAllocEvents)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
  (EncodeBytesEnv encodeBytesAllocEvents)
open LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedBudget
  (SendCt2Reserve128Env UnchunkedSendCt2Env UnchunkedSendCt2PreEnv
   sendCt2ConcatHmacEvents sendCt2FlipAllocEvents sendCt2FlipDeallocEvents
   sendCt2Reserve128Events sendCt2Seg23Events)

/-! ## Deterministic Append and `rustReallocEvents` Credit Helpers -/

theorem PhaseCreditSpec.append_eq {M : AllocCostModel} [HasFineReallocCredit M]
    {a b : List AllocEvent} {c₁ l₁ p₁ r₁ c₂ l₂ p₂ r₂ : Nat}
    (h₁ : PhaseCreditSpec M (· = a) c₁ l₁ p₁ r₁)
    (h₂ : PhaseCreditSpec M (· = b) c₂ l₂ p₂ r₂) :
    PhaseCreditSpec M (· = a ++ b) (c₁ + c₂) (l₁ + l₂) (max p₁ (l₁ + p₂)) (max r₁ r₂) :=
  (h₁.concat h₂).of_imp fun _ h => ⟨a, b, h, rfl, rfl⟩

/-- Regime-uniform affine `PhaseCreditSpec` for `rustReallocEvents old new al` when `al ≤ 16` and `al ≤ new`.
-/
theorem PhaseCreditSpec.rustRealloc_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {old new al : Nat} (hal : al ≤ 16) (hal_new : al ≤ new) :
    PhaseCreditSpec M (· = rustReallocEvents old new al)
      (2 * new + 9539) (new + 8195) (new + 8195) new where
  req_align := by
    rintro _ rfl ev hev
    unfold rustReallocEvents at hev
    simp only [hal, hal_new, and_self, ↓reduceIte, List.mem_singleton] at hev
    subst hev
    exact ⟨Nat.le_refl new, hal⟩
  credit_le := by
    rintro st0 _ rfl
    unfold rustReallocEvents
    simp only [hal, hal_new, and_self, ↓reduceIte,
      AllocCostModel.stepEvents_cons, AllocCostModel.stepEvents_nil]
    exact hM.step_nonFree_aff st0 (Nat.le_refl new) hal

/-- Small-class `PhaseCreditSpec` for `rustReallocEvents old new al` (including `old = 0`) when `old, new ≤ smallMaxReq M`.
-/
theorem PhaseCreditSpec.rustRealloc_small_any {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {old new al : Nat} (hal : al ≤ 16) (hal_new : al ≤ new)
    (hold_le : old ≤ HasFineReallocCredit.smallMaxReq M)
    (hnew_le : new ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (· = rustReallocEvents old new al)
      (2 * new + 9539) 0 0 new where
  req_align := by
    rintro _ rfl ev hev
    unfold rustReallocEvents at hev
    simp only [hal, hal_new, and_self, ↓reduceIte, List.mem_singleton] at hev
    subst hev
    exact ⟨Nat.le_refl new, hal⟩
  credit_le := by
    rintro st0 _ rfl
    unfold rustReallocEvents
    simp only [hal, hal_new, and_self, ↓reduceIte,
      AllocCostModel.stepEvents_cons, AllocCostModel.stepEvents_nil]
    obtain ⟨hc, hl, hp⟩ := hM.step_realloc_small_small_any st0 hal hold_le hnew_le
    have hsr := hM.smallRealloc_le hnew_le
    omega

/-! ## `<PolyDecoder as Decoder>::add_chunk` (`AddChunkSlotsEnv` and `AddChunkEnv`) -/

theorem addChunkSlotsEnv_iff_iterSeqEnv :
    ∀ (pts : List SortedSetPt) (evs : List AllocEvent),
      AddChunkSlotsEnv pts evs ↔ IterSeqEnv AddChunkSlotEnv pts evs
  | [], _ => Iff.rfl
  | s :: rest, evs => by
    dsimp only [AddChunkSlotsEnv, IterSeqEnv]
    constructor <;> intro h
    · rcases h with h1 | ⟨e1, e2, rfl, he1, he2⟩
      · exact Or.inl h1
      · exact Or.inr ⟨e1, e2, rfl, he1, (addChunkSlotsEnv_iff_iterSeqEnv rest e2).mp he2⟩
    · rcases h with h1 | ⟨e1, e2, rfl, he1, he2⟩
      · exact Or.inl h1
      · exact Or.inr ⟨e1, e2, rfl, he1, (addChunkSlotsEnv_iff_iterSeqEnv rest e2).mpr he2⟩

/-- Total point count across a list of `SortedSetPt` buckets. -/
def ptsLenSum (pts : List SortedSetPt) : Nat :=
  (pts.map (fun s => s.vec.length)).sum

theorem growOnePt_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (len : Nat) :
    PhaseCreditSpec M (· = growOnePtEvents len)
      (16 * len + 9571) (8 * len + 8211) (8 * len + 8211) (8 * len + 16) := by
  unfold growOnePtEvents
  split
  · exact (PhaseCreditSpec.rustAlloc_aff hM (req := 16) (al := 2) (by decide)).mono
      (by omega) (by omega) (by omega) (by omega)
  · have hal_new : 2 ≤ 4 * max (2 * len) 4 := by omega
    have hnew_le : 4 * max (2 * len) 4 ≤ 8 * len + 16 := by omega
    exact (PhaseCreditSpec.rustRealloc_aff hM (old := 4 * len)
      (new := 4 * max (2 * len) 4) (al := 2) (by decide) hal_new).mono
      (by omega) (by omega) (by omega) hnew_le

theorem growOnePt_small_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {len : Nat}
    (hsmall : 8 * len + 16 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (· = growOnePtEvents len)
      (16 * len + 9571) 0 0 (8 * len + 16) := by
  unfold growOnePtEvents
  split
  · have h16 : 16 ≤ HasFineReallocCredit.smallMaxReq M := by omega
    have hsa := hM.smallAlloc_le h16
    exact (PhaseCreditSpec.rustAlloc_small_any hM (req := 16) (al := 2) (by decide) h16).mono
      (by omega) (Nat.le_refl 0) (Nat.le_refl 0) (by omega)
  · have hal_new : 2 ≤ 4 * max (2 * len) 4 := by omega
    have hnew_le : 4 * max (2 * len) 4 ≤ 8 * len + 16 := by omega
    have hold_sm : 4 * len ≤ HasFineReallocCredit.smallMaxReq M := by omega
    have hnew_sm : 4 * max (2 * len) 4 ≤ HasFineReallocCredit.smallMaxReq M :=
      Nat.le_trans hnew_le hsmall
    exact (PhaseCreditSpec.rustRealloc_small_any hM (old := 4 * len)
      (new := 4 * max (2 * len) 4) (al := 2) (by decide) hal_new hold_sm hnew_sm).mono
      (by omega) (Nat.le_refl 0) (Nat.le_refl 0) hnew_le

theorem addChunkSlot_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (s : SortedSetPt) :
    PhaseCreditSpec M (AddChunkSlotEnv s)
      (16 * s.vec.length + 9571) (8 * s.vec.length + 8211)
      (8 * s.vec.length + 8211) (8 * s.vec.length + 16) := by
  unfold AddChunkSlotEnv
  exact ((PhaseCreditSpec.nil M).or (growOnePt_phaseCreditSpec hM s.vec.length)).mono
    (by omega) (by omega) (by omega) (by omega)

theorem addChunkSlot_small_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {s : SortedSetPt}
    (hsmall : 8 * s.vec.length + 16 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (AddChunkSlotEnv s)
      (16 * s.vec.length + 9571) 0 0 (8 * s.vec.length + 16) := by
  unfold AddChunkSlotEnv
  exact ((PhaseCreditSpec.nil M).or (growOnePt_small_phaseCreditSpec hM hsmall)).mono
    (by omega) (by omega) (by omega) (by omega)

/-- Regime-uniform `PhaseCreditSpec` for `AddChunkSlotsEnv pts` under `ModelHyps M`. -/
theorem addChunkSlots_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) :
    ∀ (pts : List SortedSetPt),
      PhaseCreditSpec M (AddChunkSlotsEnv pts)
        (16 * ptsLenSum pts + 9571 * pts.length)
        (8 * ptsLenSum pts + 8211 * pts.length)
        (8 * ptsLenSum pts + 8211 * pts.length)
        (8 * ptsLenSum pts + 16)
  | [] =>
    (PhaseCreditSpec.nil M).mono
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  | s :: rest => by
    dsimp only [AddChunkSlotsEnv]
    have h1 := addChunkSlot_phaseCreditSpec hM s
    have h2 := addChunkSlots_phaseCreditSpec hM rest
    refine (h1.seq h2).mono ?_ ?_ ?_ ?_ <;>
      simp only [ptsLenSum, List.map_cons, List.sum_cons, List.length_cons] <;> omega

/-- Small-class `PhaseCreditSpec` (`Δlive = Δpeak = 0`) for `AddChunkSlotsEnv pts` when `8 * maxPts + 16 ≤ smallMaxReq M`.
-/
theorem addChunkSlots_small_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {maxPts : Nat} :
    ∀ (pts : List SortedSetPt),
      (∀ s ∈ pts, s.vec.length ≤ maxPts) →
      8 * maxPts + 16 ≤ HasFineReallocCredit.smallMaxReq M →
      PhaseCreditSpec M (AddChunkSlotsEnv pts)
        (16 * ptsLenSum pts + 9571 * pts.length) 0 0 (8 * maxPts + 16)
  | [], _, _ =>
    (PhaseCreditSpec.nil M).mono
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  | s :: rest, hpts, hsmall => by
    dsimp only [AddChunkSlotsEnv]
    have hs : s.vec.length ≤ maxPts := hpts s List.mem_cons_self
    have h1 := addChunkSlot_small_phaseCreditSpec hM (s := s) (by omega)
    have h2 := addChunkSlots_small_phaseCreditSpec hM rest
      (fun t ht => hpts t (List.mem_cons_of_mem s ht)) hsmall
    refine (h1.seq h2).mono ?_ (by omega) (by omega) (by omega)
    simp only [ptsLenSum, List.map_cons, List.sum_cons, List.length_cons]
    omega

theorem addChunk_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (x : AddChunkGhost) :
    PhaseCreditSpec M (AddChunkEnv x)
      (16 * ptsLenSum x.dec.pts + 9571 * x.dec.pts.length)
      (8 * ptsLenSum x.dec.pts + 8211 * x.dec.pts.length)
      (8 * ptsLenSum x.dec.pts + 8211 * x.dec.pts.length)
      (8 * ptsLenSum x.dec.pts + 16) :=
  addChunkSlots_phaseCreditSpec hM x.dec.pts

theorem addChunk_small_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {x : AddChunkGhost} {maxPts : Nat}
    (hpts : ∀ s ∈ x.dec.pts, s.vec.length ≤ maxPts)
    (hsmall : 8 * maxPts + 16 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (AddChunkEnv x)
      (16 * ptsLenSum x.dec.pts + 9571 * x.dec.pts.length) 0 0 (8 * maxPts + 16) :=
  addChunkSlots_small_phaseCreditSpec hM x.dec.pts hpts hsmall

/-! ## 16-Slot Polynomial Cache Invariants and `<PolyDecoder>::decoded_message` -/

/-- Count of unpopulated (`none`) entries in the 16-slot `polys` cache, bounding `LagrangeInterpolateMissEnv` calls across `decodedMessageLoop` by at most `16`.
-/
def polyNoneCount : List (Option Poly) → Nat
  | [] => 0
  | none :: tl => polyNoneCount tl + 1
  | some _ :: tl => polyNoneCount tl

theorem polyNoneCount_replicate_none :
    ∀ (n : Nat), polyNoneCount (List.replicate n none) = n
  | 0 => rfl
  | n + 1 => by
    simp only [List.replicate_succ, polyNoneCount, polyNoneCount_replicate_none n]

theorem polyNoneCount_set_some_eq :
    ∀ (polys : List (Option Poly)) (idx : Nat) (p : Poly),
      idx < polys.length →
      polys[idx]?.getD none = none →
      polyNoneCount (polys.set idx (some p)) + 1 = polyNoneCount polys
  | [], _, _, hlt, _ => absurd hlt (Nat.not_lt_zero _)
  | none :: _, 0, _, _, _ => by
    simp [polyNoneCount]
  | some _ :: _, 0, _, _, hget => by
    simp at hget
  | none :: tl, idx + 1, p, hlt, hget => by
    simp only [List.length_cons, Nat.add_lt_add_iff_right] at hlt
    simp only [List.getElem?_cons_succ] at hget
    have ih := polyNoneCount_set_some_eq tl idx p hlt hget
    simp only [List.set_cons_succ, polyNoneCount]
    omega
  | some _ :: tl, idx + 1, p, hlt, hget => by
    simp only [List.length_cons, Nat.add_lt_add_iff_right] at hlt
    simp only [List.getElem?_cons_succ] at hget
    have ih := polyNoneCount_set_some_eq tl idx p hlt hget
    simp only [List.set_cons_succ, polyNoneCount, ih]

/-- Bounds the coefficient length of every populated `Poly` entry in `polys` by `K`. -/
def PolyCacheDegBound (K : Nat) : List (Option Poly) → Prop
  | [] => True
  | none :: tl => PolyCacheDegBound K tl
  | some p :: tl => p.coefficients.length ≤ K ∧ PolyCacheDegBound K tl

theorem polyCacheDegBound_replicate_none (K : Nat) :
    ∀ (n : Nat), PolyCacheDegBound K (List.replicate n none)
  | 0 => trivial
  | n + 1 => polyCacheDegBound_replicate_none K n

theorem polyCacheDegBound_getD_some {K : Nat} :
    ∀ (polys : List (Option Poly)) (idx : Nat) (p : Poly),
      PolyCacheDegBound K polys →
      polys[idx]?.getD none = some p →
      p.coefficients.length ≤ K
  | [], _, _, _, hget => by simp at hget
  | none :: _, 0, _, _, hget => by simp at hget
  | some _ :: _, 0, p, hdeg, hget => by
    simp only [List.getElem?_cons_zero, Option.getD_some, Option.some.injEq] at hget
    subst hget
    exact hdeg.1
  | none :: tl, idx + 1, p, hdeg, hget => by
    simp only [List.getElem?_cons_succ] at hget
    exact polyCacheDegBound_getD_some tl idx p hdeg hget
  | some _ :: tl, idx + 1, p, hdeg, hget => by
    simp only [List.getElem?_cons_succ] at hget
    exact polyCacheDegBound_getD_some tl idx p hdeg.2 hget

theorem polyCacheDegBound_set_some {K : Nat} :
    ∀ (polys : List (Option Poly)) (idx : Nat) (p : Poly),
      PolyCacheDegBound K polys →
      p.coefficients.length ≤ K →
      PolyCacheDegBound K (polys.set idx (some p))
  | [], _, _, _, _ => trivial
  | none :: _, 0, _, hdeg, hp => ⟨hp, hdeg⟩
  | some _ :: _, 0, _, hdeg, hp => ⟨hp, hdeg.2⟩
  | none :: tl, idx + 1, p, hdeg, hp =>
    polyCacheDegBound_set_some tl idx p hdeg hp
  | some _ :: tl, idx + 1, p, hdeg, hp =>
    ⟨hdeg.1, polyCacheDegBound_set_some tl idx p hdeg.2 hp⟩

/-- Every collected point slice `(collectedSlices dec 0 16)[k]?.getD []` (`k < 16`) has length at most `dec.ptsNeeded / 16 + 1`.
-/
theorem collectedSlices_getD_length_le (dec : PolyDecoder) {k : Nat} (hk : k < 16) :
    ((collectedSlices dec 0 16)[k]?.getD []).length ≤ dec.ptsNeeded / 16 + 1 := by
  have hlen : (collectedSlices dec 0 16).length = 16 := collectedSlices_length dec 16 0
  have hk' : k < (collectedSlices dec 0 16).length := hlen ▸ hk
  rw [List.getElem?_eq_getElem hk', Option.getD_some, collectedSlices_getElem dec 16 0 k hk]
  exact Nat.le_trans (List.length_take_le _ _) (by rw [Nat.zero_add]; exact necessaryPoints_le dec k)

theorem computeAtCall_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {len K : Nat} (hlen : len ≤ K) :
    PhaseCreditSpec M (ComputeAtCallEnv len)
      (4 * K + 19098) (2 * K + 16400) (2 * K + 16400) (max 8 (2 * K)) := by
  unfold ComputeAtCallEnv
  have halloc :
      PhaseCreditSpec M (· = computeAtAllocEvents len)
        (4 * K + 19098) (2 * K + 16400) (2 * K + 16400) (max 8 (2 * K)) := by
    unfold computeAtAllocEvents
    split
    · exact (PhaseCreditSpec.rustAlloc_aff hM (req := 8) (al := 2) (by decide)).mono
        (by omega) (by omega) (by omega) (by omega)
    · split
      · have h1 := PhaseCreditSpec.rustAlloc_aff hM (req := 2) (al := 2) (by decide)
        have h2 := PhaseCreditSpec.rustRealloc_aff hM (old := 2) (new := 8) (al := 2)
          (by decide) (by decide)
        exact (PhaseCreditSpec.append_eq h1 h2).mono (by omega) (by omega) (by omega) (by omega)
      · exact (PhaseCreditSpec.rustAlloc_aff hM (req := 2 * len) (al := 2) (by decide)).mono
          (by omega) (by omega) (by omega) (by omega)
  exact (halloc.seq (PhaseCreditSpec.freeOnly_of_hyps hM)).mono
    (by omega) (by omega) (by omega) (by omega)

theorem computeAtCall_small_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {len K : Nat} (hlen : len ≤ K)
    (hsmall : max 8 (2 * K) ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (ComputeAtCallEnv len)
      (4 * K + 19098) 0 0 (max 8 (2 * K)) := by
  unfold ComputeAtCallEnv
  have halloc :
      PhaseCreditSpec M (· = computeAtAllocEvents len)
        (4 * K + 19098) 0 0 (max 8 (2 * K)) := by
    unfold computeAtAllocEvents
    split
    · have h8 : 8 ≤ HasFineReallocCredit.smallMaxReq M := by omega
      have hsa := hM.smallAlloc_le h8
      exact (PhaseCreditSpec.rustAlloc_small_any hM (req := 8) (al := 2) (by decide) h8).mono
        (by omega) (Nat.le_refl 0) (Nat.le_refl 0) (by omega)
    · split
      · have h2s : 2 ≤ HasFineReallocCredit.smallMaxReq M := by omega
        have h8s : 8 ≤ HasFineReallocCredit.smallMaxReq M := by omega
        have hsa2 := hM.smallAlloc_le h2s
        have h1 := PhaseCreditSpec.rustAlloc_small_any hM (req := 2) (al := 2) (by decide) h2s
        have h2 := PhaseCreditSpec.rustRealloc_small_any hM (old := 2) (new := 8) (al := 2)
          (by decide) (by decide) h2s h8s
        exact (PhaseCreditSpec.append_eq h1 h2).mono (by omega) (by omega) (by omega) (by omega)
      · have h2l : 2 * len ≤ HasFineReallocCredit.smallMaxReq M := by omega
        have hsa := hM.smallAlloc_le h2l
        exact (PhaseCreditSpec.rustAlloc_small_any hM (req := 2 * len) (al := 2)
          (by decide) h2l).mono (by omega) (Nat.le_refl 0) (Nat.le_refl 0) (by omega)
  exact (halloc.seq (PhaseCreditSpec.freeOnly_of_hyps hM)).mono
    (by omega) (by omega) (by omega) (by omega)

theorem lagrangeInterpolateMiss_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {k K : Nat} (hk : k ≤ K) :
    PhaseCreditSpec M (LagrangeInterpolateMissEnv k)
      (12 * K + 28625) (6 * K + 24589) (6 * K + 24589) (2 * K + 2) := by
  unfold LagrangeInterpolateMissEnv
  have h1 := PhaseCreditSpec.rustAlloc_aff hM (req := 2 * k) (al := 2) (by decide)
  have h2 := PhaseCreditSpec.rustAlloc_aff hM (req := 2 * (k + 1)) (al := 2) (by decide)
  have halloc := PhaseCreditSpec.append_eq (PhaseCreditSpec.append_eq h1 h2) h2
  exact (halloc.seq (PhaseCreditSpec.freeOnly_of_hyps hM)).mono
    (by omega) (by omega) (by omega) (by omega)

theorem lagrangeInterpolateMiss_small_phaseCreditSpec
    {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {k K : Nat} (hk : k ≤ K)
    (hsmall : 2 * K + 2 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (LagrangeInterpolateMissEnv k)
      (12 * K + 28625) 0 0 (2 * K + 2) := by
  unfold LagrangeInterpolateMissEnv
  have hk_sm : 2 * k ≤ HasFineReallocCredit.smallMaxReq M := by omega
  have hk1_sm : 2 * (k + 1) ≤ HasFineReallocCredit.smallMaxReq M := by omega
  have hsa0 := hM.smallAlloc_le hk_sm
  have hsa1 := hM.smallAlloc_le hk1_sm
  have h1 := PhaseCreditSpec.rustAlloc_small_any hM (req := 2 * k) (al := 2) (by decide) hk_sm
  have h2 := PhaseCreditSpec.rustAlloc_small_any hM (req := 2 * (k + 1)) (al := 2)
    (by decide) hk1_sm
  have halloc := PhaseCreditSpec.append_eq (PhaseCreditSpec.append_eq h1 h2) h2
  exact (halloc.seq (PhaseCreditSpec.freeOnly_of_hyps hM)).mono
    (by omega) (by omega) (by omega) (by omega)

theorem lagrangeInterpolateInlined_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (optPoly : Option Poly) {k K : Nat} (hk : k ≤ K) :
    PhaseCreditSpec M (LagrangeInterpolateInlinedEnv optPoly k)
      (12 * K + 28625) (6 * K + 24589) (6 * K + 24589) (2 * K + 2) := by
  cases optPoly with
  | some _ =>
    exact (PhaseCreditSpec.nil M).mono
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  | none =>
    exact lagrangeInterpolateMiss_phaseCreditSpec hM hk

private theorem decodedMessageLoopEnv_succ (self : PolyDecoder) (pointsVecs : List (List Pt))
    (i rem : Nat) (polys : List (Option Poly)) :
    DecodedMessageLoopEnv self pointsVecs i (rem + 1) polys =
      match (self.pts[i % 16]?.getD SortedSetPt.new).binarySearch
          { x := GF16.new (BitVec.ofNat 16 (i / 16)), y := GF16.ZERO } with
      | .ok _ => DecodedMessageLoopEnv self pointsVecs (i + 1) rem polys
      | .error _ =>
        match polys[i % 16]?.getD none with
        | some p =>
          SeqEnv (ComputeAtCallEnv p.coefficients.length)
            (DecodedMessageLoopEnv self pointsVecs (i + 1) rem polys)
        | none =>
          let ptsSlice := pointsVecs[i % 16]?.getD []
          let interp := lagrangeInterpolateTotal ptsSlice
          SeqEnv (LagrangeInterpolateMissEnv ptsSlice.length)
            (SeqEnv (ComputeAtCallEnv interp.coefficients.length)
              (DecodedMessageLoopEnv self pointsVecs (i + 1) rem
                (polys.set (i % 16) (some interp)))) := by
  funext evs
  simp only [DecodedMessageLoopEnv]
  cases (self.pts[i % 16]?.getD SortedSetPt.new).binarySearch
      { x := GF16.new (BitVec.ofNat 16 (i / 16)), y := GF16.ZERO }
  · cases polys[i % 16]?.getD none <;> rfl
  · rfl

/-- Loop-invariant `PhaseCreditSpec` for `DecodedMessageLoopEnv`: across `rem` iterations with at most
`m` unpopulated cache entries, `LagrangeInterpolateMissEnv` runs at most `m` times and
`ComputeAtCallEnv` runs at most `rem` times. -/
theorem decodedMessageLoop_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (self : PolyDecoder) (pointsVecs : List (List Pt)) (K : Nat)
    (hSlices : ∀ poly < 16, (pointsVecs[poly]?.getD []).length ≤ K) :
    ∀ (rem i m : Nat) (polys : List (Option Poly)),
      polys.length = 16 →
      polyNoneCount polys ≤ m →
      PolyCacheDegBound K polys →
      PhaseCreditSpec M (DecodedMessageLoopEnv self pointsVecs i rem polys)
        (rem * (4 * K + 19098) + m * (12 * K + 28625))
        (rem * (2 * K + 16400) + m * (6 * K + 24589))
        (rem * (2 * K + 16400) + m * (6 * K + 24589))
        (max 8 (2 * K + 2))
  | 0, _, _, _, _, _, _ =>
    (PhaseCreditSpec.nil M).mono
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  | rem + 1, i, m, polys, hlen, hcnt, hdeg => by
    rw [decodedMessageLoopEnv_succ, Nat.add_one_mul rem, Nat.add_one_mul rem]
    split
    · have hTail := decodedMessageLoop_phaseCreditSpec hM self pointsVecs K hSlices
        rem (i + 1) m polys hlen hcnt hdeg
      exact hTail.mono (by omega) (by omega) (by omega) (Nat.le_refl _)
    · cases hopt : polys[i % 16]?.getD none with
      | some p =>
        dsimp only
        have hp_deg : p.coefficients.length ≤ K :=
          polyCacheDegBound_getD_some polys (i % 16) p hdeg hopt
        have hComp := computeAtCall_phaseCreditSpec hM hp_deg
        have hTail := decodedMessageLoop_phaseCreditSpec hM self pointsVecs K hSlices
          rem (i + 1) m polys hlen hcnt hdeg
        exact (hComp.seq hTail).mono (by omega) (by omega) (by omega) (by omega)
      | none =>
        dsimp only
        have hpoly : i % 16 < 16 := Nat.mod_lt i (by decide)
        have hpoly_lt : i % 16 < polys.length := hlen ▸ hpoly
        let ptsSlice := pointsVecs[i % 16]?.getD []
        let interp := lagrangeInterpolateTotal ptsSlice
        have hslice_le : ptsSlice.length ≤ K := hSlices (i % 16) hpoly
        have hinterp_le : interp.coefficients.length ≤ K :=
          (lagrangeInterpolateTotal_length ptsSlice) ▸ hslice_le
        have hcnt_eq := polyNoneCount_set_some_eq polys (i % 16) interp hpoly_lt hopt
        cases m with
        | zero => omega
        | succ m' =>
          rw [Nat.add_one_mul m', Nat.add_one_mul m']
          have hlen' : (polys.set (i % 16) (some interp)).length = 16 := by simp [hlen]
          have hcnt' : polyNoneCount (polys.set (i % 16) (some interp)) ≤ m' := by omega
          have hdeg' : PolyCacheDegBound K (polys.set (i % 16) (some interp)) :=
            polyCacheDegBound_set_some polys (i % 16) interp hdeg hinterp_le
          have hMiss := lagrangeInterpolateMiss_phaseCreditSpec hM hslice_le
          have hComp := computeAtCall_phaseCreditSpec hM hinterp_le
          have hTail := decodedMessageLoop_phaseCreditSpec hM self pointsVecs K hSlices
            rem (i + 1) m' (polys.set (i % 16) (some interp)) hlen' hcnt' hdeg'
          exact (hMiss.seq (hComp.seq hTail)).mono
            (by omega) (by omega) (by omega) (by omega)

theorem decodedMessageLoop_small_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (self : PolyDecoder) (pointsVecs : List (List Pt)) (K : Nat)
    (hSlices : ∀ poly < 16, (pointsVecs[poly]?.getD []).length ≤ K)
    (hsmall : max 8 (2 * K + 2) ≤ HasFineReallocCredit.smallMaxReq M) :
    ∀ (rem i m : Nat) (polys : List (Option Poly)),
      polys.length = 16 →
      polyNoneCount polys ≤ m →
      PolyCacheDegBound K polys →
      PhaseCreditSpec M (DecodedMessageLoopEnv self pointsVecs i rem polys)
        (rem * (4 * K + 19098) + m * (12 * K + 28625))
        0 0
        (max 8 (2 * K + 2))
  | 0, _, _, _, _, _, _ =>
    (PhaseCreditSpec.nil M).mono
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  | rem + 1, i, m, polys, hlen, hcnt, hdeg => by
    rw [decodedMessageLoopEnv_succ, Nat.add_one_mul rem]
    split
    · have hTail := decodedMessageLoop_small_phaseCreditSpec hM self pointsVecs K hSlices hsmall
        rem (i + 1) m polys hlen hcnt hdeg
      exact hTail.mono (by omega) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl _)
    · cases hopt : polys[i % 16]?.getD none with
      | some p =>
        dsimp only
        have hp_deg : p.coefficients.length ≤ K :=
          polyCacheDegBound_getD_some polys (i % 16) p hdeg hopt
        have hComp := computeAtCall_small_phaseCreditSpec hM hp_deg (by omega)
        have hTail := decodedMessageLoop_small_phaseCreditSpec hM self pointsVecs K hSlices hsmall
          rem (i + 1) m polys hlen hcnt hdeg
        exact (hComp.seq hTail).mono (by omega) (by decide) (by decide) (by omega)
      | none =>
        dsimp only
        have hpoly : i % 16 < 16 := Nat.mod_lt i (by decide)
        have hpoly_lt : i % 16 < polys.length := hlen ▸ hpoly
        let ptsSlice := pointsVecs[i % 16]?.getD []
        let interp := lagrangeInterpolateTotal ptsSlice
        have hslice_le : ptsSlice.length ≤ K := hSlices (i % 16) hpoly
        have hinterp_le : interp.coefficients.length ≤ K :=
          (lagrangeInterpolateTotal_length ptsSlice) ▸ hslice_le
        have hcnt_eq := polyNoneCount_set_some_eq polys (i % 16) interp hpoly_lt hopt
        cases m with
        | zero => omega
        | succ m' =>
          rw [Nat.add_one_mul m']
          have hlen' : (polys.set (i % 16) (some interp)).length = 16 := by simp [hlen]
          have hcnt' : polyNoneCount (polys.set (i % 16) (some interp)) ≤ m' := by omega
          have hdeg' : PolyCacheDegBound K (polys.set (i % 16) (some interp)) :=
            polyCacheDegBound_set_some polys (i % 16) interp hdeg hinterp_le
          have hMiss := lagrangeInterpolateMiss_small_phaseCreditSpec hM hslice_le (by omega)
          have hComp := computeAtCall_small_phaseCreditSpec hM hinterp_le (by omega)
          have hTail := decodedMessageLoop_small_phaseCreditSpec hM self pointsVecs K hSlices hsmall
            rem (i + 1) m' (polys.set (i % 16) (some interp)) hlen' hcnt' hdeg'
          exact (hMiss.seq (hComp.seq hTail)).mono
            (by omega) (by decide) (by decide) (by omega)

/-- Regime-uniform `PhaseCreditSpec` for `<PolyDecoder as Decoder>::decoded_message` under `ModelHyps M`.
-/
theorem decodedMessage_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (dec : PolyDecoder) :
    let K := dec.ptsNeeded / 16 + 1
    PhaseCreditSpec M (DecodedMessageEnv dec)
      (4 * dec.ptsNeeded + 19590 + dec.ptsNeeded * (4 * K + 19098) + 16 * (12 * K + 28625))
      (2 * dec.ptsNeeded + 16646 + dec.ptsNeeded * (2 * K + 16400) + 16 * (6 * K + 24589))
      (2 * dec.ptsNeeded + 16646 + dec.ptsNeeded * (2 * K + 16400) + 16 * (6 * K + 24589))
      (max 256 (max (2 * dec.ptsNeeded) (2 * K + 2))) := by
  intro K
  unfold DecodedMessageEnv
  split
  · exact (PhaseCreditSpec.nil M).mono
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  · split
    · have h256 := PhaseCreditSpec.rustAlloc_aff hM (req := 256) (al := 8) (by decide)
      exact (h256.seq (PhaseCreditSpec.freeOnly_of_hyps hM)).mono
        (by omega) (by omega) (by omega) (by omega)
    · have h256 := PhaseCreditSpec.rustAlloc_aff hM (req := 256) (al := 8) (by decide)
      have hout := PhaseCreditSpec.rustAlloc_aff hM (req := 2 * dec.ptsNeeded) (al := 1) (by decide)
      have hHead := PhaseCreditSpec.append_eq h256 hout
      have hLoop := decodedMessageLoop_phaseCreditSpec hM dec (collectedSlices dec 0 16) K
        (fun poly hpoly => collectedSlices_getD_length_le dec hpoly)
        dec.ptsNeeded 0 16 (List.replicate 16 none)
        (by simp) (by rw [polyNoneCount_replicate_none]) (polyCacheDegBound_replicate_none K 16)
      exact (hHead.seq (hLoop.seq (PhaseCreditSpec.freeOnly_of_hyps hM))).mono
        (by omega) (by omega) (by omega) (by omega)

private theorem decodedMessage_cum_256_le {a n k : Nat} (ha : a ≤ 2 * 256 + 9539) :
    a + 0 ≤ 4 * n + 19590 + n * (4 * k + 19098) + 16 * (12 * k + 28625) := by
  rw [Nat.add_zero]
  have h1 : a ≤ 19590 := Nat.le_trans ha (by decide)
  have h2 : 19590 ≤ 4 * n + 19590 := Nat.le_add_left _ _
  have h3 : 4 * n + 19590 ≤ 4 * n + 19590 + n * (4 * k + 19098) := Nat.le_add_right _ _
  exact Nat.le_trans h1 (Nat.le_trans h2 (Nat.le_trans h3 (Nat.le_add_right _ _)))

private theorem add_head_loop_le_aux {a b n c256 c9539 c19590 R1 R2 : Nat}
    (ha : a ≤ c256) (hb : b ≤ 2 * (2 * n) + c9539) (hc : c256 + c9539 ≤ c19590) :
    a + b + (R1 + R2 + 0) ≤ 4 * n + c19590 + R1 + R2 := by
  have hb' : b ≤ 4 * n + c9539 := by rw [← Nat.mul_assoc] at hb; exact hb
  omega

private theorem decodedMessage_cum_head_loop_le {a b n k : Nat}
    (ha : a ≤ 2 * 256 + 9539) (hb : b ≤ 2 * (2 * n) + 9539) :
    a + b + (n * (4 * k + 19098) + 16 * (12 * k + 28625) + 0) ≤
      4 * n + 19590 + n * (4 * k + 19098) + 16 * (12 * k + 28625) :=
  add_head_loop_le_aux ha hb (by decide)

private theorem quad_linear_le_aux {n K a0 a1 b0 b1 c1 c2 m1 mTotal bTotal cTotal : Nat}
    (hK_b : b0 * K + b1 ≤ m1)
    (hK_c : 16 * (c1 * K + c2) ≤ bTotal)
    (hm : a0 + m1 ≤ mTotal)
    (hc : a1 + bTotal ≤ cTotal) :
    a0 * n + a1 + n * (b0 * K + b1) + 16 * (c1 * K + c2) ≤ mTotal * n + cTotal := by
  have hn1 : n * (b0 * K + b1) ≤ m1 * n := by
    rw [Nat.mul_comm m1 n]
    exact Nat.mul_le_mul_left n hK_b
  have hn2 : a0 * n + m1 * n ≤ mTotal * n := by
    rw [← Nat.add_mul]
    exact Nat.mul_le_mul_right n hm
  omega

private theorem linear_step_le {K kMax b0 b1 m1 : Nat}
    (hK : K ≤ kMax) (h : b0 * kMax + b1 ≤ m1) : b0 * K + b1 ≤ m1 :=
  Nat.le_trans (Nat.add_le_add_right (Nat.mul_le_mul_left b0 hK) b1) h

private theorem linear_step16_le {K kMax c1 c2 bTotal : Nat}
    (hK : K ≤ kMax) (h : 16 * (c1 * kMax + c2) ≤ bTotal) : 16 * (c1 * K + c2) ≤ bTotal :=
  Nat.le_trans (Nat.mul_le_mul_left 16 (Nat.add_le_add_right (Nat.mul_le_mul_left c1 hK) c2)) h

private theorem decodedMessage_cum_le_576 {n : Nat} (hn : n ≤ 576) :
    let K := n / 16 + 1
    4 * n + 19590 + n * (4 * K + 19098) + 16 * (12 * K + 28625) ≤ 19250 * n + 484694 := by
  intro K
  have hK : K ≤ 37 :=
    Nat.le_trans (Nat.add_le_add_right (Nat.div_le_div_right hn) 1) (by decide)
  exact quad_linear_le_aux (m1 := 19246) (bTotal := 465104)
    (linear_step_le hK (by decide))
    (linear_step16_le hK (by decide))
    (by decide)
    (by decide)

private theorem decodedMessage_req_le_576 {n : Nat} (hn : n ≤ 576) :
    max 256 (max (2 * n) (2 * (n / 16 + 1) + 2)) ≤ max 256 (2 * n) := by
  omega

private theorem decodedMessage_sm_le_8195 {n s : Nat} (hn : n ≤ 576) (hs : 8195 ≤ s) :
    max 256 (max (2 * n) (2 * (n / 16 + 1) + 2)) ≤ s := by
  omega

/-- Small-class `PhaseCreditSpec` (`Δlive = Δpeak = 0`) for `DecodedMessageEnv dec`. -/
theorem decodedMessage_small_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (dec : PolyDecoder)
    (hsmall :
      max 256 (max (2 * dec.ptsNeeded) (2 * (dec.ptsNeeded / 16 + 1) + 2)) ≤
        HasFineReallocCredit.smallMaxReq M) :
    let K := dec.ptsNeeded / 16 + 1
    PhaseCreditSpec M (DecodedMessageEnv dec)
      (4 * dec.ptsNeeded + 19590 + dec.ptsNeeded * (4 * K + 19098) + 16 * (12 * K + 28625))
      0 0
      (max 256 (max (2 * dec.ptsNeeded) (2 * K + 2))) := by
  intro K
  have h256_sm : 256 ≤ HasFineReallocCredit.smallMaxReq M :=
    Nat.le_trans (Nat.le_max_left _ _) hsmall
  have hout_sm : 2 * dec.ptsNeeded ≤ HasFineReallocCredit.smallMaxReq M :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hsmall
  have hloop_sm : max 8 (2 * K + 2) ≤ HasFineReallocCredit.smallMaxReq M := by
    have h1 : 8 ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans (by decide) h256_sm
    have h2 : 2 * K + 2 ≤ HasFineReallocCredit.smallMaxReq M :=
      Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hsmall
    exact Nat.max_le.mpr ⟨h1, h2⟩
  have hsa256 := hM.smallAlloc_le h256_sm
  have hsa_out := hM.smallAlloc_le hout_sm
  unfold DecodedMessageEnv
  split
  · exact (PhaseCreditSpec.nil M).mono
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  · split
    · have h256 := PhaseCreditSpec.rustAlloc_small_any hM (req := 256) (al := 8) (by decide) h256_sm
      exact (h256.seq (PhaseCreditSpec.freeOnly_of_hyps hM)).mono
        (decodedMessage_cum_256_le hsa256) (Nat.le_refl 0) (Nat.le_refl 0)
        (Nat.le_trans (Nat.max_le.mpr ⟨Nat.le_refl 256, Nat.zero_le _⟩) (Nat.le_max_left _ _))
    · have h256 := PhaseCreditSpec.rustAlloc_small_any hM (req := 256) (al := 8) (by decide) h256_sm
      have hout := PhaseCreditSpec.rustAlloc_small_any hM (req := 2 * dec.ptsNeeded) (al := 1)
        (by decide) hout_sm
      have hHead := PhaseCreditSpec.append_eq h256 hout
      have hLoop := decodedMessageLoop_small_phaseCreditSpec hM dec (collectedSlices dec 0 16) K
        (fun poly hpoly => collectedSlices_getD_length_le dec hpoly) hloop_sm
        dec.ptsNeeded 0 16 (List.replicate 16 none)
        (by simp) (by rw [polyNoneCount_replicate_none]) (polyCacheDegBound_replicate_none K 16)
      exact (hHead.seq (hLoop.seq (PhaseCreditSpec.freeOnly_of_hyps hM))).mono
        (decodedMessage_cum_head_loop_le hsa256 hsa_out)
        (by decide) (by decide)
        (by clear *- ; omega)

/-- Small-class `PhaseCreditSpec` for `DecodedMessageEnv dec` when `dec.ptsNeeded ≤ 576` and `8195 ≤ smallMaxReq M`.
-/
theorem decodedMessage_ptsNeeded_le_576_phaseCreditSpec
    {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {dec : PolyDecoder}
    (hpts : dec.ptsNeeded ≤ 576)
    (hsmall8k : 8195 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (DecodedMessageEnv dec)
      (19250 * dec.ptsNeeded + 484694) 0 0 (max 256 (2 * dec.ptsNeeded)) :=
  (decodedMessage_small_phaseCreditSpec hM dec
    (decodedMessage_sm_le_8195 hpts hsmall8k)).mono
    (decodedMessage_cum_le_576 hpts) (Nat.le_refl 0) (Nat.le_refl 0)
    (decodedMessage_req_le_576 hpts)

/-! ## `libcruxHmacSha256Events` and `<Ct1SentEkReceived>::send_ct2` -/

theorem libcruxHmacSha256_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) :
    PhaseCreditSpec M (· = libcruxHmacSha256Events) 38604 32992 32992 64 := by
  have h1 := PhaseCreditSpec.tempAllocFree_aff hM (req := 64) (al := 1) (by decide)
  have h2 := PhaseCreditSpec.tempAllocBodyFree_aff hM (req := 64) (al := 1) (by decide) h1
  have h3 := PhaseCreditSpec.tempAllocBodyFree_aff hM (req := 64) (al := 1) (by decide) h2
  have ha32 := PhaseCreditSpec.rustAlloc_aff hM (req := 32) (al := 1) (by decide)
  refine ((h3.concat ha32).of_imp ?_).mono (by decide) (by decide) (by decide) (by decide)
  rintro _ rfl
  refine ⟨((rustAllocEvents 64 1 ++ ((rustAllocEvents 64 1 ++
      (rustAllocEvents 64 1 ++ rustDeallocEvents 64 1)) ++ rustDeallocEvents 64 1)) ++
      rustDeallocEvents 64 1),
    rustAllocEvents 32 1, ?_,
    ⟨_, rustDeallocEvents 64 1, rfl,
      ⟨rustAllocEvents 64 1, _, rfl, rfl,
        ⟨_, rustDeallocEvents 64 1, rfl,
          ⟨rustAllocEvents 64 1, _, rfl, rfl,
            ⟨rustAllocEvents 64 1, rustDeallocEvents 64 1, rfl, rfl, rfl⟩⟩,
          rfl⟩⟩,
      rfl⟩,
    rfl⟩
  unfold libcruxHmacSha256Events
  simp only [List.append_assoc]

theorem libcruxHmacSha256_small_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hsmall : 64 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (· = libcruxHmacSha256Events) 38604 0 0 64 := by
  unfold libcruxHmacSha256Events
  have h32 : 32 ≤ HasFineReallocCredit.smallMaxReq M := by omega
  have hsa64 := hM.smallAlloc_le hsmall
  have hsa32 := hM.smallAlloc_le h32
  have ha64 := PhaseCreditSpec.rustAlloc_small_any hM (req := 64) (al := 1) (by decide) hsmall
  have hd64 := PhaseCreditSpec.rustDealloc_align16 M (req := 64) (al := 1) (by decide)
  have ha32 := PhaseCreditSpec.rustAlloc_small_any hM (req := 32) (al := 1) (by decide) h32
  exact (PhaseCreditSpec.append_eq
    (PhaseCreditSpec.append_eq
      (PhaseCreditSpec.append_eq
        (PhaseCreditSpec.append_eq
          (PhaseCreditSpec.append_eq
            (PhaseCreditSpec.append_eq ha64 ha64) ha64) hd64) hd64) hd64) ha32).mono
    (by omega) (by decide) (by decide) (by decide)

theorem sendCt2Seg23_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (es : Bytes) :
    PhaseCreditSpec M (· = sendCt2Seg23Events es) 23494 8323 18598 2080 := by
  unfold sendCt2Seg23Events sendCt2FlipAllocEvents sendCt2FlipDeallocEvents
  have h128 := PhaseCreditSpec.rustAlloc_aff hM (req := 128) (al := 1) (by decide)
  split
  · have hcancel := PhaseCreditSpec.tempAllocBodyFree_aff hM (req := 2080) (al := 1) (by decide) h128
    refine (hcancel.of_imp fun _ h => ?_).mono (by omega) (by omega) (by omega) (by omega)
    exact ⟨rustAllocEvents 2080 1 ++ rustAllocEvents 128 1, rustDeallocEvents 2080 1, h,
      ⟨rustAllocEvents 2080 1, rustAllocEvents 128 1, rfl, rfl, rfl⟩, rfl⟩
  · simpa only [List.nil_append, List.append_nil] using
      h128.mono (by omega) (by omega) (by omega) (by omega)

theorem sendCt2Reserve128_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (ct1Len : Nat) :
    PhaseCreditSpec M (SendCt2Reserve128Env ct1Len)
      (4 * ct1Len + 10047) (2 * ct1Len + 8449) (2 * ct1Len + 8449) (2 * ct1Len + 254) := by
  refine { req_align := ?_, credit_le := ?_ }
  · rintro evs (rfl | ⟨cap, hlo, hhi, rfl⟩)
    · intro ev hev; nomatch hev
    · have hnew_ge : 1 ≤ reserveCap cap.toNat ct1Len 128 := by dsimp [reserveCap]; omega
      have hnew_le : reserveCap cap.toNat ct1Len 128 ≤ 2 * ct1Len + 254 := by
        dsimp [reserveCap]; omega
      unfold sendCt2Reserve128Events
      dsimp only
      split
      · exact ((PhaseCreditSpec.rustAlloc_aff hM (req := reserveCap cap.toNat ct1Len 128)
          (al := 1) (by decide)).mono
          (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) hnew_le).req_align _ rfl
      · exact ((PhaseCreditSpec.rustRealloc_aff hM (old := cap.toNat)
          (new := reserveCap cap.toNat ct1Len 128) (al := 1) (by decide) hnew_ge).mono
          (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) hnew_le).req_align _ rfl
  · rintro st0 evs (rfl | ⟨cap, hlo, hhi, rfl⟩)
    · exact ((PhaseCreditSpec.nil M).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.le_refl 0)).credit_le st0 rfl
    · have hnew_ge : 1 ≤ reserveCap cap.toNat ct1Len 128 := by dsimp [reserveCap]; omega
      have hnew_le : reserveCap cap.toNat ct1Len 128 ≤ 2 * ct1Len + 254 := by
        dsimp [reserveCap]; omega
      unfold sendCt2Reserve128Events
      dsimp only
      split
      · exact ((PhaseCreditSpec.rustAlloc_aff hM (req := reserveCap cap.toNat ct1Len 128)
          (al := 1) (by decide)).mono (by omega) (by omega) (by omega) hnew_le).credit_le st0 rfl
      · exact ((PhaseCreditSpec.rustRealloc_aff hM (old := cap.toNat)
          (new := reserveCap cap.toNat ct1Len 128) (al := 1) (by decide) hnew_ge).mono
          (by omega) (by omega) (by omega) hnew_le).credit_le st0 rfl

/-- Regime-uniform `PhaseCreditSpec` for `UnchunkedSendCt2Env x`, linear in `x.st.ct1.length`. -/
theorem unchunkedSendCt2_phaseCreditSpec {F : ShaCompress}
    {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (x : UnchunkedSendCt2Ghost F) :
    let L := x.st.ct1.length
    PhaseCreditSpec M (UnchunkedSendCt2Env x)
      (6 * L + 82026) (3 * L + 58130) (3 * L + 68405) (max 2080 (2 * L + 254)) := by
  intro L
  have hSeg23 := sendCt2Seg23_phaseCreditSpec hM x.st.es
  have hRes := sendCt2Reserve128_phaseCreditSpec hM L
  have hConcatHmac :
      PhaseCreditSpec M (· = sendCt2ConcatHmacEvents L)
        (2 * L + 48485) (L + 41358) (L + 41358) (max (L + 171) 64) := by
    unfold sendCt2ConcatHmacEvents
    have hc := PhaseCreditSpec.rustAlloc_aff hM (req := 35 + 8 + (L + 128)) (al := 1) (by decide)
    exact (PhaseCreditSpec.append_eq hc (libcruxHmacSha256_phaseCreditSpec hM)).mono
      (by omega) (by omega) (by omega) (by omega)
  have hPre :
      PhaseCreditSpec M (UnchunkedSendCt2PreEnv x)
        (6 * L + 82026) (3 * L + 58130) (3 * L + 68405) (max 2080 (2 * L + 254)) := by
    refine (((hSeg23.concat hRes).concat hConcatHmac).of_imp ?_).mono
      (by omega) (by omega) (by omega) (by omega)
    rintro evs ⟨evsRes, hResEv, rfl⟩
    exact ⟨sendCt2Seg23Events x.st.es ++ evsRes, sendCt2ConcatHmacEvents L, rfl,
      ⟨sendCt2Seg23Events x.st.es, evsRes, rfl, rfl, hResEv⟩, rfl⟩
  refine ((hPre.concat (PhaseCreditSpec.freeOnly_of_hyps hM)).of_imp ?_).mono
    (by omega) (by omega) (by omega) (by omega)
  rintro evs ⟨evsPre, evsFree, hPreEv, hFreeEv, rfl⟩
  exact ⟨evsPre, evsFree, rfl, hPreEv, hFreeEv⟩

/-! ## Tight Small-Class and `fineCostModel` Credit Helpers -/

/-- Small-target `PhaseCreditSpec` for `rustReallocEvents old new al` (`new ≤ smallMaxReq M`, `Δlive = Δpeak = 0`) across both small and large `old`.
-/
theorem PhaseCreditSpec.rustRealloc_small_exact {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {old new al : Nat} (hal : al ≤ 16) (hal_new : al ≤ new)
    (hnew_le : new ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (· = rustReallocEvents old new al)
      (HasFineReallocCredit.smallReallocCost M new) 0 0 new where
  req_align := by
    rintro _ rfl ev hev
    unfold rustReallocEvents at hev
    simp only [hal, hal_new, and_self, ↓reduceIte, List.mem_singleton] at hev
    subst hev
    exact ⟨Nat.le_refl new, hal⟩
  credit_le := by
    rintro st0 _ rfl
    unfold rustReallocEvents
    simp only [hal, hal_new, and_self, ↓reduceIte,
      AllocCostModel.stepEvents_cons, AllocCostModel.stepEvents_nil]
    by_cases hold_le : old ≤ HasFineReallocCredit.smallMaxReq M
    · obtain ⟨hc, hl, hp⟩ := hM.step_realloc_small_small_any st0 hal hold_le hnew_le
      omega
    · have hold_gt : HasFineReallocCredit.smallMaxReq M < old := by omega
      obtain ⟨hc, hl, hp⟩ := hM.step_realloc_large_small_any st0 hal hold_gt hnew_le
      omega

private def checkFineAllocRange (maxReq bound : Nat) : Bool :=
  (List.range (maxReq + 1)).all fun req => fineSmallAllocCost req ≤ bound

private def checkFineReallocRange (maxSz bound : Nat) : Bool :=
  (List.range (maxSz + 1)).all fun sz => fineSmallReallocCost sz ≤ bound

private theorem checkFineAlloc74_true : checkFineAllocRange 74 1607 = true := by
  decide +kernel

private theorem checkFineAlloc1280_true : checkFineAllocRange 1280 9789 = true := by
  decide +kernel

private theorem checkFineAlloc2430_true : checkFineAllocRange 2430 9789 = true := by
  decide +kernel

private theorem checkFineRealloc296_true : checkFineReallocRange 296 9789 = true := by
  decide +kernel

private theorem checkFineRealloc2430_true : checkFineReallocRange 2430 10747 = true := by
  decide +kernel

private theorem checkFineRealloc4608_true : checkFineReallocRange 4608 12925 = true := by
  decide +kernel

private theorem checkFineRealloc5120_true : checkFineReallocRange 5120 13440 = true := by
  decide +kernel

theorem fineSmallAllocCost_160 :
    HasFineReallocCredit.smallAllocCost fineCostModel 160 = 9137 := by
  change fineSmallAllocCost 160 = 9137
  decide +kernel

theorem fineSmallAllocCost_1152 :
    HasFineReallocCredit.smallAllocCost fineCostModel 1152 = 2109 := by
  change fineSmallAllocCost 1152 = 2109
  decide +kernel

theorem fineSmallAllocCost_2080 :
    HasFineReallocCredit.smallAllocCost fineCostModel 2080 = 4218 := by
  change fineSmallAllocCost 2080 = 4218
  decide +kernel

theorem fineSmallReallocCost_8 :
    HasFineReallocCredit.smallReallocCost fineCostModel 8 = 8325 := by
  change fineSmallReallocCost 8 = 8325
  decide +kernel

theorem fineSmallAllocCost_le_1607_of_le_74 {req : Nat} (h : req ≤ 74) :
    HasFineReallocCredit.smallAllocCost fineCostModel req ≤ 1607 := by
  change fineSmallAllocCost req ≤ 1607
  have hmem : req ∈ List.range 75 := List.mem_range.mpr (by omega)
  exact of_decide_eq_true (List.all_eq_true.mp checkFineAlloc74_true req hmem)

theorem fineSmallAllocCost_le_9789_of_le_1280 {req : Nat} (h : req ≤ 1280) :
    HasFineReallocCredit.smallAllocCost fineCostModel req ≤ 9789 := by
  change fineSmallAllocCost req ≤ 9789
  have hmem : req ∈ List.range 1281 := List.mem_range.mpr (by omega)
  exact of_decide_eq_true (List.all_eq_true.mp checkFineAlloc1280_true req hmem)

theorem fineSmallAllocCost_le_9789_of_le_2430 {req : Nat} (h : req ≤ 2430) :
    HasFineReallocCredit.smallAllocCost fineCostModel req ≤ 9789 := by
  change fineSmallAllocCost req ≤ 9789
  have hmem : req ∈ List.range 2431 := List.mem_range.mpr (by omega)
  exact of_decide_eq_true (List.all_eq_true.mp checkFineAlloc2430_true req hmem)

theorem fineSmallReallocCost_le_9789_of_le_296 {newSz : Nat} (h : newSz ≤ 296) :
    HasFineReallocCredit.smallReallocCost fineCostModel newSz ≤ 9789 := by
  change fineSmallReallocCost newSz ≤ 9789
  have hmem : newSz ∈ List.range 297 := List.mem_range.mpr (by omega)
  exact of_decide_eq_true (List.all_eq_true.mp checkFineRealloc296_true newSz hmem)

theorem fineSmallReallocCost_le_10747_of_le_2430 {newSz : Nat} (h : newSz ≤ 2430) :
    HasFineReallocCredit.smallReallocCost fineCostModel newSz ≤ 10747 := by
  change fineSmallReallocCost newSz ≤ 10747
  have hmem : newSz ∈ List.range 2431 := List.mem_range.mpr (by omega)
  exact of_decide_eq_true (List.all_eq_true.mp checkFineRealloc2430_true newSz hmem)

theorem fineSmallReallocCost_le_12925_of_le_4608 {newSz : Nat} (h : newSz ≤ 4608) :
    HasFineReallocCredit.smallReallocCost fineCostModel newSz ≤ 12925 := by
  change fineSmallReallocCost newSz ≤ 12925
  have hmem : newSz ∈ List.range 4609 := List.mem_range.mpr (by omega)
  exact of_decide_eq_true (List.all_eq_true.mp checkFineRealloc4608_true newSz hmem)

theorem fineSmallReallocCost_le_13440_of_le_5120 {newSz : Nat} (h : newSz ≤ 5120) :
    HasFineReallocCredit.smallReallocCost fineCostModel newSz ≤ 13440 := by
  change fineSmallReallocCost newSz ≤ 13440
  have hmem : newSz ∈ List.range 5121 := List.mem_range.mpr (by omega)
  exact of_decide_eq_true (List.all_eq_true.mp checkFineRealloc5120_true newSz hmem)

/-- Small-class `PhaseCreditSpec` for `<PolyEncoder as Encoder>::encode_bytes` (`Δlive = Δpeak = 0`).
-/
theorem encodeBytes_small_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {msgLen : Nat}
    (hsmall : msgLen ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (EncodeBytesEnv msgLen)
      (16 * HasFineReallocCredit.smallAllocCost M msgLen) 0 0 msgLen := by
  unfold EncodeBytesEnv encodeBytesAllocEvents
  split
  · have hstep := PhaseCreditSpec.rustAlloc_small_any hM (req := msgLen) (al := 2)
      (by decide) hsmall
    have hrep :
        ∀ n : Nat,
          PhaseCreditSpec M (· = (List.replicate n (rustAllocEvents msgLen 2)).flatten)
            (n * HasFineReallocCredit.smallAllocCost M msgLen) 0 0 msgLen := by
      intro n
      induction n with
      | zero =>
        simpa using (PhaseCreditSpec.nil M).mono
          (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)
      | succ n ih =>
        rw [List.replicate_succ, List.flatten_cons, Nat.add_one_mul]
        exact (PhaseCreditSpec.append_eq hstep ih).mono
          (by omega) (by decide) (by decide) (by omega)
    exact hrep 16
  · exact (PhaseCreditSpec.nil M).mono
      (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)

theorem encodeBytes_fine_1152_phaseCreditSpec :
    PhaseCreditSpec fineCostModel (EncodeBytesEnv 1152) 33744 0 0 1152 := by
  have h := encodeBytes_small_phaseCreditSpec fineCostModel_modelHyps (msgLen := 1152)
    (by rw [fineCostModel_smallMaxReq_eq]; decide)
  rw [fineSmallAllocCost_1152] at h
  exact h.mono (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 1152)

theorem encodeBytes_fine_160_phaseCreditSpec :
    PhaseCreditSpec fineCostModel (EncodeBytesEnv 160) 146192 0 0 160 := by
  have h := encodeBytes_small_phaseCreditSpec fineCostModel_modelHyps (msgLen := 160)
    (by rw [fineCostModel_smallMaxReq_eq]; decide)
  rw [fineSmallAllocCost_160] at h
  exact h.mono (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 160)

theorem encodeBytes_fine_le_1280_phaseCreditSpec {msgLen : Nat} (hle : msgLen ≤ 1280) :
    PhaseCreditSpec fineCostModel (EncodeBytesEnv msgLen) 156624 0 0 1280 := by
  have hsm : msgLen ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; omega
  have hc : 16 * HasFineReallocCredit.smallAllocCost fineCostModel msgLen ≤ 156624 := by
    have h1 := fineSmallAllocCost_le_9789_of_le_1280 hle
    omega
  exact (encodeBytes_small_phaseCreditSpec fineCostModel_modelHyps hsm).mono
    hc (Nat.le_refl 0) (Nat.le_refl 0) hle

private theorem addChunkSlot_fine_empty_phaseCreditSpec :
    PhaseCreditSpec fineCostModel (AddChunkSlotEnv SortedSetPt.new) 488 0 0 16 := by
  unfold AddChunkSlotEnv
  have hlen : SortedSetPt.new.vec.length = 0 := rfl
  rw [hlen]
  unfold growOnePtEvents
  have h16 := PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps (req := 16) (al := 2)
    (by decide) (by rw [fineCostModel_smallMaxReq_eq]; decide)
  have hc := smallAllocCost_le_488_of_le_28 (req := 16) (by decide)
  exact ((PhaseCreditSpec.nil fineCostModel).or h16).mono
    (by omega) (by decide) (by decide) (by decide)

theorem addChunkSlots_fine_replicate16_phaseCreditSpec :
    PhaseCreditSpec fineCostModel (AddChunkSlotsEnv (List.replicate 16 SortedSetPt.new))
      7808 0 0 16 := by
  have hrep :
      ∀ n : Nat,
        PhaseCreditSpec fineCostModel (AddChunkSlotsEnv (List.replicate n SortedSetPt.new))
          (488 * n) 0 0 16 := by
    intro n
    induction n with
    | zero =>
      exact (PhaseCreditSpec.nil fineCostModel).mono
        (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)
    | succ n ih =>
      dsimp only [List.replicate_succ, AddChunkSlotsEnv]
      exact (addChunkSlot_fine_empty_phaseCreditSpec.seq ih).mono
        (by omega) (by decide) (by decide) (by decide)
  exact (hrep 16).mono (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 16)

private theorem addChunkSlot_fine_576_phaseCreditSpec {s : SortedSetPt}
    (hs : s.vec.length ≤ 576) :
    PhaseCreditSpec fineCostModel (AddChunkSlotEnv s) 12925 0 0 4608 := by
  unfold AddChunkSlotEnv
  have hgrow : PhaseCreditSpec fineCostModel (· = growOnePtEvents s.vec.length) 12925 0 0 4608 := by
    unfold growOnePtEvents
    split
    · have h16 := PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps (req := 16) (al := 2)
        (by decide) (by rw [fineCostModel_smallMaxReq_eq]; decide)
      have hc := smallAllocCost_le_488_of_le_28 (req := 16) (by decide)
      exact h16.mono (by omega) (Nat.le_refl 0) (Nat.le_refl 0) (by decide)
    · have hal_new : 2 ≤ 4 * max (2 * s.vec.length) 4 := by omega
      have hnew_4608 : 4 * max (2 * s.vec.length) 4 ≤ 4608 := by omega
      have hnew_sm :
          4 * max (2 * s.vec.length) 4 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
        rw [fineCostModel_smallMaxReq_eq]; omega
      have hc := fineSmallReallocCost_le_12925_of_le_4608 hnew_4608
      exact (PhaseCreditSpec.rustRealloc_small_exact fineCostModel_modelHyps
        (old := 4 * s.vec.length) (new := 4 * max (2 * s.vec.length) 4) (al := 2)
        (by decide) hal_new hnew_sm).mono hc (Nat.le_refl 0) (Nat.le_refl 0) hnew_4608
  exact ((PhaseCreditSpec.nil fineCostModel).or hgrow).mono
    (by decide) (by decide) (by decide) (by decide)

theorem addChunkSlots_fine_576_phaseCreditSpec {pts : List SortedSetPt}
    (hlen : pts.length ≤ 16) (hpts : ∀ s ∈ pts, s.vec.length ≤ 576) :
    PhaseCreditSpec fineCostModel (AddChunkSlotsEnv pts) 206800 0 0 4608 := by
  have hall :
      ∀ (xs : List SortedSetPt),
        (∀ s ∈ xs, s.vec.length ≤ 576) →
        PhaseCreditSpec fineCostModel (AddChunkSlotsEnv xs) (12925 * xs.length) 0 0 4608 := by
    intro xs hxs
    induction xs with
    | nil =>
      exact (PhaseCreditSpec.nil fineCostModel).mono
        (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)
    | cons s rest ih =>
      dsimp only [AddChunkSlotsEnv]
      have h1 := addChunkSlot_fine_576_phaseCreditSpec (hxs s List.mem_cons_self)
      have h2 := ih (fun t ht => hxs t (List.mem_cons_of_mem s ht))
      refine (h1.seq h2).mono ?_ (by decide) (by decide) (by decide)
      simp only [List.length_cons]
      omega
  have hc : 12925 * pts.length ≤ 206800 := by omega
  exact (hall pts hpts).mono hc (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 4608)

private theorem addChunkSlot_fine_640_phaseCreditSpec {s : SortedSetPt}
    (hs : s.vec.length ≤ 640) :
    PhaseCreditSpec fineCostModel (AddChunkSlotEnv s) 13440 0 0 5120 := by
  unfold AddChunkSlotEnv
  have hgrow : PhaseCreditSpec fineCostModel (· = growOnePtEvents s.vec.length) 13440 0 0 5120 := by
    unfold growOnePtEvents
    split
    · have h16 := PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps (req := 16) (al := 2)
        (by decide) (by rw [fineCostModel_smallMaxReq_eq]; decide)
      have hc := smallAllocCost_le_488_of_le_28 (req := 16) (by decide)
      exact h16.mono (by omega) (Nat.le_refl 0) (Nat.le_refl 0) (by decide)
    · have hal_new : 2 ≤ 4 * max (2 * s.vec.length) 4 := by omega
      have hnew_5120 : 4 * max (2 * s.vec.length) 4 ≤ 5120 := by omega
      have hnew_sm :
          4 * max (2 * s.vec.length) 4 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
        rw [fineCostModel_smallMaxReq_eq]; omega
      have hc := fineSmallReallocCost_le_13440_of_le_5120 hnew_5120
      exact (PhaseCreditSpec.rustRealloc_small_exact fineCostModel_modelHyps
        (old := 4 * s.vec.length) (new := 4 * max (2 * s.vec.length) 4) (al := 2)
        (by decide) hal_new hnew_sm).mono hc (Nat.le_refl 0) (Nat.le_refl 0) hnew_5120
  exact ((PhaseCreditSpec.nil fineCostModel).or hgrow).mono
    (by decide) (by decide) (by decide) (by decide)

theorem addChunkSlots_fine_640_phaseCreditSpec {pts : List SortedSetPt}
    (hlen : pts.length ≤ 16) (hpts : ∀ s ∈ pts, s.vec.length ≤ 640) :
    PhaseCreditSpec fineCostModel (AddChunkSlotsEnv pts) 215040 0 0 5120 := by
  have hall :
      ∀ (xs : List SortedSetPt),
        (∀ s ∈ xs, s.vec.length ≤ 640) →
        PhaseCreditSpec fineCostModel (AddChunkSlotsEnv xs) (13440 * xs.length) 0 0 5120 := by
    intro xs hxs
    induction xs with
    | nil =>
      exact (PhaseCreditSpec.nil fineCostModel).mono
        (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)
    | cons s rest ih =>
      dsimp only [AddChunkSlotsEnv]
      have h1 := addChunkSlot_fine_640_phaseCreditSpec (hxs s List.mem_cons_self)
      have h2 := ih (fun t ht => hxs t (List.mem_cons_of_mem s ht))
      refine (h1.seq h2).mono ?_ (by decide) (by decide) (by decide)
      simp only [List.length_cons]
      omega
  have hc : 13440 * pts.length ≤ 215040 := by omega
  exact (hall pts hpts).mono hc (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 5120)

private theorem addChunkSlot_fine_raw_phaseCreditSpec {s : SortedSetPt}
    (hsmall : 8 * s.vec.length + 16 ≤ 135167) :
    PhaseCreditSpec fineCostModel (AddChunkSlotEnv s)
      (8 * s.vec.length + 26381) 0 0 (8 * s.vec.length + 16) := by
  unfold AddChunkSlotEnv
  have hgrow :
      PhaseCreditSpec fineCostModel (· = growOnePtEvents s.vec.length)
        (8 * s.vec.length + 26381) 0 0 (8 * s.vec.length + 16) := by
    unfold growOnePtEvents
    split
    · have h16 := PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps (req := 16) (al := 2)
        (by decide) (by rw [fineCostModel_smallMaxReq_eq]; decide)
      have hc := smallAllocCost_le_488_of_le_28 (req := 16) (by decide)
      exact h16.mono (by omega) (Nat.le_refl 0) (Nat.le_refl 0) (by omega)
    · have hal_new : 2 ≤ 4 * max (2 * s.vec.length) 4 := by omega
      have hnew_le : 4 * max (2 * s.vec.length) 4 ≤ 8 * s.vec.length + 16 := by omega
      have hnew_sm :
          4 * max (2 * s.vec.length) 4 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
        rw [fineCostModel_smallMaxReq_eq]; omega
      have hc := smallReallocCost_le_add_26365 (4 * max (2 * s.vec.length) 4)
      exact (PhaseCreditSpec.rustRealloc_small_exact fineCostModel_modelHyps
        (old := 4 * s.vec.length) (new := 4 * max (2 * s.vec.length) 4) (al := 2)
        (by decide) hal_new hnew_sm).mono (by omega) (Nat.le_refl 0) (Nat.le_refl 0) hnew_le
  exact ((PhaseCreditSpec.nil fineCostModel).or hgrow).mono
    (by omega) (by decide) (by decide) (by omega)

theorem addChunkSlots_fine_raw_phaseCreditSpec :
    ∀ (pts : List SortedSetPt),
      8 * ptsLenSum pts + 16 ≤ 135167 →
      PhaseCreditSpec fineCostModel (AddChunkSlotsEnv pts)
        (8 * ptsLenSum pts + 26381 * pts.length) 0 0 (8 * ptsLenSum pts + 16)
  | [], _ =>
    (PhaseCreditSpec.nil fineCostModel).mono
      (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)
  | s :: rest, hsm => by
    dsimp only [AddChunkSlotsEnv]
    have hsum : ptsLenSum (s :: rest) = s.vec.length + ptsLenSum rest := by
      simp [ptsLenSum]
    have hs_sm : 8 * s.vec.length + 16 ≤ 135167 := by omega
    have hrest_sm : 8 * ptsLenSum rest + 16 ≤ 135167 := by omega
    have h1 := addChunkSlot_fine_raw_phaseCreditSpec hs_sm
    have h2 := addChunkSlots_fine_raw_phaseCreditSpec rest hrest_sm
    refine (h1.seq h2).mono ?_ (by decide) (by decide) ?_
    · simp only [List.length_cons, hsum]
      omega
    · rw [hsum]
      omega

/-- Small-class `PhaseCreditSpec` for `ComputeAtCallEnv len` when `2 ≤ len` (avoiding the `len = 1` temporary 8-byte `realloc`).
-/
theorem computeAtCall_small_exact_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {len : Nat} (hge2 : 2 ≤ len)
    (hsmall : 2 * len ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (ComputeAtCallEnv len)
      (HasFineReallocCredit.smallAllocCost M (2 * len)) 0 0 (2 * len) := by
  unfold ComputeAtCallEnv
  have h0 : ¬ (len = 0) := by omega
  have h1 : ¬ (len = 1) := by omega
  have halloc :
      PhaseCreditSpec M (· = computeAtAllocEvents len)
        (HasFineReallocCredit.smallAllocCost M (2 * len)) 0 0 (2 * len) := by
    unfold computeAtAllocEvents
    simp only [h0, h1, ↓reduceIte]
    exact PhaseCreditSpec.rustAlloc_small_any hM (req := 2 * len) (al := 2) (by decide) hsmall
  exact (halloc.seq (PhaseCreditSpec.freeOnly_of_hyps hM)).mono
    (by omega) (by decide) (by decide) (by omega)

theorem computeAtCall_fine_ge2_le36_phaseCreditSpec {len : Nat}
    (hge2 : 2 ≤ len) (hle36 : len ≤ 36) :
    PhaseCreditSpec fineCostModel (ComputeAtCallEnv len) 1607 0 0 72 := by
  have hsm : 2 * len ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; omega
  have hc := fineSmallAllocCost_le_1607_of_le_74 (req := 2 * len) (by omega)
  exact (computeAtCall_small_exact_phaseCreditSpec fineCostModel_modelHyps hge2 hsm).mono
    hc (Nat.le_refl 0) (Nat.le_refl 0) (by omega)

theorem computeAtCall_fine_le2_phaseCreditSpec {len : Nat} (hle2 : len ≤ 2) :
    PhaseCreditSpec fineCostModel (ComputeAtCallEnv len) 8513 0 0 8 := by
  unfold ComputeAtCallEnv
  have halloc : PhaseCreditSpec fineCostModel (· = computeAtAllocEvents len) 8513 0 0 8 := by
    unfold computeAtAllocEvents
    split
    · have h8 := PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps (req := 8) (al := 2)
        (by decide) (by rw [fineCostModel_smallMaxReq_eq]; decide)
      have hc := smallAllocCost_eq_188_of_le_12 (req := 8) (by decide)
      exact h8.mono (by omega) (Nat.le_refl 0) (Nat.le_refl 0) (by decide)
    · split
      · have h1 := PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps (req := 2) (al := 2)
          (by decide) (by rw [fineCostModel_smallMaxReq_eq]; decide)
        have h2 := PhaseCreditSpec.rustRealloc_small_exact fineCostModel_modelHyps
          (old := 2) (new := 8) (al := 2) (by decide) (by decide)
          (by rw [fineCostModel_smallMaxReq_eq]; decide)
        have hc1 := smallAllocCost_eq_188_of_le_12 (req := 2) (by decide)
        have hc2 := fineSmallReallocCost_8
        exact (PhaseCreditSpec.append_eq h1 h2).mono
          (by omega) (by decide) (by decide) (by decide)
      · have h2l : 2 * len ≤ 4 := by omega
        have h := PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps
          (req := 2 * len) (al := 2) (by decide) (by rw [fineCostModel_smallMaxReq_eq]; omega)
        have hc := smallAllocCost_eq_188_of_le_12 (req := 2 * len) (by omega)
        exact h.mono (by omega) (Nat.le_refl 0) (Nat.le_refl 0) (by omega)
  exact (halloc.seq (PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps)).mono
    (by omega) (by decide) (by decide) (by omega)

theorem lagrangeInterpolateMiss_fine_ge2_le36_phaseCreditSpec {k : Nat}
    (_hge2 : 2 ≤ k) (hle36 : k ≤ 36) :
    PhaseCreditSpec fineCostModel (LagrangeInterpolateMissEnv k) 4821 0 0 74 := by
  unfold LagrangeInterpolateMissEnv
  have hk_sm : 2 * k ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; omega
  have hk1_sm : 2 * (k + 1) ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; omega
  have hc0 := fineSmallAllocCost_le_1607_of_le_74 (req := 2 * k) (by omega)
  have hc1 := fineSmallAllocCost_le_1607_of_le_74 (req := 2 * (k + 1)) (by omega)
  have h1 := PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps
    (req := 2 * k) (al := 2) (by decide) hk_sm
  have h2 := PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps
    (req := 2 * (k + 1)) (al := 2) (by decide) hk1_sm
  have halloc := PhaseCreditSpec.append_eq (PhaseCreditSpec.append_eq h1 h2) h2
  exact (halloc.seq (PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps)).mono
    (by omega) (by decide) (by decide) (by omega)

theorem lagrangeInterpolateMiss_fine_le2_phaseCreditSpec {k : Nat} (hle2 : k ≤ 2) :
    PhaseCreditSpec fineCostModel (LagrangeInterpolateMissEnv k) 564 0 0 6 := by
  unfold LagrangeInterpolateMissEnv
  have hk_sm : 2 * k ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; omega
  have hk1_sm : 2 * (k + 1) ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; omega
  have hc0 := smallAllocCost_eq_188_of_le_12 (req := 2 * k) (by omega)
  have hc1 := smallAllocCost_eq_188_of_le_12 (req := 2 * (k + 1)) (by omega)
  have h1 := PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps
    (req := 2 * k) (al := 2) (by decide) hk_sm
  have h2 := PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps
    (req := 2 * (k + 1)) (al := 2) (by decide) hk1_sm
  have halloc := PhaseCreditSpec.append_eq (PhaseCreditSpec.append_eq h1 h2) h2
  exact (halloc.seq (PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps)).mono
    (by omega) (by decide) (by decide) (by omega)

/-- Two-sided coefficient-length invariant `[lo, hi]` on populated entries of the 16-slot `polys` cache.
-/
def PolyCacheRangeBound (lo hi : Nat) : List (Option Poly) → Prop
  | [] => True
  | none :: tl => PolyCacheRangeBound lo hi tl
  | some p :: tl =>
    (lo ≤ p.coefficients.length ∧ p.coefficients.length ≤ hi) ∧ PolyCacheRangeBound lo hi tl

private theorem polyCacheRangeBound_replicate_none (lo hi : Nat) :
    ∀ n : Nat, PolyCacheRangeBound lo hi (List.replicate n none)
  | 0 => trivial
  | n + 1 => polyCacheRangeBound_replicate_none lo hi n

private theorem polyCacheRangeBound_getD_some {lo hi : Nat} :
    ∀ (polys : List (Option Poly)) (idx : Nat) (p : Poly),
      PolyCacheRangeBound lo hi polys →
      polys[idx]?.getD none = some p →
      lo ≤ p.coefficients.length ∧ p.coefficients.length ≤ hi
  | [], _, _, _, hget => by simp at hget
  | none :: _, 0, _, _, hget => by simp at hget
  | some _ :: _, 0, p, hdeg, hget => by
    simp only [List.getElem?_cons_zero, Option.getD_some, Option.some.injEq] at hget
    subst hget
    exact hdeg.1
  | none :: tl, idx + 1, p, hdeg, hget => by
    simp only [List.getElem?_cons_succ] at hget
    exact polyCacheRangeBound_getD_some tl idx p hdeg hget
  | some _ :: tl, idx + 1, p, hdeg, hget => by
    simp only [List.getElem?_cons_succ] at hget
    exact polyCacheRangeBound_getD_some tl idx p hdeg.2 hget

private theorem polyCacheRangeBound_set_some {lo hi : Nat} :
    ∀ (polys : List (Option Poly)) (idx : Nat) (p : Poly),
      PolyCacheRangeBound lo hi polys →
      lo ≤ p.coefficients.length ∧ p.coefficients.length ≤ hi →
      PolyCacheRangeBound lo hi (polys.set idx (some p))
  | [], _, _, _, _ => trivial
  | none :: _, 0, _, hdeg, hp => ⟨hp, hdeg⟩
  | some _ :: _, 0, _, hdeg, hp => ⟨hp, hdeg.2⟩
  | none :: tl, idx + 1, p, hdeg, hp =>
    polyCacheRangeBound_set_some tl idx p hdeg hp
  | some _ :: tl, idx + 1, p, hdeg, hp =>
    ⟨hdeg.1, polyCacheRangeBound_set_some tl idx p hdeg.2 hp⟩

private theorem decodedMessageLoop_fine_ge2_le36_phaseCreditSpec
    (self : PolyDecoder) (pointsVecs : List (List Pt))
    (hSlices : ∀ poly < 16,
      2 ≤ (pointsVecs[poly]?.getD []).length ∧ (pointsVecs[poly]?.getD []).length ≤ 36) :
    ∀ (rem i m : Nat) (polys : List (Option Poly)),
      polys.length = 16 →
      polyNoneCount polys ≤ m →
      PolyCacheRangeBound 2 36 polys →
      PhaseCreditSpec fineCostModel (DecodedMessageLoopEnv self pointsVecs i rem polys)
        (1607 * rem + 4821 * m) 0 0 74
  | 0, _, _, _, _, _, _ =>
    (PhaseCreditSpec.nil fineCostModel).mono
      (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)
  | rem + 1, i, m, polys, hlen, hcnt, hdeg => by
    rw [decodedMessageLoopEnv_succ]
    split
    · have hTail := decodedMessageLoop_fine_ge2_le36_phaseCreditSpec self pointsVecs hSlices
        rem (i + 1) m polys hlen hcnt hdeg
      exact hTail.mono (by omega) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 74)
    · cases hopt : polys[i % 16]?.getD none with
      | some p =>
        dsimp only
        obtain ⟨hp_lo, hp_hi⟩ := polyCacheRangeBound_getD_some polys (i % 16) p hdeg hopt
        have hComp := computeAtCall_fine_ge2_le36_phaseCreditSpec hp_lo hp_hi
        have hTail := decodedMessageLoop_fine_ge2_le36_phaseCreditSpec self pointsVecs hSlices
          rem (i + 1) m polys hlen hcnt hdeg
        exact (hComp.seq hTail).mono (by omega) (by decide) (by decide) (by decide)
      | none =>
        dsimp only
        have hpoly : i % 16 < 16 := Nat.mod_lt i (by decide)
        have hpoly_lt : i % 16 < polys.length := hlen ▸ hpoly
        let ptsSlice := pointsVecs[i % 16]?.getD []
        let interp := lagrangeInterpolateTotal ptsSlice
        obtain ⟨hsl_lo, hsl_hi⟩ := hSlices (i % 16) hpoly
        have hint_eq := lagrangeInterpolateTotal_length ptsSlice
        have hint_lo : 2 ≤ interp.coefficients.length := hint_eq ▸ hsl_lo
        have hint_hi : interp.coefficients.length ≤ 36 := hint_eq ▸ hsl_hi
        have hcnt_eq := polyNoneCount_set_some_eq polys (i % 16) interp hpoly_lt hopt
        cases m with
        | zero => omega
        | succ m' =>
          have hlen' : (polys.set (i % 16) (some interp)).length = 16 := by simp [hlen]
          have hcnt' : polyNoneCount (polys.set (i % 16) (some interp)) ≤ m' := by omega
          have hdeg' : PolyCacheRangeBound 2 36 (polys.set (i % 16) (some interp)) :=
            polyCacheRangeBound_set_some polys (i % 16) interp hdeg ⟨hint_lo, hint_hi⟩
          have hMiss := lagrangeInterpolateMiss_fine_ge2_le36_phaseCreditSpec hsl_lo hsl_hi
          have hComp := computeAtCall_fine_ge2_le36_phaseCreditSpec hint_lo hint_hi
          have hTail := decodedMessageLoop_fine_ge2_le36_phaseCreditSpec self pointsVecs hSlices
            rem (i + 1) m' (polys.set (i % 16) (some interp)) hlen' hcnt' hdeg'
          exact (hMiss.seq (hComp.seq hTail)).mono
            (by omega) (by decide) (by decide) (by decide)

private theorem decodedMessageLoop_fine_le2_phaseCreditSpec
    (self : PolyDecoder) (pointsVecs : List (List Pt))
    (hSlices : ∀ poly < 16, (pointsVecs[poly]?.getD []).length ≤ 2) :
    ∀ (rem i m : Nat) (polys : List (Option Poly)),
      polys.length = 16 →
      polyNoneCount polys ≤ m →
      PolyCacheDegBound 2 polys →
      PhaseCreditSpec fineCostModel (DecodedMessageLoopEnv self pointsVecs i rem polys)
        (8513 * rem + 564 * m) 0 0 8
  | 0, _, _, _, _, _, _ =>
    (PhaseCreditSpec.nil fineCostModel).mono
      (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)
  | rem + 1, i, m, polys, hlen, hcnt, hdeg => by
    rw [decodedMessageLoopEnv_succ]
    split
    · have hTail := decodedMessageLoop_fine_le2_phaseCreditSpec self pointsVecs hSlices
        rem (i + 1) m polys hlen hcnt hdeg
      exact hTail.mono (by omega) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 8)
    · cases hopt : polys[i % 16]?.getD none with
      | some p =>
        dsimp only
        have hp_hi : p.coefficients.length ≤ 2 :=
          polyCacheDegBound_getD_some polys (i % 16) p hdeg hopt
        have hComp := computeAtCall_fine_le2_phaseCreditSpec hp_hi
        have hTail := decodedMessageLoop_fine_le2_phaseCreditSpec self pointsVecs hSlices
          rem (i + 1) m polys hlen hcnt hdeg
        exact (hComp.seq hTail).mono (by omega) (by decide) (by decide) (by decide)
      | none =>
        dsimp only
        have hpoly : i % 16 < 16 := Nat.mod_lt i (by decide)
        have hpoly_lt : i % 16 < polys.length := hlen ▸ hpoly
        let ptsSlice := pointsVecs[i % 16]?.getD []
        let interp := lagrangeInterpolateTotal ptsSlice
        have hsl_hi : ptsSlice.length ≤ 2 := hSlices (i % 16) hpoly
        have hint_hi : interp.coefficients.length ≤ 2 :=
          (lagrangeInterpolateTotal_length ptsSlice) ▸ hsl_hi
        have hcnt_eq := polyNoneCount_set_some_eq polys (i % 16) interp hpoly_lt hopt
        cases m with
        | zero => omega
        | succ m' =>
          have hlen' : (polys.set (i % 16) (some interp)).length = 16 := by simp [hlen]
          have hcnt' : polyNoneCount (polys.set (i % 16) (some interp)) ≤ m' := by omega
          have hdeg' : PolyCacheDegBound 2 (polys.set (i % 16) (some interp)) :=
            polyCacheDegBound_set_some polys (i % 16) interp hdeg hint_hi
          have hMiss := lagrangeInterpolateMiss_fine_le2_phaseCreditSpec hsl_hi
          have hComp := computeAtCall_fine_le2_phaseCreditSpec hint_hi
          have hTail := decodedMessageLoop_fine_le2_phaseCreditSpec self pointsVecs hSlices
            rem (i + 1) m' (polys.set (i % 16) (some interp)) hlen' hcnt' hdeg'
          exact (hMiss.seq (hComp.seq hTail)).mono
            (by omega) (by decide) (by decide) (by decide)

private theorem collectedSlices_getD_range_ge32_le576 {dec : PolyDecoder}
    (hfst : (collectPointsVecsTotal dec 0 16 false []).1 = false)
    (hge32 : 32 ≤ dec.ptsNeeded) (hle576 : dec.ptsNeeded ≤ 576)
    {poly : Nat} (hpoly : poly < 16) :
    2 ≤ ((collectedSlices dec 0 16)[poly]?.getD []).length ∧
      ((collectedSlices dec 0 16)[poly]?.getD []).length ≤ 36 := by
  have hlen : (collectedSlices dec 0 16).length = 16 := collectedSlices_length dec 16 0
  have hpoly' : poly < (collectedSlices dec 0 16).length := hlen ▸ hpoly
  rw [List.getElem?_eq_getElem hpoly', Option.getD_some, collectedSlices_getElem dec 16 0 poly hpoly,
    Nat.zero_add, List.length_take]
  have hnec_le : dec.necessaryPoints poly ≤ (dec.pts[poly]?.getD SortedSetPt.new).len :=
    (collectPointsVecsTotal_of_fst_false dec 16 0 false [] hfst).2.2 poly (by omega) (by omega)
  have hnec_lo : 2 ≤ dec.necessaryPoints poly := by
    unfold PolyDecoder.necessaryPoints
    dsimp only
    split <;> omega
  have hnec_hi : dec.necessaryPoints poly ≤ 36 := by
    unfold PolyDecoder.necessaryPoints
    dsimp only
    split <;> omega
  dsimp only [SortedSetPt.asSlice, SortedSetPt.len] at hnec_le ⊢
  omega

/-- `PhaseCreditSpec` (`Δcum = 1,022,346`, `Δlive = Δpeak = 0`) on `fineCostModel` for `DecodedMessageEnv dec` when `dec.ptsNeeded ≤ 576`.
-/
theorem decodedMessage_fine_tight_phaseCreditSpec {dec : PolyDecoder}
    (hpts : dec.ptsNeeded ≤ 576) :
    PhaseCreditSpec fineCostModel (DecodedMessageEnv dec)
      1022346 0 0 (max 256 (2 * dec.ptsNeeded)) := by
  unfold DecodedMessageEnv
  split
  · exact (PhaseCreditSpec.nil fineCostModel).mono
      (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)
  · split
    · have h256 := (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps
        (req := 256) (al := 8) (by decide) (by rw [fineCostModel_smallMaxReq_eq]; decide)).mono
        (fineSmallAllocCost_le_9789_of_le_1280 (by decide))
        (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 256)
      exact (h256.seq (PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps)).mono
        (by decide) (by decide) (by decide) (by omega)
    · rename_i _ hnot_or
      have hor_false :
          ((collectPointsVecsTotal dec 0 16 false []).1 || decide (dec.ptsNeeded = 0)) = false :=
        Bool.eq_false_iff.mpr hnot_or
      obtain ⟨hfst, _⟩ := Bool.or_eq_false_iff.mp hor_false
      have h256 := (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps
        (req := 256) (al := 8) (by decide) (by rw [fineCostModel_smallMaxReq_eq]; decide)).mono
        (fineSmallAllocCost_le_9789_of_le_1280 (by decide))
        (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 256)
      by_cases hge32 : 32 ≤ dec.ptsNeeded
      · have hout_sm : 2 * dec.ptsNeeded ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
          rw [fineCostModel_smallMaxReq_eq]; omega
        have hout := (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps
          (req := 2 * dec.ptsNeeded) (al := 1) (by decide) hout_sm).mono
          (fineSmallAllocCost_le_9789_of_le_1280 (by omega))
          (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl _)
        have hHead := PhaseCreditSpec.append_eq h256 hout
        have hLoop := (decodedMessageLoop_fine_ge2_le36_phaseCreditSpec dec
          (collectedSlices dec 0 16)
          (fun poly hpoly => collectedSlices_getD_range_ge32_le576 hfst hge32 hpts hpoly)
          dec.ptsNeeded 0 16 (List.replicate 16 none)
          (by simp) (by rw [polyNoneCount_replicate_none])
          (polyCacheRangeBound_replicate_none 2 36 16)).mono
          (show 1607 * dec.ptsNeeded + 4821 * 16 ≤ 1002768 by
            have hm : 1607 * dec.ptsNeeded ≤ 1607 * 576 := Nat.mul_le_mul_left 1607 hpts
            exact Nat.le_trans (Nat.add_le_add_right hm _) (by decide))
          (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 74)
        exact (hHead.seq (hLoop.seq (PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps))).mono
          (by decide) (by decide) (by decide) (by omega)
      · have hle31 : dec.ptsNeeded ≤ 31 := by omega
        have hout_sm : 2 * dec.ptsNeeded ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
          rw [fineCostModel_smallMaxReq_eq]; omega
        have hout := (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps
          (req := 2 * dec.ptsNeeded) (al := 1) (by decide) hout_sm).mono
          (fineSmallAllocCost_le_1607_of_le_74 (by omega))
          (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl _)
        have hHead := PhaseCreditSpec.append_eq h256 hout
        have hSlices2 : ∀ poly < 16, ((collectedSlices dec 0 16)[poly]?.getD []).length ≤ 2 := by
          intro poly hpoly
          have hle := collectedSlices_getD_length_le dec hpoly
          omega
        have hLoop := (decodedMessageLoop_fine_le2_phaseCreditSpec dec
          (collectedSlices dec 0 16) hSlices2
          dec.ptsNeeded 0 16 (List.replicate 16 none)
          (by simp) (by rw [polyNoneCount_replicate_none])
          (polyCacheDegBound_replicate_none 2 16)).mono
          (show 8513 * dec.ptsNeeded + 564 * 16 ≤ 272927 by
            have hm : 8513 * dec.ptsNeeded ≤ 8513 * 31 := Nat.mul_le_mul_left 8513 hle31
            exact Nat.le_trans (Nat.add_le_add_right hm _) (by decide))
          (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 8)
        exact (hHead.seq (hLoop.seq (PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps))).mono
          (by decide) (by decide) (by decide) (by omega)

theorem libcruxHmacSha256_fine_phaseCreditSpec :
    PhaseCreditSpec fineCostModel (· = libcruxHmacSha256Events) 5559 0 0 64 := by
  unfold libcruxHmacSha256Events
  have ha64 := (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps
    (req := 64) (al := 1) (by decide) (by rw [fineCostModel_smallMaxReq_eq]; decide)).mono
    (fineSmallAllocCost_le_1607_of_le_74 (by decide))
    (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 64)
  have hd64 := PhaseCreditSpec.rustDealloc_align16 fineCostModel (req := 64) (al := 1) (by decide)
  have ha32 := (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps
    (req := 32) (al := 1) (by decide) (by rw [fineCostModel_smallMaxReq_eq]; decide)).mono
    (smallAllocCost_le_738_of_le_44 (by decide))
    (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 32)
  exact (PhaseCreditSpec.append_eq
    (PhaseCreditSpec.append_eq
      (PhaseCreditSpec.append_eq
        (PhaseCreditSpec.append_eq
          (PhaseCreditSpec.append_eq
            (PhaseCreditSpec.append_eq ha64 ha64) ha64) hd64) hd64) hd64) ha32).mono
    (by decide) (by decide) (by decide) (by decide)

theorem sendCt2Seg23_fine_phaseCreditSpec (es : Bytes) :
    PhaseCreditSpec fineCostModel (· = sendCt2Seg23Events es) 14007 0 0 2080 := by
  unfold sendCt2Seg23Events sendCt2FlipAllocEvents sendCt2FlipDeallocEvents
  have h128 := (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps
    (req := 128) (al := 1) (by decide) (by rw [fineCostModel_smallMaxReq_eq]; decide)).mono
    (fineSmallAllocCost_le_9789_of_le_1280 (by decide))
    (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 128)
  split
  · have h2080 := PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps
      (req := 2080) (al := 1) (by decide) (by rw [fineCostModel_smallMaxReq_eq]; decide)
    rw [fineSmallAllocCost_2080] at h2080
    have hd2080 := PhaseCreditSpec.rustDealloc_align16 fineCostModel
      (req := 2080) (al := 1) (by decide)
    exact (PhaseCreditSpec.append_eq (PhaseCreditSpec.append_eq h2080 h128) hd2080).mono
      (by decide) (by decide) (by decide) (by decide)
  · simpa only [List.nil_append, List.append_nil] using
      h128.mono (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (by decide)

theorem sendCt2Reserve128_fine_le_1088_phaseCreditSpec {ct1Len : Nat} (hct1 : ct1Len ≤ 1088) :
    PhaseCreditSpec fineCostModel (SendCt2Reserve128Env ct1Len) 10747 0 0 2430 := by
  refine { req_align := ?_, credit_le := ?_ }
  · rintro evs (rfl | ⟨cap, hlo, hhi, rfl⟩)
    · intro ev hev; nomatch hev
    · have hnew_ge : 1 ≤ reserveCap cap.toNat ct1Len 128 := by dsimp [reserveCap]; omega
      have hnew_2430 : reserveCap cap.toNat ct1Len 128 ≤ 2430 := by dsimp [reserveCap]; omega
      have hnew_sm :
          reserveCap cap.toNat ct1Len 128 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
        rw [fineCostModel_smallMaxReq_eq]; omega
      unfold sendCt2Reserve128Events
      dsimp only
      split
      · exact ((PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps
          (req := reserveCap cap.toNat ct1Len 128) (al := 1) (by decide) hnew_sm).mono
          (Nat.le_refl _) (Nat.le_refl 0) (Nat.le_refl 0) hnew_2430).req_align _ rfl
      · exact ((PhaseCreditSpec.rustRealloc_small_exact fineCostModel_modelHyps
          (old := cap.toNat) (new := reserveCap cap.toNat ct1Len 128) (al := 1)
          (by decide) hnew_ge hnew_sm).mono
          (Nat.le_refl _) (Nat.le_refl 0) (Nat.le_refl 0) hnew_2430).req_align _ rfl
  · rintro st0 evs (rfl | ⟨cap, hlo, hhi, rfl⟩)
    · exact ((PhaseCreditSpec.nil fineCostModel).mono
        (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 0)).credit_le st0 rfl
    · have hnew_ge : 1 ≤ reserveCap cap.toNat ct1Len 128 := by dsimp [reserveCap]; omega
      have hnew_2430 : reserveCap cap.toNat ct1Len 128 ≤ 2430 := by dsimp [reserveCap]; omega
      have hnew_sm :
          reserveCap cap.toNat ct1Len 128 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
        rw [fineCostModel_smallMaxReq_eq]; omega
      unfold sendCt2Reserve128Events
      dsimp only
      split
      · have hc : HasFineReallocCredit.smallAllocCost fineCostModel
            (reserveCap cap.toNat ct1Len 128) ≤ 10747 :=
          Nat.le_trans (fineSmallAllocCost_le_9789_of_le_2430 hnew_2430) (by decide)
        exact ((PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps
          (req := reserveCap cap.toNat ct1Len 128) (al := 1) (by decide) hnew_sm).mono
          hc (Nat.le_refl 0) (Nat.le_refl 0) hnew_2430).credit_le st0 rfl
      · have hc := fineSmallReallocCost_le_10747_of_le_2430 hnew_2430
        exact ((PhaseCreditSpec.rustRealloc_small_exact fineCostModel_modelHyps
          (old := cap.toNat) (new := reserveCap cap.toNat ct1Len 128) (al := 1)
          (by decide) hnew_ge hnew_sm).mono
          hc (Nat.le_refl 0) (Nat.le_refl 0) hnew_2430).credit_le st0 rfl

theorem unchunkedSendCt2_fine_le_1088_phaseCreditSpec {F : ShaCompress}
    (x : UnchunkedSendCt2Ghost F) (hct1 : x.st.ct1.length ≤ 1088) :
    PhaseCreditSpec fineCostModel (UnchunkedSendCt2Env x) 40102 0 0 2430 := by
  have hSeg23 := sendCt2Seg23_fine_phaseCreditSpec x.st.es
  have hRes := sendCt2Reserve128_fine_le_1088_phaseCreditSpec hct1
  have hConcatHmac :
      PhaseCreditSpec fineCostModel (· = sendCt2ConcatHmacEvents x.st.ct1.length)
        15348 0 0 1280 := by
    unfold sendCt2ConcatHmacEvents
    have hsm : 35 + 8 + (x.st.ct1.length + 128) ≤
        HasFineReallocCredit.smallMaxReq fineCostModel := by
      rw [fineCostModel_smallMaxReq_eq]; omega
    have hc := (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps
      (req := 35 + 8 + (x.st.ct1.length + 128)) (al := 1) (by decide) hsm).mono
      (fineSmallAllocCost_le_9789_of_le_1280 (by omega))
      (Nat.le_refl 0) (Nat.le_refl 0) (show 35 + 8 + (x.st.ct1.length + 128) ≤ 1280 by omega)
    exact (PhaseCreditSpec.append_eq hc libcruxHmacSha256_fine_phaseCreditSpec).mono
      (by decide) (by decide) (by decide) (by decide)
  have hPre : PhaseCreditSpec fineCostModel (UnchunkedSendCt2PreEnv x) 40102 0 0 2430 := by
    refine (((hSeg23.concat hRes).concat hConcatHmac).of_imp ?_).mono
      (by decide) (by decide) (by decide) (by decide)
    rintro evs ⟨evsRes, hResEv, rfl⟩
    exact ⟨sendCt2Seg23Events x.st.es ++ evsRes, sendCt2ConcatHmacEvents x.st.ct1.length, rfl,
      ⟨sendCt2Seg23Events x.st.es, evsRes, rfl, rfl, hResEv⟩, rfl⟩
  refine ((hPre.concat (PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps)).of_imp ?_).mono
    (by decide) (by decide) (by decide) (by decide)
  rintro evs ⟨evsPre, evsFree, hPreEv, hFreeEv, rfl⟩
  exact ⟨evsPre, evsFree, rfl, hPreEv, hFreeEv⟩

private theorem addChunkSlot_fine_two_mul_phaseCreditSpec {s : SortedSetPt}
    (hsmall : 8 * s.vec.length + 16 ≤ 135167) :
    PhaseCreditSpec fineCostModel (AddChunkSlotEnv s)
      (16 * s.vec.length + 9571) 0 0 (8 * s.vec.length + 16) := by
  unfold AddChunkSlotEnv
  have hgrow :
      PhaseCreditSpec fineCostModel (· = growOnePtEvents s.vec.length)
        (16 * s.vec.length + 9571) 0 0 (8 * s.vec.length + 16) := by
    unfold growOnePtEvents
    split
    · have h16 := PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps (req := 16) (al := 2)
        (by decide) (by rw [fineCostModel_smallMaxReq_eq]; decide)
      have hc := smallAllocCost_le_488_of_le_28 (req := 16) (by decide)
      exact h16.mono (by omega) (Nat.le_refl 0) (Nat.le_refl 0) (by omega)
    · have hal_new : 2 ≤ 4 * max (2 * s.vec.length) 4 := by omega
      have hnew_le : 4 * max (2 * s.vec.length) 4 ≤ 8 * s.vec.length + 16 := by omega
      have hnew_sm :
          4 * max (2 * s.vec.length) 4 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
        rw [fineCostModel_smallMaxReq_eq]; omega
      have hc := smallReallocCost_le_two_mul_add (4 * max (2 * s.vec.length) 4)
      exact (PhaseCreditSpec.rustRealloc_small_exact fineCostModel_modelHyps
        (old := 4 * s.vec.length) (new := 4 * max (2 * s.vec.length) 4) (al := 2)
        (by decide) hal_new hnew_sm).mono (by omega) (Nat.le_refl 0) (Nat.le_refl 0) hnew_le
  exact ((PhaseCreditSpec.nil fineCostModel).or hgrow).mono
    (by omega) (by decide) (by decide) (by omega)

/-- Affine `ptsLenSum` `PhaseCreditSpec` on `fineCostModel` for `AddChunkSlotsEnv pts` when `8 * ptsLenSum pts + 16 ≤ 135,167`.
-/
theorem addChunkSlots_fine_two_mul_phaseCreditSpec :
    ∀ (pts : List SortedSetPt),
      8 * ptsLenSum pts + 16 ≤ 135167 →
      PhaseCreditSpec fineCostModel (AddChunkSlotsEnv pts)
        (16 * ptsLenSum pts + 9571 * pts.length) 0 0 (8 * ptsLenSum pts + 16)
  | [], _ =>
    (PhaseCreditSpec.nil fineCostModel).mono
      (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)
  | s :: rest, hsm => by
    dsimp only [AddChunkSlotsEnv]
    have hsum : ptsLenSum (s :: rest) = s.vec.length + ptsLenSum rest := by
      simp [ptsLenSum]
    have hs_sm : 8 * s.vec.length + 16 ≤ 135167 := by omega
    have hrest_sm : 8 * ptsLenSum rest + 16 ≤ 135167 := by omega
    have h1 := addChunkSlot_fine_two_mul_phaseCreditSpec hs_sm
    have h2 := addChunkSlots_fine_two_mul_phaseCreditSpec rest hrest_sm
    refine (h1.seq h2).mono ?_ (by decide) (by decide) ?_
    · simp only [List.length_cons, hsum]
      omega
    · rw [hsum]
      omega

/-! ## `NonFreeBound` Helpers for `PhaseGroupSpec` -/

theorem NonFreeBound.append_eq {a b : List AllocEvent} {c₁ c₂ : Nat}
    (h₁ : NonFreeBound (· = a) c₁)
    (h₂ : NonFreeBound (· = b) c₂) :
    NonFreeBound (· = a ++ b) (c₁ + c₂) :=
  (h₁.concat h₂).of_imp fun _ h => ⟨a, b, h, rfl, rfl⟩

theorem encodeBytes_nonFreeBound (msgLen : Nat) :
    NonFreeBound (EncodeBytesEnv msgLen) 16 := by
  unfold EncodeBytesEnv encodeBytesAllocEvents
  split
  · have hstep := NonFreeBound.rustAlloc msgLen 2
    have hrep :
        ∀ n : Nat,
          NonFreeBound (· = (List.replicate n (rustAllocEvents msgLen 2)).flatten) n := by
      intro n
      induction n with
      | zero => exact NonFreeBound.nil
      | succ n ih =>
        rw [List.replicate_succ, List.flatten_cons]
        exact (NonFreeBound.append_eq hstep ih).mono (by omega)
    exact hrep 16
  · exact NonFreeBound.nil.mono (by decide)

theorem addChunkSlot_nonFreeBound (s : SortedSetPt) :
    NonFreeBound (AddChunkSlotEnv s) 1 := by
  unfold AddChunkSlotEnv
  have hgrow : NonFreeBound (· = growOnePtEvents s.vec.length) 1 := by
    unfold growOnePtEvents
    split
    · exact NonFreeBound.rustAlloc 16 2
    · exact NonFreeBound.rustRealloc (4 * s.vec.length) (4 * max (2 * s.vec.length) 4) 2
  exact (NonFreeBound.nil.or hgrow).mono (by decide)

theorem addChunkSlots_nonFreeBound :
    ∀ (pts : List SortedSetPt), NonFreeBound (AddChunkSlotsEnv pts) pts.length
  | [] => NonFreeBound.nil
  | s :: rest => by
    dsimp only [AddChunkSlotsEnv, List.length_cons]
    exact ((addChunkSlot_nonFreeBound s).seq (addChunkSlots_nonFreeBound rest)).mono (by omega)

theorem computeAtCall_nonFreeBound (len : Nat) :
    NonFreeBound (ComputeAtCallEnv len) 2 := by
  unfold ComputeAtCallEnv
  have halloc : NonFreeBound (· = computeAtAllocEvents len) 2 := by
    unfold computeAtAllocEvents
    split
    · exact (NonFreeBound.rustAlloc 8 2).mono (by decide)
    · split
      · exact NonFreeBound.append_eq (NonFreeBound.rustAlloc 2 2)
          (NonFreeBound.rustRealloc 2 8 2)
      · exact (NonFreeBound.rustAlloc (2 * len) 2).mono (by decide)
  exact (halloc.seq NonFreeBound.freeOnly).mono (by decide)

theorem lagrangeInterpolateMiss_nonFreeBound (mLen : Nat) :
    NonFreeBound (LagrangeInterpolateMissEnv mLen) 3 := by
  unfold LagrangeInterpolateMissEnv
  have h1 := NonFreeBound.rustAlloc (2 * mLen) 2
  have h2 := NonFreeBound.rustAlloc (2 * (mLen + 1)) 2
  have halloc := NonFreeBound.append_eq (NonFreeBound.append_eq h1 h2) h2
  exact (halloc.seq NonFreeBound.freeOnly).mono (by decide)

private theorem decodedMessageLoop_nonFreeBound
    (self : PolyDecoder) (pointsVecs : List (List Pt)) :
    ∀ (rem i m : Nat) (polys : List (Option Poly)),
      polys.length = 16 →
      polyNoneCount polys ≤ m →
      NonFreeBound (DecodedMessageLoopEnv self pointsVecs i rem polys) (2 * rem + 3 * m)
  | 0, _, _, _, _, _ => NonFreeBound.nil.mono (Nat.zero_le _)
  | rem + 1, i, m, polys, hlen, hcnt => by
    rw [decodedMessageLoopEnv_succ]
    split
    · exact (decodedMessageLoop_nonFreeBound self pointsVecs rem (i + 1) m polys hlen hcnt).mono
        (by omega)
    · cases hopt : polys[i % 16]?.getD none with
      | some p =>
        dsimp only
        have hTail := decodedMessageLoop_nonFreeBound self pointsVecs rem (i + 1) m polys hlen hcnt
        exact ((computeAtCall_nonFreeBound p.coefficients.length).seq hTail).mono (by omega)
      | none =>
        dsimp only
        have hpoly : i % 16 < 16 := Nat.mod_lt i (by decide)
        have hpoly_lt : i % 16 < polys.length := hlen ▸ hpoly
        let ptsSlice := pointsVecs[i % 16]?.getD []
        let interp := lagrangeInterpolateTotal ptsSlice
        have hcnt_eq := polyNoneCount_set_some_eq polys (i % 16) interp hpoly_lt hopt
        cases m with
        | zero => omega
        | succ m' =>
          have hlen' : (polys.set (i % 16) (some interp)).length = 16 := by simp [hlen]
          have hcnt' : polyNoneCount (polys.set (i % 16) (some interp)) ≤ m' := by omega
          have hMiss := lagrangeInterpolateMiss_nonFreeBound ptsSlice.length
          have hComp := computeAtCall_nonFreeBound interp.coefficients.length
          have hTail := decodedMessageLoop_nonFreeBound self pointsVecs
            rem (i + 1) m' (polys.set (i % 16) (some interp)) hlen' hcnt'
          exact (hMiss.seq (hComp.seq hTail)).mono (by omega)

theorem decodedMessage_nonFreeBound (dec : PolyDecoder) :
    NonFreeBound (DecodedMessageEnv dec) (2 * dec.ptsNeeded + 50) := by
  unfold DecodedMessageEnv
  split
  · exact NonFreeBound.nil.mono (Nat.zero_le _)
  · split
    · exact ((NonFreeBound.rustAlloc 256 8).seq NonFreeBound.freeOnly).mono (by omega)
    · have hHead := NonFreeBound.append_eq
        (NonFreeBound.rustAlloc 256 8) (NonFreeBound.rustAlloc (2 * dec.ptsNeeded) 1)
      have hLoop := decodedMessageLoop_nonFreeBound dec (collectedSlices dec 0 16)
        dec.ptsNeeded 0 16 (List.replicate 16 none)
        (by simp) (by rw [polyNoneCount_replicate_none])
      exact (hHead.seq (hLoop.seq NonFreeBound.freeOnly)).mono (by omega)

theorem decodedMessage_ptsNeeded_le_576_nonFreeBound {dec : PolyDecoder}
    (hpts : dec.ptsNeeded ≤ 576) :
    NonFreeBound (DecodedMessageEnv dec) 1202 :=
  (decodedMessage_nonFreeBound dec).mono (by omega)

theorem libcruxHmacSha256_nonFreeBound :
    NonFreeBound (· = libcruxHmacSha256Events) 4 := by
  unfold libcruxHmacSha256Events
  have ha64 := NonFreeBound.rustAlloc 64 1
  have hd64 := NonFreeBound.rustDealloc 64 1
  have ha32 := NonFreeBound.rustAlloc 32 1
  exact (NonFreeBound.append_eq
    (NonFreeBound.append_eq
      (NonFreeBound.append_eq
        (NonFreeBound.append_eq
          (NonFreeBound.append_eq
            (NonFreeBound.append_eq ha64 ha64) ha64) hd64) hd64) hd64) ha32).mono (by decide)

theorem sendCt2Seg23_nonFreeBound (es : Bytes) :
    NonFreeBound (· = sendCt2Seg23Events es) 2 := by
  unfold sendCt2Seg23Events sendCt2FlipAllocEvents sendCt2FlipDeallocEvents
  have h128 := NonFreeBound.rustAlloc 128 1
  split
  · exact (NonFreeBound.append_eq
      (NonFreeBound.append_eq (NonFreeBound.rustAlloc 2080 1) h128)
      (NonFreeBound.rustDealloc 2080 1)).mono (by decide)
  · simpa only [List.nil_append, List.append_nil] using h128.mono (by decide)

theorem sendCt2Reserve128_nonFreeBound (ct1Len : Nat) :
    NonFreeBound (SendCt2Reserve128Env ct1Len) 1 := by
  rintro evs (rfl | ⟨cap, _, _, rfl⟩)
  · exact (NonFreeBound.nil.mono (by decide)) _ rfl
  · unfold sendCt2Reserve128Events
    dsimp only
    split
    · exact NonFreeBound.rustAlloc (reserveCap cap.toNat ct1Len 128) 1 _ rfl
    · exact NonFreeBound.rustRealloc cap.toNat (reserveCap cap.toNat ct1Len 128) 1 _ rfl

theorem sendCt2ConcatHmac_nonFreeBound (ct1Len : Nat) :
    NonFreeBound (· = sendCt2ConcatHmacEvents ct1Len) 5 := by
  unfold sendCt2ConcatHmacEvents
  exact (NonFreeBound.append_eq
    (NonFreeBound.rustAlloc (35 + 8 + (ct1Len + 128)) 1)
    libcruxHmacSha256_nonFreeBound).mono (by decide)

theorem unchunkedSendCt2_nonFreeBound {F : ShaCompress} (x : UnchunkedSendCt2Ghost F) :
    NonFreeBound (UnchunkedSendCt2Env x) 8 := by
  have hPre : NonFreeBound (UnchunkedSendCt2PreEnv x) 8 := by
    refine ((((sendCt2Seg23_nonFreeBound x.st.es).concat
      (sendCt2Reserve128_nonFreeBound x.st.ct1.length)).concat
      (sendCt2ConcatHmac_nonFreeBound x.st.ct1.length)).of_imp ?_).mono (by decide)
    rintro evs ⟨evsRes, hResEv, rfl⟩
    exact ⟨sendCt2Seg23Events x.st.es ++ evsRes, sendCt2ConcatHmacEvents x.st.ct1.length, rfl,
      ⟨sendCt2Seg23Events x.st.es, evsRes, rfl, rfl, hResEv⟩, rfl⟩
  refine ((hPre.concat NonFreeBound.freeOnly).of_imp ?_).mono (by decide)
  rintro evs ⟨evsPre, evsFree, hPreEv, hFreeEv, rfl⟩
  exact ⟨evsPre, evsFree, rfl, hPreEv, hFreeEv⟩

end LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvCreditHelpers
