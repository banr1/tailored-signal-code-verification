/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.PeakBudget.W3InitiateHelpers
public import LibsignalBinary.Proofs.PeakBudget.W3InitiateStagesPeak

/-!
# Regime-Free Affine `PhaseCreditSpec` Bounds for W3 `process_prekey_bundle`

Proves `W3BoundedEvs` constructors for Stage 4/5 `SessionState` operations, boxed-future
`shim ++ poll ++ drop` cancellation (`BoxedPollDropEnv`), and regime-uniform `(hM : ModelHyps M)`
`PhaseCreditSpec` bounds across `W3Stage1Env`..`W3Stage5Env` and `W3InitiateFullEnv`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.W3InitiateAffinePeak

open LibsignalBinary.Heap
  (AllocCostModel AllocEvent FreeOnlyEvs SeqEnv
   rustAllocEvents rustDeallocEvents rustReallocEvents)
open LibsignalBinary.Heap.Fine.ClientBounds (eventStepAlign eventStepReq)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
  (ConcatEnv DeallocCreditSpec ModelHyps PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.W3InitiateHelpers
  (phaseCreditSpec_segA_dropErr16 phaseCreditSpec_segC_kyberSpkClone
   phaseCreditSpec_segC_kyberSpkClone_free phaseCreditSpec_seq5)
open LibsignalBinary.Proofs.PeakBudget.W3InitiateStagesPeak
  (W3BoundedEvs W3InitiateFullEnv W3Stage1Env W3Stage2Env W3Stage4Env W3Stage5Env
   phaseCreditSpec_seq_freeOnly phaseCreditSpec_w3BoundedEvs_aff
   w3BoundedEvs_append w3BoundedEvs_nil)

/-! ## 1. `W3BoundedEvs` Builders for Stage 4 and Stage 5 Events -/

theorem w3BoundedEvs_mono {n₁ n₂ r₁ r₂ : Nat} {evs : List AllocEvent}
    (hn : n₁ ≤ n₂) (hr : r₁ ≤ r₂) (h : W3BoundedEvs n₁ r₁ evs) :
    W3BoundedEvs n₂ r₂ evs :=
  ⟨Nat.le_trans h.1 hn, fun ev hev => ⟨Nat.le_trans (h.2 ev hev).1 hr, (h.2 ev hev).2⟩⟩

theorem w3BoundedEvs_rustAlloc {req al maxReq : Nat} (hal : al ≤ 16) (hreq : req ≤ maxReq) :
    W3BoundedEvs 1 maxReq (rustAllocEvents req al) := by
  unfold rustAllocEvents
  split_ifs
  · refine ⟨Nat.le_refl 1, fun ev hev => ?_⟩
    simp only [List.mem_singleton] at hev; subst hev
    exact ⟨hreq, by dsimp [eventStepAlign]; omega⟩
  · refine ⟨Nat.le_refl 1, fun ev hev => ?_⟩
    simp only [List.mem_singleton] at hev; subst hev
    exact ⟨hreq, by dsimp [eventStepAlign]; omega⟩

theorem w3BoundedEvs_rustDealloc (req al maxReq : Nat) :
    W3BoundedEvs 0 maxReq (rustDeallocEvents req al) := by
  refine ⟨Nat.le_refl 0, fun ev hev => ?_⟩
  simp only [rustDeallocEvents, List.mem_singleton] at hev; subst hev
  exact ⟨Nat.zero_le _, by dsimp [eventStepAlign]; omega⟩

theorem w3BoundedEvs_rustRealloc {old new al maxReq : Nat}
    (hal : al ≤ 16) (hnew : new ≤ maxReq) :
    W3BoundedEvs 1 maxReq (rustReallocEvents old new al) := by
  unfold rustReallocEvents
  split_ifs
  · refine ⟨Nat.le_refl 1, fun ev hev => ?_⟩
    simp only [List.mem_singleton] at hev; subst hev
    exact ⟨hnew, hal⟩
  · refine ⟨Nat.le_refl 1, fun ev hev => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hev
    rcases hev with rfl | rfl
    · exact ⟨hnew, by dsimp [eventStepAlign]; omega⟩
    · exact ⟨Nat.zero_le _, by dsimp [eventStepAlign]; omega⟩

theorem w3BoundedEvs_doReserve {oldCap cap elemSz al maxReq : Nat}
    (hal : al ≤ 16) (hcap : cap * elemSz ≤ maxReq) :
    W3BoundedEvs 1 maxReq
      (if oldCap = 0 then rustAllocEvents (cap * elemSz) al
       else rustReallocEvents (oldCap * elemSz) (cap * elemSz) al) := by
  split_ifs
  · exact w3BoundedEvs_rustAlloc hal hcap
  · exact w3BoundedEvs_rustRealloc hal hcap

theorem w3BoundedEvs_sessionStateNew :
    W3BoundedEvs 4 33
      (rustAllocEvents 33 1 ++ rustAllocEvents 33 1 ++
        rustAllocEvents 32 1 ++ rustAllocEvents 33 1) := by
  have a33 := w3BoundedEvs_rustAlloc (req := 33) (al := 1) (maxReq := 33) (by decide) (by decide)
  have a32 := w3BoundedEvs_rustAlloc (req := 32) (al := 1) (maxReq := 33) (by decide) (by decide)
  exact w3BoundedEvs_append (w3BoundedEvs_append (w3BoundedEvs_append a33 a33) a32) a33

theorem w3BoundedEvs_withSenderChainNone :
    W3BoundedEvs 5 33
      (rustAllocEvents 32 1 ++ rustAllocEvents 33 1 ++ rustAllocEvents 33 1 ++
        rustAllocEvents 32 1 ++ rustAllocEvents 32 1 ++
        rustDeallocEvents 32 1 ++ rustDeallocEvents 33 1) := by
  have a33 := w3BoundedEvs_rustAlloc (req := 33) (al := 1) (maxReq := 33) (by decide) (by decide)
  have a32 := w3BoundedEvs_rustAlloc (req := 32) (al := 1) (maxReq := 33) (by decide) (by decide)
  have d32 := w3BoundedEvs_rustDealloc 32 1 33
  have d33 := w3BoundedEvs_rustDealloc 33 1 33
  exact w3BoundedEvs_append
    (w3BoundedEvs_append
      (w3BoundedEvs_append
        (w3BoundedEvs_append
          (w3BoundedEvs_append
            (w3BoundedEvs_append a32 a33) a33) a32) a32) d32) d33

theorem w3BoundedEvs_withReceiverChainEmpty :
    W3BoundedEvs 4 416
      (rustAllocEvents 32 1 ++ rustAllocEvents 33 1 ++ rustAllocEvents 33 1 ++
        rustDeallocEvents 33 1 ++ rustAllocEvents 416 8) := by
  have a32 := w3BoundedEvs_rustAlloc (req := 32) (al := 1) (maxReq := 416) (by decide) (by decide)
  have a33 := w3BoundedEvs_rustAlloc (req := 33) (al := 1) (maxReq := 416) (by decide) (by decide)
  have d33 := w3BoundedEvs_rustDealloc 33 1 416
  have a416 := w3BoundedEvs_rustAlloc (req := 416) (al := 8) (maxReq := 416) (by decide) (by decide)
  exact w3BoundedEvs_append
    (w3BoundedEvs_append (w3BoundedEvs_append (w3BoundedEvs_append a32 a33) a33) d33) a416

theorem w3BoundedEvs_stage4_sessionState :
    W3BoundedEvs 13 416
      ((rustAllocEvents 33 1 ++ rustAllocEvents 33 1 ++
          rustAllocEvents 32 1 ++ rustAllocEvents 33 1) ++
       (rustAllocEvents 32 1 ++ rustAllocEvents 33 1 ++ rustAllocEvents 33 1 ++
          rustAllocEvents 32 1 ++ rustAllocEvents 32 1 ++
          rustDeallocEvents 32 1 ++ rustDeallocEvents 33 1) ++
       (rustAllocEvents 32 1 ++ rustAllocEvents 33 1 ++ rustAllocEvents 33 1 ++
          rustDeallocEvents 33 1 ++ rustAllocEvents 416 8)) := by
  have hnew := w3BoundedEvs_mono (r₂ := 416) (Nat.le_refl 4) (by decide) w3BoundedEvs_sessionStateNew
  have hsnd := w3BoundedEvs_mono (r₂ := 416) (Nat.le_refl 5) (by decide) w3BoundedEvs_withSenderChainNone
  exact w3BoundedEvs_append (w3BoundedEvs_append hnew hsnd) w3BoundedEvs_withReceiverChainEmpty

theorem w3BoundedEvs_setUnackPreKeyMsg :
    W3BoundedEvs 2 33
      (rustAllocEvents 33 1 ++ rustAllocEvents 33 1 ++ rustDeallocEvents 33 1) := by
  have a33 := w3BoundedEvs_rustAlloc (req := 33) (al := 1) (maxReq := 33) (by decide) (by decide)
  have d33 := w3BoundedEvs_rustDealloc 33 1 33
  exact w3BoundedEvs_append (w3BoundedEvs_append a33 a33) d33

/-! ## 2. Boxed-Future Envelopes and Bounded `rustAlloc` -/

theorem phaseCreditSpec_rustAlloc_aff_bounded
    {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M)
    {req al maxReq : Nat} (hal : al ≤ 16) (hreq : req ≤ maxReq) :
    PhaseCreditSpec M (· = rustAllocEvents req al)
      (2 * maxReq + 9539) (maxReq + 8195) (maxReq + 8195) maxReq :=
  (PhaseCreditSpec.rustAlloc_aff hM hal).mono (by omega) (by omega) (by omega) hreq

/-- Boxed-future async call envelope (`Box::new` shim, `E_poll`, and `Box` drop). -/
def BoxedPollDropEnv (boxSz : Nat) (E_poll : List AllocEvent → Prop)
    (evs : List AllocEvent) : Prop :=
  ConcatEnv
    (ConcatEnv (fun e => e = [] ∨ e = rustAllocEvents boxSz 8) E_poll)
    (fun e => e = [] ∨ e = rustDeallocEvents boxSz 8)
    evs

/-- Exact-size boxed-future `shim ++ poll ++ drop` cancels the `boxSz` future box out of `Δlive`. -/
theorem phaseCreditSpec_exactBoxPollDrop_aff
    {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M)
    (boxSz : Nat) {E_poll : List AllocEvent → Prop} {c_p l_p p_p r_p : Nat}
    (hpoll : PhaseCreditSpec M E_poll c_p l_p p_p r_p) :
    PhaseCreditSpec M
      (ConcatEnv (ConcatEnv (· = rustAllocEvents boxSz 8) E_poll) (· = rustDeallocEvents boxSz 8))
      (2 * boxSz + 9539 + c_p) l_p (boxSz + 8195 + p_p) (max boxSz r_p) :=
  PhaseCreditSpec.tempAllocBodyFree_aff hM (by decide) hpoll

/-- Optional boxed-future shim + `E_poll` + `FreeOnlyEvs` bound under `ModelHyps M`. -/
theorem phaseCreditSpec_optBoxPollFree_aff
    {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M)
    (boxSz : Nat) {E_poll : List AllocEvent → Prop} {c_p l_p p_p r_p : Nat}
    (hpoll : PhaseCreditSpec M E_poll c_p l_p p_p r_p) :
    PhaseCreditSpec M
      (SeqEnv (fun e => e = [] ∨ e = rustAllocEvents boxSz 8) (SeqEnv E_poll FreeOnlyEvs))
      (2 * boxSz + 9539 + c_p) (boxSz + 8195 + l_p) (boxSz + 8195 + p_p) (max boxSz r_p) := by
  have hbox : PhaseCreditSpec M (fun e => e = [] ∨ e = rustAllocEvents boxSz 8)
      (2 * boxSz + 9539) (boxSz + 8195) (boxSz + 8195) boxSz := by
    refine ((PhaseCreditSpec.nil M).or (PhaseCreditSpec.rustAlloc_aff hM (by decide))).mono
      (by omega) (by omega) (by omega) (by omega)
  have hpollF := phaseCreditSpec_seq_freeOnly hM hpoll
  exact (hbox.seq hpollF).mono (by omega) (by omega) (by omega) (Nat.le_refl _)

/-! ## 3. Regime-Uniform Stage 1–5 and End-to-End `PhaseCreditSpec`s -/

/-- Regime-free `PhaseCreditSpec M` for `W3Stage1Env` (`nameLen ≤ 40`). -/
theorem phaseCreditSpec_w3Stage1_aff
    {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M)
    {E_trust E_sessLoad : List AllocEvent → Prop} {nameLen : Nat}
    {c_t l_t p_t r_t c_s l_s p_s r_s : Nat}
    (hname : nameLen ≤ 40)
    (htrust : PhaseCreditSpec M E_trust c_t l_t p_t r_t)
    (hload : PhaseCreditSpec M E_sessLoad c_s l_s p_s r_s) :
    PhaseCreditSpec M (W3Stage1Env E_trust E_sessLoad nameLen)
      (c_t + ((2 * 33 + 9539) + (2 * 1569 + 9539) + c_s))
      (l_t + ((33 + 8195) + (1569 + 8195) + l_s))
      (max p_t (l_t + ((33 + 8195) + (1569 + 8195) + p_s)))
      (max r_t (max 1569 r_s)) := by
  have hfree := PhaseCreditSpec.freeOnly_of_hyps hM
  have herr_alloc := phaseCreditSpec_rustAlloc_aff_bounded hM
    (req := nameLen + 1) (al := 1) (maxReq := 41) (by decide) (by omega)
  have herr := phaseCreditSpec_seq_freeOnly hM herr_alloc
  have ha33 : PhaseCreditSpec M (· = rustAllocEvents 33 1)
      (2 * 33 + 9539) (33 + 8195) (33 + 8195) 33 :=
    PhaseCreditSpec.rustAlloc_aff hM (by decide)
  have ha1569 : PhaseCreditSpec M (· = rustAllocEvents 1569 1)
      (2 * 1569 + 9539) (1569 + 8195) (1569 + 8195) 1569 :=
    PhaseCreditSpec.rustAlloc_aff hM (by decide)
  have hpass := ha33.seq (hfree.seq (ha1569.seq (hfree.seq hload)))
  have hbranch := herr.or hpass
  exact (htrust.seq hbranch).mono
    (s1_cum c_t c_s _ _ _ (by decide))
    (s1_live l_t l_s _ _ _ (by decide))
    (s1_peak p_t l_t p_s _ _ _ (by decide))
    (s1_req r_t r_s 41 33 1569 (by decide) (by decide))
where
  s1_cum (c_t c_s k41 k33 k1569 : Nat) (h : k41 ≤ k33 + k1569) :
      c_t + max k41 (k33 + (0 + (k1569 + (0 + c_s)))) ≤ c_t + (k33 + k1569 + c_s) := by omega
  s1_live (l_t l_s a41 a33 a1569 : Nat) (h : a41 ≤ a33 + a1569) :
      l_t + max a41 (a33 + (0 + (a1569 + (0 + l_s)))) ≤ l_t + (a33 + a1569 + l_s) := by omega
  s1_peak (p_t l_t p_s a41 a33 a1569 : Nat) (h : a41 ≤ a33 + a1569) :
      max p_t
        (l_t + max a41
          (max a33 (a33 + max 0 (0 + max a1569 (a1569 + max 0 (0 + p_s)))))) ≤
        max p_t (l_t + (a33 + a1569 + p_s)) := by omega
  s1_req (r_t r_s k41 k33 k1569 : Nat) (h1 : k41 ≤ k1569) (h2 : k33 ≤ k1569) :
      max r_t (max k41 (max k33 (max 0 (max k1569 (max 0 r_s))))) ≤
        max r_t (max k1569 r_s) := by
    let R := max r_t (max k1569 r_s)
    change _ ≤ R
    have hrt : r_t ≤ R := Nat.le_max_left _ _
    have hk1569 : k1569 ≤ R := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
    have hrs : r_s ≤ R := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
    have hk41 : k41 ≤ R := Nat.le_trans h1 hk1569
    have hk33 : k33 ≤ R := Nat.le_trans h2 hk1569
    have h0 : 0 ≤ R := Nat.zero_le _
    repeat' refine Nat.max_le.mpr ⟨?_, ?_⟩
    all_goals assumption

theorem phaseCreditSpec_w3Stage2_aff
    {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M)
    {E_idKp : List AllocEvent → Prop} {c_k l_k p_k r_k : Nat}
    (hkp : PhaseCreditSpec M E_idKp c_k l_k p_k r_k) :
    PhaseCreditSpec M (W3Stage2Env E_idKp)
      (c_k + (2 * 1568 + 9539))
      (l_k + (1568 + 8195))
      (max p_k (l_k + (1568 + 8195)))
      (max r_k 1568) := by
  have hd16 := phaseCreditSpec_seq_freeOnly hM (phaseCreditSpec_segA_dropErr16 M)
  have hsame := phaseCreditSpec_seq_freeOnly hM (phaseCreditSpec_segC_kyberSpkClone_free hM)
  have hclone := phaseCreditSpec_segC_kyberSpkClone hM
  have htail := hd16.or (hsame.or hclone)
  exact (hkp.seq htail).mono
    (s2_cum c_k _) (s2_live l_k _) (s2_peak p_k l_k _) (by omega)
where
  s2_cum (c_k k : Nat) : c_k + max 0 (max k k) ≤ c_k + k := by omega
  s2_live (l_k a : Nat) : l_k + max 0 (max 0 a) ≤ l_k + a := by omega
  s2_peak (p_k l_k a : Nat) : max p_k (l_k + max 0 (max a a)) ≤ max p_k (l_k + a) := by omega

theorem phaseCreditSpec_w3Stage3_aff
    {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M) :
    PhaseCreditSpec M (W3BoundedEvs 8 1569)
      (8 * (2 * 1569 + 9539))
      (8 * (1569 + 8195))
      (8 * (1569 + 8195))
      1569 :=
  phaseCreditSpec_w3BoundedEvs_aff hM 8 1569

theorem phaseCreditSpec_w3Stage4_aff
    {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M)
    {E_spqrInit : List AllocEvent → Prop} {c_q l_q p_q r_q : Nat}
    (hspqr : PhaseCreditSpec M E_spqrInit c_q l_q p_q r_q) :
    PhaseCreditSpec M (W3Stage4Env E_spqrInit)
      ((2 * 33 + 9539) + c_q + 13 * (2 * 416 + 9539))
      ((33 + 8195) + l_q + 13 * (416 + 8195))
      ((33 + 8195) + max p_q (l_q + 13 * (416 + 8195)))
      (max 416 r_q) := by
  have hpre := phaseCreditSpec_w3BoundedEvs_aff hM 1 33
  have hpost := phaseCreditSpec_w3BoundedEvs_aff hM 13 416
  have h := hpre.seq (hspqr.seq hpost)
  exact h.mono
    (s4_cum _ c_q _) (s4_live _ l_q _) (s4_peak _ p_q l_q _) (by omega)
where
  s4_cum (a c_q b : Nat) : 1 * a + (c_q + b) ≤ a + c_q + b := by omega
  s4_live (a l_q b : Nat) : 1 * a + (l_q + b) ≤ a + l_q + b := by omega
  s4_peak (a p_q l_q b : Nat) :
      max (1 * a) (1 * a + max p_q (l_q + b)) ≤ a + max p_q (l_q + b) := by omega

theorem phaseCreditSpec_w3Stage5_aff
    {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M)
    {E_idRegId E_idSave E_sessStore : List AllocEvent → Prop}
    {c_r l_r p_r r_r c_i l_i p_i r_i c_s l_s p_s r_s : Nat}
    (hreg : PhaseCreditSpec M E_idRegId c_r l_r p_r r_r)
    (hsave : PhaseCreditSpec M E_idSave c_i l_i p_i r_i)
    (hstore : PhaseCreditSpec M E_sessStore c_s l_s p_s r_s) :
    PhaseCreditSpec M (W3Stage5Env E_idRegId E_idSave E_sessStore)
      (4 * (2 * 68 + 9539) + c_r + c_i + c_s)
      (4 * (68 + 8195) + l_r + l_i + l_s)
      (4 * (68 + 8195) + max p_r (l_r + max p_i (l_i + p_s)))
      (max 68 (max r_r (max r_i r_s))) := by
  have hpre := phaseCreditSpec_w3BoundedEvs_aff hM 4 68
  have hstoreF := phaseCreditSpec_seq_freeOnly hM hstore
  have h := hpre.seq (hreg.seq (hsave.seq hstoreF))
  exact h.mono
    (s5_cum _ c_r c_i c_s) (s5_live _ l_r l_i l_s) (s5_peak _ _) (Nat.le_refl _)
where
  s5_cum (a c_r c_i c_s : Nat) : a + (c_r + (c_i + c_s)) ≤ a + c_r + c_i + c_s := by omega
  s5_live (a l_r l_i l_s : Nat) : a + (l_r + (l_i + l_s)) ≤ a + l_r + l_i + l_s := by omega
  s5_peak (a p : Nat) : max a (a + p) ≤ a + p := by omega

/-- Native non-callee affine `Δlive` upper bound across Stages 1–5. -/
def w3InitiateNativeAffLive : Nat :=
  ((33 + 8195) + (1569 + 8195)) +
  (1568 + 8195) +
  8 * (1569 + 8195) +
  ((33 + 8195) + 13 * (416 + 8195)) +
  4 * (68 + 8195)

private theorem aff_cum_reassoc (a1 a2 b c d1 d2 e c_t c_sl c_k c_q c_r c_i c_ss : Nat) :
    ((((c_t + (a1 + a2 + c_sl)) + (c_k + b)) + c) + (d1 + c_q + d2)) + (e + c_r + c_i + c_ss) ≤
      ((a1 + a2) + b + c + (d1 + d2) + e) + c_t + c_sl + c_k + c_q + c_r + c_i + c_ss := by
  omega

private theorem aff_live_reassoc (a1 a2 b c d1 d2 e l_t l_sl l_k l_q l_r l_i l_ss : Nat) :
    ((((l_t + (a1 + a2 + l_sl)) + (l_k + b)) + c) + (d1 + l_q + d2)) + (e + l_r + l_i + l_ss) ≤
      ((a1 + a2) + b + c + (d1 + d2) + e) + l_t + l_sl + l_k + l_q + l_r + l_i + l_ss := by
  omega

private theorem aff_peak_sum_bound (p1 l1 p2 l2 p3 l3 p4 l4 p5 : Nat) :
    max (max (max (max p1 (l1 + p2)) ((l1 + l2) + p3)) (((l1 + l2) + l3) + p4))
      ((((l1 + l2) + l3) + l4) + p5) ≤
      p1 + l1 + p2 + l2 + p3 + l3 + p4 + l4 + p5 := by
  refine Nat.max_le.mpr ⟨?_, by omega⟩
  refine Nat.max_le.mpr ⟨?_, by omega⟩
  refine Nat.max_le.mpr ⟨?_, by omega⟩
  refine Nat.max_le.mpr ⟨by omega, by omega⟩

private theorem aff_req_reassoc (r_t r_sl r_k r_q r5 k1568 k1569 k416 k68 : Nat)
    (h1 : k1568 ≤ k1569) (h2 : k416 ≤ k1569) (h3 : k68 ≤ k1569) :
    max (max (max (max (max r_t (max k1569 r_sl)) (max r_k k1568)) k1569) (max k416 r_q))
      (max k68 r5) ≤
      max k1569 (max r_t (max r_sl (max r_k (max r_q r5)))) := by
  let R := max k1569 (max r_t (max r_sl (max r_k (max r_q r5))))
  change _ ≤ R
  have hk1569 : k1569 ≤ R := Nat.le_max_left _ _
  have hrt : r_t ≤ R := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have hrsl : r_sl ≤ R :=
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
  have hrk : r_k ≤ R :=
    Nat.le_trans (Nat.le_max_left _ _)
      (Nat.le_trans (Nat.le_max_right _ _)
        (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)))
  have hrq : r_q ≤ R :=
    Nat.le_trans (Nat.le_max_left _ _)
      (Nat.le_trans (Nat.le_max_right _ _)
        (Nat.le_trans (Nat.le_max_right _ _)
          (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))))
  have hr5 : r5 ≤ R :=
    Nat.le_trans (Nat.le_max_right _ _)
      (Nat.le_trans (Nat.le_max_right _ _)
        (Nat.le_trans (Nat.le_max_right _ _)
          (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))))
  have hk1568 : k1568 ≤ R := Nat.le_trans h1 hk1569
  have hk416 : k416 ≤ R := Nat.le_trans h2 hk1569
  have hk68 : k68 ≤ R := Nat.le_trans h3 hk1569
  repeat' refine Nat.max_le.mpr ⟨?_, ?_⟩
  all_goals assumption

/-- End-to-end 5-stage regime-free `PhaseCreditSpec M` for `W3InitiateFullEnv` under `ModelHyps M` and `nameLen ≤ 40`.
-/
theorem phaseCreditSpec_w3InitiateFull_aff
    {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M)
    {E_trust E_sessLoad E_idKp E_spqrInit E_idRegId E_idSave E_sessStore :
      List AllocEvent → Prop}
    {nameLen : Nat}
    {c_t l_t p_t r_t c_sl l_sl p_sl r_sl c_k l_k p_k r_k
     c_q l_q p_q r_q c_r l_r p_r r_r c_i l_i p_i r_i c_ss l_ss p_ss r_ss : Nat}
    (hname : nameLen ≤ 40)
    (htrust : PhaseCreditSpec M E_trust c_t l_t p_t r_t)
    (hload : PhaseCreditSpec M E_sessLoad c_sl l_sl p_sl r_sl)
    (hkp : PhaseCreditSpec M E_idKp c_k l_k p_k r_k)
    (hspqr : PhaseCreditSpec M E_spqrInit c_q l_q p_q r_q)
    (hreg : PhaseCreditSpec M E_idRegId c_r l_r p_r r_r)
    (hsave : PhaseCreditSpec M E_idSave c_i l_i p_i r_i)
    (hstore : PhaseCreditSpec M E_sessStore c_ss l_ss p_ss r_ss) :
    let l1 := l_t + ((33 + 8195) + (1569 + 8195) + l_sl)
    let p1 := max p_t (l_t + ((33 + 8195) + (1569 + 8195) + p_sl))
    let l2 := l_k + (1568 + 8195)
    let p2 := max p_k (l_k + (1568 + 8195))
    let l3 := 8 * (1569 + 8195)
    let l4 := (33 + 8195) + l_q + 13 * (416 + 8195)
    let p4 := (33 + 8195) + max p_q (l_q + 13 * (416 + 8195))
    let p5 := 4 * (68 + 8195) + max p_r (l_r + max p_i (l_i + p_ss))
    PhaseCreditSpec M
      (W3InitiateFullEnv E_trust E_sessLoad E_idKp E_spqrInit E_idRegId E_idSave E_sessStore
        nameLen)
      (W3InitiateStagesPeak.w3InitiateNativeSmallCum +
        c_t + c_sl + c_k + c_q + c_r + c_i + c_ss)
      (w3InitiateNativeAffLive + l_t + l_sl + l_k + l_q + l_r + l_i + l_ss)
      (p1 + l1 + p2 + l2 + l3 + l3 + p4 + l4 + p5)
      (max 1569
        (max r_t (max r_sl (max r_k (max r_q (max r_r (max r_i r_ss))))))) := by
  intro l1 p1 l2 p2 l3 l4 p4 p5
  have hs1 := phaseCreditSpec_w3Stage1_aff hM hname htrust hload
  have hs2 := phaseCreditSpec_w3Stage2_aff hM hkp
  have hs3 := phaseCreditSpec_w3Stage3_aff hM
  have hs4 := phaseCreditSpec_w3Stage4_aff hM hspqr
  have hs5 := phaseCreditSpec_w3Stage5_aff hM hreg hsave hstore
  have hall := phaseCreditSpec_seq5 hs1 hs2 hs3 hs4 hs5
  exact hall.mono
    (aff_cum_reassoc _ _ _ _ _ _ _ c_t c_sl c_k c_q c_r c_i c_ss)
    (aff_live_reassoc _ _ _ _ _ _ _ l_t l_sl l_k l_q l_r l_i l_ss)
    (aff_peak_sum_bound p1 l1 p2 l2 l3 l3 p4 l4 p5)
    (aff_req_reassoc r_t r_sl r_k r_q _ 1568 1569 416 68 (by decide) (by decide) (by decide))

end LibsignalBinary.Proofs.PeakBudget.W3InitiateAffinePeak
