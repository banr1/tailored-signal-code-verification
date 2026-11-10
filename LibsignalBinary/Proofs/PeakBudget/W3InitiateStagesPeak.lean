/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.W3InitiateHelpers

/-!
# Stage and End-to-End `PhaseCreditSpec` Bounds for W3 `process_prekey_bundle`

Parametric stage-by-stage (`W3Stage1Env`..`W3Stage5Env`) and 5-stage (`W3InitiateFullEnv`,
`W3InitiateFullEnvWide`) `PhaseCreditSpec M` assembly for `signal_session_handshake::initiate`
(`process_prekey_bundle`) over `W3BoundedEvs`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.W3InitiateStagesPeak

open LibsignalBinary.Heap
  (AllocCostModel AllocEvent FreeOnlyEvs SeqEnv
   rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Heap.Fine.ClientBounds
  (eventStepAlign eventStepReq)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit
  (HasFineReallocCredit)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
  (ConcatEnv ModelHyps PhaseCreditSpec stepEvents_freeOnly_le)
open LibsignalBinary.Proofs.PeakBudget.W3InitiateHelpers
  (phaseCreditSpec_alloc32_small phaseCreditSpec_alloc33_small
   phaseCreditSpec_eq_append phaseCreditSpec_kemSerialize1569_small
   phaseCreditSpec_kyberPreKeyIdDisplay14_small phaseCreditSpec_optDh4_small
   phaseCreditSpec_rustAlloc_small_bounded phaseCreditSpec_segA_dropErr16
   phaseCreditSpec_segC_kyberSpkClone phaseCreditSpec_segC_kyberSpkClone_body_free
   phaseCreditSpec_segC_kyberSpkClone_free phaseCreditSpec_segC_kyberSpkClone_small
   phaseCreditSpec_seq5 phaseCreditSpec_seq5_right
   phaseCreditSpec_sessionStateNew_small phaseCreditSpec_setUnackPreKeyMsg_small
   phaseCreditSpec_withReceiverChainEmpty_small phaseCreditSpec_withSenderChainNone_small)

/-! ## 1. `W3BoundedEvs`: Bounded Non-Free Operations and Interleaved Frees -/

def nonFreeCount : List AllocEvent → Nat
  | [] => 0
  | .free _ _ :: tl => nonFreeCount tl
  | _ :: tl => nonFreeCount tl + 1

/-- Envelope of at most `maxOps` non-`.free` events (`eventStepReq ≤ maxReq`, `eventStepAlign ≤ 16`) with interleaved `.free` events.
-/
def W3BoundedEvs (maxOps maxReq : Nat) (evs : List AllocEvent) : Prop :=
  nonFreeCount evs ≤ maxOps ∧
  ∀ ev ∈ evs, eventStepReq ev ≤ maxReq ∧ eventStepAlign ev ≤ 16

theorem w3BoundedEvs_nil (maxOps maxReq : Nat) : W3BoundedEvs maxOps maxReq [] :=
  ⟨Nat.zero_le maxOps, fun _ h => nomatch h⟩

theorem w3BoundedEvs_freeOnly {maxOps maxReq : Nat} {evs : List AllocEvent}
    (hf : FreeOnlyEvs evs) : W3BoundedEvs maxOps maxReq evs := by
  induction evs with
  | nil => exact w3BoundedEvs_nil maxOps maxReq
  | cons ev tl ih =>
    obtain ⟨al, sz, rfl⟩ := hf ev List.mem_cons_self
    obtain ⟨hc, ha⟩ := ih (fun e he => hf e (List.mem_cons_of_mem _ he))
    refine ⟨hc, fun e he => ?_⟩
    rcases List.mem_cons.mp he with rfl | hmem
    · exact ⟨Nat.zero_le maxReq, Nat.le_refl 16⟩
    · exact ha e hmem

theorem nonFreeCount_append (evs₁ evs₂ : List AllocEvent) :
    nonFreeCount (evs₁ ++ evs₂) = nonFreeCount evs₁ + nonFreeCount evs₂ := by
  induction evs₁ with
  | nil => simp [nonFreeCount]
  | cons ev tl ih =>
    cases ev <;> simp only [List.cons_append, nonFreeCount, ih] <;> omega

theorem w3BoundedEvs_append {n₁ n₂ r₁ r₂ : Nat} {evs₁ evs₂ : List AllocEvent}
    (h₁ : W3BoundedEvs n₁ r₁ evs₁) (h₂ : W3BoundedEvs n₂ r₂ evs₂) :
    W3BoundedEvs (n₁ + n₂) (max r₁ r₂) (evs₁ ++ evs₂) := by
  refine ⟨by rw [nonFreeCount_append]; exact Nat.add_le_add h₁.1 h₂.1, fun ev hev => ?_⟩
  rcases List.mem_append.mp hev with he1 | he2
  · obtain ⟨hr, hal⟩ := h₁.2 ev he1
    exact ⟨Nat.le_trans hr (Nat.le_max_left r₁ r₂), hal⟩
  · obtain ⟨hr, hal⟩ := h₂.2 ev he2
    exact ⟨Nat.le_trans hr (Nat.le_max_right r₁ r₂), hal⟩

theorem w3BoundedEvs_seqEnv {n₁ n₂ r₁ r₂ : Nat} {E₁ E₂ : List AllocEvent → Prop}
    (h₁ : ∀ evs, E₁ evs → W3BoundedEvs n₁ r₁ evs)
    (h₂ : ∀ evs, E₂ evs → W3BoundedEvs n₂ r₂ evs) :
    ∀ evs, SeqEnv E₁ E₂ evs → W3BoundedEvs (n₁ + n₂) (max r₁ r₂) evs := by
  rintro evs (hE1 | ⟨evs₁, evs₂, rfl, hE1, hE2⟩)
  · obtain ⟨hc, ha⟩ := h₁ evs hE1
    exact ⟨Nat.le_trans hc (Nat.le_add_right n₁ n₂), fun ev hev =>
      ⟨Nat.le_trans (ha ev hev).1 (Nat.le_max_left r₁ r₂), (ha ev hev).2⟩⟩
  · exact w3BoundedEvs_append (h₁ evs₁ hE1) (h₂ evs₂ hE2)

private theorem step_small_nonFree_le {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {ev : AllocEvent} {maxReq : Nat} (st : M.σ)
    (hreq : eventStepReq ev ≤ maxReq) (hal : eventStepAlign ev ≤ 16)
    (hsmall : maxReq ≤ HasFineReallocCredit.smallMaxReq M) :
    let st' := M.step ev st
    HasFineReallocCredit.cumSmall st' ≤
      HasFineReallocCredit.cumSmall st + (2 * maxReq + 9539) ∧
    HasFineReallocCredit.liveLarge st' ≤ HasFineReallocCredit.liveLarge st ∧
    HasFineReallocCredit.peakLarge st' ≤ HasFineReallocCredit.peakLarge st := by
  cases ev with
  | free al sz =>
    obtain ⟨hc, hl, hp⟩ := hM.freeNonInc al sz st
    omega
  | alloc req =>
    simp only [eventStepReq] at hreq
    have hle : req ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans hreq hsmall
    obtain ⟨hc, hl, hp⟩ := hM.step_alloc_small_any st hle
    have hsa := hM.smallAlloc_le hle
    omega
  | aligned al req =>
    simp only [eventStepReq, eventStepAlign] at hreq hal
    have hle : req ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans hreq hsmall
    obtain ⟨hc, hl, hp⟩ := hM.step_aligned_small_any st hal hle
    have hsa := hM.smallAlloc_le hle
    omega
  | realloc al old new =>
    simp only [eventStepReq, eventStepAlign] at hreq hal
    have hnew_le : new ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans hreq hsmall
    by_cases hold_le : old ≤ HasFineReallocCredit.smallMaxReq M
    · obtain ⟨hc, hl, hp⟩ := hM.step_realloc_small_small_any st hal hold_le hnew_le
      have hsr := hM.smallRealloc_le hnew_le
      omega
    · have hold_gt : HasFineReallocCredit.smallMaxReq M < old := by omega
      obtain ⟨hc, hl, hp⟩ := hM.step_realloc_large_small_any st hal hold_gt hnew_le
      have hsr := hM.smallRealloc_le hnew_le
      omega

private theorem stepEvents_w3BoundedEvs_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {maxReq : Nat} (hsmall : maxReq ≤ HasFineReallocCredit.smallMaxReq M) :
    ∀ (evs : List AllocEvent) (st : M.σ),
      (∀ ev ∈ evs, eventStepReq ev ≤ maxReq ∧ eventStepAlign ev ≤ 16) →
      HasFineReallocCredit.cumSmall (M.stepEvents evs st) ≤
        HasFineReallocCredit.cumSmall st + nonFreeCount evs * (2 * maxReq + 9539) ∧
      HasFineReallocCredit.liveLarge (M.stepEvents evs st) ≤ HasFineReallocCredit.liveLarge st ∧
      HasFineReallocCredit.peakLarge (M.stepEvents evs st) ≤ HasFineReallocCredit.peakLarge st
  | [], st, _ => by
    simp [nonFreeCount]
  | ev :: tl, st, ha => by
    have hev := ha ev List.mem_cons_self
    have htl : ∀ e ∈ tl, eventStepReq e ≤ maxReq ∧ eventStepAlign e ≤ 16 :=
      fun e he => ha e (List.mem_cons_of_mem _ he)
    cases ev with
    | free al sz =>
      obtain ⟨hc₁, hl₁, hp₁⟩ := hM.freeNonInc al sz st
      obtain ⟨hc₂, hl₂, hp₂⟩ := stepEvents_w3BoundedEvs_small hM hsmall tl (M.step (.free al sz) st) htl
      simp only [AllocCostModel.stepEvents_cons, nonFreeCount]
      exact ⟨by omega, Nat.le_trans hl₂ hl₁, Nat.le_trans hp₂ hp₁⟩
    | alloc req =>
      obtain ⟨hc₁, hl₁, hp₁⟩ := step_small_nonFree_le hM st hev.1 hev.2 hsmall
      obtain ⟨hc₂, hl₂, hp₂⟩ := stepEvents_w3BoundedEvs_small hM hsmall tl (M.step (.alloc req) st) htl
      simp only [AllocCostModel.stepEvents_cons, nonFreeCount, Nat.add_mul, Nat.one_mul]
      exact ⟨by omega, Nat.le_trans hl₂ hl₁, Nat.le_trans hp₂ hp₁⟩
    | aligned al req =>
      obtain ⟨hc₁, hl₁, hp₁⟩ := step_small_nonFree_le hM st hev.1 hev.2 hsmall
      obtain ⟨hc₂, hl₂, hp₂⟩ := stepEvents_w3BoundedEvs_small hM hsmall tl (M.step (.aligned al req) st) htl
      simp only [AllocCostModel.stepEvents_cons, nonFreeCount, Nat.add_mul, Nat.one_mul]
      exact ⟨by omega, Nat.le_trans hl₂ hl₁, Nat.le_trans hp₂ hp₁⟩
    | realloc al old new =>
      obtain ⟨hc₁, hl₁, hp₁⟩ := step_small_nonFree_le hM st hev.1 hev.2 hsmall
      obtain ⟨hc₂, hl₂, hp₂⟩ := stepEvents_w3BoundedEvs_small hM hsmall tl (M.step (.realloc al old new) st) htl
      simp only [AllocCostModel.stepEvents_cons, nonFreeCount, Nat.add_mul, Nat.one_mul]
      exact ⟨by omega, Nat.le_trans hl₂ hl₁, Nat.le_trans hp₂ hp₁⟩

/-- Small-regime (`maxReq ≤ smallMaxReq M`) `PhaseCreditSpec` for `W3BoundedEvs maxOps maxReq`. -/
theorem phaseCreditSpec_w3BoundedEvs_small
    {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M)
    (maxOps maxReq : Nat) (hsmall : maxReq ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (W3BoundedEvs maxOps maxReq)
      (maxOps * (2 * maxReq + 9539)) 0 0 maxReq where
  req_align _ hE := hE.2
  credit_le st0 {evs} hE := by
    obtain ⟨hc, hl, hp⟩ := stepEvents_w3BoundedEvs_small hM hsmall evs st0 hE.2
    have hmul : nonFreeCount evs * (2 * maxReq + 9539) ≤ maxOps * (2 * maxReq + 9539) :=
      Nat.mul_le_mul_right _ hE.1
    omega

private theorem stepEvents_w3BoundedEvs_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (maxReq : Nat) :
    ∀ (evs : List AllocEvent) (st : M.σ),
      (∀ ev ∈ evs, eventStepReq ev ≤ maxReq ∧ eventStepAlign ev ≤ 16) →
      HasFineReallocCredit.cumSmall (M.stepEvents evs st) ≤
        HasFineReallocCredit.cumSmall st + nonFreeCount evs * (2 * maxReq + 9539) ∧
      HasFineReallocCredit.liveLarge (M.stepEvents evs st) ≤
        HasFineReallocCredit.liveLarge st + nonFreeCount evs * (maxReq + 8195) ∧
      HasFineReallocCredit.peakLarge (M.stepEvents evs st) ≤
        max (HasFineReallocCredit.peakLarge st)
          (HasFineReallocCredit.liveLarge st + nonFreeCount evs * (maxReq + 8195))
  | [], st, _ => by
    simp only [AllocCostModel.stepEvents_nil, nonFreeCount, Nat.zero_mul, Nat.add_zero]
    exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_max_left _ _⟩
  | ev :: tl, st, ha => by
    have hev := ha ev List.mem_cons_self
    have htl : ∀ e ∈ tl, eventStepReq e ≤ maxReq ∧ eventStepAlign e ≤ 16 :=
      fun e he => ha e (List.mem_cons_of_mem _ he)
    cases ev with
    | free al sz =>
      obtain ⟨hc₁, hl₁, hp₁⟩ := hM.freeNonInc al sz st
      obtain ⟨hc₂, hl₂, hp₂⟩ := stepEvents_w3BoundedEvs_aff hM maxReq tl (M.step (.free al sz) st) htl
      simp only [AllocCostModel.stepEvents_cons, nonFreeCount]
      omega
    | alloc req =>
      obtain ⟨hc₁, hl₁, hp₁⟩ := hM.step_nonFree_aff st hev.1 hev.2
      obtain ⟨hc₂, hl₂, hp₂⟩ := stepEvents_w3BoundedEvs_aff hM maxReq tl (M.step (.alloc req) st) htl
      simp only [AllocCostModel.stepEvents_cons, nonFreeCount, Nat.add_mul, Nat.one_mul]
      omega
    | aligned al req =>
      obtain ⟨hc₁, hl₁, hp₁⟩ := hM.step_nonFree_aff st hev.1 hev.2
      obtain ⟨hc₂, hl₂, hp₂⟩ := stepEvents_w3BoundedEvs_aff hM maxReq tl (M.step (.aligned al req) st) htl
      simp only [AllocCostModel.stepEvents_cons, nonFreeCount, Nat.add_mul, Nat.one_mul]
      omega
    | realloc al old new =>
      obtain ⟨hc₁, hl₁, hp₁⟩ := hM.step_nonFree_aff st hev.1 hev.2
      obtain ⟨hc₂, hl₂, hp₂⟩ := stepEvents_w3BoundedEvs_aff hM maxReq tl (M.step (.realloc al old new) st) htl
      simp only [AllocCostModel.stepEvents_cons, nonFreeCount, Nat.add_mul, Nat.one_mul]
      omega

/-- Regime-uniform `PhaseCreditSpec` for `W3BoundedEvs maxOps maxReq` under `ModelHyps M`. -/
theorem phaseCreditSpec_w3BoundedEvs_aff
    {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M)
    (maxOps maxReq : Nat) :
    PhaseCreditSpec M (W3BoundedEvs maxOps maxReq)
      (maxOps * (2 * maxReq + 9539))
      (maxOps * (maxReq + 8195))
      (maxOps * (maxReq + 8195))
      maxReq where
  req_align _ hE := hE.2
  credit_le st0 {evs} hE := by
    obtain ⟨hc, hl, hp⟩ := stepEvents_w3BoundedEvs_aff hM maxReq evs st0 hE.2
    have hmulC : nonFreeCount evs * (2 * maxReq + 9539) ≤ maxOps * (2 * maxReq + 9539) :=
      Nat.mul_le_mul_right _ hE.1
    have hmulL : nonFreeCount evs * (maxReq + 8195) ≤ maxOps * (maxReq + 8195) :=
      Nat.mul_le_mul_right _ hE.1
    omega

/-- Appending `FreeOnlyEvs` after `E` preserves `(c, l, p, r)` without requiring `l ≤ p`. -/
theorem phaseCreditSpec_seq_freeOnly
    {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M)
    {E : List AllocEvent → Prop} {c l p r : Nat}
    (h : PhaseCreditSpec M E c l p r) :
    PhaseCreditSpec M (SeqEnv E FreeOnlyEvs) c l p r where
  req_align evs hE ev hev := by
    rcases hE with h1 | ⟨evs₁, evs₂, rfl, h1, h2⟩
    · exact h.req_align evs h1 ev hev
    · rcases List.mem_append.mp hev with he1 | he2
      · exact h.req_align evs₁ h1 ev he1
      · obtain ⟨al, sz, rfl⟩ := h2 ev he2
        exact ⟨Nat.zero_le r, Nat.le_refl 16⟩
  credit_le st0 {_} hE := by
    rcases hE with h1 | ⟨evs₁, evs₂, rfl, h1, h2⟩
    · exact h.credit_le st0 h1
    · rw [M.stepEvents_append evs₁ evs₂ st0]
      obtain ⟨hc₁, hl₁, hp₁⟩ := h.credit_le st0 h1
      obtain ⟨hc₂, hl₂, hp₂⟩ := stepEvents_freeOnly_le hM.freeNonInc h2 (M.stepEvents evs₁ st0)
      exact ⟨Nat.le_trans hc₂ hc₁, Nat.le_trans hl₂ hl₁, Nat.le_trans hp₂ hp₁⟩

/-! ## 2. Parametric Stage 1–5 `PhaseCreditSpec` Composers -/

/-- Stage 1 envelope (`idTrust`, followed by untrusted-identity clone error or SPK/Kyber PK serialize + `sessLoad`).
-/
def W3Stage1Env
    (E_trust E_sessLoad : List AllocEvent → Prop) (nameLen : Nat)
    (evs : List AllocEvent) : Prop :=
  SeqEnv E_trust
    (fun evs' =>
      SeqEnv (· = rustAllocEvents (nameLen + 1) 1) FreeOnlyEvs evs' ∨
      SeqEnv (· = rustAllocEvents 33 1)
        (SeqEnv FreeOnlyEvs
          (SeqEnv (· = rustAllocEvents 1569 1)
            (SeqEnv FreeOnlyEvs E_sessLoad))) evs')
    evs

theorem phaseCreditSpec_w3Stage1_small
    {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M)
    {E_trust E_sessLoad : List AllocEvent → Prop} {nameLen : Nat}
    {c_t l_t p_t r_t c_s l_s p_s r_s : Nat}
    (hname : nameLen ≤ 40)
    (hsmall : 1569 ≤ HasFineReallocCredit.smallMaxReq M)
    (htrust : PhaseCreditSpec M E_trust c_t l_t p_t r_t)
    (hload : PhaseCreditSpec M E_sessLoad c_s l_s p_s r_s) :
    PhaseCreditSpec M (W3Stage1Env E_trust E_sessLoad nameLen)
      (c_t + ((2 * 33 + 9539) + (2 * 1569 + 9539) + c_s))
      (l_t + l_s)
      (max p_t (l_t + p_s))
      (max r_t (max 1569 r_s)) := by
  have hfree := PhaseCreditSpec.freeOnly_of_hyps hM
  have h41_small : 41 ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans (by decide) hsmall
  have h33_small : 33 ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans (by decide) hsmall
  have herr_alloc := phaseCreditSpec_rustAlloc_small_bounded hM
    (req := nameLen + 1) (al := 1) (maxReq := 41) (by decide) (by omega) h41_small
  have herr := phaseCreditSpec_seq_freeOnly hM herr_alloc
  have hpass := (phaseCreditSpec_alloc33_small hM h33_small).seq
    (hfree.seq ((phaseCreditSpec_kemSerialize1569_small hM hsmall).seq (hfree.seq hload)))
  have hbranch := herr.or hpass
  refine (htrust.seq hbranch).mono ?_ (by omega) (by omega) (by omega)
  exact stage1_cum_le c_t c_s _ _ _ (by decide)
where
  stage1_cum_le (c_t c_s k41 k33 k1569 : Nat) (h : k41 ≤ k33 + k1569) :
      c_t + max k41 (k33 + (0 + (k1569 + (0 + c_s)))) ≤ c_t + (k33 + k1569 + c_s) := by
    omega

/-- Stage 2 envelope (`idKeyPair`, followed by error drop, same-account `1568` B clone+free, or `1568` B Kyber SPK clone).
-/
def W3Stage2Env (E_idKp : List AllocEvent → Prop) (evs : List AllocEvent) : Prop :=
  SeqEnv E_idKp
    (fun evs' =>
      SeqEnv (· = rustDeallocEvents 16 8) FreeOnlyEvs evs' ∨
      SeqEnv (ConcatEnv (· = rustAllocEvents 1568 1) (· = rustDeallocEvents 1568 1)) FreeOnlyEvs evs' ∨
      evs' = rustAllocEvents 1568 1)
    evs

theorem phaseCreditSpec_w3Stage2_small
    {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M)
    {E_idKp : List AllocEvent → Prop} {c_k l_k p_k r_k : Nat}
    (hsmall : 1568 ≤ HasFineReallocCredit.smallMaxReq M)
    (hkp : PhaseCreditSpec M E_idKp c_k l_k p_k r_k) :
    PhaseCreditSpec M (W3Stage2Env E_idKp)
      (c_k + (2 * 1568 + 9539))
      l_k
      (max p_k l_k)
      (max r_k 1568) := by
  have hd16 := phaseCreditSpec_seq_freeOnly hM (phaseCreditSpec_segA_dropErr16 M)
  have hclone := phaseCreditSpec_segC_kyberSpkClone_small hM hsmall
  have hd1568 : PhaseCreditSpec M (· = rustDeallocEvents 1568 1) 0 0 0 0 :=
    PhaseCreditSpec.rustDealloc_align16 M (by decide)
  have hsame := phaseCreditSpec_seq_freeOnly hM (hclone.concat hd1568)
  have htail := hd16.or (hsame.or hclone)
  refine (hkp.seq htail).mono ?_ (by omega) (by omega) (by omega)
  exact stage2_cum_le c_k _
where
  stage2_cum_le (c_k k : Nat) : c_k + max 0 (max (k + 0) k) ≤ c_k + k := by omega

/-- Stage 2→3 bracketed envelope cancelling the `1568` B Kyber SPK clone across `E_stage3Body`. -/
def W3Stage23BracketEnv (E_idKp E_stage3Body : List AllocEvent → Prop)
    (evs : List AllocEvent) : Prop :=
  SeqEnv E_idKp
    (fun evs' =>
      SeqEnv (· = rustDeallocEvents 16 8) FreeOnlyEvs evs' ∨
      SeqEnv (ConcatEnv (· = rustAllocEvents 1568 1) (· = rustDeallocEvents 1568 1)) FreeOnlyEvs evs' ∨
      SeqEnv
        (ConcatEnv (ConcatEnv (· = rustAllocEvents 1568 1) E_stage3Body)
          (· = rustDeallocEvents 1568 1))
        FreeOnlyEvs evs')
    evs

theorem phaseCreditSpec_w3Stage23_bracket_aff
    {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M)
    {E_idKp E_stage3Body : List AllocEvent → Prop}
    {c_k l_k p_k r_k c_3 l_3 p_3 r_3 : Nat}
    (hkp : PhaseCreditSpec M E_idKp c_k l_k p_k r_k)
    (hs3 : PhaseCreditSpec M E_stage3Body c_3 l_3 p_3 r_3) :
    PhaseCreditSpec M (W3Stage23BracketEnv E_idKp E_stage3Body)
      (c_k + (2 * 1568 + 9539 + c_3))
      (l_k + l_3)
      (max p_k (l_k + (1568 + 8195 + p_3)))
      (max r_k (max 1568 r_3)) := by
  have hd16 := phaseCreditSpec_seq_freeOnly hM (phaseCreditSpec_segA_dropErr16 M)
  have hsame := phaseCreditSpec_seq_freeOnly hM (phaseCreditSpec_segC_kyberSpkClone_free hM)
  have hpass := phaseCreditSpec_seq_freeOnly hM (phaseCreditSpec_segC_kyberSpkClone_body_free hM hs3)
  have htail := hd16.or (hsame.or hpass)
  refine (hkp.seq htail).mono (stage23_cum_le c_k _ c_3) (by omega)
    (stage23_peak_le p_k l_k _ p_3) (by omega)
where
  stage23_cum_le (c_k k c_3 : Nat) :
      c_k + max 0 (max k (k + c_3)) ≤ c_k + (k + c_3) := by omega
  stage23_peak_le (p_k l_k pk p_3 : Nat) :
      max p_k (l_k + max 0 (max pk (pk + p_3))) ≤ max p_k (l_k + (pk + p_3)) := by omega

/-- Small-regime Stage 3 PQXDH initiator key-agreement bound (`W3BoundedEvs 8 1569`). -/
theorem phaseCreditSpec_w3Stage3_small
    {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M)
    (hsmall : 1569 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (W3BoundedEvs 8 1569)
      (8 * (2 * 1569 + 9539)) 0 0 1569 :=
  phaseCreditSpec_w3BoundedEvs_small hM 8 1569 hsmall

/-- Stage 4 envelope (`create_chain` → `E_spqrInit` → `SessionState` construction). -/
def W3Stage4Env (E_spqrInit : List AllocEvent → Prop) (evs : List AllocEvent) : Prop :=
  SeqEnv (W3BoundedEvs 1 33)
    (SeqEnv E_spqrInit (W3BoundedEvs 13 416))
    evs

theorem phaseCreditSpec_w3Stage4_small
    {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M)
    {E_spqrInit : List AllocEvent → Prop} {c_q l_q p_q r_q : Nat}
    (hsmall : 416 ≤ HasFineReallocCredit.smallMaxReq M)
    (hspqr : PhaseCreditSpec M E_spqrInit c_q l_q p_q r_q) :
    PhaseCreditSpec M (W3Stage4Env E_spqrInit)
      ((2 * 33 + 9539) + c_q + 13 * (2 * 416 + 9539))
      l_q
      (max p_q l_q)
      (max 416 r_q) := by
  have h33 : 33 ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans (by decide) hsmall
  have hpre := phaseCreditSpec_w3BoundedEvs_small hM 1 33 h33
  have hpost := phaseCreditSpec_w3BoundedEvs_small hM 13 416 hsmall
  have h := hpre.seq (hspqr.seq hpost)
  exact h.mono (stage4_cum_le _ c_q _) (by omega) (by omega) (by omega)
where
  stage4_cum_le (k33 c_q kpost : Nat) :
      1 * k33 + (c_q + kpost) ≤ k33 + c_q + kpost := by omega

/-- Stage 5 envelope (pending prekey / `KyberPreKeyId::fmt` → `idRegId` → `idSave` → `sessStore` → `FreeOnlyEvs`).
-/
def W3Stage5Env (E_idRegId E_idSave E_sessStore : List AllocEvent → Prop)
    (evs : List AllocEvent) : Prop :=
  SeqEnv (W3BoundedEvs 4 68)
    (SeqEnv E_idRegId
      (SeqEnv E_idSave
        (SeqEnv E_sessStore FreeOnlyEvs)))
    evs

theorem phaseCreditSpec_w3Stage5_small
    {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M)
    {E_idRegId E_idSave E_sessStore : List AllocEvent → Prop}
    {c_r l_r p_r r_r c_i l_i p_i r_i c_s l_s p_s r_s : Nat}
    (hsmall : 68 ≤ HasFineReallocCredit.smallMaxReq M)
    (hreg : PhaseCreditSpec M E_idRegId c_r l_r p_r r_r)
    (hsave : PhaseCreditSpec M E_idSave c_i l_i p_i r_i)
    (hstore : PhaseCreditSpec M E_sessStore c_s l_s p_s r_s) :
    PhaseCreditSpec M (W3Stage5Env E_idRegId E_idSave E_sessStore)
      (4 * (2 * 68 + 9539) + c_r + c_i + c_s)
      (l_r + l_i + l_s)
      (max p_r (l_r + max p_i (l_i + p_s)))
      (max 68 (max r_r (max r_i r_s))) := by
  have hpre := phaseCreditSpec_w3BoundedEvs_small hM 4 68 hsmall
  have hstoreF := phaseCreditSpec_seq_freeOnly hM hstore
  have h := hpre.seq (hreg.seq (hsave.seq hstoreF))
  exact h.mono (stage5_cum_le _ c_r c_i c_s) (by omega)
    (stage5_peak_le _) (stage5_req_le 68 _)
where
  stage5_cum_le (k c_r c_i c_s : Nat) :
      k + (c_r + (c_i + c_s)) ≤ k + c_r + c_i + c_s := by omega
  stage5_peak_le (p : Nat) : max 0 (0 + p) ≤ p := by omega
  stage5_req_le (a b : Nat) : max a b ≤ max a b := Nat.le_refl _

/-! ## 3. Full 5-Stage `W3InitiateFullEnv` Composition -/

/-- 5-stage `process_prekey_bundle` sequential allocation envelope (`S1 → S2 → S3 → S4 → S5`). -/
def W3InitiateFullEnv
    (E_trust E_sessLoad E_idKp E_spqrInit E_idRegId E_idSave E_sessStore :
      List AllocEvent → Prop)
    (nameLen : Nat) (evs : List AllocEvent) : Prop :=
  SeqEnv
    (SeqEnv
      (SeqEnv
        (SeqEnv (W3Stage1Env E_trust E_sessLoad nameLen) (W3Stage2Env E_idKp))
        (W3BoundedEvs 8 1569))
      (W3Stage4Env E_spqrInit))
    (W3Stage5Env E_idRegId E_idSave E_sessStore)
    evs

/-- Native non-callee small-class cumulative constant of `W3InitiateFullEnv` across Stages 1–5. -/
def w3InitiateNativeSmallCum : Nat :=
  ((2 * 33 + 9539) + (2 * 1569 + 9539)) +
  (2 * 1568 + 9539) +
  8 * (2 * 1569 + 9539) +
  ((2 * 33 + 9539) + 13 * (2 * 416 + 9539)) +
  4 * (2 * 68 + 9539)

private theorem full_cum_reassoc (a1 a2 b c d1 d2 e c_t c_sl c_k c_q c_r c_i c_ss : Nat) :
    ((((c_t + (a1 + a2 + c_sl)) + (c_k + b)) + c) + (d1 + c_q + d2)) + (e + c_r + c_i + c_ss) ≤
      ((a1 + a2) + b + c + (d1 + d2) + e) + c_t + c_sl + c_k + c_q + c_r + c_i + c_ss := by
  omega

private theorem full_live_reassoc (l_t l_sl l_k l_q l_r l_i l_ss : Nat) :
    ((((l_t + l_sl) + l_k) + 0) + l_q) + (l_r + l_i + l_ss) ≤
      (l_t + l_sl + l_k + l_q) + l_r + l_i + l_ss := by
  omega

private theorem full_peak_reassoc (p1 l1 p2 l_k l12 pq l_q l14 p5 : Nat)
    (h12 : l1 + l_k = l12) (h14 : l12 + l_q = l14) :
    max (max (max (max p1 (l1 + p2)) ((l1 + l_k) + 0)) (((l1 + l_k) + 0) + pq))
      ((((l1 + l_k) + 0) + l_q) + p5) ≤
      max (max (max p1 (l1 + p2)) (max l12 (l12 + pq))) (l14 + p5) := by
  subst h12; subst h14
  simp only [Nat.add_zero]
  refine Nat.max_le.mpr ⟨?_, Nat.le_max_right _ _⟩
  refine Nat.le_trans ?_ (Nat.le_max_left _ _)
  refine Nat.max_le.mpr ⟨?_, Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)⟩
  refine Nat.max_le.mpr ⟨Nat.le_max_left _ _,
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)⟩

private theorem full_req_reassoc (r_t r_sl r_k r_q r5 k1568 k1569 k416 k68 : Nat)
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

/-- End-to-end 5-stage `PhaseCreditSpec M` for `W3InitiateFullEnv` under `1569 ≤ smallMaxReq M`. -/
theorem phaseCreditSpec_w3InitiateFull_small
    {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M)
    {E_trust E_sessLoad E_idKp E_spqrInit E_idRegId E_idSave E_sessStore :
      List AllocEvent → Prop}
    {nameLen : Nat}
    {c_t l_t p_t r_t c_sl l_sl p_sl r_sl c_k l_k p_k r_k
     c_q l_q p_q r_q c_r l_r p_r r_r c_i l_i p_i r_i c_ss l_ss p_ss r_ss : Nat}
    (hname : nameLen ≤ 40)
    (hsmall : 1569 ≤ HasFineReallocCredit.smallMaxReq M)
    (htrust : PhaseCreditSpec M E_trust c_t l_t p_t r_t)
    (hload : PhaseCreditSpec M E_sessLoad c_sl l_sl p_sl r_sl)
    (hkp : PhaseCreditSpec M E_idKp c_k l_k p_k r_k)
    (hspqr : PhaseCreditSpec M E_spqrInit c_q l_q p_q r_q)
    (hreg : PhaseCreditSpec M E_idRegId c_r l_r p_r r_r)
    (hsave : PhaseCreditSpec M E_idSave c_i l_i p_i r_i)
    (hstore : PhaseCreditSpec M E_sessStore c_ss l_ss p_ss r_ss) :
    let l12 := l_t + l_sl + l_k
    let l14 := l12 + l_q
    PhaseCreditSpec M
      (W3InitiateFullEnv E_trust E_sessLoad E_idKp E_spqrInit E_idRegId E_idSave E_sessStore
        nameLen)
      (w3InitiateNativeSmallCum + c_t + c_sl + c_k + c_q + c_r + c_i + c_ss)
      (l14 + l_r + l_i + l_ss)
      (max
        (max
          (max (max p_t (l_t + p_sl)) (l_t + l_sl + max p_k l_k))
          (max l12 (l12 + max p_q l_q)))
        (l14 + max p_r (l_r + max p_i (l_i + p_ss))))
      (max 1569
        (max r_t (max r_sl (max r_k (max r_q (max r_r (max r_i r_ss))))))) := by
  intro l12 l14
  have h1568 : 1568 ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans (by decide) hsmall
  have h416 : 416 ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans (by decide) hsmall
  have h68 : 68 ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans (by decide) hsmall
  have hs1 := phaseCreditSpec_w3Stage1_small hM hname hsmall htrust hload
  have hs2 := phaseCreditSpec_w3Stage2_small hM h1568 hkp
  have hs3 := phaseCreditSpec_w3Stage3_small hM hsmall
  have hs4 := phaseCreditSpec_w3Stage4_small hM h416 hspqr
  have hs5 := phaseCreditSpec_w3Stage5_small hM h68 hreg hsave hstore
  have hall := phaseCreditSpec_seq5 hs1 hs2 hs3 hs4 hs5
  exact hall.mono
    (full_cum_reassoc _ _ _ _ _ _ _ c_t c_sl c_k c_q c_r c_i c_ss)
    (full_live_reassoc l_t l_sl l_k l_q l_r l_i l_ss)
    (full_peak_reassoc _ (l_t + l_sl) _ l_k l12 _ l_q l14 _ rfl rfl)
    (full_req_reassoc r_t r_sl r_k r_q _ 1568 1569 416 68 (by decide) (by decide) (by decide))

/-! ## 4. Widened Stage 1 (`nameLen` or `nameLen + 1`) and 5-Stage Twins -/

/-- Widened Stage 1 envelope admitting both `rustAllocEvents (nameLen + 1) 1` and `rustAllocEvents nameLen 1`.
-/
def W3Stage1EnvWide
    (E_trust E_sessLoad : List AllocEvent → Prop) (nameLen : Nat)
    (evs : List AllocEvent) : Prop :=
  SeqEnv E_trust
    (fun evs' =>
      SeqEnv (fun e => e = rustAllocEvents (nameLen + 1) 1 ∨ e = rustAllocEvents nameLen 1)
        FreeOnlyEvs evs' ∨
      SeqEnv (· = rustAllocEvents 33 1)
        (SeqEnv FreeOnlyEvs
          (SeqEnv (· = rustAllocEvents 1569 1)
            (SeqEnv FreeOnlyEvs E_sessLoad))) evs')
    evs

theorem w3Stage1Env_imp_wide
    {E_trust E_sessLoad : List AllocEvent → Prop} {nameLen : Nat} {evs : List AllocEvent}
    (h : W3Stage1Env E_trust E_sessLoad nameLen evs) :
    W3Stage1EnvWide E_trust E_sessLoad nameLen evs := by
  rcases h with ht | ⟨e1, e2, rfl, ht, htail⟩
  · exact Or.inl ht
  · refine Or.inr ⟨e1, e2, rfl, ht, ?_⟩
    rcases htail with herr | hpass
    · refine Or.inl ?_
      rcases herr with ha | ⟨ea, ef, rfl, ha, hf⟩
      · exact Or.inl (Or.inl ha)
      · exact Or.inr ⟨ea, ef, rfl, Or.inl ha, hf⟩
    · exact Or.inr hpass

private theorem w3BoundedEvs_rustAlloc_wide {req al maxReq : Nat}
    (hal : al ≤ 16) (hreq : req ≤ maxReq) :
    W3BoundedEvs 1 maxReq (rustAllocEvents req al) := by
  unfold rustAllocEvents
  split_ifs
  · refine ⟨Nat.le_refl 1, fun ev hev => ?_⟩
    simp only [List.mem_singleton] at hev; subst hev
    exact ⟨hreq, by dsimp [eventStepAlign]; omega⟩
  · refine ⟨Nat.le_refl 1, fun ev hev => ?_⟩
    simp only [List.mem_singleton] at hev; subst hev
    exact ⟨hreq, by dsimp [eventStepAlign]; omega⟩

theorem phaseCreditSpec_w3Stage1Wide_small
    {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M)
    {E_trust E_sessLoad : List AllocEvent → Prop} {nameLen : Nat}
    {c_t l_t p_t r_t c_s l_s p_s r_s : Nat}
    (hname : nameLen ≤ 40)
    (hsmall : 1569 ≤ HasFineReallocCredit.smallMaxReq M)
    (htrust : PhaseCreditSpec M E_trust c_t l_t p_t r_t)
    (hload : PhaseCreditSpec M E_sessLoad c_s l_s p_s r_s) :
    PhaseCreditSpec M (W3Stage1EnvWide E_trust E_sessLoad nameLen)
      (c_t + ((2 * 33 + 9539) + (2 * 1569 + 9539) + c_s))
      (l_t + l_s)
      (max p_t (l_t + p_s))
      (max r_t (max 1569 r_s)) := by
  have hfree := PhaseCreditSpec.freeOnly_of_hyps hM
  have h41_small : 41 ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans (by decide) hsmall
  have h33_small : 33 ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans (by decide) hsmall
  have herr_alloc : PhaseCreditSpec M
      (fun e => e = rustAllocEvents (nameLen + 1) 1 ∨ e = rustAllocEvents nameLen 1)
      (2 * 41 + 9539) 0 0 41 := by
    refine PhaseCreditSpec.of_imp ?_
      ((phaseCreditSpec_w3BoundedEvs_small hM 1 41 h41_small).mono
        (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 41))
    rintro e (rfl | rfl)
    · exact w3BoundedEvs_rustAlloc_wide (by decide) (by omega)
    · exact w3BoundedEvs_rustAlloc_wide (by decide) (by omega)
  have herr := phaseCreditSpec_seq_freeOnly hM herr_alloc
  have hpass := (phaseCreditSpec_alloc33_small hM h33_small).seq
    (hfree.seq ((phaseCreditSpec_kemSerialize1569_small hM hsmall).seq (hfree.seq hload)))
  have hbranch := herr.or hpass
  refine (htrust.seq hbranch).mono ?_ (by omega) (by omega) (by omega)
  exact stage1Wide_cum_le c_t c_s _ _ _ (by decide)
where
  stage1Wide_cum_le (c_t c_s k41 k33 k1569 : Nat) (h : k41 ≤ k33 + k1569) :
      c_t + max k41 (k33 + (0 + (k1569 + (0 + c_s)))) ≤ c_t + (k33 + k1569 + c_s) := by
    omega

/-- 5-stage `process_prekey_bundle` sequential envelope over `W3Stage1EnvWide`. -/
def W3InitiateFullEnvWide
    (E_trust E_sessLoad E_idKp E_spqrInit E_idRegId E_idSave E_sessStore :
      List AllocEvent → Prop)
    (nameLen : Nat) (evs : List AllocEvent) : Prop :=
  SeqEnv
    (SeqEnv
      (SeqEnv
        (SeqEnv (W3Stage1EnvWide E_trust E_sessLoad nameLen) (W3Stage2Env E_idKp))
        (W3BoundedEvs 8 1569))
      (W3Stage4Env E_spqrInit))
    (W3Stage5Env E_idRegId E_idSave E_sessStore)
    evs

private theorem seqEnv_mono_wide {E₁ E₁' E₂ E₂' : List AllocEvent → Prop}
    (h1 : ∀ evs, E₁ evs → E₁' evs) (h2 : ∀ evs, E₂ evs → E₂' evs)
    {evs : List AllocEvent} (h : SeqEnv E₁ E₂ evs) :
    SeqEnv E₁' E₂' evs := by
  rcases h with hE1 | ⟨evs₁, evs₂, rfl, hE1, hE2⟩
  · exact Or.inl (h1 evs hE1)
  · exact Or.inr ⟨evs₁, evs₂, rfl, h1 evs₁ hE1, h2 evs₂ hE2⟩

theorem w3InitiateFullEnv_imp_wide
    {E_trust E_sessLoad E_idKp E_spqrInit E_idRegId E_idSave E_sessStore :
      List AllocEvent → Prop}
    {nameLen : Nat} {evs : List AllocEvent}
    (h : W3InitiateFullEnv E_trust E_sessLoad E_idKp E_spqrInit E_idRegId E_idSave E_sessStore
      nameLen evs) :
    W3InitiateFullEnvWide E_trust E_sessLoad E_idKp E_spqrInit E_idRegId E_idSave E_sessStore
      nameLen evs :=
  seqEnv_mono_wide
    (fun _ h4 => seqEnv_mono_wide
      (fun _ h3 => seqEnv_mono_wide
        (fun _ h2 => seqEnv_mono_wide
          (fun _ h1 => w3Stage1Env_imp_wide h1) (fun _ x => x) h2)
        (fun _ x => x) h3)
      (fun _ x => x) h4)
    (fun _ x => x) h

/-- End-to-end 5-stage `PhaseCreditSpec M` for `W3InitiateFullEnvWide`. -/
theorem phaseCreditSpec_w3InitiateFullWide_small
    {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M)
    {E_trust E_sessLoad E_idKp E_spqrInit E_idRegId E_idSave E_sessStore :
      List AllocEvent → Prop}
    {nameLen : Nat}
    {c_t l_t p_t r_t c_sl l_sl p_sl r_sl c_k l_k p_k r_k
     c_q l_q p_q r_q c_r l_r p_r r_r c_i l_i p_i r_i c_ss l_ss p_ss r_ss : Nat}
    (hname : nameLen ≤ 40)
    (hsmall : 1569 ≤ HasFineReallocCredit.smallMaxReq M)
    (htrust : PhaseCreditSpec M E_trust c_t l_t p_t r_t)
    (hload : PhaseCreditSpec M E_sessLoad c_sl l_sl p_sl r_sl)
    (hkp : PhaseCreditSpec M E_idKp c_k l_k p_k r_k)
    (hspqr : PhaseCreditSpec M E_spqrInit c_q l_q p_q r_q)
    (hreg : PhaseCreditSpec M E_idRegId c_r l_r p_r r_r)
    (hsave : PhaseCreditSpec M E_idSave c_i l_i p_i r_i)
    (hstore : PhaseCreditSpec M E_sessStore c_ss l_ss p_ss r_ss) :
    let l12 := l_t + l_sl + l_k
    let l14 := l12 + l_q
    PhaseCreditSpec M
      (W3InitiateFullEnvWide E_trust E_sessLoad E_idKp E_spqrInit E_idRegId E_idSave E_sessStore
        nameLen)
      (w3InitiateNativeSmallCum + c_t + c_sl + c_k + c_q + c_r + c_i + c_ss)
      (l14 + l_r + l_i + l_ss)
      (max
        (max
          (max (max p_t (l_t + p_sl)) (l_t + l_sl + max p_k l_k))
          (max l12 (l12 + max p_q l_q)))
        (l14 + max p_r (l_r + max p_i (l_i + p_ss))))
      (max 1569
        (max r_t (max r_sl (max r_k (max r_q (max r_r (max r_i r_ss))))))) := by
  intro l12 l14
  have h1568 : 1568 ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans (by decide) hsmall
  have h416 : 416 ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans (by decide) hsmall
  have h68 : 68 ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans (by decide) hsmall
  have hs1 := phaseCreditSpec_w3Stage1Wide_small hM hname hsmall htrust hload
  have hs2 := phaseCreditSpec_w3Stage2_small hM h1568 hkp
  have hs3 := phaseCreditSpec_w3Stage3_small hM hsmall
  have hs4 := phaseCreditSpec_w3Stage4_small hM h416 hspqr
  have hs5 := phaseCreditSpec_w3Stage5_small hM h68 hreg hsave hstore
  have hall := phaseCreditSpec_seq5 hs1 hs2 hs3 hs4 hs5
  exact hall.mono
    (full_cum_reassoc _ _ _ _ _ _ _ c_t c_sl c_k c_q c_r c_i c_ss)
    (full_live_reassoc l_t l_sl l_k l_q l_r l_i l_ss)
    (full_peak_reassoc _ (l_t + l_sl) _ l_k l12 _ l_q l14 _ rfl rfl)
    (full_req_reassoc r_t r_sl r_k r_q _ 1568 1569 416 68 (by decide) (by decide) (by decide))

end LibsignalBinary.Proofs.PeakBudget.W3InitiateStagesPeak
