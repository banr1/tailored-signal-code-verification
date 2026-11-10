/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit

/-!
# Leaf and Helper Peak Bounds for W3 `process_prekey_bundle`

`PhaseCreditSpec` leaf and stage-composition lemmas for W3 `process_prekey_bundle` (`Initiate`
Stages 1–5), parametric in `(M : AllocCostModel) [HasFineReallocCredit M]` under `ModelHyps M`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.W3InitiateHelpers

open LibsignalBinary.Heap
  (AllocCostModel AllocEvent FreeOnlyEvs SeqEnv
   rustAllocEvents rustDeallocEvents rustReallocEvents)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit
  (HasFineReallocCredit)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
  (ConcatEnv DeallocCreditSpec FreeNonInc IterConcatEnv IterSeqEnv ModelHyps PhaseCreditSpec)

/-! ## 1. Stage 1 and Stage 5 Fixed-Layout Allocation Leaves -/

theorem phaseCreditSpec_alloc33
    {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M) :
    PhaseCreditSpec M (· = rustAllocEvents 33 1)
      (2 * 33 + 9539) (33 + 8195) (33 + 8195) 33 :=
  PhaseCreditSpec.rustAlloc_aff hM (by decide)

theorem phaseCreditSpec_alloc33_small
    {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M)
    (hle : 33 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (· = rustAllocEvents 33 1)
      (2 * 33 + 9539) 0 0 33 :=
  (PhaseCreditSpec.rustAlloc_small M (by decide) (by decide) hle).mono
    (hM.smallAlloc_le hle) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 33)

theorem phaseCreditSpec_kemSerialize1569_small
    {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M)
    (hle : 1569 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (· = rustAllocEvents 1569 1)
      (2 * 1569 + 9539) 0 0 1569 :=
  (PhaseCreditSpec.rustAlloc_small M (by decide) (by decide) hle).mono
    (hM.smallAlloc_le hle) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 1569)

theorem phaseCreditSpec_kemSerialize1569_aff
    {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M) :
    PhaseCreditSpec M (· = rustAllocEvents 1569 1)
      (2 * 1569 + 9539) (1569 + 8195) (1569 + 8195) 1569 :=
  PhaseCreditSpec.rustAlloc_aff hM (by decide)

theorem phaseCreditSpec_kyberPreKeyIdDisplay14_small
    {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M)
    (hle : 14 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (· = rustAllocEvents 14 1)
      (2 * 14 + 9539) 0 0 14 :=
  (PhaseCreditSpec.rustAlloc_small M (by decide) (by decide) hle).mono
    (hM.smallAlloc_le hle) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 14)

theorem phaseCreditSpec_rustAlloc_small_bounded
    {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M)
    {req al maxReq : Nat} (hal : al ≤ 16) (hreq : req ≤ maxReq)
    (hsmall : maxReq ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (· = rustAllocEvents req al)
      (2 * maxReq + 9539) 0 0 maxReq := by
  have hle : req ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans hreq hsmall
  have hsa := hM.smallAlloc_le hle
  exact (PhaseCreditSpec.rustAlloc_small_any hM hal hle).mono
    (by omega) (Nat.le_refl 0) (Nat.le_refl 0) hreq

/-! ## 2. Stage 2 `1568` B Kyber SPK Clone and Error Deallocation -/

theorem phaseCreditSpec_segA_dropErr16
    (M : AllocCostModel) [HasFineReallocCredit M] :
    PhaseCreditSpec M (· = rustDeallocEvents 16 8) 0 0 0 0 :=
  PhaseCreditSpec.rustDealloc_align16 M (by decide)

theorem phaseCreditSpec_segC_kyberSpkClone_small
    {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M)
    (hle : 1568 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (· = rustAllocEvents 1568 1)
      (2 * 1568 + 9539) 0 0 1568 :=
  phaseCreditSpec_rustAlloc_small_bounded hM (by decide) (Nat.le_refl 1568) hle

theorem phaseCreditSpec_segC_kyberSpkClone
    {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M) :
    PhaseCreditSpec M (· = rustAllocEvents 1568 1)
      (2 * 1568 + 9539) (1568 + 8195) (1568 + 8195) 1568 :=
  PhaseCreditSpec.rustAlloc_aff hM (by decide)

theorem phaseCreditSpec_segC_kyberSpkClone_free
    {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M) :
    PhaseCreditSpec M
      (ConcatEnv (· = rustAllocEvents 1568 1) (· = rustDeallocEvents 1568 1))
      (2 * 1568 + 9539) 0 (1568 + 8195) 1568 :=
  PhaseCreditSpec.tempAllocFree_aff hM (by decide)

/-- Bracketed `1568` B Kyber SPK clone + body + `rustDeallocEvents 1568 1` cancellation (`Δlive = l_b`).
-/
theorem phaseCreditSpec_segC_kyberSpkClone_body_free
    {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M)
    {E_body : List AllocEvent → Prop} {c_b l_b p_b r_b : Nat}
    (hbody : PhaseCreditSpec M E_body c_b l_b p_b r_b) :
    PhaseCreditSpec M
      (ConcatEnv (ConcatEnv (· = rustAllocEvents 1568 1) E_body) (· = rustDeallocEvents 1568 1))
      (2 * 1568 + 9539 + c_b) l_b (1568 + 8195 + p_b) (max 1568 r_b) :=
  PhaseCreditSpec.tempAllocBodyFree_aff hM (by decide) hbody

/-! ## 3. Stage 3 `do_reserve` and Optional `DH4` Helpers -/

/-- Small-regime bound for `Vec<u8>::do_reserve_and_handle`. -/
theorem phaseCreditSpec_doReserve_raw_small
    {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M)
    (cap len add : BitVec 64) {maxCap : Nat}
    (hcap : max (2 * cap.toNat) (max (len.toNat + add.toNat) 8) ≤ maxCap)
    (hsmall : maxCap ≤ HasFineReallocCredit.smallMaxReq M) :
    let newCap := max (2 * cap.toNat) (max (len.toNat + add.toNat) 8)
    PhaseCreditSpec M
      (fun evs => evs = if cap = 0#64 then rustAllocEvents newCap 1
                        else rustReallocEvents cap.toNat newCap 1)
      (2 * maxCap + 9539) 0 0 maxCap := by
  intro newCap
  have hnew_pos : 1 ≤ newCap := by dsimp [newCap]; omega
  have hnew_small : newCap ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans hcap hsmall
  have hold_small : cap.toNat ≤ HasFineReallocCredit.smallMaxReq M := by
    have : cap.toNat ≤ newCap := by dsimp [newCap]; omega
    exact Nat.le_trans this hnew_small
  split
  · exact phaseCreditSpec_rustAlloc_small_bounded hM (by decide) hcap hsmall
  · rename_i hne
    have hold_pos : 0 < cap.toNat := by
      have : cap.toNat ≠ 0 := fun h0 => hne (BitVec.eq_of_toNat_eq h0)
      omega
    have hsr := hM.smallRealloc_le hnew_small
    exact (PhaseCreditSpec.rustRealloc_small_small M (old := cap.toNat) (new := newCap) (al := 1)
      (by decide) hnew_pos hold_pos hold_small hnew_pos hnew_small).mono
      (by omega) (Nat.le_refl 0) (Nat.le_refl 0) hcap

theorem phaseCreditSpec_optDh4_small
    {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M)
    (hasOpk : Bool) (hle : 33 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M
      (fun evs => evs = if hasOpk then rustAllocEvents 33 1 else [])
      (if hasOpk then 2 * 33 + 9539 else 0) 0 0 (if hasOpk then 33 else 0) := by
  cases hasOpk
  · simpa using PhaseCreditSpec.nil M
  · simpa using phaseCreditSpec_alloc33_small hM hle

/-! ## 4. Event-List Concatenation and Stage 4 `SessionState` Helpers -/

theorem phaseCreditSpec_eq_append
    {M : AllocCostModel} [HasFineReallocCredit M]
    {evs₁ evs₂ : List AllocEvent} {c₁ l₁ p₁ r₁ c₂ l₂ p₂ r₂ : Nat}
    (h₁ : PhaseCreditSpec M (· = evs₁) c₁ l₁ p₁ r₁)
    (h₂ : PhaseCreditSpec M (· = evs₂) c₂ l₂ p₂ r₂) :
    PhaseCreditSpec M (· = evs₁ ++ evs₂)
      (c₁ + c₂) (l₁ + l₂) (max p₁ (l₁ + p₂)) (max r₁ r₂) :=
  (h₁.concat h₂).of_imp fun _ h => h ▸ ConcatEnv.append rfl rfl

theorem phaseCreditSpec_alloc32_small
    {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M)
    (hle : 32 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (· = rustAllocEvents 32 1)
      (2 * 32 + 9539) 0 0 32 :=
  (PhaseCreditSpec.rustAlloc_small M (by decide) (by decide) hle).mono
    (hM.smallAlloc_le hle) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 32)

theorem phaseCreditSpec_growOneChain416_small
    {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M)
    (hle : 416 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (· = rustAllocEvents 416 8)
      (2 * 416 + 9539) 0 0 416 :=
  (PhaseCreditSpec.rustAlloc_small M (by decide) (by decide) hle).mono
    (hM.smallAlloc_le hle) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 416)

theorem phaseCreditSpec_sessionStateNew_small
    {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M)
    (hle : 33 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M
      (· = rustAllocEvents 33 1 ++ rustAllocEvents 33 1 ++
            rustAllocEvents 32 1 ++ rustAllocEvents 33 1)
      (3 * (2 * 33 + 9539) + (2 * 32 + 9539)) 0 0 33 := by
  have h32 : 32 ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans (by decide) hle
  have h1 := phaseCreditSpec_alloc33_small hM hle
  have h2 := phaseCreditSpec_alloc32_small hM h32
  have h := phaseCreditSpec_eq_append
    (phaseCreditSpec_eq_append (phaseCreditSpec_eq_append h1 h1) h2) h1
  exact h.mono (by omega) (by omega) (by omega) (by omega)

theorem phaseCreditSpec_withSenderChainNone_small
    {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M)
    (hle : 33 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M
      (· = rustAllocEvents 32 1 ++ rustAllocEvents 33 1 ++ rustAllocEvents 33 1 ++
            rustAllocEvents 32 1 ++ rustAllocEvents 32 1 ++
            rustDeallocEvents 32 1 ++ rustDeallocEvents 33 1)
      (2 * (2 * 33 + 9539) + 3 * (2 * 32 + 9539)) 0 0 33 := by
  have h32 : 32 ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans (by decide) hle
  have a33 := phaseCreditSpec_alloc33_small hM hle
  have a32 := phaseCreditSpec_alloc32_small hM h32
  have d32 : PhaseCreditSpec M (· = rustDeallocEvents 32 1) 0 0 0 0 :=
    PhaseCreditSpec.rustDealloc_align16 M (by decide)
  have d33 : PhaseCreditSpec M (· = rustDeallocEvents 33 1) 0 0 0 0 :=
    PhaseCreditSpec.rustDealloc_align16 M (by decide)
  have h := phaseCreditSpec_eq_append
    (phaseCreditSpec_eq_append
      (phaseCreditSpec_eq_append
        (phaseCreditSpec_eq_append
          (phaseCreditSpec_eq_append
            (phaseCreditSpec_eq_append a32 a33) a33) a32) a32) d32) d33
  exact h.mono (by omega) (by omega) (by omega) (by omega)

theorem phaseCreditSpec_withReceiverChainEmpty_small
    {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M)
    (hle : 416 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M
      (· = rustAllocEvents 32 1 ++ rustAllocEvents 33 1 ++ rustAllocEvents 33 1 ++
            rustDeallocEvents 33 1 ++ rustAllocEvents 416 8)
      ((2 * 32 + 9539) + 2 * (2 * 33 + 9539) + (2 * 416 + 9539)) 0 0 416 := by
  have h33 : 33 ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans (by decide) hle
  have h32 : 32 ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans (by decide) hle
  have a32 := phaseCreditSpec_alloc32_small hM h32
  have a33 := phaseCreditSpec_alloc33_small hM h33
  have d33 : PhaseCreditSpec M (· = rustDeallocEvents 33 1) 0 0 0 0 :=
    PhaseCreditSpec.rustDealloc_align16 M (by decide)
  have a416 := phaseCreditSpec_growOneChain416_small hM hle
  have h := phaseCreditSpec_eq_append
    (phaseCreditSpec_eq_append
      (phaseCreditSpec_eq_append
        (phaseCreditSpec_eq_append a32 a33) a33) d33) a416
  exact h.mono (by omega) (by omega) (by omega) (by omega)

theorem phaseCreditSpec_setUnackPreKeyMsg_small
    {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M)
    (hle : 33 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M
      (· = rustAllocEvents 33 1 ++ rustAllocEvents 33 1 ++ rustDeallocEvents 33 1)
      (2 * (2 * 33 + 9539)) 0 0 33 := by
  have a33 := phaseCreditSpec_alloc33_small hM hle
  have d33 : PhaseCreditSpec M (· = rustDeallocEvents 33 1) 0 0 0 0 :=
    PhaseCreditSpec.rustDealloc_align16 M (by decide)
  have h := phaseCreditSpec_eq_append (phaseCreditSpec_eq_append a33 a33) d33
  exact h.mono (by omega) (by omega) (by omega) (by omega)

/-! ## 5. Stage 5 Deallocation and 5-Stage Sequential Composition -/

theorem phaseCreditSpec_callKit_dealloc
    {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M) (size align : Nat) :
    PhaseCreditSpec M (· = rustDeallocEvents size align) 0 0 0 0 :=
  PhaseCreditSpec.rustDealloc hM.freeNonInc size align

theorem phaseCreditSpec_dropSessionStructure
    {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M) :
    PhaseCreditSpec M FreeOnlyEvs 0 0 0 0 :=
  PhaseCreditSpec.freeOnly_of_hyps hM

/-- Left-associated 5-stage `SeqEnv` `PhaseCreditSpec` composition. -/
theorem phaseCreditSpec_seq5
    {M : AllocCostModel} [HasFineReallocCredit M]
    {E₁ E₂ E₃ E₄ E₅ : List AllocEvent → Prop}
    {c₁ l₁ p₁ r₁ c₂ l₂ p₂ r₂ c₃ l₃ p₃ r₃ c₄ l₄ p₄ r₄ c₅ l₅ p₅ r₅ : Nat}
    (h₁ : PhaseCreditSpec M E₁ c₁ l₁ p₁ r₁)
    (h₂ : PhaseCreditSpec M E₂ c₂ l₂ p₂ r₂)
    (h₃ : PhaseCreditSpec M E₃ c₃ l₃ p₃ r₃)
    (h₄ : PhaseCreditSpec M E₄ c₄ l₄ p₄ r₄)
    (h₅ : PhaseCreditSpec M E₅ c₅ l₅ p₅ r₅) :
    PhaseCreditSpec M
      (SeqEnv (SeqEnv (SeqEnv (SeqEnv E₁ E₂) E₃) E₄) E₅)
      ((((c₁ + c₂) + c₃) + c₄) + c₅)
      ((((l₁ + l₂) + l₃) + l₄) + l₅)
      (max (max (max (max p₁ (l₁ + p₂)) ((l₁ + l₂) + p₃)) (((l₁ + l₂) + l₃) + p₄))
        ((((l₁ + l₂) + l₃) + l₄) + p₅))
      (max (max (max (max r₁ r₂) r₃) r₄) r₅) :=
  (((h₁.seq h₂).seq h₃).seq h₄).seq h₅

/-- Right-associated 5-stage `SeqEnv` `PhaseCreditSpec` composition. -/
theorem phaseCreditSpec_seq5_right
    {M : AllocCostModel} [HasFineReallocCredit M]
    {E₁ E₂ E₃ E₄ E₅ : List AllocEvent → Prop}
    {c₁ l₁ p₁ r₁ c₂ l₂ p₂ r₂ c₃ l₃ p₃ r₃ c₄ l₄ p₄ r₄ c₅ l₅ p₅ r₅ : Nat}
    (h₁ : PhaseCreditSpec M E₁ c₁ l₁ p₁ r₁)
    (h₂ : PhaseCreditSpec M E₂ c₂ l₂ p₂ r₂)
    (h₃ : PhaseCreditSpec M E₃ c₃ l₃ p₃ r₃)
    (h₄ : PhaseCreditSpec M E₄ c₄ l₄ p₄ r₄)
    (h₅ : PhaseCreditSpec M E₅ c₅ l₅ p₅ r₅) :
    PhaseCreditSpec M
      (SeqEnv E₁ (SeqEnv E₂ (SeqEnv E₃ (SeqEnv E₄ E₅))))
      (c₁ + (c₂ + (c₃ + (c₄ + c₅))))
      (l₁ + (l₂ + (l₃ + (l₄ + l₅))))
      (max p₁ (l₁ + max p₂ (l₂ + max p₃ (l₃ + max p₄ (l₄ + p₅)))))
      (max r₁ (max r₂ (max r₃ (max r₄ r₅)))) :=
  h₁.seq (h₂.seq (h₃.seq (h₄.seq h₅)))

end LibsignalBinary.Proofs.PeakBudget.W3InitiateHelpers
