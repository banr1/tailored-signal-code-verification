/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.VecVecDefsBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.ChainClone4PlacedMidBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.LeavesBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitStep12Budget

/-!
# W4 Inner Handshake Primitive and Cancellation Helpers

Parametric `(M : AllocCostModel) [HasFineReallocCredit M]` helper lemmas over `SeqCreditKit` for the
W4 inner handshake family: optional single-buffer alloc/dealloc cancellation (`OptRustAllocEnv`),
1-element `Vec<Vec<u8>>` clone cancellation (`VecVecClone1Env`), bounded `≤ k`-iteration zero-live
loops, `init_bob` KEM/reserve primitives, and `Chain::clone` `MessageKey` loop cancellation.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.W4InnerHelpers

open LibsignalBinary.Heap (
  AllocEvent AllocCostModel FreeOnlyEvs
  rustAllocEvents rustDeallocEvents rustReallocEvents
)
open LibsignalBinary.Heap.Fine.ClientBounds (eventStepReq eventStepAlign)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open CryptoGames.LibsignalSession (MessageKeyGenerator ReceiverChain)
open CryptoVerification.LibsignalTripleRatchet (DoReserveCall reserveCap)
open CryptoVerification.LibsignalSessionRepr (ChainGhost)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (
  ConcatEnv IterConcatEnv IterSeqEnv ModelHyps PhaseCreditSpec DeallocCreditSpec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.VecVecDefsBudget (
  VecVecClone1Ghost vecVecClone1Events VecVecClone1Env
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.ChainClone4PlacedMidBudget (
  chainClonePreMkEvents mkLoopEvents chainCloneMkEvents
)
open LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.LeavesBudget (
  doReserveEvents DoReserveEnv KemSerialize1569Env
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  chainKeyToPbEvents publicKeySerializeEvents
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitStep12Budget (
  dhCommitStep12Events DhCommitStep12Env
)

/-! ## 1. Optional-Empty Single-Allocation Helpers -/

/-- `FreeOnlyEvs` suffix composition preserving `(c, l, p, r)` directly. -/
theorem phaseCredit_concat_freeOnly {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {E : List AllocEvent → Prop} {c l p r : Nat}
    (hE : PhaseCreditSpec M E c l p r) :
    PhaseCreditSpec M (ConcatEnv E FreeOnlyEvs) c l p r := by
  have hE' : PhaseCreditSpec M E c (l + 0) p r := hE
  exact hE'.concat_dealloc_cancel (DeallocCreditSpec.freeOnly_of_hyps hM)

/-- Exact-order envelope for Rust `Vec` clone buffer allocation that skips allocation on `n = 0`. -/
def OptRustAllocEnv (n al : Nat) : List AllocEvent → Prop :=
  if n = 0 then (· = []) else (· = rustAllocEvents n al)

/-- Exact-order envelope for Rust `Vec` buffer drop that skips deallocation on `n = 0`. -/
def OptRustDeallocEnv (n al : Nat) : List AllocEvent → Prop :=
  if n = 0 then (· = []) else (· = rustDeallocEvents n al)

/-- Regime-uniform `PhaseCreditSpec` for `OptRustAllocEnv n al` (`al ≤ 16`, `n ≤ cap`). -/
theorem phaseCredit_optRustAlloc_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {n al cap : Nat} (hal : al ≤ 16) (hn : n ≤ cap) :
    PhaseCreditSpec M (OptRustAllocEnv n al)
      (if n = 0 then 0 else 2 * cap + 9539)
      (if n = 0 then 0 else cap + 8195)
      (if n = 0 then 0 else cap + 8195)
      cap := by
  by_cases h0 : n = 0
  · unfold OptRustAllocEnv
    simp only [h0, ↓reduceIte]
    exact (PhaseCreditSpec.nil M).mono (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  · unfold OptRustAllocEnv
    simp only [h0, ↓reduceIte]
    by_cases hle : n ≤ HasFineReallocCredit.smallMaxReq M
    · have hs := PhaseCreditSpec.rustAlloc_small_any hM hal hle
      have hsa := hM.smallAlloc_le hle
      exact hs.mono (by omega) (Nat.zero_le _) (Nat.zero_le _) hn
    · have hgt : HasFineReallocCredit.smallMaxReq M < n := by omega
      have hl := PhaseCreditSpec.rustAlloc_large M hal hgt
      have hm := hM.meta_le
      have hla := hM.largeCost_le hgt
      exact hl.mono (by omega) (by omega) (by omega) hn

theorem phaseCredit_optRustAlloc_ub {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {n al cap : Nat} (hal : al ≤ 16) (hn : n ≤ cap) :
    PhaseCreditSpec M (OptRustAllocEnv n al)
      (2 * cap + 9539) (cap + 8195) (cap + 8195) cap := by
  refine (phaseCredit_optRustAlloc_aff hM hal hn).mono ?_ ?_ ?_ (Nat.le_refl _)
  · by_cases h0 : n = 0 <;> simp only [h0, ↓reduceIte] <;> omega
  · by_cases h0 : n = 0 <;> simp only [h0, ↓reduceIte] <;> omega
  · by_cases h0 : n = 0 <;> simp only [h0, ↓reduceIte] <;> omega

/-- Bracketed `OptRustAllocEnv n al ++ E_body ++ OptRustDeallocEnv n al` cancellation (`Δlive = l_b`).
-/
theorem phaseCredit_optRustAllocBodyDealloc_cancel {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {n al cap : Nat} {E_body : List AllocEvent → Prop}
    {c_b l_b p_b r_b : Nat}
    (hal : al ≤ 16) (hn : n ≤ cap)
    (hbody : PhaseCreditSpec M E_body c_b l_b p_b r_b) :
    PhaseCreditSpec M
      (ConcatEnv (ConcatEnv (OptRustAllocEnv n al) E_body) (OptRustDeallocEnv n al))
      ((2 * cap + 9539) + c_b)
      l_b
      ((cap + 8195) + p_b)
      (max cap r_b) := by
  by_cases h0 : n = 0
  · unfold OptRustAllocEnv OptRustDeallocEnv
    simp only [h0, ↓reduceIte]
    have ha := PhaseCreditSpec.nil M
    have hd := DeallocCreditSpec.nil M
    have h12 : PhaseCreditSpec M (ConcatEnv (· = []) E_body)
        ((2 * cap + 9539) + c_b) (l_b + 0) ((cap + 8195) + p_b) (max cap r_b) :=
      (ha.concat hbody).mono (by omega) (by omega) (by omega) (by omega)
    exact h12.concat_dealloc_cancel hd
  · unfold OptRustAllocEnv OptRustDeallocEnv
    simp only [h0, ↓reduceIte]
    by_cases hle : n ≤ HasFineReallocCredit.smallMaxReq M
    · have ha := PhaseCreditSpec.rustAlloc_small_any hM hal hle
      have hsa := hM.smallAlloc_le hle
      have hd := DeallocCreditSpec.free_small M hal hle
      have h12 :
          PhaseCreditSpec M (ConcatEnv (· = rustAllocEvents n al) E_body)
            ((2 * cap + 9539) + c_b) (l_b + 0) ((cap + 8195) + p_b) (max cap r_b) :=
        (ha.concat hbody).mono (by omega) (by omega) (by omega) (by omega)
      exact h12.concat_dealloc_cancel hd
    · have hgt : HasFineReallocCredit.smallMaxReq M < n := by omega
      have hm := hM.meta_le
      have hla := hM.largeCost_le hgt
      have hcancel := PhaseCreditSpec.largeAllocBodyFree_cancel hal hgt hbody
      exact hcancel.mono (by omega) (Nat.le_refl _) (by omega) (by omega)

/-! ## 2. `<Vec<Vec<u8>> as Clone>::clone` (`len = 1`) Helpers -/

theorem vecVecClone1Env_iff_concat (x : VecVecClone1Ghost) (evs : List AllocEvent) :
    VecVecClone1Env x evs ↔
      ConcatEnv (· = rustAllocEvents 24 8) (OptRustAllocEnv x.enc.length 1) evs := by
  by_cases h0 : x.enc.length = 0
  · simp only [VecVecClone1Env, vecVecClone1Events, OptRustAllocEnv, h0, ↓reduceIte, ConcatEnv]
    constructor
    · intro h
      exact ⟨rustAllocEvents 24 8, [], by simp [h], rfl, rfl⟩
    · rintro ⟨_, _, rfl, rfl, rfl⟩
      simp
  · simp only [VecVecClone1Env, vecVecClone1Events, OptRustAllocEnv, h0, ↓reduceIte, ConcatEnv]
    constructor
    · intro h
      exact ⟨rustAllocEvents 24 8, rustAllocEvents x.enc.length 1, h, rfl, rfl⟩
    · rintro ⟨_, _, rfl, rfl, rfl⟩
      rfl

/-- `PhaseCreditSpec` for `VecVecClone1Env x` when `x.enc.length ≤ encCap`. -/
theorem phaseCredit_vecVecClone1 {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {x : VecVecClone1Ghost} {encCap : Nat}
    (hSmall24 : 24 ≤ HasFineReallocCredit.smallMaxReq M)
    (henc : x.enc.length ≤ encCap) :
    PhaseCreditSpec M (VecVecClone1Env x)
      (9587 + (2 * encCap + 9539))
      (encCap + 8195)
      (encCap + 8195)
      (max 24 encCap) := by
  have h24 : PhaseCreditSpec M (· = rustAllocEvents 24 8) 9587 0 0 24 :=
    (PhaseCreditSpec.rustAlloc_small_any hM (by decide : 8 ≤ 16) hSmall24).mono
      (hM.smallAlloc_le hSmall24) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 24)
  have he := phaseCredit_optRustAlloc_ub hM (by decide : 1 ≤ 16) henc
  have hc := (h24.concat he).of_imp fun evs h => (vecVecClone1Env_iff_concat x evs).mp h
  refine hc.mono (Nat.le_refl _) ?_ ?_ (Nat.le_refl _)
  · simp only [Nat.zero_add]; exact Nat.le_refl _
  · simp only [Nat.zero_add, Nat.zero_max]; exact Nat.le_refl _

/-- `VecVecClone1Env x ++ E_body ++ E_drop` cancellation (`Δlive = l_b`). -/
theorem phaseCredit_vecVecClone1_body_free_cancel {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {x : VecVecClone1Ghost} {encCap : Nat}
    {E_body E_drop : List AllocEvent → Prop} {c_b l_b p_b r_b : Nat}
    (hSmall24 : 24 ≤ HasFineReallocCredit.smallMaxReq M)
    (henc : x.enc.length ≤ encCap)
    (hbody : PhaseCreditSpec M E_body c_b l_b p_b r_b)
    (hdrop : ∀ evs, E_drop evs →
      ConcatEnv (OptRustDeallocEnv x.enc.length 1) FreeOnlyEvs evs) :
    PhaseCreditSpec M
      (ConcatEnv (ConcatEnv (VecVecClone1Env x) E_body) E_drop)
      (9587 + (2 * encCap + 9539) + c_b)
      l_b
      ((encCap + 8195) + p_b)
      (max 24 (max encCap r_b)) := by
  have h24 := PhaseCreditSpec.rustAlloc_small_any hM (by decide : 8 ≤ 16) hSmall24
  have h24_aff := hM.smallAlloc_le hSmall24
  have dinner := phaseCredit_optRustAllocBodyDealloc_cancel hM (n := x.enc.length) (al := 1)
    (cap := encCap) (by decide) henc hbody
  have houter := h24.concat dinner
  have hrew : ∀ evs,
      ConcatEnv (ConcatEnv (VecVecClone1Env x) E_body) E_drop evs →
      ConcatEnv
        (ConcatEnv (· = rustAllocEvents 24 8)
          (ConcatEnv (ConcatEnv (OptRustAllocEnv x.enc.length 1) E_body)
            (OptRustDeallocEnv x.enc.length 1)))
        FreeOnlyEvs evs := by
    rintro _ ⟨evs12, evs3, rfl, ⟨evs1, evs2, rfl, hv1, hb⟩, hd⟩
    obtain ⟨evs_24, evs_in, rfl, h24_eq, hin⟩ := (vecVecClone1Env_iff_concat x evs1).mp hv1
    obtain ⟨evs_din, evs_fo, rfl, hdin, hfo⟩ := hdrop evs3 hd
    refine ⟨evs_24 ++ ((evs_in ++ evs2) ++ evs_din), evs_fo, by simp [List.append_assoc], ?_, hfo⟩
    refine ⟨evs_24, (evs_in ++ evs2) ++ evs_din, rfl, h24_eq, ?_⟩
    exact ⟨evs_in ++ evs2, evs_din, rfl, ⟨evs_in, evs2, rfl, hin, hb⟩, hdin⟩
  have hfull := phaseCredit_concat_freeOnly hM houter
  exact (hfull.of_imp hrew).mono (by omega) (by omega) (by omega) (by omega)

/-! ## 3. Bounded `≤ k`-Iteration Zero-Live Loop Helper -/

/-- Bounded-length `IterSeqEnv` wrapper when each step leaves `Δlive = 0` (`Δcum ≤ k * c`, `Δlive = 0`, `Δpeak ≤ p`).
-/
theorem phaseCredit_iter_zero_live_le {α : Type} {M : AllocCostModel} [HasFineReallocCredit M]
    {Step : α → List AllocEvent → Prop} {xs : List α} {k c p r : Nat}
    (hlen : xs.length ≤ k)
    (hstep : ∀ x ∈ xs, PhaseCreditSpec M (Step x) c 0 p r) :
    PhaseCreditSpec M (IterSeqEnv Step xs) (k * c) 0 p r := by
  have hit := PhaseCreditSpec.iter_zero_live xs hstep
  have hmul : xs.length * c ≤ k * c := Nat.mul_le_mul_right c hlen
  exact hit.mono hmul (Nat.le_refl 0) (Nat.le_refl p) (Nat.le_refl r)

/-! ## 4. `init_bob` KEM Serialize and `DoReserveEnv` Helpers -/

theorem phaseCredit_kemSerialize1569 {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M)
    (hSmall1569 : 1569 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M KemSerialize1569Env 12677 0 0 1569 := by
  have h := PhaseCreditSpec.rustAlloc_small_any hM (by decide : 1 ≤ 16) hSmall1569
  have ha := hM.smallAlloc_le hSmall1569
  exact (h.of_imp fun _ he => he).mono (by omega) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 1569)

/-- Small-regime `PhaseCreditSpec` for `DoReserveEnv x` (`≤ cap ≤ smallMaxReq M`). -/
theorem phaseCredit_doReserve_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {x : DoReserveCall} {cap : Nat}
    (hold : x.cap.toNat ≤ cap)
    (hnew : reserveCap x.cap.toNat x.bs.length x.additional ≤ cap)
    (hSmall : cap ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (DoReserveEnv x) (2 * cap + 9539) 0 0 cap := by
  set newCap := reserveCap x.cap.toNat x.bs.length x.additional
  have hold_s : x.cap.toNat ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans hold hSmall
  have hnew_s : newCap ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans hnew hSmall
  by_cases hc0 : x.cap = 0#64
  · have h := PhaseCreditSpec.rustAlloc_small_any hM (req := newCap) (al := 1) (by decide) hnew_s
    have ha := hM.smallAlloc_le hnew_s
    have heq : ∀ evs, DoReserveEnv x evs → evs = rustAllocEvents newCap 1 := by
      intro evs he
      simpa [DoReserveEnv, doReserveEvents, hc0, newCap] using he
    exact (h.of_imp heq).mono (by omega) (Nat.le_refl 0) (Nat.le_refl 0) hnew
  · refine ⟨?_, ?_⟩
    · intro evs he ev hev
      have he' : evs = rustReallocEvents x.cap.toNat newCap 1 := by
        simpa [DoReserveEnv, doReserveEvents, hc0, newCap] using he
      subst he'
      unfold rustReallocEvents at hev
      split at hev
      · simp only [List.mem_singleton] at hev
        subst hev
        exact ⟨hnew, by simp only [eventStepAlign]; decide⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hev
        rcases hev with rfl | rfl
        · exact ⟨hnew, by simp only [eventStepAlign]; decide⟩
        · exact ⟨Nat.zero_le _, by simp only [eventStepAlign]; decide⟩
    · intro st0 evs he
      have he' : evs = rustReallocEvents x.cap.toNat newCap 1 := by
        simpa [DoReserveEnv, doReserveEvents, hc0, newCap] using he
      subst he'
      unfold rustReallocEvents
      split
      · simp only [AllocCostModel.stepEvents_cons, AllocCostModel.stepEvents_nil]
        obtain ⟨hc, hl, hp⟩ :=
          hM.step_realloc_small_small_any st0 (al := 1) (by decide) hold_s hnew_s
        have hsr := hM.smallRealloc_le hnew_s
        omega
      · simp only [AllocCostModel.stepEvents_cons, AllocCostModel.stepEvents_nil]
        have hal8 : max 1 8 ≤ 16 := by decide
        obtain ⟨hc1, hl1, hp1⟩ := hM.step_aligned_small_any st0 (al := max 1 8) hal8 hnew_s
        obtain ⟨hc2, hl2, hp2⟩ := hM.freeNonInc 1 x.cap.toNat (M.step (.aligned (max 1 8) newCap) st0)
        have hsa := hM.smallAlloc_le hnew_s
        omega

/-! ## 5. `Chain::clone` Pre-`message_keys` and Seed-Loop Helpers -/

/-- `PhaseCreditSpec` for `chainClonePreMkEvents gc` (`srk ≤ 33` B, `priv ≤ 32` B, `ck ≤ 32` B). -/
theorem phaseCredit_chainClonePreMk {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {gc : ChainGhost × ReceiverChain}
    (hsrk : gc.1.srk.bytes.length ≤ 33)
    (hpriv : gc.1.priv.bytes.length ≤ 32)
    (hSmall33 : 33 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (· = chainClonePreMkEvents gc) (3 * (2 * 33 + 9539)) 0 0 33 := by
  have hs1 : PhaseCreditSpec M (OptRustAllocEnv gc.1.srk.bytes.length 1) (2 * 33 + 9539) 0 0 33 := by
    by_cases h0 : gc.1.srk.bytes.length = 0
    · unfold OptRustAllocEnv
      simp only [h0, ↓reduceIte]
      exact (PhaseCreditSpec.nil M).mono (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)
    · unfold OptRustAllocEnv
      simp only [h0, ↓reduceIte]
      have hle : gc.1.srk.bytes.length ≤ HasFineReallocCredit.smallMaxReq M :=
        Nat.le_trans hsrk hSmall33
      have h := PhaseCreditSpec.rustAlloc_small_any hM (by decide : 1 ≤ 16) hle
      have ha := hM.smallAlloc_le hle
      exact h.mono (by omega) (Nat.le_refl 0) (Nat.le_refl 0) hsrk
  have hs2 : PhaseCreditSpec M (OptRustAllocEnv gc.1.priv.bytes.length 1) (2 * 33 + 9539) 0 0 33 := by
    by_cases h0 : gc.1.priv.bytes.length = 0
    · unfold OptRustAllocEnv
      simp only [h0, ↓reduceIte]
      exact (PhaseCreditSpec.nil M).mono (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)
    · unfold OptRustAllocEnv
      simp only [h0, ↓reduceIte]
      have hle33 : gc.1.priv.bytes.length ≤ 33 := Nat.le_trans hpriv (by decide)
      have hle : gc.1.priv.bytes.length ≤ HasFineReallocCredit.smallMaxReq M :=
        Nat.le_trans hle33 hSmall33
      have h := PhaseCreditSpec.rustAlloc_small_any hM (by decide : 1 ≤ 16) hle
      have ha := hM.smallAlloc_le hle
      exact h.mono (by omega) (Nat.le_refl 0) (Nat.le_refl 0) hle33
  have hs3 : PhaseCreditSpec M
      (· = match gc.2.chainKey with | none => [] | some _ => rustAllocEvents 32 1)
      (2 * 33 + 9539) 0 0 33 := by
    cases gc.2.chainKey with
    | none =>
      exact (PhaseCreditSpec.nil M).mono (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0)
        (Nat.zero_le _)
    | some _ =>
      have hle32 : 32 ≤ HasFineReallocCredit.smallMaxReq M :=
        Nat.le_trans (by decide : 32 ≤ 33) hSmall33
      have h := PhaseCreditSpec.rustAlloc_small_any hM (req := 32) (al := 1) (by decide) hle32
      have ha := hM.smallAlloc_le hle32
      exact h.mono (by omega) (Nat.le_refl 0) (Nat.le_refl 0) (by decide)
  have h123 := (hs1.concat hs2).concat hs3
  have himp : ∀ evs, evs = chainClonePreMkEvents gc →
      ConcatEnv
        (ConcatEnv (OptRustAllocEnv gc.1.srk.bytes.length 1)
          (OptRustAllocEnv gc.1.priv.bytes.length 1))
        (· = match gc.2.chainKey with | none => [] | some _ => rustAllocEvents 32 1) evs := by
    rintro _ rfl
    let e1 : List AllocEvent :=
      if gc.1.srk.bytes.length = 0 then [] else rustAllocEvents gc.1.srk.bytes.length 1
    let e2 : List AllocEvent :=
      if gc.1.priv.bytes.length = 0 then [] else rustAllocEvents gc.1.priv.bytes.length 1
    let e3 : List AllocEvent :=
      match gc.2.chainKey with | none => [] | some _ => rustAllocEvents 32 1
    refine ⟨e1 ++ e2, e3, ?_, ⟨e1, e2, rfl, ?_, ?_⟩, rfl⟩
    · simp only [chainClonePreMkEvents, e1, e2, e3, List.append_assoc]; rfl
    · by_cases h0 : gc.1.srk.bytes.length = 0 <;> simp [OptRustAllocEnv, e1, h0]
    · by_cases h0 : gc.1.priv.bytes.length = 0 <;> simp [OptRustAllocEnv, e2, h0]
  exact (h123.of_imp himp).mono (by omega) (Nat.le_refl 0) (Nat.le_refl 0) (by decide)

theorem eq_flatMap_imp_iterConcat {α : Type} (f : α → List AllocEvent) (xs : List α)
    {evs : List AllocEvent} (h : evs = xs.flatMap f) :
    IterConcatEnv (fun x e => e = f x) xs evs := by
  subst h
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    exact ⟨f x, xs.flatMap f, rfl, rfl, ih⟩

/-- `PhaseCreditSpec` for the `message_keys` seed-clone loop (`mks.length ≤ mkCap`, `seed.length ≤ seedCap ≤ smallMaxReq M`).
-/
theorem phaseCredit_mkSeedFlatMap {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {mks : List MessageKeyGenerator} {mkCap seedCap : Nat}
    (hlen : mks.length ≤ mkCap)
    (hseed : ∀ mkg ∈ mks, mkg.seed.length ≤ seedCap)
    (hSmallSeed : seedCap ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M
      (· = mks.flatMap (fun mkg => rustAllocEvents mkg.seed.length 1))
      (mkCap * (2 * seedCap + 9539)) 0 0 seedCap := by
  have hstep : ∀ mkg ∈ mks,
      PhaseCreditSpec M (fun e => e = rustAllocEvents mkg.seed.length 1)
        (2 * seedCap + 9539) 0 0 seedCap := by
    intro mkg hm
    have hs := hseed mkg hm
    have hle : mkg.seed.length ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans hs hSmallSeed
    have h := PhaseCreditSpec.rustAlloc_small_any hM (by decide : 1 ≤ 16) hle
    have ha := hM.smallAlloc_le hle
    exact h.mono (by omega) (Nat.le_refl 0) (Nat.le_refl 0) hs
  have hit := (PhaseCreditSpec.iter_zero_live mks hstep).of_imp fun _ he =>
    IterConcatEnv.toIterSeqEnv (eq_flatMap_imp_iterConcat _ mks he)
  have hmul : mks.length * (2 * seedCap + 9539) ≤ mkCap * (2 * seedCap + 9539) :=
    Nat.mul_le_mul_right _ hlen
  exact hit.mono hmul (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl _)

/-- Cancels the cloned `Chain`'s `104 * mks.length` outer `Vec<MessageKey>` buffer across `E_body` and `E_dropMk` (`Δlive = l_b`).
-/
theorem phaseCredit_chainCloneMk_body_free_cancel {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {mks : List MessageKeyGenerator} {mkCap seedCap : Nat}
    {E_body E_dropMk : List AllocEvent → Prop} {c_b l_b p_b r_b : Nat}
    (hlen : mks.length ≤ mkCap)
    (hseed : ∀ mkg ∈ mks, mkg.seed.length ≤ seedCap)
    (hSmallSeed : seedCap ≤ HasFineReallocCredit.smallMaxReq M)
    (hbody : PhaseCreditSpec M E_body c_b l_b p_b r_b)
    (hdrop : ∀ evs, E_dropMk evs →
      if mks = [] then FreeOnlyEvs evs
      else ConcatEnv FreeOnlyEvs
        (ConcatEnv (· = rustDeallocEvents (104 * mks.length) 8) FreeOnlyEvs) evs) :
    PhaseCreditSpec M
      (ConcatEnv (ConcatEnv (· = chainCloneMkEvents mks) E_body) E_dropMk)
      ((2 * (104 * mkCap) + 9539) + mkCap * (2 * seedCap + 9539) + c_b)
      l_b
      (((104 * mkCap) + 8195) + p_b)
      (max (104 * mkCap) (max seedCap r_b)) := by
  by_cases hnil : mks = []
  · subst hnil
    have hmk : PhaseCreditSpec M (· = chainCloneMkEvents []) 0 0 0 0 := by
      simpa [chainCloneMkEvents] using PhaseCreditSpec.nil M
    have h12 := hmk.concat hbody
    have h123 : PhaseCreditSpec M
        (ConcatEnv (ConcatEnv (· = chainCloneMkEvents []) E_body) FreeOnlyEvs)
        (0 + c_b) (0 + l_b) (max 0 (0 + p_b)) (max 0 r_b) :=
      phaseCredit_concat_freeOnly hM h12
    have himp : ∀ evs,
        ConcatEnv (ConcatEnv (· = chainCloneMkEvents []) E_body) E_dropMk evs →
        ConcatEnv (ConcatEnv (· = chainCloneMkEvents []) E_body) FreeOnlyEvs evs := by
      rintro _ ⟨e12, e3, rfl, h12', hd'⟩
      exact ⟨e12, e3, rfl, h12', by simpa using hdrop e3 hd'⟩
    exact (h123.of_imp himp).mono (by omega) (by omega) (by omega) (by omega)
  · have hseeds := phaseCredit_mkSeedFlatMap hM hlen hseed hSmallSeed
    have hmid := phaseCredit_concat_freeOnly hM (hseeds.concat hbody)
    have h104_le : 104 * mks.length ≤ 104 * mkCap := Nat.mul_le_mul_left 104 hlen
    have h104_ne : 104 * mks.length ≠ 0 := by
      cases mks with
      | nil => contradiction
      | cons _ _ => simp
    have hcancel := phaseCredit_optRustAllocBodyDealloc_cancel hM
      (n := 104 * mks.length) (al := 8) (cap := 104 * mkCap)
      (by decide) h104_le hmid
    have hfull := phaseCredit_concat_freeOnly hM hcancel
    have hrew : ∀ evs,
        ConcatEnv (ConcatEnv (· = chainCloneMkEvents mks) E_body) E_dropMk evs →
        ConcatEnv
          (ConcatEnv
            (ConcatEnv (OptRustAllocEnv (104 * mks.length) 8)
              (ConcatEnv
                (ConcatEnv (· = mks.flatMap (fun mkg => rustAllocEvents mkg.seed.length 1)) E_body)
                FreeOnlyEvs))
            (OptRustDeallocEnv (104 * mks.length) 8))
          FreeOnlyEvs evs := by
      rintro _ ⟨evs12, evs3, rfl, ⟨evs1, evs2, rfl, rfl, hb⟩, hd⟩
      have hd' := hdrop evs3 hd
      simp only [hnil, ↓reduceIte] at hd'
      obtain ⟨fo1, rest, rfl, hfo1, ⟨d104, fo2, rfl, hd104, hfo2⟩⟩ := hd'
      simp only [chainCloneMkEvents, hnil, ↓reduceIte]
      refine ⟨(((rustAllocEvents (104 * mks.length) 8) ++
          ((mks.flatMap (fun mkg => rustAllocEvents mkg.seed.length 1) ++ evs2) ++ fo1)) ++ d104),
        fo2, by simp [List.append_assoc], ?_, hfo2⟩
      refine ⟨_, d104, rfl, ?_, by simpa [OptRustDeallocEnv, h104_ne] using hd104⟩
      refine ⟨rustAllocEvents (104 * mks.length) 8, _, rfl,
        by simp [OptRustAllocEnv, h104_ne], ?_⟩
      exact ⟨_, fo1, rfl, ⟨_, evs2, rfl, rfl, hb⟩, hfo1⟩
    exact (hfull.of_imp hrew).mono (by omega) (by omega) (by omega) (by omega)

/-! ## 6. `try_decrypt_pq` DH Ratchet Step 1 and 2 -/

theorem phaseCredit_dhCommitStep12 {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hSmall33 : 33 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M DhCommitStep12Env (3 * (2 * 33 + 9539)) 0 0 33 := by
  have hle32 : 32 ≤ HasFineReallocCredit.smallMaxReq M :=
    Nat.le_trans (by decide : 32 ≤ 33) hSmall33
  have h33 := PhaseCreditSpec.rustAlloc_small_any hM (req := 33) (al := 1) (by decide) hSmall33
  have h33_aff := hM.smallAlloc_le hSmall33
  have h32 := PhaseCreditSpec.rustAlloc_small_any hM (req := 32) (al := 1) (by decide) hle32
  have h32_aff := hM.smallAlloc_le hle32
  have h123 := (h33.concat h33).concat h32
  have himp : ∀ evs, DhCommitStep12Env evs →
      ConcatEnv
        (ConcatEnv (· = rustAllocEvents 33 1) (· = rustAllocEvents 33 1))
        (· = rustAllocEvents 32 1) evs := by
    rintro _ rfl
    refine ⟨_, _, rfl, ⟨_, _, rfl, rfl, rfl⟩, rfl⟩
  exact (h123.of_imp himp).mono (by omega) (Nat.le_refl 0) (Nat.le_refl 0) (by decide)

end LibsignalBinary.Proofs.PeakBudget.W4InnerHelpers
