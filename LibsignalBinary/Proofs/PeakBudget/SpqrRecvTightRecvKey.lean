/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.ClientBounds
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvPeakHelpers
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightHelpers
public import LibsignalBinary.Proofs.PeakBudget.VecGrowCreditHelpers

/-!
# Amortized `<Chain>::recv_key` `KeyHistory` Reserve Credit Bound

Uses the remaining small-pool potential `remPot S cap = 4 * (S - min cap S)` to bound `KeyHistory`
`doReserveStep` cumulative small-allocation charges in `<spqr::chain::Chain>::recv_key` by
`4 * smallMaxReq M + d * 9539` across arbitrary initial ghost capacities `x.G`, yielding closed
`fineCostModel` bounds both unconditionally (`Δcum = 19,163,846`, `Δlive = 310,675`,
`Δpeak = 621,350`) and under `KeyHistorySmallOrReserved` (`Δlive = Δpeak = 0`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightRecvKey

open CryptoVerification.LibsignalSpqrV1
  (Bytes ChainEpochDirection ChainParamsPB HkdfFn KeyHistory)
open CryptoVerification.LibsignalTripleRatchet (reserveCap)
open CryptoVerification.SpqrV1.ChainProofs (ChainRecvKeyGhost)
open LibsignalBinary.Heap (AllocCostModel rustAllocEvents)
open LibsignalBinary.Heap.Fine (fineCostModel)
open LibsignalBinary.Heap.Fine.ClientBounds
  (eventStepAlign eventStepReq fineCostModel_smallMaxReq_eq smallAllocCost_le_738_of_le_44)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit
  (HasFineReallocCredit stepEvents_rustAlloc_large stepEvents_rustAlloc_small
   stepEvents_rustRealloc_large_large stepEvents_rustRealloc_small_large
   stepEvents_rustRealloc_small_small)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (ModelHyps PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas (fineCostModel_modelHyps)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvPeakHelpers
  (capLargeLive keyAddBudget nextKeyInternalReq nextKeyInternal_phaseCreditSpec recvKeyCapMax
   virtCap)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightHelpers
  (nextKeyInternal_fine_phaseCreditSpec req_align_rustAlloc_local req_align_rustRealloc_local)
open LibsignalBinary.Proofs.PeakBudget.VecGrowCreditHelpers (super_doubling_potential_step)
open LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget (nextKeyInternalEvents)
open LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyHelpersBudget
  (ChainRecvKeyEnv chainRecvKeyEvents doReserveStep keyAdvanceLoopEvents keyHistoryAddStep)

/-! ## Constant-Free Arithmetic Combinators -/

private theorem chain_add3_le {s0 s1 s2 s3 a b c bound : Nat}
    (h1 : s1 ≤ s0 + a) (h2 : s2 ≤ s1 + b) (h3 : s3 ≤ s2 + c)
    (habc : (a + b) + c ≤ bound) :
    s3 ≤ s0 + bound := by
  omega

private theorem chain_add3_pot_le {s0 s1 s2 s3 pot potCap a dCost b c bound : Nat}
    (h1 : s1 ≤ s0 + pot + a + dCost)
    (hpot : pot ≤ potCap)
    (h2 : s2 ≤ s1 + b)
    (h3 : s3 ≤ s2 + c)
    (hbound : potCap + dCost + (a + b) + c ≤ bound) :
    s3 ≤ s0 + bound := by
  omega

private theorem live_peak_3_small {l0 l1 l2 l3 p0 p1 p2 p3 : Nat}
    (hl1 : l1 ≤ l0) (hp1 : p1 ≤ max p0 l0)
    (hl2 : l2 ≤ l1 + 0) (hp2 : p2 ≤ max p1 (l1 + 0))
    (hl3 : l3 ≤ l2 + 0) (hp3 : p3 ≤ max p2 (l2 + 0)) :
    l3 ≤ l0 + 0 ∧ p3 ≤ max p0 (l0 + 0) := by
  omega

/-! ## Remaining Potential `remPot` and Step-by-Step Reserve Amortization -/

/-- Remaining small-pool byte potential `4 * (S - min cap S)` for super-doubling `Vec<u8>` growth.
-/
def remPot (S cap : Nat) : Nat :=
  4 * (S - min cap S)

theorem remPot_le (S cap : Nat) : remPot S cap ≤ 4 * S := by
  unfold remPot; omega

private theorem remPot_step {S oldReq newReq : Nat} (h2 : 2 * oldReq ≤ newReq) :
    (if newReq ≤ S then 2 * newReq else 0) + remPot S newReq ≤ remPot S oldReq := by
  have h := super_doubling_potential_step (S := S) h2
  have hm1 : min oldReq S ≤ S := Nat.min_le_right oldReq S
  have hm2 : min newReq S ≤ S := Nat.min_le_right newReq S
  unfold remPot
  split at h <;> split <;> omega

private theorem capLargeLive_le_aff_local {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {cap capMax : Nat} (hcap : cap ≤ capMax) :
    capLargeLive M cap ≤
      if HasFineReallocCredit.smallMaxReq M < capMax then capMax + 8195 else 0 := by
  unfold capLargeLive
  split
  · next hgt =>
    have hgtMax : HasFineReallocCredit.smallMaxReq M < capMax := by omega
    rw [ite_eq_left hgtMax]
    have hla := hM.largeCost_le hgt
    omega
  · split <;> omega

private theorem doReserveStep_amortized_spec
    {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M)
    {cap len additional maxLen capMax d : Nat}
    (_hadd_pos : 0 < additional)
    (hlen : len + additional ≤ maxLen)
    (hcap : cap ≤ capMax)
    (hcapMax : 2 * maxLen + 8 ≤ capMax)
    (hinv : maxLen < virtCap cap * 2 ^ d) :
    let res := doReserveStep cap len additional
    let S := HasFineReallocCredit.smallMaxReq M
    ∃ d', d' ≤ d ∧
      res.1 ≤ capMax ∧
      maxLen < virtCap res.1 * 2 ^ d' ∧
      (∀ e ∈ res.2, eventStepReq e ≤ capMax ∧ eventStepAlign e ≤ 16) ∧
      (∀ (st : M.σ) (L₀ : Nat),
        HasFineReallocCredit.liveLarge st ≤ L₀ + capLargeLive M cap →
        HasFineReallocCredit.cumSmall (M.stepEvents res.2 st) + remPot S res.1 ≤
          HasFineReallocCredit.cumSmall st + remPot S cap + (d - d') * 9539 ∧
        HasFineReallocCredit.liveLarge (M.stepEvents res.2 st) ≤
          L₀ + capLargeLive M res.1 ∧
        HasFineReallocCredit.peakLarge (M.stepEvents res.2 st) ≤
          max (HasFineReallocCredit.peakLarge st)
            (L₀ + capLargeLive M cap + capLargeLive M res.1)) := by
  dsimp only [doReserveStep]
  set S := HasFineReallocCredit.smallMaxReq M
  by_cases hfit : len + additional ≤ cap
  · rw [ite_eq_left hfit]
    dsimp only
    refine ⟨d, Nat.le_refl d, hcap, hinv, (fun _ he => nomatch he), ?_⟩
    intro st L₀ hL
    simp only [AllocCostModel.stepEvents_nil, Nat.sub_self, Nat.zero_mul, Nat.add_zero]
    exact ⟨Nat.le_refl _, hL, Nat.le_max_left _ _⟩
  · rw [ite_eq_right hfit]
    have hlt : cap < len + additional := by omega
    cases d with
    | zero =>
      exfalso
      unfold virtCap at hinv
      split at hinv <;> simp only [Nat.pow_zero, Nat.mul_one] at hinv <;> omega
    | succ d' =>
      set cap' := reserveCap cap len additional
      dsimp only
      have hcap'_ge8 : 8 ≤ cap' := by unfold cap' reserveCap; omega
      have hcap'_ge2 : 2 * cap ≤ cap' := by unfold cap' reserveCap; omega
      have hcap'_le : cap' ≤ capMax := by unfold cap' reserveCap; omega
      have hvirt : 2 * virtCap cap ≤ virtCap cap' := by
        unfold virtCap
        split
        · rw [ite_eq_right (by omega)]; omega
        · rw [ite_eq_right (by omega)]; omega
      have hinv' : maxLen < virtCap cap' * 2 ^ d' := by
        have hpow : virtCap cap * 2 ^ (d' + 1) = (2 * virtCap cap) * 2 ^ d' := by
          rw [Nat.pow_succ]; ring
        have hmul : (2 * virtCap cap) * 2 ^ d' ≤ virtCap cap' * 2 ^ d' :=
          Nat.mul_le_mul_right (2 ^ d') hvirt
        omega
      have hpot := remPot_step (S := S) hcap'_ge2
      have hsub1 : d' + 1 - d' = 1 := by omega
      refine ⟨d', Nat.le_succ d', hcap'_le, hinv', ?_, ?_⟩
      · intro e he
        by_cases hc0 : cap = 0
        · rw [ite_eq_left hc0] at he
          obtain ⟨hr, ha⟩ := req_align_rustAlloc_local (al := 1) (by decide) e he
          exact ⟨Nat.le_trans hr hcap'_le, ha⟩
        · rw [ite_eq_right hc0] at he
          obtain ⟨hr, ha⟩ := req_align_rustRealloc_local (al := 1) (by decide) (by omega) e he
          exact ⟨Nat.le_trans hr hcap'_le, ha⟩
      · intro st L₀ hL
        rw [hsub1, Nat.one_mul]
        by_cases hc0 : cap = 0
        · rw [ite_eq_left hc0]
          have hcl0 : capLargeLive M cap = 0 := by unfold capLargeLive; rw [hc0]; simp
          by_cases hsm : cap' ≤ S
          · rw [ite_eq_left hsm] at hpot
            obtain ⟨hc, hl, hp⟩ :=
              stepEvents_rustAlloc_small M (req := cap') (al := 1) st (by decide) (by omega) hsm
            have hsa := hM.smallAlloc_le hsm
            have hcl' : capLargeLive M cap' = 0 := by
              unfold capLargeLive; rw [ite_eq_right (by dsimp only [S] at hsm; omega)]
            omega
          · rw [ite_eq_right hsm] at hpot
            have hgt : HasFineReallocCredit.smallMaxReq M < cap' := by dsimp only [S] at hsm; omega
            obtain ⟨hc, hl, hp⟩ :=
              stepEvents_rustAlloc_large M (req := cap') (al := 1) st (by decide) hgt
            have hm := hM.meta_le
            have hcl' : capLargeLive M cap' = HasFineReallocCredit.largeCost M cap' := by
              unfold capLargeLive; rw [ite_eq_left hgt]
            omega
        · rw [ite_eq_right hc0]
          have hcpos : 0 < cap := by omega
          by_cases hold_sm : cap ≤ S
          · have hold_sm' : cap ≤ HasFineReallocCredit.smallMaxReq M := hold_sm
            have hcl_old : capLargeLive M cap = 0 := by
              unfold capLargeLive; rw [ite_eq_right (by omega)]
            by_cases hnew_sm : cap' ≤ S
            · rw [ite_eq_left hnew_sm] at hpot
              obtain ⟨hc, hl, hp⟩ :=
                stepEvents_rustRealloc_small_small M (old := cap) (new := cap') (al := 1) st
                  (by decide) (by omega) hcpos hold_sm' (by omega) hnew_sm
              have hsr := hM.smallRealloc_le hnew_sm
              have hcl_new : capLargeLive M cap' = 0 := by
                unfold capLargeLive; rw [ite_eq_right (by dsimp only [S] at hnew_sm; omega)]
              omega
            · rw [ite_eq_right hnew_sm] at hpot
              have hnew_gt : HasFineReallocCredit.smallMaxReq M < cap' := by
                dsimp only [S] at hnew_sm; omega
              obtain ⟨hc, hl, hp⟩ :=
                stepEvents_rustRealloc_small_large M (old := cap) (new := cap') (al := 1) st
                  (by decide) (by omega) hcpos hold_sm' hnew_gt
              have hm := hM.meta_le
              have hcl_new : capLargeLive M cap' = HasFineReallocCredit.largeCost M cap' := by
                unfold capLargeLive; rw [ite_eq_left hnew_gt]
              omega
          · have hold_gt : HasFineReallocCredit.smallMaxReq M < cap := by
              dsimp only [S] at hold_sm; omega
            have hnew_gt : HasFineReallocCredit.smallMaxReq M < cap' := by omega
            have hnew_not_sm : ¬ (cap' ≤ S) := by dsimp only [S]; omega
            rw [ite_eq_right hnew_not_sm] at hpot
            obtain ⟨hc, hl, hp⟩ :=
              stepEvents_rustRealloc_large_large M (old := cap) (new := cap') (al := 1) st
                (by decide) (by omega) hold_gt hnew_gt
            have hm := hM.meta_le
            have hcl_old : capLargeLive M cap = HasFineReallocCredit.largeCost M cap := by
              unfold capLargeLive; rw [ite_eq_left hold_gt]
            have hcl_new : capLargeLive M cap' = HasFineReallocCredit.largeCost M cap' := by
              unfold capLargeLive; rw [ite_eq_left hnew_gt]
            omega

private theorem keyHistoryAddStep_amortized_spec
    {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M)
    {cap len maxLen capMax d : Nat}
    (hlen : len + 36 ≤ maxLen)
    (hcap : cap ≤ capMax)
    (hcapMax : 2 * maxLen + 8 ≤ capMax)
    (hinv : maxLen < virtCap cap * 2 ^ d) :
    let res := keyHistoryAddStep cap len
    let S := HasFineReallocCredit.smallMaxReq M
    ∃ d2, d2 ≤ d ∧
      res.1 ≤ capMax ∧
      maxLen < virtCap res.1 * 2 ^ d2 ∧
      (∀ e ∈ res.2, eventStepReq e ≤ capMax ∧ eventStepAlign e ≤ 16) ∧
      (∀ (st : M.σ) (L₀ : Nat),
        HasFineReallocCredit.liveLarge st ≤ L₀ + capLargeLive M cap →
        HasFineReallocCredit.cumSmall (M.stepEvents res.2 st) + remPot S res.1 ≤
          HasFineReallocCredit.cumSmall st + remPot S cap + (d - d2) * 9539 ∧
        HasFineReallocCredit.liveLarge (M.stepEvents res.2 st) ≤
          L₀ + capLargeLive M res.1 ∧
        HasFineReallocCredit.peakLarge (M.stepEvents res.2 st) ≤
          max (HasFineReallocCredit.peakLarge st)
            (L₀ + 2 * (if HasFineReallocCredit.smallMaxReq M < capMax then capMax + 8195 else 0))) := by
  dsimp only [keyHistoryAddStep]
  set r1 := doReserveStep cap len 4
  set r2 := doReserveStep r1.1 (len + 4) 32
  obtain ⟨d1, hd1_le, hcap1, hinv1, hreq1, hcr1⟩ :=
    doReserveStep_amortized_spec hM (cap := cap) (len := len) (additional := 4)
      (by decide) (by omega) hcap hcapMax hinv
  obtain ⟨d2, hd2_le, hcap2, hinv2, hreq2, hcr2⟩ :=
    doReserveStep_amortized_spec hM (cap := r1.1) (len := len + 4) (additional := 32)
      (by decide) hlen hcap1 hcapMax hinv1
  refine ⟨d2, Nat.le_trans hd2_le hd1_le, hcap2, hinv2, ?_, ?_⟩
  · intro e he
    rcases List.mem_append.mp he with he1 | he2
    · exact hreq1 e he1
    · exact hreq2 e he2
  · intro st L₀ hL
    rw [M.stepEvents_append]
    obtain ⟨hc1, hl1, hp1⟩ := hcr1 st L₀ hL
    obtain ⟨hc2, hl2, hp2⟩ := hcr2 (M.stepEvents r1.2 st) L₀ hl1
    have hcl0 := capLargeLive_le_aff_local hM hcap
    have hcl1 := capLargeLive_le_aff_local hM hcap1
    have hcl2 := capLargeLive_le_aff_local hM hcap2
    have hdist : (d - d1) * 9539 + (d1 - d2) * 9539 = (d - d2) * 9539 := by
      rw [← Nat.add_mul]; congr 1; omega
    dsimp only [r1, r2] at *
    omega

private theorem nextKeyInternal_ctr_and_key_len_local
    (hkdf : HkdfFn) {next : Bytes} {ctr : BitVec 32}
    {next1 : Bytes} {ctr1 cOut : BitVec 32} {key : Bytes}
    (h : ChainEpochDirection.nextKeyInternal hkdf next ctr = .ok (next1, ctr1, (cOut, key))) :
    ctr1.toNat = ctr.toNat + 1 ∧ key.length ≤ 32 := by
  unfold ChainEpochDirection.nextKeyInternal at h
  by_cases hlen : (next.length != 32) = true
  · simp [hlen] at h
  · by_cases hmax : (ctr == 0xffffffff#32) = true
    · simp [hlen, hmax] at h
    · simp only [hlen, hmax, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq,
        Prod.mk.injEq] at h
      rcases h with ⟨_, hctr1, _, rfl⟩
      have hne : ctr.toNat ≠ 0xffffffff := by
        intro heq; apply hmax; apply beq_iff_eq.mpr; exact BitVec.eq_of_toNat_eq heq
      have hlt : ctr.toNat < 2 ^ 32 - 1 := by have := ctr.isLt; omega
      have hctr_nat : (ctr + 1#32).toNat = ctr.toNat + 1 := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      exact ⟨hctr1 ▸ hctr_nat, List.length_take_le 32 _⟩

private theorem keyAdvanceLoopEvents_amortized_spec
    {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M)
    (hSmallNki : nextKeyInternalReq ≤ HasFineReallocCredit.smallMaxReq M)
    (hkdf : HkdfFn) (params : ChainParamsPB) (atIdx : BitVec 32) :
    ∀ (rem : Nat) (ced : ChainEpochDirection) (cap maxLen capMax d : Nat),
      ced.prev.data.length + 36 * keyAddBudget atIdx.toNat params.maxOooKeysOrDefault.toNat ced.ctr.toNat ≤ maxLen →
      cap ≤ capMax →
      2 * maxLen + 8 ≤ capMax →
      maxLen < virtCap cap * 2 ^ d →
      let ev := keyAdvanceLoopEvents hkdf params atIdx rem ced cap
      let S := HasFineReallocCredit.smallMaxReq M
      (∀ e ∈ ev, eventStepReq e ≤ max nextKeyInternalReq capMax ∧ eventStepAlign e ≤ 16) ∧
      (∀ (st : M.σ) (L₀ : Nat),
        HasFineReallocCredit.liveLarge st ≤ L₀ + capLargeLive M cap →
        HasFineReallocCredit.cumSmall (M.stepEvents ev st) ≤
          HasFineReallocCredit.cumSmall st + remPot S cap +
            rem * HasFineReallocCredit.smallAllocCost M nextKeyInternalReq +
            d * 9539 ∧
        HasFineReallocCredit.liveLarge (M.stepEvents ev st) ≤
          L₀ + (if HasFineReallocCredit.smallMaxReq M < capMax then capMax + 8195 else 0) ∧
        HasFineReallocCredit.peakLarge (M.stepEvents ev st) ≤
          max (HasFineReallocCredit.peakLarge st)
            (L₀ + 2 * (if HasFineReallocCredit.smallMaxReq M < capMax then capMax + 8195 else 0))) := by
  intro rem
  induction rem with
  | zero =>
    intro ced cap maxLen capMax d _ hcap _ _
    dsimp only [keyAdvanceLoopEvents]
    refine ⟨(fun _ h => nomatch h), ?_⟩
    intro st L₀ hL
    simp only [AllocCostModel.stepEvents_nil, Nat.zero_mul, Nat.add_zero]
    have hcl := capLargeLive_le_aff_local hM hcap
    exact ⟨by omega, by omega, Nat.le_max_left _ _⟩
  | succ rem ih =>
    intro ced cap maxLen capMax d hlenB hcap hcapMax hinv
    dsimp only [keyAdvanceLoopEvents]
    have hnki := nextKeyInternal_phaseCreditSpec hSmallNki
    by_cases hlt_idx : ced.ctr.toNat + 1 < atIdx.toNat
    · rw [ite_eq_left hlt_idx]
      cases hnki_call : ChainEpochDirection.nextKeyInternal hkdf ced.next ced.ctr with
      | error _ =>
        refine ⟨(fun _ h => nomatch h), ?_⟩
        intro st L₀ hL
        simp only [AllocCostModel.stepEvents_nil]
        have hcl := capLargeLive_le_aff_local hM hcap
        exact ⟨by omega, by omega, Nat.le_max_left _ _⟩
      | ok res =>
        rcases res with ⟨next1, ctr1, cOut, key⟩
        dsimp only
        obtain ⟨hctr1_nat, hkey_len⟩ := nextKeyInternal_ctr_and_key_len_local hkdf hnki_call
        set maxOoo := params.maxOooKeysOrDefault
        by_cases hovf : ctr1.toNat + maxOoo.toNat ≥ 2 ^ 32
        · rw [ite_eq_left hovf]
          refine ⟨?_, ?_⟩
          · intro e he
            obtain ⟨hr, ha⟩ := hnki.req_align nextKeyInternalEvents rfl e he
            exact ⟨Nat.le_trans hr (Nat.le_max_left _ _), ha⟩
          · intro st L₀ hL
            obtain ⟨hc, hl, hp⟩ := hnki.credit_le st rfl
            have hcl := capLargeLive_le_aff_local hM hcap
            have h1 : (rem + 1) * HasFineReallocCredit.smallAllocCost M nextKeyInternalReq =
                HasFineReallocCredit.smallAllocCost M nextKeyInternalReq +
                  rem * HasFineReallocCredit.smallAllocCost M nextKeyInternalReq := by
              rw [Nat.succ_mul, Nat.add_comm]
            omega
        · rw [ite_eq_right hovf]
          by_cases hwin : ctr1 + maxOoo ≥ atIdx
          · rw [ite_eq_left hwin]
            have hsum_nat : (ctr1 + maxOoo).toNat = ctr1.toNat + maxOoo.toNat := by
              rw [BitVec.toNat_add]; omega
            have hge_idx : ctr1.toNat + maxOoo.toNat ≥ atIdx.toNat := by
              have : atIdx.toNat ≤ (ctr1 + maxOoo).toNat := hwin; omega
            have hbud_pos : 1 ≤ keyAddBudget atIdx.toNat maxOoo.toNat ced.ctr.toNat := by
              unfold keyAddBudget; omega
            have hbud_next : keyAddBudget atIdx.toNat maxOoo.toNat ctr1.toNat =
                keyAddBudget atIdx.toNat maxOoo.toNat ced.ctr.toNat - 1 := by
              unfold keyAddBudget; omega
            have hlen36 : ced.prev.data.length + 36 ≤ maxLen := by
              have := Nat.mul_le_mul_left 36 hbud_pos; omega
            obtain ⟨d2, hd2_le, hcap2, hinv2, hreq_add, hcr_add⟩ :=
              keyHistoryAddStep_amortized_spec hM hlen36 hcap hcapMax hinv
            set addRes := keyHistoryAddStep cap ced.prev.data.length
            set ced' : ChainEpochDirection :=
              { ctr := ctr1, next := next1, prev := ced.prev.add (ctr1, key) params }
            have hlenB' : ced'.prev.data.length +
                36 * keyAddBudget atIdx.toNat maxOoo.toNat ced'.ctr.toNat ≤ maxLen := by
              have hadd_len :=
                CryptoVerification.SpqrV1.Top.StateSize.KeyHistory.add_length_le
                  ced.prev (ctr1, key) params hkey_len
              change (ced.prev.add (ctr1, key) params).data.length +
                36 * keyAddBudget atIdx.toNat maxOoo.toNat ctr1.toNat ≤ maxLen
              rw [hbud_next]; omega
            obtain ⟨hreq_tail, hcr_tail⟩ := ih ced' addRes.1 maxLen capMax d2 hlenB' hcap2 hcapMax hinv2
            refine ⟨?_, ?_⟩
            · intro e he
              rcases List.mem_append.mp he with he12 | he3
              · rcases List.mem_append.mp he12 with he1 | he2
                · obtain ⟨hr, ha⟩ := hnki.req_align nextKeyInternalEvents rfl e he1
                  exact ⟨Nat.le_trans hr (Nat.le_max_left _ _), ha⟩
                · obtain ⟨hr, ha⟩ := hreq_add e he2
                  exact ⟨Nat.le_trans hr (Nat.le_max_right _ _), ha⟩
              · exact hreq_tail e he3
            · intro st L₀ hL
              rw [M.stepEvents_append, M.stepEvents_append]
              have hcl := capLargeLive_le_aff_local hM hcap
              obtain ⟨hc1, hl1, hp1⟩ := hnki.credit_le st rfl
              obtain ⟨hc2, hl2, hp2⟩ := hcr_add (M.stepEvents nextKeyInternalEvents st) L₀
                (by omega)
              obtain ⟨hc3, hl3, hp3⟩ := hcr_tail
                (M.stepEvents addRes.2 (M.stepEvents nextKeyInternalEvents st)) L₀ hl2
              have hmul_d : (d - d2) * 9539 + d2 * 9539 = d * 9539 := by
                rw [← Nat.add_mul]; congr 1; omega
              have hmul_r : (rem + 1) * HasFineReallocCredit.smallAllocCost M nextKeyInternalReq =
                  HasFineReallocCredit.smallAllocCost M nextKeyInternalReq +
                    rem * HasFineReallocCredit.smallAllocCost M nextKeyInternalReq := by
                rw [Nat.succ_mul, Nat.add_comm]
              omega
          · rw [ite_eq_right hwin]
            set ced' : ChainEpochDirection :=
              { ctr := ctr1, next := next1, prev := ced.prev }
            have hbud_le : keyAddBudget atIdx.toNat maxOoo.toNat ctr1.toNat ≤
                keyAddBudget atIdx.toNat maxOoo.toNat ced.ctr.toNat := by
              unfold keyAddBudget; omega
            have hlenB' : ced'.prev.data.length +
                36 * keyAddBudget atIdx.toNat maxOoo.toNat ced'.ctr.toNat ≤ maxLen := by
              have := Nat.mul_le_mul_left 36 hbud_le
              change ced.prev.data.length +
                36 * keyAddBudget atIdx.toNat maxOoo.toNat ctr1.toNat ≤ maxLen
              omega
            obtain ⟨hreq_tail, hcr_tail⟩ := ih ced' cap maxLen capMax d hlenB' hcap hcapMax hinv
            refine ⟨?_, ?_⟩
            · intro e he
              rcases List.mem_append.mp he with he1 | he2
              · obtain ⟨hr, ha⟩ := hnki.req_align nextKeyInternalEvents rfl e he1
                exact ⟨Nat.le_trans hr (Nat.le_max_left _ _), ha⟩
              · exact hreq_tail e he2
            · intro st L₀ hL
              rw [M.stepEvents_append]
              have hcl := capLargeLive_le_aff_local hM hcap
              obtain ⟨hc1, hl1, hp1⟩ := hnki.credit_le st rfl
              obtain ⟨hc2, hl2, hp2⟩ := hcr_tail (M.stepEvents nextKeyInternalEvents st) L₀
                (by omega)
              have hmul_r : (rem + 1) * HasFineReallocCredit.smallAllocCost M nextKeyInternalReq =
                  HasFineReallocCredit.smallAllocCost M nextKeyInternalReq +
                    rem * HasFineReallocCredit.smallAllocCost M nextKeyInternalReq := by
                rw [Nat.succ_mul, Nat.add_comm]
              omega
    · rw [ite_eq_right hlt_idx]
      refine ⟨(fun _ h => nomatch h), ?_⟩
      intro st L₀ hL
      simp only [AllocCostModel.stepEvents_nil]
      have hcl := capLargeLive_le_aff_local hM hcap
      exact ⟨by omega, by omega, Nat.le_max_left _ _⟩

private theorem keyHistoryAddStep_eq_self_local {cap len : Nat} (h : len + 36 ≤ cap) :
    keyHistoryAddStep cap len = (cap, []) := by
  have h1 : len + 4 ≤ cap := by omega
  have h2 : len + 4 + 32 ≤ cap := by omega
  simp only [keyHistoryAddStep, doReserveStep, h1, h2, ↓reduceIte, List.nil_append]

private theorem keyAdvanceLoopEvents_spec_ge_local
    {M : AllocCostModel} [HasFineReallocCredit M]
    (hSmallNki : nextKeyInternalReq ≤ HasFineReallocCredit.smallMaxReq M)
    (hkdf : HkdfFn) (params : ChainParamsPB) (atIdx : BitVec 32) :
    ∀ (rem : Nat) (ced : ChainEpochDirection) (cap maxLen : Nat),
      ced.prev.data.length + 36 * keyAddBudget atIdx.toNat params.maxOooKeysOrDefault.toNat ced.ctr.toNat ≤ maxLen →
      maxLen ≤ cap →
      let ev := keyAdvanceLoopEvents hkdf params atIdx rem ced cap
      (∀ e ∈ ev, eventStepReq e ≤ nextKeyInternalReq ∧ eventStepAlign e ≤ 16) ∧
      (∀ (st : M.σ),
        HasFineReallocCredit.cumSmall (M.stepEvents ev st) ≤
          HasFineReallocCredit.cumSmall st +
            rem * HasFineReallocCredit.smallAllocCost M nextKeyInternalReq ∧
        HasFineReallocCredit.liveLarge (M.stepEvents ev st) ≤
          HasFineReallocCredit.liveLarge st ∧
        HasFineReallocCredit.peakLarge (M.stepEvents ev st) ≤
          max (HasFineReallocCredit.peakLarge st) (HasFineReallocCredit.liveLarge st)) := by
  intro rem
  induction rem with
  | zero =>
    intro ced cap maxLen _ _
    dsimp only [keyAdvanceLoopEvents]
    exact ⟨(fun _ h => nomatch h), fun st => ⟨by simp, le_rfl, Nat.le_max_left _ _⟩⟩
  | succ rem ih =>
    intro ced cap maxLen hlenB hcap_ge
    dsimp only [keyAdvanceLoopEvents]
    have hnki := nextKeyInternal_phaseCreditSpec hSmallNki
    by_cases hlt_idx : ced.ctr.toNat + 1 < atIdx.toNat
    · rw [ite_eq_left hlt_idx]
      cases hnki_call : ChainEpochDirection.nextKeyInternal hkdf ced.next ced.ctr with
      | error _ =>
        exact ⟨(fun _ h => nomatch h), fun st => ⟨by simp, le_rfl, Nat.le_max_left _ _⟩⟩
      | ok res =>
        rcases res with ⟨next1, ctr1, cOut, key⟩
        dsimp only
        obtain ⟨hctr1_nat, hkey_len⟩ := nextKeyInternal_ctr_and_key_len_local hkdf hnki_call
        set maxOoo := params.maxOooKeysOrDefault
        by_cases hovf : ctr1.toNat + maxOoo.toNat ≥ 2 ^ 32
        · rw [ite_eq_left hovf]
          refine ⟨fun e he => hnki.req_align nextKeyInternalEvents rfl e he, fun st => ?_⟩
          obtain ⟨hc, hl, hp⟩ := hnki.credit_le st rfl
          have h1 : (rem + 1) * HasFineReallocCredit.smallAllocCost M nextKeyInternalReq =
              HasFineReallocCredit.smallAllocCost M nextKeyInternalReq +
                rem * HasFineReallocCredit.smallAllocCost M nextKeyInternalReq := by
            rw [Nat.succ_mul, Nat.add_comm]
          omega
        · rw [ite_eq_right hovf]
          by_cases hwin : ctr1 + maxOoo ≥ atIdx
          · rw [ite_eq_left hwin]
            have hsum_nat : (ctr1 + maxOoo).toNat = ctr1.toNat + maxOoo.toNat := by
              rw [BitVec.toNat_add]; omega
            have hge_idx : ctr1.toNat + maxOoo.toNat ≥ atIdx.toNat := by
              have : atIdx.toNat ≤ (ctr1 + maxOoo).toNat := hwin; omega
            have hbud_pos : 1 ≤ keyAddBudget atIdx.toNat maxOoo.toNat ced.ctr.toNat := by
              unfold keyAddBudget; omega
            have hbud_next : keyAddBudget atIdx.toNat maxOoo.toNat ctr1.toNat =
                keyAddBudget atIdx.toNat maxOoo.toNat ced.ctr.toNat - 1 := by
              unfold keyAddBudget; omega
            have hlen36 : ced.prev.data.length + 36 ≤ maxLen := by
              have := Nat.mul_le_mul_left 36 hbud_pos; omega
            rw [keyHistoryAddStep_eq_self_local (le_trans hlen36 hcap_ge)]
            dsimp only
            rw [List.append_nil]
            set ced' : ChainEpochDirection :=
              { ctr := ctr1, next := next1, prev := ced.prev.add (ctr1, key) params }
            have hlenB' : ced'.prev.data.length +
                36 * keyAddBudget atIdx.toNat maxOoo.toNat ced'.ctr.toNat ≤ maxLen := by
              have hadd_len :=
                CryptoVerification.SpqrV1.Top.StateSize.KeyHistory.add_length_le
                  ced.prev (ctr1, key) params hkey_len
              have hmul :
                  36 * (keyAddBudget atIdx.toNat maxOoo.toNat ced.ctr.toNat - 1) + 36 =
                  36 * keyAddBudget atIdx.toNat maxOoo.toNat ced.ctr.toNat := by
                have := Nat.mul_sub_left_distrib 36
                  (keyAddBudget atIdx.toNat maxOoo.toNat ced.ctr.toNat) 1
                omega
              change (ced.prev.add (ctr1, key) params).data.length +
                36 * keyAddBudget atIdx.toNat maxOoo.toNat ctr1.toNat ≤ maxLen
              rw [hbud_next]; omega
            obtain ⟨hreq_tail, hcr_tail⟩ := ih ced' cap maxLen hlenB' hcap_ge
            refine ⟨?_, ?_⟩
            · intro e he
              rcases List.mem_append.mp he with he1 | he2
              · exact hnki.req_align nextKeyInternalEvents rfl e he1
              · exact hreq_tail e he2
            · intro st
              rw [M.stepEvents_append]
              obtain ⟨hc1, hl1, hp1⟩ := hnki.credit_le st rfl
              obtain ⟨hc2, hl2, hp2⟩ := hcr_tail (M.stepEvents nextKeyInternalEvents st)
              have h1 : (rem + 1) * HasFineReallocCredit.smallAllocCost M nextKeyInternalReq =
                  HasFineReallocCredit.smallAllocCost M nextKeyInternalReq +
                    rem * HasFineReallocCredit.smallAllocCost M nextKeyInternalReq := by
                rw [Nat.succ_mul, Nat.add_comm]
              omega
          · rw [ite_eq_right hwin]
            have hbud_le : keyAddBudget atIdx.toNat maxOoo.toNat ctr1.toNat ≤
                keyAddBudget atIdx.toNat maxOoo.toNat ced.ctr.toNat := by
              unfold keyAddBudget; omega
            set ced' : ChainEpochDirection :=
              { ctr := ctr1, next := next1, prev := ced.prev }
            have hlenB' : ced'.prev.data.length +
                36 * keyAddBudget atIdx.toNat maxOoo.toNat ced'.ctr.toNat ≤ maxLen := by
              have := Nat.mul_le_mul_left 36 hbud_le
              change ced.prev.data.length +
                36 * keyAddBudget atIdx.toNat maxOoo.toNat ctr1.toNat ≤ maxLen
              omega
            obtain ⟨hreq_tail, hcr_tail⟩ := ih ced' cap maxLen hlenB' hcap_ge
            refine ⟨?_, ?_⟩
            · intro e he
              rcases List.mem_append.mp he with he1 | he2
              · obtain ⟨hr, ha⟩ := hnki.req_align nextKeyInternalEvents rfl e he1
                exact ⟨hr, ha⟩
              · exact hreq_tail e he2
            · intro st
              rw [M.stepEvents_append]
              obtain ⟨hc1, hl1, hp1⟩ := hnki.credit_le st rfl
              obtain ⟨hc2, hl2, hp2⟩ := hcr_tail (M.stepEvents nextKeyInternalEvents st)
              have h1 : (rem + 1) * HasFineReallocCredit.smallAllocCost M nextKeyInternalReq =
                  HasFineReallocCredit.smallAllocCost M nextKeyInternalReq +
                    rem * HasFineReallocCredit.smallAllocCost M nextKeyInternalReq := by
                rw [Nat.succ_mul, Nat.add_comm]
              omega
    · rw [ite_eq_right hlt_idx]
      exact ⟨(fun _ h => nomatch h), fun st => ⟨by simp, le_rfl, Nat.le_max_left _ _⟩⟩

/-! ## Amortized and `fineCostModel` `<Chain>::recv_key` Credit Specs -/

/-- Amortized `PhaseCreditSpec` for `<spqr::chain::Chain>::recv_key` independent of `x.G.epochs`,
bounding `KeyHistory` reserve small charges by `4 * smallMaxReq M + d * 9539`. -/
theorem chainRecvKey_amortized_phaseCreditSpec
    {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M)
    (hSmall : max 32 nextKeyInternalReq ≤ HasFineReallocCredit.smallMaxReq M)
    (hkdf : HkdfFn) (x : ChainRecvKeyGhost)
    {maxJumpCap maxOooCap initLenBound d : Nat}
    (hJump : x.self.params.maxJumpOrDefault.toNat ≤ maxJumpCap)
    (hOoo : x.self.params.maxOooKeysOrDefault.toNat ≤ maxOooCap)
    (hPrevLen : ∀ link ∈ x.self.links, link.recv.prev.data.length ≤ initLenBound)
    (hd : initLenBound + 36 * maxOooCap < 2 ^ d) :
    let capMax := recvKeyCapMax initLenBound maxOooCap
    let largeB := if HasFineReallocCredit.smallMaxReq M < capMax then capMax + 8195 else 0
    let cumB :=
      (maxJumpCap + 1) * HasFineReallocCredit.smallAllocCost M nextKeyInternalReq +
        HasFineReallocCredit.smallAllocCost M 32 +
        (4 * HasFineReallocCredit.smallMaxReq M + d * 9539)
    let reqB := max (max 32 nextKeyInternalReq) capMax
    PhaseCreditSpec M (ChainRecvKeyEnv hkdf x) cumB largeB (2 * largeB) reqB := by
  intro capMax largeB cumB reqB
  have h32 : 32 ≤ HasFineReallocCredit.smallMaxReq M := le_trans (Nat.le_max_left _ _) hSmall
  have hNki : nextKeyInternalReq ≤ HasFineReallocCredit.smallMaxReq M :=
    le_trans (Nat.le_max_right _ _) hSmall
  have ha32 := PhaseCreditSpec.rustAlloc_small M (req := 32) (al := 1) (by decide) (by decide) h32
  have hnki := nextKeyInternal_phaseCreditSpec hNki
  have hnil : PhaseCreditSpec M (· = []) cumB largeB (2 * largeB) reqB :=
    (PhaseCreditSpec.nil M).mono
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  unfold ChainRecvKeyEnv chainRecvKeyEvents
  split
  · exact hnil
  · cases heidx : x.self.epochIdx x.epoch with
    | error _ => exact hnil
    | ok epochIndex =>
      dsimp only
      split
      · next hlt_links =>
        set link := x.self.links[epochIndex]'hlt_links
        set gCap := if hg : epochIndex < x.G.epochs.length then
            (x.G.epochs[epochIndex]'hg).recv.prev.cap.toNat else 0
        split
        · cases link.recv.prev.get x.index link.recv.ctr x.self.params with
          | error _ => exact hnil
          | ok _ =>
            refine ha32.mono ?_ (Nat.zero_le _) (Nat.zero_le _) ?_
            · dsimp only [cumB]
              exact Nat.le_trans (Nat.le_add_left _ _) (Nat.le_add_right _ _)
            · exact le_trans (Nat.le_max_left 32 nextKeyInternalReq) (Nat.le_max_left _ capMax)
        · next hnot_lt =>
          split
          · exact hnil
          · split
            · exact hnil
            · next hjump_le =>
              split
              · exact hnil
              · set maxOoo := x.self.params.maxOooKeysOrDefault
                set self0 : ChainEpochDirection := if x.index > link.recv.ctr + maxOoo then
                    { link.recv with prev := link.recv.prev.clear } else link.recv
                set rem := x.index.toNat - self0.ctr.toNat
                have hctr_le : link.recv.ctr.toNat ≤ x.index.toNat := by
                  have : ¬ (x.index.toNat < link.recv.ctr.toNat) := hnot_lt; omega
                have hsub_nat : (x.index - link.recv.ctr).toNat =
                    x.index.toNat - link.recv.ctr.toNat := BitVec.toNat_sub_of_le hctr_le
                have hself0_ctr : self0.ctr = link.recv.ctr := by dsimp only [self0]; split <;> rfl
                have hrem_le : rem ≤ maxJumpCap := by
                  have hj : (x.index - link.recv.ctr).toNat ≤ x.self.params.maxJumpOrDefault.toNat :=
                    Nat.not_lt.mp hjump_le
                  dsimp only [rem]; rw [hself0_ctr]; omega
                have hlink_mem : link ∈ x.self.links := List.getElem_mem hlt_links
                have hself0_len : self0.prev.data.length ≤ initLenBound := by
                  dsimp only [self0]; split
                  · simp [KeyHistory.clear]
                  · exact hPrevLen link hlink_mem
                set maxLen := initLenBound + 36 * maxOooCap
                have hbud_le : keyAddBudget x.index.toNat maxOoo.toNat self0.ctr.toNat ≤ maxOooCap :=
                  le_trans (Nat.min_le_right _ _) hOoo
                have hlenB0 : self0.prev.data.length +
                    36 * keyAddBudget x.index.toNat maxOoo.toNat self0.ctr.toNat ≤ maxLen := by
                  have hmul := Nat.mul_le_mul_left 36 hbud_le; omega
                have hmul_rem :
                    rem * HasFineReallocCredit.smallAllocCost M nextKeyInternalReq +
                      HasFineReallocCredit.smallAllocCost M nextKeyInternalReq ≤
                    (maxJumpCap + 1) * HasFineReallocCredit.smallAllocCost M nextKeyInternalReq := by
                  have h2 := Nat.mul_le_mul_right
                    (HasFineReallocCredit.smallAllocCost M nextKeyInternalReq)
                    (by omega : rem + 1 ≤ maxJumpCap + 1)
                  rwa [Nat.succ_mul] at h2
                by_cases hg_le : gCap ≤ maxLen
                · have hcapMax_ge : 2 * maxLen + 8 ≤ capMax := le_rfl
                  have hgCap_max : gCap ≤ capMax := by dsimp only [capMax, recvKeyCapMax]; omega
                  have hvirt_pos : 1 ≤ virtCap gCap := by unfold virtCap; split <;> omega
                  have hinv0 : maxLen < virtCap gCap * 2 ^ d := by
                    have h1 : 1 * 2 ^ d ≤ virtCap gCap * 2 ^ d :=
                      Nat.mul_le_mul_right (2 ^ d) hvirt_pos
                    omega
                  obtain ⟨hreq_loop, hcr_loop⟩ :=
                    keyAdvanceLoopEvents_amortized_spec hM hNki hkdf x.self.params x.index
                      rem self0 gCap maxLen capMax d hlenB0 hgCap_max hcapMax_ge hinv0
                  refine
                    { req_align := ?_
                      credit_le := ?_ }
                  · rintro _ rfl e he
                    rcases List.mem_append.mp he with he12 | he3
                    · rcases List.mem_append.mp he12 with he1 | he2
                      · obtain ⟨hr, ha⟩ := hreq_loop e he1
                        exact ⟨le_trans hr (by dsimp only [reqB]; omega), ha⟩
                      · obtain ⟨hr, ha⟩ := hnki.req_align nextKeyInternalEvents rfl e he2
                        exact ⟨le_trans hr (by dsimp only [reqB]; omega), ha⟩
                    · obtain ⟨hr, ha⟩ := ha32.req_align (rustAllocEvents 32 1) rfl e he3
                      exact ⟨le_trans hr (by dsimp only [reqB]; omega), ha⟩
                  · rintro st0 _ rfl
                    rw [M.stepEvents_append, M.stepEvents_append]
                    set evLoop := keyAdvanceLoopEvents hkdf x.self.params x.index rem self0 gCap
                    have hpot_le := remPot_le (HasFineReallocCredit.smallMaxReq M) gCap
                    obtain ⟨hc1, hl1, hp1⟩ :=
                      hcr_loop st0 (HasFineReallocCredit.liveLarge st0) (by omega)
                    obtain ⟨hc2, hl2, hp2⟩ :=
                      hnki.credit_le (M.stepEvents evLoop st0) rfl
                    obtain ⟨hc3, hl3, hp3⟩ :=
                      ha32.credit_le (M.stepEvents nextKeyInternalEvents (M.stepEvents evLoop st0)) rfl
                    dsimp only [cumB, largeB]
                    omega
                · have hg_ge : maxLen ≤ gCap := by omega
                  obtain ⟨hreq_loop, hcr_loop⟩ :=
                    keyAdvanceLoopEvents_spec_ge_local hNki hkdf x.self.params x.index
                      rem self0 gCap maxLen hlenB0 hg_ge
                  refine
                    { req_align := ?_
                      credit_le := ?_ }
                  · rintro _ rfl e he
                    rcases List.mem_append.mp he with he12 | he3
                    · rcases List.mem_append.mp he12 with he1 | he2
                      · obtain ⟨hr, ha⟩ := hreq_loop e he1
                        exact ⟨le_trans hr (by dsimp only [reqB]; omega), ha⟩
                      · obtain ⟨hr, ha⟩ := hnki.req_align nextKeyInternalEvents rfl e he2
                        exact ⟨le_trans hr (by dsimp only [reqB]; omega), ha⟩
                    · obtain ⟨hr, ha⟩ := ha32.req_align (rustAllocEvents 32 1) rfl e he3
                      exact ⟨le_trans hr (by dsimp only [reqB]; omega), ha⟩
                  · rintro st0 _ rfl
                    rw [M.stepEvents_append, M.stepEvents_append]
                    set evLoop := keyAdvanceLoopEvents hkdf x.self.params x.index rem self0 gCap
                    obtain ⟨hc1, hl1, hp1⟩ := hcr_loop st0
                    obtain ⟨hc2, hl2, hp2⟩ :=
                      hnki.credit_le (M.stepEvents evLoop st0) rfl
                    obtain ⟨hc3, hl3, hp3⟩ :=
                      ha32.credit_le (M.stepEvents nextKeyInternalEvents (M.stepEvents evLoop st0)) rfl
                    dsimp only [cumB, largeB]
                    omega
      · exact hnil

/-- Closed `fineCostModel` `PhaseCreditSpec` for `<spqr::chain::Chain>::recv_key` when `maxJump ≤ 25,000`,
`maxOoo ≤ 2,000`, and initial `prev.data.length ≤ 79,236` (`Δcum = 19,163,846`, `Δlive = 310,675`,
`Δpeak = 621,350`, `maxReq = 302,480`). -/
theorem chainRecvKey_fine_phaseCreditSpec_tight
    (hkdf : HkdfFn) (x : ChainRecvKeyGhost)
    (hJump : x.self.params.maxJumpOrDefault.toNat ≤ 25000)
    (hOoo : x.self.params.maxOooKeysOrDefault.toNat ≤ 2000)
    (hPrevLen : ∀ link ∈ x.self.links, link.recv.prev.data.length ≤ 79236) :
    PhaseCreditSpec fineCostModel (ChainRecvKeyEnv hkdf x)
      19163846 310675 621350 302480 := by
  have hSmall : max 32 nextKeyInternalReq ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have hd : 79236 + 36 * 2000 < 2 ^ 18 := by decide
  have hamort := chainRecvKey_amortized_phaseCreditSpec fineCostModel_modelHyps hSmall
    hkdf x hJump hOoo hPrevLen hd
  have hnki738 := smallAllocCost_le_738_of_le_44 (req := nextKeyInternalReq) (by decide)
  have h32_738 := smallAllocCost_le_738_of_le_44 (req := 32) (by decide)
  have hsm_eq := fineCostModel_smallMaxReq_eq
  have hcap_eq : recvKeyCapMax 79236 2000 = 302480 := rfl
  have hreq_le : max 32 nextKeyInternalReq ≤ 302480 := by decide
  refine hamort.mono ?_ ?_ ?_ ?_
  · rw [hsm_eq]
    exact Nat.le_trans
      (Nat.add_le_add
        (Nat.add_le_add (Nat.mul_le_mul_left 25001 hnki738) h32_738)
        (Nat.le_refl _))
      (by decide)
  · rw [hsm_eq, hcap_eq]; decide
  · rw [hsm_eq, hcap_eq]; decide
  · rw [hcap_eq]; exact Nat.max_le.mpr ⟨hreq_le, Nat.le_refl _⟩

/-- Predicate ensuring `KeyHistory` in `<Chain>::recv_key` never allocates above
`smallMaxReq fineCostModel = 135,167` bytes (either `gCap` already covers the post-step length or
`self0.prev` plus window growth is at most `67,579` bytes). -/
def KeyHistorySmallOrReserved (x : ChainRecvKeyGhost) : Prop :=
  ∀ (epochIndex : Nat) (hlt : epochIndex < x.self.links.length),
    let link := x.self.links[epochIndex]'hlt
    let gCap := if hg : epochIndex < x.G.epochs.length then
        (x.G.epochs[epochIndex]'hg).recv.prev.cap.toNat else 0
    let maxOoo := x.self.params.maxOooKeysOrDefault
    let initLen := if x.index > link.recv.ctr + maxOoo then 0 else link.recv.prev.data.length
    let needed := initLen + 36 * keyAddBudget x.index.toNat maxOoo.toNat link.recv.ctr.toNat
    needed ≤ gCap ∨ needed ≤ 67579

/-- Under `KeyHistorySmallOrReserved x`, `<Chain>::recv_key` stays in small classes (`Δcum = 19,154,307`, `Δlive = Δpeak = 0`, `maxReq = 135,166`).
-/
theorem chainRecvKey_fine_phaseCreditSpec_tight_smallHist
    (hkdf : HkdfFn) (x : ChainRecvKeyGhost)
    (hJump : x.self.params.maxJumpOrDefault.toNat ≤ 25000)
    (hHist : KeyHistorySmallOrReserved x) :
    PhaseCreditSpec fineCostModel (ChainRecvKeyEnv hkdf x)
      19154307 0 0 135166 := by
  have h32 : 32 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have hNki : nextKeyInternalReq ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have ha32 := PhaseCreditSpec.rustAlloc_small fineCostModel (req := 32) (al := 1)
    (by decide) (by decide) h32
  have hnki := nextKeyInternal_fine_phaseCreditSpec
  have h32_738 := smallAllocCost_le_738_of_le_44 (req := 32) (by decide)
  have hnki_738 := smallAllocCost_le_738_of_le_44 (req := nextKeyInternalReq) (by decide)
  have hnil : PhaseCreditSpec fineCostModel (· = []) 19154307 0 0 135166 :=
    (PhaseCreditSpec.nil fineCostModel).mono
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  unfold ChainRecvKeyEnv chainRecvKeyEvents
  split
  · exact hnil
  · cases heidx : x.self.epochIdx x.epoch with
    | error _ => exact hnil
    | ok epochIndex =>
      dsimp only
      split
      · next hlt_links =>
        set link := x.self.links[epochIndex]'hlt_links
        set gCap := if hg : epochIndex < x.G.epochs.length then
            (x.G.epochs[epochIndex]'hg).recv.prev.cap.toNat else 0
        split
        · cases link.recv.prev.get x.index link.recv.ctr x.self.params with
          | error _ => exact hnil
          | ok _ =>
            exact ha32.mono
              (Nat.le_trans h32_738 (by decide : 738 ≤ 19154307))
              (Nat.le_refl 0) (Nat.le_refl 0) (by decide)
        · next hnot_lt =>
          split
          · exact hnil
          · split
            · exact hnil
            · next hjump_le =>
              split
              · exact hnil
              · set maxOoo := x.self.params.maxOooKeysOrDefault
                set self0 : ChainEpochDirection := if x.index > link.recv.ctr + maxOoo then
                    { link.recv with prev := link.recv.prev.clear } else link.recv
                set rem := x.index.toNat - self0.ctr.toNat
                have hctr_le : link.recv.ctr.toNat ≤ x.index.toNat := by
                  have : ¬ (x.index.toNat < link.recv.ctr.toNat) := hnot_lt; omega
                have hsub_nat : (x.index - link.recv.ctr).toNat =
                    x.index.toNat - link.recv.ctr.toNat := BitVec.toNat_sub_of_le hctr_le
                have hself0_ctr : self0.ctr = link.recv.ctr := by dsimp only [self0]; split <;> rfl
                have hrem_le : rem ≤ 25000 := by
                  have hj : (x.index - link.recv.ctr).toNat ≤ x.self.params.maxJumpOrDefault.toNat :=
                    Nat.not_lt.mp hjump_le
                  dsimp only [rem]; rw [hself0_ctr]; omega
                have hinit_eq : self0.prev.data.length =
                    (if x.index > link.recv.ctr + maxOoo then 0 else link.recv.prev.data.length) := by
                  dsimp only [self0]; split
                  · simp [KeyHistory.clear]
                  · rfl
                set needed := self0.prev.data.length +
                    36 * keyAddBudget x.index.toNat maxOoo.toNat self0.ctr.toNat
                have hHist_ep := hHist epochIndex hlt_links
                dsimp only at hHist_ep
                rw [← hinit_eq, ← hself0_ctr] at hHist_ep
                have hmul_rem :
                    rem * HasFineReallocCredit.smallAllocCost fineCostModel nextKeyInternalReq + 738 ≤
                      25001 * 738 := by
                  have h1 : rem * HasFineReallocCredit.smallAllocCost fineCostModel nextKeyInternalReq ≤
                      rem * 738 := Nat.mul_le_mul_left rem hnki_738
                  have h2 : rem * 738 + 738 ≤ 25001 * 738 := by
                    have h := Nat.mul_le_mul_right 738 (Nat.succ_le_succ hrem_le)
                    rwa [Nat.succ_mul] at h
                  exact Nat.le_trans (Nat.add_le_add_right h1 738) h2
                have hcum_small_bound :
                    (rem * HasFineReallocCredit.smallAllocCost fineCostModel nextKeyInternalReq + 738) +
                      HasFineReallocCredit.smallAllocCost fineCostModel 32 ≤ 19154307 :=
                  Nat.le_trans (Nat.add_le_add hmul_rem h32_738) (by decide)
                rcases hHist_ep with hres_ge | hsmall_need
                · obtain ⟨hreq_loop, hcr_loop⟩ :=
                    keyAdvanceLoopEvents_spec_ge_local hNki hkdf x.self.params x.index
                      rem self0 gCap needed (Nat.le_refl _) hres_ge
                  refine
                    { req_align := ?_
                      credit_le := ?_ }
                  · rintro _ rfl e he
                    have hnki_le : nextKeyInternalReq ≤ 135166 := by decide
                    rcases List.mem_append.mp he with he12 | he3
                    · rcases List.mem_append.mp he12 with he1 | he2
                      · obtain ⟨hr, ha⟩ := hreq_loop e he1
                        exact ⟨le_trans hr hnki_le, ha⟩
                      · obtain ⟨hr, ha⟩ := hnki.req_align nextKeyInternalEvents rfl e he2
                        exact ⟨le_trans hr hnki_le, ha⟩
                    · obtain ⟨hr, ha⟩ := ha32.req_align (rustAllocEvents 32 1) rfl e he3
                      exact ⟨le_trans hr (by decide), ha⟩
                  · rintro st0 _ rfl
                    rw [fineCostModel.stepEvents_append, fineCostModel.stepEvents_append]
                    set evLoop := keyAdvanceLoopEvents hkdf x.self.params x.index rem self0 gCap
                    obtain ⟨hc1, hl1, hp1⟩ := hcr_loop st0
                    obtain ⟨hc2, hl2, hp2⟩ := hnki.credit_le (fineCostModel.stepEvents evLoop st0) rfl
                    obtain ⟨hc3, hl3, hp3⟩ := ha32.credit_le
                      (fineCostModel.stepEvents nextKeyInternalEvents
                        (fineCostModel.stepEvents evLoop st0)) rfl
                    obtain ⟨hl_out, hp_out⟩ := live_peak_3_small hl1 hp1 hl2 hp2 hl3 hp3
                    exact ⟨chain_add3_le hc1 hc2 hc3 hcum_small_bound, hl_out, hp_out⟩
                · by_cases hg_le : gCap ≤ 67579
                  · have hvirt_pos : 1 ≤ virtCap gCap := by unfold virtCap; split <;> omega
                    have hinv0 : (67579 : Nat) < virtCap gCap * 2 ^ 17 := by
                      have h1 : 1 * 2 ^ 17 ≤ virtCap gCap * 2 ^ 17 :=
                        Nat.mul_le_mul_right (2 ^ 17) hvirt_pos
                      omega
                    obtain ⟨hreq_loop, hcr_loop⟩ :=
                      keyAdvanceLoopEvents_amortized_spec fineCostModel_modelHyps hNki
                        hkdf x.self.params x.index rem self0 gCap 67579 135166 17
                        hsmall_need (by omega) (by decide) hinv0
                    refine
                      { req_align := ?_
                        credit_le := ?_ }
                    · rintro _ rfl e he
                      have hmax_le : max nextKeyInternalReq 135166 ≤ 135166 := by decide
                      rcases List.mem_append.mp he with he12 | he3
                      · rcases List.mem_append.mp he12 with he1 | he2
                        · obtain ⟨hr, ha⟩ := hreq_loop e he1
                          exact ⟨le_trans hr hmax_le, ha⟩
                        · obtain ⟨hr, ha⟩ := hnki.req_align nextKeyInternalEvents rfl e he2
                          exact ⟨le_trans hr (by decide), ha⟩
                      · obtain ⟨hr, ha⟩ := ha32.req_align (rustAllocEvents 32 1) rfl e he3
                        exact ⟨le_trans hr (by decide), ha⟩
                    · rintro st0 _ rfl
                      rw [fineCostModel.stepEvents_append, fineCostModel.stepEvents_append]
                      set evLoop := keyAdvanceLoopEvents hkdf x.self.params x.index rem self0 gCap
                      have hpot_le := remPot_le (HasFineReallocCredit.smallMaxReq fineCostModel) gCap
                      rw [fineCostModel_smallMaxReq_eq] at hpot_le
                      obtain ⟨hc1, hl1, hp1⟩ :=
                        hcr_loop st0 (HasFineReallocCredit.liveLarge st0) (by omega)
                      rw [fineCostModel_smallMaxReq_eq] at hc1 hl1 hp1
                      simp only [show ¬ (135167 < 135166) by decide, ↓reduceIte, Nat.mul_zero,
                        Nat.add_zero] at hl1 hp1
                      obtain ⟨hc2, hl2, hp2⟩ := hnki.credit_le (fineCostModel.stepEvents evLoop st0) rfl
                      obtain ⟨hc3, hl3, hp3⟩ := ha32.credit_le
                        (fineCostModel.stepEvents nextKeyInternalEvents
                          (fineCostModel.stepEvents evLoop st0)) rfl
                      have hpot_bound :
                          4 * 135167 + 17 * 9539 +
                            (rem * HasFineReallocCredit.smallAllocCost fineCostModel nextKeyInternalReq +
                              738) +
                            HasFineReallocCredit.smallAllocCost fineCostModel 32 ≤ 19154307 :=
                        Nat.le_trans
                          (Nat.add_le_add (Nat.add_le_add_left hmul_rem (4 * 135167 + 17 * 9539)) h32_738)
                          (by decide)
                      obtain ⟨hl_out, hp_out⟩ := live_peak_3_small hl1 hp1 hl2 hp2 hl3 hp3
                      exact ⟨chain_add3_pot_le hc1 hpot_le hc2 hc3 hpot_bound, hl_out, hp_out⟩
                  · have hg_ge : needed ≤ gCap := Nat.le_trans hsmall_need (by omega)
                    obtain ⟨hreq_loop, hcr_loop⟩ :=
                      keyAdvanceLoopEvents_spec_ge_local hNki hkdf x.self.params x.index
                        rem self0 gCap needed (Nat.le_refl _) hg_ge
                    refine
                      { req_align := ?_
                        credit_le := ?_ }
                    · rintro _ rfl e he
                      have hnki_le : nextKeyInternalReq ≤ 135166 := by decide
                      rcases List.mem_append.mp he with he12 | he3
                      · rcases List.mem_append.mp he12 with he1 | he2
                        · obtain ⟨hr, ha⟩ := hreq_loop e he1
                          exact ⟨le_trans hr hnki_le, ha⟩
                        · obtain ⟨hr, ha⟩ := hnki.req_align nextKeyInternalEvents rfl e he2
                          exact ⟨le_trans hr hnki_le, ha⟩
                      · obtain ⟨hr, ha⟩ := ha32.req_align (rustAllocEvents 32 1) rfl e he3
                        exact ⟨le_trans hr (by decide), ha⟩
                    · rintro st0 _ rfl
                      rw [fineCostModel.stepEvents_append, fineCostModel.stepEvents_append]
                      set evLoop := keyAdvanceLoopEvents hkdf x.self.params x.index rem self0 gCap
                      obtain ⟨hc1, hl1, hp1⟩ := hcr_loop st0
                      obtain ⟨hc2, hl2, hp2⟩ := hnki.credit_le (fineCostModel.stepEvents evLoop st0) rfl
                      obtain ⟨hc3, hl3, hp3⟩ := ha32.credit_le
                        (fineCostModel.stepEvents nextKeyInternalEvents
                          (fineCostModel.stepEvents evLoop st0)) rfl
                      obtain ⟨hl_out, hp_out⟩ := live_peak_3_small hl1 hp1 hl2 hp2 hl3 hp3
                      exact ⟨chain_add3_le hc1 hc2 hc3 hcum_small_bound, hl_out, hp_out⟩
      · exact hnil

end LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightRecvKey
