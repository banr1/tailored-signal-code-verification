/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Chain.AddEpochHelpersBudget
public import LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyHelpersBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.StateSizeStep

/-!
# SPQR `spqr::recv` Runtime Chain Credit and Raw-Size Helpers

Exact-call-order `PhaseCreditSpec` bounds for the SPQR V1 runtime `Chain` operations invoked inside
`spqr::recv` (`next_key_internal`, `Chain::new`, `VecDeque::grow`, `Chain::add_epoch`, and
`Chain::recv_key`), together with `maxOooCap`-parameterized `rawChain` growth bounds.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.SpqrRecvPeakHelpers

open CryptoVerification.LibsignalSpqrV1
  (Bytes Chain ChainEpochDirection ChainParamsPB Epoch Error HkdfFn KeyHistory chainNextInfo)
open CryptoVerification.LibsignalTripleRatchet (reserveCap)
open CryptoVerification.SpqrV1.ChainProofs
  (ChainAddEpochGhost ChainRecvKeyGhost chainEpochAlign chainEpochSize)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent FreeOnlyEvs SeqEnv rustAllocEvents rustDeallocEvents rustReallocEvents)
open LibsignalBinary.Heap.Fine.ClientBounds (eventStepAlign eventStepReq)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit
  (HasFineReallocCredit stepEvents_rustAlloc_large stepEvents_rustAlloc_small
   stepEvents_rustRealloc_large_large stepEvents_rustRealloc_small_large
   stepEvents_rustRealloc_small_small)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (ConcatEnv ModelHyps PhaseCreditSpec)
open LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget
  (ChainNewEnv NextKeyInternalEnv VecDequeGrowEnv chainNewEvents nextKeyInternalEvents vecDequeGrowEvents)
open LibsignalBinary.Proofs.SpqrV1.Chain.AddEpochHelpersBudget (ChainAddEpochEnv chainAddEpochEvents)
open LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyHelpersBudget
  (ChainRecvKeyEnv chainRecvKeyEvents doReserveStep keyAdvanceLoopEvents keyHistoryAddStep)
open CryptoVerification.SpqrV1.Top.StateSize (rawChain rawChainEpoch rawEpochDir)

private theorem req_align_rustAlloc {req al : Nat} (hal : al ≤ 16) :
    ∀ ev ∈ rustAllocEvents req al, eventStepReq ev ≤ req ∧ eventStepAlign ev ≤ 16 := by
  unfold rustAllocEvents
  split <;> intro ev hev <;> rw [List.mem_singleton] at hev <;> subst hev <;>
    simp only [eventStepReq, eventStepAlign] <;> omega

private theorem req_align_rustDealloc (req al : Nat) :
    ∀ ev ∈ rustDeallocEvents req al, eventStepReq ev ≤ 0 ∧ eventStepAlign ev ≤ 16 := by
  intro ev hev
  unfold rustDeallocEvents at hev
  rw [List.mem_singleton] at hev
  subst hev
  exact ⟨Nat.le_refl 0, Nat.le_refl 16⟩

private theorem req_align_rustRealloc {old new al : Nat} (hal : al ≤ 16) (hal_new : al ≤ new) :
    ∀ ev ∈ rustReallocEvents old new al, eventStepReq ev ≤ new ∧ eventStepAlign ev ≤ 16 := by
  unfold rustReallocEvents
  simp only [hal, hal_new, and_self, ↓reduceIte]
  intro ev hev
  rw [List.mem_singleton] at hev
  subst hev
  exact ⟨Nat.le_refl new, hal⟩

/-! ## `<ChainEpochDirection>::next_key_internal` (`NextKeyInternalEnv`) -/

abbrev nextKeyInternalReq : Nat :=
  4 + chainNextInfo.length

/-- `PhaseCreditSpec` for `NextKeyInternalEnv` (`rustAllocEvents req 1 ++ rustDeallocEvents req 1`
with `req = 4 + chainNextInfo.length`): `Δcum = smallAllocCost M req` and `Δlive = Δpeak = 0` when
`req ≤ smallMaxReq M`. -/
theorem nextKeyInternal_phaseCreditSpec
    {M : AllocCostModel} [HasFineReallocCredit M]
    (hSmall : nextKeyInternalReq ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M NextKeyInternalEnv
      (HasFineReallocCredit.smallAllocCost M nextKeyInternalReq)
      0 0 nextKeyInternalReq := by
  have hpos : 0 < nextKeyInternalReq := by simp [nextKeyInternalReq]
  have ha := PhaseCreditSpec.rustAlloc_small M (req := nextKeyInternalReq) (al := 1)
    (by decide) hpos hSmall
  have hd := PhaseCreditSpec.rustDealloc_align16 M (req := nextKeyInternalReq) (al := 1)
    (by decide)
  refine (ha.concat hd).congr_mono ?_ (by omega) (by omega) (by omega) (by omega)
  intro evs hE
  rw [hE]
  exact ConcatEnv.append rfl rfl

theorem nextKeyInternal_phaseCreditSpec_of_hyps
    {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M) :
    PhaseCreditSpec M NextKeyInternalEnv
      (2 * nextKeyInternalReq + 9539)
      (nextKeyInternalReq + 8195)
      (nextKeyInternalReq + 8195)
      nextKeyInternalReq where
  req_align := by
    rintro _ rfl ev hev
    unfold nextKeyInternalEvents at hev
    rcases List.mem_append.mp hev with h1 | h2
    · exact req_align_rustAlloc (by decide) ev h1
    · obtain ⟨hr, ha⟩ := req_align_rustDealloc nextKeyInternalReq 1 ev h2
      exact ⟨by omega, ha⟩
  credit_le := by
    rintro st0 _ rfl
    have heq : nextKeyInternalEvents =
        rustAllocEvents nextKeyInternalReq 1 ++ rustDeallocEvents nextKeyInternalReq 1 := rfl
    rw [heq, M.stepEvents_append]
    by_cases hle : nextKeyInternalReq ≤ HasFineReallocCredit.smallMaxReq M
    · have hpos : 0 < nextKeyInternalReq := by simp [nextKeyInternalReq]
      obtain ⟨hc1, hl1, hp1⟩ :=
        stepEvents_rustAlloc_small M (req := nextKeyInternalReq) (al := 1) st0 (by decide) hpos hle
      have hsa := hM.smallAlloc_le hle
      obtain ⟨hc2, hl2, hp2⟩ :=
        (PhaseCreditSpec.rustDealloc_align16 M (req := nextKeyInternalReq) (al := 1)
          (by decide)).credit_le (M.stepEvents (rustAllocEvents nextKeyInternalReq 1) st0) rfl
      omega
    · have hgt : HasFineReallocCredit.smallMaxReq M < nextKeyInternalReq := by omega
      obtain ⟨hc1, hl1, hp1⟩ :=
        stepEvents_rustAlloc_large M (req := nextKeyInternalReq) (al := 1) st0 (by decide) hgt
      have hm := hM.meta_le
      have hla := hM.largeCost_le hgt
      obtain ⟨hc2, hl2, hp2⟩ :=
        (PhaseCreditSpec.rustDealloc_align16 M (req := nextKeyInternalReq) (al := 1)
          (by decide)).credit_le (M.stepEvents (rustAllocEvents nextKeyInternalReq 1) st0) rfl
      omega

/-! ## `<spqr::chain::Chain>::new` (`ChainNewEnv`) -/

/-- `PhaseCreditSpec` for `ChainNewEnv` when `448 ≤ smallMaxReq M` (all six allocations are small-class, so `Δlive = Δpeak = 0`).
-/
theorem chainNew_phaseCreditSpec_exact
    {M : AllocCostModel} [HasFineReallocCredit M]
    (hSmall448 : 448 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M ChainNewEnv
      (2 * HasFineReallocCredit.smallAllocCost M 72 +
        3 * HasFineReallocCredit.smallAllocCost M 32 +
        HasFineReallocCredit.smallAllocCost M 448)
      0 0 448 := by
  have h72 : 72 ≤ HasFineReallocCredit.smallMaxReq M := by omega
  have h32 : 32 ≤ HasFineReallocCredit.smallMaxReq M := by omega
  have ha72 := PhaseCreditSpec.rustAlloc_small M (req := 72) (al := 1) (by decide) (by decide) h72
  have ha32 := PhaseCreditSpec.rustAlloc_small M (req := 32) (al := 1) (by decide) (by decide) h32
  have ha448 : PhaseCreditSpec M
      (· = rustAllocEvents (4 * chainEpochSize) chainEpochAlign)
      (HasFineReallocCredit.smallAllocCost M 448) 0 0 448 :=
    PhaseCreditSpec.rustAlloc_small M (req := 448) (al := 8) (by decide) (by decide) hSmall448
  have h6 := ((((ha72.concat ha32).concat ha72).concat ha32).concat ha448).concat ha32
  refine h6.congr_mono ?_ (by omega) (by omega) (by omega) (by decide)
  intro evs hE
  rw [hE]
  unfold chainNewEvents
  exact ConcatEnv.append
    (ConcatEnv.append
      (ConcatEnv.append
        (ConcatEnv.append (ConcatEnv.append rfl rfl) rfl) rfl) rfl) rfl

theorem chainNew_phaseCreditSpec
    {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hSmall448 : 448 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M ChainNewEnv 58610 0 0 448 := by
  have h72 := hM.smallAlloc_le (r := 72) (by omega)
  have h32 := hM.smallAlloc_le (r := 32) (by omega)
  have h448 := hM.smallAlloc_le (r := 448) hSmall448
  exact (chainNew_phaseCreditSpec_exact hSmall448).mono
    (by omega) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 448)

/-! ## `<VecDeque<ChainEpoch>>::grow` and `<Chain>::add_epoch` (`ChainAddEpochEnv`) -/

def vecDequeGrowMaxReq (capBound : Nat) : Nat :=
  max (2 * capBound) 4 * chainEpochSize

/-- Single-step `PhaseCreditSpec` for `vecDequeGrowEvents cap` when `cap.toNat ≤ capBound`. -/
theorem vecDequeGrow_phaseCreditSpec
    {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M)
    {cap : BitVec 64} {capBound : Nat} (hcap : cap.toNat ≤ capBound) :
    let reqB := vecDequeGrowMaxReq capBound
    PhaseCreditSpec M (· = vecDequeGrowEvents cap)
      (2 * reqB + 9539) (reqB + 8195) (reqB + 8195) reqB := by
  intro reqB
  have hreq_align : ∀ ev ∈ vecDequeGrowEvents cap,
      eventStepReq ev ≤ reqB ∧ eventStepAlign ev ≤ 16 := by
    intro ev hev
    unfold vecDequeGrowEvents at hev
    by_cases hc : cap = 0#64
    · rw [ite_eq_left hc] at hev
      obtain ⟨hr, ha⟩ := req_align_rustAlloc (al := chainEpochAlign) (by decide) ev hev
      have h448 : 4 * chainEpochSize ≤ reqB := by
        unfold reqB vecDequeGrowMaxReq chainEpochSize
        omega
      exact ⟨Nat.le_trans hr h448, ha⟩
    · rw [ite_eq_right hc] at hev
      have hal_new : chainEpochAlign ≤ max (2 * cap.toNat) 4 * chainEpochSize := by
        unfold chainEpochAlign chainEpochSize
        omega
      obtain ⟨hr, ha⟩ := req_align_rustRealloc (al := chainEpochAlign) (by decide) hal_new ev hev
      have hnew : max (2 * cap.toNat) 4 * chainEpochSize ≤ reqB := by
        unfold reqB vecDequeGrowMaxReq chainEpochSize
        omega
      exact ⟨Nat.le_trans hr hnew, ha⟩
  refine
    { req_align := by
        rintro _ rfl ev hev
        exact hreq_align ev hev
      credit_le := ?_ }
  rintro st0 _ rfl
  unfold vecDequeGrowEvents
  by_cases hc : cap = 0#64
  · rw [ite_eq_left hc]
    unfold rustAllocEvents
    split
    · have h := hreq_align (.alloc (4 * chainEpochSize)) (by
        unfold vecDequeGrowEvents; rw [ite_eq_left hc]; unfold rustAllocEvents; split <;> simp_all)
      simpa [AllocCostModel.stepEvents] using hM.step_nonFree_aff st0 h.1 h.2
    · have h := hreq_align (.aligned (max chainEpochAlign 8) (4 * chainEpochSize)) (by
        unfold vecDequeGrowEvents; rw [ite_eq_left hc]; unfold rustAllocEvents; split <;> simp_all)
      simpa [AllocCostModel.stepEvents] using hM.step_nonFree_aff st0 h.1 h.2
  · rw [ite_eq_right hc]
    have hal_new : chainEpochAlign ≤ max (2 * cap.toNat) 4 * chainEpochSize := by
      unfold chainEpochAlign chainEpochSize
      omega
    have hre : rustReallocEvents (cap.toNat * chainEpochSize)
        (max (2 * cap.toNat) 4 * chainEpochSize) chainEpochAlign =
        [.realloc chainEpochAlign (cap.toNat * chainEpochSize)
          (max (2 * cap.toNat) 4 * chainEpochSize)] := by
      unfold rustReallocEvents
      simp only [show chainEpochAlign ≤ 16 by decide, hal_new, and_self, ↓reduceIte]
    rw [hre]
    have h := hreq_align
      (.realloc chainEpochAlign (cap.toNat * chainEpochSize)
        (max (2 * cap.toNat) 4 * chainEpochSize))
      (by unfold vecDequeGrowEvents; rw [ite_eq_right hc, hre]; simp)
    simpa [AllocCostModel.stepEvents] using hM.step_nonFree_aff st0 h.1 h.2

/-- `PhaseCreditSpec` for `<spqr::chain::Chain>::add_epoch` when `72 ≤ smallMaxReq M` and
`x.self.links.length ≤ lenBound` (independent of `x.G.linksCap`, since `vecDequeGrowEvents` fires
only when `x.self.links.length = x.G.linksCap.toNat`). -/
theorem chainAddEpoch_phaseCreditSpec
    {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hSmall72 : 72 ≤ HasFineReallocCredit.smallMaxReq M)
    (hkdf : HkdfFn) (x : ChainAddEpochGhost) {lenBound : Nat}
    (hlen : x.self.links.length ≤ lenBound) :
    let reqB := vecDequeGrowMaxReq lenBound
    PhaseCreditSpec M (ChainAddEpochEnv hkdf x)
      (2 * reqB + 57714) (reqB + 8195) (reqB + 8195) reqB := by
  intro reqB
  have h32 : 32 ≤ HasFineReallocCredit.smallMaxReq M := by omega
  have ha32 := PhaseCreditSpec.rustAlloc_small M (req := 32) (al := 1) (by decide) (by decide) h32
  have ha72 := PhaseCreditSpec.rustAlloc_small M (req := 72) (al := 1) (by decide) (by decide) hSmall72
  have hc32 := hM.smallAlloc_le h32
  have hc72 := hM.smallAlloc_le hSmall72
  have hd_nr : PhaseCreditSpec M
      (· = if x.G.nextRoot.cap = 0#64 then [] else rustDeallocEvents x.G.nextRoot.cap.toNat 1)
      0 0 0 0 := by
    split
    · exact PhaseCreditSpec.nil M
    · exact PhaseCreditSpec.rustDealloc_align16 M (by decide)
  have hd_es : PhaseCreditSpec M
      (· = if x.esPin.cap = 0#64 then [] else rustDeallocEvents x.esPin.cap.toNat 1)
      0 0 0 0 := by
    split
    · exact PhaseCreditSpec.nil M
    · exact PhaseCreditSpec.rustDealloc_align16 M (by decide)
  have hgrow_opt : PhaseCreditSpec M
      (· = if x.self.links.length = x.G.linksCap.toNat then vecDequeGrowEvents x.G.linksCap else [])
      (2 * reqB + 9539) (reqB + 8195) (reqB + 8195) reqB := by
    split
    · rename_i heq
      exact vecDequeGrow_phaseCreditSpec hM (Nat.le_trans (Nat.le_of_eq heq.symm) hlen)
    · exact (PhaseCreditSpec.nil M).mono (by omega) (by omega) (by omega) (by omega)
  have hreq_ge72 : 72 ≤ reqB := by
    unfold reqB vecDequeGrowMaxReq chainEpochSize
    omega
  have hok_seq :=
    (((((((ha32.concat hd_nr).concat ha72).concat ha32).concat ha72).concat ha32).concat hgrow_opt).concat hd_es)
  have hok : PhaseCreditSpec M (· = chainAddEpochEvents x)
      (2 * reqB + 57714) (reqB + 8195) (reqB + 8195) reqB := by
    refine hok_seq.congr_mono ?_ (by omega) (by omega) (by omega) (by omega)
    intro evs hE
    rw [hE]
    unfold chainAddEpochEvents
    exact ConcatEnv.append
      (ConcatEnv.append
        (ConcatEnv.append
          (ConcatEnv.append
            (ConcatEnv.append
              (ConcatEnv.append
                (ConcatEnv.append rfl rfl) rfl) rfl) rfl) rfl) rfl) rfl
  unfold ChainAddEpochEnv
  split
  · exact (PhaseCreditSpec.nil M).mono (by omega) (by omega) (by omega) (by omega)
  · exact hok

/-! ## `<spqr::chain::Chain>::recv_key` (`ChainRecvKeyEnv`) -/

/-- Virtual capacity `max cap 1` used in the exponential `reserveCap` doubling invariant `maxLen < virtCap cap * 2 ^ d`.
-/
def virtCap (cap : Nat) : Nat :=
  if cap = 0 then 1 else cap

/-- Live `sc = 63` byte charge held by a `Vec<u8>` buffer of capacity `cap` (`largeCost M cap` above `smallMaxReq M`, `0` otherwise).
-/
def capLargeLive (M : AllocCostModel) [HasFineReallocCredit M] (cap : Nat) : Nat :=
  if HasFineReallocCredit.smallMaxReq M < cap then
    HasFineReallocCredit.largeCost M cap
  else
    0

/-- Remaining `KeyHistory::add` calls permitted along `keyAdvanceLoopEvents` from counter `ctr` toward `atIdx` (`min (atIdx - 1 - ctr) maxOoo`).
-/
def keyAddBudget (atIdx maxOoo ctr : Nat) : Nat :=
  min (atIdx - 1 - ctr) maxOoo

private theorem capLargeLive_le_aff {M : AllocCostModel} [HasFineReallocCredit M]
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

private theorem doReserveStep_spec
    {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M)
    {cap len additional maxLen capMax d : Nat}
    (hadd_pos : 0 < additional)
    (hlen : len + additional ≤ maxLen)
    (hcap : cap ≤ capMax)
    (hcapMax : 2 * maxLen + 8 ≤ capMax)
    (hinv : maxLen < virtCap cap * 2 ^ d) :
    let res := doReserveStep cap len additional
    ∃ d', d' ≤ d ∧
      res.1 ≤ capMax ∧
      maxLen < virtCap res.1 * 2 ^ d' ∧
      (∀ e ∈ res.2, eventStepReq e ≤ capMax ∧ eventStepAlign e ≤ 16) ∧
      (∀ (st : M.σ) (L₀ : Nat),
        HasFineReallocCredit.liveLarge st ≤ L₀ + capLargeLive M cap →
        HasFineReallocCredit.cumSmall (M.stepEvents res.2 st) ≤
          HasFineReallocCredit.cumSmall st + (d - d') * (2 * capMax + 9539) ∧
        HasFineReallocCredit.liveLarge (M.stepEvents res.2 st) ≤
          L₀ + capLargeLive M res.1 ∧
        HasFineReallocCredit.peakLarge (M.stepEvents res.2 st) ≤
          max (HasFineReallocCredit.peakLarge st)
            (L₀ + capLargeLive M cap + capLargeLive M res.1)) := by
  dsimp only [doReserveStep]
  by_cases hfit : len + additional ≤ cap
  · rw [ite_eq_left hfit]
    dsimp only
    refine ⟨d, Nat.le_refl d, hcap, hinv, ?_, ?_⟩
    · intro e he; nomatch he
    · intro st L₀ hL
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
      have hcap'_gt : cap < cap' := by unfold cap' reserveCap; omega
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
      have hsub1 : d' + 1 - d' = 1 := by omega
      refine ⟨d', Nat.le_succ d', hcap'_le, hinv', ?_, ?_⟩
      · intro e he
        by_cases hc0 : cap = 0
        · rw [ite_eq_left hc0] at he
          obtain ⟨hr, ha⟩ := req_align_rustAlloc (al := 1) (by decide) e he
          exact ⟨Nat.le_trans hr hcap'_le, ha⟩
        · rw [ite_eq_right hc0] at he
          obtain ⟨hr, ha⟩ := req_align_rustRealloc (al := 1) (by decide) (by omega) e he
          exact ⟨Nat.le_trans hr hcap'_le, ha⟩
      · intro st L₀ hL
        rw [hsub1, Nat.one_mul]
        by_cases hc0 : cap = 0
        · rw [ite_eq_left hc0]
          have hcl0 : capLargeLive M cap = 0 := by unfold capLargeLive; rw [hc0]; simp
          by_cases hsm : cap' ≤ HasFineReallocCredit.smallMaxReq M
          · obtain ⟨hc, hl, hp⟩ :=
              stepEvents_rustAlloc_small M (req := cap') (al := 1) st (by decide) (by omega) hsm
            have hsa := hM.smallAlloc_le hsm
            have hcl' : capLargeLive M cap' = 0 := by unfold capLargeLive; rw [ite_eq_right (by omega)]
            omega
          · have hgt : HasFineReallocCredit.smallMaxReq M < cap' := by omega
            obtain ⟨hc, hl, hp⟩ :=
              stepEvents_rustAlloc_large M (req := cap') (al := 1) st (by decide) hgt
            have hm := hM.meta_le
            have hcl' : capLargeLive M cap' = HasFineReallocCredit.largeCost M cap' := by
              unfold capLargeLive; rw [ite_eq_left hgt]
            omega
        · rw [ite_eq_right hc0]
          have hcpos : 0 < cap := by omega
          by_cases hold_sm : cap ≤ HasFineReallocCredit.smallMaxReq M
          · have hcl_old : capLargeLive M cap = 0 := by
              unfold capLargeLive; rw [ite_eq_right (by omega)]
            by_cases hnew_sm : cap' ≤ HasFineReallocCredit.smallMaxReq M
            · obtain ⟨hc, hl, hp⟩ :=
                stepEvents_rustRealloc_small_small M (old := cap) (new := cap') (al := 1) st
                  (by decide) (by omega) hcpos hold_sm (by omega) hnew_sm
              have hsr := hM.smallRealloc_le hnew_sm
              have hcl_new : capLargeLive M cap' = 0 := by
                unfold capLargeLive; rw [ite_eq_right (by omega)]
              omega
            · have hnew_gt : HasFineReallocCredit.smallMaxReq M < cap' := by omega
              obtain ⟨hc, hl, hp⟩ :=
                stepEvents_rustRealloc_small_large M (old := cap) (new := cap') (al := 1) st
                  (by decide) (by omega) hcpos hold_sm hnew_gt
              have hm := hM.meta_le
              have hcl_new : capLargeLive M cap' = HasFineReallocCredit.largeCost M cap' := by
                unfold capLargeLive; rw [ite_eq_left hnew_gt]
              omega
          · have hold_gt : HasFineReallocCredit.smallMaxReq M < cap := by omega
            have hnew_gt : HasFineReallocCredit.smallMaxReq M < cap' := by omega
            obtain ⟨hc, hl, hp⟩ :=
              stepEvents_rustRealloc_large_large M (old := cap) (new := cap') (al := 1) st
                (by decide) (by omega) hold_gt hnew_gt
            have hm := hM.meta_le
            have hcl_old : capLargeLive M cap = HasFineReallocCredit.largeCost M cap := by
              unfold capLargeLive; rw [ite_eq_left hold_gt]
            have hcl_new : capLargeLive M cap' = HasFineReallocCredit.largeCost M cap' := by
              unfold capLargeLive; rw [ite_eq_left hnew_gt]
            omega

private theorem keyHistoryAddStep_eq (cap len : Nat) :
    keyHistoryAddStep cap len =
      let r1 := doReserveStep cap len 4
      let r2 := doReserveStep r1.1 (len + 4) 32
      (r2.1, r1.2 ++ r2.2) := rfl

private theorem keyHistoryAddStep_spec
    {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M)
    {cap len maxLen capMax d : Nat}
    (hlen : len + 36 ≤ maxLen)
    (hcap : cap ≤ capMax)
    (hcapMax : 2 * maxLen + 8 ≤ capMax)
    (hinv : maxLen < virtCap cap * 2 ^ d) :
    let res := keyHistoryAddStep cap len
    ∃ d2, d2 ≤ d ∧
      res.1 ≤ capMax ∧
      maxLen < virtCap res.1 * 2 ^ d2 ∧
      (∀ e ∈ res.2, eventStepReq e ≤ capMax ∧ eventStepAlign e ≤ 16) ∧
      (∀ (st : M.σ) (L₀ : Nat),
        HasFineReallocCredit.liveLarge st ≤ L₀ + capLargeLive M cap →
        HasFineReallocCredit.cumSmall (M.stepEvents res.2 st) ≤
          HasFineReallocCredit.cumSmall st + (d - d2) * (2 * capMax + 9539) ∧
        HasFineReallocCredit.liveLarge (M.stepEvents res.2 st) ≤
          L₀ + capLargeLive M res.1 ∧
        HasFineReallocCredit.peakLarge (M.stepEvents res.2 st) ≤
          max (HasFineReallocCredit.peakLarge st)
            (L₀ + 2 * (if HasFineReallocCredit.smallMaxReq M < capMax then capMax + 8195 else 0))) := by
  dsimp only
  rw [keyHistoryAddStep_eq]
  set r1 := doReserveStep cap len 4
  set r2 := doReserveStep r1.1 (len + 4) 32
  dsimp only
  obtain ⟨d1, hd1_le, hcap1, hinv1, hreq1, hcr1⟩ :=
    doReserveStep_spec hM (cap := cap) (len := len) (additional := 4)
      (by decide) (by omega) hcap hcapMax hinv
  obtain ⟨d2, hd2_le, hcap2, hinv2, hreq2, hcr2⟩ :=
    doReserveStep_spec hM (cap := r1.1) (len := len + 4) (additional := 32)
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
    have hcl0 := capLargeLive_le_aff hM hcap
    have hcl1 := capLargeLive_le_aff hM hcap1
    have hcl2 := capLargeLive_le_aff hM hcap2
    have hdist : (d - d1) * (2 * capMax + 9539) + (d1 - d2) * (2 * capMax + 9539) =
        (d - d2) * (2 * capMax + 9539) := by
      rw [← Nat.add_mul]
      congr 1
      omega
    dsimp only [r1, r2] at *
    omega

private theorem nextKeyInternal_ctr_and_key_len
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
        intro heq
        apply hmax
        apply beq_iff_eq.mpr
        exact BitVec.eq_of_toNat_eq heq
      have hlt : ctr.toNat < 2 ^ 32 - 1 := by
        have := ctr.isLt
        omega
      have hctr_nat : (ctr + 1#32).toNat = ctr.toNat + 1 := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]
        omega
      exact ⟨hctr1 ▸ hctr_nat, List.length_take_le 32 _⟩

private theorem keyHistory_add_length_le (kh : KeyHistory) (c : BitVec 32) (key : Bytes)
    (params : ChainParamsPB) (hk : key.length ≤ 32) :
    (kh.add (c, key) params).data.length ≤ kh.data.length + 36 :=
  CryptoVerification.SpqrV1.Top.StateSize.KeyHistory.add_length_le kh (c, key) params hk

private theorem keyAdvanceLoopEvents_spec
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
      (∀ e ∈ ev, eventStepReq e ≤ max nextKeyInternalReq capMax ∧ eventStepAlign e ≤ 16) ∧
      (∀ (st : M.σ) (L₀ : Nat),
        HasFineReallocCredit.liveLarge st ≤ L₀ + capLargeLive M cap →
        HasFineReallocCredit.cumSmall (M.stepEvents ev st) ≤
          HasFineReallocCredit.cumSmall st +
            rem * HasFineReallocCredit.smallAllocCost M nextKeyInternalReq +
            d * (2 * capMax + 9539) ∧
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
    have hcl := capLargeLive_le_aff hM hcap
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
        have hcl := capLargeLive_le_aff hM hcap
        exact ⟨by omega, by omega, Nat.le_max_left _ _⟩
      | ok res =>
        rcases res with ⟨next1, ctr1, cOut, key⟩
        dsimp only
        obtain ⟨hctr1_nat, hkey_len⟩ := nextKeyInternal_ctr_and_key_len hkdf hnki_call
        set maxOoo := params.maxOooKeysOrDefault
        by_cases hovf : ctr1.toNat + maxOoo.toNat ≥ 2 ^ 32
        · rw [ite_eq_left hovf]
          refine ⟨?_, ?_⟩
          · intro e he
            obtain ⟨hr, ha⟩ := hnki.req_align nextKeyInternalEvents rfl e he
            exact ⟨Nat.le_trans hr (Nat.le_max_left _ _), ha⟩
          · intro st L₀ hL
            obtain ⟨hc, hl, hp⟩ := hnki.credit_le st rfl
            have hcl := capLargeLive_le_aff hM hcap
            have h1 : (rem + 1) * HasFineReallocCredit.smallAllocCost M nextKeyInternalReq =
                HasFineReallocCredit.smallAllocCost M nextKeyInternalReq +
                  rem * HasFineReallocCredit.smallAllocCost M nextKeyInternalReq := by
              rw [Nat.succ_mul, Nat.add_comm]
            omega
        · rw [ite_eq_right hovf]
          by_cases hwin : ctr1 + maxOoo ≥ atIdx
          · rw [ite_eq_left hwin]
            have hsum_nat : (ctr1 + maxOoo).toNat = ctr1.toNat + maxOoo.toNat := by
              rw [BitVec.toNat_add]
              omega
            have hge_idx : ctr1.toNat + maxOoo.toNat ≥ atIdx.toNat := by
              have : atIdx.toNat ≤ (ctr1 + maxOoo).toNat := hwin
              omega
            have hbud_eq : keyAddBudget atIdx.toNat maxOoo.toNat ced.ctr.toNat =
                atIdx.toNat - 1 - ced.ctr.toNat := by
              unfold keyAddBudget
              omega
            have hbud_pos : 1 ≤ keyAddBudget atIdx.toNat maxOoo.toNat ced.ctr.toNat := by
              omega
            have hbud_next : keyAddBudget atIdx.toNat maxOoo.toNat ctr1.toNat =
                keyAddBudget atIdx.toNat maxOoo.toNat ced.ctr.toNat - 1 := by
              unfold keyAddBudget
              omega
            have hlen36 : ced.prev.data.length + 36 ≤ maxLen := by
              have : 36 * 1 ≤ 36 * keyAddBudget atIdx.toNat maxOoo.toNat ced.ctr.toNat :=
                Nat.mul_le_mul_left 36 hbud_pos
              omega
            obtain ⟨d2, hd2_le, hcap2, hinv2, hreq_add, hcr_add⟩ :=
              keyHistoryAddStep_spec hM hlen36 hcap hcapMax hinv
            set addRes := keyHistoryAddStep cap ced.prev.data.length
            set ced' : ChainEpochDirection :=
              { ctr := ctr1, next := next1, prev := ced.prev.add (ctr1, key) params }
            have hlenB' : ced'.prev.data.length +
                36 * keyAddBudget atIdx.toNat maxOoo.toNat ced'.ctr.toNat ≤ maxLen := by
              have hadd_len := keyHistory_add_length_le ced.prev ctr1 key params hkey_len
              change (ced.prev.add (ctr1, key) params).data.length +
                36 * keyAddBudget atIdx.toNat maxOoo.toNat ctr1.toNat ≤ maxLen
              rw [hbud_next]
              omega
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
              have hcl := capLargeLive_le_aff hM hcap
              obtain ⟨hc1, hl1, hp1⟩ := hnki.credit_le st rfl
              obtain ⟨hc2, hl2, hp2⟩ := hcr_add (M.stepEvents nextKeyInternalEvents st) L₀
                (by omega)
              obtain ⟨hc3, hl3, hp3⟩ := hcr_tail
                (M.stepEvents addRes.2 (M.stepEvents nextKeyInternalEvents st)) L₀ hl2
              have hmul_d : (d - d2) * (2 * capMax + 9539) + d2 * (2 * capMax + 9539) =
                  d * (2 * capMax + 9539) := by
                rw [← Nat.add_mul]
                congr 1
                omega
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
              unfold keyAddBudget
              omega
            have hlenB' : ced'.prev.data.length +
                36 * keyAddBudget atIdx.toNat maxOoo.toNat ced'.ctr.toNat ≤ maxLen := by
              have : 36 * keyAddBudget atIdx.toNat maxOoo.toNat ctr1.toNat ≤
                  36 * keyAddBudget atIdx.toNat maxOoo.toNat ced.ctr.toNat :=
                Nat.mul_le_mul_left 36 hbud_le
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
              have hcl := capLargeLive_le_aff hM hcap
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
      have hcl := capLargeLive_le_aff hM hcap
      exact ⟨by omega, by omega, Nat.le_max_left _ _⟩

private theorem keyHistoryAddStep_eq_self {cap len : Nat} (h : len + 36 ≤ cap) :
    keyHistoryAddStep cap len = (cap, []) := by
  have h1 : len + 4 ≤ cap := by omega
  have h2 : len + 4 + 32 ≤ cap := by omega
  simp only [keyHistoryAddStep, doReserveStep, h1, h2, ↓reduceIte, List.nil_append]

private theorem keyAdvanceLoopEvents_spec_ge
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
        obtain ⟨hctr1_nat, hkey_len⟩ := nextKeyInternal_ctr_and_key_len hkdf hnki_call
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
              have : atIdx.toNat ≤ (ctr1 + maxOoo).toNat := hwin
              omega
            have hbud_pos : 1 ≤ keyAddBudget atIdx.toNat maxOoo.toNat ced.ctr.toNat := by
              unfold keyAddBudget; omega
            have hbud_next : keyAddBudget atIdx.toNat maxOoo.toNat ctr1.toNat =
                keyAddBudget atIdx.toNat maxOoo.toNat ced.ctr.toNat - 1 := by
              unfold keyAddBudget; omega
            have hlen36 : ced.prev.data.length + 36 ≤ maxLen := by
              have := Nat.mul_le_mul_left 36 hbud_pos; omega
            rw [keyHistoryAddStep_eq_self (le_trans hlen36 hcap_ge)]
            dsimp only
            rw [List.append_nil]
            set ced' : ChainEpochDirection :=
              { ctr := ctr1, next := next1, prev := ced.prev.add (ctr1, key) params }
            have hlenB' : ced'.prev.data.length +
                36 * keyAddBudget atIdx.toNat maxOoo.toNat ced'.ctr.toNat ≤ maxLen := by
              have hadd_len := keyHistory_add_length_le ced.prev ctr1 key params hkey_len
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
    · rw [ite_eq_right hlt_idx]
      exact ⟨(fun _ h => nomatch h), fun st => ⟨by simp, le_rfl, Nat.le_max_left _ _⟩⟩

/-- Maximum `KeyHistory` byte capacity allocated by `<Chain>::recv_key` from initial length bound `initLenBound` and `maxOooCap`.
-/
def recvKeyCapMax (initLenBound maxOooCap : Nat) : Nat :=
  2 * (initLenBound + 36 * maxOooCap) + 8

/-- `PhaseCreditSpec` for `<spqr::chain::Chain>::recv_key` parameterized by `maxJumpCap`, `maxOooCap`,
`initLenBound`, and doubling bound `d`, independent of initial ghost capacities `x.G.epochs`. -/
theorem chainRecvKey_phaseCreditSpec
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
        d * (2 * capMax + 9539)
    let reqB := max (max 32 nextKeyInternalReq) capMax
    PhaseCreditSpec M (ChainRecvKeyEnv hkdf x) cumB largeB (2 * largeB) reqB := by
  intro capMax largeB cumB reqB
  have h32 : 32 ≤ HasFineReallocCredit.smallMaxReq M := le_trans (Nat.le_max_left _ _) hSmall
  have hNki : nextKeyInternalReq ≤ HasFineReallocCredit.smallMaxReq M :=
    le_trans (Nat.le_max_right _ _) hSmall
  have ha32 := PhaseCreditSpec.rustAlloc_small M (req := 32) (al := 1) (by decide) (by decide) h32
  have hnki := nextKeyInternal_phaseCreditSpec hNki
  have hnil : PhaseCreditSpec M (· = []) cumB largeB (2 * largeB) reqB :=
    (PhaseCreditSpec.nil M).mono (by omega) (by omega) (by omega) (by omega)
  unfold ChainRecvKeyEnv chainRecvKeyEvents
  split
  · exact hnil
  · cases heidx : x.self.epochIdx x.epoch with
    | error _ =>
      dsimp only
      exact hnil
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
            refine ha32.mono (by omega) (by omega) (by omega) ?_
            exact le_trans (Nat.le_max_left 32 nextKeyInternalReq) (Nat.le_max_left _ capMax)
        · next hnot_lt =>
          split
          · exact hnil
          · split
            · next hjump_gt => exact hnil
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
                    (HasFineReallocCredit.smallAllocCost M nextKeyInternalReq) (by omega : rem + 1 ≤ maxJumpCap + 1)
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
                    keyAdvanceLoopEvents_spec hM hNki hkdf x.self.params x.index
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
                    keyAdvanceLoopEvents_spec_ge hNki hkdf x.self.params x.index
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

/-! ## `maxOooCap`-Parameterized `rawChain` Step Bounds -/

private theorem keyAdvanceLoop_window_length_le
    (hkdf : HkdfFn) (ed : ChainEpochDirection) (atIdx : BitVec 32) (params : ChainParamsPB)
    {ed' : ChainEpochDirection}
    (h : ed.keyAdvanceLoop hkdf atIdx params = .ok ed') :
    ed'.prev.data.length ≤
      ed.prev.data.length + 36 * keyAddBudget atIdx.toNat params.maxOooKeysOrDefault.toNat ed.ctr.toNat := by
  suffices ∀ n (ed : ChainEpochDirection), atIdx.toNat - ed.ctr.toNat ≤ n →
      ed.keyAdvanceLoop hkdf atIdx params = .ok ed' →
      ed'.prev.data.length ≤
        ed.prev.data.length + 36 * keyAddBudget atIdx.toNat params.maxOooKeysOrDefault.toNat ed.ctr.toNat from
    this (atIdx.toNat - ed.ctr.toNat) ed (Nat.le_refl _) h
  intro n; induction n with
  | zero =>
    intro ed hn h
    unfold ChainEpochDirection.keyAdvanceLoop at h
    split at h
    · omega
    · split at h
      · contradiction
      · simp only [Except.ok.injEq] at h; subst h; exact Nat.le_add_right _ _
  | succ n ih =>
    intro ed hn h
    unfold ChainEpochDirection.keyAdvanceLoop at h
    split at h
    · rename_i hlt
      split at h
      · contradiction
      · rename_i next1 ctr1 k hnk
        rcases k with ⟨cOut, key⟩
        obtain ⟨hctr1_nat, hkey_len⟩ := nextKeyInternal_ctr_and_key_len hkdf hnk
        dsimp only [] at h
        split at h
        · contradiction
        · by_cases hwin : ctr1 + params.maxOooKeysOrDefault ≥ atIdx
          · simp only [hwin, ↓reduceIte] at h
            have ihp := ih { ctr := ctr1, next := next1, prev := ed.prev.add (cOut, key) params }
              (by dsimp only []; omega) h
            have hsum_nat : (ctr1 + params.maxOooKeysOrDefault).toNat =
                ctr1.toNat + params.maxOooKeysOrDefault.toNat := by
              rw [BitVec.toNat_add]; omega
            have hge_idx : ctr1.toNat + params.maxOooKeysOrDefault.toNat ≥ atIdx.toNat := by
              have : atIdx.toNat ≤ (ctr1 + params.maxOooKeysOrDefault).toNat := hwin
              omega
            have hbud_pos : 1 ≤ keyAddBudget atIdx.toNat params.maxOooKeysOrDefault.toNat ed.ctr.toNat := by
              unfold keyAddBudget; omega
            have hbud_next : keyAddBudget atIdx.toNat params.maxOooKeysOrDefault.toNat ctr1.toNat =
                keyAddBudget atIdx.toNat params.maxOooKeysOrDefault.toNat ed.ctr.toNat - 1 := by
              unfold keyAddBudget; omega
            have hadd := keyHistory_add_length_le ed.prev cOut key params hkey_len
            dsimp only [] at ihp
            rw [hbud_next] at ihp
            have : 36 + 36 * (keyAddBudget atIdx.toNat params.maxOooKeysOrDefault.toNat ed.ctr.toNat - 1) =
                36 * keyAddBudget atIdx.toNat params.maxOooKeysOrDefault.toNat ed.ctr.toNat := by
              have h1 : keyAddBudget atIdx.toNat params.maxOooKeysOrDefault.toNat ed.ctr.toNat =
                  (keyAddBudget atIdx.toNat params.maxOooKeysOrDefault.toNat ed.ctr.toNat - 1) + 1 := by
                omega
              conv_rhs => rw [h1, Nat.mul_add]
              omega
            omega
          · simp only [hwin, ↓reduceIte] at h
            have ihp := ih { ctr := ctr1, next := next1, prev := ed.prev }
              (by dsimp only []; omega) h
            have hbud_le : keyAddBudget atIdx.toNat params.maxOooKeysOrDefault.toNat ctr1.toNat ≤
                keyAddBudget atIdx.toNat params.maxOooKeysOrDefault.toNat ed.ctr.toNat := by
              unfold keyAddBudget; omega
            have hmul := Nat.mul_le_mul_left 36 hbud_le
            dsimp only [] at ihp
            omega
    · split at h
      · contradiction
      · simp only [Except.ok.injEq] at h; subst h; exact Nat.le_add_right _ _

/-- Bounds `rawEpochDir ed'.intoPb ≤ rawEpochDir ed.intoPb + 32 + 36 * maxOooCap` for `ChainEpochDirection.key`.
-/
theorem key_raw_le_of_maxOoo (hkdf : HkdfFn) (ed : ChainEpochDirection)
    (atIdx : BitVec 32) (params : ChainParamsPB) {maxOooCap : Nat}
    (hOoo : params.maxOooKeysOrDefault.toNat ≤ maxOooCap)
    {ed' : ChainEpochDirection} {out : Bytes}
    (h : ed.key hkdf atIdx params = .ok (ed', out)) :
    rawEpochDir ed'.intoPb ≤ rawEpochDir ed.intoPb + 32 + 36 * maxOooCap := by
  unfold ChainEpochDirection.key at h; dsimp only [] at h; split at h
  · rcases hget : ed.prev.get atIdx ed.ctr params with e | ⟨prev', out'⟩
    · simp [hget, Bind.bind, Except.bind] at h
    · simp only [hget, Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq,
        Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      have hp := CryptoVerification.SpqrV1.Top.StateSize.KeyHistory.get_length_le
        ed.prev atIdx ed.ctr params hget
      simp only [ChainEpochDirection.intoPb, rawEpochDir]; omega
  · split at h
    · contradiction
    · split at h
      · contradiction
      · split at h
        · contradiction
        · set self0 :=
            if atIdx > ed.ctr + params.maxOooKeysOrDefault then
              { ed with prev := ed.prev.clear }
            else
              ed
          rcases hadv : self0.keyAdvanceLoop hkdf atIdx params with e | self1
          · simp [self0, hadv, Bind.bind, Except.bind] at h
          · simp only [self0, hadv, Bind.bind, Except.bind] at h
            rcases hgc : CryptoVerification.LibsignalSpqrV1.ChainResult.ofPanic
                (self1.prev.gc self1.ctr params) with e | prevGc
            · simp [hgc] at h
            · simp only [hgc] at h
              rcases hnk : CryptoVerification.LibsignalSpqrV1.ChainResult.ofPanic
                  (ChainEpochDirection.nextKeyInternal hkdf self1.next self1.ctr) with
                e | ⟨next', ctr', cOut, outKey⟩
              · simp [hnk] at h
              · simp only [hnk, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
                rcases h with ⟨rfl, rfl⟩
                have h0 : self0.prev.data.length ≤ ed.prev.data.length := by
                  dsimp [self0]; split <;> simp [KeyHistory.clear]
                have hadvp := keyAdvanceLoop_window_length_le hkdf self0 atIdx params hadv
                have hgc' : self1.prev.gc self1.ctr params = .ok prevGc := by
                  unfold CryptoVerification.LibsignalSpqrV1.ChainResult.ofPanic at hgc
                  split at hgc <;> simp_all
                have hgcp := CryptoVerification.SpqrV1.Top.StateSize.KeyHistory.gc_length_le
                  self1.prev self1.ctr params hgc'
                have hnk' : ChainEpochDirection.nextKeyInternal hkdf self1.next self1.ctr =
                    .ok (next', ctr', (cOut, outKey)) := by
                  unfold CryptoVerification.LibsignalSpqrV1.ChainResult.ofPanic at hnk
                  split at hnk <;> simp_all
                have ⟨hn, _⟩ :=
                  CryptoVerification.SpqrV1.Top.StateSize.ChainEpochDirection.nextKeyInternal_length_le
                    hkdf self1.next self1.ctr hnk'
                have hbud_le : keyAddBudget atIdx.toNat params.maxOooKeysOrDefault.toNat self0.ctr.toNat ≤
                    maxOooCap := by
                  unfold keyAddBudget
                  exact le_trans (Nat.min_le_right _ _) hOoo
                have hmul := Nat.mul_le_mul_left 36 hbud_le
                simp only [ChainEpochDirection.intoPb, rawEpochDir]; omega

/-- Bounds `rawChain c'.intoPb ≤ rawChain c.intoPb + 32 + 36 * maxOooCap` for `<Chain>::recv_key`.
-/
theorem recvKey_raw_le_of_maxOoo (hkdf : HkdfFn) (c : Chain) (epoch : Epoch) (index : BitVec 32)
    {maxOooCap : Nat} (hOoo : c.params.maxOooKeysOrDefault.toNat ≤ maxOooCap)
    {c' : Chain} {out : Bytes} (h : c.recvKey hkdf epoch index = .ok (c', out)) :
    rawChain c'.intoPb ≤ rawChain c.intoPb + 32 + 36 * maxOooCap := by
  unfold Chain.recvKey at h; split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h; rcases h with ⟨rfl, _⟩; omega
  · rcases heidx : CryptoVerification.LibsignalSpqrV1.ChainResult.ofError (c.epochIdx epoch) with
      e | epochIndex
    · simp [heidx, Bind.bind, Except.bind] at h
    · simp only [heidx, Bind.bind, Except.bind] at h
      cases hlink : c.links[epochIndex]? with
      | none => simp [hlink] at h
      | some link =>
        simp only [hlink] at h
        rcases hkey : link.recv.key hkdf index c.params with e | ⟨recv', out'⟩
        · simp [hkey] at h
        · simp only [hkey, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          have hrecv := key_raw_le_of_maxOoo hkdf link.recv index c.params hOoo hkey
          have hset := CryptoVerification.SpqrV1.Top.StateSize.sum_map_set_le
            CryptoVerification.SpqrV1.Top.StateSize.linkRaw
            c.links epochIndex link { link with recv := recv' }
            (32 + 36 * maxOooCap) hlink
            (by simp only [CryptoVerification.SpqrV1.Top.StateSize.linkRaw]; omega)
          have hmap :
              ((c.links.set epochIndex { link with recv := recv' }).map
                (fun link => ({ send := some link.send.intoPb, recv := some link.recv.intoPb } :
                  CryptoVerification.LibsignalSpqrV1.ChainEpochPB))).map
                (fun e => rawChainEpoch e + 200) =
              (c.links.set epochIndex { link with recv := recv' }).map
                CryptoVerification.SpqrV1.Top.StateSize.linkRaw := by
            clear * -
            induction (c.links.set epochIndex { link with recv := recv' }) with
            | nil => rfl
            | cons l ls ih => rw [List.map_cons, List.map_cons, List.map_cons, ih]; rfl
          have hmap0 :
              (c.links.map
                (fun link => ({ send := some link.send.intoPb, recv := some link.recv.intoPb } :
                  CryptoVerification.LibsignalSpqrV1.ChainEpochPB))).map
                (fun e => rawChainEpoch e + 200) =
              c.links.map CryptoVerification.SpqrV1.Top.StateSize.linkRaw := by
            clear * -
            induction c.links with
            | nil => rfl
            | cons l ls ih => rw [List.map_cons, List.map_cons, List.map_cons, ih]; rfl
          simp only [Chain.intoPb, rawChain, hmap, hmap0]
          omega

end LibsignalBinary.Proofs.PeakBudget.SpqrRecvPeakHelpers
