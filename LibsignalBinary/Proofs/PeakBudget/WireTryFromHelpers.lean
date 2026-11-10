/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.ClientBounds
public import LibsignalBinary.Proofs.PeakBudget.GroupCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.PeakBudget.WireSignalHelpers
public import LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDefs

/-!
# Parametric Fine-Credit Helpers for `SignalMessage::try_from` & `PreKeySignalMessage::try_from`

Parametric `(M : AllocCostModel) [HasFineReallocCredit M]` step and amortization helpers under
`ModelHyps M` and `WireLowInterceptHyps M`:
1. `WireLowInterceptHyps M` (`smallMaxReq M = 135167` and positive-request `78 * r + 110` bound,
   discharged on `fineCostModel`).
2. Bounded-fuel capacity-doubling counter `wireGrowsFrom` / `wireRemGrows` (`= 19` at `N = 1 MiB`)
   with monotonicity and `reserveCap` step decrement lemmas.
3. Tight `135167`-capped allocation/reallocation bounds, `reserveClear_cum_amortized_S`, and
   `g`-sum `sc = 63` `liveLarge` / `peakLarge` step bounds.
4. Post-loop `into_boxed_slice`, `try_clone_from_ref`, `SignalMessage.tryFrom` field-length bounds,
   and `WireGroupHyps M` small-allocation group step lemmas.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.WireTryFromHelpers

open CryptoGames.LibsignalSession (ProtoSignalMessage SignalMessage SignalProtocolError)
open CryptoVerification.LibsignalProtoCodec (WireType decode mergeBytes protoSignalCodec)
open CryptoVerification.LibsignalTripleRatchet (reserveCap)
open CryptoVerification.LibsignalTripleRatchet.Wire (MsgFieldsLe decode_field_lengths)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent FreeOnlyEvs SeqEnv
   rustAllocEvents rustDeallocEvents rustReallocEvents)
open LibsignalBinary.Heap.Fine (FineScale MmapThresholdReq coarseGrpWtS fineCostModel)
open LibsignalBinary.Heap.Fine.ClientBounds
  (eventStepAlign eventStepReq fineCostModel_smallMaxReq_eq reqMinOfClass
   smallAllocCost_pos_le_78_mul_add)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit
  (HasFineGroupCredit PhaseGroupSpec
   smallAllocGroupS_le_16659_of_le_44 smallAllocGroupS_le_43464_of_le_108)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (ConcatEnv ModelHyps PhaseCreditSpec)
open VerifiedLibraries.Mallocng.Proofs (sizeToClassUnits sizeToClass_spec)
open LibsignalBinary.Proofs.PeakBudget.WireSignalHelpers
  (bytesCumAlloc bytesCumAlloc_le_aff bytesCumRealloc bytesCumRealloc_le_aff
   bytesLargeLive bytesLargeLive_le_aff bytesLargeLive_zero
   req_align_of_rustAllocEvents req_align_of_rustDeallocEvents req_align_of_rustReallocEvents
   stepEvents_rustAlloc_pos stepEvents_rustDealloc_any stepEvents_rustRealloc_pos)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
  (bytesMergeEventsCore doReserveClearEvents)

/-! ## Low-Intercept Hypothesis (`WireLowInterceptHyps`) & Computable `wireRemGrows` -/

/-- Low-intercept small-allocation hypothesis on `M` (discharged on `fineCostModel` via
`ClientBounds.fineCostModel_smallMaxReq_eq` and `ClientBounds.smallAllocCost_pos_le_78_mul_add`),
keeping `SeqCreditKit.ModelHyps` untouched. -/
structure WireLowInterceptHyps (M : AllocCostModel) [HasFineReallocCredit M] : Prop where
  hSmallMaxEq : HasFineReallocCredit.smallMaxReq M = 135167
  hSmallAllocPos78 : ∀ {r : Nat}, 0 < r → r ≤ HasFineReallocCredit.smallMaxReq M →
    HasFineReallocCredit.smallAllocCost M r ≤ 78 * r + 110

/-- Discharge `WireLowInterceptHyps` on `fineCostModel`. -/
theorem fineCostModel_wireLowInterceptHyps : WireLowInterceptHyps fineCostModel where
  hSmallMaxEq := fineCostModel_smallMaxReq_eq
  hSmallAllocPos78 hpos _ := smallAllocCost_pos_le_78_mul_add hpos

/-- Bounded-fuel capacity-doubling counter (`fuel = 65` covers every `cap < 2 ^ 64`, while structural
recursion on `fuel` ensures instant kernel `decide` / `rfl` reduction without `WellFounded.fix`). -/
def wireGrowsAux : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | fuel + 1, B, cap =>
    if B < cap ∨ cap = 0 then 0
    else 1 + wireGrowsAux fuel B (2 * cap)

/-- Number of remaining `Vec<u8>` capacity doublings starting from positive capacity `cap`
while `cap ≤ min N (2 ^ 64 - 1)`. -/
def wireGrowsFrom (N cap : Nat) : Nat :=
  wireGrowsAux 65 (min N (2 ^ 64 - 1)) cap

/-- Number of remaining `Vec<u8>` `reserveCap` growths starting from capacity `cap`
under payload length cap `N` (`= 19` at `N = 1048576, cap = 0`). -/
def wireRemGrows (N cap : Nat) : Nat :=
  if cap = 0 then 1 + wireGrowsFrom N 8
  else wireGrowsFrom N cap

private theorem wireGrowsAux_anti :
    ∀ (k B c₁ c₂ : Nat), 0 < c₁ → c₁ ≤ c₂ →
      wireGrowsAux k B c₂ ≤ wireGrowsAux k B c₁
  | 0, _, _, _, _, _ => Nat.le_refl 0
  | k + 1, B, c₁, c₂, hpos, hle => by
    simp only [wireGrowsAux]
    by_cases h2 : B < c₂ ∨ c₂ = 0
    · simp only [h2, ↓reduceIte]
      exact Nat.zero_le _
    · have h1 : ¬ (B < c₁ ∨ c₁ = 0) := by omega
      simp only [h2, h1, ↓reduceIte]
      exact Nat.add_le_add_left
        (wireGrowsAux_anti k B (2 * c₁) (2 * c₂) (by omega) (by omega)) 1

theorem wireGrowsFrom_anti_cap (N c₁ c₂ : Nat) (hpos : 0 < c₁) (hle : c₁ ≤ c₂) :
    wireGrowsFrom N c₂ ≤ wireGrowsFrom N c₁ :=
  wireGrowsAux_anti 65 (min N (2 ^ 64 - 1)) c₁ c₂ hpos hle

private theorem wireGrowsAux_mono :
    ∀ (k B₁ B₂ cap : Nat), B₁ ≤ B₂ →
      wireGrowsAux k B₁ cap ≤ wireGrowsAux k B₂ cap
  | 0, _, _, _, _ => Nat.le_refl 0
  | k + 1, B₁, B₂, cap, hB => by
    simp only [wireGrowsAux]
    by_cases h1 : B₁ < cap ∨ cap = 0
    · simp only [h1, ↓reduceIte]
      exact Nat.zero_le _
    · have h2 : ¬ (B₂ < cap ∨ cap = 0) := by omega
      simp only [h1, h2, ↓reduceIte]
      exact Nat.add_le_add_left (wireGrowsAux_mono k B₁ B₂ (2 * cap) hB) 1

theorem wireGrowsFrom_mono {N₁ N₂ : Nat} (cap : Nat) (hN : N₁ ≤ N₂) :
    wireGrowsFrom N₁ cap ≤ wireGrowsFrom N₂ cap :=
  wireGrowsAux_mono 65 _ _ cap
    (Nat.le_min.mpr ⟨Nat.le_trans (Nat.min_le_left _ _) hN, Nat.min_le_right _ _⟩)

theorem wireRemGrows_mono {N₁ N₂ : Nat} (cap : Nat) (hN : N₁ ≤ N₂) :
    wireRemGrows N₁ cap ≤ wireRemGrows N₂ cap := by
  unfold wireRemGrows
  split_ifs
  · exact Nat.add_le_add_left (wireGrowsFrom_mono 8 hN) 1
  · exact wireGrowsFrom_mono cap hN

private theorem wireGrowsAux_eq_succ :
    ∀ (k B c : Nat), 0 < c → B < 2 ^ k * c →
      wireGrowsAux (k + 1) B c = wireGrowsAux k B c
  | 0, B, c, _, hf => by
    have hBc : B < c := by simpa using hf
    have hcond : B < c ∨ c = 0 := Or.inl hBc
    simp only [wireGrowsAux, hcond, ↓reduceIte]
  | k + 1, B, c, hpos, hf => by
    change (if B < c ∨ c = 0 then 0 else 1 + wireGrowsAux (k + 1) B (2 * c)) =
      (if B < c ∨ c = 0 then 0 else 1 + wireGrowsAux k B (2 * c))
    by_cases hcond : B < c ∨ c = 0
    · simp only [hcond, ↓reduceIte]
    · simp only [hcond, ↓reduceIte]
      have hf' : B < 2 ^ k * (2 * c) := by
        rw [Nat.pow_succ, Nat.mul_assoc] at hf
        exact hf
      rw [wireGrowsAux_eq_succ k B (2 * c) (Nat.mul_pos (by decide) hpos) hf']

theorem reserveCap_grow_bounds {cap vLen : Nat} (hlt : cap < vLen) :
    8 ≤ reserveCap cap 0 vLen ∧
    2 * cap ≤ reserveCap cap 0 vLen ∧
    cap < reserveCap cap 0 vLen ∧
    reserveCap cap 0 vLen ≤ max (2 * vLen) 8 := by
  dsimp only [reserveCap]
  omega

theorem wireRemGrows_reserveCap_step {N cap vLen : Nat}
    (hcap64 : cap < 2 ^ 64) (hlt : cap < vLen) (hv : vLen ≤ N) :
    wireRemGrows N (reserveCap cap 0 vLen) + 1 ≤ wireRemGrows N cap := by
  obtain ⟨h8, h2c, _, _⟩ := reserveCap_grow_bounds hlt
  set cap' := reserveCap cap 0 vLen
  have hne' : cap' ≠ 0 := by omega
  unfold wireRemGrows
  by_cases hc0 : cap = 0
  · simp only [hc0, hne', ↓reduceIte]
    have hanti := wireGrowsFrom_anti_cap N 8 cap' (by decide) h8
    rw [Nat.add_comm 1 _]
    exact Nat.add_le_add_right hanti 1
  · simp only [hc0, hne', ↓reduceIte]
    have hpos : 0 < cap := Nat.pos_of_ne_zero hc0
    set B := min N (2 ^ 64 - 1)
    have hcapN : cap ≤ N := Nat.le_of_lt (Nat.lt_of_lt_of_le hlt hv)
    have hcap264 : cap ≤ 2 ^ 64 - 1 := Nat.le_sub_one_of_lt hcap64
    have hcapB : cap ≤ B := Nat.le_min.mpr ⟨hcapN, hcap264⟩
    have hnot : ¬ (B < cap ∨ cap = 0) := by
      rintro (hB | h0)
      · exact Nat.not_lt_of_ge hcapB hB
      · exact hc0 h0
    have hRhs : wireGrowsFrom N cap = 1 + wireGrowsAux 64 B (2 * cap) := by
      unfold wireGrowsFrom
      change wireGrowsAux (64 + 1) B cap = 1 + wireGrowsAux 64 B (2 * cap)
      simp only [wireGrowsAux, hnot, ↓reduceIte]
    have hf64 : B < 2 ^ 64 * (2 * cap) :=
      Nat.lt_of_le_of_lt (Nat.min_le_right N (2 ^ 64 - 1))
        (Nat.lt_of_lt_of_le (by decide : 2 ^ 64 - 1 < 2 ^ 64 * 2)
          (Nat.mul_le_mul_left (2 ^ 64) (Nat.mul_le_mul_left 2 (Nat.succ_le_of_lt hpos))))
    have heq64 : wireGrowsFrom N (2 * cap) = wireGrowsAux 64 B (2 * cap) :=
      wireGrowsAux_eq_succ 64 B (2 * cap) (Nat.mul_pos (by decide) hpos) hf64
    have hanti := wireGrowsFrom_anti_cap N (2 * cap) cap' (Nat.mul_pos (by decide) hpos) h2c
    rw [hRhs, ← heq64, Nat.add_comm 1 _]
    exact Nat.add_le_add_right hanti 1

/-! ## Tight `WireLowInterceptHyps` Single-Step Cost & Doubling Lemmas -/

theorem bytesCumAlloc_pos_le_94 {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : WireLowInterceptHyps M) {req : Nat} (hpos : 0 < req) :
    bytesCumAlloc M req ≤ 94 * (req + 1) := by
  unfold bytesCumAlloc
  have hne : req ≠ 0 := Nat.ne_of_gt hpos
  simp only [hne, ↓reduceIte]
  split_ifs with hsm
  · have h78 := hLow.hSmallAllocPos78 hpos hsm
    omega
  · have hm := hM.meta_le
    omega

theorem bytesCumAlloc_le_min_S {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {S : Nat} (hSm : HasFineReallocCredit.smallMaxReq M = S) (req : Nat) :
    bytesCumAlloc M req ≤ 2 * min req S + 9539 := by
  unfold bytesCumAlloc
  split_ifs with h0 hsm
  · omega
  · have hsa := hM.smallAlloc_le hsm
    omega
  · have hm := hM.meta_le
    omega

theorem bytesCumRealloc_le_min_S {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {S : Nat} (hSm : HasFineReallocCredit.smallMaxReq M = S)
    (old new : Nat) :
    bytesCumRealloc M old new ≤ 2 * min new S + 9539 := by
  unfold bytesCumRealloc
  split_ifs with h0 hsm
  · omega
  · have hsr := hM.smallRealloc_le hsm
    omega
  · have hm := hM.meta_le
    omega

theorem bytesLargeLive_eq_zero_of_le_S {M : AllocCostModel} [HasFineReallocCredit M]
    {S : Nat} (hSm : HasFineReallocCredit.smallMaxReq M = S) {req : Nat} (hle : req ≤ S) :
    bytesLargeLive M req = 0 := by
  unfold bytesLargeLive
  have hsm : req ≤ HasFineReallocCredit.smallMaxReq M := by omega
  simp [hsm]

theorem bytesLargeLive_le_two_mul_of_le_max {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {S : Nat} (hSm : HasFineReallocCredit.smallMaxReq M = S) (hS8 : 8 ≤ S)
    {c g : Nat} (hc : c ≤ max (2 * g) 8) :
    bytesLargeLive M c ≤ 2 * g + 8195 := by
  unfold bytesLargeLive
  split_ifs with hsm
  · omega
  · have hgt : HasFineReallocCredit.smallMaxReq M < c := Nat.lt_of_not_ge hsm
    have hl := hM.largeCost_le hgt
    omega

theorem reserveClear_cum_amortized_S {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {S : Nat} (hSm : HasFineReallocCredit.smallMaxReq M = S)
    {cap vLen : Nat} (hlt : cap < vLen) :
    let cap' := reserveCap cap 0 vLen
    (if cap = 0 then bytesCumAlloc M cap' else bytesCumRealloc M cap cap') ≤
      4 * (min cap' S - min cap S) + 9539 := by
  obtain ⟨h8, h2c, _, _⟩ := reserveCap_grow_bounds hlt
  set cap' := reserveCap cap 0 vLen
  have hpos' : 0 < cap' := by omega
  have hne' : cap' ≠ 0 := by omega
  by_cases hc0 : cap = 0
  · simp only [hc0, ↓reduceIte]
    unfold bytesCumAlloc
    simp only [hne', ↓reduceIte]
    split_ifs with hsm
    · have hsa := hM.smallAlloc_le hsm
      omega
    · have hm := hM.meta_le
      omega
  · simp only [hc0, ↓reduceIte]
    unfold bytesCumRealloc
    have hnot0 : ¬ (cap = 0 ∨ cap' = 0) := by omega
    simp only [hnot0, ↓reduceIte]
    split_ifs with hsm
    · have hsr := hM.smallRealloc_le hsm
      omega
    · have hm := hM.meta_le
      omega

theorem doReserveClearEvents_step_tight {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {S cap vLen rem maxLen base Φ_other g_other g_f : Nat}
    (hSm : HasFineReallocCredit.smallMaxReq M = S) (hS8 : 8 ≤ S)
    (hlt : cap < vLen) (hv_rem : vLen ≤ rem) (hrem_max : rem ≤ maxLen)
    (hcap_g : cap ≤ max (2 * g_f) 8)
    (hother : Φ_other ≤ 2 * g_other + 24585)
    (hg_sum : g_other + g_f + vLen ≤ maxLen)
    (stA : M.σ)
    (hliveA : HasFineReallocCredit.liveLarge stA ≤
      base + Φ_other + bytesLargeLive M cap + bytesLargeLive M vLen) :
    let cap' := reserveCap cap 0 vLen
    (∀ ev ∈ doReserveClearEvents cap vLen,
      eventStepReq ev ≤ max 128 (2 * rem) ∧ eventStepAlign ev ≤ 16) ∧
    cap < cap' ∧
    cap' ≤ max 8 (2 * maxLen) ∧
    cap' ≤ max (2 * vLen) 8 ∧
    HasFineReallocCredit.cumSmall (M.stepEvents (doReserveClearEvents cap vLen) stA) ≤
      HasFineReallocCredit.cumSmall stA + 4 * (min cap' S - min cap S) + 9539 ∧
    HasFineReallocCredit.liveLarge (M.stepEvents (doReserveClearEvents cap vLen) stA) ≤
      base + Φ_other + bytesLargeLive M cap' + bytesLargeLive M vLen ∧
    HasFineReallocCredit.peakLarge (M.stepEvents (doReserveClearEvents cap vLen) stA) ≤
      max (HasFineReallocCredit.peakLarge stA) (base + (3 * maxLen + 49170)) := by
  obtain ⟨h8, _, hcap_lt', hcap_v2⟩ := reserveCap_grow_bounds hlt
  set cap' := reserveCap cap 0 vLen with hcap'_eq
  have hcap'_req : cap' ≤ max 128 (2 * rem) := by omega
  have hcap'_max : cap' ≤ max 8 (2 * maxLen) := by omega
  have hl_cap := bytesLargeLive_le_two_mul_of_le_max hM hSm hS8 hcap_g
  have hl_v := bytesLargeLive_le_aff hM vLen
  have hl_cap' := bytesLargeLive_le_two_mul_of_le_max hM hSm hS8 hcap_v2
  have hamort := reserveClear_cum_amortized_S hM hSm hlt
  change (if cap = 0 then bytesCumAlloc M cap' else bytesCumRealloc M cap cap') ≤
    4 * (min cap' S - min cap S) + 9539 at hamort
  have hnot_le : ¬ (vLen ≤ cap) := by omega
  unfold doReserveClearEvents
  simp only [hnot_le, ↓reduceIte, ← hcap'_eq]
  by_cases hcap0 : cap = 0
  · simp only [hcap0, ↓reduceIte] at hamort ⊢
    have hreq := req_align_of_rustAllocEvents (req := cap') (al := 1) hcap'_req (by decide)
    have hstep := stepEvents_rustAlloc_pos M (req := cap') (al := 1) (by decide) (by omega) stA
    subst hcap0
    rw [bytesLargeLive_zero] at hliveA
    exact ⟨hreq, hcap_lt', hcap'_max, hcap_v2, by omega, by omega, by omega⟩
  · have hcap_pos : 0 < cap := by omega
    simp only [hcap0, ↓reduceIte] at hamort ⊢
    have hreq := req_align_of_rustReallocEvents (old := cap) (new := cap') (al := 1)
      hcap'_req (by decide)
    have hstep := stepEvents_rustRealloc_pos M (old := cap) (new := cap') (al := 1)
      (by decide) (by omega) hcap_pos (by omega) stA
    exact ⟨hreq, hcap_lt', hcap'_max, hcap_v2, by omega, by omega, by omega⟩

theorem bytesMergeEventsCore_step_tight {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : WireLowInterceptHyps M)
    {wt : WireType} {bs v rest : List (BitVec 8)}
    {S cap rem rem' maxLen base Φ_other g_other g_f : Nat}
    (hSm : HasFineReallocCredit.smallMaxReq M = S) (hS8 : 8 ≤ S)
    (hm : mergeBytes wt bs = some (v, rest))
    (hrem : rem' + v.length + 1 ≤ rem)
    (hmax : rem ≤ maxLen)
    (hcap64 : cap < 2 ^ 64)
    (hcap_le : cap ≤ max 8 (2 * maxLen))
    (hcap_g : cap ≤ max (2 * g_f) 8)
    (hother : Φ_other ≤ 2 * g_other + 24585)
    (hg_rem : g_other + g_f + rem ≤ maxLen)
    (st : M.σ)
    (hlive : HasFineReallocCredit.liveLarge st ≤ base + Φ_other + bytesLargeLive M cap) :
    let cap' := if v.length ≤ cap then cap else reserveCap cap 0 v.length
    let g_f' := if v.length ≤ cap then g_f else v.length
    (∀ ev ∈ bytesMergeEventsCore wt (BitVec.ofNat 64 cap) bs,
      eventStepReq ev ≤ max 128 (2 * rem) ∧ eventStepAlign ev ≤ 16) ∧
    min cap S ≤ min cap' S ∧
    min cap' S ≤ min (max 8 (2 * maxLen)) S ∧
    cap' ≤ max 8 (2 * maxLen) ∧
    cap' ≤ max (2 * g_f') 8 ∧
    g_other + g_f' + rem' ≤ maxLen ∧
    HasFineReallocCredit.cumSmall
        (M.stepEvents (bytesMergeEventsCore wt (BitVec.ofNat 64 cap) bs) st) +
        9539 * wireRemGrows maxLen cap' ≤
      HasFineReallocCredit.cumSmall st + 94 * (rem - rem') +
        4 * (min cap' S - min cap S) + 9539 * wireRemGrows maxLen cap ∧
    HasFineReallocCredit.liveLarge
        (M.stepEvents (bytesMergeEventsCore wt (BitVec.ofNat 64 cap) bs) st) ≤
      base + Φ_other + bytesLargeLive M cap' ∧
    HasFineReallocCredit.peakLarge
        (M.stepEvents (bytesMergeEventsCore wt (BitVec.ofNat 64 cap) bs) st) ≤
      max (HasFineReallocCredit.peakLarge st) (base + (3 * maxLen + 49170)) := by
  have htoNat : (BitVec.ofNat 64 cap).toNat = cap := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcap64]
  unfold bytesMergeEventsCore
  rw [hm, htoNat]
  by_cases hv0 : v.length = 0
  · simp only [hv0, Nat.zero_le, ↓reduceIte, AllocCostModel.stepEvents_nil]
    exact ⟨(fun _ h => nomatch h), Nat.le_refl _, by omega, hcap_le, hcap_g, by omega,
      by omega, hlive, Nat.le_max_left _ _⟩
  · have hv_pos : 0 < v.length := by omega
    have hv_rem : v.length ≤ rem := by omega
    have hv_max : v.length ≤ maxLen := by omega
    have hv_req : v.length ≤ max 128 (2 * rem) := by omega
    simp only [hv0, ↓reduceIte, AllocCostModel.stepEvents_append]
    have hA_req := req_align_of_rustAllocEvents (req := v.length) (al := 1) hv_req (by decide)
    have hA := stepEvents_rustAlloc_pos M (req := v.length) (al := 1) (by decide) hv_pos st
    set stA := M.stepEvents (rustAllocEvents v.length 1) st
    have hc_v := bytesCumAlloc_pos_le_94 hM hLow hv_pos
    have hl_v := bytesLargeLive_le_aff hM v.length
    have hl_cap := bytesLargeLive_le_two_mul_of_le_max hM hSm hS8 hcap_g
    by_cases hv_le : v.length ≤ cap
    · simp only [hv_le, ↓reduceIte]
      have hB_nil : doReserveClearEvents cap v.length = [] := by
        unfold doReserveClearEvents; simp [hv_le]
      rw [hB_nil, AllocCostModel.stepEvents_nil]
      have hC := stepEvents_rustDealloc_any M v.length 1 (by decide) stA
      have hC_req := req_align_of_rustDeallocEvents (req := v.length) (al := 1)
        (maxReq := max 128 (2 * rem)) (by decide)
      set W := wireRemGrows maxLen cap
      refine ⟨?_, Nat.le_refl _, by omega, hcap_le, hcap_g, by omega, by omega, by omega, by omega⟩
      intro ev hev
      rcases List.mem_append.mp hev with h12 | h3
      · rcases List.mem_append.mp h12 with h1 | h2
        · exact hA_req ev h1
        · nomatch h2
      · exact hC_req ev h3
    · have hcap_lt_v : cap < v.length := by omega
      simp only [hv_le, ↓reduceIte]
      have hliveA : HasFineReallocCredit.liveLarge stA ≤
          base + Φ_other + bytesLargeLive M cap + bytesLargeLive M v.length := by omega
      have hg_sum_v : g_other + v.length ≤ maxLen := by omega
      have hg_sum_step : g_other + g_f + v.length ≤ maxLen := by omega
      obtain ⟨hB_req, hcap_lt', hcap'_max, hcap'_v2, hB_cum, hB_live, hB_peak⟩ :=
        doReserveClearEvents_step_tight hM hSm hS8 hcap_lt_v hv_rem hmax
          hcap_g hother hg_sum_step stA hliveA
      set cap' := reserveCap cap 0 v.length
      set stB := M.stepEvents (doReserveClearEvents cap v.length) stA
      have hC := stepEvents_rustDealloc_any M v.length 1 (by decide) stB
      have hC_req := req_align_of_rustDeallocEvents (req := v.length) (al := 1)
        (maxReq := max 128 (2 * rem)) (by decide)
      have hW_step := wireRemGrows_reserveCap_step hcap64 hcap_lt_v hv_max
      change wireRemGrows maxLen cap' + 1 ≤ wireRemGrows maxLen cap at hW_step
      set W := wireRemGrows maxLen cap
      set W' := wireRemGrows maxLen cap'
      refine ⟨?_, by omega, by omega, hcap'_max, hcap'_v2, by omega, by omega, by omega, by omega⟩
      intro ev hev
      rcases List.mem_append.mp hev with h12 | h3
      · rcases List.mem_append.mp h12 with h1 | h2
        · exact hA_req ev h1
        · exact hB_req ev h2
      · exact hC_req ev h3

theorem errTail_nil_or_from_or_push_tight {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {S maxLen base Φ : Nat}
    (hSm : HasFineReallocCredit.smallMaxReq M = S) (hS128 : 128 ≤ S)
    (st : M.σ)
    (hlive : HasFineReallocCredit.liveLarge st ≤ base + Φ)
    {evs : List AllocEvent}
    (hevs : evs = [] ∨ evs = rustAllocEvents 72 8 ∨
      evs = rustAllocEvents 72 8 ++ [] ∨
      evs = rustAllocEvents 72 8 ++ rustAllocEvents 128 8) :
    (∀ ev ∈ evs, eventStepReq ev ≤ max 128 (2 * maxLen) ∧ eventStepAlign ev ≤ 16) ∧
    HasFineReallocCredit.cumSmall (M.stepEvents evs st) ≤
      HasFineReallocCredit.cumSmall st + 19478 ∧
    HasFineReallocCredit.liveLarge (M.stepEvents evs st) ≤
      base + Φ ∧
    HasFineReallocCredit.peakLarge (M.stepEvents evs st) ≤
      max (HasFineReallocCredit.peakLarge st) (base + Φ) := by
  have h72_req : 72 ≤ max 128 (2 * maxLen) := by omega
  have h128_req : 128 ≤ max 128 (2 * maxLen) := by omega
  have hc72 := bytesCumAlloc_le_aff hM 72
  have hc128 := bytesCumAlloc_le_aff hM 128
  have hl72 : bytesLargeLive M 72 = 0 := bytesLargeLive_eq_zero_of_le_S hSm (by omega)
  have hl128 : bytesLargeLive M 128 = 0 := bytesLargeLive_eq_zero_of_le_S hSm hS128
  rcases hevs with rfl | rfl | rfl | rfl
  · refine ⟨(fun _ h => nomatch h), ?_⟩
    simp only [AllocCostModel.stepEvents_nil]
    exact ⟨by omega, by omega, by omega⟩
  · refine ⟨req_align_of_rustAllocEvents (al := 8) h72_req (by decide), ?_⟩
    have h1 := stepEvents_rustAlloc_pos M (req := 72) (al := 8) (by decide) (by decide) st
    exact ⟨by omega, by omega, by omega⟩
  · rw [List.append_nil]
    refine ⟨req_align_of_rustAllocEvents (al := 8) h72_req (by decide), ?_⟩
    have h1 := stepEvents_rustAlloc_pos M (req := 72) (al := 8) (by decide) (by decide) st
    exact ⟨by omega, by omega, by omega⟩
  · refine ⟨?_, ?_⟩
    · intro ev hev
      rcases List.mem_append.mp hev with h1 | h2
      · exact req_align_of_rustAllocEvents (al := 8) h72_req (by decide) ev h1
      · exact req_align_of_rustAllocEvents (al := 8) h128_req (by decide) ev h2
    · rw [AllocCostModel.stepEvents_append]
      have h1 := stepEvents_rustAlloc_pos M (req := 72) (al := 8) (by decide) (by decide) st
      set s1 := M.stepEvents (rustAllocEvents 72 8) st
      have h2 := stepEvents_rustAlloc_pos M (req := 128) (al := 8) (by decide) (by decide) s1
      exact ⟨by omega, by omega, by omega⟩

theorem phaseCredit_intoBoxedSlice_S {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {S : Nat} (hSm : HasFineReallocCredit.smallMaxReq M = S)
    (bs : List (BitVec 8)) :
    PhaseCreditSpec M
      (fun evs => ∃ cap : BitVec 64, bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧
        evs = (if cap.toNat ≤ bs.length then []
               else if bs = [] then rustDeallocEvents cap.toNat 1
               else rustReallocEvents cap.toNat bs.length 1))
      (2 * min bs.length S + 9539) (bs.length + 8195) (bs.length + 8195) bs.length where
  req_align := by
    rintro evs ⟨cap, _, _, rfl⟩ ev hev
    split at hev
    · nomatch hev
    · split at hev
      · exact req_align_of_rustDeallocEvents (al := 1) (by decide) ev hev
      · exact req_align_of_rustReallocEvents (al := 1) (Nat.le_refl _) (by decide) ev hev
  credit_le := by
    rintro st0 evs ⟨cap, hle, _, rfl⟩
    split
    · simp only [AllocCostModel.stepEvents_nil]
      exact ⟨by omega, by omega, by omega⟩
    · rename_i hnot_le
      split
      · have hd := stepEvents_rustDealloc_any M cap.toNat 1 (by decide) st0
        exact ⟨by omega, by omega, by omega⟩
      · rename_i hne_nil
        have hbs_pos : 0 < bs.length := List.length_pos_iff.mpr hne_nil
        have hcap_pos : 0 < cap.toNat := by omega
        have hr := stepEvents_rustRealloc_pos M (old := cap.toNat) (new := bs.length) (al := 1)
          (by decide) (by omega) hcap_pos hbs_pos st0
        have hc := bytesCumRealloc_le_min_S hM hSm cap.toNat bs.length
        have hl := bytesLargeLive_le_aff hM bs.length
        exact ⟨by omega, by omega, by omega⟩

theorem phaseCredit_tryCloneBytes_S {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {S : Nat} (hSm : HasFineReallocCredit.smallMaxReq M = S)
    (bs : List (BitVec 8)) :
    PhaseCreditSpec M
      (fun evs => evs = if bs = [] then [] else rustAllocEvents bs.length 1)
      (2 * min bs.length S + 9539) (bs.length + 8195) (bs.length + 8195) bs.length where
  req_align := by
    rintro evs rfl ev hev
    split at hev
    · nomatch hev
    · exact req_align_of_rustAllocEvents (al := 1) (Nat.le_refl _) (by decide) ev hev
  credit_le := by
    rintro st0 evs rfl
    split
    · simp only [AllocCostModel.stepEvents_nil]
      exact ⟨by omega, by omega, by omega⟩
    · rename_i hne_nil
      have hbs_pos : 0 < bs.length := List.length_pos_iff.mpr hne_nil
      have ha := stepEvents_rustAlloc_pos M (req := bs.length) (al := 1) (by decide) hbs_pos st0
      have hc := bytesCumAlloc_le_min_S hM hSm bs.length
      have hl := bytesLargeLive_le_aff hM bs.length
      exact ⟨by omega, by omega, by omega⟩

/-! ## Affine `ModelHyps`-Only Helpers & `SignalMessage.tryFrom` Field Bounds -/

theorem reserveCap_step_bounds {cap vLen maxLen : Nat}
    (hlt : cap < vLen) (hv : vLen ≤ maxLen) (hcap_lt : cap < maxLen) :
    let cap' := reserveCap cap 0 vLen
    8 ≤ cap' ∧ cap < cap' ∧ cap' ≤ 2 * (cap' - cap) ∧ cap' ≤ max 8 (2 * maxLen) := by
  dsimp only [reserveCap]
  omega

theorem bytesLargeLive_le_capBound {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {c maxLen : Nat} (hc : c ≤ max 8 (2 * maxLen)) :
    bytesLargeLive M c ≤ 2 * maxLen + 8203 := by
  have hl := bytesLargeLive_le_aff hM c
  omega

theorem phaseCredit_intoBoxedSlice {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (bs : List (BitVec 8)) :
    PhaseCreditSpec M
      (fun evs => ∃ cap : BitVec 64, bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧
        evs = (if cap.toNat ≤ bs.length then []
               else if bs = [] then rustDeallocEvents cap.toNat 1
               else rustReallocEvents cap.toNat bs.length 1))
      (2 * bs.length + 9539) (bs.length + 8195) (bs.length + 8195) bs.length where
  req_align := by
    rintro evs ⟨cap, _, _, rfl⟩ ev hev
    split at hev
    · nomatch hev
    · split at hev
      · exact req_align_of_rustDeallocEvents (al := 1) (by decide) ev hev
      · exact req_align_of_rustReallocEvents (al := 1) (Nat.le_refl _) (by decide) ev hev
  credit_le := by
    rintro st0 evs ⟨cap, hle, _, rfl⟩
    split
    · simp only [AllocCostModel.stepEvents_nil]
      exact ⟨by omega, by omega, by omega⟩
    · rename_i hnot_le
      split
      · have hd := stepEvents_rustDealloc_any M cap.toNat 1 (by decide) st0
        exact ⟨by omega, by omega, by omega⟩
      · rename_i hne_nil
        have hbs_pos : 0 < bs.length := List.length_pos_iff.mpr hne_nil
        have hcap_pos : 0 < cap.toNat := by omega
        have hr := stepEvents_rustRealloc_pos M (old := cap.toNat) (new := bs.length) (al := 1)
          (by decide) (by omega) hcap_pos hbs_pos st0
        have hc := bytesCumRealloc_le_aff hM cap.toNat bs.length
        have hl := bytesLargeLive_le_aff hM bs.length
        exact ⟨by omega, by omega, by omega⟩

theorem phaseCredit_tryCloneBytes {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (bs : List (BitVec 8)) :
    PhaseCreditSpec M
      (fun evs => evs = if bs = [] then [] else rustAllocEvents bs.length 1)
      (2 * bs.length + 9539) (bs.length + 8195) (bs.length + 8195) bs.length where
  req_align := by
    rintro evs rfl ev hev
    split at hev
    · nomatch hev
    · exact req_align_of_rustAllocEvents (al := 1) (Nat.le_refl _) (by decide) ev hev
  credit_le := by
    rintro st0 evs rfl
    split
    · simp only [AllocCostModel.stepEvents_nil]
      exact ⟨by omega, by omega, by omega⟩
    · rename_i hne_nil
      have hbs_pos : 0 < bs.length := List.length_pos_iff.mpr hne_nil
      have ha := stepEvents_rustAlloc_pos M (req := bs.length) (al := 1) (by decide) hbs_pos st0
      have hc := bytesCumAlloc_le_aff hM bs.length
      have hl := bytesLargeLive_le_aff hM bs.length
      exact ⟨by omega, by omega, by omega⟩

theorem tryFrom_ok_field_lengths {bs : List (BitVec 8)} {msg : SignalMessage}
    (h : SignalMessage.tryFrom protoSignalCodec bs = .ok msg) :
    msg.serialized.length ≤ bs.length ∧
    msg.ciphertext.length ≤ bs.length ∧
    (msg.addresses.getD []).length ≤ bs.length := by
  unfold SignalMessage.tryFrom at h
  simp only [bind, Except.bind] at h
  split at h
  · nomatch h
  · split at h
    · nomatch h
    · split at h
      · nomatch h
      · cases hdec : protoSignalCodec.decode
            ((bs.take (bs.length - CryptoGames.LibsignalSession.macLength)).drop 1) with
        | none => rw [hdec] at h; cases h
        | some p =>
          rw [hdec] at h
          dsimp only at h
          cases hrk : p.ratchetKey with
          | none => rw [hrk] at h; cases h
          | some rk =>
            rw [hrk] at h
            dsimp only at h
            cases hpk : CryptoGames.LibsignalSession.PublicKey.deserialize rk with
            | error _ => rw [hpk] at h; cases h
            | ok pk =>
              rw [hpk] at h
              dsimp only at h
              cases hctr : p.counter with
              | none => rw [hctr] at h; cases h
              | some ctr =>
                rw [hctr] at h
                dsimp only at h
                cases hct : p.ciphertext with
                | none => rw [hct] at h; cases h
                | some ct =>
                  rw [hct] at h
                  dsimp only [pure, Except.pure] at h
                  injection h with hmsg
                  subst hmsg
                  have hd : decode
                      ((bs.take (bs.length - CryptoGames.LibsignalSession.macLength)).drop 1) =
                      some p := hdec
                  obtain ⟨_, hct_le, _, had_le⟩ := decode_field_lengths hd
                  have hslice_le :
                      ((bs.take (bs.length - CryptoGames.LibsignalSession.macLength)).drop 1).length ≤
                      bs.length := by
                    simp only [List.length_drop, List.length_take]
                    omega
                  simp only [hct, Option.getD_some] at hct_le
                  exact ⟨Nat.le_refl _, Nat.le_trans hct_le hslice_le,
                    Nat.le_trans had_le hslice_le⟩

/-! ## Small-Allocation Group Hypotheses (`WireGroupHyps`) & `PhaseGroupSpec` Step Lemmas -/

/-- Per-size-class group-weight hypotheses on `M` (discharged on `fineCostModel` via a 48-class
`decide +kernel` check plus `GroupCreditKit` small-bucket lemmas), keeping `SeqCreditKit` and
`GroupCreditKit` untouched:
- `hSmallAllocPosGrp`: across all `0 < r ≤ MmapThresholdReq` (`sc = 0..47`),
  `smallAllocGroupS M r ≤ 2369 * (r + 1)` (attained at `sc = 0, r = 1` where
  `coarseGrpWtS 0 = 4737 ≤ 2369 * 2 = 4738`, and covering `sc = 8, r ≥ 125` where
  `coarseGrpWtS 8 = 140011 ≤ 2369 * 126 = 298494`);
- `hSmallAllocLe44`: `smallAllocGroupS M r ≤ 16659` for `r ≤ 44` (`sc ≤ 2`);
- `hSmallAllocLe108`: `smallAllocGroupS M r ≤ 43464` for `r ≤ 108` (`sc ≤ 6`);
- `hSmallAllocCapGrp` / `hSmallReallocCapGrp`: global cap `140011` (`sc = 8, 9`) across all
  `r ≤ MmapThresholdReq`. -/
structure WireGroupHyps (M : AllocCostModel) [HasFineGroupCredit M] : Prop where
  hSmallAllocPosGrp : ∀ {r : Nat}, 0 < r → r ≤ MmapThresholdReq →
    HasFineGroupCredit.smallAllocGroupS M r ≤ 2369 * (r + 1)
  hSmallAllocLe44 : ∀ {r : Nat}, r ≤ 44 →
    HasFineGroupCredit.smallAllocGroupS M r ≤ 16659
  hSmallAllocLe108 : ∀ {r : Nat}, r ≤ 108 →
    HasFineGroupCredit.smallAllocGroupS M r ≤ 43464
  hSmallAllocCapGrp : ∀ {r : Nat}, r ≤ MmapThresholdReq →
    HasFineGroupCredit.smallAllocGroupS M r ≤ 140011
  hSmallReallocCapGrp : ∀ {r : Nat}, r ≤ MmapThresholdReq →
    HasFineGroupCredit.smallReallocGroupS M r ≤ 140011

private def checkWireGroupBounds : Bool :=
  (List.range 48).all fun sc =>
    let rMinPos := max 1 (reqMinOfClass sc)
    let gWt := coarseGrpWtS sc
    let rWt := max gWt FineScale
    decide (
      gWt ≤ 2369 * (rMinPos + 1) ∧
      gWt ≤ 140011 ∧
      rWt ≤ 140011)

private theorem checkWireGroupBounds_true : checkWireGroupBounds = true := by
  decide +kernel

private theorem wire_reqMinOfClass_le {req : Nat} (hreq : req ≤ MmapThresholdReq) :
    sizeToClassUnits ((req + 3) / 16) < 48 ∧
    reqMinOfClass (sizeToClassUnits ((req + 3) / 16)) ≤ req := by
  have hspec := sizeToClass_spec (req := req) (by unfold MmapThresholdReq at hreq; exact hreq)
  dsimp only at hspec ⊢
  refine ⟨hspec.1, ?_⟩
  unfold reqMinOfClass
  rcases hspec.2.2 with h0 | hprev
  · simp [h0]
  · split <;> omega

/-- Discharge `WireGroupHyps` on `fineCostModel`. -/
theorem fineCostModel_wireGroupHyps : WireGroupHyps fineCostModel where
  hSmallAllocPosGrp {r} hpos hle := by
    obtain ⟨hsc, hrmin⟩ := wire_reqMinOfClass_le hle
    have hcell := List.all_eq_true.mp checkWireGroupBounds_true _ (List.mem_range.mpr hsc)
    have hb := (of_decide_eq_true hcell).1
    exact Nat.le_trans hb
      (Nat.mul_le_mul_left 2369 (Nat.add_le_add_right (Nat.max_le.mpr ⟨hpos, hrmin⟩) 1))
  hSmallAllocLe44 h := smallAllocGroupS_le_16659_of_le_44 h
  hSmallAllocLe108 h := smallAllocGroupS_le_43464_of_le_108 h
  hSmallAllocCapGrp {_} hle := by
    obtain ⟨hsc, _⟩ := wire_reqMinOfClass_le hle
    have hcell := List.all_eq_true.mp checkWireGroupBounds_true _ (List.mem_range.mpr hsc)
    exact (of_decide_eq_true hcell).2.1
  hSmallReallocCapGrp {_} hle := by
    obtain ⟨hsc, _⟩ := wire_reqMinOfClass_le hle
    have hcell := List.all_eq_true.mp checkWireGroupBounds_true _ (List.mem_range.mpr hsc)
    exact (of_decide_eq_true hcell).2.2

theorem phaseGroupSpec_rustAlloc_cap {M : AllocCostModel} [HasFineGroupCredit M]
    (hGrp : WireGroupHyps M) (size : Nat) {align : Nat} (hal : align ≤ 16) :
    PhaseGroupSpec M (· = rustAllocEvents size align) 140011 := by
  by_cases hle : size ≤ MmapThresholdReq
  · exact (PhaseGroupSpec.rustAlloc_small M hal hle).mono (hGrp.hSmallAllocCapGrp hle)
  · exact (PhaseGroupSpec.rustAlloc_large M hal (Nat.lt_of_not_ge hle)).mono
      (by decide : FineScale ≤ 140011)

theorem phaseGroupSpec_rustAlloc_le44 {M : AllocCostModel} [HasFineGroupCredit M]
    (hGrp : WireGroupHyps M) {size align : Nat} (hsz : size ≤ 44) (hal : align ≤ 16) :
    PhaseGroupSpec M (· = rustAllocEvents size align) 16659 :=
  (PhaseGroupSpec.rustAlloc_small M hal
    (Nat.le_trans hsz (by decide : 44 ≤ MmapThresholdReq))).mono
    (hGrp.hSmallAllocLe44 hsz)

theorem phaseGroupSpec_rustAlloc_le108 {M : AllocCostModel} [HasFineGroupCredit M]
    (hGrp : WireGroupHyps M) {size align : Nat} (hsz : size ≤ 108) (hal : align ≤ 16) :
    PhaseGroupSpec M (· = rustAllocEvents size align) 43464 :=
  (PhaseGroupSpec.rustAlloc_small M hal
    (Nat.le_trans hsz (by decide : 108 ≤ MmapThresholdReq))).mono
    (hGrp.hSmallAllocLe108 hsz)

theorem phaseGroupSpec_rustAlloc_pos_2369 {M : AllocCostModel} [HasFineGroupCredit M]
    (hGrp : WireGroupHyps M) {size align : Nat} (hpos : 0 < size) (hal : align ≤ 16) :
    PhaseGroupSpec M (· = rustAllocEvents size align) (2369 * (size + 1)) := by
  by_cases hle : size ≤ MmapThresholdReq
  · exact (PhaseGroupSpec.rustAlloc_small M hal hle).mono (hGrp.hSmallAllocPosGrp hpos hle)
  · have hgt : MmapThresholdReq < size := Nat.lt_of_not_ge hle
    have hfs : FineScale ≤ 2369 * (size + 1) :=
      Nat.le_trans (by decide : FineScale ≤ 2369 * (MmapThresholdReq + 2))
        (Nat.mul_le_mul_left 2369 (Nat.add_le_add_right hgt 1))
    exact (PhaseGroupSpec.rustAlloc_large M hal hgt).mono hfs

theorem phaseGroupSpec_rustRealloc_cap {M : AllocCostModel} [HasFineGroupCredit M]
    (hGrp : WireGroupHyps M) (oldSz newSz : Nat) {align : Nat} (hal : align ≤ 16) :
    PhaseGroupSpec M (· = rustReallocEvents oldSz newSz align) 140011 := by
  by_cases hle : newSz ≤ MmapThresholdReq
  · exact (PhaseGroupSpec.rustRealloc_small M hal hle).mono (hGrp.hSmallReallocCapGrp hle)
  · exact (PhaseGroupSpec.rustRealloc_large M hal (Nat.lt_of_not_ge hle)).mono
      (by decide : FineScale ≤ 140011)

theorem phaseGroupSpec_doReserveClear_cap {M : AllocCostModel} [HasFineGroupCredit M]
    (hGrp : WireGroupHyps M) (cap vLen : Nat) :
    PhaseGroupSpec M (· = doReserveClearEvents cap vLen) 140011 := by
  unfold doReserveClearEvents
  by_cases hv : vLen ≤ cap
  · simp only [hv, ↓reduceIte]
    exact (PhaseGroupSpec.nil M).mono (Nat.zero_le 140011)
  · simp only [hv, ↓reduceIte]
    by_cases hc0 : cap = 0
    · simp only [hc0, ↓reduceIte]
      exact phaseGroupSpec_rustAlloc_cap hGrp _ (by decide : 1 ≤ 16)
    · simp only [hc0, ↓reduceIte]
      exact phaseGroupSpec_rustRealloc_cap hGrp _ _ (by decide : 1 ≤ 16)

private theorem grp_idle_le (G R W : Nat) : G + W ≤ G + R + W := by
  omega

private theorem grp_fit_step {g0 gA gC V R W : Nat}
    (hA : gA ≤ g0 + V) (hV : V ≤ R) (hC : gC ≤ gA + 0) :
    gC + W ≤ g0 + R + W := by
  omega

private theorem grp_grow_step {g0 gA gB gC V R K W' W : Nat}
    (hA : gA ≤ g0 + V) (hV : V ≤ R)
    (hB : gB ≤ gA + K) (hC : gC ≤ gB + 0)
    (hW : W' + K ≤ W) :
    gC + W' ≤ g0 + R + W := by
  omega

/-- Per-tag `bytes::merge` group-credit step: charges `2369 * (rem - rem')` `FineScale` units for
the temporary `copy_to_bytes` buffer (`v.length = 0` emits `[]`, while `v.length ≥ 1` consumes
`≥ v.length + 1 ≥ 2` input bytes across `sc = 0..47` and `mmap`) and amortizes `Vec<u8>` capacity
doublings at `140011` per remaining `wireRemGrows maxLen cap`. -/
theorem bytesMergeEventsCore_groups_step {M : AllocCostModel} [HasFineGroupCredit M]
    (hGrp : WireGroupHyps M)
    {wt : WireType} {bs v rest : List (BitVec 8)}
    {cap rem rem' maxLen : Nat}
    (hm : mergeBytes wt bs = some (v, rest))
    (hrem : rem' + v.length + 1 ≤ rem)
    (hmax : rem ≤ maxLen)
    (hcap64 : cap < 2 ^ 64)
    (st : M.σ) :
    let cap' := if v.length ≤ cap then cap else reserveCap cap 0 v.length
    HasFineGroupCredit.groupsScaled
        (M.stepEvents (bytesMergeEventsCore wt (BitVec.ofNat 64 cap) bs) st) +
        140011 * wireRemGrows maxLen cap' ≤
      HasFineGroupCredit.groupsScaled st + 2369 * (rem - rem') +
        140011 * wireRemGrows maxLen cap := by
  have htoNat : (BitVec.ofNat 64 cap).toNat = cap := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcap64]
  unfold bytesMergeEventsCore
  rw [hm, htoNat]
  by_cases hv0 : v.length = 0
  · simp only [hv0, Nat.zero_le, ↓reduceIte, AllocCostModel.stepEvents_nil]
    exact grp_idle_le _ _ _
  · have hv_pos : 0 < v.length := Nat.pos_of_ne_zero hv0
    have hv_max : v.length ≤ maxLen := by omega
    have hv_step : 2369 * (v.length + 1) ≤ 2369 * (rem - rem') :=
      Nat.mul_le_mul_left 2369 (by omega)
    simp only [hv0, ↓reduceIte, AllocCostModel.stepEvents_append]
    have hA := (phaseGroupSpec_rustAlloc_pos_2369 hGrp hv_pos (by decide : 1 ≤ 16)).groups_le st rfl
    set stA := M.stepEvents (rustAllocEvents v.length 1) st
    by_cases hv_le : v.length ≤ cap
    · simp only [hv_le, ↓reduceIte]
      have hB_nil : doReserveClearEvents cap v.length = [] := by
        unfold doReserveClearEvents; simp [hv_le]
      rw [hB_nil, AllocCostModel.stepEvents_nil]
      have hC := (PhaseGroupSpec.rustDealloc M v.length 1).groups_le stA rfl
      exact grp_fit_step hA hv_step hC
    · have hcap_lt_v : cap < v.length := Nat.lt_of_not_ge hv_le
      simp only [hv_le, ↓reduceIte]
      have hB := (phaseGroupSpec_doReserveClear_cap hGrp cap v.length).groups_le stA rfl
      set stB := M.stepEvents (doReserveClearEvents cap v.length) stA
      have hC := (PhaseGroupSpec.rustDealloc M v.length 1).groups_le stB rfl
      have hW_step := wireRemGrows_reserveCap_step hcap64 hcap_lt_v hv_max
      have hW_mul :
          140011 * wireRemGrows maxLen (reserveCap cap 0 v.length) + 140011 ≤
            140011 * wireRemGrows maxLen cap := by
        have hm1 := Nat.mul_le_mul_left 140011 hW_step
        rw [Nat.mul_add, Nat.mul_one] at hm1
        exact hm1
      exact grp_grow_step hA hv_step hB hC hW_mul

theorem phaseGroupSpec_intoBoxedSlice {M : AllocCostModel} [HasFineGroupCredit M]
    (hGrp : WireGroupHyps M) (bs : List (BitVec 8)) :
    PhaseGroupSpec M
      (fun evs => ∃ cap : BitVec 64, bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧
        evs = (if cap.toNat ≤ bs.length then []
               else if bs = [] then rustDeallocEvents cap.toNat 1
               else rustReallocEvents cap.toNat bs.length 1))
      140011 where
  groups_le st0 {evs} := by
    rintro ⟨cap, _, _, rfl⟩
    split
    · simp only [AllocCostModel.stepEvents_nil]
      exact Nat.le_add_right _ 140011
    · split
      · exact ((PhaseGroupSpec.rustDealloc M cap.toNat 1).mono (Nat.zero_le 140011)).groups_le
          st0 rfl
      · exact (phaseGroupSpec_rustRealloc_cap hGrp cap.toNat bs.length (by decide : 1 ≤ 16)).groups_le
          st0 rfl

theorem phaseGroupSpec_tryCloneBytes {M : AllocCostModel} [HasFineGroupCredit M]
    (hGrp : WireGroupHyps M) (bs : List (BitVec 8)) :
    PhaseGroupSpec M
      (fun evs => evs = if bs = [] then [] else rustAllocEvents bs.length 1)
      140011 where
  groups_le st0 {evs} := by
    rintro rfl
    split
    · simp only [AllocCostModel.stepEvents_nil]
      exact Nat.le_add_right _ 140011
    · exact (phaseGroupSpec_rustAlloc_cap hGrp bs.length (by decide : 1 ≤ 16)).groups_le st0 rfl

theorem phaseGroupSpec_optBytesAlloc {M : AllocCostModel} [HasFineGroupCredit M]
    (hGrp : WireGroupHyps M) (bs : List (BitVec 8)) :
    PhaseGroupSpec M
      (fun evs => evs = if bs.isEmpty then [] else rustAllocEvents bs.length 1)
      140011 where
  groups_le st0 {evs} := by
    rintro rfl
    split
    · simp only [AllocCostModel.stepEvents_nil]
      exact Nat.le_add_right _ 140011
    · exact (phaseGroupSpec_rustAlloc_cap hGrp bs.length (by decide : 1 ≤ 16)).groups_le st0 rfl

theorem phaseGroupSpec_optBytesDealloc (M : AllocCostModel) [HasFineGroupCredit M]
    (bs : List (BitVec 8)) :
    PhaseGroupSpec M
      (fun evs => evs = if bs.isEmpty then [] else rustDeallocEvents bs.length 1)
      0 where
  groups_le st0 {evs} := by
    rintro rfl
    split
    · simp only [AllocCostModel.stepEvents_nil, Nat.add_zero]
      exact Nat.le_refl _
    · exact (PhaseGroupSpec.rustDealloc M bs.length 1).groups_le st0 rfl

theorem phaseGroupSpec_bytesMergeZeroCap {M : AllocCostModel} [HasFineGroupCredit M]
    (hGrp : WireGroupHyps M) (wt : WireType) (bs : List (BitVec 8)) :
    PhaseGroupSpec M (· = bytesMergeEventsCore wt 0#64 bs) 280022 := by
  unfold bytesMergeEventsCore
  rcases hm : mergeBytes wt bs with _ | ⟨v, rest⟩
  · exact (phaseGroupSpec_rustAlloc_le108 hGrp (by decide : 72 ≤ 108) (by decide : 8 ≤ 16)).mono
      (by decide : 43464 ≤ 280022)
  · dsimp only
    by_cases hv0 : v.length = 0
    · simp only [hv0, ↓reduceIte]
      exact (PhaseGroupSpec.nil M).mono (Nat.zero_le 280022)
    · simp only [hv0, ↓reduceIte]
      have hCat :=
        ((phaseGroupSpec_rustAlloc_cap hGrp v.length (by decide : 1 ≤ 16)).concat
          (phaseGroupSpec_doReserveClear_cap hGrp (0#64).toNat v.length)).concat
          (PhaseGroupSpec.rustDealloc M v.length 1)
      refine (hCat.of_imp (fun _ hE => ?_)).mono (by decide : 140011 + 140011 + 0 ≤ 280022)
      rw [hE]
      exact ⟨_, _, rfl, ⟨_, _, rfl, rfl, rfl⟩, rfl⟩

end LibsignalBinary.Proofs.PeakBudget.WireTryFromHelpers
