/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.Cost.GroupTable

/-!
# Root `mmap` Length Summary and Usage-Indexed Bound

Arithmetic bridge from the symbolic-execution postconditions of the root `mmap` branch of
`alloc_group` (`RootLenOk`, `RootCntRel`) to the closed-form group-size table `rootBytesAt`
(`rootLen_le_rootBytesAt`).
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs.Cost

open Arm64 VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs

/-- Path-independent summary of the root `mmap` length chosen for final count `c`, with `x2` the
    usage register and `x5` the "bouncing" flag at the `cnt = 1` replacement check. -/
def RootLenOk (sc c len : Nat) (x2 x5 : BitVec 64) : Prop :=
  len ≤ pageAlignUp (slotStride sc + 16) ∨
  (len = pageAlignUp (c * slotStride sc + 16) ∧
    (c ≤ 7 → x5 = 0#64 → 16384 ≤ slotStride sc + 16 → (BitVec.ofNat 64 (2 * c)).ule x2 = true))

/-- Relation between the pre-reduction count `c'` and the count `c` that reaches `mmap_prep`:
    either is allowed for keep classes; for `sc ≥ 39` the `4 * c' ≤ usage` gate decides. -/
def RootCntRel (sc c' c : Nat) (x2 : BitVec 64) : Prop :=
  (c = c' ∨ c = reduceCnt sc c') ∧
  (38 < sc → c = if 4 * c' ≤ x2.toNat then c' else reduceCnt sc c')

theorem rootCntRel_keep {sc c' : Nat} {x2 : BitVec 64} (hge : 38 < sc → 4 * c' ≤ x2.toNat) :
    RootCntRel sc c' c' x2 :=
  ⟨Or.inl rfl, fun h => by simp only [hge h, ↓reduceIte]⟩

theorem rootCntRel_reduce {sc c' c : Nat} {x2 : BitVec 64} (hc : c = reduceCnt sc c')
    (hlt : 38 < sc → x2.toNat < 4 * c') : RootCntRel sc c' c x2 :=
  ⟨Or.inr hc, fun h => by
    have := hlt h; simp only [show ¬ 4 * c' ≤ x2.toNat by omega, ↓reduceIte]; exact hc⟩

private theorem pageAlignUp_mono' {a b : Nat} (h : a ≤ b) : pageAlignUp a ≤ pageAlignUp b := by
  unfold pageAlignUp PAGE_SIZE
  exact Nat.mul_le_mul_right _ (Nat.div_le_div_right (by omega))

theorem halveUsage_of_le : ∀ (f u c : Nat), 4 * c ≤ u → halveUsage f u c = c
  | 0, _, _, _ => rfl
  | f + 1, u, c, h => by
    simp only [halveUsage]; split
    · omega
    · rfl

private theorem cnt_tab_le_check :
    ((List.range 27).all fun k => (smallCntTabBytes.getD k 0#8).toNat ≤ 31) = true ∧
    ((List.range 4).all fun k => (medCntTabBytes.getD k 0#8).toNat ≤ 32) = true := by
  decide +kernel

private theorem smallCnt_le {sc i : Nat} (hsc : sc < 9) (hi : i < 3) : smallCnt sc i ≤ 31 := by
  have := List.all_eq_true.mp cnt_tab_le_check.1 (3 * sc + i) (List.mem_range.mpr (by omega))
  simpa [smallCnt] using this

private theorem medCnt_le (sc : Nat) : medCnt sc ≤ 32 := by
  have := List.all_eq_true.mp cnt_tab_le_check.2 (sc % 4) (List.mem_range.mpr (by omega))
  simpa [medCnt] using this

theorem cntRaw_sat (sc u : Nat) (hu : 128 ≤ u) : cntRaw sc u = cntRaw sc 128 := by
  unfold cntRaw
  by_cases h9 : sc < 9
  · have h0 := smallCnt_le (i := 0) h9 (by omega)
    simp only [h9, ↓reduceIte, show 4 * smallCnt sc 0 ≤ u by omega,
      show 4 * smallCnt sc 0 ≤ 128 by omega]
  · have hm := medCnt_le sc
    simp only [h9, ↓reduceIte]
    rw [halveUsage_of_le 8 u _ (by omega), halveUsage_of_le 8 128 _ (by omega)]

theorem cntSel_min (sc u : Nat) : cntSel sc u = cntSel sc (min u 128) := by
  by_cases hu : u ≤ 128
  · rw [Nat.min_eq_left hu]
  · rw [Nat.min_eq_right (by omega)]; unfold cntSel; rw [cntRaw_sat sc u (by omega)]

private theorem root_tab :
    ((List.range 48).all fun sc => (List.range 129).all fun v =>
      decide (1 ≤ cntSel sc v) && decide (cntSel sc v ≤ 32) &&
      (decide (cntSel sc v * slotStride sc + 16 ≤ 2048) ||
        (decide (1 ≤ reduceCnt sc (cntSel sc v)) && decide (reduceCnt sc (cntSel sc v) ≤ cntSel sc v) &&
          (decide (7 ≤ sc) || decide (sc % 2 = 0))))) = true := by
  decide +kernel

private theorem root_tab_at {sc u : Nat} (hsc : sc < 48) :
    1 ≤ cntSel sc u ∧ cntSel sc u ≤ 32 ∧
    (cntSel sc u * slotStride sc + 16 ≤ 2048 ∨
      (1 ≤ reduceCnt sc (cntSel sc u) ∧ reduceCnt sc (cntSel sc u) ≤ cntSel sc u ∧
        (7 ≤ sc ∨ sc % 2 = 0))) := by
  have h := List.all_eq_true.mp (List.all_eq_true.mp root_tab sc (List.mem_range.mpr hsc))
    (min u 128) (List.mem_range.mpr (by omega))
  rw [← cntSel_min] at h
  simpa only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, and_assoc] using h

theorem rootLen_le_rootBytesAt {sc u c' c len : Nat} {x2 x5 : BitVec 64}
    (hsc : sc < 48) (hc' : c' = cntSel sc u) (hroot : 2048 < c' * slotStride sc + 16)
    (hc : c = c' ∨ c = reduceCnt sc c')
    (h39 : 39 ≤ sc → x2.toNat = u ∧ x5 = 0#64 ∧ c = if 4 * c' ≤ u then c' else reduceCnt sc c')
    (hlen : RootLenOk sc c len x2 x5) :
    len ≤ rootBytesAt sc u := by
  obtain ⟨hc1, _, hrest⟩ := root_tab_at (u := u) hsc
  rw [← hc'] at hc1 hrest
  rcases hrest with hnest | ⟨hr1, hrle, hpar⟩
  · omega
  have hcle : c ≤ c' := by rcases hc with rfl | rfl <;> omega
  have hcge : 1 ≤ c := by rcases hc with rfl | rfl <;> omega
  have hmul : ∀ k, 1 ≤ k → slotStride sc ≤ slotStride sc * k := fun k hk => by
    have := Nat.mul_le_mul_left (slotStride sc) hk; rwa [Nat.mul_one] at this
  have hroot' : ¬ (slotStride sc * c' + 16 ≤ 2048) := by rw [Nat.mul_comm]; omega
  have hcs : c * slotStride sc ≤ slotStride sc * c' := by
    rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ hcle
  simp only [rootBytesAt, ← hc', hroot', ↓reduceIte]
  by_cases hkeep : (7 ≤ sc ∧ sc ≤ 38) ∨ (sc % 2 = 0 ∧ sc < 32)
  · simp only [hkeep, true_or, ↓reduceIte, not_true, false_and]
    rcases hlen with h1 | ⟨h2, _⟩
    · exact Nat.le_trans h1 (pageAlignUp_mono' (by have := hmul c' hc1; omega))
    · rw [h2]; exact pageAlignUp_mono' (by omega)
  · have hsc39 : 39 ≤ sc := by omega
    obtain ⟨hx2, hx5, hceq⟩ := h39 hsc39
    simp only [hkeep, false_or, not_false_eq_true, true_and]
    rw [← hceq]
    split
    · rename_i hrep
      rcases hlen with h1 | ⟨_, h2⟩
      · exact h1
      · have hule := h2 hrep.1 hx5 hrep.2.2
        rw [BitVec.ule, decide_eq_true_eq, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega)] at hule
        omega
    · rcases hlen with h1 | ⟨h2, _⟩
      · exact Nat.le_trans h1 (pageAlignUp_mono' (by have := hmul c hcge; omega))
      · rw [h2, Nat.mul_comm]; exact Nat.le_refl _

theorem rootLen_le_rootBytesAt' {sc u c' c len : Nat} {x2 x5 : BitVec 64}
    (hsc : sc < 48) (hc' : c' = cntSel sc u) (hroot : 2048 < c' * slotStride sc + 16)
    (hrel : RootCntRel sc c' c x2) (h39 : 38 < sc → x2.toNat = u ∧ x5 = 0#64)
    (hlen : RootLenOk sc c len x2 x5) : len ≤ rootBytesAt sc u :=
  rootLen_le_rootBytesAt hsc hc' hroot hrel.1
    (fun h => ⟨(h39 (by omega)).1, (h39 (by omega)).2, by rw [hrel.2 (by omega), (h39 (by omega)).1]⟩) hlen

end VerifiedLibraries.Mallocng.Proofs.Cost
