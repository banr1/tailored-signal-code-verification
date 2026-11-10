/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.SwissTable.Proofs.Control
public import ProofLib.SepLogic.Entry
import ProofLib.SepLogic.SymWP
import ProofLib.SepLogic.LoopTactics

/-!
# SwissTable 8-Byte Control Groups and Bucket-Mask Arithmetic

Defines 8-byte control-group words (`ctrlGroupWord`) and lane extraction (`getLane8`), proves
modular arithmetic properties of `ValidBucketMask`, and relates group lanes to `CtrlMirrorInv`
control bytes.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.SwissTable

open Arm64 ProofLib

/-! ## 8-Byte Control Group Words and `SepLoad64` -/

/-- Extract byte lane `j` (`0 ≤ j < 8`) from a 64-bit group word. -/
def getLane8 (w : BitVec 64) (j : Nat) : BitVec 8 :=
  w.extractLsb' (8 * j) 8

theorem getLane8_pack64 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) {j : Nat} (hj : j < 8) :
    getLane8 (pack64 b0 b1 b2 b3 b4 b5 b6 b7) j =
      [b0, b1, b2, b3, b4, b5, b6, b7][j]'(by simp; omega) := by
  match j with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 =>
    simp only [getLane8, pack64, List.getElem_cons_zero, List.getElem_cons_succ]
    bv_slice
  | n + 8 => omega

/-- 64-bit group word packed from the 8-byte control slice `ctrl[pos .. pos + 8)`
    (matching `SepLoad64.of_pointsToBytes` for `ldr d, [ctrlPtr, pos]`). -/
def ctrlGroupWord (ctrl : List (BitVec 8)) (pos : Nat) : BitVec 64 :=
  pack64 (ctrl.getD pos 0#8) (ctrl.getD (pos + 1) 0#8)
    (ctrl.getD (pos + 2) 0#8) (ctrl.getD (pos + 3) 0#8)
    (ctrl.getD (pos + 4) 0#8) (ctrl.getD (pos + 5) 0#8)
    (ctrl.getD (pos + 6) 0#8) (ctrl.getD (pos + 7) 0#8)

theorem getLane8_ctrlGroupWord (ctrl : List (BitVec 8)) (pos : Nat) {j : Nat} (hj : j < 8) :
    getLane8 (ctrlGroupWord ctrl pos) j = ctrl.getD (pos + j) 0#8 := by
  rw [ctrlGroupWord, getLane8_pack64 _ _ _ _ _ _ _ _ hj]
  match j with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => simp [Nat.add_zero]
  | n + 8 => omega

theorem getLane8_ctrlGroupWord_eq_getElem {ctrl : List (BitVec 8)} {pos j : Nat}
    (hpos : pos + 8 ≤ ctrl.length) (hj : j < 8) :
    getLane8 (ctrlGroupWord ctrl pos) j = ctrl[pos + j]'(by omega) := by
  rw [getLane8_ctrlGroupWord ctrl pos hj, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by omega)]
  rfl

theorem ctrlGroupAt_length {ctrl : List (BitVec 8)} {pos : Nat}
    (hpos : pos + 8 ≤ ctrl.length) :
    (ctrlGroupAt ctrl pos).length = 8 := by
  simp [ctrlGroupAt]
  omega

theorem ctrlGroupAt_getElem {ctrl : List (BitVec 8)} {pos j : Nat}
    (hpos : pos + 8 ≤ ctrl.length) (hj : j < 8) :
    (ctrlGroupAt ctrl pos)[j]'(by rw [ctrlGroupAt_length hpos]; exact hj) =
      ctrl[pos + j]'(by omega) := by
  simp [ctrlGroupAt]

theorem ctrlGroupAt_getElem? {ctrl : List (BitVec 8)} {pos j : Nat}
    (hpos : pos + 8 ≤ ctrl.length) (hj : j < 8) :
    (ctrlGroupAt ctrl pos)[j]? = some (getLane8 (ctrlGroupWord ctrl pos) j) := by
  rw [List.getElem?_eq_getElem (by rw [ctrlGroupAt_length hpos]; exact hj),
    ctrlGroupAt_getElem hpos hj, getLane8_ctrlGroupWord_eq_getElem hpos hj]

theorem mem_ctrlGroupAt_iff {ctrl : List (BitVec 8)} {pos : Nat}
    (hpos : pos + 8 ≤ ctrl.length) (b : BitVec 8) :
    b ∈ ctrlGroupAt ctrl pos ↔ ∃ j < 8, getLane8 (ctrlGroupWord ctrl pos) j = b := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨j, hj, hjb⟩
    have hj8 : j < 8 := by rw [ctrlGroupAt_length hpos] at hj; exact hj
    refine ⟨j, hj8, ?_⟩
    rw [getLane8_ctrlGroupWord_eq_getElem hpos hj8, ← ctrlGroupAt_getElem hpos hj8]
    exact hjb
  · rintro ⟨j, hj8, hjb⟩
    refine ⟨j, by rw [ctrlGroupAt_length hpos]; exact hj8, ?_⟩
    rw [ctrlGroupAt_getElem hpos hj8, ← getLane8_ctrlGroupWord_eq_getElem hpos hj8]
    exact hjb

theorem unpack64_ctrlGroupWord {ctrl : List (BitVec 8)} {pos : Nat}
    (hpos : pos + 8 ≤ ctrl.length) :
    unpack64 (ctrlGroupWord ctrl pos) = ctrlGroupAt ctrl pos := by
  apply List.ext_getElem
  · rw [unpack64_length, ctrlGroupAt_length hpos]
  · intro j hj1 hj2
    rw [unpack64_length] at hj1
    have hpack : unpack64 (ctrlGroupWord ctrl pos) =
        [ctrl.getD pos 0#8, ctrl.getD (pos + 1) 0#8, ctrl.getD (pos + 2) 0#8,
         ctrl.getD (pos + 3) 0#8, ctrl.getD (pos + 4) 0#8, ctrl.getD (pos + 5) 0#8,
         ctrl.getD (pos + 6) 0#8, ctrl.getD (pos + 7) 0#8] :=
      unpack64_pack64 ..
    simp only [hpack]
    rw [ctrlGroupAt_getElem hpos hj1, ← getLane8_ctrlGroupWord_eq_getElem hpos hj1,
      getLane8_ctrlGroupWord ctrl pos hj1]
    match j with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => simp [Nat.add_zero]
    | n + 8 => omega

@[simp]
theorem ctrlGroupWord_empty8 :
    ctrlGroupWord (List.replicate 8 tagEmpty) 0 = 0xffffffffffffffff#64 := by
  decide

theorem getLane8_allOnes {j : Nat} (hj : j < 8) :
    getLane8 0xffffffffffffffff#64 j = tagEmpty := by
  match j with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => decide
  | n + 8 => omega

theorem sepLoad64_ctrlGroupWord {ea ctrlPtr : BitVec 64} {ctrl : List (BitVec 8)} {pos : Nat}
    {P F : SepProp} (hP : P = (ctrlPtr ↦ₛ ctrl) ∗ F) (hpos : pos + 8 ≤ ctrl.length)
    (hea : ctrlPtr + BitVec.ofNat 64 pos = ea) :
    SepLoad64 ea P (ctrlGroupWord ctrl pos) :=
  SepLoad64.of_pointsToBytes hP hpos hea

theorem sepLoad64_ctrlGroupWord_here {ea ctrlPtr : BitVec 64} {ctrl : List (BitVec 8)} {pos : Nat}
    (hpos : pos + 8 ≤ ctrl.length) (hea : ctrlPtr + BitVec.ofNat 64 pos = ea) :
    SepLoad64 ea (ctrlPtr ↦ₛ ctrl) (ctrlGroupWord ctrl pos) :=
  SepLoad64.of_pointsToBytes (F := emp) (sepConj_emp _).symm hpos hea

/-! ## `ValidBucketMask` Modular Arithmetic -/

theorem ValidBucketMask.and_toNat_eq_mod {bm : BitVec 64} (hbm : ValidBucketMask bm)
    (x : BitVec 64) :
    (x &&& bm).toNat = x.toNat % (bm.toNat + 1) := by
  rcases hbm with ⟨exp, hlo, hhi, rfl⟩
  have hbuck := ValidBucketMask.buckets_eq hlo hhi rfl
  have hlo' : 2 ^ 2 ≤ 2 ^ exp := Nat.pow_le_pow_right (by omega) hlo
  have hhi' : 2 ^ exp ≤ 2 ^ 58 := Nat.pow_le_pow_right (by omega) hhi
  have h4 : 2 ^ 2 = 4 := by decide
  have h58 : 2 ^ 58 < 2 ^ 64 := by decide
  have hlt64 : 2 ^ exp - 1 < 2 ^ 64 := by omega
  rw [hbuck, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64,
    Nat.and_two_pow_sub_one_eq_mod]

theorem ValidBucketMask.and_lt_buckets {bm : BitVec 64} (hbm : ValidBucketMask bm)
    (x : BitVec 64) :
    (x &&& bm).toNat < bm.toNat + 1 := by
  rw [hbm.and_toNat_eq_mod x]
  exact Nat.mod_lt _ (by omega)

theorem ValidBucketMask.buckets_cases {bm : BitVec 64} (hbm : ValidBucketMask bm) :
    bm.toNat + 1 = 4 ∨ (8 ≤ bm.toNat + 1 ∧ (bm.toNat + 1) % 8 = 0) := by
  rcases hbm with ⟨exp, hlo, hhi, rfl⟩
  have hbuck := ValidBucketMask.buckets_eq hlo hhi rfl
  by_cases hexp : exp = 2
  · subst hexp; left; omega
  · right
    have hexp3 : 3 ≤ exp := by omega
    have hsplit : 2 ^ exp = 8 * 2 ^ (exp - 3) := by
      have h1 : exp = 3 + (exp - 3) := by omega
      conv => lhs; rw [h1, Nat.pow_add]
    rw [hbuck, hsplit]
    have hpos : 1 ≤ 2 ^ (exp - 3) := Nat.one_le_pow _ _ (by omega)
    exact ⟨by omega, by omega⟩

theorem ValidBucketMask.numGroups_pow2 {bm : BitVec 64} (hbm : ValidBucketMask bm) :
    ∃ gExp : Nat,
      numGroups bm = 2 ^ gExp ∧
      (bm.toNat + 1 = 4 → gExp = 0) ∧
      (8 ≤ bm.toNat + 1 → bm.toNat + 1 = 8 * 2 ^ gExp) := by
  rcases hbm with ⟨exp, hlo, hhi, rfl⟩
  have hbuck := ValidBucketMask.buckets_eq hlo hhi rfl
  by_cases hexp : exp = 2
  · subst hexp
    refine ⟨0, ?_, fun _ => rfl, fun h8 => by omega⟩
    rw [numGroups, hbuck]
    decide
  · have hexp3 : 3 ≤ exp := by omega
    refine ⟨exp - 3, ?_, ?_, ?_⟩
    · have hsplit : 2 ^ exp = 8 * 2 ^ (exp - 3) := by
        have h1 : exp = 3 + (exp - 3) := by omega
        conv => lhs; rw [h1, Nat.pow_add]
      have hpos : 1 ≤ 2 ^ (exp - 3) := Nat.one_le_pow _ _ (by omega)
      rw [numGroups, hbuck, hsplit]
      omega
    · intro h4
      have h8le : 2 ^ 3 ≤ 2 ^ exp := Nat.pow_le_pow_right (by omega) hexp3
      have h8eq : 2 ^ 3 = 8 := by decide
      omega
    · intro _
      have h1 : exp = 3 + (exp - 3) := by omega
      rw [hbuck]
      conv => lhs; rw [h1, Nat.pow_add]

theorem ValidBucketMask.buckets_bounds_dvd {bm : BitVec 64} (hbm : ValidBucketMask bm) :
    4 ≤ bm.toNat + 1 ∧ bm.toNat + 1 ≤ 2 ^ 58 ∧ (bm.toNat + 1) ∣ 2 ^ 64 := by
  rcases hbm with ⟨exp, hlo, hhi, rfl⟩
  rw [ValidBucketMask.buckets_eq hlo hhi rfl]
  refine ⟨Nat.pow_le_pow_right (by decide : 0 < 2) hlo,
    Nat.pow_le_pow_right (by decide : 0 < 2) hhi, ⟨2 ^ (64 - exp), ?_⟩⟩
  rw [← Nat.pow_add, show exp + (64 - exp) = 64 by omega]

theorem ValidBucketMask.add_and_eq {bm : BitVec 64} (hbm : ValidBucketMask bm)
    (x y : BitVec 64) : (((x &&& bm) + y) &&& bm) = ((x + y) &&& bm) := by
  rcases hbm.buckets_bounds_dvd with ⟨_, _, hdvd⟩
  apply BitVec.eq_of_toNat_eq
  rw [hbm.and_toNat_eq_mod, hbm.and_toNat_eq_mod, BitVec.toNat_add, BitVec.toNat_add,
    Nat.mod_mod_of_dvd _ hdvd, Nat.mod_mod_of_dvd _ hdvd, hbm.and_toNat_eq_mod, Nat.mod_add_mod]

theorem ValidBucketMask.laneIdx_bv {bm : BitVec 64} (hbm : ValidBucketMask bm)
    {pos j : Nat} (hpos : pos < bm.toNat + 1) (hj : j < 8) :
    ((BitVec.ofNat 64 pos + BitVec.ofNat 64 j) &&& bm) =
      BitVec.ofNat 64 ((pos + j) % (bm.toNat + 1)) := by
  rcases hbm.buckets_bounds_dvd with ⟨hb4, hb58, _⟩
  have h58 : 2 ^ 58 + 8 < 2 ^ 64 := by decide
  have hlt1 : pos + j < 2 ^ 64 := by omega
  have hlt2 : (pos + j) % (bm.toNat + 1) < 2 ^ 64 :=
    Nat.lt_trans (Nat.mod_lt _ (by omega)) (by omega)
  apply BitVec.eq_of_toNat_eq
  rw [← BitVec.ofNat_add, hbm.and_toNat_eq_mod, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2]

/-! ## `CtrlMirrorInv` Lane Bridges -/

theorem CtrlMirrorInv.lane_eq_mod_of_ge8 {buckets : Nat} {ctrl : List (BitVec 8)}
    (hm : CtrlMirrorInv buckets ctrl) (hb : 8 ≤ buckets) {pos j : Nat}
    (hpos : pos < buckets) (hj : j < 8) :
    getLane8 (ctrlGroupWord ctrl pos) j =
      ctrl[(pos + j) % buckets]'(by
        have hlen : ctrl.length = buckets + 8 := hm.1
        have hmod := Nat.mod_lt (pos + j) (by omega : 0 < buckets)
        omega) := by
  have hlen : ctrl.length = buckets + 8 := hm.1
  rw [getLane8_ctrlGroupWord_eq_getElem (by omega) hj]
  by_cases hlt : pos + j < buckets
  · have hmod : (pos + j) % buckets = pos + j := Nat.mod_eq_of_lt hlt
    simp [hmod]
  · have hge : buckets ≤ pos + j := by omega
    have hrem_lt8 : pos + j - buckets < 8 := by omega
    have hrem_ltb : pos + j - buckets < buckets := by omega
    have hmod : (pos + j) % buckets = pos + j - buckets := by
      calc (pos + j) % buckets
          = ((pos + j - buckets) + buckets) % buckets := by congr 1; omega
        _ = pos + j - buckets := by rw [Nat.add_mod_right, Nat.mod_eq_of_lt hrem_ltb]
    have hmir := hm.2.2.2 hb (pos + j - buckets) hrem_lt8
    have h1 : buckets + (pos + j - buckets) = pos + j := by omega
    rw [h1, List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at hmir
    injection hmir with hmir'
    simpa [hmod] using hmir'

theorem CtrlMirrorInv.lane_of_eq4 {ctrl : List (BitVec 8)}
    (hm : CtrlMirrorInv 4 ctrl) {pos j : Nat} (hpos : pos < 4) (hj : j < 8) :
    getLane8 (ctrlGroupWord ctrl pos) j =
      if pos + j < 4 then ctrl[pos + j]'(by have hlen : ctrl.length = 4 + 8 := hm.1; omega)
      else if pos + j < 8 then tagEmpty
      else ctrl[(pos + j) % 4]'(by have hlen : ctrl.length = 4 + 8 := hm.1; omega) := by
  have hlen : ctrl.length = 4 + 8 := hm.1
  rw [getLane8_ctrlGroupWord_eq_getElem (by omega) hj]
  rcases hm.2.2.1 rfl with ⟨hpad, hmir⟩
  split
  · rfl
  · rename_i hge4
    split
    · rename_i hlt8
      have hpad' := hpad (pos + j - 4) (by omega)
      have heq : 4 + (pos + j - 4) = pos + j := by omega
      rw [heq, List.getElem?_eq_getElem (by omega)] at hpad'
      injection hpad'
    · rename_i hge8
      have hr : pos + j - 8 < 4 := by omega
      have hmod : (pos + j) % 4 = pos + j - 8 := by omega
      have hmir' := hmir (pos + j - 8) hr
      have heq : 8 + (pos + j - 8) = pos + j := by omega
      rw [heq, List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at hmir'
      injection hmir' with hmir''
      simpa [hmod] using hmir''

theorem CtrlMirrorInv.lane_full_eq_mod {bm : BitVec 64} {ctrl : List (BitVec 8)}
    (hbm : ValidBucketMask bm) (hm : CtrlMirrorInv (bm.toNat + 1) ctrl) {pos j : Nat}
    (hpos : pos < bm.toNat + 1) (hj : j < 8)
    (hfull : isFullTag (getLane8 (ctrlGroupWord ctrl pos) j) = true) :
    getLane8 (ctrlGroupWord ctrl pos) j =
      ctrl[(pos + j) % (bm.toNat + 1)]'(by
        have hlen : ctrl.length = (bm.toNat + 1) + 8 := hm.1
        have hmod := Nat.mod_lt (pos + j) (by omega : 0 < bm.toNat + 1)
        omega) := by
  rcases hbm.buckets_cases with h4 | ⟨h8, _⟩
  · have hm4 : CtrlMirrorInv 4 ctrl := h4 ▸ hm
    have hlane := CtrlMirrorInv.lane_of_eq4 hm4 (pos := pos) (j := j) (by omega) hj
    by_cases hlt4 : pos + j < 4
    · have hmod : (pos + j) % (bm.toNat + 1) = pos + j := Nat.mod_eq_of_lt (by omega)
      simp [hlane, hlt4, hmod]
    · by_cases hlt8 : pos + j < 8
      · simp only [hlane, hlt4, ↓reduceIte, hlt8, isFullTag_tagEmpty] at hfull
        cases hfull
      · simp [hlane, hlt4, hlt8, h4]
  · exact CtrlMirrorInv.lane_eq_mod_of_ge8 hm h8 hpos hj

theorem CtrlMirrorInv.empty_in_group_of_eq4 {ctrl : List (BitVec 8)}
    (hm : CtrlMirrorInv 4 ctrl) {pos : Nat} (hpos : pos < 4) :
    tagEmpty ∈ ctrlGroupAt ctrl pos := by
  have hlen := hm.1
  rw [mem_ctrlGroupAt_iff (by omega)]
  refine ⟨4 - pos, by omega, ?_⟩
  have hlane := CtrlMirrorInv.lane_of_eq4 hm hpos (j := 4 - pos) (by omega)
  have h1 : ¬ (pos + (4 - pos) < 4) := by omega
  have h2 : pos + (4 - pos) < 8 := by omega
  simp [hlane, h1, h2]

end VerifiedLibraries.SwissTable
