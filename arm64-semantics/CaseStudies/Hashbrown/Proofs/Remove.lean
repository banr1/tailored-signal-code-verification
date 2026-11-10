/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import CaseStudies.Hashbrown.Proofs.Lookup
import ProofLib.SepLogic.WPFrozen
import ProofLib.SepLogic.Entry
import ProofLib.SepLogic.SymWP
import ProofLib.SepLogic.LoopTactics
import ProofLib.BV.ReflectROBDD

/-!
# SwissTable Removal

Placement-generic (`HbPlaced`) machine-code proof for `hashbrown_remove`. Establishes `CtrlMirrorInv`
preservation under `setCtrl`, proves that writing `tagEmpty` when `tz + lz <= 7` preserves
`ProbeReachable` for remaining keys, and discharges `SwissTableInv` across removal.
-/

set_option autoImplicit false

@[expose] public section

namespace CaseStudies.Hashbrown.Proofs

open Arm64 ProofLib ProofLib.StdStartup

/-! ## Pure Mirror and Erase Lemmas -/

private theorem write8_eq_set (bs : List (BitVec 8)) {off : Nat} (v : BitVec 8)
    (hoff : off < bs.length) : ByteSlice.write8 bs off v = bs.set off v := by
  apply List.ext_getElem
  · rw [ByteSlice.write8_length bs off v (by omega), List.length_set]
  · intro i hi1 hi2
    have hd1 : (ByteSlice.write8 bs off v)[i]'hi1 = (ByteSlice.write8 bs off v).getD i 0#8 := by
      simp [List.getD, List.getElem?_eq_getElem hi1]
    have hd2 : bs[i]'(by simpa using hi2) = bs.getD i 0#8 := by
      simp [List.getD, List.getElem?_eq_getElem (by simpa using hi2)]
    rw [hd1, ByteSlice.getD_write8 bs off v i 0#8 (by omega), List.getElem_set]
    by_cases heq : off = i
    · subst heq; simp
    · simp [heq, show i ≠ off from fun h => heq h.symm, hd2]

private def removeIdxBefore (bm : BitVec 64) (idx : Nat) : Nat :=
  ((BitVec.ofNat 64 idx - 8#64) &&& bm).toNat

private def setCtrl (bm : BitVec 64) (ctrl : List (BitVec 8)) (idx : Nat) (tag : BitVec 8) :
    List (BitVec 8) :=
  (ctrl.set idx tag).set (setCtrlMirrorIdx bm idx) tag

private theorem removeIdxBefore_bv (bm : BitVec 64) (idx : Nat) :
    (BitVec.ofNat 64 idx - 8#64) &&& bm = BitVec.ofNat 64 (removeIdxBefore bm idx) := by
  apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; unfold removeIdxBefore
  exact (Nat.mod_eq_of_lt ((BitVec.ofNat 64 idx - 8#64) &&& bm).isLt).symm

private theorem removeIdxBefore_lt {bm : BitVec 64} (hbm : ValidBucketMask bm) (idx : Nat) :
    removeIdxBefore bm idx < bm.toNat + 1 := hbm.and_lt_buckets _

private theorem setCtrlMirrorIdx_eq_add8 {bm : BitVec 64} (hbm : ValidBucketMask bm) (idx : Nat) :
    setCtrlMirrorIdx bm idx = removeIdxBefore bm idx + 8 := by
  have hlt := removeIdxBefore_lt hbm idx; rcases hbm.buckets_bounds_dvd with ⟨_, hb58, _⟩
  have h58 : 2 ^ 58 < 2 ^ 64 := by decide
  unfold setCtrlMirrorIdx
  rw [removeIdxBefore_bv, ← BitVec.ofNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

private theorem setCtrlMirrorIdx_lt {bm : BitVec 64} (hbm : ValidBucketMask bm) (idx : Nat) :
    setCtrlMirrorIdx bm idx < (bm.toNat + 1) + 8 := by
  have := removeIdxBefore_lt hbm idx; have := setCtrlMirrorIdx_eq_add8 hbm idx; omega

private theorem removeIdxBefore_eq_of_eq4 {bm : BitVec 64} (_hbm : ValidBucketMask bm)
    (h4 : bm.toNat + 1 = 4) {idx : Nat} (hidx : idx < 4) : removeIdxBefore bm idx = idx := by
  have hbm3 : bm = 3#64 := BitVec.eq_of_toNat_eq (by change bm.toNat = 3; omega)
  subst hbm3; unfold removeIdxBefore; match idx with | 0 | 1 | 2 | 3 => decide | n + 4 => omega

private theorem removeIdxBefore_eq_of_ge8 {bm : BitVec 64} (hbm : ValidBucketMask bm)
    (h8 : 8 ≤ bm.toNat + 1) {idx : Nat} (hidx : idx < bm.toNat + 1) :
    removeIdxBefore bm idx = if idx < 8 then (bm.toNat + 1) + idx - 8 else idx - 8 := by
  unfold removeIdxBefore; rw [hbm.and_toNat_eq_mod]; rcases hbm with ⟨exp, hlo, hhi, hbm_eq⟩
  have hbuck : bm.toNat + 1 = 2 ^ exp := ValidBucketMask.buckets_eq hlo hhi hbm_eq
  have hb_lt64 : bm.toNat + 1 < 2 ^ 64 := by
    have : 2 ^ 58 < 2 ^ 64 := by decide
    have := Nat.pow_le_pow_right (by omega : 0 < 2) hhi; omega
  have hidx_bv : (BitVec.ofNat 64 idx).toNat = idx := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have h8_bv : (8#64).toNat = 8 := by decide
  by_cases hlt8 : idx < 8
  · simp only [hlt8, ↓reduceIte]
    have hsub : (BitVec.ofNat 64 idx - 8#64).toNat = 2 ^ 64 - 8 + idx := by
      rw [BitVec.toNat_sub, h8_bv, hidx_bv, Nat.mod_eq_of_lt (by omega)]
    have hpow64 : 2 ^ 64 = (bm.toNat + 1) * 2 ^ (64 - exp) := by
      rw [hbuck, ← Nat.pow_add, show exp + (64 - exp) = 64 by omega]
    have hge1 : 1 ≤ 2 ^ (64 - exp) := Nat.one_le_pow _ _ (by omega)
    have hdecomp : 2 ^ 64 - 8 + idx =
        ((bm.toNat + 1) + idx - 8) + (bm.toNat + 1) * (2 ^ (64 - exp) - 1) := by
      have hm : (bm.toNat + 1) * 2 ^ (64 - exp) =
          (bm.toNat + 1) * ((2 ^ (64 - exp) - 1) + 1) := by congr 1; omega
      rw [Nat.mul_add, Nat.mul_one] at hm; omega
    rw [hsub, hdecomp, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  · simp only [hlt8, ↓reduceIte]
    have hsub : (BitVec.ofNat 64 idx - 8#64).toNat = idx - 8 := by
      rw [BitVec.toNat_sub, h8_bv, hidx_bv, show 2 ^ 64 - 8 + idx = 2 ^ 64 + (idx - 8) by omega,
        Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    rw [hsub, Nat.mod_eq_of_lt (by omega)]

private theorem setCtrlMirrorIdx_cases {bm : BitVec 64} (hbm : ValidBucketMask bm)
    {idx : Nat} (hidx : idx < bm.toNat + 1) :
    setCtrlMirrorIdx bm idx = idx ∨ bm.toNat + 1 ≤ setCtrlMirrorIdx bm idx := by
  rw [setCtrlMirrorIdx_eq_add8 hbm idx]; rcases hbm.buckets_cases with h4 | ⟨h8, _⟩
  · rw [removeIdxBefore_eq_of_eq4 hbm h4 (by omega)]; right; omega
  · rw [removeIdxBefore_eq_of_ge8 hbm h8 hidx]
    by_cases hlt8 : idx < 8 <;> simp only [hlt8, ↓reduceIte] <;> omega

private theorem setCtrl_length (bm : BitVec 64) (ctrl : List (BitVec 8)) (idx : Nat)
    (tag : BitVec 8) : (setCtrl bm ctrl idx tag).length = ctrl.length := by simp [setCtrl]

private theorem setCtrl_getElem? (bm : BitVec 64) (ctrl : List (BitVec 8))
    (idx : Nat) (tag : BitVec 8) {i : Nat} (hi : i < ctrl.length) :
    (setCtrl bm ctrl idx tag)[i]? =
      if setCtrlMirrorIdx bm idx = i then some tag
      else if idx = i then some tag else ctrl[i]? := by
  unfold setCtrl; rw [List.getElem?_set, List.getElem?_set]
  by_cases h1 : setCtrlMirrorIdx bm idx = i
  · subst h1; simp [hi]
  · by_cases h2 : idx = i
    · subst h2; simp [h1, hi]
    · simp [h1, h2]

private theorem setCtrl_getElem_lt {bm : BitVec 64} (hbm : ValidBucketMask bm)
    {ctrl : List (BitVec 8)} (hlen : ctrl.length = (bm.toNat + 1) + 8)
    {idx : Nat} (hidx : idx < bm.toNat + 1) (tag : BitVec 8) {i : Nat} (hi : i < bm.toNat + 1) :
    (setCtrl bm ctrl idx tag)[i]'(by rw [setCtrl_length]; omega) =
      if i = idx then tag else ctrl[i]'(by omega) := by
  apply Option.some.inj
  rw [← List.getElem?_eq_getElem, setCtrl_getElem? bm ctrl idx tag (by omega),
      List.getElem?_eq_getElem (by omega)]
  rcases setCtrlMirrorIdx_cases hbm hidx with hm_eq | hm_ge
  · rw [hm_eq]; by_cases h : idx = i
    · subst h; simp
    · simp [h, show i ≠ idx from fun e => h e.symm]
  · simp only [show setCtrlMirrorIdx bm idx ≠ i by omega, ↓reduceIte]; by_cases h : idx = i
    · subst h; simp
    · simp [h, show i ≠ idx from fun e => h e.symm]

private theorem setCtrl_take_buckets {bm : BitVec 64} (hbm : ValidBucketMask bm)
    {ctrl : List (BitVec 8)} (hlen : ctrl.length = (bm.toNat + 1) + 8)
    {idx : Nat} (hidx : idx < bm.toNat + 1) (tag : BitVec 8) :
    (setCtrl bm ctrl idx tag).take (bm.toNat + 1) = (ctrl.take (bm.toNat + 1)).set idx tag := by
  apply List.ext_getElem
  · simp [setCtrl_length, hlen]
  · intro i hi1 hi2
    have hi_b : i < bm.toNat + 1 := by simp [setCtrl_length, hlen] at hi1; omega
    rw [List.getElem_take, setCtrl_getElem_lt hbm hlen hidx tag hi_b, List.getElem_set]
    by_cases h : idx = i
    · subst h; simp
    · simp [h, show i ≠ idx from fun e => h e.symm, List.getElem_take]

private theorem mem_set_imp {α : Type} {l : List α} {k : Nat} {v x : α}
    (hx : x ∈ l.set k v) : x = v ∨ x ∈ l := by
  rcases List.mem_iff_getElem.1 hx with ⟨i, hi, rfl⟩; rw [List.getElem_set]
  by_cases h : k = i <;> simp [h, List.getElem_mem]

private theorem CtrlMirrorInv.setCtrl_pres {bm : BitVec 64} (hbm : ValidBucketMask bm)
    {ctrl : List (BitVec 8)} (hm : CtrlMirrorInv (bm.toNat + 1) ctrl)
    {idx : Nat} (hidx : idx < bm.toNat + 1) {tag : BitVec 8} (htag : ValidTag tag) :
    CtrlMirrorInv (bm.toNat + 1) (setCtrl bm ctrl idx tag) := by
  have hlen := hm.1
  refine ⟨by rw [setCtrl_length, hlen], ?_, ?_, ?_⟩
  · intro b hb; rcases mem_set_imp hb with rfl | hb1
    · exact htag
    · exact (mem_set_imp hb1).elim (· ▸ htag) (hm.2.1 b)
  · intro h4
    have hm_idx : setCtrlMirrorIdx bm idx = idx + 8 := by
      rw [setCtrlMirrorIdx_eq_add8 hbm idx, removeIdxBefore_eq_of_eq4 hbm h4 (by omega)]
    rcases hm.2.2.1 h4 with ⟨hpad, hmir4⟩; refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · rw [setCtrl_getElem? bm ctrl idx tag (by omega), hm_idx]
      simp [show idx + 8 ≠ 4 + j by omega, show idx ≠ 4 + j by omega, hpad j hj]
    · rw [setCtrl_getElem? bm ctrl idx tag (by omega),
          setCtrl_getElem? bm ctrl idx tag (by omega), hm_idx]
      by_cases hji : j = idx
      · subst hji; simp [show j + 8 = 8 + j by omega]
      · simp [show idx + 8 ≠ 8 + j by omega, show idx ≠ 8 + j by omega,
          show idx + 8 ≠ j by omega, show idx ≠ j from fun e => hji e.symm, hmir4 j hj]
  · intro h8 j hj
    have hm_idx : setCtrlMirrorIdx bm idx = if idx < 8 then (bm.toNat + 1) + idx else idx := by
      rw [setCtrlMirrorIdx_eq_add8 hbm idx, removeIdxBefore_eq_of_ge8 hbm h8 hidx]; split <;> omega
    rw [setCtrl_getElem? bm ctrl idx tag (by omega),
        setCtrl_getElem? bm ctrl idx tag (by omega), hm_idx]
    by_cases hlt8 : idx < 8 <;> simp only [hlt8, ↓reduceIte]
    · by_cases hji : j = idx
      · subst hji; simp only [show (bm.toNat + 1) + j ≠ j by omega, ↓reduceIte]
      · simp only [show (bm.toNat + 1) + idx ≠ (bm.toNat + 1) + j by omega,
          show idx ≠ (bm.toNat + 1) + j by omega, show (bm.toNat + 1) + idx ≠ j by omega,
          show idx ≠ j from fun e => hji e.symm, ↓reduceIte, hm.2.2.2 h8 j hj]
    · simp [show idx ≠ (bm.toNat + 1) + j by omega, show idx ≠ j by omega, hm.2.2.2 h8 j hj]

private theorem setCtrl_lane_of_mod_ne {bm : BitVec 64} (hbm : ValidBucketMask bm)
    {ctrl : List (BitVec 8)} (hm : CtrlMirrorInv (bm.toNat + 1) ctrl)
    {idx : Nat} (hidx : idx < bm.toNat + 1) {tag : BitVec 8} (htag : ValidTag tag)
    {pos l : Nat} (hpos : pos < bm.toNat + 1) (hl : l < 8)
    (hne : (pos + l) % (bm.toNat + 1) ≠ idx) :
    getLane8 (ctrlGroupWord (setCtrl bm ctrl idx tag) pos) l =
      getLane8 (ctrlGroupWord ctrl pos) l := by
  have hm' := CtrlMirrorInv.setCtrl_pres hbm hm hidx htag; rcases hbm.buckets_cases with h4 | ⟨h8, _⟩
  · have hm4 : CtrlMirrorInv 4 ctrl := h4 ▸ hm
    have hm4' : CtrlMirrorInv 4 (setCtrl bm ctrl idx tag) := h4 ▸ hm'
    rw [CtrlMirrorInv.lane_of_eq4 hm4' (by omega) hl, CtrlMirrorInv.lane_of_eq4 hm4 (by omega) hl]
    split
    · rename_i hlt4; rw [setCtrl_getElem_lt hbm hm.1 hidx tag (by omega)]
      simp [show pos + l ≠ idx from fun heq => hne (by rw [h4, Nat.mod_eq_of_lt hlt4, heq])]
    · split; · rfl
      · rw [setCtrl_getElem_lt hbm hm.1 hidx tag
          (by have := Nat.mod_lt (pos + l) (by decide : 0 < 4); omega)]
        simp [show (pos + l) % 4 ≠ idx by rwa [h4] at hne]
  · rw [CtrlMirrorInv.lane_eq_mod_of_ge8 hm' h8 hpos hl,
        CtrlMirrorInv.lane_eq_mod_of_ge8 hm h8 hpos hl,
        setCtrl_getElem_lt hbm hm.1 hidx tag (Nat.mod_lt _ (by omega))]; simp [hne]

private theorem setCtrl_lane_cases {bm : BitVec 64} (hbm : ValidBucketMask bm)
    {ctrl : List (BitVec 8)} (hm : CtrlMirrorInv (bm.toNat + 1) ctrl)
    {idx : Nat} (hidx : idx < bm.toNat + 1) {tag : BitVec 8} (htag : ValidTag tag)
    {pos l : Nat} (hpos : pos < bm.toNat + 1) (hl : l < 8) :
    getLane8 (ctrlGroupWord (setCtrl bm ctrl idx tag) pos) l =
      getLane8 (ctrlGroupWord ctrl pos) l ∨
    ((pos + l) % (bm.toNat + 1) = idx ∧
     getLane8 (ctrlGroupWord (setCtrl bm ctrl idx tag) pos) l = tag) := by
  by_cases hmod : (pos + l) % (bm.toNat + 1) = idx
  · have hm' := CtrlMirrorInv.setCtrl_pres hbm hm hidx htag; rcases hbm.buckets_cases with h4 | ⟨h8, _⟩
    · have hm4 : CtrlMirrorInv 4 ctrl := h4 ▸ hm
      have hm4' : CtrlMirrorInv 4 (setCtrl bm ctrl idx tag) := h4 ▸ hm'
      rw [CtrlMirrorInv.lane_of_eq4 hm4' (by omega) hl, CtrlMirrorInv.lane_of_eq4 hm4 (by omega) hl]
      split
      · rename_i hlt4; right; refine ⟨hmod, ?_⟩
        rw [setCtrl_getElem_lt hbm hm.1 hidx tag (by omega)]
        simp [show pos + l = idx by rw [← hmod, h4, Nat.mod_eq_of_lt hlt4]]
      · split; · left; rfl
        · right; refine ⟨hmod, ?_⟩
          rw [setCtrl_getElem_lt hbm hm.1 hidx tag
            (by have := Nat.mod_lt (pos + l) (by decide : 0 < 4); omega)]
          simp [show (pos + l) % 4 = idx by rwa [← h4]]
    · right; refine ⟨hmod, ?_⟩
      rw [CtrlMirrorInv.lane_eq_mod_of_ge8 hm' h8 hpos hl,
          setCtrl_getElem_lt hbm hm.1 hidx tag (Nat.mod_lt _ (by omega))]; simp [hmod]
  · exact Or.inl (setCtrl_lane_of_mod_ne hbm hm hidx htag hpos hl hmod)

private theorem not_mem_empty_of_window_le7 {bm : BitVec 64} (hbm : ValidBucketMask bm)
    {ctrl : List (BitVec 8)} (hm : CtrlMirrorInv (bm.toNat + 1) ctrl)
    {idx : Nat} (hidx : idx < bm.toNat + 1)
    (hle7 : (eqBits8 (ctrlGroupWord ctrl idx) tagEmpty).ctz.toNat +
            (eqBits8 (ctrlGroupWord ctrl (removeIdxBefore bm idx)) tagEmpty).clz.toNat ≤ 7)
    {pos : Nat} (hpos : pos < bm.toNat + 1) (hno_emp : tagEmpty ∉ ctrlGroupAt ctrl pos) :
    tagEmpty ∉ ctrlGroupAt (setCtrl bm ctrl idx tagEmpty) pos := by
  have hm' := CtrlMirrorInv.setCtrl_pres hbm hm hidx ValidTag.empty
  have hlen := hm.1; have hlen' := hm'.1; intro hemp'
  rcases (mem_ctrlGroupAt_iff (by omega) tagEmpty).1 hemp' with ⟨r, hr8, hlane'⟩
  have hno_lane : ∀ w < 8, getLane8 (ctrlGroupWord ctrl pos) w ≠ tagEmpty := fun w hw hlw =>
    hno_emp ((mem_ctrlGroupAt_iff (by omega) tagEmpty).2 ⟨w, hw, hlw⟩)
  rcases setCtrl_lane_cases hbm hm hidx ValidTag.empty hpos hr8 with hsame | ⟨hmod_idx, _⟩
  · exact hno_lane r hr8 (hsame ▸ hlane')
  · rcases hbm.buckets_cases with h4 | ⟨h8, _⟩
    · exact hno_emp (CtrlMirrorInv.empty_in_group_of_eq4 (h4 ▸ hm) (by omega))
    · let b_after := eqBits8 (ctrlGroupWord ctrl idx) tagEmpty
      let b_before := eqBits8 (ctrlGroupWord ctrl (removeIdxBefore bm idx)) tagEmpty
      have htz_ge : 8 - r ≤ b_after.ctz.toNat := by
        apply Classical.byContradiction; intro hlt
        have htz8 : b_after.ctz.toNat < 8 := by omega
        have hba_nz : b_after ≠ 0#8 := by rintro h0; rw [h0] at htz8; exact absurd htz8 (by decide)
        rcases bv8_ctz_spec hba_nz with ⟨_, hbit_tz, _⟩
        rw [getLsbD_eqBits8 _ _ htz8, beq_iff_eq,
            CtrlMirrorInv.lane_eq_mod_of_ge8 hm h8 hidx htz8] at hbit_tz
        have hmod_eq : (idx + b_after.ctz.toNat) % (bm.toNat + 1) =
            (pos + (r + b_after.ctz.toNat)) % (bm.toNat + 1) := by
          rw [← hmod_idx, Nat.mod_add_mod, Nat.add_assoc]
        have hrtz8 : r + b_after.ctz.toNat < 8 := by omega
        simp only [hmod_eq] at hbit_tz
        exact hno_lane _ hrtz8 ((CtrlMirrorInv.lane_eq_mod_of_ge8 hm h8 hpos hrtz8).trans hbit_tz)
      have hlz_ge : r ≤ b_before.clz.toNat := by
        apply Classical.byContradiction; intro hlt
        have hlz8 : b_before.clz.toNat < 8 := by omega
        have hbb_nz : b_before ≠ 0#8 := fun h0 => by have := (bv8_clz_spec b_before).1 h0; omega
        rcases (bv8_clz_spec b_before).2 hbb_nz with ⟨_, hbit_lz, _⟩
        let u := 7 - b_before.clz.toNat
        have hu8 : u < 8 := by omega
        have hru_lt8 : r + u - 8 < 8 := by omega
        rw [getLsbD_eqBits8 _ _ hu8, beq_iff_eq,
            CtrlMirrorInv.lane_eq_mod_of_ge8 hm h8 (removeIdxBefore_lt hbm idx) hu8] at hbit_lz
        have hib_mod : removeIdxBefore bm idx = ((bm.toNat + 1 - 8) + idx) % (bm.toNat + 1) := by
          rw [removeIdxBefore_eq_of_ge8 hbm h8 hidx]
          by_cases hlt8 : idx < 8 <;> simp only [hlt8, ↓reduceIte]
          · rw [show (bm.toNat + 1 - 8) + idx = (bm.toNat + 1) + idx - 8 by omega,
              Nat.mod_eq_of_lt (by omega)]
          · rw [show (bm.toNat + 1 - 8) + idx = (bm.toNat + 1) + (idx - 8) by omega,
              Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
        have hmod_eq : (removeIdxBefore bm idx + u) % (bm.toNat + 1) =
            (pos + (r + u - 8)) % (bm.toNat + 1) := by
          rw [hib_mod, Nat.mod_add_mod, ← hmod_idx]
          calc ((bm.toNat + 1 - 8) + (pos + r) % (bm.toNat + 1) + u) % (bm.toNat + 1)
              = (((pos + r) % (bm.toNat + 1)) + ((bm.toNat + 1 - 8) + u)) % (bm.toNat + 1) := by
                congr 1; omega
            _ = ((pos + r) + ((bm.toNat + 1 - 8) + u)) % (bm.toNat + 1) := Nat.mod_add_mod ..
            _ = ((bm.toNat + 1) + (pos + (r + u - 8))) % (bm.toNat + 1) := by congr 1; omega
            _ = (pos + (r + u - 8)) % (bm.toNat + 1) := Nat.add_mod_left ..
        simp only [hmod_eq] at hbit_lz
        exact hno_lane _ hru_lt8
          ((CtrlMirrorInv.lane_eq_mod_of_ge8 hm h8 hpos hru_lt8).trans hbit_lz)
      dsimp only [b_after, b_before] at htz_ge hlz_ge; omega

private theorem ProbeReachable.of_setCtrl_deleted {bm : BitVec 64} (hbm : ValidBucketMask bm)
    {ctrl : List (BitVec 8)} (hm : CtrlMirrorInv (bm.toNat + 1) ctrl)
    {idx j : Nat} (hidx : idx < bm.toNat + 1) (hne : j ≠ idx) {k' : BitVec 64}
    (hreach : ProbeReachable bm ctrl k' j) :
    ProbeReachable bm (setCtrl bm ctrl idx tagDeleted) k' j := by
  have hm' := CtrlMirrorInv.setCtrl_pres hbm hm hidx ValidTag.deleted
  rcases hreach with ⟨step, lane, hstep, hlane, hgrp, hmod_j, hno_emp⟩
  refine ⟨step, lane, hstep, hlane, ?_, hmod_j, ?_⟩
  · have hpos_lt := probePos_lt_buckets hbm k' step
    rw [ctrlGroupAt_getElem? (by have := hm'.1; omega) hlane]
    rw [ctrlGroupAt_getElem? (by have := hm.1; omega) hlane] at hgrp
    rwa [setCtrl_lane_of_mod_ne hbm hm hidx ValidTag.deleted hpos_lt hlane (hmod_j ▸ hne)]
  · intro s' hs' hemp'; have hpos_lt := probePos_lt_buckets hbm k' s'
    rcases (mem_ctrlGroupAt_iff (by have := hm'.1; omega) tagEmpty).1 hemp' with ⟨r, hr8, hlr⟩
    rcases setCtrl_lane_cases hbm hm hidx ValidTag.deleted hpos_lt hr8 with hsame | ⟨_, hdel⟩
    · exact hno_emp s' hs'
        ((mem_ctrlGroupAt_iff (by have := hm.1; omega) tagEmpty).2 ⟨r, hr8, hsame ▸ hlr⟩)
    · rw [hlr] at hdel; exact absurd hdel (by decide)

private theorem ProbeReachable.of_setCtrl_empty {bm : BitVec 64} (hbm : ValidBucketMask bm)
    {ctrl : List (BitVec 8)} (hm : CtrlMirrorInv (bm.toNat + 1) ctrl)
    {idx j : Nat} (hidx : idx < bm.toNat + 1) (hne : j ≠ idx)
    (hle7 : (eqBits8 (ctrlGroupWord ctrl idx) tagEmpty).ctz.toNat +
            (eqBits8 (ctrlGroupWord ctrl (removeIdxBefore bm idx)) tagEmpty).clz.toNat ≤ 7)
    {k' : BitVec 64} (hreach : ProbeReachable bm ctrl k' j) :
    ProbeReachable bm (setCtrl bm ctrl idx tagEmpty) k' j := by
  have hm' := CtrlMirrorInv.setCtrl_pres hbm hm hidx ValidTag.empty
  rcases hreach with ⟨step, lane, hstep, hlane, hgrp, hmod_j, hno_emp⟩
  refine ⟨step, lane, hstep, hlane, ?_, hmod_j, fun s' hs' => not_mem_empty_of_window_le7 hbm hm
    hidx hle7 (probePos_lt_buckets hbm k' s') (hno_emp s' hs')⟩
  have hpos_lt := probePos_lt_buckets hbm k' step
  rw [ctrlGroupAt_getElem? (by have := hm'.1; omega) hlane]
  rw [ctrlGroupAt_getElem? (by have := hm.1; omega) hlane] at hgrp
  rwa [setCtrl_lane_of_mod_ne hbm hm hidx ValidTag.empty hpos_lt hlane (hmod_j ▸ hne)]

private theorem countP_set_eq (p : BitVec 8 → Bool) :
    ∀ (l : List (BitVec 8)) (idx : Nat) (hidx : idx < l.length) (v : BitVec 8),
      (l.set idx v).countP p + (if p (l[idx]'hidx) then 1 else 0) =
        l.countP p + (if p v then 1 else 0)
  | _ :: _, 0, _, _ => by
    simp only [List.set_cons_zero, List.getElem_cons_zero, List.countP_cons]; split <;> split <;> omega
  | _ :: xs, i + 1, hi, v => by
    have ih := countP_set_eq p xs i (by simpa using hi) v
    simp only [List.set_cons_succ, List.getElem_cons_succ, List.countP_cons] at ih ⊢; omega

private theorem SwissTableInv.erase_tag {bm gl gl' items : BitVec 64}
    {ctrl : List (BitVec 8)} {slots : List (BitVec 64 × BitVec 64)} {m : Map64}
    (hinv : SwissTableInv bm gl items ctrl slots m) {k : BitVec 64} {idx : Nat} {tag : BitVec 8}
    (hidx : idx < bm.toNat + 1) (htag : ValidTag tag) (hnf : isFullTag tag = false)
    (hfull_idx : isFullTag (ctrl[idx]'(by have := hinv.mirror.1; omega)) = true)
    (hkey_idx : (slots[idx]'(by have := hinv.slots_len; omega)).1 = k)
    (hgl' : gl'.toNat ≤ bucketMaskToCapacity bm)
    (hdel_bal : gl'.toNat + (if tag == tagDeleted then 1 else 0) = gl.toNat + 1)
    (hreach : ∀ i ≠ idx, ∀ k', ProbeReachable bm ctrl k' i →
      ProbeReachable bm (setCtrl bm ctrl idx tag) k' i) :
    SwissTableInv bm gl' (items - 1#64) (setCtrl bm ctrl idx tag) slots (cliMapErase k m) := by
  have hlen := hinv.mirror.1; have hsl := hinv.slots_len
  have hlook_k : cliMapLookup k m = some (slots[idx]'(by omega)).2 := by
    have hs := (hinv.full_sound idx hidx hfull_idx).2.1; rwa [hkey_idx] at hs
  have helen := cliMapErase_length_of_lookup_some hinv.wf hlook_k
  have hidx_t : idx < (ctrl.take (bm.toNat + 1)).length := by simp [hlen]; omega
  have ht_elem : (ctrl.take (bm.toNat + 1))[idx]'hidx_t = ctrl[idx]'(by omega) := List.getElem_take
  have hnot_del_old : ((ctrl[idx]'(by omega)) == tagDeleted) = false := by
    rw [(hinv.full_sound idx hidx hfull_idx).1]; exact beq_eq_false_iff_ne.2 (h2Tag_ne_deleted _)
  have hc_del := countP_set_eq (· == tagDeleted) (ctrl.take (bm.toNat + 1)) idx hidx_t tag
  have hc_full := countP_set_eq isFullTag (ctrl.take (bm.toNat + 1)) idx hidx_t tag
  rw [ht_elem, hnot_del_old] at hc_del; rw [ht_elem, hfull_idx, hnf] at hc_full
  refine
    { validMask := hinv.validMask, wf := hinv.wf.erase k, slots_len := hsl, growth_le := hgl',
      mirror := CtrlMirrorInv.setCtrl_pres hinv.validMask hinv.mirror hidx htag,
      items_eq := by
        rw [hinv.items_eq, ← helen, BitVec.ofNat_add]
        change (BitVec.ofNat 64 (cliMapErase k m).length + 1#64) - 1#64 = _; bv_lin,
      conservation := by
        rw [setCtrl_take_buckets hinv.validMask hlen hidx tag]; have := hinv.conservation
        simp only [Bool.false_eq_true, ↓reduceIte] at hc_del; omega,
      countFull_eq := by
        rw [setCtrl_take_buckets hinv.validMask hlen hidx tag]; have := hinv.countFull_eq
        simp only [↓reduceIte, Bool.false_eq_true] at hc_full; omega,
      full_sound := fun i hi hfull_i => by
        rw [setCtrl_getElem_lt hinv.validMask hlen hidx tag hi] at hfull_i ⊢
        have hne : i ≠ idx := by rintro rfl; simp [hnf] at hfull_i
        simp only [hne, ↓reduceIte] at hfull_i ⊢
        have hkey_ne : (slots[i]'(by omega)).1 ≠ k := fun heq =>
          hne (hinv.full_inj i idx hi hidx hfull_i hfull_idx (heq.trans hkey_idx.symm))
        rcases hinv.full_sound i hi hfull_i with ⟨ht1, hlk1, hr1⟩
        exact ⟨ht1, (cliMapLookup_erase_ne hkey_ne m).trans hlk1, hreach i hne _ hr1⟩,
      full_inj := fun i j hi hj hfi hfj hkeq => by
        rw [setCtrl_getElem_lt hinv.validMask hlen hidx tag hi] at hfi
        rw [setCtrl_getElem_lt hinv.validMask hlen hidx tag hj] at hfj
        have hnei : i ≠ idx := by rintro rfl; simp [hnf] at hfi
        have hnej : j ≠ idx := by rintro rfl; simp [hnf] at hfj
        simp only [hnei, hnej, ↓reduceIte] at hfi hfj; exact hinv.full_inj i j hi hj hfi hfj hkeq,
      complete := fun k' v' hlk' => by
        have hk'_ne : k' ≠ k := by rintro rfl; rw [cliMapLookup_erase_self] at hlk'; cases hlk'
        rw [cliMapLookup_erase_ne hk'_ne] at hlk'
        rcases hinv.complete k' v' hlk' with ⟨i, hi, hfi, hs_i⟩
        have hnei : i ≠ idx := by rintro rfl; exact hk'_ne ((congrArg Prod.fst hs_i).symm.trans hkey_idx)
        refine ⟨i, hi, ?_, hs_i⟩; rw [setCtrl_getElem_lt hinv.validMask hlen hidx tag hi]
        simp [hnei, hfi] }

private theorem SwissTableInv.erase_deleted {bm gl items : BitVec 64}
    {ctrl : List (BitVec 8)} {slots : List (BitVec 64 × BitVec 64)} {m : Map64}
    (hinv : SwissTableInv bm gl items ctrl slots m) {k : BitVec 64} {idx : Nat}
    (hidx : idx < bm.toNat + 1)
    (hfull_idx : isFullTag (ctrl[idx]'(by have := hinv.mirror.1; omega)) = true)
    (hkey_idx : (slots[idx]'(by have := hinv.slots_len; omega)).1 = k) :
    SwissTableInv bm gl (items - 1#64) (setCtrl bm ctrl idx tagDeleted) slots (cliMapErase k m) :=
  hinv.erase_tag hidx ValidTag.deleted isFullTag_tagDeleted hfull_idx hkey_idx hinv.growth_le rfl
    fun _ hne _ hr => hr.of_setCtrl_deleted hinv.validMask hinv.mirror hidx hne

private theorem SwissTableInv.erase_empty {bm gl items : BitVec 64}
    {ctrl : List (BitVec 8)} {slots : List (BitVec 64 × BitVec 64)} {m : Map64}
    (hinv : SwissTableInv bm gl items ctrl slots m) {k : BitVec 64} {idx : Nat}
    (hidx : idx < bm.toNat + 1)
    (hfull_idx : isFullTag (ctrl[idx]'(by have := hinv.mirror.1; omega)) = true)
    (hkey_idx : (slots[idx]'(by have := hinv.slots_len; omega)).1 = k)
    (hle7 : (eqBits8 (ctrlGroupWord ctrl idx) tagEmpty).ctz.toNat +
            (eqBits8 (ctrlGroupWord ctrl (removeIdxBefore bm idx)) tagEmpty).clz.toNat ≤ 7) :
    SwissTableInv bm (gl + 1#64) (items - 1#64) (setCtrl bm ctrl idx tagEmpty) slots
      (cliMapErase k m) := by
  have hcons := hinv.conservation
  have hlook_k : cliMapLookup k m = some (slots[idx]'(by have := hinv.slots_len; omega)).2 := by
    have hs := (hinv.full_sound idx hidx hfull_idx).2.1; rwa [hkey_idx] at hs
  have helen := cliMapErase_length_of_lookup_some hinv.wf hlook_k
  have hgl_add : (gl + 1#64).toNat = gl.toNat + 1 := by
    have := (hinv.validMask.capacity_bounds).2; have : 7 * 2 ^ 55 < 2 ^ 64 := by decide
    rw [BitVec.toNat_add, BitVec.toNat_ofNat,
      show (1 : Nat) % 2 ^ 64 = 1 from Nat.mod_eq_of_lt (by decide), Nat.mod_eq_of_lt (by omega)]
  exact hinv.erase_tag hidx ValidTag.empty isFullTag_tagEmpty hfull_idx hkey_idx
    (by rw [hgl_add]; omega) (by rw [hgl_add]; rfl)
    fun _ hne _ hr => hr.of_setCtrl_empty hinv.validMask hinv.mirror hidx hne hle7

/-! ## Machine-Code Proof of `hashbrown_remove` -/

private theorem hbRodata_focus_emptyCtrl (pl : Obj.Placement) :
    hbRodata pl = ((pl.ρ hbEmptyCtrlSym) ↦₆₄ᵣ 0xffffffffffffffff#64) ∗
      pointsToBytesRO (pl.ρ hbEmptyMapSym)
        (Obj.bytesLE 8 (pl.ρ hbEmptyCtrlSym) ++ List.replicate 24 0#8) := by
  unfold hbRodata
  have h8 : List.replicate 8 0xff#8 = [0xff#8, 0xff#8, 0xff#8, 0xff#8, 0xff#8, 0xff#8, 0xff#8, 0xff#8] := rfl
  rw [h8, pointsToBytesRO8_eq_pointsTo64RO]; rfl

private theorem eqBits8_allOnes_h2Tag (k : BitVec 64) : eqBits8 0xffffffffffffffff#64 (h2Tag k) = 0#8 :=
  (bv8_eq_zero_iff_forall _).2 fun j hj => by
    rw [getLsbD_eqBits8 _ _ hj, getLane8_allOnes hj, beq_eq_false_iff_ne]; exact (h2Tag_ne_empty k).symm

private def RwFrame (s0 st : State) : Prop :=
  st.sp = s0.sp ∧ st.readReg64 .lr = s0.readReg64 .lr ∧
  CalleeSavedPreserved s0 st ∧ StdStartup.StdStatePreserved s0 st

private def RoFrame (s0 st : State) : Prop := RwFrame s0 st ∧ st.mem = s0.mem

@[local simp] private theorem rwFrame_rfl (s0 : State) : RwFrame s0 s0 :=
  ⟨Eq.refl _, Eq.refl _, CalleeSavedPreserved.rfl s0, StdStartup.StdStatePreserved.rfl s0⟩
@[local simp] private theorem rwFrame_setPC (s0 s : State) (pc : BitVec 64) :
    RwFrame s0 (s.setPC pc) ↔ RwFrame s0 s := by simp [RwFrame, StdStartup.StdStatePreserved]
@[local simp] private theorem rwFrame_advancePC (s0 s : State) :
    RwFrame s0 s.advancePC ↔ RwFrame s0 s := by simp [RwFrame, StdStartup.StdStatePreserved]
@[local simp] private theorem rwFrame_setPState (s0 s : State) (ps : PState) :
    RwFrame s0 (s.setPState ps) ↔ RwFrame s0 s := by simp [RwFrame, StdStartup.StdStatePreserved]
@[local simp] private theorem rwFrame_writeReg64 (s0 s : State) (idx : BitVec 5) (val : BitVec 64)
    (hcs : isCalleeSavedReg (.gpr idx) = false := by decide) (hlr : idx ≠ 30#5 := by decide) :
    RwFrame s0 (s.writeReg64 (.gpr idx) val) ↔ RwFrame s0 s := by
  simp [RwFrame, StdStartup.StdStatePreserved, hcs, show Reg.lr ≠ Reg.gpr idx by rintro ⟨⟩; exact hlr rfl]
@[local simp] private theorem rwFrame_writeReg32 (s0 s : State) (idx : BitVec 5) (val : BitVec 32)
    (hcs : isCalleeSavedReg (.gpr idx) = false := by decide) (hlr : idx ≠ 30#5 := by decide) :
    RwFrame s0 (s.writeReg32 (.gpr idx) val) ↔ RwFrame s0 s :=
  rwFrame_writeReg64 s0 s idx (val.zeroExtend 64) hcs hlr
@[local simp] private theorem rwFrame_writeVReg128 (s0 s : State) (v : BitVec 5) (val : BitVec 128)
    (hcs : isCalleeSavedVReg v = false := by decide) :
    RwFrame s0 (s.writeVReg128 v val) ↔ RwFrame s0 s := by
  simp [RwFrame, StdStartup.StdStatePreserved, CalleeSavedPreserved_writeVReg128 s0 s v val hcs]
@[local simp] private theorem rwFrame_writeVReg64 (s0 s : State) (v : BitVec 5) (val : BitVec 64)
    (hcs : isCalleeSavedVReg v = false := by decide) :
    RwFrame s0 (s.writeVReg64 v val) ↔ RwFrame s0 s := rwFrame_writeVReg128 s0 s v (val.zeroExtend 128) hcs
@[local simp] private theorem rwFrame_writeVReg32 (s0 s : State) (v : BitVec 5) (val : BitVec 32)
    (hcs : isCalleeSavedVReg v = false := by decide) :
    RwFrame s0 (s.writeVReg32 v val) ↔ RwFrame s0 s := rwFrame_writeVReg128 s0 s v (val.zeroExtend 128) hcs

private theorem RwFrame.setMem_perm {s0 s : State} {m' : Memory}
    (h : RwFrame s0 s) (hm : m'.perm = s.mem.perm) : RwFrame s0 (s.setMem m') := by
  rcases h with ⟨hsp, hlr, hcs, h1, h2, h3, h4, h5, h6, h7, hp⟩
  exact ⟨hsp, hlr, hcs, h1, h2, h3, h4, h5, h6, h7, fun a => (congrFun hm a).trans (hp a)⟩

@[local simp] private theorem roFrame_rfl (s0 : State) : RoFrame s0 s0 := ⟨rwFrame_rfl s0, rfl⟩
@[local simp] private theorem roFrame_setPC (s0 s : State) (pc : BitVec 64) :
    RoFrame s0 (s.setPC pc) ↔ RoFrame s0 s := by simp [RoFrame]
@[local simp] private theorem roFrame_advancePC (s0 s : State) :
    RoFrame s0 s.advancePC ↔ RoFrame s0 s := by simp [RoFrame]
@[local simp] private theorem roFrame_setPState (s0 s : State) (ps : PState) :
    RoFrame s0 (s.setPState ps) ↔ RoFrame s0 s := by simp [RoFrame]
@[local simp] private theorem roFrame_writeReg64 (s0 s : State) (idx : BitVec 5) (val : BitVec 64)
    (hcs : isCalleeSavedReg (.gpr idx) = false := by decide) (hlr : idx ≠ 30#5 := by decide) :
    RoFrame s0 (s.writeReg64 (.gpr idx) val) ↔ RoFrame s0 s := by
  simp [RoFrame, rwFrame_writeReg64 s0 s idx val hcs hlr]
@[local simp] private theorem roFrame_writeReg32 (s0 s : State) (idx : BitVec 5) (val : BitVec 32)
    (hcs : isCalleeSavedReg (.gpr idx) = false := by decide) (hlr : idx ≠ 30#5 := by decide) :
    RoFrame s0 (s.writeReg32 (.gpr idx) val) ↔ RoFrame s0 s :=
  roFrame_writeReg64 s0 s idx (val.zeroExtend 64) hcs hlr
@[local simp] private theorem roFrame_writeVReg128 (s0 s : State) (v : BitVec 5) (val : BitVec 128)
    (hcs : isCalleeSavedVReg v = false := by decide) :
    RoFrame s0 (s.writeVReg128 v val) ↔ RoFrame s0 s := by simp [RoFrame, rwFrame_writeVReg128 s0 s v val hcs]
@[local simp] private theorem roFrame_writeVReg64 (s0 s : State) (v : BitVec 5) (val : BitVec 64)
    (hcs : isCalleeSavedVReg v = false := by decide) :
    RoFrame s0 (s.writeVReg64 v val) ↔ RoFrame s0 s := roFrame_writeVReg128 s0 s v (val.zeroExtend 128) hcs
@[local simp] private theorem roFrame_writeVReg32 (s0 s : State) (v : BitVec 5) (val : BitVec 32)
    (hcs : isCalleeSavedVReg v = false := by decide) :
    RoFrame s0 (s.writeVReg32 v val) ↔ RoFrame s0 s := roFrame_writeVReg128 s0 s v (val.zeroExtend 128) hcs

local macro "ro_simp0" : tactic => `(tactic| simp (config := { decide := true }) only [
    roFrame_setPC, roFrame_advancePC, roFrame_setPState, roFrame_writeReg64, roFrame_writeReg32,
    roFrame_writeVReg128, roFrame_writeVReg64, roFrame_writeVReg32, roFrame_rfl])
local macro "ro_simp" h:term : tactic => `(tactic| simp (config := { decide := true }) only [
    roFrame_setPC, roFrame_advancePC, roFrame_setPState, roFrame_writeReg64, roFrame_writeReg32,
    roFrame_writeVReg128, roFrame_writeVReg64, roFrame_writeVReg32, roFrame_rfl, $h:term])

private theorem setPC_setMem (s : State) (pc : BitVec 64) (m : Memory) : (s.setPC pc).setMem m = (s.setMem m).setPC pc := rfl
private theorem advancePC_setMem (s : State) (m : Memory) : s.advancePC.setMem m = (s.setMem m).advancePC := rfl
private theorem setPState_setMem (s : State) (ps : PState) (m : Memory) : (s.setPState ps).setMem m = (s.setMem m).setPState ps := rfl
private theorem writeReg64_setMem (s : State) (r : Reg) (v : BitVec 64) (m : Memory) : (s.writeReg64 r v).setMem m = (s.setMem m).writeReg64 r v := rfl
private theorem writeReg32_setMem (s : State) (r : Reg) (v : BitVec 32) (m : Memory) : (s.writeReg32 r v).setMem m = (s.setMem m).writeReg32 r v := rfl
private theorem writeVReg128_setMem (s : State) (v : BitVec 5) (val : BitVec 128) (m : Memory) : (s.writeVReg128 v val).setMem m = (s.setMem m).writeVReg128 v val := rfl
private theorem writeVReg64_setMem (s : State) (v : BitVec 5) (val : BitVec 64) (m : Memory) : (s.writeVReg64 v val).setMem m = (s.setMem m).writeVReg64 v val := rfl
private theorem writeVReg32_setMem (s : State) (v : BitVec 5) (val : BitVec 32) (m : Memory) : (s.writeVReg32 v val).setMem m = (s.setMem m).writeVReg32 v val := rfl
private theorem setMem_setMem (s : State) (m1 m2 : Memory) : (s.setMem m1).setMem m2 = s.setMem m2 := rfl

local macro "rw_simp" h:ident : tactic => `(tactic| (
    try simp (config := { decide := true }) only [setPC_setMem, advancePC_setMem, setPState_setMem,
      setMem_setMem, writeReg64_setMem, writeReg32_setMem, writeVReg128_setMem, writeVReg64_setMem,
      writeVReg32_setMem, rwFrame_setPC, rwFrame_advancePC, rwFrame_setPState, rwFrame_writeReg64,
      rwFrame_writeReg32, rwFrame_writeVReg128, rwFrame_writeVReg64, rwFrame_writeVReg32, rwFrame_rfl] at $h:ident ⊢
    exact $h:ident))

private theorem close_ro_miss {P_rep R P_f : SepProp} {s0 sf : State} {φ : Prop}
    (hpre : s0.mem ⊨ P_rep ∗ R) (hro : RoFrame s0 sf) (hφ : φ) :
    (sf.mem ⊨ P_f ∗ R →
      sf.mem ⊨ (⌜φ ∧ StdStartup.StdStatePreserved s0 sf ∧ s0.mem.KeepsFrozen sf.mem⌝ ∗ P_rep) ∗ R) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf := by
  refine ⟨fun _ => ?_, hro.1.1, hro.1.2.2.1⟩; rw [hro.2, sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨hφ, hro.1.2.2.2, hro.2 ▸ Memory.KeepsFrozen.refl s0.mem⟩, hpre⟩

private theorem close_rw_post {P_rep R P_f : SepProp} {s0 sf : State} {φ : Prop}
    (hrw : RwFrame s0 sf) (hkf : s0.mem.KeepsFrozen sf.mem) (hφ : φ) (hrep : P_f ⊢ P_rep) :
    (sf.mem ⊨ P_f ∗ R →
      sf.mem ⊨ (⌜φ ∧ StdStartup.StdStatePreserved s0 sf ∧ s0.mem.KeepsFrozen sf.mem⌝ ∗ P_rep) ∗ R) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf := by
  refine ⟨fun hmf => ?_, hrw.1, hrw.2.2.1⟩; rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨hφ, hrw.2.2.2, hkf⟩, Satisfies.mono (sepConj_mono_left hrep) hmf⟩

private theorem step_str64_perm {prog : Program} {target_pc pc pc' ea val : BitVec 64}
    {s0 s : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {rt : Reg} {addr : AddrMode} (hrw : RwFrame s0 s) (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.str .X64 rt addr)) (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, none)) (hval : s.readReg64 rt = val)
    (hstore : SepStore64 ea val P P') (hpc' : pc + 4#64 = pc' := by bv_lin)
    (hnext : ∀ m' : Memory, RwFrame s0 ((s.setPC pc').setMem m') →
      SepWP prog target_pc ((s.setPC pc').setMem m') P' post oom) :
    SepWP prog target_pc s P post oom := by
  subst hpc'; apply SepWP.of_reaches_pc; intro R hm; let m' := s.mem.write64 ea val
  have hm' := hstore.store hm; have hcan := hstore.writable hm
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.str .X64 rt addr) s = (s.setPC (pc + 4#64)).setMem m' := by
    simp [Program.evalInst, execInstWithSvc, execStr, Memory.writeSized, State.advancePC,
      State.setPC, State.setMem, hsp, haddr, hval, hcan, MemWidth.bytes, hpc, m']
  rw [hstep]; exact SepWP.to_reaches_pc
    (hnext m' (RwFrame.setMem_perm ((rwFrame_setPC s0 s _).2 hrw) (Memory.perm_write64 s.mem ea val))) hm'

private theorem step_str8_perm {prog : Program} {target_pc pc pc' ea : BitVec 64} {val : BitVec 8}
    {s0 s : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {rt : Reg} {addr : AddrMode} (hrw : RwFrame s0 s) (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.str .B8 rt addr)) (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, none)) (hval : (s.readReg64 rt).truncate 8 = val)
    (hstore : SepStore8 ea val P P') (hpc' : pc + 4#64 = pc' := by bv_lin)
    (hnext : ∀ m' : Memory, RwFrame s0 ((s.setPC pc').setMem m') →
      SepWP prog target_pc ((s.setPC pc').setMem m') P' post oom) :
    SepWP prog target_pc s P post oom := by
  subst hpc'; apply SepWP.of_reaches_pc; intro R hm; let m' := s.mem.write8 ea val
  have hm' := hstore.store hm; have hcan := hstore.writable hm
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.str .B8 rt addr) s = (s.setPC (pc + 4#64)).setMem m' := by
    simp [Program.evalInst, execInstWithSvc, execStr, Memory.writeSized, State.advancePC,
      State.setPC, State.setMem, hsp, haddr, hval, hcan, MemWidth.bytes, hpc, m']
  rw [hstep]; exact SepWP.to_reaches_pc
    (hnext m' (RwFrame.setMem_perm ((rwFrame_setPC s0 s _).2 hrw) (Memory.perm_write8 s.mem ea val))) hm'

private theorem extend_probe_prev {ctrl : List (BitVec 8)} {slots : List (BitVec 64 × BitVec 64)}
    {bm k : BitVec 64} {step : Nat}
    (hprev : ∀ s < step, ∀ j < 8, getLane8 (ctrlGroupWord ctrl (probePos bm k s)) j = h2Tag k →
      (h : (probePos bm k s + j) % (bm.toNat + 1) < slots.length) →
      (slots[(probePos bm k s + j) % (bm.toNat + 1)]'h).1 ≠ k)
    (hno_h2 : ∀ j < 8, getLane8 (ctrlGroupWord ctrl (probePos bm k step)) j = h2Tag k →
      (h : (probePos bm k step + j) % (bm.toNat + 1) < slots.length) →
      (slots[(probePos bm k step + j) % (bm.toNat + 1)]'h).1 ≠ k) :
    ∀ s < step + 1, ∀ j < 8, getLane8 (ctrlGroupWord ctrl (probePos bm k s)) j = h2Tag k →
      (h : (probePos bm k s + j) % (bm.toNat + 1) < slots.length) →
      (slots[(probePos bm k s + j) % (bm.toNat + 1)]'h).1 ≠ k := fun s hs j hj htag hsl =>
  if hlt : s < step then hprev s hlt j hj htag hsl
  else (show s = step by omega) ▸ hno_h2 j hj ((show s = step by omega) ▸ htag)
    ((show s = step by omega) ▸ hsl)

private theorem probe_empty_miss_lookup {bm growthLeft items : BitVec 64}
    {ctrl : List (BitVec 8)} {slots : List (BitVec 64 × BitVec 64)} {map : Map64}
    (hinv : SwissTableInv bm growthLeft items ctrl slots map) {k : BitVec 64} {step : Nat}
    (hemp_ne : eqBits8 (ctrlGroupWord ctrl (probePos bm k step)) tagEmpty ≠ 0#8)
    (hprev : ∀ s < step, ∀ j < 8, getLane8 (ctrlGroupWord ctrl (probePos bm k s)) j = h2Tag k →
      (h : (probePos bm k s + j) % (bm.toNat + 1) < slots.length) →
      (slots[(probePos bm k s + j) % (bm.toNat + 1)]'h).1 ≠ k)
    (hno_h2 : ∀ j < 8, getLane8 (ctrlGroupWord ctrl (probePos bm k step)) j = h2Tag k →
      (h : (probePos bm k step + j) % (bm.toNat + 1) < slots.length) →
      (slots[(probePos bm k step + j) % (bm.toNat + 1)]'h).1 ≠ k) :
    cliMapLookup k map = none := by
  rcases (bv8_ne_zero_iff_exists _).1 hemp_ne with ⟨je, hje, hbit_e⟩
  rw [getLsbD_eqBits8 _ tagEmpty hje, beq_iff_eq] at hbit_e
  have := probePos_lt_buckets hinv.validMask k step; have := hinv.mirror.1
  exact hinv.lookup_eq_none_of_probe_empty
    ((mem_ctrlGroupAt_iff (by omega) tagEmpty).2 ⟨je, hje, hbit_e⟩) fun s hs j hj htag =>
      extend_probe_prev hprev hno_h2 s (by omega) j hj htag _

private theorem probe_nonempty_lt_end {bm growthLeft items : BitVec 64}
    {ctrl : List (BitVec 8)} {slots : List (BitVec 64 × BitVec 64)} {map : Map64}
    (hinv : SwissTableInv bm growthLeft items ctrl slots map) {k : BitVec 64}
    {step step_end : Nat} (hstep_le : step ≤ step_end)
    (hemp_end : tagEmpty ∈ ctrlGroupAt ctrl (probePos bm k step_end))
    (hemp_eq : eqBits8 (ctrlGroupWord ctrl (probePos bm k step)) tagEmpty = 0#8) :
    step < step_end := by
  apply Classical.byContradiction; intro hge; obtain rfl : step = step_end := by omega
  have := probePos_lt_buckets hinv.validMask k step; have := hinv.mirror.1
  rcases (mem_ctrlGroupAt_iff (by omega) tagEmpty).1 hemp_end with ⟨je, hje, hlane_e⟩
  have hbit_e := (bv8_eq_zero_iff_forall _).1 hemp_eq je hje
  rw [getLsbD_eqBits8 _ _ hje, beq_eq_false_iff_ne] at hbit_e; exact hbit_e hlane_e

private theorem clear_lowest_miss {g bm k : BitVec 64} {slots : List (BitVec 64 × BitVec 64)}
    {pos : Nat} {b : BitVec 8} {hidx : (pos + b.ctz.toNat) % (bm.toNat + 1) < slots.length}
    (hk_ne : (slots[(pos + b.ctz.toNat) % (bm.toNat + 1)]'hidx).1 ≠ k)
    (hmiss_b : ∀ j < 8, getLane8 g j = h2Tag k → b.getLsbD j = false →
      (h : (pos + j) % (bm.toNat + 1) < slots.length) →
      (slots[(pos + j) % (bm.toNat + 1)]'h).1 ≠ k) :
    ∀ j < 8, getLane8 g j = h2Tag k → ((b - 1#8) &&& b).getLsbD j = false →
      (h : (pos + j) % (bm.toNat + 1) < slots.length) →
      (slots[(pos + j) % (bm.toNat + 1)]'h).1 ≠ k := by
  intro j hj htag hbf' hsl; rw [bv8_getLsbD_clear_lowest b hj] at hbf'
  by_cases hbj : b.getLsbD j = true
  · rw [hbj, Bool.true_and, decide_eq_false_iff_not, Classical.not_not] at hbf'; subst hbf'; exact hk_ne
  · exact hmiss_b j hj htag (Bool.eq_false_iff.2 hbj) hsl

private def RemovePost (P : HbPlaced) (A : HbAlloc) (s0 : State)
    (mapPtr bm k : BitVec 64) (map : Map64) (u : Nat) (R : SepProp) (sf : State) (P_f : SepProp) : Prop :=
  (sf.mem ⊨ P_f ∗ R →
    sf.mem ⊨ (⌜(match cliMapLookup k map with
      | none => sf.readReg64 .x0 = 0#64
      | some v => sf.readReg64 .x0 = 1#64 ∧ sf.readReg64 .x1 = v) ∧
      StdStartup.StdStatePreserved s0 sf ∧ s0.mem.KeepsFrozen sf.mem⌝ ∗
      U64MapRep P.pl A mapPtr (cliMapErase k map) bm u) ∗ R) ∧
  sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

private theorem hbRemove_finish_wp (P : HbPlaced) (A : HbAlloc) (X : String → Option (State → State))
    {s0 sf0 : State} {mapPtr bm k gl' : BitVec 64} {map : Map64} {u : Nat} {R : SepProp}
    {w : HbHeapMapWitness} {idx : Nat} {newTag : BitVec 8}
    (hmap_al : mapPtr.toNat % 8 = 0) (hmap_nw : mapPtr.toNat + 32 ≤ 2 ^ 64)
    (hbm0 : bm ≠ 0#64) (hidx_b : idx < bm.toNat + 1) (hctrl_len : w.ctrl.length = (bm.toNat + 1) + 8)
    (hidx_s : idx < w.slots.length)
    (hw_meta : w.allocPtr ≠ 0#64 ∧ w.allocPtr.toNat % 8 = 0 ∧
      w.allocPtr.toNat + (17 * (bm.toNat + 1) + 8) ≤ 2 ^ 64 ∧
      w.ctrlPtr = w.allocPtr + BitVec.ofNat 64 (16 * (bm.toNat + 1)))
    (hlook : cliMapLookup k map = some (w.slots[idx]'hidx_s).2)
    (hinv' : SwissTableInv bm gl' (w.items - 1#64) (setCtrl bm w.ctrl idx newTag) w.slots (cliMapErase k map))
    (hu' : bucketMaskToCapacity bm - gl'.toNat ≤ u)
    (hpc : sf0.pc = P.pl9.base + 240#64) (hrun : sf0.status = .Running) (hrw : RwFrame s0 sf0)
    (hx0 : sf0.readReg64 (Reg.gpr 0#5) = mapPtr) (hx8 : sf0.readReg64 (Reg.gpr 8#5) = w.ctrlPtr)
    (hx9 : sf0.readReg64 (Reg.gpr 9#5) = w.ctrlPtr + BitVec.ofNat 64 (removeIdxBefore bm idx))
    (hx10 : sf0.readReg64 (Reg.gpr 10#5) = w.ctrlPtr - (BitVec.ofNat 64 idx <<< 4))
    (hx11 : sf0.readReg64 (Reg.gpr 11#5) = BitVec.ofNat 64 idx)
    (hw12 : (sf0.readReg64 (Reg.gpr 12#5)).truncate 8 = newTag) :
    SepWP ((hbProg9 P).rebase P.pl9.base X) (s0.readReg64 .lr) sf0
      ((w.ctrlPtr ↦ₛ w.ctrl) ∗ ((mapPtr ↦₆₄ w.ctrlPtr) ∗ ((mapPtr + 8#64) ↦₆₄ bm) ∗
        ((mapPtr + 16#64) ↦₆₄ gl') ∗ ((mapPtr + 24#64) ↦₆₄ w.items)) ∗
       ((((w.ctrlPtr - (BitVec.ofNat 64 idx <<< 4)) + 0xfffffffffffffff0#64) ↦₆₄ (w.slots[idx]'hidx_s).1) ∗
        (((w.ctrlPtr - (BitVec.ofNat 64 idx <<< 4)) + 0xfffffffffffffff8#64) ↦₆₄ (w.slots[idx]'hidx_s).2) ∗
        (slotsDownFrom w.ctrlPtr (w.slots.take idx) ∗
         slotsDownFrom (slotAddr w.ctrlPtr idx) (w.slots.drop (idx + 1)))) ∗
       hbRodata P.pl ∗ A.Block w.allocPtr (17 * (bm.toNat + 1) + 8) 8)
      (fun sf P_f => s0.mem.KeepsFrozen sf.mem → RemovePost P A s0 mapPtr bm k map u R sf P_f) := by
  have hP := P.placeable9; subst hx0
  have hmir_lt : setCtrlMirrorIdx bm idx < w.ctrl.length := by
    have := setCtrlMirrorIdx_lt hinv'.validMask idx; omega
  have ha_mir : w.ctrlPtr + BitVec.ofNat 64 (setCtrlMirrorIdx bm idx) =
      (w.ctrlPtr + BitVec.ofNat 64 (removeIdxBefore bm idx)) + 8#64 := by
    rw [setCtrlMirrorIdx_eq_add8 hinv'.validMask idx, BitVec.ofNat_add]; bv_lin
  refine step_str8_perm (pc := P.pl9.base + 240#64) (pc' := P.pl9.base + 244#64)
    (ea := w.ctrlPtr + BitVec.ofNat 64 idx) (rt := .gpr 12#5)
    (addr := .RegOffset (.gpr 8#5) (.gpr 11#5) .UXTX 0) (val := newTag) hrw hpc hrun (by simp) rfl
    (by simp [evalAddrMode, extendVal, hx8, hx11]) hw12
    (SepStore8.left (SepStore8.of_pointsToBytes_here _ w.ctrlPtr w.ctrl idx newTag (by omega) rfl))
    (by bv_lin) fun m1 hrw1 => ?_
  wp_conv_pre => rw [write8_eq_set w.ctrl newTag (by omega)]
  wp_sym_steps 1
  refine step_str8_perm (pc := P.pl9.base + 248#64) (pc' := P.pl9.base + 252#64) (rt := .gpr 12#5)
    (addr := .Offset (.gpr 9#5) 8#64) (ea := (w.ctrlPtr + BitVec.ofNat 64 (removeIdxBefore bm idx)) + 8#64)
    (val := newTag) (by rw_simp hrw1) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
    (by simp) rfl (by simp [evalAddrMode, wp_norm, arm64_norm, hx9]) (by simpa [wp_norm, arm64_norm] using hw12)
    (SepStore8.left (SepStore8.of_pointsToBytes_here _ w.ctrlPtr (w.ctrl.set idx newTag)
      (setCtrlMirrorIdx bm idx) newTag (by simp; omega) ha_mir)) (by bv_lin) fun m2 hrw2 => ?_
  wp_conv_pre =>
    rw [write8_eq_set (w.ctrl.set idx newTag) newTag (by simp; omega)]
    change (w.ctrlPtr ↦ₛ setCtrl bm w.ctrl idx newTag) ∗ _
  wp_sym_steps 1
  refine SepWP.step_ldur64 (pc := P.pl9.base + 256#64) (rt := .gpr 1#5)
    (addr := .UnscaledOffset (.gpr 10#5) 0xfffffffffffffff8#64)
    (ea := (w.ctrlPtr - (BitVec.ofNat 64 idx <<< 4)) + 0xfffffffffffffff8#64) (wb := none)
    (v := (w.slots[idx]'hidx_s).2) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
    (by simp) rfl (by simp [evalAddrMode, wp_norm, arm64_norm, hx10]) (by wp_sep_access) rfl ?_
  wp_conv_pre => rw [← slotsDownFrom_focus_ldur w.ctrlPtr w.slots hidx_s]
  refine step_str64_perm (pc := P.pl9.base + 260#64) (pc' := P.pl9.base + 264#64) (rt := .gpr 8#5)
    (addr := .Offset (.gpr 0#5) 24#64) (ea := sf0.readReg64 (Reg.gpr 0#5) + 24#64)
    (val := w.items - 1#64) (by rw_simp hrw2) (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm, hrun]) (by simp) rfl (by simp [evalAddrMode, wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm]) (by wp_sep_access) (by bv_lin) fun m3 hrw3 => ?_
  wp_sym_steps 2
  apply SepWP.done (by simp [wp_norm, arm64_norm, hrw.2.1]) (by simp [wp_norm, arm64_norm, hrun])
  intro hkf; refine close_rw_post (by rw_simp hrw3) hkf (by simp [hlook, wp_norm, arm64_norm]) ?_
  unfold U64MapRep U64MapStruct; simp only [hbm0, ↓reduceIte]
  refine Entails.pure_right ⟨hmap_al, hmap_nw, hinv'.wf⟩ ?_
  let w' : HbHeapMapWitness :=
    { allocPtr := w.allocPtr, ctrlPtr := w.ctrlPtr, growthLeft := gl',
      items := w.items - 1#64, ctrl := setCtrl bm w.ctrl idx newTag, slots := w.slots }
  refine Entails.trans (Entails.of_eq (show _ =
      hbRodata P.pl ∗ (((sf0.readReg64 (Reg.gpr 0#5) ↦₆₄ w'.ctrlPtr) ∗
        ((sf0.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ bm) ∗
        ((sf0.readReg64 (Reg.gpr 0#5) + 16#64) ↦₆₄ w'.growthLeft) ∗
        ((sf0.readReg64 (Reg.gpr 0#5) + 24#64) ↦₆₄ w'.items)) ∗
        A.Block w'.allocPtr (17 * (bm.toNat + 1) + 8) 8 ∗
        slotsDownFrom w'.ctrlPtr w'.slots ∗ (w'.ctrlPtr ↦ₛ w'.ctrl)) by ac_rfl))
    (sepConj_mono_right (Entails.sepExists_right w'
      (Entails.pure_right ⟨hinv', hu', hw_meta.1, hw_meta.2.1, hw_meta.2.2.1, hw_meta.2.2.2⟩
        (Entails.of_eq (by ac_rfl)))))

private theorem hbRemove_hit_wp (P : HbPlaced) (A : HbAlloc) (X : String → Option (State → State))
    {s0 sti : State} {mapPtr bm k : BitVec 64} {map : Map64} {u : Nat} {R : SepProp}
    {w : HbHeapMapWitness} {idx : Nat}
    (hmap_al : mapPtr.toNat % 8 = 0) (hmap_nw : mapPtr.toNat + 32 ≤ 2 ^ 64)
    (hbm0 : bm ≠ 0#64) (hidx_b : idx < bm.toNat + 1) (hidx_s : idx < w.slots.length)
    (hw_meta : w.allocPtr ≠ 0#64 ∧ w.allocPtr.toNat % 8 = 0 ∧
      w.allocPtr.toNat + (17 * (bm.toNat + 1) + 8) ≤ 2 ^ 64 ∧
      w.ctrlPtr = w.allocPtr + BitVec.ofNat 64 (16 * (bm.toNat + 1)))
    (hinv : SwissTableInv bm w.growthLeft w.items w.ctrl w.slots map)
    (hu : bucketMaskToCapacity bm - w.growthLeft.toNat ≤ u)
    (hfull_idx : isFullTag (w.ctrl[idx]'(by have := hinv.mirror.1; omega)) = true)
    (hkey_idx : (w.slots[idx]'(by have := hinv.slots_len; omega)).1 = k)
    (hlook : cliMapLookup k map = some (w.slots[idx]'hidx_s).2)
    (hpc : sti.pc = P.pl9.base + 140#64) (hrun : sti.status = .Running) (hro : RoFrame s0 sti)
    (hx0 : sti.readReg64 (Reg.gpr 0#5) = mapPtr) (hx8 : sti.readReg64 (Reg.gpr 8#5) = w.ctrlPtr)
    (hx9 : sti.readReg64 (Reg.gpr 9#5) = bm)
    (hx10 : sti.readReg64 (Reg.gpr 10#5) = w.ctrlPtr - (BitVec.ofNat 64 idx <<< 4))
    (hx11 : sti.readReg64 (Reg.gpr 11#5) = BitVec.ofNat 64 idx) :
    SepWP ((hbProg9 P).rebase P.pl9.base X) (s0.readReg64 .lr) sti
      ((w.ctrlPtr ↦ₛ w.ctrl) ∗ ((mapPtr ↦₆₄ w.ctrlPtr) ∗ ((mapPtr + 8#64) ↦₆₄ bm) ∗
        ((mapPtr + 16#64) ↦₆₄ w.growthLeft) ∗ ((mapPtr + 24#64) ↦₆₄ w.items)) ∗
       ((((w.ctrlPtr - (BitVec.ofNat 64 idx <<< 4)) + 0xfffffffffffffff0#64) ↦₆₄ (w.slots[idx]'hidx_s).1) ∗
        (((w.ctrlPtr - (BitVec.ofNat 64 idx <<< 4)) + 0xfffffffffffffff8#64) ↦₆₄ (w.slots[idx]'hidx_s).2) ∗
        (slotsDownFrom w.ctrlPtr (w.slots.take idx) ∗
         slotsDownFrom (slotAddr w.ctrlPtr idx) (w.slots.drop (idx + 1)))) ∗
       hbRodata P.pl ∗ A.Block w.allocPtr (17 * (bm.toNat + 1) + 8) 8)
      (RemovePost P A s0 mapPtr bm k map u R) := by
  have hP := P.placeable9; subst hx0; have hctrl_len := hinv.mirror.1
  let g_after := ctrlGroupWord w.ctrl idx; let idx_bef := removeIdxBefore bm idx
  let g_before := ctrlGroupWord w.ctrl idx_bef
  have hbef_lt : idx_bef < bm.toNat + 1 := removeIdxBefore_lt hinv.validMask idx
  refine SepWP.mono_frozen (Φ := fun m => s0.mem.KeepsFrozen m)
    (post := fun sf P_f => s0.mem.KeepsFrozen sf.mem →
      RemovePost P A s0 (sti.readReg64 (Reg.gpr 0#5)) bm k map u R sf P_f)
    (fun _ _ => Memory.KeepsFrozen.trans) (hro.2 ▸ Memory.KeepsFrozen.refl s0.mem) ?_
    (fun _ _ _ _ hkf hp => hp hkf)
  wp_sym_steps 1
  wp_conv_pre => rw [pointsToBytes_focus_ctrlGroupWord w.ctrlPtr w.ctrl (pos := idx) (by omega)]
  refine SepWP.step_ldrSimd64 (pc := P.pl9.base + 144#64) (vt := 1#5)
    (s' := ((sti.writeVReg128 0#5 0xffffffffffffffffffffffffffffffff#128).writeVReg128 1#5
      (g_after.zeroExtend 128)).setPC (P.pl9.base + 148#64))
    (addr := .RegOffset (.gpr 8#5) (.gpr 11#5) .UXTX 0) (ea := w.ctrlPtr + BitVec.ofNat 64 idx)
    (wb := none) (v := g_after) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
    (by simp) rfl (by simp [evalAddrMode, extendVal, wp_norm, arm64_norm, hx8, hx11])
    (by wp_sep_access) (by simp [applyWriteback, wp_norm, arm64_norm]) ?_
  wp_sym_steps 3; rw [removeIdxBefore_bv bm idx]
  wp_conv_pre =>
    rw [← pointsToBytes_focus_ctrlGroupWord w.ctrlPtr w.ctrl (pos := idx) (by omega),
        pointsToBytes_focus_ctrlGroupWord w.ctrlPtr w.ctrl (pos := idx_bef) (by omega)]
  refine SepWP.step_ldrSimd64 (pc := P.pl9.base + 160#64) (vt := 2#5)
    (s' := (((((sti.writeVReg128 0#5 0xffffffffffffffffffffffffffffffff#128).writeVReg128 1#5
      (g_after.zeroExtend 128)).writeReg64 (.gpr 12#5) (BitVec.ofNat 64 idx - 8#64)).writeReg64
      (.gpr 9#5) (w.ctrlPtr + BitVec.ofNat 64 (removeIdxBefore bm idx))).writeVReg128 2#5
      (g_before.zeroExtend 128)).setPC (P.pl9.base + 164#64))
    (addr := .Offset (.gpr 9#5) 0#64) (ea := w.ctrlPtr + BitVec.ofNat 64 idx_bef)
    (wb := none) (v := g_before) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
    (by simp) rfl (by simp [evalAddrMode, wp_norm, arm64_norm, idx_bef])
    (by wp_sep_access) (by simp [applyWriteback, wp_norm, arm64_norm]) ?_
  wp_conv_pre => rw [← pointsToBytes_focus_ctrlGroupWord w.ctrlPtr w.ctrl (pos := idx_bef) (by omega)]
  wp_sym_steps 1
  have hc1 := simd_cmeq_allOnes8 g_after; conv at hc1 => lhs; simp only [wp_norm, arm64_norm]
  rw [hc1]; wp_sym_steps 1
  have hc2 := simd_cmeq_allOnes8 g_before; conv at hc2 => lhs; simp only [wp_norm, arm64_norm]
  rw [hc2]; wp_sym_steps 7
  have hsw (x : BitVec 64) : BitVec.setWidth 64 (BitVec.zeroExtend 128 x) = x := by simp
  simp only [hsw, ProofLib.reverseBits_eq_reverse, byteMaskOfBits_lowestLane (eqBits8 g_after tagEmpty),
    byteMaskOfBits_clz_lsr3 (eqBits8 g_before tagEmpty), ← BitVec.ofNat_add]
  set_option proofLib.wpBranchAutoDecide false in
  wp_sym_steps 2
  wp_if hbls
  · have hsum_lt : (eqBits8 g_after tagEmpty).ctz.toNat +
        (eqBits8 g_before tagEmpty).clz.toNat < 2 ^ 64 := by
      have := (eqBits8 g_after tagEmpty).ctz.isLt; have := (eqBits8 g_before tagEmpty).clz.isLt; omega
    have hle7 : (eqBits8 g_after tagEmpty).ctz.toNat + (eqBits8 g_before tagEmpty).clz.toNat ≤ 7 := by
      rw [BitVec.ule_iff_toNat_le, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsum_lt] at hbls; simpa using hbls
    wp_sym_steps 2
    refine step_str64_perm (pc := P.pl9.base + 232#64) (pc' := P.pl9.base + 236#64) (rt := .gpr 12#5)
      (addr := .Offset (.gpr 0#5) 16#64) (ea := sti.readReg64 (Reg.gpr 0#5) + 16#64)
      (val := w.growthLeft + 1#64) (by have h1 := hro.1; rw_simp h1)
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun]) (by simp) rfl
      (by simp [evalAddrMode, wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
      (by wp_sep_access) (by bv_lin) fun m0 hrw0 => ?_
    wp_sym_steps 1
    have hinv_e := hinv.erase_empty hidx_b hfull_idx hkey_idx hle7
    have hu_e : bucketMaskToCapacity bm - (w.growthLeft + 1#64).toNat ≤ u := by
      have := (hinv.validMask.capacity_bounds).2; have : 7 * 2 ^ 55 < 2 ^ 64 := by decide
      have := hinv.growth_le
      have hadd : (w.growthLeft + 1#64).toNat = w.growthLeft.toNat + 1 := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat,
          show (1 : Nat) % 2 ^ 64 = 1 from Nat.mod_eq_of_lt (by decide), Nat.mod_eq_of_lt (by omega)]
      omega
    exact hbRemove_finish_wp P A X hmap_al hmap_nw hbm0 hidx_b hctrl_len hidx_s hw_meta hlook
      hinv_e hu_e
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun]) (by rw_simp hrw0)
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hx8])
      (by simp [wp_norm, arm64_norm, hw_meta.2.2.2]) (by simp [wp_norm, arm64_norm, hx10])
      (by simp [wp_norm, arm64_norm, hx11]) (by simp [wp_norm, arm64_norm]; rfl)
  · wp_sym_steps 2
    exact hbRemove_finish_wp P A X hmap_al hmap_nw hbm0 hidx_b hctrl_len hidx_s hw_meta hlook
      (hinv.erase_deleted hidx_b hfull_idx hkey_idx) hu
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
      (by have h1 := hro.1; rw_simp h1) (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hx8]) (by simp [wp_norm, arm64_norm, hw_meta.2.2.2])
      (by simp [wp_norm, arm64_norm, hx10]) (by simp [wp_norm, arm64_norm, hx11])
      (by simp [wp_norm, arm64_norm]; rfl)

private structure HbMeta (w : HbHeapMapWitness) (bm : BitVec 64) : Prop where
  ne0 : w.allocPtr ≠ 0#64
  al : w.allocPtr.toNat % 8 = 0
  nw : w.allocPtr.toNat + (17 * (bm.toNat + 1) + 8) ≤ 2 ^ 64
  ce : w.ctrlPtr = w.allocPtr + BitVec.ofNat 64 (16 * (bm.toNat + 1))

private def RemoveProbeInvAt (s0 : State) (w : HbHeapMapWitness) (mapPtr bm k : BitVec 64)
    (step : Nat) (st : State) : Prop :=
  RoFrame s0 st ∧ st.readReg64 (Reg.gpr 0#5) = mapPtr ∧ st.readReg64 (Reg.gpr 1#5) = k ∧
  st.readReg64 (Reg.gpr 8#5) = w.ctrlPtr ∧ st.readReg64 (Reg.gpr 9#5) = bm ∧
  (st.readReg64 (Reg.gpr 10#5) &&& bm) = BitVec.ofNat 64 (probePos bm k step) ∧
  st.readReg64 (Reg.gpr 12#5) = BitVec.ofNat 64 (8 * step) ∧
  st.readVReg128 0#5 = dupByte8Vec ((k * fxSeed) >>> 57) ∧
  st.readVReg128 1#5 = 0xffffffffffffffffffffffffffffffff#128 ∧
  (∀ s < step, ∀ j < 8, getLane8 (ctrlGroupWord w.ctrl (probePos bm k s)) j = h2Tag k →
    (h : (probePos bm k s + j) % (bm.toNat + 1) < w.slots.length) →
    (w.slots[(probePos bm k s + j) % (bm.toNat + 1)]'h).1 ≠ k)

private def RemoveProbeInnerInv (s0 : State) (w : HbHeapMapWitness) (mapPtr bm k : BitVec 64)
    (step : Nat) (b : BitVec 8) (st : State) : Prop :=
  let pos := probePos bm k step; let g := ctrlGroupWord w.ctrl pos
  b ≠ 0#8 ∧ RoFrame s0 st ∧ st.readReg64 (Reg.gpr 0#5) = mapPtr ∧ st.readReg64 (Reg.gpr 1#5) = k ∧
  st.readReg64 (Reg.gpr 8#5) = w.ctrlPtr ∧ st.readReg64 (Reg.gpr 9#5) = bm ∧
  st.readReg64 (Reg.gpr 12#5) = BitVec.ofNat 64 (8 * step) ∧
  st.readReg64 (Reg.gpr 13#5) = BitVec.ofNat 64 pos ∧
  st.readReg64 (Reg.gpr 14#5) = highBitMaskOfBits b ∧
  st.readVReg128 0#5 = dupByte8Vec ((k * fxSeed) >>> 57) ∧
  st.readVReg128 1#5 = 0xffffffffffffffffffffffffffffffff#128 ∧
  st.readVReg128 2#5 = g.zeroExtend 128 ∧
  (∀ j < 8, b.getLsbD j = true → getLane8 g j = h2Tag k) ∧
  (∀ j < 8, getLane8 g j = h2Tag k → b.getLsbD j = false →
    (h : (pos + j) % (bm.toNat + 1) < w.slots.length) →
    (w.slots[(pos + j) % (bm.toNat + 1)]'h).1 ≠ k)

private theorem hbRemove_after_group_wp (P : HbPlaced) (A : HbAlloc)
    (X : String → Option (State → State))
    {s0 sg : State} {mapPtr bm k : BitVec 64} {map : Map64} {u : Nat} {R P_pre : SepProp}
    {w : HbHeapMapWitness} {step step_end : Nat}
    (hpre : s0.mem ⊨ U64MapRep P.pl A mapPtr map bm u ∗ R)
    (hinv : SwissTableInv bm w.growthLeft w.items w.ctrl w.slots map)
    (hstep_le : step ≤ step_end)
    (hemp_end : tagEmpty ∈ ctrlGroupAt w.ctrl (probePos bm k step_end))
    (hprev : ∀ s < step, ∀ j < 8, getLane8 (ctrlGroupWord w.ctrl (probePos bm k s)) j = h2Tag k →
      (h : (probePos bm k s + j) % (bm.toNat + 1) < w.slots.length) →
      (w.slots[(probePos bm k s + j) % (bm.toNat + 1)]'h).1 ≠ k)
    (hno_h2 : ∀ j < 8, getLane8 (ctrlGroupWord w.ctrl (probePos bm k step)) j = h2Tag k →
      (h : (probePos bm k step + j) % (bm.toNat + 1) < w.slots.length) →
      (w.slots[(probePos bm k step + j) % (bm.toNat + 1)]'h).1 ≠ k)
    (hpc : sg.pc = P.pl9.base + 112#64) (hrun : sg.status = .Running) (hro : RoFrame s0 sg)
    (hx0 : sg.readReg64 (Reg.gpr 0#5) = mapPtr) (hx1 : sg.readReg64 (Reg.gpr 1#5) = k)
    (hx8 : sg.readReg64 (Reg.gpr 8#5) = w.ctrlPtr) (hx9 : sg.readReg64 (Reg.gpr 9#5) = bm)
    (hx12 : sg.readReg64 (Reg.gpr 12#5) = BitVec.ofNat 64 (8 * step))
    (hx13 : sg.readReg64 (Reg.gpr 13#5) = BitVec.ofNat 64 (probePos bm k step))
    (hv0 : sg.readVReg128 0#5 = dupByte8Vec ((k * fxSeed) >>> 57))
    (hv1 : sg.readVReg128 1#5 = 0xffffffffffffffffffffffffffffffff#128)
    (hv2 : sg.readVReg128 2#5 = (ctrlGroupWord w.ctrl (probePos bm k step)).zeroExtend 128)
    (ih_outer : ∀ step' : Nat, ∀ s' : State, step_end + 1 - step' < step_end + 1 - step →
      s'.pc = P.pl9.base + 44#64 → s'.status = .Running →
      (step' ≤ step_end ∧ RemoveProbeInvAt s0 w mapPtr bm k step' s') →
      SepWP ((hbProg9 P).rebase P.pl9.base X) (s0.readReg64 .lr) s' P_pre
        (RemovePost P A s0 mapPtr bm k map u R)) :
    SepWP ((hbProg9 P).rebase P.pl9.base X) (s0.readReg64 .lr) sg P_pre
      (RemovePost P A s0 mapPtr bm k map u R) := by
  have hP := P.placeable9; let g := ctrlGroupWord w.ctrl (probePos bm k step)
  wp_sym_steps 1
  have hall := simd_cmeq_allOnes8 g; conv at hall => lhs; simp only [wp_norm, arm64_norm]
  rw [hall]; wp_sym_steps 1
  have humax := simdUmaxv8_byteMaskOfBits (eqBits8 g tagEmpty)
  conv at humax => lhs; simp only [simdUmaxv8, wp_norm, arm64_norm]
  rw [humax]
  set_option proofLib.wpBranchAutoDecide false in
  wp_sym_steps 2
  wp_if htbnz
  · have hemp_ne : eqBits8 g tagEmpty ≠ 0#8 := fun hz => by rw [hz] at htbnz; simp at htbnz
    have hnone := probe_empty_miss_lookup hinv hemp_ne hprev hno_h2
    wp_sym_steps 2
    apply SepWP.done (by simp [wp_norm, arm64_norm, hro.1.2.1]) (by simp [wp_norm, arm64_norm, hrun])
    rw [RemovePost, cliMapErase_eq_self_of_lookup_none hnone]
    exact close_ro_miss hpre (by ro_simp hro) (by simp [hnone, wp_norm, arm64_norm])
  · have hemp_eq : eqBits8 g tagEmpty = 0#8 :=
      Classical.byContradiction fun hne => htbnz (by simp only [hne, ↓reduceIte]; decide)
    have hlt_end := probe_nonempty_lt_end hinv hstep_le hemp_end hemp_eq
    wp_sym_steps 3
    apply ih_outer (step + 1) _ (by omega)
    · simp only [wp_norm, arm64_norm]
    · simp only [wp_norm, arm64_norm, hrun]
    · refine ⟨by omega, by ro_simp hro, by simp only [wp_norm, arm64_norm, hx0],
        by simp only [wp_norm, arm64_norm, hx1], by simp only [wp_norm, arm64_norm, hx8],
        by simp only [wp_norm, arm64_norm, hx9],
        by simpa only [wp_norm, arm64_norm, hx12, hx13] using probePos_step_bv hinv.validMask k step,
        by simp only [wp_norm, arm64_norm]
           rw [show 8 * (step + 1) = 8 * step + 8 by omega, BitVec.ofNat_add],
        by simp only [wp_norm, arm64_norm, hv0], by simp only [wp_norm, arm64_norm, hv1],
        extend_probe_prev hprev hno_h2⟩

theorem hashbrown_remove_ok (P : HbPlaced) (A : HbAlloc)
    (X : String → Option (State → State) := fun _ => none) :
    let prog := (hbProg9 P).rebase P.pl9.base X
    subroutine_ok prog (prog.fnAddr "hashbrown_remove") (hashbrownRemoveSpec P.pl A) := by
  dsimp only; unfold hashbrownRemoveSpec; wp_entry
  revert a_1 a a_2 a_3 a_rest_1 hsp_align hpre h_1 h
  intro mapPtr map bm u k _ hpre hx0 hx1; have hP := P.placeable9
  change SepWP ((hbProg9 P).rebase P.pl9.base X) (s0.readReg64 .lr) s0 _
    (RemovePost P A s0 mapPtr bm k map u R)
  wp_conv_pre => unfold U64MapRep
  apply SepWP.pure_elim; rintro ⟨hmap_al, hmap_nw, hmap_wf⟩
  by_cases hbm0 : bm = 0#64
  · subst hbm0; wp_simp_pre [U64MapStruct]; wp_focus_pure; rintro rfl; wp_sym_steps 12
    have hfx0 : k * 5871781006564002453#64 = k * fxSeed := rfl
    rw [hfx0, dup_lsr57_eq (k * fxSeed), BitVec.and_zero]
    wp_conv_pre => rw [hbRodata_focus_emptyCtrl P.pl]
    set_option proofLib.wpBranchAutoDecide false in
    wp_sym_steps 5
    wp_conv_pre => rw [← hbRodata_focus_emptyCtrl P.pl]
    have hm_empty := simd_cmeq_dup8_highMask 0xffffffffffffffff#64 ((k * fxSeed) >>> 57)
    change (zipLanes 8 ((0xffffffffffffffff#64).zeroExtend 128) (dupByte8Vec ((k * fxSeed) >>> 57))
      (fun a b => if a == b then 0xff#128 else 0#128) 8).truncate 64 &&&
      0x8080808080808080#64 = highBitMaskOfBits (eqBits8 0xffffffffffffffff#64 (h2Tag k)) at hm_empty
    conv at hm_empty => lhs; simp only [wp_norm, arm64_norm]
    rw [hm_empty, eqBits8_allOnes_h2Tag k, highBitMaskOfBits_zero]
    simp only [beq_self_eq_true, ↓reduceIte]; wp_sym_steps 1
    have hall := simd_cmeq_allOnes8 0xffffffffffffffff#64
    conv at hall => lhs; simp only [wp_norm, arm64_norm]
    rw [hall]; wp_sym_steps 1
    have humax := simdUmaxv8_byteMaskOfBits (eqBits8 0xffffffffffffffff#64 tagEmpty)
    conv at humax => lhs; simp only [simdUmaxv8, wp_norm, arm64_norm]
    have hempty_ff : eqBits8 0xffffffffffffffff#64 tagEmpty = 0xff#8 := by decide
    rw [humax, hempty_ff]; wp_sym_steps 4
    apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
    rw [RemovePost]
    exact close_ro_miss hpre (by ro_simp0) (by simp [cliMapLookup, wp_norm, arm64_norm])
  · wp_simp_pre [hbm0]; apply SepWP.exists_left; intro w
    wp_focus_pure; rintro ⟨hinv, hu, h_al1, h_al2, h_al3, h_ce⟩
    have hw_meta : HbMeta w bm := ⟨h_al1, h_al2, h_al3, h_ce⟩; clear h_al1 h_al2 h_al3 h_ce
    wp_simp_pre [U64MapStruct]
    have hctrl_len : w.ctrl.length = (bm.toNat + 1) + 8 := hinv.mirror.1
    have hslots_len : w.slots.length = bm.toNat + 1 := hinv.slots_len
    rcases hinv.exists_empty_probe_group k with ⟨step_end, _, hemp_end⟩
    wp_sym_steps 11
    apply SepWP.cfg_fixpoint_wf_cps (Label := Nat) (l0 := 0) (cut_pc := fun _ => P.pl9.base + 44#64)
      (meas := fun step _ => step_end + 1 - step) (P_inv := fun _ _ => _)
      (Inv := fun step st => step ≤ step_end ∧ RemoveProbeInvAt s0 w mapPtr bm k step st)
      (post := fun _ => RemovePost P A s0 mapPtr bm k map u R)
    · simp only [wp_norm, arm64_norm]
    · simp only [wp_norm, arm64_norm, hrun]
    · exact Entails.refl _
    · have hfx : k * 5871781006564002453#64 = k * fxSeed := rfl
      refine ⟨Nat.zero_le _, by ro_simp0, by simp only [wp_norm, arm64_norm, hx0],
        by simp only [wp_norm, arm64_norm, hx1], by simp only [wp_norm, arm64_norm],
        by simp only [wp_norm, arm64_norm],
        by simpa only [wp_norm, arm64_norm, hfx, fxHash, fxProd, triByteOff_zero, BitVec.add_zero]
             using probePos_bv_eq bm k 0,
        by simp only [wp_norm, arm64_norm],
        by simpa only [wp_norm, arm64_norm, hfx] using dup_lsr57_eq (k * fxSeed),
        by simp only [wp_norm, arm64_norm], fun _ hs => by omega⟩
    · intro step st hpc_st hrun_st ⟨hstep_le, hro, hx0_st, hx1_st, hx8_st, hx9_st, hx10_st,
        hx12_st, hv0_st, hv1_st, hprev⟩ ih_outer
      let pos := probePos bm k step; let g := ctrlGroupWord w.ctrl pos
      have hpos_lt : pos < bm.toNat + 1 := probePos_lt_buckets hinv.validMask k step
      wp_sym_steps 1
      wp_conv_pre => rw [pointsToBytes_focus_ctrlGroupWord w.ctrlPtr w.ctrl (pos := pos) (by omega)]
      set_option proofLib.wpBranchAutoDecide false in
      wp_sym_steps 5
      wp_conv_pre => rw [← pointsToBytes_focus_ctrlGroupWord w.ctrlPtr w.ctrl (pos := pos) (by omega)]
      have hm_h2 := simd_cmeq_dup8_highMask g ((k * fxSeed) >>> 57)
      change (zipLanes 8 (g.zeroExtend 128) (dupByte8Vec ((k * fxSeed) >>> 57))
        (fun a b => if a == b then 0xff#128 else 0#128) 8).truncate 64 &&&
        0x8080808080808080#64 = highBitMaskOfBits (eqBits8 g (h2Tag k)) at hm_h2
      conv at hm_h2 => lhs; simp only [wp_norm, arm64_norm]
      rw [hm_h2]; wp_if hbeq
      · have hb0 : eqBits8 g (h2Tag k) = 0#8 :=
          (highBitMaskOfBits_eq_zero_iff _).1 (by simpa using hbeq)
        have hno_h2 : ∀ j < 8, getLane8 g j = h2Tag k →
            (h : (pos + j) % (bm.toNat + 1) < w.slots.length) →
            (w.slots[(pos + j) % (bm.toNat + 1)]'h).1 ≠ k := fun j hj htag => by
          have hbit := (bv8_eq_zero_iff_forall _).1 hb0 j hj
          rw [getLsbD_eqBits8 g (h2Tag k) hj, beq_eq_false_iff_ne] at hbit
          exact False.elim (hbit htag)
        exact hbRemove_after_group_wp P A X hpre hinv hstep_le hemp_end hprev hno_h2
          (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun_st])
          (by ro_simp hro) (by simp [wp_norm, arm64_norm, hx0_st])
          (by simp [wp_norm, arm64_norm, hx1_st]) (by simp [wp_norm, arm64_norm, hx8_st])
          (by simp [wp_norm, arm64_norm, hx9_st]) (by simp [wp_norm, arm64_norm, hx12_st])
          (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hv0_st])
          (by simp [wp_norm, arm64_norm, hv1_st]) (by simp only [wp_norm, arm64_norm]; rfl) ih_outer
      · have hb_ne : eqBits8 g (h2Tag k) ≠ 0#8 := fun hz => hbeq (by rw [hz, highBitMaskOfBits_zero])
        apply SepWP.cfg_fixpoint_wf_cps (Label := BitVec 8) (l0 := eqBits8 g (h2Tag k))
          (cut_pc := fun _ => P.pl9.base + 68#64) (meas := fun b _ => b.toNat) (P_inv := fun _ _ => _)
          (Inv := fun b sti => RemoveProbeInnerInv s0 w mapPtr bm k step b sti)
          (post := fun _ => RemovePost P A s0 mapPtr bm k map u R)
        · simp only [wp_norm, arm64_norm]
        · simp only [wp_norm, arm64_norm, hrun_st]
        · exact Entails.refl _
        · refine ⟨hb_ne, by ro_simp hro, by simp only [wp_norm, arm64_norm, hx0_st],
            by simp only [wp_norm, arm64_norm, hx1_st], by simp only [wp_norm, arm64_norm, hx8_st],
            by simp only [wp_norm, arm64_norm, hx9_st], by simp only [wp_norm, arm64_norm, hx12_st],
            by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
            by simp only [wp_norm, arm64_norm, hv0_st], by simp only [wp_norm, arm64_norm, hv1_st],
            by simp only [wp_norm, arm64_norm]; rfl,
            fun j hj hbit => by rw [getLsbD_eqBits8 g (h2Tag k) hj, beq_iff_eq] at hbit; exact hbit,
            fun j hj htag hbf => by
              rw [getLsbD_eqBits8 g (h2Tag k) hj, beq_eq_false_iff_ne] at hbf
              exact False.elim (hbf htag)⟩
        · intro b sti hpc_i hrun_i ⟨hb, hro_i, hx0_i, hx1_i, hx8_i, hx9_i, hx12_i, hx13_i, hx14_i,
            hv0_i, hv1_i, hv2_i, hsub_b, hmiss_b⟩ ih_inner
          rcases bv8_ctz_spec hb with ⟨hj0_lt, hj0_bit, _⟩
          let idx := (pos + b.ctz.toNat) % (bm.toNat + 1)
          have hidx_b : idx < bm.toNat + 1 := Nat.mod_lt _ (by omega)
          have hidx_lt : idx < w.slots.length := by omega
          have htag_j0 : getLane8 g b.ctz.toNat = h2Tag k := hsub_b b.ctz.toNat hj0_lt hj0_bit
          wp_sym_steps 5
          rw [ProofLib.reverseBits_eq_reverse, highBitMaskOfBits_lowestLane b,
            hinv.validMask.laneIdx_bv hpos_lt hj0_lt]
          wp_conv_pre => rw [slotsDownFrom_focus_ldur w.ctrlPtr w.slots hidx_lt]
          set_option proofLib.wpBranchAutoDecide false in
          wp_sym_steps 3
          wp_if hkeq
          · have hlook : cliMapLookup k map = some (w.slots[idx]'hidx_lt).2 :=
              hinv.lookup_eq_some_of_lane_match hpos_lt hj0_lt htag_j0 hkeq.symm
            have hfull_lane : isFullTag (getLane8 g b.ctz.toNat) = true := htag_j0 ▸ isFullTag_h2Tag k
            have hfull_idx : isFullTag (w.ctrl[idx]'(by omega)) = true := by
              rw [← CtrlMirrorInv.lane_full_eq_mod hinv.validMask hinv.mirror hpos_lt hj0_lt hfull_lane]
              exact hfull_lane
            exact SepWP.congr_pre (by ac_rfl)
              (hbRemove_hit_wp P A X hmap_al hmap_nw hbm0 hidx_b hidx_lt
                ⟨hw_meta.ne0, hw_meta.al, hw_meta.nw, hw_meta.ce⟩ hinv (by omega) hfull_idx hkeq.symm hlook
                (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun_i])
                (by ro_simp hro_i) (by simp [wp_norm, arm64_norm, hx0_i])
                (by simp [wp_norm, arm64_norm, hx8_i]) (by simp [wp_norm, arm64_norm, hx9_i])
                (by simp [wp_norm, arm64_norm, idx]) (by simp [wp_norm, arm64_norm, idx]))
          · have hk_ne : (w.slots[idx]'hidx_lt).1 ≠ k := Ne.symm hkeq
            wp_conv_pre => rw [← slotsDownFrom_focus_ldur w.ctrlPtr w.slots hidx_lt]
            set_option proofLib.wpBranchAutoDecide false in
            wp_sym_steps 3
            rw [highBitMaskOfBits_clear_lowest b]; wp_if hbne
            · have hb' : (b - 1#8) &&& b ≠ 0#8 := fun hz => by
                rw [hz, highBitMaskOfBits_zero] at hbne; simp at hbne
              apply ih_inner ((b - 1#8) &&& b) _ (bv8_clear_lowest_lt hb)
              · simp only [wp_norm, arm64_norm]
              · simp only [wp_norm, arm64_norm, hrun_i]
              · refine ⟨hb', by ro_simp hro_i, by simp only [wp_norm, arm64_norm, hx0_i],
                  by simp only [wp_norm, arm64_norm, hx1_i], by simp only [wp_norm, arm64_norm, hx8_i],
                  by simp only [wp_norm, arm64_norm, hx9_i], by simp only [wp_norm, arm64_norm, hx12_i],
                  by simp only [wp_norm, arm64_norm, hx13_i], by simp only [wp_norm, arm64_norm],
                  by simp only [wp_norm, arm64_norm, hv0_i], by simp only [wp_norm, arm64_norm, hv1_i],
                  by simp only [wp_norm, arm64_norm, hv2_i],
                  fun j hj hbit' => by
                    rw [bv8_getLsbD_clear_lowest b hj, Bool.and_eq_true] at hbit'
                    exact hsub_b j hj hbit'.1,
                  clear_lowest_miss hk_ne hmiss_b⟩
            · have hb0' : (b - 1#8) &&& b = 0#8 := (highBitMaskOfBits_eq_zero_iff _).1 hbne
              have hno_h2 : ∀ j < 8, getLane8 g j = h2Tag k →
                  (h : (pos + j) % (bm.toNat + 1) < w.slots.length) →
                  (w.slots[(pos + j) % (bm.toNat + 1)]'h).1 ≠ k := fun j hj htag hsl =>
                clear_lowest_miss hk_ne hmiss_b j hj htag (by simp [hb0']) hsl
              exact hbRemove_after_group_wp P A X hpre hinv hstep_le hemp_end hprev hno_h2
                (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun_i])
                (by ro_simp hro_i) (by simp [wp_norm, arm64_norm, hx0_i])
                (by simp [wp_norm, arm64_norm, hx1_i]) (by simp [wp_norm, arm64_norm, hx8_i])
                (by simp [wp_norm, arm64_norm, hx9_i]) (by simp [wp_norm, arm64_norm, hx12_i])
                (by simp [wp_norm, arm64_norm, hx13_i]) (by simp [wp_norm, arm64_norm, hv0_i])
                (by simp [wp_norm, arm64_norm, hv1_i]) (by simp [wp_norm, arm64_norm, hv2_i]) ih_outer

theorem hashbrown_remove_withCodeInv_ok (P : HbPlaced) (A : HbAlloc)
    (X : String → Option (State → State) := fun _ => none) :
    let prog := (hbProg9 P).rebase P.pl9.base X
    subroutine_ok prog (prog.fnAddr "hashbrown_remove")
      (withCodeInv A (hashbrownRemoveSpec P.pl A)) :=
  subroutine_ok_withCodeInv_of_plain A (hashbrown_remove_ok P A X)

set_option maxRecDepth 200000 in
theorem hashbrown_remove_subroutineOk (A : Obj.MultiPlacement → HbAlloc)
    (X : String → Option (State → State) := fun _ => none) :
    hashbrownLib.subroutineOk "hashbrown_remove"
      (fun mpl => hashbrownRemoveSpec (mplAsPl mpl) (A mpl)) X :=
  hbMultiSubroutineOk_of_plain "hashbrown_remove" 9 (off := 0) (fun P X' => hbProg9_rebase P X')
    (fun mpl => hashbrownRemoveSpec (mplAsPl mpl) (A mpl)) X
    (hok := fun P => hbPl_eq_mplAsPl P ▸ hashbrown_remove_ok P (A P.mpl) X)

set_option maxRecDepth 200000 in
theorem hashbrown_remove_withCodeInv_subroutineOk (A : Obj.MultiPlacement → HbAlloc)
    (X : String → Option (State → State) := fun _ => none) :
    hashbrownLib.subroutineOk "hashbrown_remove"
      (fun mpl => withCodeInv (A mpl) (hashbrownRemoveSpec (mplAsPl mpl) (A mpl))) X :=
  hbMultiSubroutineOk_of_plain "hashbrown_remove" 9 (off := 0) (fun P X' => hbProg9_rebase P X')
    (fun mpl => withCodeInv (A mpl) (hashbrownRemoveSpec (mplAsPl mpl) (A mpl))) X
    (hok := fun P => hbPl_eq_mplAsPl P ▸ hashbrown_remove_withCodeInv_ok P (A P.mpl) X)

end CaseStudies.Hashbrown.Proofs
