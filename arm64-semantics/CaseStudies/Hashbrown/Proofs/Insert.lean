/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import CaseStudies.Hashbrown.Proofs.Lookup
public import ProofLib.SepLogic.WPFrozen
public import ProofLib.SepLogic.WPp
import ProofLib.SepLogic.Entry
import ProofLib.SepLogic.SymWP
import ProofLib.SepLogic.LoopTactics
import ProofLib.BV
import ProofLib.BV.ReflectROBDD
import ProofLib.BV.WidthNorm

/-!
# Verification of `hashbrown_insert`

Proves functional correctness and safety of the SwissTable insertion entry point
`hashbrown_insert`.
-/
set_option autoImplicit false
@[expose] public section
namespace CaseStudies.Hashbrown.Proofs
open Arm64 Arm64.Obj Arm64.Rust ProofLib ProofLib.StdStartup CaseStudies.Hashbrown
/-- Control-byte array update performed by `RawTableInner::set_ctrl(idx, tag)`. -/
def setCtrl (bm : BitVec 64) (ctrl : List (BitVec 8)) (idx : Nat) (tag : BitVec 8) : List (BitVec 8) := (ctrl.set idx tag).set (setCtrlMirrorIdx bm idx) tag
private theorem setCtrlMirrorIdx_eq4 {idx : Nat} (hidx : idx < 4) : setCtrlMirrorIdx 3#64 idx = idx + 8 := by match idx with | 0 | 1 | 2 | 3 => decide | n + 4 => omega
private theorem setCtrlMirrorIdx_ge8 {bm : BitVec 64} (hbm : ValidBucketMask bm) (hge8 : 8 ≤ bm.toNat + 1) {idx : Nat} (hidx : idx < bm.toNat + 1) :
    setCtrlMirrorIdx bm idx = if idx < 8 then (bm.toNat + 1) + idx else idx := by
  obtain ⟨exp, hlo, hhi, hbm_eq⟩ := hbm; have hbkt : bm.toNat + 1 = 2 ^ exp := ValidBucketMask.buckets_eq hlo hhi hbm_eq
  have hpow_le : 2 ^ exp ≤ 2 ^ 58 := Nat.pow_le_pow_right (by decide) hhi; have hpow64 : 2 ^ 58 < 2 ^ 64 := by decide
  have h8 : (8 : Nat) % 2 ^ 64 = 8 := by decide
  unfold setCtrlMirrorIdx; by_cases hlt8 : idx < 8
  · simp only [hlt8, ↓reduceIte]
    have hsub_eq : BitVec.ofNat 64 idx - 8#64 = BitVec.ofNat 64 ((bm.toNat + 1) + idx - 8) + BitVec.ofNat 64 (2 ^ 64 - (bm.toNat + 1)) := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega : idx < 2 ^ 64), Nat.mod_eq_of_lt (by omega : (bm.toNat + 1) + idx - 8 < 2 ^ 64), Nat.mod_eq_of_lt (by omega : 2 ^ 64 - (bm.toNat + 1) < 2 ^ 64)]; omega
    obtain ⟨q, hq⟩ : (bm.toNat + 1) ∣ (2 ^ 64 - (bm.toNat + 1)) := by
      rw [hbkt, show 2 ^ 64 = 2 ^ exp * 2 ^ (64 - exp) by rw [← Nat.pow_add, show exp + (64 - exp) = 64 by omega]]; exact ⟨2 ^ (64 - exp) - 1, by rw [Nat.mul_sub_one]⟩
    have hand : ((BitVec.ofNat 64 idx - 8#64) &&& bm).toNat = (bm.toNat + 1) + idx - 8 := by
      rw [ValidBucketMask.and_toNat_eq_mod ⟨exp, hlo, hhi, hbm_eq⟩, hsub_eq, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : (bm.toNat + 1) + idx - 8 < 2 ^ 64), Nat.mod_eq_of_lt (by omega : 2 ^ 64 - (bm.toNat + 1) < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : ((bm.toNat + 1) + idx - 8) + (2 ^ 64 - (bm.toNat + 1)) < 2 ^ 64), hq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    rw [BitVec.toNat_add, hand, BitVec.toNat_ofNat, h8, Nat.mod_eq_of_lt (by omega)]; omega
  · simp only [hlt8, ↓reduceIte]
    have hsub : BitVec.ofNat 64 idx - 8#64 = BitVec.ofNat 64 (idx - 8) := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt (by omega : idx < 2 ^ 64), Nat.mod_eq_of_lt (by omega : idx - 8 < 2 ^ 64)]; omega
    have hand : ((BitVec.ofNat 64 idx - 8#64) &&& bm).toNat = idx - 8 := by
      rw [hsub, ValidBucketMask.and_toNat_eq_mod ⟨exp, hlo, hhi, hbm_eq⟩, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [BitVec.toNat_add, hand, BitVec.toNat_ofNat, h8, Nat.mod_eq_of_lt (by omega)]; omega
theorem setCtrlMirrorIdx_bounds {bm : BitVec 64} (hbm : ValidBucketMask bm) {idx : Nat} (hidx : idx < bm.toNat + 1) :
    setCtrlMirrorIdx bm idx < (bm.toNat + 1) + 8 ∧ (setCtrlMirrorIdx bm idx = idx ∨ bm.toNat + 1 ≤ setCtrlMirrorIdx bm idx) := by
  rcases hbm.buckets_cases with h4 | ⟨hge8, _⟩
  · have hbm3 : bm = 3#64 := BitVec.eq_of_toNat_eq (by change bm.toNat = 3; omega)
    subst hbm3; have hm := setCtrlMirrorIdx_eq4 (by change idx < 4; omega); exact ⟨by change setCtrlMirrorIdx 3#64 idx < 4 + 8; omega, Or.inr (by change 4 ≤ _; omega)⟩
  · rw [setCtrlMirrorIdx_ge8 hbm hge8 hidx]
    if hlt8 : idx < 8 then simp only [hlt8, ↓reduceIte]; exact ⟨by omega, Or.inr (by omega)⟩ else simp only [hlt8, ↓reduceIte]; exact ⟨by omega, Or.inl trivial⟩
theorem setCtrl_length {bm : BitVec 64} (ctrl : List (BitVec 8)) (idx : Nat) (tag : BitVec 8) : (setCtrl bm ctrl idx tag).length = ctrl.length := by simp [setCtrl]
theorem setCtrl_getElem_lt_buckets {bm : BitVec 64} (hbm : ValidBucketMask bm) {ctrl : List (BitVec 8)} (hlen : ctrl.length = (bm.toNat + 1) + 8)
    {idx i : Nat} (hidx : idx < bm.toNat + 1) (hi : i < bm.toNat + 1) (tag : BitVec 8) :
    (setCtrl bm ctrl idx tag)[i]'(by rw [setCtrl_length]; omega) = if i = idx then tag else ctrl[i]'(by omega) := by
  obtain ⟨_, hor⟩ := setCtrlMirrorIdx_bounds hbm hidx
  have h1 : (setCtrl bm ctrl idx tag)[i]? = some (if i = idx then tag else ctrl[i]'(by omega)) := by
    unfold setCtrl; rw [List.getElem?_set, List.getElem?_set, List.getElem?_eq_getElem (by omega)]; rcases hor with heq | hge
    · rw [heq]; if hii : idx = i then subst hii; simp [hlen]; omega else simp [hii, Ne.symm hii]
    · simp only [show setCtrlMirrorIdx bm idx ≠ i by omega, ↓reduceIte]; if hii : idx = i then subst hii; simp [hlen]; omega else simp [hii, Ne.symm hii]
  rw [List.getElem?_eq_getElem (by rw [setCtrl_length]; omega)] at h1; exact Option.some.inj h1
theorem CtrlMirrorInv.setCtrl_preserves {bm : BitVec 64} (hbm : ValidBucketMask bm) {ctrl : List (BitVec 8)}
    (hm : CtrlMirrorInv (bm.toNat + 1) ctrl) {idx : Nat} (hidx : idx < bm.toNat + 1) {tag : BitVec 8} (htag : ValidTag tag) : CtrlMirrorInv (bm.toNat + 1) (setCtrl bm ctrl idx tag) := by
  have hlen : ctrl.length = (bm.toNat + 1) + 8 := hm.1
  refine ⟨by simp [setCtrl, hlen], fun b hb => ?_, fun h4 => ?_, fun hge8 j hj => ?_⟩
  · unfold setCtrl at hb; exact (List.mem_or_eq_of_mem_set hb).elim (fun hb1 => (List.mem_or_eq_of_mem_set hb1).elim (hm.2.1 b) (· ▸ htag)) (· ▸ htag)
  · have hbm3 : bm = 3#64 := BitVec.eq_of_toNat_eq (by change bm.toNat = 3; omega)
    subst hbm3; have hm_idx := setCtrlMirrorIdx_eq4 (by change idx < 4; omega); rcases hm.2.2.1 h4 with ⟨hpad, hmir⟩
    refine ⟨fun j hj => by unfold setCtrl; rw [hm_idx, List.getElem?_set, List.getElem?_set]; simp only [show idx + 8 ≠ 4 + j by omega, show idx ≠ 4 + j by omega, ↓reduceIte]; exact hpad j hj,
      fun j hj => ?_⟩
    unfold setCtrl; rw [hm_idx, List.getElem?_set, List.getElem?_set, List.getElem?_set, List.getElem?_set]; by_cases hji : idx = j
    · subst idx; have h1 : ¬ (j + 8 = j) := (by omega); have h2 : j + 8 < (ctrl.set j tag).length := by simp [hlen]; omega
      have h3 : j < ctrl.length := (by omega); have h1' : j + 8 = 8 + j := by omega
      simp only [h1', ↓reduceIte]; rw [← h1']; simp only [h1, h2, h3, ↓reduceIte]
    · simp only [show idx + 8 ≠ 8 + j by omega, show idx ≠ 8 + j by omega, show idx + 8 ≠ j by omega, hji, ↓reduceIte]; exact hmir j hj
  · have hm_idx := setCtrlMirrorIdx_ge8 hbm hge8 hidx; unfold setCtrl; rw [hm_idx, List.getElem?_set, List.getElem?_set, List.getElem?_set, List.getElem?_set]
    by_cases hlt8 : idx < 8
    · simp only [hlt8, ↓reduceIte]; by_cases hji : idx = j
      · subst idx; simp only [show bm.toNat + 1 + j ≠ j by omega, show bm.toNat + 1 + j < (ctrl.set j tag).length by simp [hlen]; omega, show j < ctrl.length by omega, ↓reduceIte]
      · simp only [show bm.toNat + 1 + idx ≠ bm.toNat + 1 + j by omega, show idx ≠ bm.toNat + 1 + j by omega, show bm.toNat + 1 + idx ≠ j by omega, hji, ↓reduceIte]; exact hm.2.2.2 hge8 j hj
    · simp only [hlt8, show idx ≠ bm.toNat + 1 + j by omega, show idx ≠ j by omega, ↓reduceIte]; exact hm.2.2.2 hge8 j hj
private theorem setCtrl_not_mem_empty {bm : BitVec 64} {ctrl : List (BitVec 8)} {idx pos : Nat} {tag : BitVec 8}
    (hpos : pos + 8 ≤ ctrl.length) (hne : tag ≠ tagEmpty) (hnot : tagEmpty ∉ ctrlGroupAt ctrl pos) : tagEmpty ∉ ctrlGroupAt (setCtrl bm ctrl idx tag) pos := by
  have hpos' : pos + 8 ≤ (setCtrl bm ctrl idx tag).length := by simp [setCtrl_length, hpos]
  rw [mem_ctrlGroupAt_iff hpos']; rintro ⟨j, hj, hlane⟩
  have hget : (setCtrl bm ctrl idx tag)[pos + j]? = some tagEmpty := by rw [List.getElem?_eq_getElem (by omega), ← getLane8_ctrlGroupWord_eq_getElem hpos' hj, hlane]
  unfold setCtrl at hget; rw [List.getElem?_set, List.getElem?_set] at hget; split at hget
  · split at hget <;> simp_all
  · split at hget
    · split at hget <;> simp_all
    · rw [List.getElem?_eq_getElem (by omega)] at hget; injection hget with hget'
      rw [mem_ctrlGroupAt_iff hpos] at hnot; exact hnot ⟨j, hj, (getLane8_ctrlGroupWord_eq_getElem hpos hj).trans hget'⟩
private theorem ProbeReachable.setCtrl_other {bm : BitVec 64} (hbm : ValidBucketMask bm) {ctrl : List (BitVec 8)}
    (hm : CtrlMirrorInv (bm.toNat + 1) ctrl) {idx i : Nat} (hidx : idx < bm.toNat + 1) (hi_ne : i ≠ idx) {k' : BitVec 64} {tag : BitVec 8} (htag : ValidTag tag) (hne_emp : tag ≠ tagEmpty)
    (hreach : ProbeReachable bm ctrl k' i) : ProbeReachable bm (setCtrl bm ctrl idx tag) k' i := by
  obtain ⟨s0, l0, hs0, hl0, hlane0, hmod0, hprev0⟩ := hreach; have hi_lt : i < bm.toNat + 1 := by rw [← hmod0]; exact Nat.mod_lt _ (by omega)
  have hm' := CtrlMirrorInv.setCtrl_preserves hbm hm hidx htag; have hlen := hm.1; have hlen' := hm'.1; have hpos_lt := probePos_lt_buckets hbm k' s0
  refine ⟨s0, l0, hs0, hl0, ?_, hmod0, fun s' hs' => by have hp' := probePos_lt_buckets hbm k' s'; exact setCtrl_not_mem_empty (by omega) hne_emp (hprev0 s' hs')⟩
  rw [ctrlGroupAt_getElem? (by omega) hl0] at hlane0; injection hlane0 with hlane0_eq
  have hfull0 : isFullTag (getLane8 (ctrlGroupWord ctrl (probePos bm k' s0)) l0) = true := by rw [hlane0_eq]; exact isFullTag_h2Tag k'
  rw [ctrlGroupAt_getElem? (by omega) hl0]; congr 1; rcases hbm.buckets_cases with h4 | ⟨hge8, _⟩
  · have hm4 : CtrlMirrorInv 4 ctrl := h4 ▸ hm; have hm4' : CtrlMirrorInv 4 (setCtrl bm ctrl idx tag) := h4 ▸ hm'
    have hl4 := CtrlMirrorInv.lane_of_eq4 hm4 (pos := probePos bm k' s0) (j := l0) (by omega) hl0; have hl4' := CtrlMirrorInv.lane_of_eq4 hm4' (pos := probePos bm k' s0) (j := l0) (by omega) hl0
    by_cases hlt4 : probePos bm k' s0 + l0 < 4
    · have hm_ne : probePos bm k' s0 + l0 ≠ idx := by have : (probePos bm k' s0 + l0) % (bm.toNat + 1) = probePos bm k' s0 + l0 := Nat.mod_eq_of_lt (by omega); omega
      simp only [hl4, hl4', hlt4, ↓reduceIte] at hlane0_eq ⊢; rw [setCtrl_getElem_lt_buckets hbm hlen hidx (by omega)]; simp [hm_ne, hlane0_eq]
    · by_cases hlt8 : probePos bm k' s0 + l0 < 8
      · simp only [hl4, hlt4, hlt8, ↓reduceIte, isFullTag_tagEmpty] at hfull0; cases hfull0
      · simp only [hl4, hl4', hlt4, hlt8, ↓reduceIte] at hlane0_eq ⊢; have hmod4 : (probePos bm k' s0 + l0) % 4 = i := by rw [← h4]; exact hmod0
        simp only [hmod4] at hlane0_eq ⊢; rw [setCtrl_getElem_lt_buckets hbm hlen hidx hi_lt]; simp [hi_ne, hlane0_eq]
  · rw [CtrlMirrorInv.lane_eq_mod_of_ge8 hm' hge8 hpos_lt hl0]; simp only [hmod0]; rw [setCtrl_getElem_lt_buckets hbm hlen hidx hi_lt]; simp only [hi_ne, ↓reduceIte]
    rw [CtrlMirrorInv.lane_eq_mod_of_ge8 hm hge8 hpos_lt hl0] at hlane0_eq; simpa only [hmod0] using hlane0_eq
theorem ProbeReachable.of_setCtrl_eq4 {ctrl : List (BitVec 8)} (hm : CtrlMirrorInv 4 ctrl) {idx : Nat} (hidx : idx < 4) (k : BitVec 64) :
    ProbeReachable 3#64 (setCtrl 3#64 ctrl idx (h2Tag k)) k idx := by
  have hbm3 : ValidBucketMask 3#64 := ⟨2, by decide, by decide, rfl⟩
  have hm' : CtrlMirrorInv 4 (setCtrl 3#64 ctrl idx (h2Tag k)) := CtrlMirrorInv.setCtrl_preserves hbm3 hm hidx (ValidTag.of_h2Tag k)
  have hlen' : (setCtrl 3#64 ctrl idx (h2Tag k)).length = 12 := hm'.1; let pos := probePos 3#64 k 0; have hpos : pos < 4 := probePos_lt_buckets hbm3 k 0
  by_cases hle : pos ≤ idx
  · refine ⟨0, idx - pos, by simp [numGroups], by omega, ?_, by change (pos + (idx - pos)) % 4 = idx; rw [show pos + (idx - pos) = idx by omega, Nat.mod_eq_of_lt hidx], fun _ hs => by omega⟩
    rw [ctrlGroupAt_getElem? (by omega) (by omega), CtrlMirrorInv.lane_of_eq4 hm' hpos (by omega)]
    have h1 : pos + (idx - pos) < 4 := (by omega); have heq : pos + (idx - pos) = idx := by omega
    simp only [h1, ↓reduceIte]; congr 1; simp only [heq]; rw [setCtrl_getElem_lt_buckets hbm3 hm.1 hidx hidx]; simp
  · refine ⟨0, idx + 8 - pos, by simp [numGroups], by omega, ?_, by change (pos + (idx + 8 - pos)) % 4 = idx; omega, fun _ hs => by omega⟩
    rw [ctrlGroupAt_getElem? (by omega) (by omega), CtrlMirrorInv.lane_of_eq4 hm' hpos (by omega)]
    have h1 : ¬ (pos + (idx + 8 - pos) < 4) := (by omega); have h2 : ¬ (pos + (idx + 8 - pos) < 8) := (by omega); have hmod : (pos + (idx + 8 - pos)) % 4 = idx := by omega
    simp only [h1, h2, ↓reduceIte]; congr 1; simp only [hmod]; rw [setCtrl_getElem_lt_buckets hbm3 hm.1 hidx hidx]; simp
theorem ProbeReachable.of_setCtrl_ge8 {bm : BitVec 64} (hbm : ValidBucketMask bm) (hge8 : 8 ≤ bm.toNat + 1) {ctrl : List (BitVec 8)} (hm : CtrlMirrorInv (bm.toNat + 1) ctrl)
    {k : BitVec 64} {s_cand j_cand idx : Nat} (hs : s_cand < numGroups bm) (hj : j_cand < 8) (hmod : (probePos bm k s_cand + j_cand) % (bm.toNat + 1) = idx)
    (hprev : ∀ s' < s_cand, tagEmpty ∉ ctrlGroupAt ctrl (probePos bm k s')) : ProbeReachable bm (setCtrl bm ctrl idx (h2Tag k)) k idx := by
  have hidx : idx < bm.toNat + 1 := by rw [← hmod]; exact Nat.mod_lt _ (by omega)
  have hm' := CtrlMirrorInv.setCtrl_preserves hbm hm hidx (ValidTag.of_h2Tag k); have hlen := hm.1; have hlen' := hm'.1; have hpos_lt := probePos_lt_buckets hbm k s_cand
  refine ⟨s_cand, j_cand, hs, hj, ?_, hmod, fun s' hs' => by have hp' := probePos_lt_buckets hbm k s'; exact setCtrl_not_mem_empty (by omega) (h2Tag_ne_empty k) (hprev s' hs')⟩
  rw [ctrlGroupAt_getElem? (by omega) hj, CtrlMirrorInv.lane_eq_mod_of_ge8 hm' hge8 hpos_lt hj]; congr 1; simp only [hmod]; rw [setCtrl_getElem_lt_buckets hbm hlen hidx hidx]; simp
private theorem countP_set_balance (xs : List (BitVec 8)) {idx : Nat} (hidx : idx < xs.length) (y : BitVec 8) (p : BitVec 8 → Bool) :
    (xs.set idx y).countP p + (if p xs[idx] then 1 else 0) = xs.countP p + (if p y then 1 else 0) := by
  induction xs generalizing idx with
  | nil => simp at hidx
  | cons x rest ih => cases idx with
    | zero => simp only [List.set_cons_zero, List.getElem_cons_zero, List.countP_cons]; omega
    | succ k => have hrec := ih (by simp at hidx; omega : k < rest.length); simp only [List.set_cons_succ, List.getElem_cons_succ, List.countP_cons]; omega
private theorem take_setCtrl_eq_set {bm : BitVec 64} (hbm : ValidBucketMask bm) {ctrl : List (BitVec 8)} (hlen : ctrl.length = (bm.toNat + 1) + 8) {idx : Nat} (hidx : idx < bm.toNat + 1) (tag : BitVec 8) :
    (setCtrl bm ctrl idx tag).take (bm.toNat + 1) = (ctrl.take (bm.toNat + 1)).set idx tag := by
  refine List.ext_getElem (by simp [setCtrl_length, hlen]) fun i hi1 _ => ?_; have hi : i < bm.toNat + 1 := by simp [setCtrl_length, hlen] at hi1; exact hi1
  rw [List.getElem_take, setCtrl_getElem_lt_buckets hbm hlen hidx hi tag]; if hii : i = idx then subst hii; simp else rw [List.getElem_set_ne (Ne.symm hii), List.getElem_take]; simp [hii]
theorem SwissTableInv.overwrite_full {bm growthLeft items : BitVec 64} {ctrl : List (BitVec 8)} {slots : List (BitVec 64 × BitVec 64)} {m : Map64}
    (hinv : SwissTableInv bm growthLeft items ctrl slots m) {idx : Nat} (hidx : idx < bm.toNat + 1) {k v : BitVec 64}
    (hfull : isFullTag (ctrl[idx]'(by have := hinv.mirror.1; omega)) = true) (hk_eq : (slots[idx]'(by have := hinv.slots_len; omega)).1 = k) :
    let oldV := (slots[idx]'(by have := hinv.slots_len; omega)).2
    cliMapLookup k m = some oldV ∧ SwissTableInv bm growthLeft items ctrl (slots.set idx (k, v)) (cliMapInsert k v m) := by
  have hsl : slots.length = bm.toNat + 1 := hinv.slots_len; obtain ⟨h2_idx, hlook_idx, hreach_idx⟩ := hinv.full_sound idx hidx hfull; rw [hk_eq] at h2_idx hlook_idx hreach_idx
  have hlen_ins : (cliMapInsert k v m).length = m.length := cliMapInsert_length_of_lookup_some hinv.wf hlook_idx
  have key_set_eq : ∀ (i : Nat) (hi : i < bm.toNat + 1), ((slots.set idx (k, v))[i]'(by simp [hsl, hi])).1 = (slots[i]'(by omega)).1 :=
    fun i hi => if hii : i = idx then by subst hii; simp [hk_eq] else by simp [List.getElem_set_ne (Ne.symm hii)]
  refine ⟨hlook_idx,
    { validMask := hinv.validMask, wf := hinv.wf.insert k v, slots_len := by simp [hsl], mirror := hinv.mirror, items_eq := by rw [hlen_ins, hinv.items_eq],
      growth_le := hinv.growth_le, conservation := by rw [hlen_ins]; exact hinv.conservation, countFull_eq := by rw [hlen_ins]; exact hinv.countFull_eq,
      full_sound := fun i hi hfi => by
        rw [key_set_eq i hi]; by_cases hii : i = idx
        · subst hii; simp only [hk_eq, List.getElem_set_self]; exact ⟨h2_idx, cliMapLookup_insert_self k v m, hreach_idx⟩
        · obtain ⟨h2_i, hlook_i, hreach_i⟩ := hinv.full_sound i hi hfi
          have hne_k : (slots[i]'(by omega)).1 ≠ k := fun heq => hii (hinv.full_inj i idx hi hidx hfi hfull (heq.trans hk_eq.symm))
          simp only [List.getElem_set_ne (Ne.symm hii)]; exact ⟨h2_i, (cliMapLookup_insert_ne hne_k v m).trans hlook_i, hreach_i⟩,
      full_inj := fun i j hi hj hfi hfj heq => by rw [key_set_eq i hi, key_set_eq j hj] at heq; exact hinv.full_inj i j hi hj hfi hfj heq,
      complete := fun k' v' hlook' => by
        by_cases hkk : k' = k
        · subst hkk; rw [cliMapLookup_insert_self] at hlook'; injection hlook' with hv'; subst hv'; exact ⟨idx, hidx, hfull, by simp⟩
        · rw [cliMapLookup_insert_ne hkk] at hlook'; obtain ⟨i, hi, hfi, hsi⟩ := hinv.complete k' v' hlook'
          have hii : i ≠ idx := fun he => by subst he; rw [hsi] at hk_eq; exact hkk hk_eq
          exact ⟨i, hi, hfi, by simpa [List.getElem_set_ne (Ne.symm hii)] using hsi⟩ }⟩
theorem SwissTableInv.insert_new {bm growthLeft items : BitVec 64} {ctrl : List (BitVec 8)} {slots : List (BitVec 64 × BitVec 64)} {m : Map64}
    (hinv : SwissTableInv bm growthLeft items ctrl slots m) (hgl_pos : 0 < growthLeft.toNat) {k v : BitVec 64} (hnone : cliMapLookup k m = none)
    {idx : Nat} (hidx : idx < bm.toNat + 1) (hspec : isSpecialTag (ctrl[idx]'(by have := hinv.mirror.1; omega)) = true) (hreach_new : ProbeReachable bm (setCtrl bm ctrl idx (h2Tag k)) k idx) :
    let prevTag := ctrl[idx]'(by have := hinv.mirror.1; omega); let dec : BitVec 64 := if prevTag = tagEmpty then 1#64 else 0#64
    let gl' := growthLeft - dec; let items' := items + 1#64; let ctrl' := setCtrl bm ctrl idx (h2Tag k); let slots' := slots.set idx (k, v)
    SwissTableInv bm gl' items' ctrl' slots' (cliMapInsert k v m) ∧ (0 < gl'.toNat ∨ prevTag = tagEmpty) := by
  intro prevTag dec gl' items' ctrl' slots'; have hlen : ctrl.length = (bm.toNat + 1) + 8 := hinv.mirror.1; have hsl : slots.length = bm.toNat + 1 := hinv.slots_len
  have hmir' := CtrlMirrorInv.setCtrl_preserves hinv.validMask hinv.mirror hidx (ValidTag.of_h2Tag k); have hlen' : ctrl'.length = (bm.toNat + 1) + 8 := hmir'.1
  have hvt_prev : ValidTag prevTag := hinv.mirror.2.1 _ (List.getElem_mem _); have hprev_cases := hvt_prev.special_cases hspec
  have hnot_full_prev : isFullTag prevTag = false := by rcases hprev_cases with h | h <;> simp [h]
  have hlen_ins : (cliMapInsert k v m).length = m.length + 1 := cliMapInsert_length_of_lookup_none hnone
  have hcap_max : bucketMaskToCapacity bm ≤ MaxHashbrownCapacity := by
    obtain ⟨exp, hlo, hhi, hbm_eq⟩ := hinv.validMask; have hcap := ValidBucketMask.capacity_eq hlo hhi hbm_eq
    if he2 : exp = 2 then subst he2; simp at hcap; rw [hcap]; decide
    else simp [he2] at hcap; rw [hcap]; have : 2 ^ (exp - 3) ≤ 2 ^ 55 := Nat.pow_le_pow_right (by decide) (by omega); unfold MaxHashbrownCapacity; omega
  have hmax64 : MaxHashbrownCapacity < 2 ^ 64 := (by decide); have hcons0 := hinv.conservation
  have hitems_eq' : items' = BitVec.ofNat 64 (cliMapInsert k v m).length := by rw [hlen_ins]; dsimp only [items']; rw [hinv.items_eq, ← BitVec.ofNat_add]
  let pfx := ctrl.take (bm.toNat + 1); have hpfx_len : pfx.length = bm.toNat + 1 := by simp [pfx, hlen]
  have hpfx_idx : pfx[idx]'(by omega) = prevTag := by simp [pfx, prevTag, List.getElem_take]
  have htake' : ctrl'.take (bm.toNat + 1) = pfx.set idx (h2Tag k) := take_setCtrl_eq_set hinv.validMask hlen hidx (h2Tag k)
  have hfull_cnt : (ctrl'.take (bm.toNat + 1)).countP isFullTag = (cliMapInsert k v m).length := by
    rw [htake', hlen_ins]; have hb := countP_set_balance pfx (by omega : idx < pfx.length) (h2Tag k) isFullTag
    rw [hpfx_idx, hnot_full_prev, isFullTag_h2Tag, hinv.countFull_eq] at hb; simp only [Bool.false_eq_true, ↓reduceIte] at hb; omega
  have hcons_and_gl : gl'.toNat ≤ bucketMaskToCapacity bm ∧ (cliMapInsert k v m).length + ((ctrl'.take (bm.toNat + 1)).countP (· == tagDeleted)) + gl'.toNat = bucketMaskToCapacity bm ∧
      (0 < gl'.toNat ∨ prevTag = tagEmpty) := by
    rw [htake', hlen_ins]; have hb := countP_set_balance pfx (by omega : idx < pfx.length) (h2Tag k) (· == tagDeleted)
    have hh2_ndel : (h2Tag k == tagDeleted) = false := beq_eq_false_iff_ne.mpr (h2Tag_ne_deleted k); rw [hpfx_idx, hh2_ndel] at hb
    change m.length + pfx.countP (· == tagDeleted) + growthLeft.toNat = bucketMaskToCapacity bm at hcons0
    rcases hprev_cases with hemp | hdel
    · have hgl_toNat : gl'.toNat = growthLeft.toNat - 1 := by
        dsimp only [gl', dec]; simp only [hemp, ↓reduceIte]; rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; change 1 ≤ growthLeft.toNat; omega)]; simp
      have hp_del : (prevTag == tagDeleted) = false := by rw [hemp]; decide
      rw [hp_del] at hb; simp only [Bool.false_eq_true, ↓reduceIte] at hb; exact ⟨by omega, by omega, Or.inr hemp⟩
    · have hne_emp : prevTag ≠ tagEmpty := by rw [hdel]; decide
      have hgl_toNat : gl'.toNat = growthLeft.toNat := by dsimp only [gl', dec]; simp [hne_emp]
      have hp_del : (prevTag == tagDeleted) = true := by rw [hdel]; decide
      rw [hp_del] at hb; simp only [Bool.false_eq_true, ↓reduceIte] at hb; exact ⟨by omega, by omega, Or.inl (by omega)⟩
  have hctrl'_eq : ∀ (i : Nat) (hi : i < bm.toNat + 1), ctrl'[i]'(by omega) = if i = idx then h2Tag k else ctrl[i]'(by omega) :=
    fun i hi => setCtrl_getElem_lt_buckets hinv.validMask hlen hidx hi (h2Tag k)
  refine ⟨
    { validMask := hinv.validMask, wf := hinv.wf.insert k v, slots_len := by simp [slots', hsl], mirror := hmir',
      items_eq := hitems_eq', growth_le := hcons_and_gl.1, conservation := hcons_and_gl.2.1, countFull_eq := hfull_cnt,
      full_sound := fun i hi hfi => by
        by_cases hii : i = idx
        · subst hii; have hc_eq : ctrl'[i]'(by omega) = h2Tag k := by rw [hctrl'_eq i hi]; simp
          have hs_eq : slots'[i]'(by simp [slots', hsl, hi]) = (k, v) := by simp [slots']
          rw [hc_eq, hs_eq]; exact ⟨rfl, cliMapLookup_insert_self k v m, hreach_new⟩
        · have hc_eq : ctrl'[i]'(by omega) = ctrl[i]'(by omega) := by rw [hctrl'_eq i hi]; simp [hii]
          have hs_eq : slots'[i]'(by simp [slots', hsl, hi]) = slots[i]'(by omega) := by simp [slots', List.getElem_set_ne (Ne.symm hii)]
          rw [hc_eq] at hfi; obtain ⟨h2_i, hlook_i, hreach_i⟩ := hinv.full_sound i hi hfi
          have hne_k : (slots[i]'(by omega)).1 ≠ k := fun heq => by rw [heq, hnone] at hlook_i; cases hlook_i
          rw [hc_eq, hs_eq]; exact ⟨h2_i, (cliMapLookup_insert_ne hne_k v m).trans hlook_i, hreach_i.setCtrl_other hinv.validMask hinv.mirror hidx hii (ValidTag.of_h2Tag k) (h2Tag_ne_empty k)⟩,
      full_inj := fun i j hi hj hfi hfj heq => by
        by_cases hii : i = idx <;> by_cases hjj : j = idx
        · omega
        · subst hii; rw [hctrl'_eq j hj] at hfj; simp only [hjj, ↓reduceIte] at hfj; obtain ⟨_, hlook_j, _⟩ := hinv.full_sound j hj hfj
          have hk_j : k = (slots[j]'(by omega)).1 := by simpa [slots', List.getElem_set_ne (Ne.symm hjj)] using heq
          rw [← hk_j, hnone] at hlook_j; cases hlook_j
        · subst hjj; rw [hctrl'_eq i hi] at hfi; simp only [hii, ↓reduceIte] at hfi; obtain ⟨_, hlook_i, _⟩ := hinv.full_sound i hi hfi
          have hk_i : (slots[i]'(by omega)).1 = k := by simpa [slots', List.getElem_set_ne (Ne.symm hii)] using heq
          rw [hk_i, hnone] at hlook_i; cases hlook_i
        · rw [hctrl'_eq i hi] at hfi; simp only [hii, ↓reduceIte] at hfi; rw [hctrl'_eq j hj] at hfj; simp only [hjj, ↓reduceIte] at hfj
          exact hinv.full_inj i j hi hj hfi hfj (by simpa [slots', List.getElem_set_ne (Ne.symm hii), List.getElem_set_ne (Ne.symm hjj)] using heq),
      complete := fun k' v' hlook' => by
        by_cases hkk : k' = k
        · subst hkk; rw [cliMapLookup_insert_self] at hlook'; injection hlook' with hv'; subst hv'; exact ⟨idx, hidx, by rw [hctrl'_eq idx hidx]; simp, by simp [slots']⟩
        · rw [cliMapLookup_insert_ne hkk] at hlook'; obtain ⟨i, hi, hfi, hsi⟩ := hinv.complete k' v' hlook'
          have hii : i ≠ idx := fun he => by subst he; change isFullTag prevTag = true at hfi; rw [hnot_full_prev] at hfi; cases hfi
          exact ⟨i, hi, by rw [hctrl'_eq i hi]; simp [hii, hfi], by simpa [slots', List.getElem_set_ne (Ne.symm hii)] using hsi⟩ }, hcons_and_gl.2.2⟩
private theorem pointsToBytes_focus8_getElem (base : BitVec 64) (bs : List (BitVec 8)) {off : Nat} (h : off < bs.length) :
    (base ↦ₛ bs) = ((base + BitVec.ofNat 64 off) ↦₈ bs[off]) ∗ ((base ↦ₛ bs.take off) ∗ ((base + BitVec.ofNat 64 (off + 1)) ↦ₛ bs.drop (off + 1))) := by
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h] using pointsToBytes_focus8 base bs off h
private theorem pointsToBytes_update8 (base : BitVec 64) (bs : List (BitVec 8)) {off : Nat} (v : BitVec 8) (h : off < bs.length) :
    (((base + BitVec.ofNat 64 off) ↦₈ v) ∗ ((base ↦ₛ bs.take off) ∗ ((base + BitVec.ofNat 64 (off + 1)) ↦ₛ bs.drop (off + 1)))) = (base ↦ₛ bs.set off v) := by
  rw [← pointsToBytes_merge_at base bs off v h]; ac_rfl
private theorem setCtrlMirror_addr_eq (ctrlPtr bm : BitVec 64) (hbm : ValidBucketMask bm) {idx : Nat} :
    (ctrlPtr + ((BitVec.ofNat 64 idx - 8#64) &&& bm)) + 8#64 = ctrlPtr + BitVec.ofNat 64 (setCtrlMirrorIdx bm idx) := by
  have hmax := hbm.buckets_bounds_dvd.2.1; have hlt : ((BitVec.ofNat 64 idx - 8#64) &&& bm).toNat < bm.toNat + 1 := by rw [hbm.and_toNat_eq_mod]; exact Nat.mod_lt _ (by omega)
  have h64 : 2 ^ 58 + 8 < 2 ^ 64 := (by decide); have h8 : (8 : Nat) % 2 ^ 64 = 8 := by decide
  rw [BitVec.add_assoc]; congr 1; unfold setCtrlMirrorIdx; apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat, h8, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
section MachineProofs
arm64_proof_prelude
private theorem step_str8_perm {prog : Program} {target_pc pc ea : BitVec 64} {s : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {rt : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)} {val : BitVec 8} (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.str .B8 rt addr)) (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, wb)) (hval : (s.readReg64 rt).truncate 8 = val)
    (hstore : SepStore8 ea val P P') (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP prog target_pc (((applyWriteback s wb).setPC (pc + 4#64)).setMem m') P' post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm; let m' := s.mem.write8 ea val; have hm' := hstore.store hm; have hcan := hstore.writable hm; apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.str .B8 rt addr) s = ((applyWriteback s wb).setPC (pc + 4#64)).setMem m' := by
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStr, Memory.writeSized, applyWriteback, State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr, hval, hcan, MemWidth.bytes, hpc, m']
  rw [hstep]; exact SepWP.to_reaches_pc (hnext m' (Memory.perm_write8 s.mem ea val)) hm'
private theorem step_str64_perm {prog : Program} {target_pc pc ea val : BitVec 64} {s : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {rt : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)} (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.str .X64 rt addr)) (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, wb)) (hval : s.readReg64 rt = val)
    (hstore : SepStore64 ea val P P') (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP prog target_pc (((applyWriteback s wb).setPC (pc + 4#64)).setMem m') P' post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm; let m' := s.mem.write64 ea val; have hm' := hstore.store hm; have hcan := hstore.writable hm; apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.str .X64 rt addr) s = ((applyWriteback s wb).setPC (pc + 4#64)).setMem m' := by
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStr, Memory.writeSized, applyWriteback, State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr, hval, hcan, MemWidth.bytes, hpc, m']
  rw [hstep]; exact SepWP.to_reaches_pc (hnext m' (Memory.perm_write64 s.mem ea val)) hm'
private theorem step_stp64_perm {prog : Program} {target_pc pc ea ea2 v1 v2 : BitVec 64} {s : State} {P P1 P2 : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {rt1 rt2 : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)} (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.stp .W64 rt1 rt2 addr)) (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, wb)) (hea2 : ea + 8#64 = ea2)
    (hv1 : s.readReg64 rt1 = v1) (hv2 : s.readReg64 rt2 = v2) (hstore1 : SepStore64 ea v1 P P1) (hstore2 : SepStore64 ea2 v2 P1 P2)
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP prog target_pc (((applyWriteback s wb).setPC (pc + 4#64)).setMem m') P2 post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm; let m1 := s.mem.write64 ea v1; let m2 := m1.write64 ea2 v2
  have hm1 := hstore1.store hm; have hm2 := hstore2.store hm1; have hcan1 := hstore1.writable hm; have hcan2 := hstore2.writable hm1
  rw [Memory.canWrite_congr (Memory.perm_write64 _ _ _)] at hcan2; apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.stp .W64 rt1 rt2 addr) s = ((applyWriteback s wb).setPC (pc + 4#64)).setMem m2 := by
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStp, Memory.writeSized, applyWriteback, State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr, hea2, hv1, hv2, hcan1, hcan2, MemWidth.bytes, hpc, m1, m2]
  rw [hstep]; exact SepWP.to_reaches_pc (hnext m2 ((Memory.perm_write64 m1 ea2 v2).trans (Memory.perm_write64 s.mem ea v1))) hm2
private def hbInsertFrame (s0 : State) (vPad : BitVec 64) : SepProp :=
  ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x30) ∗ ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x23) ∗ ((s0.sp - 40#64) ↦₆₄ vPad) ∗
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)
private def HbUpperSaved (s0 s : State) : Prop :=
  s.readReg64 (.gpr 24#5) = s0.readReg64 (.gpr 24#5) ∧ s.readReg64 (.gpr 25#5) = s0.readReg64 (.gpr 25#5) ∧ s.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5) ∧
  s.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) ∧ s.readReg64 (.gpr 28#5) = s0.readReg64 (.gpr 28#5) ∧ calleeSavedVRegs s = calleeSavedVRegs s0
private theorem HbUpperSaved.trans_cs {s0 s1 s2 : State} (h01 : HbUpperSaved s0 s1) (h12 : CalleeSavedPreserved s1 s2) : HbUpperSaved s0 s2 :=
  ⟨h12.readReg64_x24.trans h01.1, h12.readReg64_x25.trans h01.2.1, h12.readReg64_x26.trans h01.2.2.1, h12.readReg64_x27.trans h01.2.2.2.1, h12.readReg64_x28.trans h01.2.2.2.2.1, h12.vregs.trans h01.2.2.2.2.2⟩
private theorem sepWP_seq_frozen {prog : Program} {mid target : BitVec 64} {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp} {Φ : Memory → Prop}
    (hst : ∀ m m', Φ m → m.KeepsFrozen m' → Φ m') (hΦ : Φ s.mem) (h : SepWP prog mid s P (fun sm Pm => Φ sm.mem → SepWP prog target sm Pm post oom) oom) : SepWP prog target s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm hL; rcases SepWP.to_reaches_pc h hm hL with ⟨sm, hst1, ⟨_, _, Pm, hmm, hcont⟩ | hoom⟩
  · obtain ⟨sf, hst2, hout⟩ := SepWP.to_reaches_pc (hcont (hst _ _ hΦ hst1.keepsFrozen)) hmm (hst1.codeLoaded hL); exact ⟨sf, hst1.trans hst2, hout⟩
  · exact ⟨sm, hst1, Or.inr hoom⟩
private theorem hbInsert_prologue (P : HbPlaced) (X : String → Option (State → State)) {target : BitVec 64} {s0 : State} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp} (hpc : s0.pc = P.pl5.base) (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hcont : ∀ (s1 : State) (vPad : BitVec 64), s1.pc = P.pl5.base + 20#64 → s1.status = .Running → s1.sp = s0.sp - 64#64 → s1.spAligned = true →
      s1.readReg64 .x0 = s0.readReg64 .x0 → s1.readReg64 .x1 = s0.readReg64 .x1 → s1.readReg64 .x2 = s0.readReg64 .x2 → s1.readReg64 Reg.lr = s0.readReg64 Reg.lr →
      HbUpperSaved s0 s1 → StdStatePreserved s0 s1 → SepWP ((hbProg5 P).rebase P.pl5.base X) target s1 (hbInsertFrame s0 vPad ∗ F) post oom) :
    SepWP ((hbProg5 P).rebase P.pl5.base X) target s0 (memRegion (s0.sp - 64#64) 64 ∗ F) post oom := by
  have hP := P.placeable5; have hb : (hbProg5 P).base = P.pl5.base := rfl; have hsp64 : ((s0.sp - 64#64) &&& 15#64 == 0#64) = true := State.spAligned_sub s0 64 hsp
  open_cells (s0.sp - 64#64) 64 8; rename_i c0 c1 c2 c3 c4 c5 c6 c7; rw [show s0.sp - 64#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 = s0.sp - 8#64 by bv_omega]
  refine step_stp64_perm (rt1 := .x29) (rt2 := .x30) (addr := .PreIndex .sp (-64#64)) (ea := s0.sp - 64#64) (ea2 := s0.sp - 56#64) (wb := some (.sp, s0.sp - 64#64)) hpc hrun (by simp) hsp
    (by show (s0.sp + -64#64, some (Reg.sp, s0.sp + -64#64)) = _; rw [show s0.sp + -64#64 = s0.sp - 64#64 by bv_omega]) (by bv_omega) rfl rfl (by wp_sep_access) (by wp_sep_access) fun m1 hm1 => ?_
  refine step_str64_perm (pc := P.pl5.base + 4#64) (rt := .x23) (addr := .Offset .sp 16#64) (ea := s0.sp - 48#64) (wb := none) (val := s0.readReg64 .x23) (by simp) (by simp [hrun]) (by simp)
    (by dsimp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, applyWriteback]; simpa [State.writeReg64_sp] using hsp64)
    (by show (s0.sp - 64#64 + 16#64, none) = _; rw [show s0.sp - 64#64 + 16#64 = s0.sp - 48#64 by bv_omega]) (by simp) (by wp_sep_access) fun m2 hm2 => ?_
  refine step_stp64_perm (pc := P.pl5.base + 8#64) (rt1 := .x22) (rt2 := .x21) (addr := .Offset .sp 32#64) (ea := s0.sp - 32#64) (ea2 := s0.sp - 24#64) (wb := none)
    (v1 := s0.readReg64 .x22) (v2 := s0.readReg64 .x21) (by simp) (by simp [hrun]) (by simp)
    (by dsimp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, applyWriteback]; simpa [State.writeReg64_sp] using hsp64)
    (by show (s0.sp - 64#64 + 32#64, none) = _; rw [show s0.sp - 64#64 + 32#64 = s0.sp - 32#64 by bv_omega]) (by bv_omega) (by simp) (by simp) (by wp_sep_access) (by wp_sep_access) fun m3 hm3 => ?_
  refine step_stp64_perm (pc := P.pl5.base + 12#64) (rt1 := .x20) (rt2 := .x19) (addr := .Offset .sp 48#64) (ea := s0.sp - 16#64) (ea2 := s0.sp - 8#64) (wb := none)
    (v1 := s0.readReg64 .x20) (v2 := s0.readReg64 .x19) (by simp) (by simp [hrun]) (by simp)
    (by dsimp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, applyWriteback]; simpa [State.writeReg64_sp] using hsp64)
    (by show (s0.sp - 64#64 + 48#64, none) = _; rw [show s0.sp - 64#64 + 48#64 = s0.sp - 16#64 by bv_omega]) (by bv_omega) (by simp) (by simp) (by wp_sep_access) (by wp_sep_access) fun m4 hm4 => ?_
  dsimp only [applyWriteback]; refine SepWP.weaken_pre (P' := hbInsertFrame s0 c3 ∗ F) (Entails.of_eq (by unfold hbInsertFrame; ac_rfl)) ?_
  rw [show P.pl5.base + 12#64 + 4#64 = P.pl5.base + 16#64 by simp]; wp_step
  exact hcont _ c3 (by simp) (by simp [hrun]) (by simp) (by simpa [State.spAligned] using hsp64) (by simp) (by simp) (by simp) (by simp)
    ⟨by simp, by simp, by simp, by simp, by simp, by simp [calleeSavedVRegs]⟩ ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp, fun a => by simpa using congrFun (hm4.trans (hm3.trans (hm2.trans hm1))) a⟩
private theorem hbInsert_epilogue (P : HbPlaced) (X : String → Option (State → State)) {s0 s : State} {vPad : BitVec 64} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp} (hpc : s.pc = P.pl5.base + 296#64) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 64#64) (hsp0 : s0.spAligned = true) (hup : HbUpperSaved s0 s)
    (hcont : ∀ sf : State, sf.pc = s0.readReg64 Reg.lr → sf.status = .Running → sf.sp = s0.sp → sf.readReg64 .x0 = s.readReg64 .x0 →
      sf.readReg64 .x1 = s.readReg64 .x1 → CalleeSavedPreserved s0 sf → StdStatePreserved s sf → post sf (memRegion (s0.sp - 64#64) 64 ∗ F)) :
    SepWP ((hbProg5 P).rebase P.pl5.base X) (s0.readReg64 Reg.lr) s (hbInsertFrame s0 vPad ∗ F) post oom := by
  have hP := P.placeable5; have hb : (hbProg5 P).base = P.pl5.base := rfl
  unfold hbInsertFrame
  wp_sym_steps; refine SepWP.weaken_pre (P' := memRegion (s0.sp - 64#64) 64 ∗ F) ?_ ?_
  · have hstk64 : hbInsertFrame s0 vPad ⊢ memRegion (s0.sp - 64#64) 64 := by
      unfold hbInsertFrame
      rw [show memRegion (s0.sp - 64#64) 64 = cells (s0.sp - 64#64) 8 from memRegion_cells (s0.sp - 64#64) 8 (by decide)]
      refine cells_sub_succ_entails 64 8 (cells_sub_succ_entails 56 7 (cells_sub_succ_entails 48 6 (cells_sub_succ_entails 40 5 (cells_sub_succ_entails 32 4 (cells_sub_succ_entails 24 3 (cells_sub_succ_entails 16 2 ?_))))))
      rw [cells_sub_succ s0.sp 8 1 (by decide) (by decide), Nat.sub_self, cells_zero]; exact Entails.sepExists_right _ (by rw [sepConj_emp]; exact Entails.refl _)
    unfold hbInsertFrame at hstk64
    exact Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono_left hstk64)
  · exact SepWP.done (by simp [Reg.lr]) (by simp [hrun]) (hcont _ (by simp [Reg.lr]) (by simp [hrun]) (by simp) (by simp) (by simp)
      ⟨by simp, by simp, by simp, by simp, by simp, by simpa using hup.1, by simpa using hup.2.1, by simpa using hup.2.2.1, by simpa using hup.2.2.2.1, by simpa using hup.2.2.2.2.1, by simp [Reg.fp], by simpa [calleeSavedVRegs] using hup.2.2.2.2.2⟩
      ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp, fun _ => rfl⟩)
private def ReadyFrame (s0 sr st : State) : Prop := st.sp = s0.sp - 64#64 ∧ HbUpperSaved s0 st ∧ StdStatePreserved sr st
@[local simp] private theorem readyFrame_setPC (s0 sr s : State) (pc : BitVec 64) : ReadyFrame s0 sr (s.setPC pc) ↔ ReadyFrame s0 sr s := by simp [ReadyFrame, HbUpperSaved, calleeSavedVRegs, StdStatePreserved]
@[local simp] private theorem readyFrame_advancePC (s0 sr s : State) : ReadyFrame s0 sr s.advancePC ↔ ReadyFrame s0 sr s := by simp [ReadyFrame, HbUpperSaved, calleeSavedVRegs, StdStatePreserved]
@[local simp] private theorem readyFrame_setPState (s0 sr s : State) (ps : PState) : ReadyFrame s0 sr (s.setPState ps) ↔ ReadyFrame s0 sr s := by simp [ReadyFrame, HbUpperSaved, calleeSavedVRegs, StdStatePreserved]
@[local simp] private theorem readyFrame_writeReg64 (s0 sr s : State) (idx : BitVec 5) (val : BitVec 64)
    (h24 : idx ≠ 24#5 ∧ idx ≠ 25#5 ∧ idx ≠ 26#5 ∧ idx ≠ 27#5 ∧ idx ≠ 28#5 := by decide) : ReadyFrame s0 sr (s.writeReg64 (.gpr idx) val) ↔ ReadyFrame s0 sr s := by
  have hne : ∀ k : BitVec 5, k ≠ idx → Reg.gpr k ≠ Reg.gpr idx := fun _ h e => by cases e; exact h rfl
  simp [ReadyFrame, HbUpperSaved, calleeSavedVRegs, StdStatePreserved, hne 24#5 h24.1.symm, hne 25#5 h24.2.1.symm, hne 26#5 h24.2.2.1.symm, hne 27#5 h24.2.2.2.1.symm, hne 28#5 h24.2.2.2.2.symm]
@[local simp] private theorem readyFrame_writeReg32 (s0 sr s : State) (idx : BitVec 5) (val : BitVec 32) (h24 : idx ≠ 24#5 ∧ idx ≠ 25#5 ∧ idx ≠ 26#5 ∧ idx ≠ 27#5 ∧ idx ≠ 28#5 := by decide) :
    ReadyFrame s0 sr (s.writeReg32 (.gpr idx) val) ↔ ReadyFrame s0 sr s := readyFrame_writeReg64 s0 sr s idx (val.zeroExtend 64) h24
@[local simp] private theorem readyFrame_writeVReg128 (s0 sr s : State) (v : BitVec 5) (val : BitVec 128) (hcs : isCalleeSavedVReg v = false := by decide) :
    ReadyFrame s0 sr (s.writeVReg128 v val) ↔ ReadyFrame s0 sr s := by
  have hv := (CalleeSavedPreserved_writeVReg128 s s v val hcs).mpr (CalleeSavedPreserved.rfl s) |>.vregs
  simp [ReadyFrame, HbUpperSaved, hv, StdStatePreserved]
@[local simp] private theorem readyFrame_writeVReg64 (s0 sr s : State) (v : BitVec 5) (val : BitVec 64) (hcs : isCalleeSavedVReg v = false := by decide) :
    ReadyFrame s0 sr (s.writeVReg64 v val) ↔ ReadyFrame s0 sr s := readyFrame_writeVReg128 s0 sr s v (val.zeroExtend 128) hcs
@[local simp] private theorem readyFrame_writeVReg32 (s0 sr s : State) (v : BitVec 5) (val : BitVec 32) (hcs : isCalleeSavedVReg v = false := by decide) :
    ReadyFrame s0 sr (s.writeVReg32 v val) ↔ ReadyFrame s0 sr s := readyFrame_writeVReg128 s0 sr s v (val.zeroExtend 128) hcs
local macro "rf_simp" h:term : tactic =>
  `(tactic| simp (discharger := decide) only [readyFrame_setPC, readyFrame_advancePC, readyFrame_setPState, readyFrame_writeReg64, readyFrame_writeReg32, readyFrame_writeVReg128, readyFrame_writeVReg64, readyFrame_writeVReg32, $h:term])
private theorem readyFrame_setMem (s0 sr s : State) (m : Memory) (hm : m.perm = s.mem.perm) : ReadyFrame s0 sr (s.setMem m) ↔ ReadyFrame s0 sr s :=
  ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, fun a => (congrFun hm a).symm.trans (h.2.2.2.2.2.2.2.2.2 a)⟩,
   fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, fun a => (congrFun hm a).trans (h.2.2.2.2.2.2.2.2.2 a)⟩⟩
private def U64MapRepFast (pl : Obj.Placement) (A : HbAlloc)
    (mapPtr : BitVec 64) (m : Map64) (bm : BitVec 64) (u : Nat) : SepProp :=
  ⌜mapPtr.toNat % 8 = 0 ∧ mapPtr.toNat + 32 ≤ 2 ^ 64 ∧ Map64Wf m ∧ bm ≠ 0#64⌝ ∗
  hbRodata pl ∗
  ∃∗ w : HbHeapMapWitness,
    ⌜SwissTableInv bm w.growthLeft w.items w.ctrl w.slots m ∧
     bucketMaskToCapacity bm - w.growthLeft.toNat ≤ u ∧
     0 < w.growthLeft.toNat ∧
     w.allocPtr ≠ 0#64 ∧
     w.allocPtr.toNat % 8 = 0 ∧
     w.allocPtr.toNat + (17 * (bm.toNat + 1) + 8) ≤ 2 ^ 64 ∧
     w.ctrlPtr = w.allocPtr + BitVec.ofNat 64 (16 * (bm.toNat + 1))⌝ ∗
    U64MapStruct mapPtr w.ctrlPtr bm w.growthLeft w.items ∗
    A.Block w.allocPtr (17 * (bm.toNat + 1) + 8) 8 ∗
    slotsDownFrom w.ctrlPtr w.slots ∗
    (w.ctrlPtr ↦ₛ w.ctrl)

private theorem U64MapRepReady_entails_U64MapRepFast (pl : Obj.Placement) (A : HbAlloc)
    (mapPtr : BitVec 64) (m : Map64) (bm : BitVec 64) {u : Nat} (hu : m.length ≤ u) :
    U64MapRepReady pl A mapPtr m bm ⊢ U64MapRepFast pl A mapPtr m bm u := by
  unfold U64MapRepReady U64MapRepFast
  apply Entails.pure_left; rintro ⟨hal, hnw, hwf, hbm⟩
  refine Entails.pure_right ⟨hal, hnw, hwf, hbm⟩ (sepConj_mono_right ?_)
  apply Entails.sepExists_elim; intro w
  apply Entails.pure_left; rintro ⟨hinv, hgl_pos, hgl_eq, ha_ne, ha_al, ha_nw, hctrl⟩
  have hused : bucketMaskToCapacity bm - w.growthLeft.toNat = m.length :=
    hinv.used_eq_length_of_sub hgl_eq
  exact Entails.sepExists_right w
    (Entails.pure_right ⟨hinv, by omega, hgl_pos, ha_ne, ha_al, ha_nw, hctrl⟩ (Entails.refl _))

private def hbReadyPost (pl : Obj.Placement) (A : HbAlloc) (s0 sr : State) (mapPtr k v bm : BitVec 64) (m : Map64) (u : Nat) (F : SepProp) (sf : State) (Pf : SepProp) : Prop :=
  (match cliMapLookup k m with | none => sf.readReg64 .x0 = 0#64 | some oldV => sf.readReg64 .x0 = 1#64 ∧ sf.readReg64 .x1 = oldV) ∧
  sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ StdStatePreserved sr sf ∧ (Pf ⊢ U64MapRep pl A mapPtr (cliMapInsert k v m) bm (u + 1) ∗ memRegion (s0.sp - 64#64) 64 ∗ F)
private theorem pack_U64MapRep_heap {pl : Obj.Placement} {A : HbAlloc} {mapPtr bm allocPtr ctrlPtr gl items : BitVec 64}
    {ctrl : List (BitVec 8)} {slots : List (BitVec 64 × BitVec 64)} {m' : Map64} {u' : Nat} (hal : mapPtr.toNat % 8 = 0) (hnw : mapPtr.toNat + 32 ≤ 2 ^ 64)
    (hinv' : SwissTableInv bm gl items ctrl slots m') (hu' : bucketMaskToCapacity bm - gl.toNat ≤ u')
    (ha_ne : allocPtr ≠ 0#64) (ha_al : allocPtr.toNat % 8 = 0) (ha_nw : allocPtr.toNat + (17 * (bm.toNat + 1) + 8) ≤ 2 ^ 64)
    (hctrl : ctrlPtr = allocPtr + BitVec.ofNat 64 (16 * (bm.toNat + 1))) :
    hbRodata pl ∗ U64MapStruct mapPtr ctrlPtr bm gl items ∗ A.Block allocPtr (17 * (bm.toNat + 1) + 8) 8 ∗ slotsDownFrom ctrlPtr slots ∗ (ctrlPtr ↦ₛ ctrl) ⊢ U64MapRep pl A mapPtr m' bm u' := by
  unfold U64MapRep
  simp only [hinv'.validMask.ne_zero, ↓reduceIte]; refine Entails.pure_right ⟨hal, hnw, hinv'.wf⟩ (sepConj_mono_right ?_)
  exact Entails.sepExists_right ⟨allocPtr, ctrlPtr, gl, items, ctrl, slots⟩ (Entails.pure_right ⟨hinv', hu', ha_ne, ha_al, ha_nw, hctrl⟩ (Entails.refl _))
private theorem hbInsert_overwrite (P : HbPlaced) (A : HbAlloc) (X : String → Option (State → State))
    {s0 sr s : State} {mapPtr k v bm vPad : BitVec 64} {m : Map64} {u : Nat} {w : HbHeapMapWitness} {idx : Nat} {F : SepProp} {oom : State → SepProp}
    (hal : mapPtr.toNat % 8 = 0) (hnw : mapPtr.toNat + 32 ≤ 2 ^ 64) (hsp0 : s0.spAligned = true) (hinv : SwissTableInv bm w.growthLeft w.items w.ctrl w.slots m)
    (hu : bucketMaskToCapacity bm - w.growthLeft.toNat ≤ u)
    (ha_ne : w.allocPtr ≠ 0#64) (ha_al : w.allocPtr.toNat % 8 = 0) (ha_nw : w.allocPtr.toNat + (17 * (bm.toNat + 1) + 8) ≤ 2 ^ 64)
    (hctrl_eq : w.ctrlPtr = w.allocPtr + BitVec.ofNat 64 (16 * (bm.toNat + 1))) (hidx : idx < bm.toNat + 1) (hidx_sl : idx < w.slots.length)
    (hfull_idx : isFullTag (w.ctrl[idx]'(by have := hinv.mirror.1; omega)) = true) (hkeq : (w.slots[idx]'hidx_sl).1 = k) (hpc : s.pc = P.pl5.base + 220#64)
    (hrun : s.status = .Running) (hrf : ReadyFrame s0 sr s) (hx2 : s.readReg64 .x2 = v) (hx16 : s.readReg64 (.gpr 16#5) = w.ctrlPtr - (BitVec.ofNat 64 idx <<< 4)) :
    SepWP ((hbProg5 P).rebase P.pl5.base X) (s0.readReg64 Reg.lr) s
      ((((w.ctrlPtr - (BitVec.ofNat 64 idx <<< 4)) + 0xfffffffffffffff0#64) ↦₆₄ (w.slots[idx]'hidx_sl).1) ∗ (((w.ctrlPtr - (BitVec.ofNat 64 idx <<< 4)) + 0xfffffffffffffff8#64) ↦₆₄ (w.slots[idx]'hidx_sl).2) ∗
       (slotsDownFrom w.ctrlPtr (w.slots.take idx) ∗ slotsDownFrom (slotAddr w.ctrlPtr idx) (w.slots.drop (idx + 1))) ∗
       hbRodata P.pl ∗ U64MapStruct mapPtr w.ctrlPtr bm w.growthLeft w.items ∗ A.Block w.allocPtr (17 * (bm.toNat + 1) + 8) 8 ∗ (w.ctrlPtr ↦ₛ w.ctrl) ∗ hbInsertFrame s0 vPad ∗ F)
      (hbReadyPost P.pl A s0 sr mapPtr k v bm m u F) oom := by
  have hP := P.placeable5; have hb : (hbProg5 P).base = P.pl5.base := rfl; obtain ⟨hlook, hinv'⟩ := hinv.overwrite_full (v := v) hidx hfull_idx hkeq
  have hpack := pack_U64MapRep_heap (A := A) (pl := P.pl) hal hnw hinv' (u' := u + 1) (by omega) ha_ne ha_al ha_nw hctrl_eq; clear hctrl_eq; wp_sym_steps 2
  refine step_str64_perm (pc := P.pl5.base + 228#64) (rt := .x2) (addr := .UnscaledOffset (.gpr 16#5) (-8#64)) (ea := (w.ctrlPtr - (BitVec.ofNat 64 idx <<< 4)) + 0xfffffffffffffff8#64) (wb := none) (val := v)
    (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun]) (by simp) rfl (by dsimp [evalAddrMode]; simp [wp_norm, arm64_norm, hx16]) (by simp [wp_norm, arm64_norm, hx2]) (by wp_sep_access) fun m1 hm1 => ?_
  dsimp only [applyWriteback]; rw [show P.pl5.base + 228#64 + 4#64 = P.pl5.base + 232#64 by simp]; wp_step
  have hsl_upd : (((w.ctrlPtr - (BitVec.ofNat 64 idx <<< 4)) + 0xfffffffffffffff0#64) ↦₆₄ (w.slots[idx]'hidx_sl).1) ∗ (((w.ctrlPtr - (BitVec.ofNat 64 idx <<< 4)) + 0xfffffffffffffff8#64) ↦₆₄ v) ∗
      (slotsDownFrom w.ctrlPtr (w.slots.take idx) ∗ slotsDownFrom (slotAddr w.ctrlPtr idx) (w.slots.drop (idx + 1))) = slotsDownFrom w.ctrlPtr (w.slots.set idx (k, v)) := by
    rw [hkeq, slotAddr_sub_lsl4_sub16 w.ctrlPtr idx, slotAddr_sub_lsl4_sub8 w.ctrlPtr idx]; simpa [slotPairAt, sepConj_assoc] using slotsDownFrom_update w.ctrlPtr w.slots hidx_sl (k, v)
  refine SepWP.weaken_pre (P' := hbInsertFrame s0 vPad ∗ ((hbRodata P.pl ∗ U64MapStruct mapPtr w.ctrlPtr bm w.growthLeft w.items ∗
      A.Block w.allocPtr (17 * (bm.toNat + 1) + 8) 8 ∗ slotsDownFrom w.ctrlPtr (w.slots.set idx (k, v)) ∗ (w.ctrlPtr ↦ₛ w.ctrl)) ∗ F)) (by rw [← hsl_upd]; exact Entails.of_eq (by ac_rfl)) ?_
  have hrf_end : ReadyFrame s0 sr ((((s.writeReg64 (.gpr 1#5) (w.slots[idx]'hidx_sl).2).writeReg64 (.gpr 0#5) 1#64).setPC (P.pl5.base + 296#64)).setMem m1) := by
    rw [readyFrame_setMem _ _ _ m1 (by simpa using hm1)]; rf_simp hrf
  refine hbInsert_epilogue P X (by simp) (by simp [wp_norm, arm64_norm, hrun]) hrf_end.1 hsp0 hrf_end.2.1
    fun sf _ _ hspf hx0f hx1f hcsf hstdf => ⟨?_, hspf, hcsf, StdStatePreserved.trans hrf_end.2.2 hstdf, Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono_left hpack)⟩
  rw [hlook]; exact ⟨by simpa [wp_norm, arm64_norm] using hx0f, by simpa [wp_norm, arm64_norm] using hx1f⟩

private theorem SwissTableInv.ctrl_len {bm gl items : BitVec 64} {ctrl : List (BitVec 8)} {slots : List (BitVec 64 × BitVec 64)} {m : Map64}
    (h : SwissTableInv bm gl items ctrl slots m) : ctrl.length = (bm.toNat + 1) + 8 := h.mirror.1
private theorem hbInsert_commitSlot (P : HbPlaced) (A : HbAlloc) (X : String → Option (State → State))
    {s0 sr s : State} {mapPtr k v bm vPad : BitVec 64} {m : Map64} {u : Nat} {w : HbHeapMapWitness} {idx : Nat} {F : SepProp} {oom : State → SepProp}
    (hal : mapPtr.toNat % 8 = 0) (hnw : mapPtr.toNat + 32 ≤ 2 ^ 64) (hsp0 : s0.spAligned = true) (hinv : SwissTableInv bm w.growthLeft w.items w.ctrl w.slots m)
    (hu : bucketMaskToCapacity bm - w.growthLeft.toNat ≤ u)
    (hgl_pos : 0 < w.growthLeft.toNat) (ha_ne : w.allocPtr ≠ 0#64) (ha_al : w.allocPtr.toNat % 8 = 0) (ha_nw : w.allocPtr.toNat + (17 * (bm.toNat + 1) + 8) ≤ 2 ^ 64)
    (hctrl_eq : w.ctrlPtr = w.allocPtr + BitVec.ofNat 64 (16 * (bm.toNat + 1))) (hnone : cliMapLookup k m = none) (hidx : idx < bm.toNat + 1)
    (hspec : isSpecialTag (w.ctrl[idx]'(by have := hinv.ctrl_len; omega)) = true) (hreach : ProbeReachable bm (setCtrl bm w.ctrl idx (h2Tag k)) k idx)
    (hpc : s.pc = P.pl5.base + 244#64) (hrun : s.status = .Running) (hrf : ReadyFrame s0 sr s) (hx0 : s.readReg64 .x0 = mapPtr) (hx1 : s.readReg64 .x1 = k)
    (hx2 : s.readReg64 .x2 = v) (hx8 : (s.readReg64 (.gpr 8#5)).truncate 8 = h2Tag k) (hx9 : s.readReg64 (.gpr 9#5) = w.ctrlPtr) (hx10 : s.readReg64 (.gpr 10#5) = bm)
    (hx11 : s.readReg64 (.gpr 11#5) = BitVec.ofNat 64 idx) (hx12 : s.readReg64 (.gpr 12#5) &&& 1#64 = if w.ctrl[idx]'(by have := hinv.ctrl_len; omega) = tagEmpty then 1#64 else 0#64) :
    SepWP ((hbProg5 P).rebase P.pl5.base X) (s0.readReg64 Reg.lr) s
      (hbRodata P.pl ∗ U64MapStruct mapPtr w.ctrlPtr bm w.growthLeft w.items ∗ A.Block w.allocPtr (17 * (bm.toNat + 1) + 8) 8 ∗ slotsDownFrom w.ctrlPtr w.slots ∗ (w.ctrlPtr ↦ₛ w.ctrl) ∗ hbInsertFrame s0 vPad ∗ F)
      (hbReadyPost P.pl A s0 sr mapPtr k v bm m u F) oom := by
  have hP := P.placeable5; have hb : (hbProg5 P).base = P.pl5.base := rfl; have hlen : w.ctrl.length = (bm.toNat + 1) + 8 := hinv.ctrl_len
  have hidx_sl : idx < w.slots.length := hinv.slots_len ▸ hidx
  have hmir_lt : setCtrlMirrorIdx bm idx < (w.ctrl.set idx (h2Tag k)).length := by rw [List.length_set, hlen]; exact (setCtrlMirrorIdx_bounds hinv.validMask hidx).1
  have hinv' := (hinv.insert_new (v := v) hgl_pos hnone hidx hspec hreach).1
  let dec := if w.ctrl[idx]'(by have := hinv.ctrl_len; omega) = tagEmpty then 1#64 else 0#64; let gl' := w.growthLeft - dec; let items' := w.items + 1#64
  have hu' : bucketMaskToCapacity bm - gl'.toNat ≤ u + 1 := by
    dsimp only [gl', dec]
    split
    · rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; change 1 ≤ w.growthLeft.toNat; omega)]; simp; omega
    · rw [BitVec.sub_zero]; omega
  have hpack := pack_U64MapRep_heap (A := A) (pl := P.pl) hal hnw hinv' hu' ha_ne ha_al ha_nw hctrl_eq; clear hctrl_eq hinv'; wp_sym_steps 2
  wp_conv_pre => rw [pointsToBytes_focus8_getElem w.ctrlPtr w.ctrl (off := idx) (by omega)]
  refine step_str8_perm (pc := P.pl5.base + 252#64) (ea := w.ctrlPtr + BitVec.ofNat 64 idx) (wb := none) (val := h2Tag k)
    (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun]) (by simp; exact ⟨rfl, rfl⟩) rfl
    (by dsimp [evalAddrMode, extendVal]; simp [wp_norm, arm64_norm, hx9, hx11]) (by simp [wp_norm, arm64_norm, hx8]) (by wp_sep_access) fun m1 hm1 => ?_
  dsimp only [applyWriteback]
  wp_conv_pre => rw [show ((w.ctrlPtr + BitVec.ofNat 64 idx) ↦₈ h2Tag k) ∗ ((w.ctrlPtr ↦ₛ w.ctrl.take idx) ∗ ((w.ctrlPtr + BitVec.ofNat 64 (idx + 1)) ↦ₛ w.ctrl.drop (idx + 1))) =
    (w.ctrlPtr ↦ₛ w.ctrl.set idx (h2Tag k)) from pointsToBytes_update8 w.ctrlPtr w.ctrl (h2Tag k) (by omega)]
  rw [show P.pl5.base + 252#64 + 4#64 = P.pl5.base + 256#64 by simp]
  wp_conv_pre => unfold U64MapStruct
  wp_sym_steps 4
  wp_conv_pre => rw [pointsToBytes_focus8_getElem w.ctrlPtr (w.ctrl.set idx (h2Tag k)) (off := setCtrlMirrorIdx bm idx) hmir_lt]
  refine step_str8_perm (pc := P.pl5.base + 272#64) (ea := w.ctrlPtr + BitVec.ofNat 64 (setCtrlMirrorIdx bm idx)) (wb := none) (val := h2Tag k)
    (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun]) (by simp; exact ⟨rfl, rfl⟩) rfl
    (by dsimp [evalAddrMode]; simp [wp_norm, arm64_norm]; exact setCtrlMirror_addr_eq w.ctrlPtr bm hinv.validMask) (by simp [wp_norm, arm64_norm, hx8]) (by wp_sep_access) fun m2 hm2 => ?_
  dsimp only [applyWriteback]
  wp_conv_pre => rw [show ((w.ctrlPtr + BitVec.ofNat 64 (setCtrlMirrorIdx bm idx)) ↦₈ h2Tag k) ∗ ((w.ctrlPtr ↦ₛ (w.ctrl.set idx (h2Tag k)).take (setCtrlMirrorIdx bm idx)) ∗
      ((w.ctrlPtr + BitVec.ofNat 64 (setCtrlMirrorIdx bm idx + 1)) ↦ₛ (w.ctrl.set idx (h2Tag k)).drop (setCtrlMirrorIdx bm idx + 1))) =
    (w.ctrlPtr ↦ₛ setCtrl bm w.ctrl idx (h2Tag k)) from pointsToBytes_update8 w.ctrlPtr (w.ctrl.set idx (h2Tag k)) (h2Tag k) hmir_lt]
  rw [show P.pl5.base + 272#64 + 4#64 = P.pl5.base + 276#64 by simp]; wp_sym_steps 2
  wp_conv_pre => rw [slotsDownFrom_focus_ldur w.ctrlPtr w.slots hidx_sl]
  refine step_stp64_perm (pc := P.pl5.base + 284#64) (ea := (w.ctrlPtr - (BitVec.ofNat 64 idx <<< 4)) + 0xfffffffffffffff0#64)
    (ea2 := (w.ctrlPtr - (BitVec.ofNat 64 idx <<< 4)) + 0xfffffffffffffff8#64) (wb := none) (v1 := k) (v2 := v)
    (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun]) (by simp; exact ⟨rfl, rfl, rfl⟩) rfl (by dsimp [evalAddrMode]; simp [wp_norm, arm64_norm])
    (by bv_omega) (by simp [wp_norm, arm64_norm, hx1]) (by simp [wp_norm, arm64_norm, hx2]) (by wp_sep_access) (by wp_sep_access) fun m3 hm3 => ?_
  dsimp only [applyWriteback]; rw [show P.pl5.base + 284#64 + 4#64 = P.pl5.base + 288#64 by simp]
  refine step_stp64_perm (pc := P.pl5.base + 288#64) (ea := mapPtr + 16#64) (ea2 := mapPtr + 24#64) (wb := none) (v1 := gl') (v2 := items')
    (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun]) (by simp; exact ⟨rfl, rfl, rfl⟩) rfl (by dsimp [evalAddrMode]; simp [wp_norm, arm64_norm, hx0])
    (by bv_omega) (by simp [wp_norm, arm64_norm, gl', dec]) (by simp [wp_norm, arm64_norm, items']) (by wp_sep_access) (by wp_sep_access) fun m4 hm4 => ?_
  dsimp only [applyWriteback]; rw [show P.pl5.base + 288#64 + 4#64 = P.pl5.base + 292#64 by simp]; wp_step
  have hsl_upd : (((w.ctrlPtr - (BitVec.ofNat 64 idx <<< 4)) + 0xfffffffffffffff0#64) ↦₆₄ k) ∗ (((w.ctrlPtr - (BitVec.ofNat 64 idx <<< 4)) + 0xfffffffffffffff8#64) ↦₆₄ v) ∗
      (slotsDownFrom w.ctrlPtr (w.slots.take idx) ∗ slotsDownFrom (slotAddr w.ctrlPtr idx) (w.slots.drop (idx + 1))) = slotsDownFrom w.ctrlPtr (w.slots.set idx (k, v)) := by
    rw [slotAddr_sub_lsl4_sub16 w.ctrlPtr idx, slotAddr_sub_lsl4_sub8 w.ctrlPtr idx]; simpa [slotPairAt, sepConj_assoc] using slotsDownFrom_update w.ctrlPtr w.slots hidx_sl (k, v)
  refine SepWP.weaken_pre (P' := hbInsertFrame s0 vPad ∗ ((hbRodata P.pl ∗ U64MapStruct mapPtr w.ctrlPtr bm gl' items' ∗ A.Block w.allocPtr (17 * (bm.toNat + 1) + 8) 8 ∗
      slotsDownFrom w.ctrlPtr (w.slots.set idx (k, v)) ∗ (w.ctrlPtr ↦ₛ setCtrl bm w.ctrl idx (h2Tag k))) ∗ F)) (by
      unfold U64MapStruct
      rw [← hsl_upd]; exact Entails.of_eq (by ac_rfl)) ?_
  have hp1 : m1.perm = s.mem.perm := (by simpa using hm1); have hp2 : m2.perm = s.mem.perm := by simpa [hp1] using hm2
  have hp3 : m3.perm = s.mem.perm := (by simpa [hp2] using hm3); have hp4 : m4.perm = s.mem.perm := by simpa [hp3] using hm4
  refine hbInsert_epilogue P X (by simp) (by simp [wp_norm, arm64_norm, hrun]) (by simp [hrf.1]) hsp0
    (by suffices hrf4 : ReadyFrame s0 sr _ from hrf4.2.1; rw [readyFrame_setMem _ _ _ m4 (by simp [hp4])]; rf_simp hrf)
    fun sf _ _ hspf hx0f _ hcsf hstdf => ⟨by rw [hnone]; simpa [wp_norm, arm64_norm] using hx0f, hspf, hcsf,
      StdStatePreserved.trans (by suffices hrf4 : ReadyFrame s0 sr _ from hrf4.2.2; rw [readyFrame_setMem _ _ _ m4 (by simp [hp4])]; rf_simp hrf) hstdf,
      Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono_left hpack)⟩
private theorem hbInsert_selectAndCommit (P : HbPlaced) (A : HbAlloc) (X : String → Option (State → State))
    {s0 sr s : State} {mapPtr k v bm vPad : BitVec 64} {m : Map64} {u : Nat} {w : HbHeapMapWitness} {candIdx : Nat} {F : SepProp} {oom : State → SepProp}
    (hal : mapPtr.toNat % 8 = 0) (hnw : mapPtr.toNat + 32 ≤ 2 ^ 64) (hsp0 : s0.spAligned = true) (hinv : SwissTableInv bm w.growthLeft w.items w.ctrl w.slots m)
    (hu : bucketMaskToCapacity bm - w.growthLeft.toNat ≤ u)
    (hgl_pos : 0 < w.growthLeft.toNat) (ha_ne : w.allocPtr ≠ 0#64) (ha_al : w.allocPtr.toNat % 8 = 0) (ha_nw : w.allocPtr.toNat + (17 * (bm.toNat + 1) + 8) ≤ 2 ^ 64)
    (hctrl_eq : w.ctrlPtr = w.allocPtr + BitVec.ofNat 64 (16 * (bm.toNat + 1))) (hnone : cliMapLookup k m = none) (hcand : candIdx < bm.toNat + 1)
    (hreach : ProbeReachable bm (setCtrl bm w.ctrl candIdx (h2Tag k)) k candIdx) (h4_if_full : isSpecialTag (w.ctrl[candIdx]'(by have := hinv.ctrl_len; omega)) = false → bm = 3#64)
    (hpc : s.pc = P.pl5.base + 236#64) (hrun : s.status = .Running) (hrf : ReadyFrame s0 sr s) (hx0 : s.readReg64 .x0 = mapPtr) (hx1 : s.readReg64 .x1 = k)
    (hx2 : s.readReg64 .x2 = v) (hx8 : (s.readReg64 (.gpr 8#5)).truncate 8 = h2Tag k) (hx9 : s.readReg64 (.gpr 9#5) = w.ctrlPtr)
    (hx10 : s.readReg64 (.gpr 10#5) = bm) (hx11 : s.readReg64 (.gpr 11#5) = BitVec.ofNat 64 candIdx) :
    SepWP ((hbProg5 P).rebase P.pl5.base X) (s0.readReg64 Reg.lr) s
      (hbRodata P.pl ∗ U64MapStruct mapPtr w.ctrlPtr bm w.growthLeft w.items ∗ A.Block w.allocPtr (17 * (bm.toNat + 1) + 8) 8 ∗ slotsDownFrom w.ctrlPtr w.slots ∗ (w.ctrlPtr ↦ₛ w.ctrl) ∗ hbInsertFrame s0 vPad ∗ F)
      (hbReadyPost P.pl A s0 sr mapPtr k v bm m u F) oom := by
  have hP := P.placeable5; have hb : (hbProg5 P).base = P.pl5.base := rfl; have hlen : w.ctrl.length = (bm.toNat + 1) + 8 := hinv.ctrl_len
  have hctrl_fn : True → w.ctrlPtr = w.allocPtr + BitVec.ofNat 64 (16 * (bm.toNat + 1)) := fun _ => hctrl_eq; clear hctrl_eq
  have htag_v : ValidTag (w.ctrl[candIdx]'(by have := hinv.ctrl_len; omega)) := hinv.mirror.2.1 _ (List.getElem_mem _)
  wp_conv_pre => rw [pointsToBytes_focus8_getElem w.ctrlPtr w.ctrl (off := candIdx) (by have := hinv.ctrl_len; omega)]
  set_option proofLib.wpBranchAutoDecide false in wp_sym_steps 2
  wp_conv_pre => rw [← pointsToBytes_focus8_getElem w.ctrlPtr w.ctrl (off := candIdx) (by have := hinv.ctrl_len; omega)]
  wp_if htbz
  · have hnspec : isSpecialTag (w.ctrl[candIdx]'(by have := hinv.ctrl_len; omega)) = false :=
      htag_v.elim (fun heq => by simp [heq, tagEmpty] at htbz) fun h => h.elim (fun heq => by simp [heq, tagDeleted] at htbz)
        fun hlt => Bool.eq_false_iff.mpr fun hs => by have := (isSpecialTag_iff_ge_0x80 _).mp hs; omega
    have hbm3 : bm = 3#64 := h4_if_full hnspec; have hbm4 : bm.toNat + 1 = 4 := by rw [hbm3]; decide
    obtain ⟨ei, hei_lt, hei_emp⟩ := hinv.exists_empty_slot; have hei4 : ei < 4 := by omega
    have hsb_ei : (specialBits8 (ctrlGroupWord w.ctrl 0)).getLsbD ei = true := by
      rw [getLsbD_specialBits8 _ (by omega), getLane8_ctrlGroupWord_eq_getElem (ctrl := w.ctrl) (pos := 0) (j := ei) (by omega) (by omega)]; simp [hei_emp, tagEmpty, isSpecialTag]
    have hsb_ne : specialBits8 (ctrlGroupWord w.ctrl 0) ≠ 0#8 := fun hz => by rw [hz] at hsb_ei; simp at hsb_ei
    rcases bv8_ctz_spec hsb_ne with ⟨hfix8, hfix_bit, hfix_lo⟩; obtain ⟨fixIdx, hfix_eq⟩ : ∃ n, (specialBits8 (ctrlGroupWord w.ctrl 0)).ctz.toNat = n := ⟨_, rfl⟩
    rw [hfix_eq] at hfix8 hfix_bit hfix_lo
    have hfix4 : fixIdx < 4 := Classical.byContradiction fun hge => Bool.false_ne_true ((hfix_lo ei (by omega)).symm.trans hsb_ei)
    have hfix_lt : fixIdx < bm.toNat + 1 := by omega
    have hfix_spec : isSpecialTag (w.ctrl[fixIdx]'(by have := hinv.ctrl_len; omega)) = true := by
      have hlane := hfix_bit; rw [getLsbD_specialBits8 _ hfix8, getLane8_ctrlGroupWord_eq_getElem (ctrl := w.ctrl) (pos := 0) (j := fixIdx) (by omega) hfix8] at hlane; simpa using hlane
    have hreach_fix : ProbeReachable bm (setCtrl bm w.ctrl fixIdx (h2Tag k)) k fixIdx := by subst hbm3; exact ProbeReachable.of_setCtrl_eq4 (by simpa using hinv.mirror) hfix4 k
    wp_conv_pre => rw [pointsToBytes_focus_ctrlGroupWord w.ctrlPtr w.ctrl (pos := 0) (by omega)]
    wp_sym_steps 2
    wp_conv_pre => rw [← pointsToBytes_focus_ctrlGroupWord w.ctrlPtr w.ctrl (pos := 0) (by omega)]
    have hcmlt := simd_cmlt_zero8 (ctrlGroupWord w.ctrl 0)
    conv at hcmlt => lhs; simp only [wp_norm, arm64_norm]
    rw [hcmlt]; clear hcmlt; wp_sym_steps 4
    have htr64 : BitVec.setWidth 64 (BitVec.zeroExtend 128 (byteMaskOfBits (specialBits8 (ctrlGroupWord w.ctrl 0)))) = byteMaskOfBits (specialBits8 (ctrlGroupWord w.ctrl 0)) := by simp [BitVec.zeroExtend]
    rw [htr64, ProofLib.reverseBits_eq_reverse, byteMaskOfBits_lowestLane, hfix_eq]
    wp_conv_pre => rw [pointsToBytes_focus8_getElem w.ctrlPtr w.ctrl (off := fixIdx) (by have := hinv.ctrl_len; omega)]
    wp_sym_steps 2
    wp_conv_pre => rw [← pointsToBytes_focus8_getElem w.ctrlPtr w.ctrl (off := fixIdx) (by have := hinv.ctrl_len; omega)]
    refine hbInsert_commitSlot P A X hal hnw hsp0 hinv hu hgl_pos ha_ne ha_al ha_nw (hctrl_fn trivial) hnone hfix_lt hfix_spec hreach_fix
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun]) (by rf_simp hrf) (by simp [wp_norm, arm64_norm, hx0]) (by simp [wp_norm, arm64_norm, hx1])
      (by simp [wp_norm, arm64_norm, hx2]) (by simp [wp_norm, arm64_norm, hx8]) (by simp [wp_norm, arm64_norm, hx9]) (by simp [wp_norm, arm64_norm, hx10]) (by simp [wp_norm, arm64_norm]) ?_
    rcases ValidTag.special_cases (hinv.mirror.2.1 _ (List.getElem_mem _)) hfix_spec with heq | heq <;> simp [wp_norm, arm64_norm, heq, tagEmpty, tagDeleted]
  · have hspec : isSpecialTag (w.ctrl[candIdx]'(by have := hinv.ctrl_len; omega)) = true :=
      htag_v.elim (fun heq => by simp [heq, tagEmpty, isSpecialTag]) fun h => h.elim (fun heq => by simp [heq, tagDeleted, isSpecialTag]) fun hlt => by
        have hlt8 : w.ctrl[candIdx]'(by have := hinv.ctrl_len; omega) < 0x80#8 := by rw [BitVec.lt_def]; change _ < 128; omega
        exfalso; apply htbz; bv_robdd
    refine hbInsert_commitSlot P A X hal hnw hsp0 hinv hu hgl_pos ha_ne ha_al ha_nw (hctrl_fn trivial) hnone hcand hspec hreach
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun]) (by rf_simp hrf) (by simp [wp_norm, arm64_norm, hx0]) (by simp [wp_norm, arm64_norm, hx1])
      (by simp [wp_norm, arm64_norm, hx2]) (by simp [wp_norm, arm64_norm, hx8]) (by simp [wp_norm, arm64_norm, hx9]) (by simp [wp_norm, arm64_norm, hx10]) (by simp [wp_norm, arm64_norm, hx11]) ?_
    rcases ValidTag.special_cases htag_v hspec with heq | heq <;> simp [wp_norm, arm64_norm, heq, tagEmpty, tagDeleted]
private theorem extend_probe_prev {ctrl : List (BitVec 8)} {slots : List (BitVec 64 × BitVec 64)} {bm k : BitVec 64} {step : Nat}
    (hprev : ∀ s < step, ∀ j < 8, getLane8 (ctrlGroupWord ctrl (probePos bm k s)) j = h2Tag k → (h : (probePos bm k s + j) % (bm.toNat + 1) < slots.length) → (slots[(probePos bm k s + j) % (bm.toNat + 1)]'h).1 ≠ k)
    (hno_h2 : ∀ j < 8, getLane8 (ctrlGroupWord ctrl (probePos bm k step)) j = h2Tag k → (h : (probePos bm k step + j) % (bm.toNat + 1) < slots.length) → (slots[(probePos bm k step + j) % (bm.toNat + 1)]'h).1 ≠ k) :
    ∀ s < step + 1, ∀ j < 8, getLane8 (ctrlGroupWord ctrl (probePos bm k s)) j = h2Tag k → (h : (probePos bm k s + j) % (bm.toNat + 1) < slots.length) → (slots[(probePos bm k s + j) % (bm.toNat + 1)]'h).1 ≠ k :=
  fun s hs j hj htag hsl => if hlt : s < step then hprev s hlt j hj htag hsl else by have : s = step := (by omega); subst this; exact hno_h2 j hj htag hsl
private theorem probe_empty_miss_lookup {bm gl items : BitVec 64} {ctrl : List (BitVec 8)} {slots : List (BitVec 64 × BitVec 64)} {map : Map64}
    (hinv : SwissTableInv bm gl items ctrl slots map) {k : BitVec 64} {step : Nat} (hemp_ne : eqBits8 (ctrlGroupWord ctrl (probePos bm k step)) tagEmpty ≠ 0#8)
    (hprev : ∀ s < step, ∀ j < 8, getLane8 (ctrlGroupWord ctrl (probePos bm k s)) j = h2Tag k → (h : (probePos bm k s + j) % (bm.toNat + 1) < slots.length) → (slots[(probePos bm k s + j) % (bm.toNat + 1)]'h).1 ≠ k)
    (hno_h2 : ∀ j < 8, getLane8 (ctrlGroupWord ctrl (probePos bm k step)) j = h2Tag k → (h : (probePos bm k step + j) % (bm.toNat + 1) < slots.length) → (slots[(probePos bm k step + j) % (bm.toNat + 1)]'h).1 ≠ k) :
    cliMapLookup k map = none := by
  rcases (bv8_ne_zero_iff_exists _).1 hemp_ne with ⟨je, hje, hbit_e⟩; rw [getLsbD_eqBits8 _ tagEmpty hje, beq_iff_eq] at hbit_e
  have hpos_lt := probePos_lt_buckets hinv.validMask k step; have hlen := hinv.ctrl_len
  exact hinv.lookup_eq_none_of_probe_empty ((mem_ctrlGroupAt_iff (by omega) tagEmpty).2 ⟨je, hje, hbit_e⟩) fun s hs j hj htag => extend_probe_prev hprev hno_h2 s (by omega) j hj htag _
private theorem probe_nonempty_facts {bm gl items : BitVec 64} {ctrl : List (BitVec 8)} {slots : List (BitVec 64 × BitVec 64)} {map : Map64}
    (hinv : SwissTableInv bm gl items ctrl slots map) {k : BitVec 64} {step step_end : Nat} (hstep_le : step ≤ step_end)
    (hemp_end : tagEmpty ∈ ctrlGroupAt ctrl (probePos bm k step_end)) (hemp_eq : eqBits8 (ctrlGroupWord ctrl (probePos bm k step)) tagEmpty = 0#8) :
    tagEmpty ∉ ctrlGroupAt ctrl (probePos bm k step) ∧ step < step_end := by
  have hpos_lt := probePos_lt_buckets hinv.validMask k step; have hlen := hinv.ctrl_len
  have hnot_mem : tagEmpty ∉ ctrlGroupAt ctrl (probePos bm k step) := fun hm => by
    rcases (mem_ctrlGroupAt_iff (by omega) tagEmpty).1 hm with ⟨je, hje, hlane_e⟩
    have hbit_e := (bv8_eq_zero_iff_forall _).1 hemp_eq je hje; rw [getLsbD_eqBits8 _ _ hje, beq_eq_false_iff_ne] at hbit_e; exact hbit_e hlane_e
  exact ⟨hnot_mem, Classical.byContradiction fun hge => hnot_mem ((show step = step_end by omega) ▸ hemp_end)⟩
private theorem clear_lowest_miss {g bm k : BitVec 64} {slots : List (BitVec 64 × BitVec 64)} {pos : Nat} {b : BitVec 8}
    {hidx : (pos + b.ctz.toNat) % (bm.toNat + 1) < slots.length} (hk_ne : (slots[(pos + b.ctz.toNat) % (bm.toNat + 1)]'hidx).1 ≠ k)
    (hmiss_b : ∀ j < 8, getLane8 g j = h2Tag k → b.getLsbD j = false → (h : (pos + j) % (bm.toNat + 1) < slots.length) → (slots[(pos + j) % (bm.toNat + 1)]'h).1 ≠ k) :
    ∀ j < 8, getLane8 g j = h2Tag k → ((b - 1#8) &&& b).getLsbD j = false → (h : (pos + j) % (bm.toNat + 1) < slots.length) → (slots[(pos + j) % (bm.toNat + 1)]'h).1 ≠ k := fun j hj htag hbf' hsl => by
  rw [bv8_getLsbD_clear_lowest b hj] at hbf'; by_cases hbj : b.getLsbD j = true
  · rw [hbj, Bool.true_and, decide_eq_false_iff_not, Classical.not_not] at hbf'; subst hbf'; exact hk_ne
  · exact hmiss_b j hj htag (Bool.eq_false_iff.2 hbj) hsl
private def CandInv {bm : BitVec 64} {w : HbHeapMapWitness} {m : Map64} (hinv : SwissTableInv bm w.growthLeft w.items w.ctrl w.slots m) (k x13 x11 : BitVec 64) : Prop :=
  x13 = 0#64 ∨ (x13 = 1#64 ∧ 8 ≤ bm.toNat + 1 ∧ ∃ (candIdx : Nat) (_ : candIdx < bm.toNat + 1),
    x11 = BitVec.ofNat 64 candIdx ∧ isSpecialTag (w.ctrl[candIdx]'(by have := hinv.ctrl_len; omega)) = true ∧ ProbeReachable bm (setCtrl bm w.ctrl candIdx (h2Tag k)) k candIdx)
private def InsertProbeInv (s0 sr : State) {bm : BitVec 64} {w : HbHeapMapWitness} {m : Map64}
    (hinv : SwissTableInv bm w.growthLeft w.items w.ctrl w.slots m) (mapPtr k v : BitVec 64) (step : Nat) (st : State) : Prop :=
  ReadyFrame s0 sr st ∧ st.readReg64 .x0 = mapPtr ∧ st.readReg64 .x1 = k ∧ st.readReg64 .x2 = v ∧ (st.readReg64 (.gpr 8#5)).truncate 8 = h2Tag k ∧ st.readReg64 (.gpr 9#5) = w.ctrlPtr ∧
  st.readReg64 (.gpr 10#5) = bm ∧ st.readReg64 (.gpr 12#5) = BitVec.ofNat 64 (8 * step) ∧ (st.readReg64 (.gpr 20#5) &&& bm) = BitVec.ofNat 64 (probePos bm k step) ∧
  st.readVReg128 0#5 = dupByte8Vec ((k * fxSeed) >>> 57) ∧ st.readVReg128 1#5 = 0xffffffffffffffffffffffffffffffff#128 ∧ CandInv hinv k (st.readReg64 (.gpr 13#5)) (st.readReg64 (.gpr 11#5)) ∧
  (∀ s < step, tagEmpty ∉ ctrlGroupAt w.ctrl (probePos bm k s)) ∧ (∀ s < step, ∀ j < 8, getLane8 (ctrlGroupWord w.ctrl (probePos bm k s)) j = h2Tag k →
    (h : (probePos bm k s + j) % (bm.toNat + 1) < w.slots.length) → (w.slots[(probePos bm k s + j) % (bm.toNat + 1)]'h).1 ≠ k)
private def InsertInnerInv (s0 sr : State) {bm : BitVec 64} {w : HbHeapMapWitness} {m : Map64}
    (hinv : SwissTableInv bm w.growthLeft w.items w.ctrl w.slots m) (mapPtr k v : BitVec 64) (step : Nat) (b : BitVec 8) (st : State) : Prop :=
  let pos := probePos bm k step; let g := ctrlGroupWord w.ctrl pos
  b ≠ 0#8 ∧ ReadyFrame s0 sr st ∧ st.readReg64 .x0 = mapPtr ∧ st.readReg64 .x1 = k ∧ st.readReg64 .x2 = v ∧
  (st.readReg64 (.gpr 8#5)).truncate 8 = h2Tag k ∧ st.readReg64 (.gpr 9#5) = w.ctrlPtr ∧ st.readReg64 (.gpr 10#5) = bm ∧
  st.readReg64 (.gpr 12#5) = BitVec.ofNat 64 (8 * step) ∧ st.readReg64 (.gpr 14#5) = BitVec.ofNat 64 pos ∧ st.readReg64 (.gpr 15#5) = highBitMaskOfBits b ∧
  st.readVReg128 0#5 = dupByte8Vec ((k * fxSeed) >>> 57) ∧ st.readVReg128 1#5 = 0xffffffffffffffffffffffffffffffff#128 ∧ st.readVReg128 2#5 = g.zeroExtend 128 ∧
  CandInv hinv k (st.readReg64 (.gpr 13#5)) (st.readReg64 (.gpr 11#5)) ∧ (∀ j < 8, b.getLsbD j = true → getLane8 g j = h2Tag k) ∧
  (∀ j < 8, getLane8 g j = h2Tag k → b.getLsbD j = false → (h : (pos + j) % (bm.toNat + 1) < w.slots.length) → (w.slots[(pos + j) % (bm.toNat + 1)]'h).1 ≠ k)
private theorem hbInsert_fromEmptyCheck (P : HbPlaced) (A : HbAlloc) (X : String → Option (State → State))
    {s0 sr s : State} {mapPtr k v bm vPad : BitVec 64} {m : Map64} {u : Nat} {w : HbHeapMapWitness} {step step_end : Nat} {F : SepProp} {oom : State → SepProp}
    (hal : mapPtr.toNat % 8 = 0) (hnw : mapPtr.toNat + 32 ≤ 2 ^ 64) (hsp0 : s0.spAligned = true)
    (hinv : SwissTableInv bm w.growthLeft w.items w.ctrl w.slots m)
    (hu : bucketMaskToCapacity bm - w.growthLeft.toNat ≤ u) (hgl_pos : 0 < w.growthLeft.toNat)
    (ha_ne : w.allocPtr ≠ 0#64) (ha_al : w.allocPtr.toNat % 8 = 0) (ha_nw : w.allocPtr.toNat + (17 * (bm.toNat + 1) + 8) ≤ 2 ^ 64)
    (hctrl_eq : w.ctrlPtr = w.allocPtr + BitVec.ofNat 64 (16 * (bm.toNat + 1))) (hstep_le : step ≤ step_end)
    (hemp_end : tagEmpty ∈ ctrlGroupAt w.ctrl (probePos bm k step_end)) (hno_emp_prev : ∀ s < step, tagEmpty ∉ ctrlGroupAt w.ctrl (probePos bm k s))
    (hprev : ∀ s < step, ∀ j < 8, getLane8 (ctrlGroupWord w.ctrl (probePos bm k s)) j = h2Tag k →
      (h : (probePos bm k s + j) % (bm.toNat + 1) < w.slots.length) → (w.slots[(probePos bm k s + j) % (bm.toNat + 1)]'h).1 ≠ k)
    (hno_h2 : ∀ j < 8, getLane8 (ctrlGroupWord w.ctrl (probePos bm k step)) j = h2Tag k →
      (h : (probePos bm k step + j) % (bm.toNat + 1) < w.slots.length) → (w.slots[(probePos bm k step + j) % (bm.toNat + 1)]'h).1 ≠ k)
    (hpc : s.pc = P.pl5.base + 180#64) (hrun : s.status = .Running) (hrf : ReadyFrame s0 sr s)
    (hx0 : s.readReg64 .x0 = mapPtr) (hx1 : s.readReg64 .x1 = k) (hx2 : s.readReg64 .x2 = v) (hx8 : (s.readReg64 (.gpr 8#5)).truncate 8 = h2Tag k)
    (hx9 : s.readReg64 (.gpr 9#5) = w.ctrlPtr) (hx10 : s.readReg64 (.gpr 10#5) = bm) (hx12 : s.readReg64 (.gpr 12#5) = BitVec.ofNat 64 (8 * step))
    (hx14 : s.readReg64 (.gpr 14#5) = BitVec.ofNat 64 (probePos bm k step)) (hv0 : s.readVReg128 0#5 = dupByte8Vec ((k * fxSeed) >>> 57))
    (hv1 : s.readVReg128 1#5 = 0xffffffffffffffffffffffffffffffff#128) (hv2 : s.readVReg128 2#5 = (ctrlGroupWord w.ctrl (probePos bm k step)).zeroExtend 128)
    (hcand_fc : ∃ (candIdx : Nat) (_ : candIdx < bm.toNat + 1), s.readReg64 (.gpr 11#5) = BitVec.ofNat 64 candIdx ∧
      (bm.toNat + 1 = 4 ∨ (8 ≤ bm.toNat + 1 ∧ isSpecialTag (w.ctrl[candIdx]'(by have := hinv.ctrl_len; omega)) = true ∧
        ProbeReachable bm (setCtrl bm w.ctrl candIdx (h2Tag k)) k candIdx)))
    (hnext : ∀ s' : State, s'.pc = P.pl5.base + 76#64 → s'.status = .Running → step + 1 ≤ step_end → InsertProbeInv s0 sr hinv mapPtr k v (step + 1) s' →
      SepWP ((hbProg5 P).rebase P.pl5.base X) (s0.readReg64 Reg.lr) s' (hbRodata P.pl ∗ U64MapStruct mapPtr w.ctrlPtr bm w.growthLeft w.items ∗
        A.Block w.allocPtr (17 * (bm.toNat + 1) + 8) 8 ∗ slotsDownFrom w.ctrlPtr w.slots ∗ (w.ctrlPtr ↦ₛ w.ctrl) ∗ hbInsertFrame s0 vPad ∗ F)
        (hbReadyPost P.pl A s0 sr mapPtr k v bm m u F) oom) :
    SepWP ((hbProg5 P).rebase P.pl5.base X) (s0.readReg64 Reg.lr) s (hbRodata P.pl ∗ U64MapStruct mapPtr w.ctrlPtr bm w.growthLeft w.items ∗
      A.Block w.allocPtr (17 * (bm.toNat + 1) + 8) 8 ∗ slotsDownFrom w.ctrlPtr w.slots ∗ (w.ctrlPtr ↦ₛ w.ctrl) ∗ hbInsertFrame s0 vPad ∗ F)
      (hbReadyPost P.pl A s0 sr mapPtr k v bm m u F) oom := by
  have hP := P.placeable5; have hb : (hbProg5 P).base = P.pl5.base := rfl
  let pos := probePos bm k step; let g := ctrlGroupWord w.ctrl pos; have hpos_lt : pos < bm.toNat + 1 := probePos_lt_buckets hinv.validMask k step
  have hctrl_fn : True → w.ctrlPtr = w.allocPtr + BitVec.ofNat 64 (16 * (bm.toNat + 1)) := fun _ => hctrl_eq; clear hctrl_eq
  rcases hcand_fc with ⟨candIdx, hcand_lt, hx11, hcand_cases⟩; wp_sym_steps 1
  have hall := simd_cmeq_allOnes8 g; conv at hall => lhs; simp only [wp_norm, arm64_norm]
  (try rw [hv2]); (try rw [hv1]); rw [hall]; clear hall; wp_sym_steps 1
  have humax := simdUmaxv8_byteMaskOfBits (eqBits8 g tagEmpty); conv at humax => lhs; simp only [simdUmaxv8, wp_norm, arm64_norm]
  rw [humax]; clear humax
  set_option proofLib.wpBranchAutoDecide false in wp_sym_steps 2
  wp_if htbnz
  · have hemp_ne : eqBits8 g tagEmpty ≠ 0#8 := fun hz => by rw [hz] at htbnz; simp at htbnz
    have hnone := probe_empty_miss_lookup hinv hemp_ne hprev hno_h2
    have ⟨hreach, h4_if_full⟩ : ProbeReachable bm (setCtrl bm w.ctrl candIdx (h2Tag k)) k candIdx ∧
        (isSpecialTag (w.ctrl[candIdx]'(by have := hinv.ctrl_len; omega)) = false → bm = 3#64) := by
      rcases hcand_cases with h4 | ⟨_, hspec, hreach⟩
      · have hbm3 : bm = 3#64 := BitVec.eq_of_toNat_eq (by change bm.toNat = 3; omega)
        exact ⟨by subst hbm3; exact ProbeReachable.of_setCtrl_eq4 (by simpa using hinv.mirror) (by omega) k, fun _ => hbm3⟩
      · exact ⟨hreach, fun hf => by rw [hspec] at hf; cases hf⟩
    exact hbInsert_selectAndCommit P A X hal hnw hsp0 hinv hu hgl_pos ha_ne ha_al ha_nw (hctrl_fn trivial) hnone hcand_lt hreach h4_if_full
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun]) (by rf_simp hrf) (by simp [wp_norm, arm64_norm, hx0])
      (by simp [wp_norm, arm64_norm, hx1]) (by simp [wp_norm, arm64_norm, hx2]) (by simp [wp_norm, arm64_norm, hx8])
      (by simp [wp_norm, arm64_norm, hx9]) (by simp [wp_norm, arm64_norm, hx10]) (by simp [wp_norm, arm64_norm, hx11])
  · have hemp_eq : eqBits8 g tagEmpty = 0#8 := Classical.byContradiction fun hne => htbnz (by simp only [hne, ↓reduceIte]; decide)
    obtain ⟨hnot_emp_cur, hlt_end⟩ := probe_nonempty_facts hinv hstep_le hemp_end hemp_eq
    rcases hcand_cases with h4 | ⟨h8, hspec, hreach⟩
    · exact False.elim (hnot_emp_cur (CtrlMirrorInv.empty_in_group_of_eq4 (h4 ▸ hinv.mirror) (by omega)))
    · wp_sym_steps 5; exact hnext _ (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun]) (by omega)
        ⟨by rf_simp hrf, by simp only [wp_norm, arm64_norm, hx0], by simp only [wp_norm, arm64_norm, hx1], by simp only [wp_norm, arm64_norm, hx2],
         by simp only [wp_norm, arm64_norm, hx8], by simp only [wp_norm, arm64_norm, hx9], by simp only [wp_norm, arm64_norm, hx10],
         by simp only [wp_norm, arm64_norm]; rw [show 8 * (step + 1) = 8 * step + 8 by omega, BitVec.ofNat_add],
         by simp only [wp_norm, arm64_norm]; rw [BitVec.add_comm _ (BitVec.ofNat 64 (probePos bm k step))]; exact probePos_step_bv hinv.validMask k step,
         by simp only [wp_norm, arm64_norm, hv0], by simp only [wp_norm, arm64_norm, hv1],
         Or.inr ⟨by simp [wp_norm, arm64_norm], h8, candIdx, hcand_lt, by simp only [wp_norm, arm64_norm, hx11], hspec, hreach⟩,
         fun s' hs' => if hlt : s' < step then hno_emp_prev s' hlt else (show s' = step by omega) ▸ hnot_emp_cur, extend_probe_prev hprev hno_h2⟩
private theorem hbInsert_postH2 (P : HbPlaced) (A : HbAlloc) (X : String → Option (State → State))
    {s0 sr s : State} {mapPtr k v bm vPad : BitVec 64} {m : Map64} {u : Nat} {w : HbHeapMapWitness} {step step_end : Nat} {F : SepProp} {oom : State → SepProp}
    (hal : mapPtr.toNat % 8 = 0) (hnw : mapPtr.toNat + 32 ≤ 2 ^ 64) (hsp0 : s0.spAligned = true)
    (hinv : SwissTableInv bm w.growthLeft w.items w.ctrl w.slots m)
    (hu : bucketMaskToCapacity bm - w.growthLeft.toNat ≤ u) (hgl_pos : 0 < w.growthLeft.toNat)
    (ha_ne : w.allocPtr ≠ 0#64) (ha_al : w.allocPtr.toNat % 8 = 0) (ha_nw : w.allocPtr.toNat + (17 * (bm.toNat + 1) + 8) ≤ 2 ^ 64)
    (hctrl_eq : w.ctrlPtr = w.allocPtr + BitVec.ofNat 64 (16 * (bm.toNat + 1))) (hstep_le : step ≤ step_end) (hstep_lt : step < numGroups bm)
    (hemp_end : tagEmpty ∈ ctrlGroupAt w.ctrl (probePos bm k step_end)) (hno_emp_prev : ∀ s < step, tagEmpty ∉ ctrlGroupAt w.ctrl (probePos bm k s))
    (hprev : ∀ s < step, ∀ j < 8, getLane8 (ctrlGroupWord w.ctrl (probePos bm k s)) j = h2Tag k →
      (h : (probePos bm k s + j) % (bm.toNat + 1) < w.slots.length) → (w.slots[(probePos bm k s + j) % (bm.toNat + 1)]'h).1 ≠ k)
    (hno_h2 : ∀ j < 8, getLane8 (ctrlGroupWord w.ctrl (probePos bm k step)) j = h2Tag k →
      (h : (probePos bm k step + j) % (bm.toNat + 1) < w.slots.length) → (w.slots[(probePos bm k step + j) % (bm.toNat + 1)]'h).1 ≠ k)
    (hpc : s.pc = P.pl5.base + 144#64) (hrun : s.status = .Running) (hrf : ReadyFrame s0 sr s)
    (hx0 : s.readReg64 .x0 = mapPtr) (hx1 : s.readReg64 .x1 = k) (hx2 : s.readReg64 .x2 = v) (hx8 : (s.readReg64 (.gpr 8#5)).truncate 8 = h2Tag k)
    (hx9 : s.readReg64 (.gpr 9#5) = w.ctrlPtr) (hx10 : s.readReg64 (.gpr 10#5) = bm) (hx12 : s.readReg64 (.gpr 12#5) = BitVec.ofNat 64 (8 * step))
    (hx14 : s.readReg64 (.gpr 14#5) = BitVec.ofNat 64 (probePos bm k step)) (hv0 : s.readVReg128 0#5 = dupByte8Vec ((k * fxSeed) >>> 57))
    (hv1 : s.readVReg128 1#5 = 0xffffffffffffffffffffffffffffffff#128) (hv2 : s.readVReg128 2#5 = (ctrlGroupWord w.ctrl (probePos bm k step)).zeroExtend 128)
    (hcand : CandInv hinv k (s.readReg64 (.gpr 13#5)) (s.readReg64 (.gpr 11#5)))
    (hnext : ∀ s' : State, s'.pc = P.pl5.base + 76#64 → s'.status = .Running → step + 1 ≤ step_end → InsertProbeInv s0 sr hinv mapPtr k v (step + 1) s' →
      SepWP ((hbProg5 P).rebase P.pl5.base X) (s0.readReg64 Reg.lr) s' (hbRodata P.pl ∗ U64MapStruct mapPtr w.ctrlPtr bm w.growthLeft w.items ∗
        A.Block w.allocPtr (17 * (bm.toNat + 1) + 8) 8 ∗ slotsDownFrom w.ctrlPtr w.slots ∗ (w.ctrlPtr ↦ₛ w.ctrl) ∗ hbInsertFrame s0 vPad ∗ F)
        (hbReadyPost P.pl A s0 sr mapPtr k v bm m u F) oom) :
    SepWP ((hbProg5 P).rebase P.pl5.base X) (s0.readReg64 Reg.lr) s (hbRodata P.pl ∗ U64MapStruct mapPtr w.ctrlPtr bm w.growthLeft w.items ∗
      A.Block w.allocPtr (17 * (bm.toNat + 1) + 8) 8 ∗ slotsDownFrom w.ctrlPtr w.slots ∗ (w.ctrlPtr ↦ₛ w.ctrl) ∗ hbInsertFrame s0 vPad ∗ F)
      (hbReadyPost P.pl A s0 sr mapPtr k v bm m u F) oom := by
  have hP := P.placeable5; have hb : (hbProg5 P).base = P.pl5.base := rfl
  let pos := probePos bm k step; let g := ctrlGroupWord w.ctrl pos; have hpos_lt : pos < bm.toNat + 1 := probePos_lt_buckets hinv.validMask k step
  have hctrl_fn : True → w.ctrlPtr = w.allocPtr + BitVec.ofNat 64 (16 * (bm.toNat + 1)) := fun _ => hctrl_eq; clear hctrl_eq
  rcases hcand with hx13 | ⟨hx13, h8, candIdx, hcand_lt, hx11, hcand_spec, hcand_reach⟩
  · wp_sym_steps 3; have hcmlt := simd_cmlt_zero8 g; conv at hcmlt => lhs; simp only [wp_norm, arm64_norm]
    (try rw [hv2]); rw [hcmlt]; clear hcmlt
    set_option proofLib.wpBranchAutoDecide false in wp_sym_steps 2
    wp_if hcbz
    · have hsp_zero : specialBits8 g = 0#8 := (byteMaskOfBits_eq_zero_iff _).1 (by simpa using hcbz)
      have hemp_eq : eqBits8 g tagEmpty = 0#8 := (bv8_eq_zero_iff_forall _).2 fun j hj => by
        have hs := (bv8_eq_zero_iff_forall _).1 hsp_zero j hj; rw [getLsbD_specialBits8 g hj] at hs
        rw [getLsbD_eqBits8 g tagEmpty hj, beq_eq_false_iff_ne]; intro he; rw [he] at hs; simp [tagEmpty, isSpecialTag] at hs
      obtain ⟨hnot_emp_cur, hlt_end⟩ := probe_nonempty_facts hinv hstep_le hemp_end hemp_eq; wp_sym_steps 4
      exact hnext _ (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun]) (by omega)
        ⟨by rf_simp hrf, by simp only [wp_norm, arm64_norm, hx0], by simp only [wp_norm, arm64_norm, hx1], by simp only [wp_norm, arm64_norm, hx2],
         by simp only [wp_norm, arm64_norm, hx8], by simp only [wp_norm, arm64_norm, hx9], by simp only [wp_norm, arm64_norm, hx10],
         by simp only [wp_norm, arm64_norm]; rw [show 8 * (step + 1) = 8 * step + 8 by omega, BitVec.ofNat_add],
         by simp only [wp_norm, arm64_norm]; rw [BitVec.add_comm _ (BitVec.ofNat 64 (probePos bm k step))]; exact probePos_step_bv hinv.validMask k step,
         by simp only [wp_norm, arm64_norm, hv0], by simp only [wp_norm, arm64_norm, hv1], Or.inl (by simp [wp_norm, arm64_norm]),
         fun s' hs' => if hlt : s' < step then hno_emp_prev s' hlt else (show s' = step by omega) ▸ hnot_emp_cur, extend_probe_prev hprev hno_h2⟩
    · have hsp_ne : specialBits8 g ≠ 0#8 := fun hz => by rw [hz, byteMaskOfBits_zero] at hcbz; simp at hcbz
      rcases bv8_ctz_spec hsp_ne with ⟨hj_sp, hbit_sp, _⟩; obtain ⟨j0, hj0_eq⟩ : ∃ n, (specialBits8 g).ctz.toNat = n := ⟨_, rfl⟩
      rw [hj0_eq] at hj_sp hbit_sp; wp_sym_steps 4; (try rw [hx14]); (try rw [hx10])
      rw [ProofLib.reverseBits_eq_reverse, byteMaskOfBits_lowestLane (specialBits8 g), hj0_eq, hinv.validMask.laneIdx_bv hpos_lt hj_sp]
      refine hbInsert_fromEmptyCheck P A X hal hnw hsp0 hinv hu hgl_pos ha_ne ha_al ha_nw (hctrl_fn trivial) hstep_le hemp_end hno_emp_prev hprev hno_h2
        (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun]) (by rf_simp hrf) (by simp [wp_norm, arm64_norm, hx0])
        (by simp [wp_norm, arm64_norm, hx1]) (by simp [wp_norm, arm64_norm, hx2]) (by simp [wp_norm, arm64_norm, hx8])
        (by simp [wp_norm, arm64_norm, hx9]) (by simp [wp_norm, arm64_norm, hx10]) (by simp [wp_norm, arm64_norm, hx12])
        (by simp [wp_norm, arm64_norm, hx14]) (by simp [wp_norm, arm64_norm, hv0]) (by simp [wp_norm, arm64_norm, hv1])
        (by simp [wp_norm, arm64_norm, hv2]) ⟨(pos + j0) % (bm.toNat + 1), Nat.mod_lt _ (by omega), by simp [wp_norm, arm64_norm], ?_⟩ hnext
      rcases hinv.validMask.buckets_cases with h4 | ⟨h8, _⟩
      · exact Or.inl h4
      · refine Or.inr ⟨h8, ?_, ProbeReachable.of_setCtrl_ge8 hinv.validMask h8 hinv.mirror hstep_lt hj_sp rfl hno_emp_prev⟩
        rw [getLsbD_specialBits8 g hj_sp, CtrlMirrorInv.lane_eq_mod_of_ge8 hinv.mirror h8 hpos_lt hj_sp] at hbit_sp; exact hbit_sp
  · wp_sym_steps 2
    exact hbInsert_fromEmptyCheck P A X hal hnw hsp0 hinv hu hgl_pos ha_ne ha_al ha_nw (hctrl_fn trivial) hstep_le hemp_end hno_emp_prev hprev hno_h2
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun]) (by rf_simp hrf) (by simp [wp_norm, arm64_norm, hx0])
      (by simp [wp_norm, arm64_norm, hx1]) (by simp [wp_norm, arm64_norm, hx2]) (by simp [wp_norm, arm64_norm, hx8])
      (by simp [wp_norm, arm64_norm, hx9]) (by simp [wp_norm, arm64_norm, hx10]) (by simp [wp_norm, arm64_norm, hx12])
      (by simp [wp_norm, arm64_norm, hx14]) (by simp [wp_norm, arm64_norm, hv0]) (by simp [wp_norm, arm64_norm, hv1])
      (by simp [wp_norm, arm64_norm, hv2]) ⟨candIdx, hcand_lt, by simp [wp_norm, arm64_norm, hx11], Or.inr ⟨h8, hcand_spec, hcand_reach⟩⟩ hnext
private theorem hbInsert_fromReady_wp (P : HbPlaced) (A : HbAlloc) (X : String → Option (State → State))
    {s0 sr s : State} {mapPtr k v bm vPad : BitVec 64} {m : Map64} {u : Nat} {F : SepProp} {oom : State → SepProp}
    (hsp0 : s0.spAligned = true) (hpc : s.pc = P.pl5.base + 52#64) (hrun : s.status = .Running) (hrf : ReadyFrame s0 sr s)
    (hx0 : s.readReg64 .x0 = mapPtr) (hx1 : s.readReg64 .x1 = k) (hx2 : s.readReg64 .x2 = v) (hx20 : s.readReg64 .x20 = fxHash k) (hx21 : s.readReg64 .x21 = fxProd k) :
    SepWP ((hbProg5 P).rebase P.pl5.base X) (s0.readReg64 Reg.lr) s (U64MapRepFast P.pl A mapPtr m bm u ∗ hbInsertFrame s0 vPad ∗ F) (hbReadyPost P.pl A s0 sr mapPtr k v bm m u F) oom := by
  have hP := P.placeable5; have hb : (hbProg5 P).base = P.pl5.base := rfl
  wp_conv_pre => unfold U64MapRepFast; rw [sepConj_assoc]
  apply SepWP.pure_elim; rintro ⟨hal, hnw, _, _⟩
  refine SepWP.weaken_pre (P' := (∃∗ w : HbHeapMapWitness,
        ⌜SwissTableInv bm w.growthLeft w.items w.ctrl w.slots m ∧ bucketMaskToCapacity bm - w.growthLeft.toNat ≤ u ∧ 0 < w.growthLeft.toNat ∧ w.allocPtr ≠ 0#64 ∧ w.allocPtr.toNat % 8 = 0 ∧
         w.allocPtr.toNat + (17 * (bm.toNat + 1) + 8) ≤ 2 ^ 64 ∧ w.ctrlPtr = w.allocPtr + BitVec.ofNat 64 (16 * (bm.toNat + 1))⌝ ∗
        U64MapStruct mapPtr w.ctrlPtr bm w.growthLeft w.items ∗ A.Block w.allocPtr (17 * (bm.toNat + 1) + 8) 8 ∗
        slotsDownFrom w.ctrlPtr w.slots ∗ (w.ctrlPtr ↦ₛ w.ctrl)) ∗ (hbRodata P.pl ∗ hbInsertFrame s0 vPad ∗ F))
    (Entails.of_eq (by ac_rfl)) (SepWP.of_sepExists_left fun w => ?_); wp_conv_pre => rw [sepConj_assoc]
  apply SepWP.pure_elim; rintro ⟨hinv, hu, hgl_pos, ha_ne, ha_al, ha_nw, hctrl_eq⟩
  have hctrl_fn : True → w.ctrlPtr = w.allocPtr + BitVec.ofNat 64 (16 * (bm.toNat + 1)) := fun _ => hctrl_eq; clear hctrl_eq
  have hlen : w.ctrl.length = (bm.toNat + 1) + 8 := hinv.ctrl_len; have hslots_len : w.slots.length = bm.toNat + 1 := hinv.slots_len
  rcases hinv.exists_empty_probe_group k with ⟨step_end, hstep_end_lt, hemp_end⟩; wp_conv_pre => unfold U64MapStruct
  wp_sym_steps 6
  refine SepWP.weaken_pre (P' := hbRodata P.pl ∗ U64MapStruct mapPtr w.ctrlPtr bm w.growthLeft w.items ∗ A.Block w.allocPtr (17 * (bm.toNat + 1) + 8) 8 ∗
      slotsDownFrom w.ctrlPtr w.slots ∗ (w.ctrlPtr ↦ₛ w.ctrl) ∗ hbInsertFrame s0 vPad ∗ F) (by
      unfold U64MapStruct
      exact Entails.of_eq (by ac_rfl)) ?_
  refine SepWP.cfg_fixpoint_wf_cps (Label := Nat) (l0 := 0) (cut_pc := fun _ => P.pl5.base + 76#64) (meas := fun step _ => step_end + 1 - step)
    (P_inv := fun _ _ => _) (Inv := fun step st => step ≤ step_end ∧ InsertProbeInv s0 sr hinv mapPtr k v step st) (post := fun _ => _)
    (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun]) (Entails.refl _)
    ⟨Nat.zero_le _, by rf_simp hrf, by simp [wp_norm, arm64_norm, hx0], by simp [wp_norm, arm64_norm, hx1], by simp [wp_norm, arm64_norm, hx2],
     by simp [wp_norm, arm64_norm]; rfl, by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
     by simp [wp_norm, arm64_norm, hx20], by simpa [wp_norm, arm64_norm, hx21, fxProd] using dup_lsr57_eq (k * fxSeed), by simp [wp_norm, arm64_norm],
     Or.inl (by simp [wp_norm, arm64_norm]), fun _ hs => by omega, fun _ hs => by omega⟩ ?_
  · intro step st hpc_st hrun_st ⟨hstep_le, hrf_st, hx0_st, hx1_st, hx2_st, hx8_st, hx9_st, hx10_st, hx12_st, hx20_st, hv0_st, hv1_st, hcand_st, hno_emp_prev, hprev⟩ ih_outer
    let pos := probePos bm k step; let g := ctrlGroupWord w.ctrl pos; have hpos_lt : pos < bm.toNat + 1 := probePos_lt_buckets hinv.validMask k step
    wp_sym_steps 1; (try rw [hx20_st]); wp_conv_pre => rw [pointsToBytes_focus_ctrlGroupWord w.ctrlPtr w.ctrl (pos := pos) (by omega)]
    set_option proofLib.wpBranchAutoDecide false in wp_sym_steps 5
    wp_conv_pre => rw [← pointsToBytes_focus_ctrlGroupWord w.ctrlPtr w.ctrl (pos := pos) (by omega)]
    have hm_h2 := simd_cmeq_dup8_highMask g ((k * fxSeed) >>> 57)
    change (zipLanes 8 (g.zeroExtend 128) (dupByte8Vec ((k * fxSeed) >>> 57)) (fun a b => if a == b then 0xff#128 else 0#128) 8).truncate 64 &&&
      0x8080808080808080#64 = highBitMaskOfBits (eqBits8 g (h2Tag k)) at hm_h2
    conv at hm_h2 => lhs; simp only [wp_norm, arm64_norm]
    (try rw [hv0_st]); rw [hm_h2]; clear hm_h2; wp_if hbeq
    · have hb0 : eqBits8 g (h2Tag k) = 0#8 := (highBitMaskOfBits_eq_zero_iff _).1 (by simpa using hbeq)
      have hno_h2 : ∀ j < 8, getLane8 g j = h2Tag k → (h : (pos + j) % (bm.toNat + 1) < w.slots.length) → (w.slots[(pos + j) % (bm.toNat + 1)]'h).1 ≠ k := fun j hj htag => by
        have hbit := (bv8_eq_zero_iff_forall _).1 hb0 j hj; rw [getLsbD_eqBits8 g (h2Tag k) hj, beq_eq_false_iff_ne] at hbit; exact False.elim (hbit htag)
      exact hbInsert_postH2 P A X hal hnw hsp0 hinv hu hgl_pos ha_ne ha_al ha_nw (hctrl_fn trivial) hstep_le (by omega) hemp_end hno_emp_prev hprev hno_h2
        (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun_st]) (by rf_simp hrf_st) (by simp [wp_norm, arm64_norm, hx0_st])
        (by simp [wp_norm, arm64_norm, hx1_st]) (by simp [wp_norm, arm64_norm, hx2_st]) (by simp [wp_norm, arm64_norm, hx8_st])
        (by simp [wp_norm, arm64_norm, hx9_st]) (by simp [wp_norm, arm64_norm, hx10_st]) (by simp [wp_norm, arm64_norm, hx12_st])
        (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hv0_st]) (by simp [wp_norm, arm64_norm, hv1_st])
        (by simp [wp_norm, arm64_norm]; rfl) (by simpa [wp_norm, arm64_norm] using hcand_st) fun s' hpc' hrun' hle' hpi' => ih_outer (step + 1) s' (by omega) hpc' hrun' ⟨hle', hpi'⟩
    · have hb0 : eqBits8 g (h2Tag k) ≠ 0#8 := fun hz => by rw [hz, highBitMaskOfBits_zero] at hbeq; simp at hbeq
      refine SepWP.cfg_fixpoint_wf_cps (Label := BitVec 8) (l0 := eqBits8 g (h2Tag k)) (cut_pc := fun _ => P.pl5.base + 100#64)
        (meas := fun b _ => b.toNat) (P_inv := fun _ _ => _) (Inv := fun b sti => InsertInnerInv s0 sr hinv mapPtr k v step b sti) (post := fun _ => _)
        (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun_st]) (Entails.refl _)
        ⟨hb0, by rf_simp hrf_st, by simp [wp_norm, arm64_norm, hx0_st], by simp [wp_norm, arm64_norm, hx1_st], by simp [wp_norm, arm64_norm, hx2_st],
         by simp [wp_norm, arm64_norm, hx8_st], by simp [wp_norm, arm64_norm, hx9_st], by simp [wp_norm, arm64_norm, hx10_st], by simp [wp_norm, arm64_norm, hx12_st],
         by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm, hv0_st], by simp [wp_norm, arm64_norm, hv1_st],
         by simp [wp_norm, arm64_norm]; rfl, by simpa [wp_norm, arm64_norm] using hcand_st,
         fun j hj hbit => by rw [getLsbD_eqBits8 g (h2Tag k) hj, beq_iff_eq] at hbit; exact hbit,
         fun j hj htag hbf => by rw [getLsbD_eqBits8 g (h2Tag k) hj, beq_eq_false_iff_ne] at hbf; exact False.elim (hbf htag)⟩ ?_
      · intro b sti hpc_i hrun_i ⟨hb_ne, hrf_i, hx0_i, hx1_i, hx2_i, hx8_i, hx9_i, hx10_i, hx12_i, hx14_i, hx15_i, hv0_i, hv1_i, hv2_i, hcand_i, hsub_b, hmiss_b⟩ ih_inner
        rcases bv8_ctz_spec hb_ne with ⟨hj0_lt, hj0_bit, _⟩
        have hidx_b : (pos + b.ctz.toNat) % (bm.toNat + 1) < bm.toNat + 1 := Nat.mod_lt _ (by omega)
        have hidx_lt : (pos + b.ctz.toNat) % (bm.toNat + 1) < w.slots.length := hslots_len ▸ hidx_b
        have htag_j0 : getLane8 g b.ctz.toNat = h2Tag k := hsub_b b.ctz.toNat hj0_lt hj0_bit
        wp_sym_steps 5; (try rw [hx15_i]); (try rw [hx14_i]); (try rw [hx10_i]); (try rw [hx9_i])
        rw [ProofLib.reverseBits_eq_reverse, highBitMaskOfBits_lowestLane b, hinv.validMask.laneIdx_bv hpos_lt hj0_lt]
        wp_conv_pre => rw [slotsDownFrom_focus_ldur w.ctrlPtr w.slots hidx_lt]
        set_option proofLib.wpBranchAutoDecide false in wp_sym_steps 3
        wp_if hkeq
        · have hfull_idx : isFullTag (w.ctrl[(pos + b.ctz.toNat) % (bm.toNat + 1)]'(by have := hinv.mirror.1; omega)) = true := by
            rw [← CtrlMirrorInv.lane_full_eq_mod hinv.validMask hinv.mirror hpos_lt hj0_lt (htag_j0 ▸ isFullTag_h2Tag k), htag_j0]; exact isFullTag_h2Tag k
          exact SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (hbInsert_overwrite P A X hal hnw hsp0 hinv hu ha_ne ha_al ha_nw (hctrl_fn trivial) hidx_b hidx_lt hfull_idx hkeq.symm
            (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun_i]) (by rf_simp hrf_i) (by simp [wp_norm, arm64_norm, hx2_i]) (by simp [wp_norm, arm64_norm]))
        · have hk_ne : (w.slots[(pos + b.ctz.toNat) % (bm.toNat + 1)]'hidx_lt).1 ≠ k := Ne.symm hkeq
          wp_conv_pre => rw [← slotsDownFrom_focus_ldur w.ctrlPtr w.slots hidx_lt]
          set_option proofLib.wpBranchAutoDecide false in wp_sym_steps 3
          (try rw [hx15_i]); rw [highBitMaskOfBits_clear_lowest b]; wp_if hbne
          · have hb' : (b - 1#8) &&& b ≠ 0#8 := fun hz => by rw [hz, highBitMaskOfBits_zero] at hbne; simp at hbne
            exact ih_inner ((b - 1#8) &&& b) _ (bv8_clear_lowest_lt hb_ne) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun_i])
              ⟨hb', by rf_simp hrf_i, by simp [wp_norm, arm64_norm, hx0_i], by simp [wp_norm, arm64_norm, hx1_i], by simp [wp_norm, arm64_norm, hx2_i],
               by simp [wp_norm, arm64_norm, hx8_i], by simp [wp_norm, arm64_norm, hx9_i], by simp [wp_norm, arm64_norm, hx10_i], by simp [wp_norm, arm64_norm, hx12_i],
               by simp [wp_norm, arm64_norm, hx14_i], by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm, hv0_i], by simp [wp_norm, arm64_norm, hv1_i],
               by simp [wp_norm, arm64_norm, hv2_i], by simpa [wp_norm, arm64_norm] using hcand_i,
               fun j hj hbit' => by rw [bv8_getLsbD_clear_lowest b hj, Bool.and_eq_true] at hbit'; exact hsub_b j hj hbit'.1, clear_lowest_miss hk_ne hmiss_b⟩
          · have hb'_zero : (b - 1#8) &&& b = 0#8 := (highBitMaskOfBits_eq_zero_iff _).1 hbne
            have hno_h2 : ∀ j < 8, getLane8 g j = h2Tag k → (h : (pos + j) % (bm.toNat + 1) < w.slots.length) → (w.slots[(pos + j) % (bm.toNat + 1)]'h).1 ≠ k :=
              fun j hj htag hsl => clear_lowest_miss hk_ne hmiss_b j hj htag ((bv8_eq_zero_iff_forall _).1 hb'_zero j hj) hsl
            exact hbInsert_postH2 P A X hal hnw hsp0 hinv hu hgl_pos ha_ne ha_al ha_nw (hctrl_fn trivial) hstep_le (by omega) hemp_end hno_emp_prev hprev hno_h2
              (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun_i]) (by rf_simp hrf_i) (by simp [wp_norm, arm64_norm, hx0_i])
              (by simp [wp_norm, arm64_norm, hx1_i]) (by simp [wp_norm, arm64_norm, hx2_i]) (by simp [wp_norm, arm64_norm, hx8_i])
              (by simp [wp_norm, arm64_norm, hx9_i]) (by simp [wp_norm, arm64_norm, hx10_i]) (by simp [wp_norm, arm64_norm, hx12_i])
              (by simp [wp_norm, arm64_norm, hx14_i]) (by simp [wp_norm, arm64_norm, hv0_i]) (by simp [wp_norm, arm64_norm, hv1_i])
              (by simp [wp_norm, arm64_norm, hv2_i]) (by simpa [wp_norm, arm64_norm] using hcand_i)
              fun s' hpc' hrun' hle' hpi' => ih_outer (step + 1) s' (by omega) hpc' hrun' ⟨hle', hpi'⟩
private def U64MapRepSlow (pl : Obj.Placement) (A : HbAlloc) (mapPtr : BitVec 64) (m : Map64) (bm : BitVec 64) (u : Nat) : SepProp :=
  ⌜mapPtr.toNat % 8 = 0 ∧ mapPtr.toNat + 32 ≤ 2 ^ 64 ∧ Map64Wf m ∧ m.length ≤ u ∧ bucketMaskToCapacity bm ≤ u⌝ ∗ hbRodata pl ∗
  if bm = 0#64 then ⌜m = []⌝ ∗ U64MapStruct mapPtr (pl.ρ hbEmptyCtrlSym) 0#64 0#64 0#64
  else ∃∗ w : HbHeapMapWitness,
    ⌜SwissTableInv bm w.growthLeft w.items w.ctrl w.slots m ∧ w.growthLeft = 0#64 ∧ w.allocPtr ≠ 0#64 ∧ w.allocPtr.toNat % 8 = 0 ∧
     w.allocPtr.toNat + (17 * (bm.toNat + 1) + 8) ≤ 2 ^ 64 ∧ w.ctrlPtr = w.allocPtr + BitVec.ofNat 64 (16 * (bm.toNat + 1))⌝ ∗
    U64MapStruct mapPtr w.ctrlPtr bm w.growthLeft w.items ∗ A.Block w.allocPtr (17 * (bm.toNat + 1) + 8) 8 ∗ slotsDownFrom w.ctrlPtr w.slots ∗ (w.ctrlPtr ↦ₛ w.ctrl)
private theorem U64MapRepSlow_bounds {pl : Obj.Placement} {A : HbAlloc} {mapPtr : BitVec 64}
    {m : Map64} {bm : BitVec 64} {u : Nat} {Rest : SepProp} {mem : Memory}
    (hm : mem ⊨ U64MapRepSlow pl A mapPtr m bm u ∗ Rest) :
    m.length ≤ u ∧ bucketMaskToCapacity bm ≤ u := by
  unfold U64MapRepSlow at hm
  rw [sepConj_assoc] at hm
  have hp := ((satisfies_pure_sepConj _ _ _).mp hm).1
  exact ⟨hp.2.2.2.1, hp.2.2.2.2⟩
private theorem U64MapRep_split_fast_slow (pl : Obj.Placement) (A : HbAlloc) (mapPtr : BitVec 64) (m : Map64) (bm : BitVec 64) (u : Nat) :
    U64MapRep pl A mapPtr m bm u ⊢ ∃∗ fast : Bool, if fast then U64MapRepFast pl A mapPtr m bm u else U64MapRepSlow pl A mapPtr m bm u := by
  unfold U64MapRep
  apply Entails.pure_left; rintro ⟨hal, hnw, hwf⟩; by_cases hbm : bm = 0#64
  · simp only [hbm, ↓reduceIte]; rw [sepConj_comm (hbRodata pl), sepConj_assoc]; apply Entails.pure_left; intro hm0; rw [sepConj_comm]
    refine Entails.sepExists_right false ?_; simp only [Bool.false_eq_true, ↓reduceIte]
    unfold U64MapRepSlow
    simp only [↓reduceIte]; refine Entails.pure_right ⟨hal, hnw, hwf, by simp [hm0], by simp [bucketMaskToCapacity]⟩ ?_
    exact sepConj_mono_right (Entails.pure_right hm0 (Entails.refl _))
  · simp only [hbm, ↓reduceIte, sepExists_sepConj_right]; apply Entails.sepExists_elim; intro w
    rw [sepConj_comm, sepConj_assoc]; apply Entails.pure_left; rintro ⟨hinv, hu, ha_ne, ha_al, ha_nw, hctrl⟩; by_cases hgl : w.growthLeft = 0#64
    · have hcap_le : bucketMaskToCapacity bm ≤ u := by simpa [hgl] using hu
      have hm_le : m.length ≤ u := Nat.le_trans hinv.length_le_used hu
      refine Entails.sepExists_right false ?_; simp only [Bool.false_eq_true, ↓reduceIte]; unfold U64MapRepSlow; simp only [hbm, ↓reduceIte]
      refine Entails.pure_right ⟨hal, hnw, hwf, hm_le, hcap_le⟩ ?_; rw [sepConj_comm]
      exact sepConj_mono_right (Entails.sepExists_right w (Entails.pure_right ⟨hinv, hgl, ha_ne, ha_al, ha_nw, hctrl⟩ (Entails.refl _)))
    · have hpos : 0 < w.growthLeft.toNat := Nat.pos_of_ne_zero fun hz => hgl (BitVec.eq_of_toNat_eq (by simpa using hz))
      refine Entails.sepExists_right true ?_; simp only [↓reduceIte]
      unfold U64MapRepFast
      refine Entails.pure_right ⟨hal, hnw, hwf, hbm⟩ ?_
      rw [sepConj_comm]; exact sepConj_mono_right (Entails.sepExists_right w (Entails.pure_right ⟨hinv, hu, hpos, ha_ne, ha_al, ha_nw, hctrl⟩ (Entails.refl _)))
private theorem satisfies_U64MapRep_cases {pl : Obj.Placement} {A : HbAlloc} {mapPtr : BitVec 64}
    {m : Map64} {bm : BitVec 64} {u : Nat} {Rest : SepProp} {mem : Memory} (hm : mem ⊨ U64MapRep pl A mapPtr m bm u ∗ Rest) :
    (mem ⊨ U64MapRepFast pl A mapPtr m bm u ∗ Rest) ∨ (mem ⊨ U64MapRepSlow pl A mapPtr m bm u ∗ Rest) := by
  have hm' := Satisfies.mono (sepConj_mono_left (U64MapRep_split_fast_slow pl A mapPtr m bm u)) hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm'; exact hm'.elim fun | false, h => Or.inr h | true, h => Or.inl h
private theorem U64MapRepSlow_focus_gl0 (pl : Obj.Placement) (A : HbAlloc) (mapPtr : BitVec 64) (m : Map64) (bm : BitVec 64) (u : Nat) :
    U64MapRepSlow pl A mapPtr m bm u ⊢ ∃∗ Rest : SepProp, ⌜((mapPtr + 16#64) ↦₆₄ 0#64) ∗ Rest ⊢ U64MapRep pl A mapPtr m bm u⌝ ∗ ((mapPtr + 16#64) ↦₆₄ 0#64) ∗ Rest := by
  unfold U64MapRepSlow
  apply Entails.pure_left; rintro ⟨hal, hnw, hwf, _, hcap_le⟩; by_cases hbm : bm = 0#64
  · simp only [hbm, ↓reduceIte, sepConj_comm (hbRodata pl), sepConj_assoc]; apply Entails.pure_left; intro hm0; unfold U64MapStruct
    refine Entails.sepExists_right (hbRodata pl ∗ (mapPtr ↦₆₄ pl.ρ hbEmptyCtrlSym) ∗ ((mapPtr + 8#64) ↦₆₄ 0#64) ∗ ((mapPtr + 24#64) ↦₆₄ 0#64))
      (Entails.pure_right ?_ (Entails.of_eq (by ac_rfl)))
    unfold U64MapRep U64MapStruct
    simp only [↓reduceIte]; refine Entails.pure_right ⟨hal, hnw, hwf⟩ ?_
    exact Entails.trans (Entails.of_eq (show _ = hbRodata pl ∗ ((mapPtr ↦₆₄ pl.ρ hbEmptyCtrlSym) ∗ ((mapPtr + 8#64) ↦₆₄ 0#64) ∗
      ((mapPtr + 16#64) ↦₆₄ 0#64) ∗ ((mapPtr + 24#64) ↦₆₄ 0#64)) by ac_rfl)) (sepConj_mono_right (Entails.pure_right hm0 (Entails.refl _)))
  · simp only [hbm, ↓reduceIte, sepExists_sepConj_right]; apply Entails.sepExists_elim; intro w
    rw [sepConj_comm, sepConj_assoc]; apply Entails.pure_left; rintro ⟨hinv, hgl0, ha_ne, ha_al, ha_nw, hctrl⟩; unfold U64MapStruct; rw [hgl0]
    refine Entails.sepExists_right (hbRodata pl ∗ (mapPtr ↦₆₄ w.ctrlPtr) ∗ ((mapPtr + 8#64) ↦₆₄ bm) ∗ ((mapPtr + 24#64) ↦₆₄ w.items) ∗
      A.Block w.allocPtr (17 * (bm.toNat + 1) + 8) 8 ∗ slotsDownFrom w.ctrlPtr w.slots ∗ (w.ctrlPtr ↦ₛ w.ctrl)) (Entails.pure_right ?_ (Entails.of_eq (by ac_rfl)))
    unfold U64MapRep
    simp only [hbm, ↓reduceIte]; refine Entails.pure_right ⟨hal, hnw, hwf⟩ (Entails.trans (Entails.of_eq (show _ = hbRodata pl ∗
      (((mapPtr ↦₆₄ w.ctrlPtr) ∗ ((mapPtr + 8#64) ↦₆₄ bm) ∗ ((mapPtr + 16#64) ↦₆₄ 0#64) ∗ ((mapPtr + 24#64) ↦₆₄ w.items)) ∗
      A.Block w.allocPtr (17 * (bm.toNat + 1) + 8) 8 ∗ slotsDownFrom w.ctrlPtr w.slots ∗ (w.ctrlPtr ↦ₛ w.ctrl)) by ac_rfl))
      (sepConj_mono_right (Entails.sepExists_right w (Entails.pure_right ⟨hinv, by simp [hgl0]; exact hcap_le, ha_ne, ha_al, ha_nw, hctrl⟩ (by
        unfold U64MapStruct
        rw [hgl0]; exact Entails.of_eq (by ac_rfl))))))
private theorem U64MapRepFast_focus_gl (pl : Obj.Placement) (A : HbAlloc) (mapPtr : BitVec 64) (m : Map64) (bm : BitVec 64) (u : Nat) :
    U64MapRepFast pl A mapPtr m bm u ⊢ ∃∗ gl : BitVec 64, ∃∗ Rest : SepProp,
      ⌜gl ≠ 0#64 ∧ (((mapPtr + 16#64) ↦₆₄ gl) ∗ Rest ⊢ U64MapRepFast pl A mapPtr m bm u)⌝ ∗ ((mapPtr + 16#64) ↦₆₄ gl) ∗ Rest := by
  conv => lhs; unfold U64MapRepFast
  apply Entails.pure_left; rintro ⟨hal, hnw, hwf, hbm⟩; rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro w
  rw [sepConj_comm, sepConj_assoc]; apply Entails.pure_left; rintro ⟨hinv, hu, hgl_pos, ha_ne, ha_al, ha_nw, hctrl⟩
  have hgl_ne : w.growthLeft ≠ 0#64 := fun hz => by rw [hz] at hgl_pos; simp at hgl_pos
  conv => lhs; unfold U64MapStruct
  refine Entails.sepExists_right w.growthLeft (Entails.sepExists_right (hbRodata pl ∗ (mapPtr ↦₆₄ w.ctrlPtr) ∗ ((mapPtr + 8#64) ↦₆₄ bm) ∗
    ((mapPtr + 24#64) ↦₆₄ w.items) ∗ A.Block w.allocPtr (17 * (bm.toNat + 1) + 8) 8 ∗ slotsDownFrom w.ctrlPtr w.slots ∗ (w.ctrlPtr ↦ₛ w.ctrl))
    (Entails.pure_right ⟨hgl_ne, ?_⟩ (Entails.of_eq (by ac_rfl))))
  unfold U64MapRepFast
  refine Entails.pure_right ⟨hal, hnw, hwf, hbm⟩ (Entails.trans (Entails.of_eq (show _ = hbRodata pl ∗
    (((mapPtr ↦₆₄ w.ctrlPtr) ∗ ((mapPtr + 8#64) ↦₆₄ bm) ∗ ((mapPtr + 16#64) ↦₆₄ w.growthLeft) ∗ ((mapPtr + 24#64) ↦₆₄ w.items)) ∗
    A.Block w.allocPtr (17 * (bm.toNat + 1) + 8) 8 ∗ slotsDownFrom w.ctrlPtr w.slots ∗ (w.ctrlPtr ↦ₛ w.ctrl)) by ac_rfl))
    (sepConj_mono_right (Entails.sepExists_right w (Entails.pure_right ⟨hinv, hu, hgl_pos, ha_ne, ha_al, ha_nw, hctrl⟩ (by
      unfold U64MapStruct
      exact Entails.of_eq (by ac_rfl))))))
private theorem hbInsert_fast_wp (P : HbPlaced) (A : HbAlloc) (X : String → Option (State → State))
    {s0 : State} {mapPtr k v bm : BitVec 64} {m : Map64} {u lc blk : Nat} {R : SepProp}
    (hpc : s0.pc = P.pl5.base) (hrun : s0.status = .Running) (hsp0 : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = mapPtr) (hx1 : s0.readReg64 .x1 = k) (hx2 : s0.readReg64 .x2 = v) (hstk_nw : A.stackBytes + 176 ≤ 2 ^ 64) :
    SepWP ((hbProg5 P).rebase P.pl5.base X) (s0.readReg64 Reg.lr) s0
      (U64MapRepFast P.pl A mapPtr m bm u ∗ A.Heap lc blk s0 ∗ stackAt s0.sp (176 + A.stackBytes))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R → sf.mem ⊨ (hashbrownInsertSpec P.pl A).post (mapPtr, m, bm, u, k, v, lc, blk) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) (fun _ => ⌜A.allowOom⌝) := by
  have hP := P.placeable5; have hb : (hbProg5 P).base = P.pl5.base := rfl
  have hstk_eq : stackAt s0.sp (176 + A.stackBytes) = stackAt (s0.sp - 64#64) (112 + A.stackBytes) ∗ memRegion (s0.sp - 64#64) 64 := by
    rw [show 176 + A.stackBytes = (112 + A.stackBytes) + 64 by omega]; exact stackAt_region s0.sp (112 + A.stackBytes) 64 (by omega)
  refine SepWP.mono_frozen (Φ := fun m => s0.mem.KeepsFrozen m)
    (post := hbReadyPost P.pl A s0 s0 mapPtr k v bm m u (A.Heap lc blk s0 ∗ stackAt (s0.sp - 64#64) (112 + A.stackBytes)))
    (fun _ _ => Memory.KeepsFrozen.trans) (Memory.KeepsFrozen.refl s0.mem) ?_
    fun sf Pf _ _ hkf_sf ⟨hret, hspf, hcsf, hstdf, hPf⟩ => ⟨fun hm => ?_, hspf, hcsf⟩
  · refine SepWP.weaken_pre (P' := memRegion (s0.sp - 64#64) 64 ∗ ((∃∗ gl : BitVec 64, ∃∗ Rest : SepProp,
        ⌜gl ≠ 0#64 ∧ (((mapPtr + 16#64) ↦₆₄ gl) ∗ Rest ⊢ U64MapRepFast P.pl A mapPtr m bm u)⌝ ∗ ((mapPtr + 16#64) ↦₆₄ gl) ∗ Rest) ∗
        A.Heap lc blk s0 ∗ stackAt (s0.sp - 64#64) (112 + A.stackBytes)))
      (by rw [hstk_eq]; exact Entails.trans (Entails.of_eq (show _ = memRegion (s0.sp - 64#64) 64 ∗
            (U64MapRepFast P.pl A mapPtr m bm u ∗ (A.Heap lc blk s0 ∗ stackAt (s0.sp - 64#64) (112 + A.stackBytes))) by ac_rfl))
            (sepConj_mono_right (sepConj_mono_left (U64MapRepFast_focus_gl P.pl A mapPtr m bm u)))) ?_
    refine hbInsert_prologue P X hpc hrun hsp0 fun s1 vPad hpc1 hrun1 hsp1 _ hx0_1 hx1_1 hx2_1 _ hup1 hstd1 => ?_
    have hrf1 : ReadyFrame s0 s0 s1 := ⟨hsp1, hup1, hstd1⟩; wp_conv_pre => rw [sepConj_comm (hbInsertFrame s0 vPad), sepConj_assoc]
    refine SepWP.of_sepExists_left fun gl => SepWP.of_sepExists_left fun Rest => ?_; wp_conv_pre => rw [sepConj_assoc]
    apply SepWP.pure_elim; rintro ⟨hgl_ne, hrepack⟩; have hx0' : s1.readReg64 .x0 = mapPtr := hx0_1.trans hx0
    set_option proofLib.wpBranchAutoDecide false in wp_sym_steps 8
    wp_if hcbz
    · exact False.elim (hgl_ne (by simpa [wp_norm, arm64_norm] using hcbz))
    · refine SepWP.weaken_pre (P' := U64MapRepFast P.pl A mapPtr m bm u ∗ hbInsertFrame s0 vPad ∗ (A.Heap lc blk s0 ∗ stackAt (s0.sp - 64#64) (112 + A.stackBytes)))
        (Entails.trans (Entails.of_eq (show _ = (((mapPtr + 16#64) ↦₆₄ gl) ∗ Rest) ∗ (hbInsertFrame s0 vPad ∗ (A.Heap lc blk s0 ∗ stackAt (s0.sp - 64#64) (112 + A.stackBytes))) by ac_rfl))
          (sepConj_mono_left hrepack)) ?_
      exact hbInsert_fromReady_wp P A X hsp0 (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1]) (by rf_simp hrf1)
        (by simp [wp_norm, arm64_norm, hx0']) (by simp [wp_norm, arm64_norm, hx1_1, hx1]) (by simp [wp_norm, arm64_norm, hx2_1, hx2])
        (by simp [wp_norm, arm64_norm, fxHash, fxProd, fxSeed]) (by simp [wp_norm, arm64_norm, fxProd, fxSeed])
  · dsimp only [hashbrownInsertSpec]; rw [hstk_eq]
    refine Satisfies.mono (sepConj_mono_left (Entails.trans hPf (Entails.pure_right ⟨hret, StdStatePreserved.toAllocStatePreserved hstdf hkf_sf⟩ ?_))) hm
    refine Entails.trans (Entails.of_eq (show _ = (stackAt (s0.sp - 64#64) (112 + A.stackBytes) ∗ memRegion (s0.sp - 64#64) 64) ∗
      (U64MapRep P.pl A mapPtr (cliMapInsert k v m) bm (u + 1) ∗ A.Heap lc blk s0) by ac_rfl)) (sepConj_mono_right ?_)
    refine Entails.sepExists_right bm (Entails.pure_right ⟨Or.inl rfl, fun h => (h rfl).elim⟩ (sepConj_mono_right ?_))
    rw [Nat.add_sub_cancel, Nat.add_sub_cancel]; exact A.heap_transport (StdStatePreserved.toHbVmPreserved hstdf)

private theorem sepWP_let_state {prog : Program} {t : BitVec 64} {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : let sc := s; SepWP prog t sc P post oom) : SepWP prog t s P post oom := h
private theorem hbInsert_toReserveCall_wp (P : HbPlaced) (A : HbAlloc) (X : String → Option (State → State))
    {s0 : State} {mapPtr k v bm : BitVec 64} {m : Map64} {u lc blk : Nat} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s0.pc = P.pl5.base) (hrun : s0.status = .Running) (hsp0 : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = mapPtr) (hx1 : s0.readReg64 .x1 = k) (hx2 : s0.readReg64 .x2 = v) (hstk_nw : A.stackBytes + 176 ≤ 2 ^ 64)
    (hcont : ∀ (sc : State) (vPad : BitVec 64), sc.pc = P.pl.base → sc.status = .Running → sc.sp = s0.sp - 64#64 → sc.spAligned = true →
      sc.readReg64 Reg.lr = P.pl5.base + 340#64 → sc.readReg64 .x0 = mapPtr → sc.readReg64 .x1 = 1#64 → sc.readReg32 .x3 = 1#32 →
      sc.readReg64 .x19 = mapPtr → sc.readReg64 .x20 = fxHash k → sc.readReg64 .x21 = fxProd k → sc.readReg64 .x22 = k → sc.readReg64 .x23 = v →
      HbUpperSaved s0 sc → StdStatePreserved s0 sc → s0.mem.KeepsFrozen sc.mem →
      post sc ((U64MapRep P.pl A mapPtr m bm u ∗ A.Heap lc blk sc ∗ stackAt sc.sp (112 + A.stackBytes)) ∗ hbInsertFrame s0 vPad)) :
    SepWP ((hbProg5 P).rebase P.pl5.base X) P.pl.base s0 (U64MapRepSlow P.pl A mapPtr m bm u ∗ A.Heap lc blk s0 ∗ stackAt s0.sp (176 + A.stackBytes)) post oom := by
  have hP := P.placeable5; have hb : (hbProg5 P).base = P.pl5.base := rfl
  have hstk_eq : stackAt s0.sp (176 + A.stackBytes) = stackAt (s0.sp - 64#64) (112 + A.stackBytes) ∗ memRegion (s0.sp - 64#64) 64 := by
    rw [show 176 + A.stackBytes = (112 + A.stackBytes) + 64 by omega]; exact stackAt_region s0.sp (112 + A.stackBytes) 64 (by omega)
  refine SepWP.mono_frozen (Φ := fun m => s0.mem.KeepsFrozen m)
    (post := fun sc Pc => ∃ vPad, sc.pc = P.pl.base ∧ sc.status = .Running ∧ sc.sp = s0.sp - 64#64 ∧ sc.spAligned = true ∧
      sc.readReg64 Reg.lr = P.pl5.base + 340#64 ∧ sc.readReg64 .x0 = mapPtr ∧ sc.readReg64 .x1 = 1#64 ∧ sc.readReg32 .x3 = 1#32 ∧
      sc.readReg64 .x19 = mapPtr ∧ sc.readReg64 .x20 = fxHash k ∧ sc.readReg64 .x21 = fxProd k ∧ sc.readReg64 .x22 = k ∧ sc.readReg64 .x23 = v ∧
      HbUpperSaved s0 sc ∧ StdStatePreserved s0 sc ∧ Pc = (U64MapRep P.pl A mapPtr m bm u ∗ A.Heap lc blk sc ∗ stackAt sc.sp (112 + A.stackBytes)) ∗ hbInsertFrame s0 vPad)
    (fun _ _ => Memory.KeepsFrozen.trans) (Memory.KeepsFrozen.refl s0.mem) ?_
    fun sc Pc _ _ hkf_c ⟨vPad, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ =>
      h16 ▸ hcont sc vPad h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 hkf_c
  refine SepWP.weaken_pre (P' := memRegion (s0.sp - 64#64) 64 ∗ ((∃∗ Rest : SepProp, ⌜((mapPtr + 16#64) ↦₆₄ 0#64) ∗ Rest ⊢ U64MapRep P.pl A mapPtr m bm u⌝ ∗
      ((mapPtr + 16#64) ↦₆₄ 0#64) ∗ Rest) ∗ A.Heap lc blk s0 ∗ stackAt (s0.sp - 64#64) (112 + A.stackBytes)))
    (by rw [hstk_eq]; exact Entails.trans (Entails.of_eq (show _ = memRegion (s0.sp - 64#64) 64 ∗
          (U64MapRepSlow P.pl A mapPtr m bm u ∗ (A.Heap lc blk s0 ∗ stackAt (s0.sp - 64#64) (112 + A.stackBytes))) by ac_rfl))
          (sepConj_mono_right (sepConj_mono_left (U64MapRepSlow_focus_gl0 P.pl A mapPtr m bm u)))) ?_
  refine hbInsert_prologue P X hpc hrun hsp0 fun s1 vPad hpc1 hrun1 hsp1 hsp1_al hx0_1 hx1_1 hx2_1 _ hup1 hstd1 => ?_
  have hrf1 : ReadyFrame s0 s0 s1 := ⟨hsp1, hup1, hstd1⟩; wp_conv_pre => rw [sepConj_comm (hbInsertFrame s0 vPad), sepConj_assoc]
  refine SepWP.of_sepExists_left fun Rest => ?_; wp_conv_pre => rw [sepConj_assoc]
  apply SepWP.pure_elim; intro hrepack; have hx0' : s1.readReg64 .x0 = mapPtr := hx0_1.trans hx0
  wp_sym_steps 14; apply sepWP_let_state; intro sc; have hrf_c : ReadyFrame s0 s0 sc := by dsimp [sc]; rf_simp hrf1
  have hsp_c : sc.sp = s0.sp - 64#64 := hrf_c.1
  refine SepWP.weaken_pre (P' := (U64MapRep P.pl A mapPtr m bm u ∗ A.Heap lc blk sc ∗ stackAt sc.sp (112 + A.stackBytes)) ∗ hbInsertFrame s0 vPad)
    (by rw [hsp_c]; exact Entails.trans (Entails.of_eq (show _ = ((((mapPtr + 16#64) ↦₆₄ 0#64) ∗ Rest) ∗
          A.Heap lc blk s0 ∗ stackAt (s0.sp - 64#64) (112 + A.stackBytes)) ∗ hbInsertFrame s0 vPad by ac_rfl))
          (sepConj_mono_left (sepConj_mono hrepack (sepConj_mono_left (A.heap_transport (StdStatePreserved.toHbVmPreserved hrf_c.2.2)))))) ?_
  exact SepWP.done (by simp [sc, wp_norm, arm64_norm]; bv_lin) (by simp [sc, wp_norm, arm64_norm, hrun1])
    ⟨vPad, by simp [sc, wp_norm, arm64_norm]; bv_lin, by simp [sc, wp_norm, arm64_norm, hrun1], hsp_c, by simpa [State.spAligned, hsp_c, hsp1] using hsp1_al,
     by simp [sc, wp_norm, arm64_norm], by simp [sc, wp_norm, arm64_norm, hx0'], by simp [sc, wp_norm, arm64_norm], by simp [sc, wp_norm, arm64_norm],
     by simp [sc, wp_norm, arm64_norm], by simp [sc, wp_norm, arm64_norm, hx1_1, hx1, fxHash, fxProd, fxSeed],
     by simp [sc, wp_norm, arm64_norm, hx1_1, hx1, fxProd, fxSeed], by simp [sc, wp_norm, arm64_norm, hx1_1, hx1],
     by simp [sc, wp_norm, arm64_norm, hx2_1, hx2], hrf_c.2.1, hrf_c.2.2, rfl⟩
private theorem hbInsert_postReserve_wp (P : HbPlaced) (A : HbAlloc) (X : String → Option (State → State))
    {s0 sr : State} {mapPtr k v bm vPad : BitVec 64} {m : Map64} {u lc blk : Nat} {R : SepProp}
    (hm_le_u : m.length ≤ u) (hcap_le_u : bucketMaskToCapacity bm ≤ u)
    (hsp0 : s0.spAligned = true) (hstk_nw : A.stackBytes + 176 ≤ 2 ^ 64) (hpcr : sr.pc = P.pl5.base + 340#64) (hrunr : sr.status = .Running)
    (hspr : sr.sp = s0.sp - 64#64) (hupr : HbUpperSaved s0 sr) (hasp_0r : AllocStatePreserved s0 sr) (hx19_r : sr.readReg64 .x19 = mapPtr)
    (hx20_r : sr.readReg64 .x20 = fxHash k) (hx21_r : sr.readReg64 .x21 = fxProd k) (hx22_r : sr.readReg64 .x22 = k) (hx23_r : sr.readReg64 .x23 = v) :
    SepWP ((hbProg5 P).rebase P.pl5.base X) (s0.readReg64 Reg.lr) sr
      ((stackAt (s0.sp - 64#64) (112 + A.stackBytes) ∗ (∃∗ bm' : BitVec 64, ⌜ValidNextMask m bm bm'⌝ ∗ U64MapRepReady P.pl A mapPtr m bm' ∗
          A.Heap ((lc + hbMapCost A bm') - hbMapCost A bm) ((blk + tableAllocBlocks bm') - tableAllocBlocks bm) sr)) ∗ hbInsertFrame s0 vPad)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R → sf.mem ⊨ (hashbrownInsertSpec P.pl A).post (mapPtr, m, bm, u, k, v, lc, blk) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) (fun _ => ⌜A.allowOom⌝) := by
  have hP := P.placeable5; have hb : (hbProg5 P).base = P.pl5.base := rfl
  have hstk_eq : stackAt s0.sp (176 + A.stackBytes) = stackAt (s0.sp - 64#64) (112 + A.stackBytes) ∗ memRegion (s0.sp - 64#64) 64 := by
    rw [show 176 + A.stackBytes = (112 + A.stackBytes) + 64 by omega]; exact stackAt_region s0.sp (112 + A.stackBytes) 64 (by omega)
  wp_conv_pre => rw [sepExists_sepConj_right]
  refine SepWP.of_sepExists_left fun bm' => ?_; wp_conv_pre => rw [sepConj_assoc, sepConj_comm (stackAt _ _), sepConj_assoc, sepConj_assoc]
  apply SepWP.pure_elim; intro hvnm
  refine SepWP.mono_frozen (Φ := fun m => sr.mem.KeepsFrozen m)
    (post := hbReadyPost P.pl A s0 sr mapPtr k v bm' m u (A.Heap ((lc + hbMapCost A bm') - hbMapCost A bm) ((blk + tableAllocBlocks bm') - tableAllocBlocks bm) sr ∗ stackAt (s0.sp - 64#64) (112 + A.stackBytes)))
    (fun _ _ => Memory.KeepsFrozen.trans) (Memory.KeepsFrozen.refl sr.mem) ?_ fun sf Pf _ _ hkf_rf ⟨hret, hspf, hcsf, hstd_rf, hPf⟩ => ⟨fun hm => ?_, hspf, hcsf⟩
  · have hrfr : ReadyFrame s0 sr sr := ⟨hspr, hupr, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩⟩; wp_sym_steps 4
    exact SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ = U64MapRepReady P.pl A mapPtr m bm' ∗
          (hbInsertFrame s0 vPad ∗ (A.Heap ((lc + hbMapCost A bm') - hbMapCost A bm) ((blk + tableAllocBlocks bm') - tableAllocBlocks bm) sr ∗
          stackAt (s0.sp - 64#64) (112 + A.stackBytes))) by ac_rfl))
        (sepConj_mono_left (U64MapRepReady_entails_U64MapRepFast P.pl A mapPtr m bm' hm_le_u)))
      (hbInsert_fromReady_wp P A X hsp0 (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrunr]) (by rf_simp hrfr)
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hx20_r]) (by simp [wp_norm, arm64_norm, hx21_r]))
  · have hasp_rf := StdStatePreserved.toAllocStatePreserved hstd_rf hkf_rf
    have hasp_0f : AllocStatePreserved s0 sf := ⟨hasp_rf.1.trans hasp_0r.1, hasp_rf.2.1.trans hasp_0r.2.1, hasp_rf.2.2.1.trans hasp_0r.2.2.1, hasp_rf.2.2.2.1.trans hasp_0r.2.2.2.1, hasp_0r.2.2.2.2.trans hasp_rf.2.2.2.2⟩
    dsimp only [hashbrownInsertSpec]; rw [hstk_eq]; refine Satisfies.mono (sepConj_mono_left (Entails.trans hPf (Entails.pure_right ⟨hret, hasp_0f⟩ ?_))) hm
    exact Entails.trans (Entails.of_eq (show _ = (stackAt (s0.sp - 64#64) (112 + A.stackBytes) ∗ memRegion (s0.sp - 64#64) 64) ∗
      (U64MapRep P.pl A mapPtr (cliMapInsert k v m) bm' (u + 1) ∗ A.Heap ((lc + hbMapCost A bm') - hbMapCost A bm) ((blk + tableAllocBlocks bm') - tableAllocBlocks bm) sr) by ac_rfl))
      (sepConj_mono_right (Entails.sepExists_right bm' (Entails.pure_right ⟨hvnm, fun _ => hcap_le_u⟩ (sepConj_mono_right (A.heap_transport (StdStatePreserved.toHbVmPreserved hstd_rf))))))
private theorem hbInsert_slow_infallible_wp (P : HbPlaced) (A : HbAlloc) (X : String → Option (State → State))
    (hreserve_inf : subroutine_ok ((hbProg5 P).rebase P.pl5.base X) P.pl.base
      (hashbrownLib.withCodeLoaded P.mpl (withCodeInv A (hashbrownReserveRehashOneInfallibleSpec P.pl A))))
    {s0 : State} {mapPtr k v bm : BitVec 64} {m : Map64} {u lc blk : Nat} {R : SepProp}
    (hcl0 : hashbrownLib.CodeLoaded P.mpl s0.mem)
    (hpc : s0.pc = P.pl5.base) (hrun : s0.status = .Running)
    (hsp0 : s0.spAligned = true) (hCode0 : A.CodeInv s0.mem) (hx0 : s0.readReg64 .x0 = mapPtr) (hx1 : s0.readReg64 .x1 = k) (hx2 : s0.readReg64 .x2 = v)
    (hstk_nw : A.stackBytes + 176 ≤ 2 ^ 64) (hm_le_u : m.length ≤ u) (hcap_le_u : bucketMaskToCapacity bm ≤ u) (hcan : HbCanReserveOne A m bm lc blk) :
    SepWP ((hbProg5 P).rebase P.pl5.base X) (s0.readReg64 Reg.lr) s0 (U64MapRepSlow P.pl A mapPtr m bm u ∗ A.Heap lc blk s0 ∗ stackAt s0.sp (176 + A.stackBytes))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R → sf.mem ⊨ (hashbrownInsertSpec P.pl A).post (mapPtr, m, bm, u, k, v, lc, blk) s0 sf ∗ R) ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) (fun _ => ⌜A.allowOom⌝) := by
  refine sepWP_seq_frozen (mid := P.pl.base) (Φ := fun _ => True) (fun _ _ _ _ => trivial) trivial
    (hbInsert_toReserveCall_wp P A X hpc hrun hsp0 hx0 hx1 hx2 hstk_nw fun sc vPad hpc_c hrun_c hsp_c hsp_c_al hlr_c hx0_c hx1_c hx3_c hx19_c hx20_c hx21_c hx22_c hx23_c hup_c hstd_c hkf_c _ => ?_)
  refine SepWP.call_subroutine_frame hreserve_inf (x := (mapPtr, m, bm, u, lc, blk)) (F := hbInsertFrame s0 vPad) (ret_pc := P.pl5.base + 340#64) hpc_c hrun_c hsp_c_al hlr_c
    (fun R' hm => by
      dsimp only [MultiPlacedLib.withCodeLoaded]
      rw [sepConj_comm ((withCodeInv A (hashbrownReserveRehashOneInfallibleSpec P.pl A)).pre _ sc), sepConj_assoc]
      refine (satisfies_pure_sepConj _ _ _).mpr ⟨hcl0.of_keepsFrozen hkf_c, ?_⟩
      dsimp only [withCodeInv, hashbrownReserveRehashOneInfallibleSpec]; rw [sepConj_assoc]
      refine (satisfies_pure_sepConj _ _ _).mpr ⟨A.codeInv_keepsFrozen hkf_c hCode0, ?_⟩; rw [sepConj_assoc]
      exact (satisfies_pure_sepConj _ _ _).mpr ⟨⟨hx0_c, hx1_c, hx3_c, by omega, hcan⟩, Satisfies.mono (Entails.of_eq (by ac_rfl)) hm⟩)
    (fun _ _ _ h => not_satisfies_false_sepConj h) (fun _ _ _ _ h => not_satisfies_false_sepConj h) (fun sr hpcr hrunr hspr hcsr => ?_)
    (fun R' sf _ h => by dsimp only [MultiPlacedLib.withCodeLoaded, withCodeInv, hashbrownReserveRehashOneInfallibleSpec] at h
                         exact (satisfies_pure_sepConj _ _ _).mpr ⟨((satisfies_pure_sepConj _ _ _).mp h).1, ((satisfies_pure_sepConj True R' sf.mem).mp (satisfies_true_sepConj_frame h)).2⟩)
  dsimp only [MultiPlacedLib.withCodeLoaded, withCodeInv, hashbrownReserveRehashOneInfallibleSpec]; wp_conv_pre => rw [sepConj_assoc]
  apply SepWP.pure_elim; rintro ⟨_, hasp_cr⟩; have hasp_0c := StdStatePreserved.toAllocStatePreserved hstd_c hkf_c
  rw [hsp_c]; exact hbInsert_postReserve_wp P A X hm_le_u hcap_le_u hsp0 hstk_nw hpcr hrunr (hspr.trans hsp_c) (hup_c.trans_cs hcsr)
    ⟨hasp_cr.1.trans hasp_0c.1, hasp_cr.2.1.trans hasp_0c.2.1, hasp_cr.2.2.1.trans hasp_0c.2.2.1, hasp_cr.2.2.2.1.trans hasp_0c.2.2.2.1, hasp_0c.2.2.2.2.trans hasp_cr.2.2.2.2⟩
    (hcsr.readReg64_x19.trans hx19_c) (hcsr.readReg64_x20.trans hx20_c) (hcsr.readReg64_x21.trans hx21_c) (hcsr.readReg64_x22.trans hx22_c) (hcsr.readReg64_x23.trans hx23_c)
theorem hashbrown_insert_infallible_ok (P : HbPlaced) (A : HbAlloc) (X : String → Option (State → State))
    (hreserve_inf : let prog := (hbProg P).rebase P.pl.base X; subroutine_ok prog (prog.fnAddr hbReserveRehashSym) (withCodeInv A (hashbrownReserveRehashOneInfallibleSpec P.pl A))) :
    let prog := (hbProg5 P).rebase P.pl5.base X
    subroutine_ok prog (prog.fnAddr "hashbrown_insert")
      (hashbrownLib.withCodeLoaded P.mpl (withCodeInv A (hashbrownInsertInfallibleSpec P.pl A))) := by
  have hP0 := P.placeable; have hb0 : (hbProg P).base = P.pl.base := rfl
  have hP := P.placeable5; have hb : (hbProg5 P).base = P.pl5.base := rfl
  dsimp only at hreserve_inf ⊢; simp only [hbReserveRehashSym, arm64_norm] at hreserve_inf
  have hres5_inf := hbSubroutineOk_crossBlock P (i := 5) (j := 0) (by decide) (by decide)
    (hbProg5_rebase P X) (hbProg_rebase P X) (hbWithCodeLoaded_of_plain P.mpl hreserve_inf)
  apply subroutine_ok_of_sepWP_init; rintro ⟨mapPtr, m, bm, u, k, v, lc, blk⟩ R s0 hpc hrun hpre hsp0
  simp only [arm64_norm] at hpc
  dsimp only [MultiPlacedLib.withCodeLoaded] at hpre ⊢
  rw [sepConj_comm ((withCodeInv A (hashbrownInsertInfallibleSpec P.pl A)).pre _ s0), sepConj_assoc] at hpre
  obtain ⟨hcl0, hpre⟩ := (satisfies_pure_sepConj _ _ _).mp hpre
  dsimp only [withCodeInv, hashbrownInsertInfallibleSpec] at hpre ⊢
  rw [sepConj_assoc] at hpre; obtain ⟨hCode0, hpre⟩ := (satisfies_pure_sepConj _ _ _).mp hpre; rw [sepConj_assoc] at hpre
  obtain ⟨⟨hx0, hx1, hx2, hstk_nw, hcan⟩, hpre⟩ := (satisfies_pure_sepConj _ _ _).mp hpre; rw [sepConj_assoc] at hpre
  rcases satisfies_U64MapRep_cases hpre with hready | hslow
  · rw [← sepConj_assoc] at hready; exact ⟨_, hready, hbInsert_fast_wp P A X hpc hrun hsp0 hx0 hx1 hx2 hstk_nw⟩
  · obtain ⟨hm_le_u, hcap_le_u⟩ := U64MapRepSlow_bounds hslow
    have hcan_res : HbCanReserveOne A m bm lc blk := hcan.resolve_left (by omega)
    rw [← sepConj_assoc] at hslow; exact ⟨_, hslow, hbInsert_slow_infallible_wp P A X hres5_inf hcl0 hpc hrun hsp0 hCode0 hx0 hx1 hx2 hstk_nw hm_le_u hcap_le_u hcan_res⟩
theorem hashbrown_insert_ok (P : HbPlaced) (A : HbAlloc) (X : String → Option (State → State))
    (hreserve_inf : let prog := (hbProg P).rebase P.pl.base X; subroutine_ok prog (prog.fnAddr hbReserveRehashSym) (withCodeInv A (hashbrownReserveRehashOneInfallibleSpec P.pl A)))
    (hreserve : let prog := (hbProg P).rebase P.pl.base X; subroutine_ok prog (prog.fnAddr hbReserveRehashSym) (hashbrownLib.withCodeLoaded P.mpl (withCodeInv A (hashbrownReserveRehashOneSpec P.pl A)))) :
    let prog := (hbProg5 P).rebase P.pl5.base X
    subroutine_ok prog (prog.fnAddr "hashbrown_insert")
      (hashbrownLib.withCodeLoaded P.mpl (withCodeInv A (hashbrownInsertSpec P.pl A))) := by
  have hP0 := P.placeable; have hb0 : (hbProg P).base = P.pl.base := rfl
  have hP := P.placeable5; have hb : (hbProg5 P).base = P.pl5.base := rfl
  dsimp only at hreserve_inf hreserve ⊢; simp only [hbReserveRehashSym, arm64_norm] at hreserve_inf hreserve
  have hres5_inf := hbSubroutineOk_crossBlock P (i := 5) (j := 0) (by decide) (by decide)
    (hbProg5_rebase P X) (hbProg_rebase P X) (hbWithCodeLoaded_of_plain P.mpl hreserve_inf)
  have hres5 := hbSubroutineOk_crossBlock P (i := 5) (j := 0) (by decide) (by decide)
    (hbProg5_rebase P X) (hbProg_rebase P X) hreserve
  apply subroutine_ok_of_sepWPp_init; rintro ⟨mapPtr, m, bm, u, k, v, lc, blk⟩ R s0 hpc hrun hpre hsp0
  simp only [arm64_norm] at hpc
  dsimp only [MultiPlacedLib.withCodeLoaded] at hpre ⊢
  rw [sepConj_comm ((withCodeInv A (hashbrownInsertSpec P.pl A)).pre _ s0), sepConj_assoc] at hpre
  obtain ⟨hcl0, hpre⟩ := (satisfies_pure_sepConj _ _ _).mp hpre
  dsimp only [withCodeInv, hashbrownInsertSpec] at hpre ⊢
  rw [sepConj_assoc] at hpre; obtain ⟨hCode0, hpre⟩ := (satisfies_pure_sepConj _ _ _).mp hpre; rw [sepConj_assoc] at hpre
  obtain ⟨⟨hx0, hx1, hx2, hstk_nw, himp_can⟩, hpre⟩ := (satisfies_pure_sepConj _ _ _).mp hpre; rw [sepConj_assoc] at hpre
  rcases satisfies_U64MapRep_cases hpre with hready | hslow
  · rw [← sepConj_assoc] at hready; exact ⟨_, hready, SepWPp.of_sepWP_ret (hbInsert_fast_wp P A X hpc hrun hsp0 hx0 hx1 hx2 hstk_nw)⟩
  · obtain ⟨hm_le_u, hcap_le_u⟩ := U64MapRepSlow_bounds hslow
    rw [← sepConj_assoc] at hslow; by_cases hcan : HbCanReserveOne A m bm lc blk
    · exact ⟨_, hslow, SepWPp.of_sepWP_ret (hbInsert_slow_infallible_wp P A X hres5_inf hcl0 hpc hrun hsp0 hCode0 hx0 hx1 hx2 hstk_nw hm_le_u hcap_le_u hcan)⟩
    · have hnot_ins : ¬ HbCanInsertOne A m bm u lc blk := fun h => h.elim (by omega) hcan
      have hao : A.allowOom := Classical.byContradiction fun hna => hnot_ins (himp_can hna)
      refine ⟨_, hslow, SepWPp.of_sepWP (mid := P.pl.base) (hbInsert_toReserveCall_wp P A X hpc hrun hsp0 hx0 hx1 hx2 hstk_nw
        fun sc vPad hpc_c hrun_c hsp_c hsp_c_al hlr_c hx0_c hx1_c hx3_c hx19_c hx20_c hx21_c hx22_c hx23_c hup_c hstd_c hkf_c => ?_)⟩
      refine SepWPp.call (x := (mapPtr, m, bm, u, lc, blk)) (F := hbInsertFrame s0 vPad) hres5 hpc_c hrun_c hsp_c_al hlr_c
        (fun R' hm => by
          dsimp only [MultiPlacedLib.withCodeLoaded]
          rw [sepConj_comm ((withCodeInv A (hashbrownReserveRehashOneSpec P.pl A)).pre _ sc), sepConj_assoc]
          refine (satisfies_pure_sepConj _ _ _).mpr ⟨hcl0.of_keepsFrozen hkf_c, ?_⟩
          dsimp only [withCodeInv, hashbrownReserveRehashOneSpec]; rw [sepConj_assoc]
          refine (satisfies_pure_sepConj _ _ _).mpr ⟨A.codeInv_keepsFrozen hkf_c hCode0, ?_⟩; rw [sepConj_assoc]
          exact (satisfies_pure_sepConj _ _ _).mpr ⟨⟨hx0_c, hx1_c, hx3_c, by omega, fun hna => (hna hao).elim⟩, Satisfies.mono (Entails.of_eq (by ac_rfl)) hm⟩)
        (fun _ _ _ _ h => not_satisfies_false_sepConj h)
        (fun sf _ hmf => (satisfies_pure_sepConj _ R sf.mem).mpr ⟨⟨hao, hnot_ins⟩, ((satisfies_pure_sepConj True R sf.mem).mp (satisfies_true_sepConj hmf)).2⟩)
        (fun sr hpcr hrunr hspr hcsr => ?_)
        (fun sf R' _ h => by dsimp only [MultiPlacedLib.withCodeLoaded, withCodeInv, hashbrownReserveRehashOneSpec] at h
                             exact (satisfies_pure_sepConj _ _ _).mpr ⟨((satisfies_pure_sepConj _ _ _).mp h).1, ((satisfies_pure_sepConj True R' sf.mem).mp (satisfies_true_sepConj_frame h)).2⟩)
      dsimp only [MultiPlacedLib.withCodeLoaded, withCodeInv, hashbrownReserveRehashOneSpec]; refine SepWPp.congr_pre (by rw [sepConj_assoc]) ?_
      apply SepWPp.pure_left; rintro ⟨_, hasp_cr⟩; apply SepWPp.of_sepWP_ret; have hasp_0c := StdStatePreserved.toAllocStatePreserved hstd_c hkf_c
      rw [hsp_c]; exact hbInsert_postReserve_wp P A X hm_le_u hcap_le_u hsp0 hstk_nw hpcr hrunr (hspr.trans hsp_c) (hup_c.trans_cs hcsr)
        ⟨hasp_cr.1.trans hasp_0c.1, hasp_cr.2.1.trans hasp_0c.2.1, hasp_cr.2.2.1.trans hasp_0c.2.2.1, hasp_cr.2.2.2.1.trans hasp_0c.2.2.2.1, hasp_0c.2.2.2.2.trans hasp_cr.2.2.2.2⟩
        (hcsr.readReg64_x19.trans hx19_c) (hcsr.readReg64_x20.trans hx20_c) (hcsr.readReg64_x21.trans hx21_c) (hcsr.readReg64_x22.trans hx22_c) (hcsr.readReg64_x23.trans hx23_c)
end MachineProofs
set_option maxRecDepth 200000 in
theorem hashbrown_insert_infallible_subroutineOk (A : Obj.MultiPlacement → HbAlloc) (X : String → Option (State → State) := fun _ => none)
    (hreserve_inf : ∀ P : HbPlaced, let prog := (hbProg P).rebase P.pl.base X
      subroutine_ok prog (prog.fnAddr hbReserveRehashSym) (withCodeInv (A P.mpl) (hashbrownReserveRehashOneInfallibleSpec P.pl (A P.mpl)))) :
    hashbrownLib.subroutineOk "hashbrown_insert"
      (fun mpl => withCodeInv (A mpl) (hashbrownInsertInfallibleSpec (mplAsPl mpl) (A mpl))) X :=
  hbMultiSubroutineOk_of_withCL "hashbrown_insert" 5 (off := 0) (fun P X' => hbProg5_rebase P X')
    (fun mpl => withCodeInv (A mpl) (hashbrownInsertInfallibleSpec (mplAsPl mpl) (A mpl))) X
    (hok := fun P => hbPl_eq_mplAsPl P ▸ hashbrown_insert_infallible_ok P (A P.mpl) X (hreserve_inf P))
set_option maxRecDepth 200000 in
theorem hashbrown_insert_subroutineOk (A : Obj.MultiPlacement → HbAlloc) (X : String → Option (State → State) := fun _ => none)
    (hreserve_inf : ∀ P : HbPlaced, let prog := (hbProg P).rebase P.pl.base X
      subroutine_ok prog (prog.fnAddr hbReserveRehashSym) (withCodeInv (A P.mpl) (hashbrownReserveRehashOneInfallibleSpec P.pl (A P.mpl))))
    (hreserve : ∀ P : HbPlaced, let prog := (hbProg P).rebase P.pl.base X
      subroutine_ok prog (prog.fnAddr hbReserveRehashSym)
        (hashbrownLib.withCodeLoaded P.mpl (withCodeInv (A P.mpl) (hashbrownReserveRehashOneSpec P.pl (A P.mpl))))) :
    hashbrownLib.subroutineOk "hashbrown_insert"
      (fun mpl => withCodeInv (A mpl) (hashbrownInsertSpec (mplAsPl mpl) (A mpl))) X :=
  hbMultiSubroutineOk_of_withCL "hashbrown_insert" 5 (off := 0) (fun P X' => hbProg5_rebase P X')
    (fun mpl => withCodeInv (A mpl) (hashbrownInsertSpec (mplAsPl mpl) (A mpl))) X
    (hok := fun P => hbPl_eq_mplAsPl P ▸ hashbrown_insert_ok P (A P.mpl) X (hreserve_inf P) (hreserve P))
end CaseStudies.Hashbrown.Proofs
