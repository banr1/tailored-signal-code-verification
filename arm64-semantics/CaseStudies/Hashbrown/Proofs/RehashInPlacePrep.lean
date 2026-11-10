/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import CaseStudies.Hashbrown.Proofs.Lookup
public import ProofLib.SepLogic.WPFrozen
import ProofLib.SepLogic.Entry
import ProofLib.SepLogic.SymWP
import ProofLib.SepLogic.LoopTactics
import ProofLib.BV.ReflectROBDD

/-!
# In-Place Rehash Preparation and Invariant

Defines the intermediate table invariant `RehashTableInv` for `RawTable::rehash_in_place` and
verifies the SIMD control-tag conversion loop, epilogue, and 4-bucket case inside `reserve_rehash`.
-/

set_option autoImplicit false

@[expose] public section

namespace CaseStudies.Hashbrown.Proofs

open Arm64 Arm64.Obj Arm64.Rust ProofLib ProofLib.StdStartup
open CaseStudies.Hashbrown

/-! ## Tag Conversion and Mirror Indexing -/

def prepCtrlByte (b : BitVec 8) : BitVec 8 := if isSpecialTag b then tagEmpty else tagDeleted

theorem prepCtrlByte_validTag (b : BitVec 8) : ValidTag (prepCtrlByte b) := by
  unfold prepCtrlByte; split
  · exact ValidTag.empty
  · exact ValidTag.deleted

theorem isFullTag_prepCtrlByte (b : BitVec 8) : isFullTag (prepCtrlByte b) = false := by
  unfold prepCtrlByte; split <;> simp

theorem not_special_iff_full (b : BitVec 8) : (isSpecialTag b = false) ↔ (isFullTag b = true) := by
  constructor
  · intro hs; have hnot : ¬ (0x80 ≤ b.toNat) := fun hge => by
      rw [(isSpecialTag_iff_ge_0x80 b).mpr hge] at hs; cases hs
    exact (isFullTag_iff_lt_0x80 b).mpr (by omega)
  · intro hf; have hlt := (isFullTag_iff_lt_0x80 b).mp hf
    cases hs : isSpecialTag b with
    | false => rfl
    | true => have := (isSpecialTag_iff_ge_0x80 b).mp hs; omega

theorem prepCtrlByte_beq_deleted (b : BitVec 8) : (prepCtrlByte b == tagDeleted) = isFullTag b := by
  unfold prepCtrlByte; cases hs : isSpecialTag b with
  | true =>
    have hf : isFullTag b = false := by
      cases hfb : isFullTag b with
      | false => rfl
      | true => have := (isFullTag_iff_lt_0x80 b).mp hfb; have := (isSpecialTag_iff_ge_0x80 b).mp hs; omega
    simp [hf]; decide
  | false => simp [(not_special_iff_full b).mp hs]

def setCtrlBytes (bm : BitVec 64) (ctrl : List (BitVec 8)) (idx : Nat) (tag : BitVec 8) : List (BitVec 8) :=
  (ctrl.set idx tag).set (setCtrlMirrorIdx bm idx) tag

theorem setCtrlMirrorIdx_ge8 {bm : BitVec 64} (hbm : ValidBucketMask bm)
    (hge8 : 8 ≤ bm.toNat + 1) {idx : Nat} (hidx : idx < bm.toNat + 1) :
    setCtrlMirrorIdx bm idx = if idx < 8 then (bm.toNat + 1) + idx else idx := by
  rcases hbm.buckets_bounds_dvd with ⟨_, hb58, hdvd⟩
  have h58 : 2 ^ 58 + 16 < 2 ^ 64 := by decide
  unfold setCtrlMirrorIdx; split
  · rename_i hlt8
    have hsub : BitVec.ofNat 64 idx - 8#64 = BitVec.ofNat 64 (2 ^ 64 - 8 + idx) := by
      have hmod2 : BitVec.ofNat 64 (2 ^ 64 + idx) = BitVec.ofNat 64 idx := by
        apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ofNat]
      rw [← hmod2, show 2 ^ 64 + idx = (2 ^ 64 - 8 + idx) + 8 by omega, BitVec.ofNat_add]; bv_lin
    have hmod : (2 ^ 64 - 8 + idx) % (bm.toNat + 1) = (bm.toNat + 1) - 8 + idx := by
      rcases hdvd with ⟨k, hk⟩; have h264 : 0 < 2 ^ 64 := by decide
      have hk1 : 1 ≤ k := by cases k with | zero => simp at hk | succ _ => omega
      have hmul : (bm.toNat + 1) * k = (bm.toNat + 1) + (bm.toNat + 1) * (k - 1) := by
        conv => lhs; rw [show k = 1 + (k - 1) by omega, Nat.mul_add, Nat.mul_one]
      rw [show 2 ^ 64 - 8 + idx = ((bm.toNat + 1) - 8 + idx) + (bm.toNat + 1) * (k - 1) by omega,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    have hand : (BitVec.ofNat 64 (2 ^ 64 - 8 + idx) &&& bm) = BitVec.ofNat 64 ((bm.toNat + 1) - 8 + idx) := by
      apply BitVec.eq_of_toNat_eq; rw [hbm.and_toNat_eq_mod, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : 2 ^ 64 - 8 + idx < 2 ^ 64), hmod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [hsub, hand, show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, ← BitVec.ofNat_add,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
  · rename_i hge
    have hsub : BitVec.ofNat 64 idx - 8#64 = BitVec.ofNat 64 (idx - 8) := by
      conv => lhs; arg 1; rw [show idx = (idx - 8) + 8 by omega]
      rw [BitVec.ofNat_add]; bv_lin
    have hand : (BitVec.ofNat 64 (idx - 8) &&& bm) = BitVec.ofNat 64 (idx - 8) := by
      apply BitVec.eq_of_toNat_eq; rw [hbm.and_toNat_eq_mod, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hsub, hand, show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, ← BitVec.ofNat_add,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega

theorem setCtrlBytes_length (bm : BitVec 64) (ctrl : List (BitVec 8)) (idx : Nat) (tag : BitVec 8) :
    (setCtrlBytes bm ctrl idx tag).length = ctrl.length := by simp [setCtrlBytes]

theorem setCtrlBytes_getElem_lt {bm : BitVec 64} (hbm : ValidBucketMask bm) (hge8 : 8 ≤ bm.toNat + 1)
    {ctrl : List (BitVec 8)} (hlen : ctrl.length = (bm.toNat + 1) + 8)
    {idx q : Nat} (hidx : idx < bm.toNat + 1) (hq : q < bm.toNat + 1) (tag : BitVec 8) :
    (setCtrlBytes bm ctrl idx tag)[q]'(by rw [setCtrlBytes_length]; omega) =
      if q = idx then tag else ctrl[q]'(by omega) := by
  change ((ctrl.set idx tag).set (setCtrlMirrorIdx bm idx) tag)[q]'(by simp; omega) = _
  have hmir := setCtrlMirrorIdx_ge8 hbm hge8 hidx
  by_cases hlt8 : idx < 8
  · simp only [hlt8, ↓reduceIte] at hmir; rw [List.getElem_set, List.getElem_set]
    simp only [hmir, show (bm.toNat + 1) + idx ≠ q by omega, ↓reduceIte]
    by_cases hqi : idx = q
    · subst hqi; simp
    · simp [hqi, Ne.symm hqi]
  · simp only [hlt8, ↓reduceIte] at hmir; rw [List.getElem_set, List.getElem_set]; simp only [hmir]
    by_cases hqi : idx = q
    · subst hqi; simp
    · simp [hqi, Ne.symm hqi]

theorem setCtrlBytes_mirror {bm : BitVec 64} (hbm : ValidBucketMask bm) (hge8 : 8 ≤ bm.toNat + 1)
    {ctrl : List (BitVec 8)} (hm : CtrlMirrorInv (bm.toNat + 1) ctrl)
    {idx : Nat} (hidx : idx < bm.toNat + 1) {tag : BitVec 8} (htag : ValidTag tag) :
    CtrlMirrorInv (bm.toNat + 1) (setCtrlBytes bm ctrl idx tag) := by
  have hlen : ctrl.length = (bm.toNat + 1) + 8 := hm.1
  have hmir_idx := setCtrlMirrorIdx_ge8 hbm hge8 hidx
  refine ⟨by rw [setCtrlBytes_length]; exact hlen, ?_, fun _ => by omega, ?_⟩
  · intro b hb; unfold setCtrlBytes at hb
    rcases List.mem_or_eq_of_mem_set hb with hb1 | rfl
    · rcases List.mem_or_eq_of_mem_set hb1 with hb0 | rfl
      · exact hm.2.1 b hb0
      · exact htag
    · exact htag
  · intro _ j hj
    rw [List.getElem?_eq_getElem (by rw [setCtrlBytes_length]; omega),
      List.getElem?_eq_getElem (by rw [setCtrlBytes_length]; omega)]; congr 1
    unfold setCtrlBytes; by_cases hlt8 : idx < 8
    · simp only [hlt8, ↓reduceIte] at hmir_idx
      rw [List.getElem_set, List.getElem_set, List.getElem_set, List.getElem_set]; simp only [hmir_idx]
      by_cases hij : idx = j
      · subst hij; simp
      · simp only [show (bm.toNat + 1) + idx ≠ (bm.toNat + 1) + j by omega,
          show idx ≠ (bm.toNat + 1) + j by omega, show (bm.toNat + 1) + idx ≠ j by omega, hij, ↓reduceIte]
        have h0 := hm.2.2.2 hge8 j hj
        rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at h0; injection h0
    · simp only [hlt8, ↓reduceIte] at hmir_idx
      rw [List.getElem_set, List.getElem_set, List.getElem_set, List.getElem_set]
      simp only [hmir_idx, show idx ≠ (bm.toNat + 1) + j by omega, show idx ≠ j by omega, ↓reduceIte]
      have h0 := hm.2.2.2 hge8 j hj
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at h0; injection h0

private theorem bv64_xor_and_div8 {a b bm : BitVec 64} (hlt : ((a ^^^ b) &&& bm).toNat < 8) :
    (a &&& bm).toNat / 8 = (b &&& bm).toNat / 8 := by
  have hsh : (a &&& bm) >>> 3 = (b &&& bm) >>> 3 := by
    ext k hk; rw [← BitVec.getLsbD_eq_getElem hk, ← BitVec.getLsbD_eq_getElem hk,
      BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ushiftRight]
    by_cases hk64 : 3 + k < 64
    · have hw : (((a ^^^ b) &&& bm)).getLsbD (3 + k) = false := by
        rw [BitVec.getLsbD_eq_getElem hk64, BitVec.getElem_eq_testBit_toNat]
        exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hlt
          (Nat.le_trans (by decide : 8 ≤ 2 ^ 3) (Nat.pow_le_pow_right (by decide) (by omega))))
      rw [BitVec.getLsbD_and, BitVec.getLsbD_xor] at hw; rw [BitVec.getLsbD_and, BitVec.getLsbD_and]
      cases h1 : bm.getLsbD (3 + k) <;> cases h2 : a.getLsbD (3 + k) <;>
        cases h3 : b.getLsbD (3 + k) <;> simp_all
    · simp [BitVec.getLsbD_of_ge _ _ (by omega : 64 ≤ 3 + k)]
  simpa [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] using congrArg BitVec.toNat hsh

private theorem bv64_add_sub_cancel_left (a b : BitVec 64) : a + b - a = b := by
  rw [BitVec.add_comm, BitVec.add_sub_cancel]

private theorem ValidBucketMask.sub_and_eq_left {bm : BitVec 64} (hbm : ValidBucketMask bm) (x y : BitVec 64) :
    (((x &&& bm) - y) &&& bm) = ((x - y) &&& bm) := by
  rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg x y, hbm.add_and_eq]

theorem ne_of_not_sameGroup {bm : BitVec 64} {new_i i pos0 : Nat}
    (h : ¬ (((BitVec.ofNat 64 new_i - BitVec.ofNat 64 pos0) ^^^
              (BitVec.ofNat 64 i - BitVec.ofNat 64 pos0)) &&& bm).toNat < 8) : new_i ≠ i := by
  rintro rfl; apply h; simp only [BitVec.xor_self, BitVec.zero_and]; decide

private theorem probePos_step_bv_group {bm k : BitVec 64} (hbm : ValidBucketMask bm)
    (hge8 : 8 ≤ bm.toNat + 1) (hdvd8 : (bm.toNat + 1) % 8 = 0) (step : Nat) :
    BitVec.ofNat 64 (probePos bm k step) =
      (BitVec.ofNat 64 (probePos bm k 0) +
        BitVec.ofNat 64 (8 * (triGroupIdx step % ((bm.toNat + 1) / 8)))) &&& bm := by
  have hb58 : bm.toNat + 1 ≤ 2 ^ 58 := hbm.buckets_bounds_dvd.2.1
  have hp0_lt := probePos_lt_buckets hbm k 0
  have hps_lt := probePos_lt_buckets hbm k step
  generalize hG : (bm.toNat + 1) / 8 = G
  have hbuck : bm.toNat + 1 = 8 * G := by omega
  generalize hg : triGroupIdx step % G = g_step
  have hg_lt : g_step < G := by rw [← hg]; exact Nat.mod_lt _ (by omega)
  have hpos_eq : probePos bm k step = (probePos bm k 0 + 8 * g_step) % (bm.toNat + 1) := by
    rw [probePos_eq_add_mod hbm k step, ← hg, hbuck,
      Nat.add_mod, Nat.mul_mod_mul_left 8 (triGroupIdx step) G, Nat.mod_add_mod]
  apply BitVec.eq_of_toNat_eq
  rw [← BitVec.ofNat_add, hbm.and_toNat_eq_mod, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : probePos bm k 0 + 8 * g_step < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : probePos bm k step < 2 ^ 64), hpos_eq]

private theorem probe_lane_diff_and_bm {bm k : BitVec 64} (hbm : ValidBucketMask bm)
    (hge8 : 8 ≤ bm.toNat + 1) (hdvd8 : (bm.toNat + 1) % 8 = 0)
    {step lane : Nat} (hlane : lane < 8) :
    ((BitVec.ofNat 64 ((probePos bm k step + lane) % (bm.toNat + 1)) -
        BitVec.ofNat 64 (probePos bm k 0)) &&& bm) =
      BitVec.ofNat 64 (8 * (triGroupIdx step % ((bm.toNat + 1) / 8)) + lane) := by
  have hb58 : bm.toNat + 1 ≤ 2 ^ 58 := hbm.buckets_bounds_dvd.2.1
  have hpos_bv := probePos_step_bv_group hbm hge8 hdvd8 (k := k) step
  generalize hG : (bm.toNat + 1) / 8 = G at hpos_bv ⊢
  have hbuck : bm.toNat + 1 = 8 * G := by omega
  generalize hg : triGroupIdx step % G = g_step at hpos_bv ⊢
  have hg_lt : g_step < G := by rw [← hg]; exact Nat.mod_lt _ (by omega)
  rw [← hbm.laneIdx_bv (probePos_lt_buckets hbm k step) hlane, hpos_bv,
    hbm.add_and_eq, BitVec.add_assoc, ← BitVec.ofNat_add, ValidBucketMask.sub_and_eq_left hbm,
    bv64_add_sub_cancel_left]
  apply BitVec.eq_of_toNat_eq
  rw [hbm.and_toNat_eq_mod, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : 8 * g_step + lane < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : 8 * g_step + lane < bm.toNat + 1)]

theorem exists_lane_of_sameGroup {bm k : BitVec 64} (hbm : ValidBucketMask bm)
    (hge8 : 8 ≤ bm.toNat + 1) (hdvd8 : (bm.toNat + 1) % 8 = 0)
    {step lane i : Nat} (hlane : lane < 8) (hi : i < bm.toNat + 1)
    (hsame : (((BitVec.ofNat 64 ((probePos bm k step + lane) % (bm.toNat + 1)) -
                 BitVec.ofNat 64 (probePos bm k 0)) ^^^
                (BitVec.ofNat 64 i - BitVec.ofNat 64 (probePos bm k 0))) &&& bm).toNat < 8) :
    ∃ lane_i < 8, (probePos bm k step + lane_i) % (bm.toNat + 1) = i := by
  have hb58 : bm.toNat + 1 ≤ 2 ^ 58 := hbm.buckets_bounds_dvd.2.1
  have hi64 : i < 2 ^ 64 := by omega
  have hd_new := probe_lane_diff_and_bm hbm hge8 hdvd8 (k := k) (step := step) hlane
  have hpos_bv := probePos_step_bv_group hbm hge8 hdvd8 (k := k) step
  have hdiv := bv64_xor_and_div8 hsame
  generalize hG : (bm.toNat + 1) / 8 = G at hd_new hpos_bv
  have hbuck : bm.toNat + 1 = 8 * G := by omega
  generalize hg : triGroupIdx step % G = g_step at hd_new hpos_bv
  have hg_lt : g_step < G := by rw [← hg]; exact Nat.mod_lt _ (by omega)
  rw [hd_new, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 8 * g_step + lane < 2 ^ 64)] at hdiv
  generalize hdi_def : ((BitVec.ofNat 64 i - BitVec.ofNat 64 (probePos bm k 0)) &&& bm) = d_i_bv at hdiv
  have hdiv_eq : d_i_bv.toNat / 8 = g_step := hdiv.symm.trans (by omega)
  have hli_lt : d_i_bv.toNat % 8 < 8 := Nat.mod_lt _ (by decide)
  have hdi_decomp : d_i_bv.toNat = 8 * g_step + d_i_bv.toNat % 8 := by
    have := Nat.div_add_mod d_i_bv.toNat 8; omega
  generalize hli_def : d_i_bv.toNat % 8 = lane_i at hli_lt hdi_decomp
  refine ⟨lane_i, hli_lt, ?_⟩
  have hdi_bv : d_i_bv = BitVec.ofNat 64 (8 * g_step) + BitVec.ofNat 64 lane_i := by
    rw [← BitVec.ofNat_add, ← hdi_decomp, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hi_bv : ((BitVec.ofNat 64 (probePos bm k 0) + d_i_bv) &&& bm) = BitVec.ofNat 64 i := by
    rw [← hdi_def, BitVec.add_comm, hbm.add_and_eq, BitVec.sub_add_cancel]
    apply BitVec.eq_of_toNat_eq
    rw [hbm.and_toNat_eq_mod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64, Nat.mod_eq_of_lt hi]
  have hpos_lane_bv : ((BitVec.ofNat 64 (probePos bm k 0) + d_i_bv) &&& bm) =
      BitVec.ofNat 64 ((probePos bm k step + lane_i) % (bm.toNat + 1)) := by
    rw [hdi_bv, ← BitVec.add_assoc,
      ← hbm.add_and_eq (BitVec.ofNat 64 (probePos bm k 0) + BitVec.ofNat 64 (8 * g_step)),
      ← hpos_bv, hbm.laneIdx_bv (probePos_lt_buckets hbm k step) hli_lt]
  have hnat := congrArg BitVec.toNat (hi_bv.symm.trans hpos_lane_bv)
  have hmod_lt : (probePos bm k step + lane_i) % (bm.toNat + 1) < 2 ^ 64 :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega)) (by omega)
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64, Nat.mod_eq_of_lt hmod_lt] at hnat
  exact hnat.symm

/-! ## In-Place Rehash Invariant -/

def isActiveRehashTag (b : BitVec 8) : Bool := isFullTag b || (b == tagDeleted)

private theorem countP_eq_map_count {α : Type} (p : α → Bool) (xs : List α) :
    xs.countP p = (xs.map p).count true := by
  induction xs with | nil => rfl | cons x rest ih => simp [List.countP_cons, List.count_cons, ih]

private theorem countP_take_congr {xs ys : List (BitVec 8)} {p q : BitVec 8 → Bool} {n : Nat}
    (hx : n ≤ xs.length) (hy : n ≤ ys.length)
    (heq : ∀ i (hi : i < n), p (xs[i]'(by omega)) = q (ys[i]'(by omega))) :
    (xs.take n).countP p = (ys.take n).countP q := by
  rw [countP_eq_map_count, countP_eq_map_count]; congr 1; apply List.ext_getElem
  · simp [Nat.min_eq_left hx, Nat.min_eq_left hy]
  · intro i hi1 _; simp only [List.length_map, List.length_take, Nat.min_eq_left hx] at hi1
    simp only [List.getElem_map, List.getElem_take]; exact heq i hi1

private theorem bool_count_set_true (bs : List Bool) :
    ∀ (idx : Nat) (h : idx < bs.length), bs[idx] = false → (bs.set idx true).count true = bs.count true + 1 := by
  induction bs with
  | nil => intro _ h; simp at h
  | cons b rest ih =>
    intro idx h hb; cases idx with
    | zero => simp only [List.getElem_cons_zero] at hb; subst hb; simp
    | succ idx =>
      simp only [List.length_cons] at h; simp only [List.getElem_cons_succ] at hb
      simp only [List.set_cons_succ, List.count_cons, ih idx (by omega) hb]; omega

private theorem countP_take_flip_down {xs ys : List (BitVec 8)} {p : BitVec 8 → Bool}
    {n idx : Nat} (hx : n ≤ xs.length) (hy : n ≤ ys.length) (hidx : idx < n)
    (ht : p (xs[idx]'(by omega)) = true) (hf : p (ys[idx]'(by omega)) = false)
    (hrest : ∀ i (hi : i < n), i ≠ idx → p (xs[i]'(by omega)) = p (ys[i]'(by omega))) :
    (ys.take n).countP p + 1 = (xs.take n).countP p := by
  rw [countP_eq_map_count, countP_eq_map_count]
  have hset : (xs.take n).map p = ((ys.take n).map p).set idx true := by
    apply List.ext_getElem (by simp [Nat.min_eq_left hx, Nat.min_eq_left hy]); intro i hi1 _
    simp only [List.length_map, List.length_take, Nat.min_eq_left hx] at hi1
    rw [List.getElem_set]; by_cases hii : idx = i
    · subst hii; simp [List.getElem_take, ht]
    · simp [hii, List.getElem_take, hrest i hi1 (Ne.symm hii)]
  rw [hset, bool_count_set_true ((ys.take n).map p) idx
    (by simp [Nat.min_eq_left hy, hidx]) (by simp [List.getElem_take, hf])]

/-- Data-structure invariant across the outer/inner re-probe and swap loops of `rehash_in_place`
    for `8 ≤ buckets` (`8 ∣ buckets`). -/
structure RehashTableInv (bm : BitVec 64) (m : Map64)
    (ctrl : List (BitVec 8)) (slots : List (BitVec 64 × BitVec 64)) : Prop where
  validMask : ValidBucketMask bm
  wf : Map64Wf m
  ge8 : 8 ≤ bm.toNat + 1
  dvd8 : (bm.toNat + 1) % 8 = 0
  slots_len : slots.length = bm.toNat + 1
  mirror : CtrlMirrorInv (bm.toNat + 1) ctrl
  has_empty : ∃ (e : Nat) (_ : e < bm.toNat + 1), ctrl[e]'(by have := mirror.1; omega) = tagEmpty
  countActive_eq : (ctrl.take (bm.toNat + 1)).countP isActiveRehashTag = m.length
  active_lookup : ∀ (q : Nat) (hq : q < bm.toNat + 1),
    isActiveRehashTag (ctrl[q]'(by have := mirror.1; omega)) = true →
    cliMapLookup (slots[q]'(by omega)).1 m = some (slots[q]'(by omega)).2
  active_inj : ∀ (p q : Nat) (hp : p < bm.toNat + 1) (hq : q < bm.toNat + 1),
    isActiveRehashTag (ctrl[p]'(by have := mirror.1; omega)) = true →
    isActiveRehashTag (ctrl[q]'(by have := mirror.1; omega)) = true →
    (slots[p]'(by omega)).1 = (slots[q]'(by omega)).1 → p = q
  complete : ∀ (k v : BitVec 64), cliMapLookup k m = some v →
    ∃ (q : Nat) (hq : q < bm.toNat + 1),
      isActiveRehashTag (ctrl[q]'(by have := mirror.1; omega)) = true ∧ slots[q]'(by omega) = (k, v)
  full_placed : ∀ (q : Nat) (hq : q < bm.toNat + 1),
    isFullTag (ctrl[q]'(by have := mirror.1; omega)) = true →
      ctrl[q]'(by have := mirror.1; omega) = h2Tag (slots[q]'(by omega)).1 ∧
      ∃ step lane : Nat, step < numGroups bm ∧ lane < 8 ∧
        (probePos bm (slots[q]'(by omega)).1 step + lane) % (bm.toNat + 1) = q ∧
        ∀ s' < step, ∀ j < 8,
          isFullTag (ctrl[(probePos bm (slots[q]'(by omega)).1 s' + j) % (bm.toNat + 1)]'(by
            have := mirror.1
            have := @Nat.mod_lt (probePos bm (slots[q]'(by omega)).1 s' + j) (bm.toNat + 1) (by omega)
            omega)) = true

def countDeletedTags (bm : BitVec 64) (ctrl : List (BitVec 8)) : Nat :=
  (ctrl.take (bm.toNat + 1)).countP (· == tagDeleted)

theorem RehashTableInv.of_prep {bm gl items : BitVec 64}
    {ctrl : List (BitVec 8)} {slots : List (BitVec 64 × BitVec 64)} {m : Map64}
    (hinv : SwissTableInv bm gl items ctrl slots m) (hge8 : 8 ≤ bm.toNat + 1) (hdvd8 : (bm.toNat + 1) % 8 = 0) :
    let buckets := bm.toNat + 1
    RehashTableInv bm m ((ctrl.take buckets).map prepCtrlByte ++ (ctrl.take 8).map prepCtrlByte) slots := by
  intro buckets; let ctrl0 := (ctrl.take buckets).map prepCtrlByte ++ (ctrl.take 8).map prepCtrlByte
  have hlen : ctrl.length = buckets + 8 := hinv.mirror.1
  have hlen0 : ctrl0.length = buckets + 8 := by
    simp [ctrl0, Nat.min_eq_left (by omega : buckets ≤ ctrl.length), Nat.min_eq_left (by omega : 8 ≤ ctrl.length)]
  have hget0 : ∀ q (hq : q < buckets), ctrl0[q]'(by omega) = prepCtrlByte (ctrl[q]'(by omega)) := fun q hq => by
    rw [List.getElem_append_left (by simp [Nat.min_eq_left (by omega : buckets ≤ ctrl.length), hq]),
      List.getElem_map, List.getElem_take]
  have hact_eq : ∀ q (hq : q < buckets),
      isActiveRehashTag (ctrl0[q]'(by omega)) = isFullTag (ctrl[q]'(by omega)) := fun q hq => by
    rw [hget0 q hq]; simp [isActiveRehashTag, isFullTag_prepCtrlByte, prepCtrlByte_beq_deleted]
  have hmir0 : CtrlMirrorInv buckets ctrl0 := by
    refine ⟨hlen0, ?_, fun h4 => by omega, ?_⟩
    · intro b hb; rcases List.mem_append.mp hb with hb1 | hb2
      · rcases List.mem_map.mp hb1 with ⟨x, _, rfl⟩; exact prepCtrlByte_validTag x
      · rcases List.mem_map.mp hb2 with ⟨x, _, rfl⟩; exact prepCtrlByte_validTag x
    · intro _ j hj; rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)]; congr 1
      have hr : ctrl0[buckets + j]'(by omega) = ((ctrl.take 8).map prepCtrlByte)[j]'(by
          simp [Nat.min_eq_left (by omega : 8 ≤ ctrl.length), hj]) := by
        rw [List.getElem_append_right (by simp [Nat.min_eq_left (by omega : buckets ≤ ctrl.length)])]
        congr 1; simp [Nat.min_eq_left (by omega : buckets ≤ ctrl.length)]
      rw [hr, hget0 j (by omega), List.getElem_map, List.getElem_take]
  rcases hinv.exists_empty_slot with ⟨e, he_lt, he_emp⟩
  exact { validMask := hinv.validMask, wf := hinv.wf, ge8 := hge8, dvd8 := hdvd8,
          slots_len := hinv.slots_len, mirror := hmir0,
          has_empty := ⟨e, he_lt, by rw [hget0 e he_lt, he_emp]; rfl⟩,
          countActive_eq := by
            rw [countP_take_congr (ys := ctrl) (q := isFullTag) (by omega) (by omega) hact_eq]
            exact hinv.countFull_eq,
          active_lookup := fun q hq ha => by rw [hact_eq q hq] at ha; exact (hinv.full_sound q hq ha).2.1,
          active_inj := fun p q hp hq hap haq hkey => by
            rw [hact_eq p hp] at hap; rw [hact_eq q hq] at haq; exact hinv.full_inj p q hp hq hap haq hkey,
          complete := fun k v hlook => by
            rcases hinv.complete k v hlook with ⟨q, hq, hfq, hsq⟩
            exact ⟨q, hq, by rw [hact_eq q hq]; exact hfq, hsq⟩,
          full_placed := fun q hq hfq => by rw [hget0 q hq, isFullTag_prepCtrlByte] at hfq; cases hfq }

theorem RehashTableInv.place_same {bm : BitVec 64} {m : Map64}
    {ctrl : List (BitVec 8)} {slots : List (BitVec 64 × BitVec 64)}
    (h : RehashTableInv bm m ctrl slots) {i step lane_i : Nat} (hi : i < bm.toNat + 1)
    (hdel_i : ctrl[i]'(by have := h.mirror.1; omega) = tagDeleted)
    (hpfx : ∀ (q : Nat) (hq : q < i), ctrl[q]'(by have := h.mirror.1; omega) ≠ tagDeleted)
    (hstep : step < numGroups bm) (hlane : lane_i < 8)
    (hidx_i : (probePos bm (slots[i]'(by have := h.slots_len; omega)).1 step + lane_i) % (bm.toNat + 1) = i)
    (hprev_full : ∀ s' < step, ∀ j < 8,
      isFullTag (ctrl[(probePos bm (slots[i]'(by have := h.slots_len; omega)).1 s' + j) %
        (bm.toNat + 1)]'(by
        have := h.mirror.1
        have := @Nat.mod_lt (probePos bm (slots[i]'(by have := h.slots_len; omega)).1 s' + j) (bm.toNat + 1) (by omega)
        omega)) = true) :
    let ctrl' := setCtrlBytes bm ctrl i (h2Tag (slots[i]'(by have := h.slots_len; omega)).1)
    RehashTableInv bm m ctrl' slots ∧
    ∀ (q : Nat) (hq : q < i + 1),
      ctrl'[q]'(by rw [setCtrlBytes_length]; have := h.mirror.1; omega) ≠ tagDeleted := by
  intro ctrl'; let buckets := bm.toNat + 1; let k := (slots[i]'(by have := h.slots_len; omega)).1
  have hlen : ctrl.length = buckets + 8 := h.mirror.1
  have hlen' : ctrl'.length = buckets + 8 := by rw [setCtrlBytes_length]; exact hlen
  have hmir' := setCtrlBytes_mirror h.validMask h.ge8 h.mirror hi (ValidTag.of_h2Tag k)
  have hget' : ∀ q (hq : q < buckets),
      ctrl'[q]'(by omega) = if q = i then h2Tag k else ctrl[q]'(by omega) :=
    fun q hq => setCtrlBytes_getElem_lt h.validMask h.ge8 hlen hi hq (h2Tag k)
  have hact_eq : ∀ q (hq : q < buckets),
      isActiveRehashTag (ctrl'[q]'(by omega)) = isActiveRehashTag (ctrl[q]'(by omega)) := fun q hq => by
    rw [hget' q hq]; by_cases hqi : q = i
    · subst hqi; simp [isActiveRehashTag, hdel_i]
    · simp [hqi]
  have hfull_mono : ∀ r (hr : r < buckets),
      isFullTag (ctrl[r]'(by omega)) = true → isFullTag (ctrl'[r]'(by omega)) = true := fun r hr hfr => by
    rw [hget' r hr]; by_cases hri : r = i
    · subst hri; simp [hdel_i] at hfr
    · simp [hri, hfr]
  rcases h.has_empty with ⟨e, he_lt, he_emp⟩
  refine ⟨{ validMask := h.validMask, wf := h.wf, ge8 := h.ge8, dvd8 := h.dvd8,
            slots_len := h.slots_len, mirror := hmir',
            has_empty := ⟨e, he_lt, by
              rw [hget' e he_lt]
              have hei : e ≠ i := fun h0 => by subst h0; rw [hdel_i] at he_emp; cases he_emp
              simp [hei, he_emp]⟩,
            countActive_eq := by
              rw [countP_take_congr (ys := ctrl) (q := isActiveRehashTag) (by omega) (by omega) hact_eq]
              exact h.countActive_eq,
            active_lookup := fun q hq ha => by rw [hact_eq q hq] at ha; exact h.active_lookup q hq ha,
            active_inj := fun p q hp hq hap haq hkey => by
              rw [hact_eq p hp] at hap; rw [hact_eq q hq] at haq; exact h.active_inj p q hp hq hap haq hkey,
            complete := fun k0 v0 hlook => by
              rcases h.complete k0 v0 hlook with ⟨q, hq, haq, hsq⟩
              exact ⟨q, hq, by rw [hact_eq q hq]; exact haq, hsq⟩,
            full_placed := fun q hq hfq => by
              rw [hget' q hq] at hfq ⊢; by_cases hqi : q = i
              · subst hqi; simp only [↓reduceIte]
                exact ⟨rfl, step, lane_i, hstep, hlane, hidx_i, fun s' hs' j hj =>
                  hfull_mono _ (Nat.mod_lt _ (by omega)) (hprev_full s' hs' j hj)⟩
              · simp only [hqi, ↓reduceIte] at hfq ⊢
                rcases h.full_placed q hq hfq with ⟨htag_q, s_q, l_q, hs_q, hl_q, hidx_q, hall_q⟩
                exact ⟨htag_q, s_q, l_q, hs_q, hl_q, hidx_q, fun s' hs' j hj =>
                  hfull_mono _ (Nat.mod_lt _ (by omega)) (hall_q s' hs' j hj)⟩ }, ?_⟩
  intro q hq; rw [hget' q (by omega)]; by_cases hqi : q = i
  · subst hqi; simp only [↓reduceIte]; intro heq
    have hlt := h2Tag_lt_0x80 k; rw [heq] at hlt; simp [tagDeleted] at hlt
  · simp only [hqi, ↓reduceIte]; exact hpfx q (by omega)

theorem RehashTableInv.move_to_empty {bm : BitVec 64} {m : Map64}
    {ctrl : List (BitVec 8)} {slots : List (BitVec 64 × BitVec 64)} (h : RehashTableInv bm m ctrl slots)
    {i new_i step lane : Nat} (hi : i < bm.toNat + 1) (hnew : new_i < bm.toNat + 1) (hne : new_i ≠ i)
    (hdel_i : ctrl[i]'(by have := h.mirror.1; omega) = tagDeleted)
    (hemp_new : ctrl[new_i]'(by have := h.mirror.1; omega) = tagEmpty)
    (hpfx : ∀ (q : Nat) (hq : q < i), ctrl[q]'(by have := h.mirror.1; omega) ≠ tagDeleted)
    (hstep : step < numGroups bm) (hlane : lane < 8)
    (hidx_new : (probePos bm (slots[i]'(by have := h.slots_len; omega)).1 step + lane) % (bm.toNat + 1) = new_i)
    (hprev_full : ∀ s' < step, ∀ j < 8,
      isFullTag (ctrl[(probePos bm (slots[i]'(by have := h.slots_len; omega)).1 s' + j) %
        (bm.toNat + 1)]'(by
        have := h.mirror.1
        have := @Nat.mod_lt (probePos bm (slots[i]'(by have := h.slots_len; omega)).1 s' + j) (bm.toNat + 1) (by omega)
        omega)) = true) :
    let kv := slots[i]'(by have := h.slots_len; omega)
    let ctrl1 := setCtrlBytes bm ctrl new_i (h2Tag kv.1)
    let ctrl2 := setCtrlBytes bm ctrl1 i tagEmpty
    let slots' := slots.set new_i kv
    RehashTableInv bm m ctrl2 slots' ∧
    ∀ (q : Nat) (hq : q < i + 1),
      ctrl2[q]'(by rw [setCtrlBytes_length, setCtrlBytes_length]; have := h.mirror.1; omega) ≠ tagDeleted := by
  intro kv ctrl1 ctrl2 slots'; let buckets := bm.toNat + 1
  have hlen : ctrl.length = buckets + 8 := h.mirror.1
  have hlen1 : ctrl1.length = buckets + 8 := by rw [setCtrlBytes_length]; exact hlen
  have hlen2 : ctrl2.length = buckets + 8 := by rw [setCtrlBytes_length]; exact hlen1
  have hmir1 := setCtrlBytes_mirror h.validMask h.ge8 h.mirror hnew (ValidTag.of_h2Tag kv.1)
  have hmir2 := setCtrlBytes_mirror h.validMask h.ge8 hmir1 hi ValidTag.empty
  have hget1 : ∀ q (hq : q < buckets),
      ctrl1[q]'(by omega) = if q = new_i then h2Tag kv.1 else ctrl[q]'(by omega) :=
    fun q hq => setCtrlBytes_getElem_lt h.validMask h.ge8 hlen hnew hq (h2Tag kv.1)
  have hget2 : ∀ q (hq : q < buckets), ctrl2[q]'(by omega) =
      if q = i then tagEmpty else if q = new_i then h2Tag kv.1 else ctrl[q]'(by omega) :=
    fun q hq => by rw [setCtrlBytes_getElem_lt h.validMask h.ge8 hlen1 hi hq tagEmpty, hget1 q hq]
  have hfull_mono : ∀ r (hr : r < buckets),
      isFullTag (ctrl[r]'(by omega)) = true → isFullTag (ctrl2[r]'(by omega)) = true := fun r hr hfr => by
    rw [hget2 r hr]
    have hri : r ≠ i := fun h0 => by subst h0; simp [hdel_i] at hfr
    have hrn : r ≠ new_i := fun h0 => by subst h0; simp [hemp_new] at hfr
    simp [hri, hrn, hfr]
  have hcnt1 : (ctrl.take buckets).countP isActiveRehashTag + 1 =
      (ctrl1.take buckets).countP isActiveRehashTag := by
    apply countP_take_flip_down (xs := ctrl1) (ys := ctrl) (idx := new_i) (by omega) (by omega) hnew
    · rw [hget1 new_i hnew]; simp [isActiveRehashTag]
    · simp [isActiveRehashTag, hemp_new]; decide
    · intro q hq hqn; rw [hget1 q hq]; simp [hqn]
  have hcnt2 : (ctrl2.take buckets).countP isActiveRehashTag + 1 =
      (ctrl1.take buckets).countP isActiveRehashTag := by
    apply countP_take_flip_down (xs := ctrl1) (ys := ctrl2) (idx := i) (by omega) (by omega) hi
    · rw [hget1 i hi]; simp [Ne.symm hne, isActiveRehashTag, hdel_i]
    · rw [hget2 i hi]; simp [isActiveRehashTag]; decide
    · intro q hq hqi; rw [setCtrlBytes_getElem_lt h.validMask h.ge8 hlen1 hi hq tagEmpty]; simp [hqi]
  have hact_i : isActiveRehashTag (ctrl[i]'(by omega)) = true := by simp [isActiveRehashTag, hdel_i]
  have hact_new_false : isActiveRehashTag (ctrl[new_i]'(by omega)) = false := by
    simp [isActiveRehashTag, hemp_new]; decide
  refine ⟨{ validMask := h.validMask, wf := h.wf, ge8 := h.ge8, dvd8 := h.dvd8,
            slots_len := by simp [slots', h.slots_len], mirror := hmir2,
            has_empty := ⟨i, hi, by rw [hget2 i hi]; simp⟩,
            countActive_eq := by dsimp only [buckets] at hcnt1 hcnt2; have := h.countActive_eq; omega,
            active_lookup := fun q hq ha => by
              rw [hget2 q hq] at ha; by_cases hqi : q = i
              · subst hqi; simp [isActiveRehashTag, show (tagEmpty == tagDeleted) = false by decide] at ha
              · simp only [hqi, ↓reduceIte] at ha; by_cases hqn : q = new_i
                · subst hqn; simp only [slots', List.getElem_set_self]; exact h.active_lookup i hi hact_i
                · simp only [hqn, ↓reduceIte] at ha; simp only [slots', List.getElem_set_ne (Ne.symm hqn)]
                  exact h.active_lookup q hq ha,
            active_inj := fun p q hp hq hap haq hkey => by
              rw [hget2 p hp] at hap; rw [hget2 q hq] at haq
              have hpi : p ≠ i := fun h0 => by
                subst h0; simp [isActiveRehashTag, show (tagEmpty == tagDeleted) = false by decide] at hap
              have hqi : q ≠ i := fun h0 => by
                subst h0; simp [isActiveRehashTag, show (tagEmpty == tagDeleted) = false by decide] at haq
              simp only [hpi, hqi, ↓reduceIte] at hap haq
              by_cases hpn : p = new_i <;> by_cases hqn : q = new_i
              · omega
              · subst hpn; simp only [slots', List.getElem_set_self, List.getElem_set_ne (Ne.symm hqn)] at hkey
                simp only [hqn, ↓reduceIte] at haq
                exact False.elim (hqi (h.active_inj i q hi hq hact_i haq hkey).symm)
              · subst hqn; simp only [slots', List.getElem_set_self, List.getElem_set_ne (Ne.symm hpn)] at hkey
                simp only [hpn, ↓reduceIte] at hap
                exact False.elim (hpi (h.active_inj p i hp hi hap hact_i hkey))
              · simp only [hpn, hqn, ↓reduceIte] at hap haq
                simp only [slots', List.getElem_set_ne (Ne.symm hpn), List.getElem_set_ne (Ne.symm hqn)] at hkey
                exact h.active_inj p q hp hq hap haq hkey,
            complete := fun k0 v0 hlook => by
              rcases h.complete k0 v0 hlook with ⟨q, hq, haq, hsq⟩; by_cases hqi : q = i
              · subst hqi; exact ⟨new_i, hnew, by rw [hget2 new_i hnew]; simp [hne, isActiveRehashTag],
                  by simp [slots', kv, hsq]⟩
              · have hqn : q ≠ new_i := fun h0 => by subst h0; rw [hact_new_false] at haq; cases haq
                exact ⟨q, hq, by rw [hget2 q hq]; simp [hqi, hqn, haq],
                  by simp [slots', List.getElem_set_ne (Ne.symm hqn), hsq]⟩,
            full_placed := fun q hq hfq => by
              rw [hget2 q hq] at hfq ⊢
              have hqi : q ≠ i := fun h0 => by subst h0; simp at hfq
              simp only [hqi, ↓reduceIte] at hfq ⊢; by_cases hqn : q = new_i
              · subst hqn; simp only [↓reduceIte, slots', List.getElem_set_self]
                exact ⟨trivial, step, lane, hstep, hlane, hidx_new, fun s' hs' j hj =>
                  hfull_mono _ (Nat.mod_lt _ (by omega)) (hprev_full s' hs' j hj)⟩
              · simp only [hqn, ↓reduceIte, slots', List.getElem_set_ne (Ne.symm hqn)] at hfq ⊢
                rcases h.full_placed q hq hfq with ⟨htag_q, s_q, l_q, hs_q, hl_q, hidx_q, hall_q⟩
                exact ⟨htag_q, s_q, l_q, hs_q, hl_q, hidx_q, fun s' hs' j hj =>
                  hfull_mono _ (Nat.mod_lt _ (by omega)) (hall_q s' hs' j hj)⟩ }, ?_⟩
  intro q hq; rw [hget2 q (by omega)]; by_cases hqi : q = i
  · subst hqi; simp; decide
  · simp only [hqi, ↓reduceIte]; by_cases hqn : q = new_i
    · subst hqn; simp only [↓reduceIte]; intro heq
      have hlt := h2Tag_lt_0x80 kv.1; rw [heq] at hlt; simp [tagDeleted] at hlt
    · simp only [hqn, ↓reduceIte]; exact hpfx q (by omega)

theorem RehashTableInv.swap_deleted {bm : BitVec 64} {m : Map64}
    {ctrl : List (BitVec 8)} {slots : List (BitVec 64 × BitVec 64)} (h : RehashTableInv bm m ctrl slots)
    {i new_i step lane : Nat} (hi : i < bm.toNat + 1) (hnew : new_i < bm.toNat + 1) (hne : new_i ≠ i)
    (hdel_i : ctrl[i]'(by have := h.mirror.1; omega) = tagDeleted)
    (hdel_new : ctrl[new_i]'(by have := h.mirror.1; omega) = tagDeleted)
    (hpfx : ∀ (q : Nat) (hq : q < i), ctrl[q]'(by have := h.mirror.1; omega) ≠ tagDeleted)
    (hstep : step < numGroups bm) (hlane : lane < 8)
    (hidx_new : (probePos bm (slots[i]'(by have := h.slots_len; omega)).1 step + lane) % (bm.toNat + 1) = new_i)
    (hprev_full : ∀ s' < step, ∀ j < 8,
      isFullTag (ctrl[(probePos bm (slots[i]'(by have := h.slots_len; omega)).1 s' + j) %
        (bm.toNat + 1)]'(by
        have := h.mirror.1
        have := @Nat.mod_lt (probePos bm (slots[i]'(by have := h.slots_len; omega)).1 s' + j) (bm.toNat + 1) (by omega)
        omega)) = true) :
    let kv_i := slots[i]'(by have := h.slots_len; omega)
    let kv_new := slots[new_i]'(by have := h.slots_len; omega)
    let ctrl1 := setCtrlBytes bm ctrl new_i (h2Tag kv_i.1)
    let slots' := (slots.set i kv_new).set new_i kv_i
    RehashTableInv bm m ctrl1 slots' ∧
    ctrl1[i]'(by rw [setCtrlBytes_length]; have := h.mirror.1; omega) = tagDeleted ∧
    (∀ (q : Nat) (hq : q < i), ctrl1[q]'(by rw [setCtrlBytes_length]; have := h.mirror.1; omega) ≠ tagDeleted) ∧
    countDeletedTags bm ctrl1 < countDeletedTags bm ctrl := by
  intro kv_i kv_new ctrl1 slots'; let buckets := bm.toNat + 1
  have hlen : ctrl.length = buckets + 8 := h.mirror.1
  have hlen1 : ctrl1.length = buckets + 8 := by rw [setCtrlBytes_length]; exact hlen
  have hmir1 := setCtrlBytes_mirror h.validMask h.ge8 h.mirror hnew (ValidTag.of_h2Tag kv_i.1)
  have hget1 : ∀ q (hq : q < buckets),
      ctrl1[q]'(by omega) = if q = new_i then h2Tag kv_i.1 else ctrl[q]'(by omega) :=
    fun q hq => setCtrlBytes_getElem_lt h.validMask h.ge8 hlen hnew hq (h2Tag kv_i.1)
  have hact_eq : ∀ q (hq : q < buckets),
      isActiveRehashTag (ctrl1[q]'(by omega)) = isActiveRehashTag (ctrl[q]'(by omega)) := by
    intro q hq; rw [hget1 q hq]; by_cases hqn : q = new_i
    · subst hqn; simp [isActiveRehashTag, hdel_new]
    · simp [hqn]
  have hfull_mono : ∀ r (hr : r < buckets),
      isFullTag (ctrl[r]'(by omega)) = true → isFullTag (ctrl1[r]'(by omega)) = true := by
    intro r hr hfr; rw [hget1 r hr]
    have hrn : r ≠ new_i := fun h0 => by subst h0; simp [hdel_new] at hfr
    simp [hrn, hfr]
  have hslot' : ∀ q (hq : q < buckets), slots'[q]'(by simp [slots', h.slots_len]; omega) =
      if q = new_i then kv_i else if q = i then kv_new else slots[q]'(by have := h.slots_len; omega) := by
    intro q hq; dsimp only [slots']; rw [List.getElem_set, List.getElem_set]
    by_cases hqn : new_i = q
    · subst hqn; simp
    · simp only [hqn, Ne.symm hqn, ↓reduceIte]; by_cases hqi : i = q
      · subst hqi; simp
      · simp [hqi, Ne.symm hqi]
  have hact_i : isActiveRehashTag (ctrl[i]'(by omega)) = true := by simp [isActiveRehashTag, hdel_i]
  have hact_new : isActiveRehashTag (ctrl[new_i]'(by omega)) = true := by simp [isActiveRehashTag, hdel_new]
  have hdec : countDeletedTags bm ctrl1 + 1 = countDeletedTags bm ctrl := by
    unfold countDeletedTags
    apply countP_take_flip_down (xs := ctrl) (ys := ctrl1) (idx := new_i) (by omega) (by omega) hnew
    · simp [hdel_new]
    · rw [hget1 new_i hnew]; simp only [↓reduceIte, beq_eq_false_iff_ne]; intro heq
      have hlt := h2Tag_lt_0x80 kv_i.1; rw [heq] at hlt; simp [tagDeleted] at hlt
    · intro q hq hqn; rw [hget1 q hq]; simp [hqn]
  rcases h.has_empty with ⟨e, he_lt, he_emp⟩; refine ⟨?_, ?_, ?_, by omega⟩
  · refine
      { validMask := h.validMask, wf := h.wf, ge8 := h.ge8, dvd8 := h.dvd8,
        slots_len := by simp [slots', h.slots_len], mirror := hmir1,
        has_empty := ⟨e, he_lt, by
          rw [hget1 e he_lt]
          have hen : e ≠ new_i := fun h0 => by subst h0; rw [hdel_new] at he_emp; cases he_emp
          simp [hen, he_emp]⟩,
        countActive_eq := by
          rw [countP_take_congr (ys := ctrl) (q := isActiveRehashTag) (by omega) (by omega) hact_eq]
          exact h.countActive_eq,
        active_lookup := fun q hq ha => by
          rw [hslot' q hq]; by_cases hqn : q = new_i
          · subst hqn; simp only [↓reduceIte]; exact h.active_lookup i hi hact_i
          · simp only [hqn, ↓reduceIte]; by_cases hqi : q = i
            · subst hqi; simp only [↓reduceIte]; exact h.active_lookup new_i hnew hact_new
            · simp only [hqi, ↓reduceIte]; rw [hact_eq q hq] at ha; exact h.active_lookup q hq ha,
        active_inj := fun p q hp hq hap haq hkey => by
          rw [hact_eq p hp] at hap; rw [hact_eq q hq] at haq; rw [hslot' p hp, hslot' q hq] at hkey
          let permIdx := fun x => if x = new_i then i else if x = i then new_i else x
          have hperm_lt : ∀ x, x < buckets → permIdx x < buckets := fun x hx => by
            dsimp only [permIdx]; by_cases h1 : x = new_i <;> by_cases h2 : x = i <;> simp_all <;> omega
          have hperm_act : ∀ x (hx : x < buckets), isActiveRehashTag (ctrl[x]'(by omega)) = true →
              isActiveRehashTag (ctrl[permIdx x]'(by have := hperm_lt x hx; omega)) = true := fun x _ hax => by
            dsimp only [permIdx]; by_cases h1 : x = new_i <;> by_cases h2 : x = i <;> simp_all
          have hperm_slot : ∀ x (hx : x < buckets),
              (if x = new_i then kv_i else if x = i then kv_new else slots[x]'(by have := h.slots_len; omega)) =
              slots[permIdx x]'(by have := hperm_lt x hx; have := h.slots_len; omega) := fun x _ => by
            dsimp only [permIdx, kv_i, kv_new]; by_cases h1 : x = new_i <;> by_cases h2 : x = i <;> simp_all
          rw [hperm_slot p hp, hperm_slot q hq] at hkey
          have hinj := h.active_inj (permIdx p) (permIdx q) (hperm_lt p hp) (hperm_lt q hq)
            (hperm_act p hp hap) (hperm_act q hq haq) hkey
          dsimp only [permIdx] at hinj
          by_cases hpn : p = new_i <;> by_cases hpi : p = i <;>
            by_cases hqn : q = new_i <;> by_cases hqi : q = i <;> simp_all,
        complete := fun k0 v0 hlook => by
          rcases h.complete k0 v0 hlook with ⟨q, hq, haq, hsq⟩; by_cases hqi : q = i
          · subst hqi; exact ⟨new_i, hnew, (hact_eq new_i hnew).symm ▸ hact_new,
              by rw [hslot' new_i hnew]; simp [kv_i, hsq]⟩
          · by_cases hqn : q = new_i
            · subst hqn; exact ⟨i, hi, (hact_eq i hi).symm ▸ hact_i,
                by rw [hslot' i hi]; simp [Ne.symm hne, kv_new, hsq]⟩
            · exact ⟨q, hq, (hact_eq q hq).symm ▸ haq, by rw [hslot' q hq]; simp [hqn, hqi, hsq]⟩,
        full_placed := fun q hq hfq => by
          rw [hget1 q hq] at hfq ⊢; simp only [hslot' q hq]; by_cases hqn : q = new_i
          · subst hqn; simp only [↓reduceIte]
            exact ⟨trivial, step, lane, hstep, hlane, hidx_new, fun s' hs' j hj =>
              hfull_mono _ (Nat.mod_lt _ (by omega)) (hprev_full s' hs' j hj)⟩
          · simp only [hqn, ↓reduceIte] at hfq ⊢
            have hqi : q ≠ i := fun h0 => by subst h0; simp [hdel_i] at hfq
            simp only [hqi, ↓reduceIte]
            rcases h.full_placed q hq hfq with ⟨htag_q, s_q, l_q, hs_q, hl_q, hidx_q, hall_q⟩
            exact ⟨htag_q, s_q, l_q, hs_q, hl_q, hidx_q, fun s' hs' j hj =>
              hfull_mono _ (Nat.mod_lt _ (by omega)) (hall_q s' hs' j hj)⟩ }
  · rw [hget1 i hi]; simp [Ne.symm hne, hdel_i]
  · intro q hq; rw [hget1 q (by omega)]; by_cases hqn : q = new_i
    · subst hqn; simp only [↓reduceIte]; intro heq
      have hlt := h2Tag_lt_0x80 kv_i.1; rw [heq] at hlt; simp [tagDeleted] at hlt
    · simp only [hqn, ↓reduceIte]; exact hpfx q hq

theorem RehashTableInv.to_swissTableInv {bm items : BitVec 64} {m : Map64}
    {ctrl : List (BitVec 8)} {slots : List (BitVec 64 × BitVec 64)}
    (h : RehashTableInv bm m ctrl slots) (hitems : items = BitVec.ofNat 64 m.length)
    (hno_del : ∀ (q : Nat) (hq : q < bm.toNat + 1), ctrl[q]'(by have := h.mirror.1; omega) ≠ tagDeleted)
    (hle_half : m.length + 1 ≤ bucketMaskToCapacity bm / 2) :
    let gl := bucketMaskToCapacityBV bm - items
    SwissTableInv bm gl items ctrl slots m ∧ 0 < gl.toNat := by
  intro gl; let buckets := bm.toNat + 1; have hlen : ctrl.length = buckets + 8 := h.mirror.1
  rcases h.validMask.buckets_bounds_dvd with ⟨_, hb58, _⟩
  have h58 : 2 ^ 58 < 2 ^ 64 := by decide
  have hcap_lt : bucketMaskToCapacity bm < buckets := (h.validMask.capacity_bounds).2
  have hmlen_lt : m.length < bucketMaskToCapacity bm := by omega
  have hgl_nat : gl.toNat = bucketMaskToCapacity bm - m.length := by
    dsimp only [gl]; rw [hitems]
    have hcap_bv : bucketMaskToCapacityBV bm = BitVec.ofNat 64 (bucketMaskToCapacity bm) := by
      unfold bucketMaskToCapacity; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rw [hcap_bv, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : bucketMaskToCapacity bm < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : m.length < 2 ^ 64)]
    rw [show 2 ^ 64 - m.length + bucketMaskToCapacity bm = 2 ^ 64 + (bucketMaskToCapacity bm - m.length) by omega,
      Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  have hact_full : ∀ q (hq : q < buckets),
      isActiveRehashTag (ctrl[q]'(by omega)) = isFullTag (ctrl[q]'(by omega)) := fun q hq => by
    simp [isActiveRehashTag, beq_eq_false_iff_ne.mpr (hno_del q hq)]
  have hdel_zero : (ctrl.take buckets).countP (· == tagDeleted) = 0 := by
    rw [List.countP_eq_zero]; intro b hb; rcases List.mem_iff_getElem.mp hb with ⟨q, hq_t, rfl⟩
    have hq : q < buckets := by simp [Nat.min_eq_left (by omega : buckets ≤ ctrl.length)] at hq_t; exact hq_t
    simp [List.getElem_take, beq_eq_false_iff_ne.mpr (hno_del q hq)]
  refine ⟨{ validMask := h.validMask, wf := h.wf, slots_len := h.slots_len, mirror := h.mirror,
            items_eq := hitems, growth_le := by omega, conservation := by rw [hdel_zero, hgl_nat]; omega,
            countFull_eq := by
              rw [← countP_take_congr (xs := ctrl) (p := isActiveRehashTag) (by omega) (by omega) hact_full]
              exact h.countActive_eq,
            full_sound := fun i hi hfi => (by
              have hai : isActiveRehashTag (ctrl[i]'(by omega)) = true := (hact_full i hi).symm ▸ hfi
              rcases h.full_placed i hi hfi with ⟨htag_i, step, lane, hstep, hlane, hidx, hall⟩
              refine ⟨htag_i, h.active_lookup i hi hai, step, lane, hstep, hlane, ?_, hidx, ?_⟩
              · have hpos_lt := probePos_lt_buckets h.validMask (slots[i]'(by have := h.slots_len; omega)).1 step
                rw [ctrlGroupAt_getElem? (by omega) hlane,
                  CtrlMirrorInv.lane_eq_mod_of_ge8 h.mirror h.ge8 hpos_lt hlane]
                simp [hidx, htag_i]
              · intro s' hs' hemp
                have hpos_lt := probePos_lt_buckets h.validMask (slots[i]'(by have := h.slots_len; omega)).1 s'
                rw [mem_ctrlGroupAt_iff (by omega)] at hemp; rcases hemp with ⟨j, hj, hj_emp⟩
                rw [CtrlMirrorInv.lane_eq_mod_of_ge8 h.mirror h.ge8 hpos_lt hj] at hj_emp
                have hfj := hall s' hs' j hj; rw [hj_emp, isFullTag_tagEmpty] at hfj; cases hfj),
            full_inj := fun p q hp hq hfp hfq hkey =>
              h.active_inj p q hp hq ((hact_full p hp).symm ▸ hfp) ((hact_full q hq).symm ▸ hfq) hkey,
            complete := fun k0 v0 hlook => by
              rcases h.complete k0 v0 hlook with ⟨q, hq, haq, hsq⟩
              exact ⟨q, hq, (hact_full q hq) ▸ haq, hsq⟩ }, by omega⟩

/-! ## Store-Permission Steps and Control-Byte Lemmas -/

def MutFrame (s1 st : State) : Prop :=
  st.sp = s1.sp ∧ st.spAligned = true ∧ st.readReg64 (.gpr 28#5) = s1.readReg64 (.gpr 28#5) ∧
  calleeSavedVRegs st = calleeSavedVRegs s1 ∧ StdStatePreserved s1 st

theorem MutFrame.refl {s1 : State} (hsp : s1.spAligned = true) : MutFrame s1 s1 :=
  ⟨rfl, hsp, rfl, rfl, StdStatePreserved.rfl s1⟩

theorem mutFrame_setMem (s1 st : State) (m' : Memory) (hp : m'.perm = st.mem.perm) :
    MutFrame s1 (st.setMem m') ↔ MutFrame s1 st := by
  constructor <;> rintro ⟨h1, h2, h3, h4, hfs, htr, htp, hsig, hbrk, hbrks, hpm, hperm⟩
  · exact ⟨h1, h2, h3, h4, hfs, htr, htp, hsig, hbrk, hbrks, hpm, fun a => (congrFun hp a).symm.trans (hperm a)⟩
  · exact ⟨h1, h2, h3, h4, hfs, htr, htp, hsig, hbrk, hbrks, hpm, fun a => (congrFun hp a).trans (hperm a)⟩

theorem MutFrame.of_call {s1 sm sf : State} (hm : MutFrame s1 sm) (hsp : sf.sp = sm.sp)
    (hcs : CalleeSavedPreserved sm sf) (hstd : StdStatePreserved sm sf) : MutFrame s1 sf :=
  ⟨hsp.trans hm.1, by rw [State.spAligned, hsp]; exact hm.2.1,
   hcs.readReg64_x28.trans hm.2.2.1, hcs.vregs.trans hm.2.2.2.1, StdStatePreserved.trans hm.2.2.2.2 hstd⟩

theorem pointsToBytes_focus8_getElem (base : BitVec 64) (bs : List (BitVec 8)) {off : Nat} (h : off < bs.length) :
    (base ↦ₛ bs) = ((base + BitVec.ofNat 64 off) ↦₈ bs[off]) ∗
      ((base ↦ₛ bs.take off) ∗ ((base + BitVec.ofNat 64 (off + 1)) ↦ₛ bs.drop (off + 1))) := by
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h] using pointsToBytes_focus8 base bs off h

theorem pointsToBytes_update8 (base : BitVec 64) (bs : List (BitVec 8)) {off : Nat} (v : BitVec 8) (h : off < bs.length) :
    (((base + BitVec.ofNat 64 off) ↦₈ v) ∗
      ((base ↦ₛ bs.take off) ∗ ((base + BitVec.ofNat 64 (off + 1)) ↦ₛ bs.drop (off + 1)))) = (base ↦ₛ bs.set off v) := by
  rw [← pointsToBytes_merge_at base bs off v h]; ac_rfl

theorem setCtrlMirror_addr_eq (ctrlPtr bm : BitVec 64) (hbm : ValidBucketMask bm) {idx : Nat} :
    (ctrlPtr + ((BitVec.ofNat 64 idx - 8#64) &&& bm)) + 8#64 = ctrlPtr + BitVec.ofNat 64 (setCtrlMirrorIdx bm idx) := by
  have hmax := hbm.buckets_bounds_dvd.2.1
  have hlt : ((BitVec.ofNat 64 idx - 8#64) &&& bm).toNat < bm.toNat + 1 := by
    rw [hbm.and_toNat_eq_mod]; exact Nat.mod_lt _ (by omega)
  have h64 : 2 ^ 58 + 8 < 2 ^ 64 := by decide
  rw [BitVec.add_assoc]; congr 1; unfold setCtrlMirrorIdx; apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat,
    show (8 : Nat) % 2 ^ 64 = 8 by decide, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem step_str8_perm {prog : Program} {target_pc pc ea : BitVec 64} {val : BitVec 8}
    {s : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {rt : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)}
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hfetch : prog.fetch pc = some (.str .B8 rt addr))
    (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, wb))
    (hval : (s.readReg64 rt).truncate 8 = val) (hstore : SepStore8 ea val P P')
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm →
      SepWP prog target_pc (((applyWriteback s wb).setPC (pc + 4#64)).setMem m') P' post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm; let m' := s.mem.write8 ea val
  have hm' := hstore.store hm; have hcan := hstore.writable hm
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.str .B8 rt addr) s = ((applyWriteback s wb).setPC (pc + 4#64)).setMem m' := by
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStr, Memory.writeSized, applyWriteback,
      State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr, hval, hcan, MemWidth.bytes, hpc, m']
  rw [hstep]; exact SepWP.to_reaches_pc (hnext m' (Memory.perm_write8 s.mem ea val)) hm'
theorem step_str64_perm {prog : Program} {target_pc pc ea val : BitVec 64}
    {s : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {rt : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)}
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hfetch : prog.fetch pc = some (.str .X64 rt addr))
    (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, wb))
    (hval : s.readReg64 rt = val) (hstore : SepStore64 ea val P P')
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm →
      SepWP prog target_pc (((applyWriteback s wb).setPC (pc + 4#64)).setMem m') P' post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm; let m' := s.mem.write64 ea val
  have hm' := hstore.store hm; have hcan := hstore.writable hm
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.str .X64 rt addr) s = ((applyWriteback s wb).setPC (pc + 4#64)).setMem m' := by
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStr, Memory.writeSized, applyWriteback,
      State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr, hval, hcan, MemWidth.bytes, hpc, m']
  rw [hstep]; exact SepWP.to_reaches_pc (hnext m' (Memory.perm_write64 s.mem ea val)) hm'
theorem step_strSimd64_perm {prog : Program} {target_pc pc ea v : BitVec 64}
    {s : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {vt : BitVec 5} {addr : AddrMode} {wb : Option (Reg × BitVec 64)}
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hfetch : prog.fetch pc = some (.strSimd .D64 vt addr))
    (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, wb))
    (hv : (s.readVReg128 vt).extractLsb' 0 64 = v) (hstore : SepStore64 ea v P P')
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm →
      SepWP prog target_pc (((applyWriteback s wb).setPC (pc + 4#64)).setMem m') P' post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm; let m' := s.mem.write64 ea v
  have hm' := hstore.store hm; have hcan := hstore.writable hm
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.strSimd .D64 vt addr) s = ((applyWriteback s wb).setPC (pc + 4#64)).setMem m' := by
    cases wb <;> simp [Program.evalInst, execInstWithSvc, Memory.writeSimdSized, applyWriteback,
      State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr, hcan, SimdMemSize.bytes, hpc, m', ← hv]
  rw [hstep]; exact SepWP.to_reaches_pc (hnext m' (Memory.perm_write64 s.mem ea v)) hm'
theorem step_strSimd128_perm {prog : Program} {target_pc pc ea ea2 v1 v2 : BitVec 64}
    {s : State} {P P1 P2 : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {vt : BitVec 5} {addr : AddrMode} {wb : Option (Reg × BitVec 64)}
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hfetch : prog.fetch pc = some (.strSimd .Q128 vt addr))
    (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, wb)) (hea2 : ea + 8#64 = ea2)
    (hv1 : (s.readVReg128 vt).extractLsb' 0 64 = v1) (hv2 : (s.readVReg128 vt).extractLsb' 64 64 = v2)
    (hstore1 : SepStore64 ea v1 P P1) (hstore2 : SepStore64 ea2 v2 P1 P2)
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm →
      SepWP prog target_pc (((applyWriteback s wb).setPC (pc + 4#64)).setMem m') P2 post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm; let m1 := s.mem.write64 ea v1; let m2 := m1.write64 ea2 v2
  have hm1 := hstore1.store hm; have hm2 := hstore2.store hm1
  have hcan1 := hstore1.writable hm; have hcan2 := hstore2.writable hm1
  rw [Memory.canWrite_congr (Memory.perm_write64 _ _ _)] at hcan2
  have hcan16 := Memory.canWrite_16_of_8_8 hcan1 (hea2.symm ▸ hcan2)
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.strSimd .Q128 vt addr) s = ((applyWriteback s wb).setPC (pc + 4#64)).setMem m2 := by
    cases wb <;> simp [Program.evalInst, execInstWithSvc, Memory.writeSimdSized, Memory.write128, applyWriteback,
      State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr, hea2, hv1, hv2, hcan16, SimdMemSize.bytes, hpc, m1, m2]
  rw [hstep]; exact SepWP.to_reaches_pc (hnext m2 ((Memory.perm_write64 m1 ea2 v2).trans (Memory.perm_write64 s.mem ea v1))) hm2

def prepPrefix (ctrl : List (BitVec 8)) (k : Nat) : List (BitVec 8) := (ctrl.take k).map prepCtrlByte ++ ctrl.drop k
theorem prepPrefix_zero (ctrl : List (BitVec 8)) : prepPrefix ctrl 0 = ctrl := by simp [prepPrefix]
theorem prepPrefix_length (ctrl : List (BitVec 8)) {k : Nat} (hk : k ≤ ctrl.length) :
    (prepPrefix ctrl k).length = ctrl.length := by simp [prepPrefix, Nat.min_eq_left hk]; omega
private theorem getElem_unpackLE8 (w : BitVec 64) (j : Nat) (hj : j < 8) :
    (ByteSlice.unpackLE 8 w)[j]'(by simp [ByteSlice.unpackLE_length, hj]) = getLane8 w j := by
  simp [ByteSlice.unpackLE, getLane8]
private theorem unpackLE8_ctrlGroupWord {bs : List (BitVec 8)} {pos : Nat} (hpos : pos + 8 ≤ bs.length) :
    ByteSlice.unpackLE 8 (ctrlGroupWord bs pos) = (bs.drop pos).take 8 := by
  apply List.ext_getElem (by simp [ByteSlice.unpackLE_length, Nat.min_eq_left (by omega : 8 ≤ bs.length - pos)])
  intro j hj1 _; simp only [ByteSlice.unpackLE_length] at hj1
  rw [getElem_unpackLE8 _ j hj1, getLane8_ctrlGroupWord_eq_getElem hpos hj1, List.getElem_take, List.getElem_drop]
theorem prepPrefix_getElem (ctrl : List (BitVec 8)) {k i : Nat} (hk : k ≤ ctrl.length) (hi : i < ctrl.length) :
    (prepPrefix ctrl k)[i]'(by rw [prepPrefix_length ctrl hk]; exact hi) =
      if i < k then prepCtrlByte (ctrl[i]'hi) else ctrl[i]'hi := by
  simp only [prepPrefix]; by_cases hlt : i < k
  · rw [List.getElem_append_left (by simp [Nat.min_eq_left hk, hlt])]; simp [hlt, List.getElem_take]
  · rw [List.getElem_append_right (by simp [Nat.min_eq_left hk]; omega)]
    simp [hlt, Nat.min_eq_left hk, List.getElem_drop]; congr 1; omega

private theorem prepPrefix_write64_step (ctrl : List (BitVec 8)) {g : Nat} (hg : 8 * (g + 1) ≤ ctrl.length) :
    let cur := prepPrefix ctrl (8 * g)
    let raw64 := ctrlGroupWord cur (8 * g)
    ByteSlice.write64 cur (8 * g) (byteMaskOfBits (specialBits8 raw64) ||| 0x8080808080808080#64) =
      prepPrefix ctrl (8 * (g + 1)) := by
  intro cur raw64; let out64 := byteMaskOfBits (specialBits8 raw64) ||| 0x8080808080808080#64
  have hcur_len : cur.length = ctrl.length := prepPrefix_length ctrl (by omega)
  have hnext_len : (prepPrefix ctrl (8 * (g + 1))).length = ctrl.length := prepPrefix_length ctrl hg
  have hunp_len : (ByteSlice.unpackLE 8 out64).length = 8 := ByteSlice.unpackLE_length 8 out64
  have htake_len : (cur.take (8 * g)).length = 8 * g := by simp [Nat.min_eq_left (by omega : 8 * g ≤ cur.length)]
  change (cur.take (8 * g) ++ ByteSlice.unpackLE 8 out64) ++
      cur.drop (8 * g + (ByteSlice.unpackLE 8 out64).length) = prepPrefix ctrl (8 * (g + 1))
  have hlhs_len : ((cur.take (8 * g) ++ ByteSlice.unpackLE 8 out64) ++
      cur.drop (8 * g + (ByteSlice.unpackLE 8 out64).length)).length = ctrl.length := by
    simp [htake_len, hunp_len]; omega
  apply List.ext_getElem (hlhs_len.trans hnext_len.symm); intro i hi1 _
  have hi : i < ctrl.length := hlhs_len ▸ hi1
  rw [prepPrefix_getElem ctrl hg hi]; by_cases hi_lo : i < 8 * g
  · rw [List.getElem_append_left (by simp [htake_len, hunp_len]; omega),
      List.getElem_append_left (by simp [htake_len, hi_lo]), List.getElem_take,
      prepPrefix_getElem ctrl (by omega) hi]; simp [hi_lo, show i < 8 * (g + 1) by omega]
  · by_cases hi_mid : i < 8 * (g + 1)
    · rw [List.getElem_append_left (by simp [htake_len, hunp_len]; omega),
        List.getElem_append_right (by simp [htake_len]; omega)]
      have hj : i - (cur.take (8 * g)).length < 8 := by rw [htake_len]; omega
      rw [getElem_unpackLE8 out64 _ hj, show i - (cur.take (8 * g)).length = i - 8 * g by rw [htake_len]]
      dsimp only [out64]; rw [getLane8_byteMask_special_orr_0x80 raw64 (by omega),
        getLane8_ctrlGroupWord_eq_getElem (by omega) (by omega)]
      have hcur_i : cur[8 * g + (i - 8 * g)]'(by omega) = ctrl[i] := by
        have h1 : cur[8 * g + (i - 8 * g)]'(by omega) =
            (prepPrefix ctrl (8 * g))[i]'(by rw [prepPrefix_length ctrl (by omega)]; exact hi) := by congr 1; omega
        rw [h1, prepPrefix_getElem ctrl (by omega) hi]; simp [hi_lo]
      rw [hcur_i]; simp [hi_mid, prepCtrlByte]
    · rw [List.getElem_append_right (by simp [htake_len, hunp_len]; omega)]
      simp only [List.length_append, htake_len, hunp_len, List.getElem_drop, hi_mid, ↓reduceIte]
      have h1 : cur[8 * g + 8 + (i - (8 * g + 8))]'(by omega) =
          (prepPrefix ctrl (8 * g))[i]'(by rw [prepPrefix_length ctrl (by omega)]; exact hi) := by congr 1; omega
      rw [h1, prepPrefix_getElem ctrl (by omega) hi]; simp [hi_lo]

theorem prepPrefix_mirror_write64 {ctrl : List (BitVec 8)} {buckets : Nat}
    (hge8 : 8 ≤ buckets) (hlen : ctrl.length = buckets + 8) :
    let cur := prepPrefix ctrl buckets
    ByteSlice.write64 cur buckets (ctrlGroupWord cur 0) =
      (ctrl.take buckets).map prepCtrlByte ++ (ctrl.take 8).map prepCtrlByte := by
  intro cur; have hcur_len : cur.length = buckets + 8 := (prepPrefix_length ctrl (by omega)).trans hlen
  change (cur.take buckets ++ ByteSlice.unpackLE 8 (ctrlGroupWord cur 0)) ++
      cur.drop (buckets + (ByteSlice.unpackLE 8 (ctrlGroupWord cur 0)).length) = _
  rw [ByteSlice.unpackLE_length, unpackLE8_ctrlGroupWord (by omega : 0 + 8 ≤ cur.length)]; simp only [List.drop_zero]
  have htake_cur : cur.take buckets = (ctrl.take buckets).map prepCtrlByte := by
    dsimp only [cur, prepPrefix]
    rw [List.take_append_of_le_length (by simp [Nat.min_eq_left (by omega : buckets ≤ ctrl.length)]),
      List.take_of_length_le (by simp [Nat.min_eq_left (by omega : buckets ≤ ctrl.length)])]
  have htake8_cur : cur.take 8 = (ctrl.take 8).map prepCtrlByte := by
    dsimp only [cur, prepPrefix]
    rw [List.take_append_of_le_length (by simp [Nat.min_eq_left (by omega : buckets ≤ ctrl.length), hge8]),
      ← List.map_take, List.take_take, Nat.min_eq_left hge8]
  rw [htake_cur, htake8_cur, (List.drop_eq_nil_iff.mpr (by omega) : cur.drop (buckets + 8) = []), List.append_nil]

theorem write8_write8_eq_setCtrlBytes (bm : BitVec 64) (ctrl : List (BitVec 8)) {idx : Nat} (tag : BitVec 8)
    (hi1 : idx < ctrl.length) (hi2 : setCtrlMirrorIdx bm idx < ctrl.length) :
    ByteSlice.write8 (ByteSlice.write8 ctrl idx tag) (setCtrlMirrorIdx bm idx) tag = setCtrlBytes bm ctrl idx tag := by
  dsimp only [ByteSlice.write8, setCtrlBytes]
  rw [← ByteSlice.set_eq_write ctrl idx tag hi1,
    ← ByteSlice.set_eq_write (ctrl.set idx tag) (setCtrlMirrorIdx bm idx) tag (by simp [hi2])]

/-! ## Preparation Loop, Epilogue, and 4-Bucket Case -/

section MachineProofs
arm64_proof_prelude

theorem mutFrame_setPC (s1 s : State) (pc : BitVec 64) : MutFrame s1 (s.setPC pc) ↔ MutFrame s1 s := by
  simp [MutFrame, StdStatePreserved, State.spAligned]
theorem mutFrame_advancePC (s1 s : State) : MutFrame s1 s.advancePC ↔ MutFrame s1 s := by
  simp [MutFrame, StdStatePreserved, State.spAligned]
theorem mutFrame_setPState (s1 s : State) (ps : PState) : MutFrame s1 (s.setPState ps) ↔ MutFrame s1 s := by
  simp [MutFrame, StdStatePreserved, State.spAligned]
theorem mutFrame_writeReg64 (s1 s : State) (idx : BitVec 5) (val : BitVec 64) (h28 : idx ≠ 28#5 := by decide) :
    MutFrame s1 (s.writeReg64 (.gpr idx) val) ↔ MutFrame s1 s := by
  have hne : Reg.gpr 28#5 ≠ Reg.gpr idx := fun h => by cases h; exact h28 rfl
  simp [MutFrame, StdStatePreserved, State.spAligned, hne]
theorem mutFrame_writeVReg128 (s1 s : State) (v : BitVec 5) (val : BitVec 128)
    (hcs : isCalleeSavedVReg v = false := by decide) :
    MutFrame s1 (s.writeVReg128 v val) ↔ MutFrame s1 s := by
  simp [MutFrame, StdStatePreserved, State.spAligned, calleeSavedVRegs_writeVReg128 s v val hcs]

local macro "mut_simp" h:term : tactic =>
  `(tactic| simp (discharger := decide) only [mutFrame_setPC, mutFrame_advancePC, mutFrame_setPState,
      mutFrame_writeReg64, mutFrame_writeVReg128, $h:term])

private theorem bv64_not_eq_neg_sub_one (x : BitVec 64) : ~~~ x = -x - 1#64 := by
  have h := BitVec.neg_eq_not_add x
  bv_lin [h]

theorem slotAddr_mvn_lsl4 (ctrlPtr : BitVec 64) (i : Nat) :
    ctrlPtr + (~~~ (BitVec.ofNat 64 i)) <<< 4 = slotAddr ctrlPtr i := by
  unfold slotAddr
  rw [bv64_not_eq_neg_sub_one, show 16 * (i + 1) = 16 * i + 16 by omega,
    BitVec.ofNat_add, Nat.mul_comm 16 i, BitVec.ofNat_mul]
  generalize BitVec.ofNat 64 i = x
  change ctrlPtr + (-x - 1#64) <<< 4 = ctrlPtr - (x * 16#64 + 16#64)
  bv_lin

theorem hbRehash_prep_loop_wp (P : HbPlaced) (X : String → Option (State → State))
    {target_pc ctrlPtr : BitVec 64} {ctrl : List (BitVec 8)} {G : Nat}
    {s1 : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hG_le : 8 * G ≤ ctrl.length) (hG_bound : G ≤ 2 ^ 55) :
    ∀ (k : Nat) {g : Nat} {st : State}, k = G - g → g < G →
      st.pc = P.pl.base + 144#64 → st.status = .Running → MutFrame s1 st →
      st.readReg64 (.gpr 8#5) = BitVec.ofNat 64 (G - g) →
      st.readReg64 (.gpr 9#5) = ctrlPtr + BitVec.ofNat 64 (8 * g) →
      st.readVReg128 0#5 = 0x8080808080808080#128 →
      (∀ st' : State, st'.pc = P.pl.base + 168#64 → st'.status = .Running → MutFrame s1 st' →
        (∀ r : Reg, r ≠ .gpr 8#5 → r ≠ .gpr 9#5 → st'.readReg64 r = st.readReg64 r) →
        SepWP ((hbProg P).rebase P.pl.base X) target_pc st'
          ((ctrlPtr ↦ₛ prepPrefix ctrl (8 * G)) ∗ F) post oom) →
      SepWP ((hbProg P).rebase P.pl.base X) target_pc st
        ((ctrlPtr ↦ₛ prepPrefix ctrl (8 * g)) ∗ F) post oom := by
  intro k; induction k with
  | zero => intro g st hk hg; omega
  | succ k ih =>
    intro g st hk hg hpc hrun hmut hx8 hx9 hv0 hcont
    have hP := P.placeable
    let cur := prepPrefix ctrl (8 * g)
    have hcur_len : cur.length = ctrl.length := prepPrefix_length ctrl (by omega)
    wp_conv_pre => rw [pointsToBytes_focus_ctrlGroupWord ctrlPtr cur (pos := 8 * g) (by omega), sepConj_assoc]
    set_option proofLib.wpBranchAutoDecide false in
    wp_sym_steps 4
    wp_conv_pre => rw [← sepConj_assoc, ← pointsToBytes_focus_ctrlGroupWord ctrlPtr cur (pos := 8 * g) (by omega)]
    refine step_strSimd64_perm (pc := P.pl.base + 160#64) (ea := ctrlPtr + BitVec.ofNat 64 (8 * g))
      (wb := some (.gpr 9#5, ctrlPtr + BitVec.ofNat 64 (8 * g) + 8#64))
      (v := byteMaskOfBits (specialBits8 (ctrlGroupWord cur (8 * g))) ||| 0x8080808080808080#64)
      (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
      (by simp only [wp_norm, arm64_norm]; rfl) (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hx9])
      (by simp only [wp_norm, arm64_norm, byteMaskOfBits, specialBits8, packPred8, ofBits8,
            isSpecialTag, getLane8, pack64]; bv_robdd)
      (SepStore64.left (SepStore64.of_pointsToBytes_here _ ctrlPtr cur (8 * g) _ (by omega) rfl))
      fun m' hm_perm => ?_
    dsimp only [applyWriteback]; rw [show P.pl.base + 160#64 + 4#64 = P.pl.base + 164#64 by bv_lin]
    have hp_m : m'.perm = st.mem.perm := by simpa using hm_perm
    rw [prepPrefix_write64_step ctrl (by omega : 8 * (g + 1) ≤ ctrl.length)]
    have h55 : 2 ^ 55 < 2 ^ 64 := by decide
    set_option proofLib.wpBranchAutoDecide false in
    wp_sym_steps 1
    wp_if hne
    · by_cases hg1 : g + 1 = G
      · have h1 : G - g = 1 := by omega
        rw [h1] at hne; simp at hne
      · have hsub_bv : BitVec.ofNat 64 (G - g) - 1#64 = BitVec.ofNat 64 (G - (g + 1)) := by
          conv => lhs; arg 1; rw [show G - g = (G - (g + 1)) + 1 by omega]
          rw [BitVec.ofNat_add]; bv_lin
        refine ih (g := g + 1) (by omega) (by omega) (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm, hrun])
          (by rw [mutFrame_setMem _ _ m' (by simp [hp_m])]; mut_simp hmut)
          (by simp only [wp_norm, arm64_norm]; exact hsub_bv)
          (by simp only [wp_norm, arm64_norm]; rw [show 8 * (g + 1) = 8 * g + 8 by omega, BitVec.ofNat_add]; bv_lin)
          (by simp only [wp_norm, arm64_norm, hv0]) ?_
        intro st'' hpc'' hrun'' hmut'' hregs''
        exact hcont st'' hpc'' hrun'' hmut'' fun r hr8 hr9 =>
          (hregs'' r hr8 hr9).trans (by simp [wp_norm, arm64_norm, hr8, hr9])
    · by_cases hg1 : g + 1 = G
      · rw [hg1]
        exact hcont _ (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
          (by rw [mutFrame_setMem _ _ m' (by simp [hp_m])]; mut_simp hmut)
          fun r hr8 hr9 => by simp [wp_norm, arm64_norm, hr8, hr9]
      · have hnat := congrArg BitVec.toNat hne
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : G - g < 2 ^ 64)] at hnat; simp at hnat; omega

theorem hbRehash_epilogue_wp (P : HbPlaced) (A : HbAlloc) (X : String → Option (State → State))
    {s1 st : State} {mapPtr ctrlPtr bm gl items : BitVec 64} {m : Map64} {F : SepProp} {oom : State → SepProp}
    (hpc : st.pc = P.pl.base + 540#64) (hrun : st.status = .Running) (hmut : MutFrame s1 st)
    (hx0 : st.readReg64 .x0 = mapPtr) (hx20 : st.readReg64 (.gpr 20#5) = bucketMaskToCapacityBV bm)
    (hx22 : st.readReg64 (.gpr 22#5) = items)
    (hent : U64MapStruct mapPtr ctrlPtr bm (bucketMaskToCapacityBV bm - items) items ∗ F ⊢
      U64MapRepReady P.pl A mapPtr m bm) :
    SepWP ((hbProg P).rebase P.pl.base X) (P.pl.base + 1080#64) st
      (U64MapStruct mapPtr ctrlPtr bm gl items ∗ F)
      (fun s2 P2 => MutFrame s1 s2 ∧ s2.readReg64 .x0 = 0xffffffffffffffff#64 ∧
        (P2 ⊢ U64MapRepReady P.pl A mapPtr m bm)) oom := by
  have hP := P.placeable; wp_conv_pre => dsimp only [U64MapStruct]
  set_option proofLib.wpBranchAutoDecide false in
  wp_sym_steps 1
  refine step_str64_perm (pc := P.pl.base + 544#64)
    (ea := mapPtr + 16#64) (wb := none) (val := bucketMaskToCapacityBV bm - items)
    (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [wp_norm, arm64_norm]; rfl) (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hx0]) (by simp only [wp_norm, arm64_norm])
    (SepStore64.left (SepStore64.right (SepStore64.right (SepStore64.left (SepStore64.here rfl)))))
    fun m' hm_perm => ?_
  dsimp only [applyWriteback]; rw [show P.pl.base + 544#64 + 4#64 = P.pl.base + 548#64 by bv_lin]
  have hp_m : m'.perm = st.mem.perm := by simpa using hm_perm
  set_option proofLib.wpBranchAutoDecide false in
  wp_sym_steps 2
  refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
    ⟨by rw [mutFrame_setMem _ _ m' (by simp [hp_m])]; mut_simp hmut,
     by simp only [wp_norm, arm64_norm], hent⟩

private theorem subcase4_empty_facts {bm gl items : BitVec 64}
    {ctrl : List (BitVec 8)} {slots : List (BitVec 64 × BitVec 64)} {m : Map64}
    (hinv : SwissTableInv bm gl items ctrl slots m)
    (hb4 : bm.toNat + 1 = 4) (hle_half : m.length + 1 ≤ bucketMaskToCapacity bm / 2) :
    bm = 3#64 ∧ m = [] ∧ items = 0#64 ∧ (prepPrefix ctrl 8).take 8 = List.replicate 8 tagEmpty := by
  have hbm3 : bm = 3#64 := BitVec.eq_of_toNat_eq (by simp; omega)
  subst hbm3; have hcap : bucketMaskToCapacity 3#64 / 2 = 1 := by decide
  rw [hcap] at hle_half; have hm_nil : m = [] := List.eq_nil_iff_length_eq_zero.2 (by omega)
  subst hm_nil; refine ⟨rfl, rfl, (hinv.items_eq_zero_iff_nil).2 rfl, ?_⟩
  have hlen : ctrl.length = 12 := hinv.mirror.1.trans (by omega)
  have hplen : (prepPrefix ctrl 8).length = 12 := (prepPrefix_length ctrl (by omega)).trans hlen
  apply List.ext_getElem (by simp [hplen]); intro i hi1 _
  have hi8 : i < 8 := by simp [hplen] at hi1; exact hi1
  rw [List.getElem_take, List.getElem_replicate, prepPrefix_getElem ctrl (by omega) (by omega)]
  simp only [hi8, ↓reduceIte]; by_cases hi4 : i < 4
  · cases hsp : isSpecialTag (ctrl[i]'(by omega))
    · have hf : isFullTag (ctrl[i]'(by omega)) = true := by rw [← not_special_iff_full, hsp]
      have hlk := (hinv.full_sound i (by omega) hf).2.1; simp [cliMapLookup] at hlk
    · simp [prepCtrlByte, hsp]
  · have hpad := (hinv.mirror.2.2.1 hb4).1 (i - 4) (by omega)
    rw [show 4 + (i - 4) = i by omega, List.getElem?_eq_getElem (by omega)] at hpad
    injection hpad with hpad'; rw [hpad']; decide

theorem hbRehash_subcase4_wp (P : HbPlaced) (A : HbAlloc) (X : String → Option (State → State))
    (hext : HbExterns ((hbProg P).rebase P.pl.base X) P.pl A)
    {s1 : State} {mapPtr bm : BitVec 64} {m : Map64} {w : HbHeapMapWitness} {oom : State → SepProp}
    (hb4 : bm.toNat + 1 = 4) (hpc : s1.pc = P.pl.base + 120#64) (hrun : s1.status = .Running)
    (hsp_al : s1.spAligned = true) (hCode : A.CodeInv s1.mem) (hx0 : s1.readReg64 .x0 = mapPtr)
    (hx8 : s1.readReg64 .x8 = (bm + 1#64) >>> 3) (hx20 : s1.readReg64 .x20 = bucketMaskToCapacityBV bm)
    (hx22 : s1.readReg64 .x22 = w.items) (hx23 : s1.readReg64 .x23 = bm)
    (hx24 : s1.readReg64 .x24 = bm + 1#64) (hal : mapPtr.toNat % 8 = 0)
    (hnw : mapPtr.toNat + 32 ≤ 2 ^ 64) (hinv : SwissTableInv bm w.growthLeft w.items w.ctrl w.slots m)
    (ha_ne : w.allocPtr ≠ 0#64) (ha_al : w.allocPtr.toNat % 8 = 0)
    (ha_nw : w.allocPtr.toNat + (17 * (bm.toNat + 1) + 8) ≤ 2 ^ 64)
    (hctrl : w.ctrlPtr = w.allocPtr + BitVec.ofNat 64 (16 * (bm.toNat + 1)))
    (hle_half : m.length + 1 ≤ bucketMaskToCapacity bm / 2) :
    SepWP ((hbProg P).rebase P.pl.base X) (P.pl.base + 1080#64) s1
      (hbRodata P.pl ∗ U64MapStruct mapPtr w.ctrlPtr bm w.growthLeft w.items ∗
       A.Block w.allocPtr (17 * (bm.toNat + 1) + 8) 8 ∗
       slotsDownFrom w.ctrlPtr w.slots ∗ (w.ctrlPtr ↦ₛ w.ctrl))
      (fun s2 P2 => MutFrame s1 s2 ∧ s2.readReg64 .x0 = 0xffffffffffffffff#64 ∧
        (P2 ⊢ U64MapRepReady P.pl A mapPtr m bm)) oom := by
  have hP := P.placeable
  rcases subcase4_empty_facts hinv hb4 hle_half with ⟨hbm3, hm_nil, hitems0, htake8⟩
  subst hbm3 hm_nil; rw [hitems0]
  have hctrl_fn : Unit → w.ctrlPtr = w.allocPtr + BitVec.ofNat 64 (16 * ((3#64 : BitVec 64).toNat + 1)) :=
    fun _ => hctrl
  clear hctrl
  have hx8_0 : s1.readReg64 .x8 = 0#64 := hx8.trans (by decide)
  have hx20_3 : s1.readReg64 .x20 = 3#64 := hx20.trans (by decide)
  have hx22_0 : s1.readReg64 .x22 = 0#64 := hx22.trans hitems0
  have hx24_4 : s1.readReg64 .x24 = 4#64 := hx24.trans (by decide)
  let rep4 := List.replicate 4 tagEmpty
  let F_tail := hbRodata P.pl ∗ ((mapPtr ↦₆₄ w.ctrlPtr) ∗ ((mapPtr + 8#64) ↦₆₄ 3#64) ∗
    ((mapPtr + 16#64) ↦₆₄ w.growthLeft) ∗ ((mapPtr + 24#64) ↦₆₄ 0#64)) ∗
    A.Block w.allocPtr (17 * ((3#64 : BitVec 64).toNat + 1) + 8) 8 ∗ slotsDownFrom w.ctrlPtr w.slots
  let F_mm := ((w.ctrlPtr + 4#64) ↦ₛ rep4) ∗ F_tail
  let Q_mm (sm : State) : Prop :=
    MutFrame s1 sm ∧ sm.readReg64 .lr = P.pl.base + 1128#64 ∧
    sm.readReg64 .x0 = w.ctrlPtr + 8#64 ∧ sm.readReg64 .x1 = w.ctrlPtr ∧
    sm.readReg64 .x2 = 4#64 ∧ sm.readReg64 (.gpr 19#5) = w.ctrlPtr ∧
    sm.readReg64 (.gpr 20#5) = 3#64 ∧ sm.readReg64 (.gpr 21#5) = mapPtr ∧
    sm.readReg64 (.gpr 22#5) = 0#64 ∧ sm.readReg64 (.gpr 23#5) = 3#64
  refine SepWP.seq_entails_emp (s := s1) (mid_pc := P.pl.ρ hbMemmoveSym)
    (Q_regs := fun sm => A.CodeInv sm.mem ∧ Q_mm sm)
    (P_mid := (memRegion (w.ctrlPtr + 8#64) 4 ∗ (w.ctrlPtr ↦ₛ rep4)) ∗ F_mm)
    (SepWP.mono_frozen (target := P.pl.ρ hbMemmoveSym) (s := s1) (Φ := A.CodeInv)
      (post := fun sm Pm => Q_mm sm ∧ (Pm ⊢ (memRegion (w.ctrlPtr + 8#64) 4 ∗ (w.ctrlPtr ↦ₛ rep4)) ∗ F_mm))
      (fun _ _ hci hkf => A.codeInv_keepsFrozen hkf hci) hCode ?_
      (fun _ _ _ _ hci ⟨hq, hent⟩ => ⟨⟨hci, hq⟩, hent⟩)) ?_
  · wp_conv_pre => dsimp only [U64MapStruct]
    wp_sym_steps 6
    wp_conv_pre =>
      rw [show hbRodata P.pl ∗ ((mapPtr ↦₆₄ w.ctrlPtr) ∗ ((mapPtr + 8#64) ↦₆₄ 3#64) ∗
            ((mapPtr + 16#64) ↦₆₄ w.growthLeft) ∗ ((mapPtr + 24#64) ↦₆₄ 0#64)) ∗
            A.Block w.allocPtr (17 * ((3#64 : BitVec 64).toNat + 1) + 8) 8 ∗
            slotsDownFrom w.ctrlPtr w.slots ∗ (w.ctrlPtr ↦ₛ w.ctrl) =
          (w.ctrlPtr ↦ₛ prepPrefix w.ctrl (8 * 0)) ∗ F_tail by
        rw [prepPrefix_zero]; dsimp only [F_tail]; ac_rfl]
    refine hbRehash_prep_loop_wp P X (s1 := s1) (ctrlPtr := w.ctrlPtr) (G := 1)
      (by have := hinv.mirror.1; omega) (by decide) 1 (g := 0) rfl (by omega)
      (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
      (by mut_simp (MutFrame.refl hsp_al)) (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm]) ?_
    intro st' hpc' hrun' hmut' hregs'
    have hx0' : st'.readReg64 .x0 = mapPtr :=
      (hregs' .x0 (by decide) (by decide)).trans (by simp [wp_norm, arm64_norm, hx0])
    have hx19' : st'.readReg64 (.gpr 19#5) = w.ctrlPtr :=
      (hregs' (.gpr 19#5) (by decide) (by decide)).trans (by simp [wp_norm, arm64_norm])
    have hx20' : st'.readReg64 (.gpr 20#5) = 3#64 :=
      (hregs' (.gpr 20#5) (by decide) (by decide)).trans (by simp [wp_norm, arm64_norm, hx20_3])
    have hx22' : st'.readReg64 (.gpr 22#5) = 0#64 :=
      (hregs' (.gpr 22#5) (by decide) (by decide)).trans (by simp [wp_norm, arm64_norm, hx22_0])
    have hx23' : st'.readReg64 (.gpr 23#5) = 3#64 :=
      (hregs' (.gpr 23#5) (by decide) (by decide)).trans (by simp [wp_norm, arm64_norm, hx23])
    have hx24' : st'.readReg64 (.gpr 24#5) = 4#64 :=
      (hregs' (.gpr 24#5) (by decide) (by decide)).trans (by simp [wp_norm, arm64_norm, hx24_4])
    wp_sym_steps 7
    refine SepWP.done (by simp only [wp_norm, arm64_norm, hbMemmoveSym]; bv_lin)
      (by simp only [wp_norm, arm64_norm, hrun']) ⟨?_, ?_⟩
    · exact ⟨by mut_simp hmut', by simp only [wp_norm, arm64_norm],
        by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
        by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm, hx19'],
        by simp only [wp_norm, arm64_norm, hx20'], by simp only [wp_norm, arm64_norm],
        by simp only [wp_norm, arm64_norm, hx22'], by simp only [wp_norm, arm64_norm, hx23']⟩
    · let cur := prepPrefix w.ctrl 8
      have hcur_len : cur.length = 12 :=
        (prepPrefix_length w.ctrl (by have := hinv.mirror.1; omega)).trans hinv.mirror.1
      have hcur_eq : cur = rep4 ++ (rep4 ++ cur.drop 8) := by
        conv => lhs; rw [← List.take_append_drop 8 cur, htake8]
        rw [← List.append_assoc]; rfl
      have hpts : (w.ctrlPtr ↦ₛ cur) =
          (w.ctrlPtr ↦ₛ rep4) ∗ (((w.ctrlPtr + 4#64) ↦ₛ rep4) ∗ ((w.ctrlPtr + 8#64) ↦ₛ cur.drop 8)) := by
        conv => lhs; rw [hcur_eq]
        rw [pointsToBytes_append, pointsToBytes_append]
        simp only [rep4, List.length_replicate, show w.ctrlPtr + 4#64 + 4#64 = w.ctrlPtr + 8#64 by bv_lin]
      change (w.ctrlPtr ↦ₛ cur) ∗ F_tail ⊢ _; rw [hpts]
      have hmr : ((w.ctrlPtr + 8#64) ↦ₛ cur.drop 8) ⊢ memRegion (w.ctrlPtr + 8#64) 4 :=
        pointsToBytes_entails_memRegion_of_length (by simp [hcur_len])
      exact Entails.trans (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right hmr)))
        (Entails.of_eq (by dsimp only [F_mm]; ac_rfl))
  · rintro sm hpc_sm hrun_sm ⟨hci_sm, hmut_sm, hlr_sm, hx0_sm, hx1_sm, hx2_sm,
      hx19_sm, hx20_sm, hx21_sm, hx22_sm, hx23_sm⟩
    refine SepWP.call_subroutine_frame hext.memmove_ok
      (x := (w.ctrlPtr + 8#64, w.ctrlPtr, rep4)) (F := F_mm) hpc_sm hrun_sm hmut_sm.2.1 hlr_sm ?_
      (fun _ _ _ h => not_satisfies_false_sepConj h)
      (fun _ _ _ _ h => not_satisfies_false_sepConj h) ?_
      (h_oom := fun _ _ _ h => False.elim (not_satisfies_false_sepConj h))
    · intro R hm; dsimp only [withCodeInv, stdMemcpySpec]; rw [sepConj_assoc] at hm
      exact Satisfies.mono (sepConj_mono_left (Entails.pure_right hci_sm
        (Entails.pure_right ⟨hx0_sm, hx1_sm, hx2_sm, by decide⟩ (Entails.refl _)))) hm
    · intro sf hpc_sf hrun_sf hsp_sf hcs_sf
      dsimp only [withCodeInv, stdMemcpySpec]; rw [sepConj_assoc]; apply SepWP.pure_elim
      rintro ⟨_, hstd_sf⟩
      have hmut_sf : MutFrame s1 sf := MutFrame.of_call hmut_sm hsp_sf hcs_sf hstd_sf
      have hx19_sf : sf.readReg64 (.gpr 19#5) = w.ctrlPtr := hcs_sf.readReg64_x19.trans hx19_sm
      have hx20_sf : sf.readReg64 (.gpr 20#5) = 3#64 := hcs_sf.readReg64_x20.trans hx20_sm
      have hx21_sf : sf.readReg64 (.gpr 21#5) = mapPtr := hcs_sf.readReg64_x21.trans hx21_sm
      have hx22_sf : sf.readReg64 (.gpr 22#5) = 0#64 := hcs_sf.readReg64_x22.trans hx22_sm
      have hx23_sf : sf.readReg64 (.gpr 23#5) = 3#64 := hcs_sf.readReg64_x23.trans hx23_sm
      have hrep4_open : (w.ctrlPtr ↦ₛ rep4) = (w.ctrlPtr ↦₈ 0xff#8) ∗ ((w.ctrlPtr + 1#64) ↦₈ 0xff#8) ∗
          ((w.ctrlPtr + 2#64) ↦₈ 0xff#8) ∗ ((w.ctrlPtr + 3#64) ↦₈ 0xff#8) ∗ ((w.ctrlPtr + 4#64) ↦ₛ []) := by
        dsimp only [rep4, tagEmpty, List.replicate]
        rw [pointsToBytes_cons, pointsToBytes_cons, pointsToBytes_cons, pointsToBytes_cons]
        simp only [show w.ctrlPtr + 1#64 + 1#64 = w.ctrlPtr + 2#64 by bv_lin,
          show w.ctrlPtr + 2#64 + 1#64 = w.ctrlPtr + 3#64 by bv_lin,
          show w.ctrlPtr + 3#64 + 1#64 = w.ctrlPtr + 4#64 by bv_lin]
      have hrep12 : (w.ctrlPtr ↦ₛ List.replicate 12 tagEmpty) =
          (w.ctrlPtr ↦ₛ rep4) ∗ (((w.ctrlPtr + 4#64) ↦ₛ rep4) ∗ ((w.ctrlPtr + 8#64) ↦ₛ rep4)) := by
        change (w.ctrlPtr ↦ₛ (rep4 ++ (rep4 ++ rep4))) = _
        rw [pointsToBytes_append, pointsToBytes_append]
        simp only [rep4, List.length_replicate, show w.ctrlPtr + 4#64 + 4#64 = w.ctrlPtr + 8#64 by bv_lin]
      wp_conv_pre => rw [hrep4_open]
      wp_sym_steps 33
      wp_conv_pre =>
        rw [← hrep4_open]; dsimp only [F_mm, F_tail]
        rw [show (((w.ctrlPtr + 8#64) ↦ₛ rep4) ∗ (w.ctrlPtr ↦ₛ rep4)) ∗
              (((w.ctrlPtr + 4#64) ↦ₛ rep4) ∗
              (hbRodata P.pl ∗ ((mapPtr ↦₆₄ w.ctrlPtr) ∗ ((mapPtr + 8#64) ↦₆₄ 3#64) ∗
               ((mapPtr + 16#64) ↦₆₄ w.growthLeft) ∗ ((mapPtr + 24#64) ↦₆₄ 0#64)) ∗
               A.Block w.allocPtr (17 * ((3#64 : BitVec 64).toNat + 1) + 8) 8 ∗
               slotsDownFrom w.ctrlPtr w.slots)) =
            U64MapStruct mapPtr w.ctrlPtr 3#64 w.growthLeft 0#64 ∗
              (hbRodata P.pl ∗ A.Block w.allocPtr (17 * ((3#64 : BitVec 64).toNat + 1) + 8) 8 ∗
               slotsDownFrom w.ctrlPtr w.slots ∗ (w.ctrlPtr ↦ₛ List.replicate 12 tagEmpty)) by
          rw [hrep12]; dsimp only [U64MapStruct]; ac_rfl]
      refine hbRehash_epilogue_wp P A X (s1 := s1) (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm, hrun_sf]) (by mut_simp hmut_sf)
        (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hx20_sf]; rfl)
        (by simp only [wp_norm, arm64_norm, hx22_sf]) ?_
      have hsub0 : bucketMaskToCapacityBV 3#64 - 0#64 = bucketMaskToCapacityBV 3#64 := by decide
      rw [hsub0, hctrl_fn ()]
      exact Entails.trans (Entails.of_eq (by ac_rfl))
        (U64MapRepReady_init hinv.validMask hal hnw ha_ne ha_al ha_nw hinv.slots_len)

end MachineProofs

end CaseStudies.Hashbrown.Proofs
