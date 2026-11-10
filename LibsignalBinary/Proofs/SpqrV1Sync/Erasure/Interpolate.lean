/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1Sync.ErasureDefs
import LibsignalBinary.Proofs.SpqrV1Sync.Erasure.Complete
import LibsignalBinary.Proofs.SpqrV1Sync.Erasure.Prepare

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1Sync.Erasure.Interpolate

open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1Sync.GF16Field
open CryptoVerification.SpqrV1Sync.Erasure.Prepare
open CryptoVerification.SpqrV1Sync.Erasure.Complete
open Polynomial

theorem gf16_toNat_injective : Function.Injective (fun x : GF16 => x.value.toNat) := by
  intro a b h
  cases a; cases b
  congr
  exact BitVec.eq_of_toNat_eq h

theorem length_le_of_nodup_x (pts : List Pt) (hnd : (pts.map Pt.x).Nodup) :
    pts.length ≤ 2 ^ 16 := by
  let ns := (pts.map Pt.x).map (fun x => x.value.toNat)
  have hnd_ns : ns.Nodup := hnd.map gf16_toNat_injective
  have hsub : ns.toFinset ⊆ Finset.range (2 ^ 16) := by
    intro k hk
    rw [List.mem_toFinset] at hk
    rcases List.mem_map.1 hk with ⟨x, _, rfl⟩
    exact Finset.mem_range.2 x.value.isLt
  have hcard : ns.toFinset.card ≤ (Finset.range (2 ^ 16)).card :=
    Finset.card_le_card hsub
  rw [List.card_toFinset, hnd_ns.dedup, Finset.card_range] at hcard
  simpa [ns] using hcard

def zipAdd : List GF16 → List GF16 → List GF16
  | [], _ => []
  | _, [] => []
  | a :: as, b :: bs => GF16.add a b :: zipAdd as bs

theorem length_zipAdd :
    ∀ (as bs : List GF16), as.length = bs.length → (zipAdd as bs).length = as.length
  | [], [], _ => rfl
  | _ :: _, [], h => by simp at h
  | [], _ :: _, h => by simp at h
  | a :: as, b :: bs, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp [zipAdd, length_zipAdd as bs h]

theorem polyOf_zipAdd :
    ∀ (as bs : List GF16), as.length = bs.length →
      polyOf (zipAdd as bs) = polyOf as + polyOf bs
  | [], [], _ => by simp [zipAdd]
  | _ :: _, [], h => by simp at h
  | [], _ :: _, h => by simp at h
  | a :: as, b :: bs, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    rw [zipAdd, polyOf_cons, polyOf_zipAdd as bs h, polyOf_cons, polyOf_cons, ← add_eq, map_add]
    ring

theorem lagrangeAccumulateCoeffs_eq_zipAdd (w0 : GF16) :
    ∀ (outRest wRest pre preW : List GF16) (j : Nat),
      outRest.length = wRest.length →
      pre.length = j →
      preW.length = j →
      j + outRest.length ≤ USIZE_MAX →
      Poly.lagrangeAccumulateCoeffs j outRest.length (pre ++ outRest) (w0 :: preW ++ wRest) =
        .ok (pre ++ zipAdd outRest wRest)
  | [], [], pre, _, j, _, _, _, _ => by
    simp [Poly.lagrangeAccumulateCoeffs, zipAdd]
  | _ :: _, [], _, _, _, hlen, _, _, _ => by simp at hlen
  | [], _ :: _, _, _, _, hlen, _, _, _ => by simp at hlen
  | o :: os, w :: ws, pre, preW, j, hlen, hpre, hpreW, husize => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    have hnotgt : ¬ (j + 1 > USIZE_MAX) := by simp at husize; omega
    have hget_o : (pre ++ o :: os)[j]? = some o := by
      rw [← hpre, List.getElem?_append_right (Nat.le_refl _)]
      simp
    have hget_w : (w0 :: preW ++ w :: ws)[j + 1]? = some w := by
      change (w0 :: (preW ++ w :: ws))[j + 1]? = some w
      rw [List.getElem?_cons_succ, ← hpreW, List.getElem?_append_right (Nat.le_refl _)]
      simp
    have hset : (pre ++ o :: os).set j (GF16.add o w) = (pre ++ [GF16.add o w]) ++ os := by
      rw [← hpre, List.set_append_right _ _ (Nat.le_refl _)]
      simp [List.append_assoc]
    have hw_assoc : w0 :: preW ++ w :: ws = w0 :: (preW ++ [w]) ++ ws := by
      simp [List.append_assoc]
    rw [List.length_cons, Poly.lagrangeAccumulateCoeffs]
    simp only [hnotgt, ↓reduceIte, hget_o, hget_w, hset]
    rw [hw_assoc]
    rw [lagrangeAccumulateCoeffs_eq_zipAdd w0 os ws (pre ++ [GF16.add o w]) (preW ++ [w]) (j + 1)
      hlen (by simp [hpre]) (by simp [hpreW]) (by simp at husize ⊢; omega)]
    simp [List.append_assoc, zipAdd]

theorem lagrangeAccumulateCoeffs_zero_spec (outCoeffs w : List GF16) (n : Nat)
    (hout : outCoeffs.length = n) (hw : w.length = n + 1) (husize : n ≤ USIZE_MAX) :
    Poly.lagrangeAccumulateCoeffs 0 outCoeffs.length outCoeffs w =
      .ok (zipAdd outCoeffs w.tail) := by
  cases w with
  | nil => simp at hw
  | cons w0 wTail =>
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hw
    simpa using lagrangeAccumulateCoeffs_eq_zipAdd w0 outCoeffs wTail [] [] 0
      (by omega) rfl rfl (by omega)

noncomputable def lagrangeTerm (pts : List Pt) (k : Nat) : GF16[X] :=
  if hk : k < pts.length then
    C (GF16.div pts[k].y (Poly.lagrangeDenominator pts[k].x pts)) *
      ((pts.eraseIdx k).map fun pt => X - C pt.x).prod
  else 0

theorem lagrangeInterpolateLoop_spec (pts : List Pt) (template : Poly)
    (ht_len : template.coefficients.length = pts.length + 1)
    (ht_poly : polyOf template.coefficients = (pts.map fun pt => X - C pt.x).prod)
    (husize : pts.length ≤ USIZE_MAX) :
    ∀ (rem i : Nat) (outCoeffs : List GF16),
      i + rem = pts.length →
      outCoeffs.length = pts.length →
      polyOf outCoeffs = ∑ k ∈ Finset.range i, lagrangeTerm pts k →
      ∃ res : List GF16,
        Poly.lagrangeInterpolateLoop template pts i rem outCoeffs = .ok res ∧
        res.length = pts.length ∧
        polyOf res = ∑ k ∈ Finset.range pts.length, lagrangeTerm pts k := by
  intro rem
  induction rem with
  | zero =>
    intro i outCoeffs hsum hout hpoly
    have hi : i = pts.length := by omega
    subst hi
    exact ⟨outCoeffs, by simp [Poly.lagrangeInterpolateLoop], hout, hpoly⟩
  | succ m ih =>
    intro i outCoeffs hsum hout hpoly
    have hi : i < pts.length := by omega
    obtain ⟨working, hw_ok, hw_len, hw_poly⟩ :=
      lagrangeInterpolateComplete_spec pts template i hi ht_len ht_poly
    have hacc := lagrangeAccumulateCoeffs_zero_spec outCoeffs working.coefficients pts.length
      hout hw_len husize
    rw [Poly.lagrangeInterpolateLoop, hw_ok]
    dsimp only [Bind.bind, Except.bind]
    rw [hacc]
    dsimp only
    have hlen_tail : working.coefficients.tail.length = pts.length := by
      simp [hw_len]
    apply ih (i + 1) (zipAdd outCoeffs working.coefficients.tail)
    · omega
    · rw [length_zipAdd outCoeffs working.coefficients.tail (by omega), hout]
    · rw [polyOf_zipAdd outCoeffs working.coefficients.tail (by omega), hpoly, hw_poly,
        Finset.sum_range_succ]
      simp [lagrangeTerm, hi]

theorem eval_prod_X_sub_C (ls : List Pt) (x : GF16) :
    ((ls.map fun (pt : Pt) => X - C pt.x).prod).eval x = (ls.map fun (pt : Pt) => x - pt.x).prod := by
  induction ls with
  | nil =>
    rw [List.map_nil, List.prod_nil, eval_one, List.map_nil, List.prod_nil]
  | cons p ps ih =>
    rw [List.map_cons, List.prod_cons, eval_mul, eval_sub, eval_X, eval_C, ih,
      List.map_cons, List.prod_cons]

theorem mem_eraseIdx_of_ne {α : Type*} :
    ∀ (xs : List α) (k j : Nat) (_hk : k < xs.length) (hj : j < xs.length),
      k ≠ j → xs[j] ∈ xs.eraseIdx k
  | [], _, _, _hk, _, _ => by contradiction
  | _ :: _, 0, 0, _, _, hne => absurd rfl hne
  | _ :: xs, 0, j + 1, _, hj, _ => by
    simp only [List.getElem_cons_succ, List.eraseIdx_zero, List.tail_cons]
    exact List.getElem_mem (Nat.lt_of_succ_lt_succ hj)
  | x :: _, k + 1, 0, _, _, _ => by
    simp [List.eraseIdx_cons_succ]
  | x :: xs, k + 1, j + 1, hk, hj, hne => by
    simp only [List.getElem_cons_succ, List.eraseIdx_cons_succ]
    exact List.mem_cons_of_mem x
      (mem_eraseIdx_of_ne xs k j (Nat.lt_of_succ_lt_succ hk) (Nat.lt_of_succ_lt_succ hj) (by omega))

theorem prod_sub_eq_zero_of_mem (x : GF16) :
    ∀ (ls : List Pt), (∃ p ∈ ls, p.x = x) → (ls.map fun pt => x - pt.x).prod = 0
  | [], ⟨_, hmem, _⟩ => by simp at hmem
  | p :: ps, ⟨q, hmem, hqx⟩ => by
    rw [List.map_cons, List.prod_cons]
    rcases List.mem_cons.1 hmem with rfl | hmem'
    · rw [hqx, sub_self, zero_mul]
    · rw [prod_sub_eq_zero_of_mem x ps ⟨q, hmem', hqx⟩, mul_zero]

def denomStep (pix denominator : GF16) (pj : Pt) : GF16 :=
  if pix == pj.x then denominator else GF16.mul denominator (GF16.sub pix pj.x)

theorem foldl_denomStep_not_mem (pix : GF16) :
    ∀ (ls : List Pt) (acc : GF16),
      pix ∉ ls.map Pt.x →
      ls.foldl (denomStep pix) acc = acc * (ls.map fun pj => pix - pj.x).prod
  | [], acc, _ => by
    rw [List.foldl_nil, List.map_nil, List.prod_nil, mul_one]
  | p :: ps, acc, hnotmem => by
    simp only [List.map_cons, List.mem_cons, not_or] at hnotmem
    have hbeq : (pix == p.x) = false := beq_false_of_ne hnotmem.1
    simp only [List.foldl_cons, denomStep, hbeq, Bool.false_eq_true, ↓reduceIte,
      List.map_cons, List.prod_cons]
    have hstep : GF16.mul acc (GF16.sub pix p.x) = acc * (pix - p.x) := rfl
    rw [hstep, foldl_denomStep_not_mem pix ps (acc * (pix - p.x)) hnotmem.2, mul_assoc]

theorem foldl_denomStep_eraseIdx :
    ∀ (ls : List Pt) (i : Nat) (hi : i < ls.length) (acc : GF16),
      (ls.map Pt.x).Nodup →
      ls.foldl (denomStep ls[i].x) acc =
        acc * ((ls.eraseIdx i).map fun pj => ls[i].x - pj.x).prod
  | [], _, hi, _, _ => by contradiction
  | p :: ps, 0, _, acc, hnd => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [List.getElem_cons_zero, List.foldl_cons, denomStep, beq_self_eq_true, ↓reduceIte,
      List.eraseIdx_zero, List.tail_cons]
    exact foldl_denomStep_not_mem p.x ps acc hnd.1
  | p :: ps, k + 1, hi, acc, hnd => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    have hk : k < ps.length := Nat.lt_of_succ_lt_succ hi
    have hmem : ps[k].x ∈ ps.map Pt.x := List.mem_map_of_mem (List.getElem_mem hk)
    have hne : ps[k].x ≠ p.x := fun heq => hnd.1 (heq ▸ hmem)
    have hbeq : (ps[k].x == p.x) = false := beq_false_of_ne hne
    simp only [List.getElem_cons_succ, List.foldl_cons, denomStep, hbeq, Bool.false_eq_true,
      ↓reduceIte, List.eraseIdx_cons_succ, List.map_cons, List.prod_cons]
    have hstep : GF16.mul acc (GF16.sub ps[k].x p.x) = acc * (ps[k].x - p.x) := rfl
    rw [hstep, foldl_denomStep_eraseIdx ps k hk (acc * (ps[k].x - p.x)) hnd.2, mul_assoc]

theorem lagrangeDenominator_eq_prod_eraseIdx (pts : List Pt) (i : Nat) (hi : i < pts.length)
    (hnd : (pts.map Pt.x).Nodup) :
    Poly.lagrangeDenominator pts[i].x pts =
      ((pts.eraseIdx i).map fun pj => pts[i].x - pj.x).prod := by
  unfold Poly.lagrangeDenominator
  change pts.foldl (denomStep pts[i].x) GF16.ONE = _
  rw [foldl_denomStep_eraseIdx pts i hi GF16.ONE hnd, ← one_eq, one_mul]

theorem not_mem_map_eraseIdx :
    ∀ (ls : List Pt) (i : Nat) (hi : i < ls.length),
      (ls.map Pt.x).Nodup →
      ls[i].x ∉ (ls.eraseIdx i).map Pt.x
  | [], _, hi, _ => by contradiction
  | p :: ps, 0, _, hnd => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    simpa using hnd.1
  | p :: ps, k + 1, hi, hnd => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    have hk : k < ps.length := Nat.lt_of_succ_lt_succ hi
    have hmem : ps[k].x ∈ ps.map Pt.x := List.mem_map_of_mem (List.getElem_mem hk)
    have hne : ps[k].x ≠ p.x := fun heq => hnd.1 (heq ▸ hmem)
    simp only [List.getElem_cons_succ, List.eraseIdx_cons_succ, List.map_cons, List.mem_cons,
      not_or]
    exact ⟨hne, not_mem_map_eraseIdx ps k hk hnd.2⟩

theorem prod_sub_ne_zero_of_not_mem (x : GF16) :
    ∀ (ls : List Pt), x ∉ ls.map Pt.x → (ls.map fun pj => x - pj.x).prod ≠ 0
  | [], _ => one_ne_zero
  | p :: ps, hnotmem => by
    simp only [List.map_cons, List.mem_cons, not_or] at hnotmem
    rw [List.map_cons, List.prod_cons]
    exact mul_ne_zero (sub_ne_zero.2 hnotmem.1) (prod_sub_ne_zero_of_not_mem x ps hnotmem.2)

theorem eval_lagrangeTerm_eq (pts : List Pt) (hnd : (pts.map Pt.x).Nodup)
    (j : Nat) (hj : j < pts.length) :
    (∑ k ∈ Finset.range pts.length, lagrangeTerm pts k).eval pts[j].x = pts[j].y := by
  rw [Polynomial.eval_finsetSum]
  rw [Finset.sum_eq_single j]
  · simp only [lagrangeTerm, hj, ↓reduceDIte, eval_mul, eval_C]
    rw [eval_prod_X_sub_C, lagrangeDenominator_eq_prod_eraseIdx pts j hj hnd, ← div_eq]
    have hne : ((pts.eraseIdx j).map fun pj => pts[j].x - pj.x).prod ≠ 0 :=
      prod_sub_ne_zero_of_not_mem pts[j].x (pts.eraseIdx j) (not_mem_map_eraseIdx pts j hj hnd)
    exact div_mul_cancel₀ pts[j].y hne
  · intro k hk hkj
    have hk_lt : k < pts.length := Finset.mem_range.1 hk
    simp only [lagrangeTerm, hk_lt, ↓reduceDIte, eval_mul, eval_C]
    rw [eval_prod_X_sub_C]
    have hmem : pts[j] ∈ pts.eraseIdx k := mem_eraseIdx_of_ne pts k j hk_lt hj hkj
    rw [prod_sub_eq_zero_of_mem pts[j].x (pts.eraseIdx k) ⟨pts[j], hmem, rfl⟩, mul_zero]
  · intro hj_not
    exact absurd (Finset.mem_range.2 hj) hj_not

theorem lagrangeInterpolate_spec (pts : List Pt) (hnd : (pts.map Pt.x).Nodup) :
    ∃ p : Poly, Poly.lagrangeInterpolate pts = .ok p ∧
      p.coefficients.length = pts.length ∧
      ∀ pt ∈ pts, (polyOf p.coefficients).eval pt.x = pt.y := by
  unfold Poly.lagrangeInterpolate
  cases hpts : pts with
  | nil =>
    refine ⟨Poly.zero 0, rfl, rfl, ?_⟩
    intro pt hmem
    simp at hmem
  | cons pt0 ptsRest =>
    rw [← hpts]
    have hemp : pts.isEmpty = false := by simp [hpts]
    have hpos : 0 < pts.length := by simp [hpts]
    have hle16 : pts.length ≤ 2 ^ 16 := length_le_of_nodup_x pts hnd
    have husize1 : pts.length + 1 ≤ USIZE_MAX := by unfold USIZE_MAX; omega
    have husize : pts.length ≤ USIZE_MAX := by omega
    obtain ⟨template, hprep_ok, ht_len, ht_poly⟩ :=
      lagrangeInterpolatePrepare_spec_usize pts husize1
    obtain ⟨working0, hw0_ok, hw0_len, hw0_poly⟩ :=
      lagrangeInterpolateComplete_spec pts template 0 hpos ht_len ht_poly
    cases hw0 : working0.coefficients with
    | nil =>
      rw [hw0] at hw0_len
      simp at hw0_len
    | cons w0 rest0 =>
      have hrest0_len : rest0.length = pts.length := by
        rw [hw0, List.length_cons] at hw0_len
        omega
      have hrest0_poly : polyOf rest0 = ∑ k ∈ Finset.range 1, lagrangeTerm pts k := by
        rw [Finset.sum_range_one]
        simp only [List.tail_cons, hw0] at hw0_poly
        simpa [lagrangeTerm, hpos] using hw0_poly
      obtain ⟨outCoeffs, hloop_ok, hout_len, hout_poly⟩ :=
        lagrangeInterpolateLoop_spec pts template ht_len ht_poly husize
          (pts.length - 1) 1 rest0 (by omega) hrest0_len hrest0_poly
      simp only [hemp, Bool.false_eq_true, ↓reduceIte]
      rw [hprep_ok]
      dsimp only [Bind.bind, Except.bind]
      rw [hw0_ok]
      dsimp only
      rw [hw0]
      dsimp only
      rw [hloop_ok]
      refine ⟨{ coefficients := outCoeffs }, rfl, hout_len, ?_⟩
      intro pt hmem
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hmem
      rw [hout_poly]
      exact eval_lagrangeTerm_eq pts hnd j hj

end CryptoVerification.SpqrV1Sync.Erasure.Interpolate
