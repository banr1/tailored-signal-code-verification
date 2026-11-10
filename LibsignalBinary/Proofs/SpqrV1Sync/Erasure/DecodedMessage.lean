/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1Sync.ErasureDefs
import LibsignalBinary.Proofs.SpqrV1Sync.ErasurePoly

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1Sync.Erasure.DecodedMessage

open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1Sync.GF16Field
open Polynomial

/-! ## Arithmetic and `needed` helpers -/

theorem needed_le_needed_zero (L j : Nat) : needed L j ≤ needed L 0 := by
  simp only [needed]
  split <;> split <;> omega

theorem needed_le_two_pow_16 (L j : Nat) (hL : L ≤ 2 ^ 20) : needed L j ≤ 2 ^ 16 := by
  simp only [needed]
  split <;> omega

theorem div_16_lt_needed (L i : Nat) (hi : i < L / 2) : i / 16 < needed L (i % 16) := by
  simp only [needed]
  split <;> omega

theorem eval_msgPoly_at_idxPt (msg : List (BitVec 8)) (hlen : msg.length ≤ 2 ^ 20)
    (i : Nat) (hi : i < msg.length / 2) :
    (msgPoly msg (i % 16)).eval (idxPt (i / 16)) = msgVal msg i := by
  have hinj : Set.InjOn idxPt (Finset.range (needed msg.length (i % 16))) :=
    idxPt_injOn (needed msg.length (i % 16)) (needed_le_two_pow_16 msg.length (i % 16) hlen)
  have hmem : i / 16 ∈ Finset.range (needed msg.length (i % 16)) :=
    Finset.mem_range.mpr (div_16_lt_needed msg.length i hi)
  have heval := Lagrange.eval_interpolate_at_node
    (fun k => msgVal msg (16 * k + i % 16)) hinj hmem
  rw [msgPoly, heval]
  congr 1
  omega

/-! ## Point set and node helpers -/

theorem idxPt_value_toNat (c : Nat) (hc : c < 2 ^ 16) : (idxPt c).value.toNat = c := by
  simp only [idxPt, GF16.new, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt hc

theorem nodup_map_x_of_sorted {pts : List Pt}
    (h : (pts.map fun pt => pt.x.value.toNat).Pairwise (· < ·)) :
    (pts.map Pt.x).Nodup := by
  have hnd : (pts.map fun pt => pt.x.value.toNat).Nodup := h.imp ne_of_lt
  have hmap : pts.map (fun pt => pt.x.value.toNat) = (pts.map Pt.x).map (fun x => x.value.toNat) := by
    rw [List.map_map]
    rfl
  rw [hmap] at hnd
  exact List.Nodup.of_map _ hnd

theorem pts_vec_length_le_card {msg : List (BitVec 8)} {S : Finset Nat} {dec : PolyDecoder}
    (hd : DecInv msg S dec) (j : Nat) (hj : j < dec.pts.length) :
    (dec.pts[j]).vec.length ≤ S.card := by
  let xs := (dec.pts[j]).vec.map fun pt => pt.x.value.toNat
  have hnd : xs.Nodup := (hd.sorted j hj).imp ne_of_lt
  have hsub : xs.toFinset ⊆ S := by
    intro a ha
    rw [List.mem_toFinset] at ha
    obtain ⟨pt, hpt, rfl⟩ := List.mem_map.mp ha
    obtain ⟨c, hcS, hclt, hcx⟩ := hd.atNode j hj pt hpt
    rw [hcx, idxPt_value_toNat c hclt]
    exact hcS
  calc (dec.pts[j]).vec.length
      = xs.length := (List.length_map _).symm
    _ = xs.toFinset.card := (List.toFinset_card_of_nodup hnd).symm
    _ ≤ S.card := Finset.card_le_card hsub

/-! ## `collectPointsVecs` helpers -/

theorem collectPointsVecs_true (dec : PolyDecoder) :
    ∀ (i rem : Nat) (pointsVecs : List (List Pt)),
      i + rem ≤ dec.pts.length →
      ∃ pointsVecs',
        PolyDecoder.collectPointsVecs dec i rem true pointsVecs = .ok (true, pointsVecs')
  | _, 0, pointsVecs, _ => ⟨pointsVecs, rfl⟩
  | i, rem + 1, pointsVecs, h => by
    have hi : i < dec.pts.length := by omega
    unfold PolyDecoder.collectPointsVecs
    rw [List.getElem?_eq_getElem hi]
    dsimp only [bind, Except.bind]
    split <;> exact collectPointsVecs_true dec (i + 1) rem _ (by omega)

theorem decodedMessage_none_aux (msg : List (BitVec 8)) (S : Finset Nat) (dec : PolyDecoder)
    (hd : DecInv msg S dec) (hS : S.card < needed msg.length 0) :
    dec.decodedMessage = .ok none := by
  have hlen : dec.pts.length = 16 := hd.len
  have h0 : 0 < dec.pts.length := by omega
  have hnec0 : dec.necessaryPoints 0 = needed msg.length 0 :=
    necessaryPoints_eq dec msg.length hd.ptsNeeded 0
  have hpts0 : (dec.pts[0]).len < dec.necessaryPoints 0 := by
    rw [SortedSetPt.len, hnec0]
    exact Nat.lt_of_le_of_lt (pts_vec_length_le_card hd 0 h0) hS
  unfold PolyDecoder.decodedMessage
  rw [hd.notComplete, hlen]
  change (do
    let (retNone, pointsVecs) ← PolyDecoder.collectPointsVecs dec 0 (15 + 1) false []
    if retNone = true then return none
    else if dec.ptsNeeded * 2 > USIZE_MAX then .error .mulOverflow
    else
      let initPolys := List.replicate 16 none
      let (_, out) ← PolyDecoder.decodedMessageLoop dec pointsVecs 0 dec.ptsNeeded initPolys []
      return some out) = .ok none
  unfold PolyDecoder.collectPointsVecs
  rw [List.getElem?_eq_getElem h0]
  dsimp only [bind, Except.bind]
  rw [ite_eq_left_iff.mpr (fun h => absurd hpts0 h)]
  obtain ⟨pointsVecs', htrue⟩ := collectPointsVecs_true dec 1 15 [] (by omega)
  rw [htrue]
  rfl

theorem collectPointsVecs_spec (dec : PolyDecoder)
    (hnec : ∀ j (hj : j < dec.pts.length), dec.necessaryPoints j ≤ (dec.pts[j]).len) :
    ∀ (i rem : Nat) (acc : List (List Pt)),
      i + rem = dec.pts.length →
      acc.length = i →
      (∀ j (_hj : j < i) (hj' : j < dec.pts.length),
        acc[j]? = some ((dec.pts[j]).vec.take (dec.necessaryPoints j))) →
      ∃ pointsVecs,
        PolyDecoder.collectPointsVecs dec i rem false acc = .ok (false, pointsVecs) ∧
        pointsVecs.length = dec.pts.length ∧
        ∀ j (hj : j < dec.pts.length),
          pointsVecs[j]? = some ((dec.pts[j]).vec.take (dec.necessaryPoints j))
  | i, 0, acc, hsum, hacc_len, hacc => by
    refine ⟨acc, rfl, by omega, fun j hj => hacc j (by omega) hj⟩
  | i, rem + 1, acc, hsum, hacc_len, hacc => by
    have hi : i < dec.pts.length := by omega
    have hnotlt : ¬ (dec.pts[i]).len < dec.necessaryPoints i := Nat.not_lt.mpr (hnec i hi)
    unfold PolyDecoder.collectPointsVecs
    rw [List.getElem?_eq_getElem hi]
    dsimp only [bind, Except.bind]
    rw [ite_eq_right_iff.mpr (fun h => absurd h hnotlt)]
    refine collectPointsVecs_spec dec hnec (i + 1) rem
      (acc ++ [(dec.pts[i]).asSlice.take (dec.necessaryPoints i)]) (by omega)
      (by simp [hacc_len]) (fun j hj hj' => ?_)
    by_cases hji : j < i
    · rw [List.getElem?_append_left (by omega)]
      exact hacc j hji hj'
    · have hjeq : j = i := by omega
      subst hjeq
      rw [List.getElem?_append_right (by omega)]
      simp [hacc_len, SortedSetPt.asSlice]

/-! ## Interpolation and binary search helpers -/

theorem lagrangeInterpolate_ptsSlice_spec (msg : List (BitVec 8)) (S : Finset Nat)
    (dec : PolyDecoder) (hd : DecInv msg S dec) (hlen : msg.length ≤ 2 ^ 20)
    (hS : needed msg.length 0 ≤ S.card) (j : Nat) (hj : j < 16) :
    ∃ interp : Poly,
      Poly.lagrangeInterpolate
        ((dec.pts[j]'(by have := hd.len; omega)).vec.take (needed msg.length j)) = .ok interp ∧
      polyOf interp.coefficients = msgPoly msg j := by
  have hj' : j < dec.pts.length := by have := hd.len; omega
  let vec := (dec.pts[j]'hj').vec
  let n := needed msg.length j
  have hnS : n ≤ S.card := Nat.le_trans (needed_le_needed_zero msg.length j) hS
  have hvec_len : n ≤ vec.length := by
    have hen := hd.enough j hj'
    rwa [Nat.min_eq_right hnS] at hen
  have hslice_len : (vec.take n).length = n := by
    simp [List.length_take, Nat.min_eq_left hvec_len]
  have hsorted_slice : ((vec.take n).map fun pt => pt.x.value.toNat).Pairwise (· < ·) := by
    rw [List.map_take]
    exact (hd.sorted j hj').take
  have hnd : ((vec.take n).map Pt.x).Nodup := nodup_map_x_of_sorted hsorted_slice
  obtain ⟨interp, hok, hcoeff_len, heval⟩ := lagrangeInterpolate_spec (vec.take n) hnd
  refine ⟨interp, hok, ?_⟩
  let xs : Finset GF16 := ((vec.take n).map Pt.x).toFinset
  have hxs_card : xs.card = n := by
    rw [List.toFinset_card_of_nodup hnd, List.length_map, hslice_len]
  have hdeg1 : (polyOf interp.coefficients).degree < xs.card := by
    rw [hxs_card, ← hslice_len, ← hcoeff_len]
    exact degree_polyOf_lt interp.coefficients
  have hdeg2 : (msgPoly msg j).degree < xs.card := by
    rw [hxs_card, msgPoly]
    have hcard_range : (Finset.range n).card = n := Finset.card_range n
    rw [← hcard_range]
    exact Lagrange.degree_interpolate_lt _
      (idxPt_injOn n (needed_le_two_pow_16 msg.length j hlen))
  refine Polynomial.eq_of_degrees_lt_of_eval_finset_eq xs hdeg1 hdeg2 (fun x hx => ?_)
  rw [List.mem_toFinset] at hx
  obtain ⟨pt, hpt_slice, rfl⟩ := List.mem_map.mp hx
  have hpt_vec : pt ∈ vec := List.mem_of_mem_take hpt_slice
  rw [heval pt hpt_slice, hd.onPoly j hj' pt hpt_vec]

theorem pt_cmp_eq_iff (a b : Pt) : Pt.cmp a b = .eq ↔ a.x = b.x := by
  simp only [Pt.cmp, Ord.compare, compareOfLessAndEq]
  split
  · rename_i hlt
    simp only [reduceCtorEq, false_iff]
    intro h
    rw [h] at hlt
    exact Nat.lt_irrefl _ hlt
  · split
    · rename_i hlt heq
      simp only [true_iff]
      cases ha : a.x with | mk va =>
      cases hb : b.x with | mk vb =>
      simp only [ha, hb] at heq
      congr 1
      exact BitVec.eq_of_toNat_eq heq
    · rename_i hlt heq
      simp only [reduceCtorEq, false_iff]
      intro h
      rw [h] at heq
      exact heq rfl

theorem binarySearchAux_ok {target : Pt} :
    ∀ (k : Nat) (xs : List Pt) {idx : Nat},
      SortedSetPt.binarySearchAux target k xs = .ok idx →
      k ≤ idx ∧ ∃ pt ∈ xs, xs[idx - k]? = some pt ∧ pt.x = target.x
  | k, [], idx, h => by
    simp [SortedSetPt.binarySearchAux] at h
  | k, pt :: rest, idx, h => by
    unfold SortedSetPt.binarySearchAux at h
    split at h
    · obtain ⟨hle, foundPt, hmem, hget, hx⟩ := binarySearchAux_ok (k + 1) rest h
      refine ⟨by omega, foundPt, List.mem_cons_of_mem pt hmem, ?_, hx⟩
      have hsub : idx - k = (idx - (k + 1)) + 1 := by omega
      rw [hsub, List.getElem?_cons_succ]
      exact hget
    · rename_i hcmp
      cases h
      refine ⟨Nat.le_refl k, pt, List.mem_cons_self, by simp, ?_⟩
      exact (pt_cmp_eq_iff pt target).mp hcmp
    · cases h

/-! ## Byte packing and `decodedMessageLoop` -/

theorem u16ToBeBytes_pack (b0 b1 : BitVec 8) :
    u16ToBeBytes ((b0.zeroExtend 16 <<< 8) + b1.zeroExtend 16) = [b0, b1] := by
  have hb0 : b0.toNat < 256 := b0.isLt
  have hb1 : b1.toNat < 256 := b1.isLt
  unfold u16ToBeBytes
  congr 1
  · apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_add,
      BitVec.toNat_shiftLeft]
    omega
  · congr 1
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_shiftLeft]
    omega

theorem u16ToBeBytes_msgVal (msg : List (BitVec 8)) (i : Nat) (hi : 2 * i + 1 < msg.length) :
    u16ToBeBytes (msgVal msg i).value = [msg[2 * i]'(by omega), msg[2 * i + 1]'hi] := by
  have hi0 : 2 * i < msg.length := by omega
  unfold msgVal GF16.new
  simp only [List.getD, List.getElem?_eq_getElem hi0, List.getElem?_eq_getElem hi, Option.getD_some]
  exact u16ToBeBytes_pack _ _

theorem take_two_mul_succ (msg : List (BitVec 8)) (i : Nat) (hi : 2 * i + 1 < msg.length) :
    msg.take (2 * i) ++ [msg[2 * i]'(by omega), msg[2 * i + 1]'hi] = msg.take (2 * (i + 1)) := by
  have hi0 : 2 * i < msg.length := by omega
  have h1 : msg.take (2 * i + 1) = msg.take (2 * i) ++ [msg[2 * i]'hi0] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hi0, Option.toList_some]
  have h2 : msg.take (2 * i + 1 + 1) = msg.take (2 * i + 1) ++ [msg[2 * i + 1]'hi] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some]
  have h3 : 2 * (i + 1) = 2 * i + 1 + 1 := by omega
  rw [h3, h2, h1, List.append_assoc]
  rfl

def PolysInv (msg : List (BitVec 8)) (polys : List (Option Poly)) : Prop :=
  polys.length = 16 ∧
    ∀ j (hj : j < polys.length) (p : Poly),
      polys[j]'hj = some p → polyOf p.coefficients = msgPoly msg j

theorem polysInv_init (msg : List (BitVec 8)) :
    PolysInv msg (List.replicate 16 none) := by
  refine ⟨by simp, fun j hj p hp => ?_⟩
  rw [List.getElem_replicate] at hp
  cases hp

theorem polysInv_set {msg : List (BitVec 8)} {polys : List (Option Poly)}
    (hinv : PolysInv msg polys) {j : Nat} (hj : j < 16) {interp : Poly}
    (hinterp : polyOf interp.coefficients = msgPoly msg j) :
    PolysInv msg (polys.set j (some interp)) := by
  refine ⟨by simp [hinv.1], fun k hk p hp => ?_⟩
  by_cases hkj : k = j
  · subst hkj
    rw [List.getElem_set_self] at hp
    injection hp with hp'
    subst hp'
    exact hinterp
  · rw [List.getElem_set_ne (Ne.symm hkj)] at hp
    exact hinv.2 k (by rw [List.length_set] at hk; exact hk) p hp

theorem decodedMessageLoop_spec (msg : List (BitVec 8)) (S : Finset Nat) (dec : PolyDecoder)
    (hd : DecInv msg S dec) (heven : msg.length % 2 = 0) (hlen : msg.length ≤ 2 ^ 20)
    (hS : needed msg.length 0 ≤ S.card) (pointsVecs : List (List Pt))
    (hpv : ∀ j (hj : j < 16),
      pointsVecs[j]? =
        some ((dec.pts[j]'(by have := hd.len; omega)).vec.take (needed msg.length j))) :
    ∀ (i rem : Nat) (polys : List (Option Poly)),
      i + rem = msg.length / 2 →
      PolysInv msg polys →
      ∃ polys',
        PolyDecoder.decodedMessageLoop dec pointsVecs i rem polys (msg.take (2 * i)) =
          .ok (polys', msg.take (2 * (i + rem)))
  | i, 0, polys, _, _ => ⟨polys, by simp [PolyDecoder.decodedMessageLoop]⟩
  | i, rem + 1, polys, hsum, hpolys => by
    have hi_half : i < msg.length / 2 := by omega
    have hi_len : 2 * i + 1 < msg.length := by omega
    have hpoly_lt : i % 16 < 16 := Nat.mod_lt i (by decide)
    have hpoly_pts_lt : i % 16 < dec.pts.length := by have := hd.len; omega
    let pt : Pt := { x := GF16.new (BitVec.ofNat 16 (i / 16)), y := GF16.ZERO }
    have heval_msg : (msgPoly msg (i % 16)).eval (idxPt (i / 16)) = msgVal msg i :=
      eval_msgPoly_at_idxPt msg hlen i hi_half
    unfold PolyDecoder.decodedMessageLoop
    dsimp only [bind, Except.bind, Pure.pure, Except.pure]
    rw [List.getElem?_eq_getElem hpoly_pts_lt]
    dsimp only
    have hih_step : ∀ (polys' : List (Option Poly)),
        PolysInv msg polys' →
        ∃ polys'',
          PolyDecoder.decodedMessageLoop dec pointsVecs (i + 1) rem polys'
            (msg.take (2 * i) ++ u16ToBeBytes (msgVal msg i).value) =
            .ok (polys'', msg.take (2 * (i + (rem + 1)))) := by
      intro polys' hpolys'
      rw [u16ToBeBytes_msgVal msg i hi_len, take_two_mul_succ msg i hi_len]
      obtain ⟨polys'', hih_eq⟩ :=
        decodedMessageLoop_spec msg S dec hd heven hlen hS pointsVecs hpv
          (i + 1) rem polys' (by omega) hpolys'
      refine ⟨polys'', ?_⟩
      have hadd : i + 1 + rem = i + (rem + 1) := by omega
      rw [hadd] at hih_eq
      exact hih_eq
    cases hbs : (dec.pts[i % 16]'hpoly_pts_lt).binarySearch pt with
    | ok idx =>
      dsimp only
      obtain ⟨_, foundPt, hmem, hget, hx⟩ := binarySearchAux_ok 0 _ hbs
      simp only [Nat.sub_zero] at hget
      rw [hget]
      dsimp only
      have hy : foundPt.y = msgVal msg i := by
        rw [hd.onPoly (i % 16) hpoly_pts_lt foundPt hmem, hx]
        exact heval_msg
      rw [hy]
      exact hih_step polys hpolys
    | error _ =>
      dsimp only
      have hpoly_polys_lt : i % 16 < polys.length := by rw [hpolys.1]; exact hpoly_lt
      rw [List.getElem?_eq_getElem hpoly_polys_lt]
      dsimp only
      cases hopt : polys[i % 16]'hpoly_polys_lt with
      | some p =>
        dsimp only
        rw [computeAt_spec p _, hpolys.2 (i % 16) hpoly_polys_lt p hopt]
        dsimp only
        rw [show GF16.new (BitVec.ofNat 16 (i / 16)) = idxPt (i / 16) from rfl, heval_msg]
        exact hih_step polys hpolys
      | none =>
        dsimp only
        rw [hpv (i % 16) hpoly_lt]
        dsimp only
        obtain ⟨interp, hinterp_ok, hinterp_poly⟩ :=
          lagrangeInterpolate_ptsSlice_spec msg S dec hd hlen hS (i % 16) hpoly_lt
        rw [hinterp_ok]
        dsimp only
        have hpoly_set_lt : i % 16 < (polys.set (i % 16) (some interp)).length := by
          rw [List.length_set]; exact hpoly_polys_lt
        rw [List.getElem?_eq_getElem hpoly_set_lt, List.getElem_set_self]
        dsimp only
        rw [computeAt_spec interp _, hinterp_poly]
        dsimp only
        rw [show GF16.new (BitVec.ofNat 16 (i / 16)) = idxPt (i / 16) from rfl, heval_msg]
        exact hih_step (polys.set (i % 16) (some interp))
          (polysInv_set hpolys hpoly_lt hinterp_poly)

theorem decodedMessage_spec_aux (msg : List (BitVec 8)) (S : Finset Nat) (dec : PolyDecoder)
    (hd : DecInv msg S dec) (heven : msg.length % 2 = 0) (hlen : msg.length ≤ 2 ^ 20)
    (hS : needed msg.length 0 ≤ S.card) :
    dec.decodedMessage = .ok (some msg) := by
  have hpts_len : dec.pts.length = 16 := hd.len
  have hnec_all : ∀ j (hj : j < dec.pts.length), dec.necessaryPoints j ≤ (dec.pts[j]).len := by
    intro j hj
    rw [necessaryPoints_eq dec msg.length hd.ptsNeeded j, SortedSetPt.len]
    have hnS : needed msg.length j ≤ S.card :=
      Nat.le_trans (needed_le_needed_zero msg.length j) hS
    have hen := hd.enough j hj
    rwa [Nat.min_eq_right hnS] at hen
  obtain ⟨pointsVecs, hcollect, hpv_len, hpv⟩ :=
    collectPointsVecs_spec dec hnec_all 0 dec.pts.length [] (by omega) rfl (fun _ hj => by omega)
  have hpv16 : ∀ j (hj : j < 16),
      pointsVecs[j]? = some ((dec.pts[j]'(by omega)).vec.take (needed msg.length j)) := by
    intro j hj
    rw [hpv j (by omega), necessaryPoints_eq dec msg.length hd.ptsNeeded j]
  have hmul : ¬ (dec.ptsNeeded * 2 > USIZE_MAX) := by
    rw [hd.ptsNeeded, USIZE_MAX]
    omega
  obtain ⟨polys', hloop⟩ :=
    decodedMessageLoop_spec msg S dec hd heven hlen hS pointsVecs hpv16
      0 (msg.length / 2) (List.replicate 16 none) (by omega) (polysInv_init msg)
  unfold PolyDecoder.decodedMessage
  rw [hd.notComplete, hcollect]
  dsimp only [bind, Except.bind, Pure.pure, Except.pure]
  rw [ite_eq_right_iff.mpr (fun h => nomatch h),
    ite_eq_right_iff.mpr (fun h => absurd h hmul), hd.ptsNeeded]
  have htake0 : msg.take (2 * 0) = [] := by simp
  have htake_all : msg.take (2 * (0 + msg.length / 2)) = msg := by
    have h2 : 2 * (0 + msg.length / 2) = msg.length := by omega
    rw [h2, List.take_length]
  rw [htake0, htake_all] at hloop
  rw [hloop]
  rfl

end CryptoVerification.SpqrV1Sync.Erasure.DecodedMessage
