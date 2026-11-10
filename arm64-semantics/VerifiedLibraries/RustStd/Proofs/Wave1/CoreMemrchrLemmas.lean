/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Spec

public import ProofLib

/-!
# Pure and SWAR Lemmas for `core::slice::memchr::memrchr`

Defines `memrchrLastIdx` and `NoMatchFrom` and proves the 16-byte GPR SWAR needle-detection
equivalence (`memrchrSwarBics_eq_zero_iff`), alignment and bounds-check lemmas, and 16-byte slice
focus (`pointsToBytes_focus16_words`) used to verify `core::slice::memchr::memrchr`.
-/

@[expose] public section

set_option autoImplicit false

namespace VerifiedLibraries.RustStd

open Arm64 ProofLib

/-- Largest index `i < bs.length` satisfying `bs[i]? = some c`, or `none` if `c` does not occur in `bs`. -/
def memrchrLastIdx (c : BitVec 8) (bs : List (BitVec 8)) : Option Nat :=
  ((List.range bs.length).filter fun i => bs[i]? == some c).getLast?

/-- Needle `c` does not appear at any index `j` with `lo ≤ j < bs.length`. -/
def NoMatchFrom (c : BitVec 8) (bs : List (BitVec 8)) (lo : Nat) : Prop :=
  ∀ j, lo ≤ j → j < bs.length → bs[j]? ≠ some c

theorem noMatchFrom_self (c : BitVec 8) (bs : List (BitVec 8)) :
    NoMatchFrom c bs bs.length := by
  intro j hge hlt
  omega

theorem noMatchFrom_mono {c : BitVec 8} {bs : List (BitVec 8)} {lo1 lo2 : Nat}
    (hle : lo1 ≤ lo2) (h : NoMatchFrom c bs lo1) : NoMatchFrom c bs lo2 := by
  intro j hge hlt
  exact h j (by omega) hlt

theorem getElem?_eq_some_getD_zero {bs : List (BitVec 8)} {idx : Nat} (h : idx < bs.length) :
    bs[idx]? = some (bs.getD idx 0#8) := by
  simp [List.getD, h]

theorem noMatchFrom_step_one {c : BitVec 8} {bs : List (BitVec 8)} {idx : Nat}
    (hidx : idx < bs.length) (hne : bs.getD idx 0#8 ≠ c)
    (hprev : NoMatchFrom c bs (idx + 1)) :
    NoMatchFrom c bs idx := by
  intro j hge hlt
  by_cases hj : j = idx
  · subst hj
    rw [getElem?_eq_some_getD_zero hidx]
    exact fun h => hne (Option.some.inj h)
  · exact hprev j (by omega) hlt

theorem noMatchFrom_step_one_sub {c : BitVec 8} {bs : List (BitVec 8)} {k : Nat}
    (hk : k < bs.length) (hne : bs.getD (bs.length - 1 - k) 0#8 ≠ c)
    (hprev : NoMatchFrom c bs (bs.length - k)) :
    NoMatchFrom c bs (bs.length - (k + 1)) := by
  have heq1 : bs.length - (k + 1) = bs.length - 1 - k := by omega
  have heq2 : bs.length - 1 - k + 1 = bs.length - k := by omega
  rw [heq1]
  exact noMatchFrom_step_one (by omega) hne (heq2.symm ▸ hprev)

theorem noMatchFrom_step_chunk16 {c : BitVec 8} {bs : List (BitVec 8)} {cur : Nat}
    {w0 w1 : BitVec 64}
    (h16 : 16 ≤ cur) (_hcur : cur ≤ bs.length)
    (hchunk : (bs.drop (cur - 16)).take 16 = unpack64 w0 ++ unpack64 w1)
    (hw0 : ∀ b ∈ unpack64 w0, b ≠ c) (hw1 : ∀ b ∈ unpack64 w1, b ≠ c)
    (hprev : NoMatchFrom c bs cur) :
    NoMatchFrom c bs (cur - 16) := by
  intro j hge hlt
  by_cases hj : cur ≤ j
  · exact hprev j hj hlt
  · intro hjeq
    have hsub : ((bs.drop (cur - 16)).take 16)[j - (cur - 16)]? = some c := by
      rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop,
        show cur - 16 + (j - (cur - 16)) = j by omega]
      exact hjeq
    have hmem : c ∈ (bs.drop (cur - 16)).take 16 := List.mem_of_getElem? hsub
    rw [hchunk, List.mem_append] at hmem
    rcases hmem with hm0 | hm1
    · exact hw0 c hm0 rfl
    · exact hw1 c hm1 rfl

theorem memrchrLastIdx_eq_none {c : BitVec 8} {bs : List (BitVec 8)}
    (h : NoMatchFrom c bs 0) :
    memrchrLastIdx c bs = none := by
  unfold memrchrLastIdx
  suffices hnil : ((List.range bs.length).filter fun i => bs[i]? == some c) = [] by
    simp [hnil]
  rw [List.filter_eq_nil_iff]
  intro i hi
  simp only [List.mem_range] at hi
  have hne := h i (Nat.zero_le i) hi
  simp [hne]

theorem memrchrLastIdx_eq_some_of_hit {c : BitVec 8} {bs : List (BitVec 8)} {idx : Nat}
    (hidx : idx < bs.length) (hhit : bs.getD idx 0#8 = c)
    (habove : NoMatchFrom c bs (idx + 1)) :
    memrchrLastIdx c bs = some idx := by
  unfold memrchrLastIdx
  have hlen : bs.length = (idx + 1) + (bs.length - (idx + 1)) := by omega
  have hget : bs[idx]? = some c := by
    rw [getElem?_eq_some_getD_zero hidx, hhit]
  have htail :
      List.filter (fun i => bs[i]? == some c)
        ((List.range (bs.length - (idx + 1))).map ((idx + 1) + ·)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro m hm
    simp only [List.mem_map, List.mem_range] at hm
    rcases hm with ⟨d, hd, rfl⟩
    have hne := habove (idx + 1 + d) (by omega) (by omega)
    simp [hne]
  rw [hlen, List.range_add, List.range_succ, List.filter_append, List.filter_append, htail]
  simp [hget]

theorem memrchrLastIdx_eq_none_iff {c : BitVec 8} {bs : List (BitVec 8)} :
    memrchrLastIdx c bs = none ↔ NoMatchFrom c bs 0 := by
  constructor
  · intro hnone j _ hj
    unfold memrchrLastIdx at hnone
    rw [List.getLast?_eq_none_iff, List.filter_eq_nil_iff] at hnone
    have hj' := hnone j (List.mem_range.mpr hj)
    simpa using hj'
  · exact memrchrLastIdx_eq_none

private theorem getLast?_mem_of_some : ∀ {α : Type} {xs : List α} {a : α},
    xs.getLast? = some a → a ∈ xs
  | _, [], _, h => by simp at h
  | _, [x], a, h => by
    simp only [List.getLast?_singleton, Option.some.injEq] at h
    subst h
    exact List.mem_singleton.mpr rfl
  | _, _ :: y :: rest, a, h =>
    List.mem_cons_of_mem _ (getLast?_mem_of_some (xs := y :: rest) (by simpa using h))

private theorem getLast?_append_cons {α : Type} : ∀ (xs : List α) (y : α) (ys : List α),
    (xs ++ y :: ys).getLast? = (y :: ys).getLast?
  | [], _, _ => rfl
  | [_], _, _ => rfl
  | _ :: x2 :: rest, y, ys => getLast?_append_cons (x2 :: rest) y ys

theorem memrchrLastIdx_eq_some_iff {c : BitVec 8} {bs : List (BitVec 8)} {idx : Nat} :
    memrchrLastIdx c bs = some idx ↔
      idx < bs.length ∧ bs[idx]? = some c ∧ NoMatchFrom c bs (idx + 1) := by
  constructor
  · intro hsome
    unfold memrchrLastIdx at hsome
    have hmem : idx ∈ (List.range bs.length).filter (fun i => bs[i]? == some c) :=
      getLast?_mem_of_some hsome
    rw [List.mem_filter, List.mem_range, beq_iff_eq] at hmem
    refine ⟨hmem.1, hmem.2, fun j hj1 hj2 hjc => ?_⟩
    have hlen : bs.length = (j + 1) + (bs.length - (j + 1)) := by omega
    let tailRest := ((List.range (bs.length - (j + 1))).map ((j + 1) + ·)).filter
      (fun i => bs[i]? == some c)
    have hsplit :
        (List.range bs.length).filter (fun i => bs[i]? == some c) =
          (List.range j).filter (fun i => bs[i]? == some c) ++ (j :: tailRest) := by
      dsimp [tailRest]
      rw [hlen, List.range_add, List.range_succ, List.filter_append, List.filter_append]
      simp [hjc, List.append_assoc]
    rw [hsplit, getLast?_append_cons] at hsome
    have hmem_tail : idx ∈ (j :: tailRest) := getLast?_mem_of_some hsome
    simp only [tailRest, List.mem_cons, List.mem_filter,
      List.mem_map, List.mem_range] at hmem_tail
    rcases hmem_tail with rfl | ⟨⟨d, _, rfl⟩, _⟩ <;> omega
  · rintro ⟨hidx, hget, habove⟩
    have hhit : bs.getD idx 0#8 = c := by
      rw [getElem?_eq_some_getD_zero hidx] at hget
      exact Option.some.inj hget
    exact memrchrLastIdx_eq_some_of_hit hidx hhit habove

abbrev memrchrRepeatByte64 (c : BitVec 8) : BitVec 64 :=
  c.zeroExtend 64 * 72340172838076673#64

theorem memrchrRepeatByte64_eq_append (c : BitVec 8) :
    memrchrRepeatByte64 c = c ++ c ++ c ++ c ++ c ++ c ++ c ++ c := by
  decide +revert

theorem movk_swar_const :
    (72340172838076673#64 &&& 0xffff_ffff_ffff_0000#64) ||| 256#64 = 72340172838076672#64 := by
  decide

theorem lowByte_mov_and_ff (x0 : BitVec 64) :
    BitVec.zeroExtend 64 (BitVec.setWidth 32 (BitVec.zeroExtend 64 (BitVec.setWidth 32 x0)) &&& 255#32) =
      (x0.setWidth 8).zeroExtend 64 := by
  bv_slice

theorem byte_zext32_beq (b c : BitVec 8) :
    (b.zeroExtend 32 == c.zeroExtend 32) = (b == c) := by
  bv_slice

theorem byte_zext64_beq (b c : BitVec 8) :
    (b.zeroExtend 64 == c.zeroExtend 64) = (b == c) := by
  bv_slice

theorem byte_setWidth32_zext64_beq (b c : BitVec 8) :
    (BitVec.setWidth 32 (b.zeroExtend 64) == BitVec.setWidth 32 (c.zeroExtend 64)) = (b == c) := by
  bv_slice

private theorem swar_word_high_bits_iff (u : BitVec 64) :
    ((72340172838076672#64 - u) ||| u) &&& 9259542123273814144#64 = 9259542123273814144#64 ↔
      (u.extractLsb' 0 8 ≠ 0#8 ∧ u.extractLsb' 8 8 ≠ 0#8 ∧
       u.extractLsb' 16 8 ≠ 0#8 ∧ u.extractLsb' 24 8 ≠ 0#8 ∧
       u.extractLsb' 32 8 ≠ 0#8 ∧ u.extractLsb' 40 8 ≠ 0#8 ∧
       u.extractLsb' 48 8 ≠ 0#8 ∧ u.extractLsb' 56 8 ≠ 0#8) := by
  bv_robdd

private theorem repeatByte64_extract (c : BitVec 8) :
    let r := memrchrRepeatByte64 c
    r.extractLsb' 0 8 = c ∧ r.extractLsb' 8 8 = c ∧
    r.extractLsb' 16 8 = c ∧ r.extractLsb' 24 8 = c ∧
    r.extractLsb' 32 8 = c ∧ r.extractLsb' 40 8 = c ∧
    r.extractLsb' 48 8 = c ∧ r.extractLsb' 56 8 = c := by
  decide +revert

private theorem byte_xor_ne_zero_iff (b c : BitVec 8) :
    (b ^^^ c ≠ 0#8) ↔ b ≠ c := by
  bv_slice

private theorem xor_repeatByte_lanes_ne_zero_iff (w : BitVec 64) (c : BitVec 8) :
    (let u := w ^^^ memrchrRepeatByte64 c
     u.extractLsb' 0 8 ≠ 0#8 ∧ u.extractLsb' 8 8 ≠ 0#8 ∧
     u.extractLsb' 16 8 ≠ 0#8 ∧ u.extractLsb' 24 8 ≠ 0#8 ∧
     u.extractLsb' 32 8 ≠ 0#8 ∧ u.extractLsb' 40 8 ≠ 0#8 ∧
     u.extractLsb' 48 8 ≠ 0#8 ∧ u.extractLsb' 56 8 ≠ 0#8) ↔
    (∀ b ∈ unpack64 w, b ≠ c) := by
  obtain ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7⟩ := repeatByte64_extract c
  simp only [unpack64, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    BitVec.extractLsb'_xor, hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, byte_xor_ne_zero_iff]

private theorem bics_pair_high_bits_iff (a b : BitVec 64) :
    9259542123273814144#64 &&& ~~~(a &&& b) = 0#64 ↔
      (a &&& 9259542123273814144#64 = 9259542123273814144#64 ∧
       b &&& 9259542123273814144#64 = 9259542123273814144#64) := by
  bv_slice

theorem memrchrSwarBics_eq_zero_iff (w0 w1 : BitVec 64) (c : BitVec 8) :
    (let rep := memrchrRepeatByte64 c
     let u0 := w0 ^^^ rep
     let u1 := w1 ^^^ rep
     9259542123273814144#64 &&&
       ~~~(((72340172838076672#64 - u0) ||| u0) &&& ((72340172838076672#64 - u1) ||| u1)) = 0#64) ↔
      (∀ b ∈ unpack64 w0, b ≠ c) ∧ (∀ b ∈ unpack64 w1, b ≠ c) := by
  dsimp only
  rw [bics_pair_high_bits_iff, swar_word_high_bits_iff, swar_word_high_bits_iff,
    xor_repeatByte_lanes_ne_zero_iff, xor_repeatByte_lanes_ne_zero_iff]

abbrev memrchrAlign8 (p : BitVec 64) : BitVec 64 :=
  (p + 7#64) &&& 0xffff_ffff_ffff_fff8#64

abbrev memrchrHeadBV (p : BitVec 64) : BitVec 64 :=
  memrchrAlign8 p - p

theorem memrchrHeadBV_lt8 (p : BitVec 64) : (memrchrHeadBV p).toNat < 8 := by
  have h : (memrchrHeadBV p).ult 8#64 = true := by
    dsimp [memrchrHeadBV, memrchrAlign8]
    bv_robdd
  simpa [BitVec.ult] using h

theorem memrchrHeadBV_eq_ofNat (p : BitVec 64) :
    memrchrHeadBV p = BitVec.ofNat 64 (memrchrHeadBV p).toNat := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ofNat]

theorem sub32_zext64_and15_eq (a b : BitVec 64) :
    BitVec.zeroExtend 64 (a.setWidth 32 - b.setWidth 32) &&& 15#64 = (a - b) &&& 15#64 := by
  apply BitVec.eq_of_toNat_eq
  have h15 : (15#64).toNat = 15 := rfl
  rw [BitVec.toNat_and, BitVec.toNat_and, h15,
    Nat.and_two_pow_sub_one_eq_mod _ 4, Nat.and_two_pow_sub_one_eq_mod _ 4]
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub]
  omega

theorem ofNat_sub_and15_eq_mod16 {n head : Nat} (hle : head ≤ n) (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n - BitVec.ofNat 64 head) &&& 15#64 = BitVec.ofNat 64 ((n - head) % 16) := by
  have hsub : BitVec.ofNat 64 n - BitVec.ofNat 64 head = BitVec.ofNat 64 (n - head) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  rw [hsub]
  apply BitVec.eq_of_toNat_eq
  have hand : (BitVec.ofNat 64 (n - head) &&& 15#64).toNat = (n - head) % 16 := by
    rw [BitVec.toNat_and, BitVec.toNat_ofNat]
    have h15 : (15#64).toNat = 15 := rfl
    rw [h15, Nat.and_two_pow_sub_one_eq_mod _ 4]
    have hmod : (n - head) % 2 ^ 64 = n - head := Nat.mod_eq_of_lt (by omega)
    rw [hmod]
  simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show (n - head) % 16 < 2 ^ 64 by omega)] using hand

theorem memrchr_split_of_ge {n head : Nat} (hle : head ≤ n) (hn : n < 2 ^ 64) :
    let tailLen := (n - head) % 16
    let mid := n - tailLen
    let q := (n - head) / 16
    tailLen ≤ n ∧
      (BitVec.ofNat 64 n).ult (BitVec.ofNat 64 tailLen) = false ∧
      BitVec.ofNat 64 n - BitVec.ofNat 64 tailLen = BitVec.ofNat 64 mid ∧
      mid = head + 16 * q ∧
      mid ≤ n := by
  dsimp only
  have htl : (n - head) % 16 ≤ n - head := Nat.mod_le _ _
  refine ⟨by omega, ?_, ?_, by omega, by omega⟩
  · simp [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
      Nat.mod_eq_of_lt (show (n - head) % 16 < 2 ^ 64 by omega)]
    omega
  · apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega

theorem memrchr_prefix_check_false {cur n : Nat} (hcur : cur ≤ n) (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n).ult (BitVec.ofNat 64 cur) = false ∧
      (BitVec.ofNat 64 cur).ule (BitVec.ofNat 64 n) = true := by
  simp [BitVec.ult, BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (show cur < 2 ^ 64 by omega)]
  omega

theorem memrchr_loop1_ptr_eq (p : BitVec 64) {n k : Nat} (hk : k < n) (_hn : n < 2 ^ 64) :
    (p + BitVec.ofNat 64 n - 1#64) - BitVec.ofNat 64 k =
      p + BitVec.ofNat 64 (n - 1 - k) := by
  have := _hn
  have h1 : BitVec.ofNat 64 n - 1#64 - BitVec.ofNat 64 k = BitVec.ofNat 64 (n - 1 - k) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  calc
    (p + BitVec.ofNat 64 n - 1#64) - BitVec.ofNat 64 k
      = p + (BitVec.ofNat 64 n - 1#64 - BitVec.ofNat 64 k) := by bv_lin
    _ = p + BitVec.ofNat 64 (n - 1 - k) := by rw [h1]

theorem memrchr_loop1_hit_idx {n k : Nat} (hk : k < n) (_hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n - BitVec.ofNat 64 (k + 1) = BitVec.ofNat 64 (n - 1 - k) := by
  have := _hn
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem memrchr_loop2_ptr_eq (p : BitVec 64) {cur : Nat} (h16 : 16 ≤ cur) (hcur : cur < 2 ^ 64) :
    (p + BitVec.ofNat 64 cur) - 16#64 = p + BitVec.ofNat 64 (cur - 16) ∧
      BitVec.ofNat 64 cur - 16#64 = BitVec.ofNat 64 (cur - 16) := by
  have hsub : BitVec.ofNat 64 cur - 16#64 = BitVec.ofNat 64 (cur - 16) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  refine ⟨?_, hsub⟩
  calc
    (p + BitVec.ofNat 64 cur) - 16#64
      = p + (BitVec.ofNat 64 cur - 16#64) := by bv_lin
    _ = p + BitVec.ofNat 64 (cur - 16) := by rw [hsub]

theorem memrchr_loop3_ptr_eq (p : BitVec 64) (idx : Nat) :
    (p - 1#64) + BitVec.ofNat 64 (idx + 1) = p + BitVec.ofNat 64 idx ∧
      BitVec.ofNat 64 (idx + 1) - 1#64 = BitVec.ofNat 64 idx := by
  rw [BitVec.ofNat_add]
  exact ⟨by bv_lin, by bv_lin⟩

theorem pointsToBytes_focus16_words (p : BitVec 64) (bs : List (BitVec 8)) {cur : Nat}
    (h16 : 16 ≤ cur) (hcur : cur ≤ bs.length) :
    ∃ w0 w1 : BitVec 64,
      (bs.drop (cur - 16)).take 16 = unpack64 w0 ++ unpack64 w1 ∧
      (p ↦ₛ bs) =
        ((p + BitVec.ofNat 64 (cur - 16)) ↦₆₄ w0) ∗
        (((p + BitVec.ofNat 64 (cur - 16)) + 8#64) ↦₆₄ w1) ∗
        ((p ↦ₛ bs.take (cur - 16)) ∗
         ((p + BitVec.ofNat 64 cur) ↦ₛ bs.drop cur)) := by
  have hlen16 : ((bs.drop (cur - 16)).take 16).length = 16 := by simp; omega
  obtain ⟨w0, w1, hchunk, hpair⟩ := exists_unpack64_of_length_16 hlen16
  refine ⟨w0, w1, hchunk, ?_⟩
  have hsplit := pointsToBytes_split3 p bs (cur - 16) 16 (by omega)
  have hcur_eq : cur - 16 + 16 = cur := by omega
  rw [hcur_eq] at hsplit
  rw [hsplit, hpair (p + BitVec.ofNat 64 (cur - 16))]
  ac_rfl

end VerifiedLibraries.RustStd
