/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.Stack
public import ProofLib.SepLogic.Fresh
public import ProofLib.BV.Arith
public import ProofLib.BV.Bits
import ProofLib.SepLogic.Model

/-!
# Byte-Slice Separation Logic

Separation-logic algebra for byte slices (`↦ₛ` and `↦ᵣ`), little-endian and big-endian word
pack/unpack conversions, subslice focus/update lemmas, and `Memory.writeBytes` / `Memory.readBytes`
frame bridges.
-/

@[expose] public section

namespace ProofLib

open Arm64

/-! ## Core `pointsToBytes` and `memRegion` Bridges -/

theorem pointsToBytes_append (a : BitVec 64) (xs ys : List (BitVec 8)) :
    (a ↦ₛ (xs ++ ys)) = (a ↦ₛ xs) ∗ ((a + BitVec.ofNat 64 xs.length) ↦ₛ ys) := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
    rw [List.cons_append, pointsToBytes_cons, pointsToBytes_cons, ih, sepConj_assoc]
    have e : a + 1#64 + BitVec.ofNat 64 xs.length = a + BitVec.ofNat 64 (x :: xs).length := by
      simp only [List.length_cons]; bv_arith
    rw [e]

theorem pointsToBytesRO_append (a : BitVec 64) (xs ys : List (BitVec 8)) :
    (a ↦ᵣ (xs ++ ys)) = (a ↦ᵣ xs) ∗ ((a + BitVec.ofNat 64 xs.length) ↦ᵣ ys) := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
    rw [List.cons_append, pointsToBytesRO_cons, pointsToBytesRO_cons, ih, sepConj_assoc]
    have e : a + 1#64 + BitVec.ofNat 64 xs.length = a + BitVec.ofNat 64 (x :: xs).length := by
      simp only [List.length_cons]; bv_arith
    rw [e]

theorem pointsToBytes_entails_memRegion (a : BitVec 64) (bs : List (BitVec 8)) :
    (a ↦ₛ bs) ⊢ memRegion a bs.length :=
  IsBlock.entails (IsBlock.pointsToBytes a bs) (IsBlock.memRegion a _) fun _ _ => trivial

theorem memRegion_eq_exists_bytes (a : BitVec 64) (n : Nat) (h : n ≤ 2 ^ 64) :
    memRegion a n = ∃∗ bs, ⌜bs.length = n⌝ ∗ (a ↦ₛ bs) :=
  IsBlock.eq (IsBlock.memRegion a n)
    (IsBlock.sepExists fun bs =>
      IsBlock.pure_sepConj fun e => IsBlock.pointsToBytes_len (a := a) (bs := bs) e)
    fun m => ⟨fun _ => ⟨m.readBytes a n, Memory.readBytes_length m a n,
        by rw [Memory.readBytes_length]; exact h, by rw [Memory.readBytes_length]⟩,
      fun _ => trivial⟩

@[simp]
theorem pointsToBytes_singleton (a : BitVec 64) (b : BitVec 8) :
    (a ↦ₛ [b]) = (a ↦₈ b) := by
  rw [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]

@[simp]
theorem pointsToBytesRO_singleton (a : BitVec 64) (b : BitVec 8) :
    (a ↦ᵣ [b]) = (a ↦₈ᵣ b) := by
  rw [pointsToBytesRO_cons, pointsToBytesRO_nil, sepConj_emp]

theorem pointsToBytes_snoc (a : BitVec 64) (xs : List (BitVec 8)) (x : BitVec 8) :
    (a ↦ₛ (xs ++ [x])) = (a ↦ₛ xs) ∗ ((a + BitVec.ofNat 64 xs.length) ↦₈ x) := by
  rw [pointsToBytes_append, pointsToBytes_singleton]



theorem pointsToBytes_take_drop (ptr : BitVec 64) (n : Nat) (bs : List (BitVec 8))
    (hn : n ≤ bs.length) :
    (ptr ↦ₛ bs) = (ptr ↦ₛ bs.take n) ∗ ((ptr + BitVec.ofNat 64 n) ↦ₛ bs.drop n) := by
  have h := pointsToBytes_append ptr (bs.take n) (bs.drop n)
  rw [List.take_append_drop, List.length_take_of_le hn] at h
  exact h

theorem pointsToBytes_cons_off (p : BitVec 64) (k : Nat) (x : BitVec 8) (xs : List (BitVec 8)) :
    ((p + BitVec.ofNat 64 k) ↦ₛ (x :: xs)) =
      (((p + BitVec.ofNat 64 k) ↦₈ x) ∗ ((p + BitVec.ofNat 64 (k + 1)) ↦ₛ xs)) := by
  rw [pointsToBytes_cons]
  have h : (p + BitVec.ofNat 64 k) + 1#64 = p + BitVec.ofNat 64 (k + 1) := by
    rw [BitVec.add_assoc]; congr 1
    change BitVec.ofNat 64 k + BitVec.ofNat 64 1 = BitVec.ofNat 64 (k + 1)
    rw [← BitVec.ofNat_add]
  rw [h]

theorem pointsToBytes_append_off (p : BitVec 64) (k m : Nat)
    (xs ys : List (BitVec 8)) (h : k + xs.length = m) :
    ((p + BitVec.ofNat 64 k) ↦ₛ (xs ++ ys)) =
      (((p + BitVec.ofNat 64 k) ↦ₛ xs) ∗ ((p + BitVec.ofNat 64 m) ↦ₛ ys)) := by
  subst h
  rw [pointsToBytes_append, BitVec.add_assoc, ← BitVec.ofNat_add]

/-- Split the last byte off a non-empty byte slice `ptr ↦ₛ xs`. -/
theorem pointsToBytes_split_last (ptr : BitVec 64) (xs : List (BitVec 8)) (hne : xs ≠ []) :
    (ptr ↦ₛ xs) =
      (ptr ↦ₛ xs.dropLast) ∗
      ((ptr + BitVec.ofNat 64 xs.length - 1#64) ↦₈ xs.getLast hne) := by
  conv => lhs; rw [← List.dropLast_concat_getLast hne]
  rw [pointsToBytes_snoc]
  have hlen : xs.dropLast.length + 1 = xs.length := by
    rw [List.length_dropLast]
    have := List.length_pos_iff.mpr hne
    omega
  have hbv : ptr + BitVec.ofNat 64 xs.dropLast.length =
      ptr + BitVec.ofNat 64 xs.length - 1#64 := by
    rw [← hlen, BitVec.ofNat_add]
    bv_lin
  rw [hbv]

/-- A byte slice `p ↦ₛ bs` followed by `memRegion (p + bs.length) (n - bs.length)` entails `memRegion p n`. -/
theorem pointsToBytes_memRegion_entails (p : BitVec 64) (bs : List (BitVec 8)) (n : Nat)
    (hbn : bs.length ≤ n) (hn : n ≤ 2 ^ 64) :
    (p ↦ₛ bs) ∗ memRegion (p + BitVec.ofNat 64 bs.length) (n - bs.length) ⊢ memRegion p n := by
  have heq : n = bs.length + (n - bs.length) := by omega
  conv => rhs; rw [heq, memRegion_split p bs.length (n - bs.length) (by omega)]
  exact sepConj_mono (pointsToBytes_entails_memRegion p bs) (Entails.refl _)

/-- A `2^64`-byte `pointsToBytes` covers the whole address space, so it cannot be separated
    from any 8-byte cell. -/
theorem pointsToBytes_full_false {m : Memory} {a p v : BitVec 64}
    {bs : List (BitVec 8)} {R : SepProp}
    (hlen : bs.length = 2 ^ 64) (h : m ⊨ (a ↦ₛ bs) ∗ ((p ↦₆₄ v) ∗ R)) : False := by
  have hd := IsBlock.disjoint (IsBlock.pointsToBytes a bs) (IsBlock.pointsTo64 p v)
    (by omega) (by decide) h
  unfold DisjointRegions at hd
  have := (p - a).isLt
  omega

/-! ## Little-Endian Word-Unpack Bridges -/

/-- Unpack a 64-bit word into its 8 little-endian bytes. -/
def unpack64 (v : BitVec 64) : List (BitVec 8) :=
  [v.extractLsb' 0 8, v.extractLsb' 8 8, v.extractLsb' 16 8, v.extractLsb' 24 8,
   v.extractLsb' 32 8, v.extractLsb' 40 8, v.extractLsb' 48 8, v.extractLsb' 56 8]

@[simp]
theorem unpack64_length (v : BitVec 64) : (unpack64 v).length = 8 := rfl

theorem pointsTo64_eq_pointsToBytes (a : BitVec 64) (v : BitVec 64) :
    (a ↦₆₄ v) = (a ↦ₛ unpack64 v) := by
  simp only [pointsTo64, unpack64, pointsToBytes_cons, pointsToBytes_nil, sepConj_emp,
    BitVec.add_zero]
  have h2 : a + 1#64 + 1#64 = a + 2#64 := by bv_arith
  have h3 : a + 2#64 + 1#64 = a + 3#64 := by bv_arith
  have h4 : a + 3#64 + 1#64 = a + 4#64 := by bv_arith
  have h5 : a + 4#64 + 1#64 = a + 5#64 := by bv_arith
  have h6 : a + 5#64 + 1#64 = a + 6#64 := by bv_arith
  have h7 : a + 6#64 + 1#64 = a + 7#64 := by bv_arith
  rw [h2, h3, h4, h5, h6, h7]



theorem pointsTo64RO_eq_pointsToBytesRO (a : BitVec 64) (v : BitVec 64) :
    (a ↦₆₄ᵣ v) = (a ↦ᵣ unpack64 v) := by
  simp only [pointsTo64RO, unpack64, pointsToBytesRO_cons, pointsToBytesRO_nil, sepConj_emp,
    BitVec.add_zero]
  have h2 : a + 1#64 + 1#64 = a + 2#64 := by bv_arith
  have h3 : a + 2#64 + 1#64 = a + 3#64 := by bv_arith
  have h4 : a + 3#64 + 1#64 = a + 4#64 := by bv_arith
  have h5 : a + 4#64 + 1#64 = a + 5#64 := by bv_arith
  have h6 : a + 5#64 + 1#64 = a + 6#64 := by bv_arith
  have h7 : a + 6#64 + 1#64 = a + 7#64 := by bv_arith
  rw [h2, h3, h4, h5, h6, h7]



private theorem extractLsb'_zero_append {n : Nat} (x : BitVec n) (b : BitVec 8) :
    (x ++ b).extractLsb' 0 8 = b := by
  ext i hi
  simp [BitVec.getElem_extractLsb', BitVec.getLsbD_append, hi]

private theorem extractLsb'_add_eight_append {n : Nat} (x : BitVec n) (b : BitVec 8) (k : Nat) :
    (x ++ b).extractLsb' (k + 8) 8 = x.extractLsb' k 8 := by
  ext i hi
  have hlt : ¬(k + 8 + i < 8) := by omega
  have hsub : k + 8 + i - 8 = k + i := by omega
  simp [BitVec.getElem_extractLsb', BitVec.getLsbD_append, hlt, hsub]

private theorem extractLsb'_8_append {n : Nat} (x : BitVec n) (b : BitVec 8) :
    (x ++ b).extractLsb' 8 8 = x.extractLsb' 0 8 :=
  extractLsb'_add_eight_append x b 0

private theorem extractLsb'_16_append {n : Nat} (x : BitVec n) (b : BitVec 8) :
    (x ++ b).extractLsb' 16 8 = x.extractLsb' 8 8 :=
  extractLsb'_add_eight_append x b 8

private theorem extractLsb'_24_append {n : Nat} (x : BitVec n) (b : BitVec 8) :
    (x ++ b).extractLsb' 24 8 = x.extractLsb' 16 8 :=
  extractLsb'_add_eight_append x b 16

private theorem extractLsb'_32_append {n : Nat} (x : BitVec n) (b : BitVec 8) :
    (x ++ b).extractLsb' 32 8 = x.extractLsb' 24 8 :=
  extractLsb'_add_eight_append x b 24

private theorem extractLsb'_40_append {n : Nat} (x : BitVec n) (b : BitVec 8) :
    (x ++ b).extractLsb' 40 8 = x.extractLsb' 32 8 :=
  extractLsb'_add_eight_append x b 32

private theorem extractLsb'_48_append {n : Nat} (x : BitVec n) (b : BitVec 8) :
    (x ++ b).extractLsb' 48 8 = x.extractLsb' 40 8 :=
  extractLsb'_add_eight_append x b 40

private theorem extractLsb'_56_append {n : Nat} (x : BitVec n) (b : BitVec 8) :
    (x ++ b).extractLsb' 56 8 = x.extractLsb' 48 8 :=
  extractLsb'_add_eight_append x b 48

private theorem extractLsb'_self_eight (b : BitVec 8) :
    b.extractLsb' 0 8 = b := by
  simp

theorem unpack64_pack64 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    unpack64 (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) =
      [b0, b1, b2, b3, b4, b5, b6, b7] := by
  simp only [unpack64, extractLsb'_56_append, extractLsb'_48_append, extractLsb'_40_append,
    extractLsb'_32_append, extractLsb'_24_append, extractLsb'_16_append, extractLsb'_8_append,
    extractLsb'_zero_append, extractLsb'_self_eight]

theorem pointsToBytes8_eq_pointsTo64 (a : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (a ↦ₛ [b0, b1, b2, b3, b4, b5, b6, b7]) =
      (a ↦₆₄ (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0)) := by
  rw [pointsTo64_eq_pointsToBytes, unpack64_pack64]

theorem pointsToBytesRO8_eq_pointsTo64RO (a : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (a ↦ᵣ [b0, b1, b2, b3, b4, b5, b6, b7]) =
      (a ↦₆₄ᵣ (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0)) := by
  rw [pointsTo64RO_eq_pointsToBytesRO, unpack64_pack64]

theorem exists_unpack64_of_length_8 {bs : List (BitVec 8)} (h : bs.length = 8) :
    ∃ v : BitVec 64, bs = unpack64 v := by
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    try (simp at h)
  exact ⟨b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0, (unpack64_pack64 b0 b1 b2 b3 b4 b5 b6 b7).symm⟩

theorem exists_unpack64_of_length_16 {bs : List (BitVec 8)} (h : bs.length = 16) :
    ∃ w0 w1 : BitVec 64,
      bs = unpack64 w0 ++ unpack64 w1 ∧
      ∀ a : BitVec 64, (a ↦ₛ bs) = ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1)) := by
  have h0 : (bs.take 8).length = 8 := by simp [h]
  have h1 : (bs.drop 8).length = 8 := by simp [h]
  obtain ⟨w0, hw0⟩ := exists_unpack64_of_length_8 h0
  obtain ⟨w1, hw1⟩ := exists_unpack64_of_length_8 h1
  have hbs : bs = unpack64 w0 ++ unpack64 w1 := by
    rw [← hw0, ← hw1, List.take_append_drop]
  refine ⟨w0, w1, hbs, fun a => ?_⟩
  rw [hbs, pointsToBytes_append, unpack64_length, ← pointsTo64_eq_pointsToBytes,
    ← pointsTo64_eq_pointsToBytes]

theorem exists_unpack64_of_length_32 {bs : List (BitVec 8)} (h : bs.length = 32) :
    ∃ w0 w1 w2 w3 : BitVec 64,
      bs = unpack64 w0 ++ unpack64 w1 ++ unpack64 w2 ++ unpack64 w3 ∧
      ∀ a : BitVec 64,
        (a ↦ₛ bs) =
          ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3)) := by
  have h0 : (bs.take 16).length = 16 := by simp [h]
  have h1 : (bs.drop 16).length = 16 := by simp [h]
  obtain ⟨w0, w1, hw01, hp01⟩ := exists_unpack64_of_length_16 h0
  obtain ⟨w2, w3, hw23, hp23⟩ := exists_unpack64_of_length_16 h1
  have hbs : bs = (unpack64 w0 ++ unpack64 w1) ++ (unpack64 w2 ++ unpack64 w3) := by
    rw [← hw01, ← hw23, List.take_append_drop]
  refine ⟨w0, w1, w2, w3, by simpa [List.append_assoc] using hbs, fun a => ?_⟩
  have hsplit : bs = bs.take 16 ++ bs.drop 16 := (List.take_append_drop 16 bs).symm
  rw [hsplit, pointsToBytes_append, h0, hp01, hp23]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]



/-- Unpack a 32-bit word into its 4 little-endian bytes. -/
def unpack32 (w : BitVec 32) : List (BitVec 8) :=
  [w.extractLsb' 0 8, w.extractLsb' 8 8, w.extractLsb' 16 8, w.extractLsb' 24 8]

@[simp]
theorem unpack32_length (w : BitVec 32) : (unpack32 w).length = 4 := rfl

theorem pointsTo32_eq_pointsToBytes (a : BitVec 64) (w : BitVec 32) :
    (a ↦₃₂ w) = (a ↦ₛ unpack32 w) := by
  simp only [pointsTo32, unpack32, pointsToBytes_cons, pointsToBytes_nil, sepConj_emp,
    BitVec.add_zero]
  have h2 : a + 1#64 + 1#64 = a + 2#64 := by bv_arith
  have h3 : a + 2#64 + 1#64 = a + 3#64 := by bv_arith
  rw [h2, h3]

theorem pointsTo32RO_eq_pointsToBytesRO (a : BitVec 64) (w : BitVec 32) :
    (a ↦₃₂ᵣ w) = (a ↦ᵣ unpack32 w) := by
  simp only [pointsTo32RO, unpack32, pointsToBytesRO_cons, pointsToBytesRO_nil, sepConj_emp,
    BitVec.add_zero]
  have h2 : a + 1#64 + 1#64 = a + 2#64 := by bv_arith
  have h3 : a + 2#64 + 1#64 = a + 3#64 := by bv_arith
  rw [h2, h3]

theorem unpack32_pack32 (b0 b1 b2 b3 : BitVec 8) :
    unpack32 (b3 ++ b2 ++ b1 ++ b0) = [b0, b1, b2, b3] := by
  simp only [unpack32, extractLsb'_24_append, extractLsb'_16_append, extractLsb'_8_append,
    extractLsb'_zero_append, extractLsb'_self_eight]

theorem pointsToBytes4_eq_pointsTo32 (a : BitVec 64) (b0 b1 b2 b3 : BitVec 8) :
    (a ↦ₛ [b0, b1, b2, b3]) = (a ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) := by
  rw [pointsTo32_eq_pointsToBytes, unpack32_pack32]

theorem pointsToBytesRO4_eq_pointsTo32RO (a : BitVec 64) (b0 b1 b2 b3 : BitVec 8) :
    (a ↦ᵣ [b0, b1, b2, b3]) = (a ↦₃₂ᵣ (b3 ++ b2 ++ b1 ++ b0)) := by
  rw [pointsTo32RO_eq_pointsToBytesRO, unpack32_pack32]

/-- Unpack a 16-bit halfword into its 2 little-endian bytes. -/
def unpack16 (w : BitVec 16) : List (BitVec 8) :=
  [w.extractLsb' 0 8, w.extractLsb' 8 8]

@[simp]
theorem unpack16_length (w : BitVec 16) : (unpack16 w).length = 2 := rfl

theorem pointsTo16_eq_pointsToBytes (a : BitVec 64) (w : BitVec 16) :
    (a ↦₁₆ w) = (a ↦ₛ unpack16 w) := by
  simp only [pointsTo16, unpack16, pointsToBytes_cons, pointsToBytes_nil, sepConj_emp,
    BitVec.add_zero]

theorem pointsTo16RO_eq_pointsToBytesRO (a : BitVec 64) (w : BitVec 16) :
    (a ↦₁₆ᵣ w) = (a ↦ᵣ unpack16 w) := by
  simp only [pointsTo16RO, unpack16, pointsToBytesRO_cons, pointsToBytesRO_nil, sepConj_emp,
    BitVec.add_zero]

theorem pointsToBytes2_eq_pointsTo16 (a : BitVec 64) (b0 b1 : BitVec 8) :
    (a ↦ₛ [b0, b1]) = (a ↦₁₆ (b1 ++ b0)) := by
  rw [pointsTo16_eq_pointsToBytes]
  congr 1
  simp only [unpack16, List.cons.injEq, and_true]
  exact ⟨by bv_bits, by bv_bits⟩

theorem pointsToBytesRO2_eq_pointsTo16RO (a : BitVec 64) (b0 b1 : BitVec 8) :
    (a ↦ᵣ [b0, b1]) = (a ↦₁₆ᵣ (b1 ++ b0)) := by
  rw [pointsTo16RO_eq_pointsToBytesRO]
  congr 1
  simp only [unpack16, List.cons.injEq, and_true]
  exact ⟨by bv_bits, by bv_bits⟩

theorem unpack64_append32 (lo hi : BitVec 32) :
    unpack64 (hi ++ lo) = unpack32 lo ++ unpack32 hi := by
  simp only [unpack64, unpack32, List.cons_append, List.nil_append, List.cons.injEq, and_true]
  refine ⟨by bv_bits, by bv_bits, by bv_bits, by bv_bits,
          by bv_bits, by bv_bits, by bv_bits, by bv_bits⟩

/-- Combine two adjacent 32-bit cells into one 64-bit cell. -/
theorem pointsTo32_pair (a : BitVec 64) (lo hi : BitVec 32) :
    ((a ↦₃₂ lo) ∗ ((a + 4#64) ↦₃₂ hi)) = (a ↦₆₄ (hi ++ lo)) := by
  rw [pointsTo32_eq_pointsToBytes, pointsTo32_eq_pointsToBytes, pointsTo64_eq_pointsToBytes,
      unpack64_append32, pointsToBytes_append, unpack32_length]


/-- Split a 64-bit points-to cell into two adjacent 32-bit points-to cells. -/
theorem pointsTo64_split32 (a v : BitVec 64) :
    (a ↦₆₄ v) = ((a ↦₃₂ v.extractLsb' 0 32) ∗ ((a + 4#64) ↦₃₂ v.extractLsb' 32 32)) := by
  rw [pointsTo32_pair]
  congr 1
  bv_bits


/-- Split a 64-bit points-to cell into two adjacent 32-bit cells using `v.truncate 32` for the low half. -/
theorem pointsTo64_split32' (a v : BitVec 64) :
    (a ↦₆₄ v) = ((a ↦₃₂ v.truncate 32) ∗ ((a + 4#64) ↦₃₂ v.extractLsb' 32 32)) := by
  rw [pointsTo32_pair]
  congr 1
  bv_bits

/-- Combine two adjacent 64-bit cells into one 128-bit cell. -/
theorem pointsTo64_pair (a : BitVec 64) (lo hi : BitVec 64) :
    ((a ↦₆₄ lo) ∗ ((a + 8#64) ↦₆₄ hi)) = (a ↦₁₂₈ (hi ++ lo)) :=
  ((IsBlock.pointsTo64 a lo).sepConj (IsBlock.pointsTo64 (a + 8#64) hi)
    (by bv_arith) (by decide)).eq (IsBlock.pointsTo128 a (hi ++ lo)) fun m => by
    simp only [Memory.read128]
    generalize m.read64 a = x
    generalize m.read64 (a + 8#64) = y
    bv_bits

/-- Split a 128-bit points-to cell into two adjacent 64-bit points-to cells. -/
theorem pointsTo128_split64 (a : BitVec 64) (v : BitVec 128) :
    (a ↦₁₂₈ v) = ((a ↦₆₄ v.extractLsb' 0 64) ∗ ((a + 8#64) ↦₆₄ v.extractLsb' 64 64)) := by
  rw [pointsTo64_pair]
  congr 1
  bv_bits

/-- Disjointness of a non-wrapping 64-bit cell and a non-empty `↦ₛ` byte slice. -/
theorem pointsTo64_outside_pointsToBytes {a v p : BitVec 64} {bs : List (BitVec 8)}
    (ha : a.toNat + 8 ≤ 2 ^ 64) (hn : 0 < bs.length) :
    ((a ↦₆₄ v) ∗ (p ↦ₛ bs)) ⊢
      ⌜a.toNat + 8 ≤ p.toNat ∨ p.toNat + bs.length ≤ a.toNat⌝ ∗ ((a ↦₆₄ v) ∗ (p ↦ₛ bs)) := by
  have h1 : ((a ↦₆₄ v) ∗ (p ↦ₛ bs)) ⊢ ((a ↦₆₄ v) ∗ (memRegion p bs.length ∗ emp)) := by
    rw [sepConj_emp]; exact sepConj_mono_right (pointsToBytes_entails_memRegion p bs)
  exact entails_pure_keep (Entails.trans h1 (ProofLib.Entails.pointsTo64_outside_memRegion ha hn))

abbrev Entails.pointsTo64_outside_pointsToBytes := @ProofLib.pointsTo64_outside_pointsToBytes

private theorem sub_add_four_eq_sub {sp off_lo off_hi : BitVec 64} (h : off_lo - 4#64 = off_hi) :
    sp - off_lo + 4#64 = sp - off_hi := by
  subst h
  bv_lin

private theorem add_add_four_eq_add {base off_lo off_hi : BitVec 64} (h : off_lo + 4#64 = off_hi) :
    base + off_lo + 4#64 = base + off_hi := by
  subst h
  bv_lin

/-- Split a 64-bit stack cell `(sp - off_lo) ↦₆₄ v ∗ R` into right-associated 32-bit halves
    `(sp - off_lo) ↦₃₂ v.truncate 32 ∗ (sp - off_hi) ↦₃₂ v.extractLsb' 32 32 ∗ R`. -/
theorem pointsTo64_split32_sub (sp off_lo off_hi v : BitVec 64) (R : SepProp)
    (hoff : off_lo - 4#64 = off_hi := by rfl) :
    ((sp - off_lo) ↦₆₄ v) ∗ R =
      ((sp - off_lo) ↦₃₂ v.truncate 32) ∗ ((sp - off_hi) ↦₃₂ v.extractLsb' 32 32) ∗ R := by
  rw [pointsTo64_split32' (sp - off_lo) v, sub_add_four_eq_sub hoff, sepConj_assoc]

/-- Recombine two adjacent 32-bit stack cells `(sp - off_lo) ↦₃₂ lo ∗ (sp - off_hi) ↦₃₂ hi ∗ R`
    into `(sp - off_lo) ↦₆₄ (hi ++ lo) ∗ R`. -/
theorem pointsTo32_combine64_sub (sp off_lo off_hi : BitVec 64) (lo hi : BitVec 32) (R : SepProp)
    (hoff : off_lo - 4#64 = off_hi := by rfl) :
    ((sp - off_lo) ↦₃₂ lo) ∗ ((sp - off_hi) ↦₃₂ hi) ∗ R =
      ((sp - off_lo) ↦₆₄ (hi ++ lo)) ∗ R := by
  rw [← sepConj_assoc, ← sub_add_four_eq_sub hoff, pointsTo32_pair]

/-- Split a 64-bit struct field `(base + off_lo) ↦₆₄ v ∗ R` into right-associated 32-bit halves
    `(base + off_lo) ↦₃₂ v.truncate 32 ∗ (base + off_hi) ↦₃₂ v.extractLsb' 32 32 ∗ R`. -/
theorem pointsTo64_split32_add (base off_lo off_hi v : BitVec 64) (R : SepProp)
    (hoff : off_lo + 4#64 = off_hi := by rfl) :
    ((base + off_lo) ↦₆₄ v) ∗ R =
      ((base + off_lo) ↦₃₂ v.truncate 32) ∗ ((base + off_hi) ↦₃₂ v.extractLsb' 32 32) ∗ R := by
  rw [pointsTo64_split32' (base + off_lo) v, add_add_four_eq_add hoff, sepConj_assoc]

/-- Recombine two adjacent 32-bit struct fields `(base + off_lo) ↦₃₂ lo ∗ (base + off_hi) ↦₃₂ hi ∗ R`
    into `(base + off_lo) ↦₆₄ (hi ++ lo) ∗ R`. -/
theorem pointsTo32_combine64_add (base off_lo off_hi : BitVec 64) (lo hi : BitVec 32) (R : SepProp)
    (hoff : off_lo + 4#64 = off_hi := by rfl) :
    ((base + off_lo) ↦₃₂ lo) ∗ ((base + off_hi) ↦₃₂ hi) ∗ R =
      ((base + off_lo) ↦₆₄ (hi ++ lo)) ∗ R := by
  rw [← sepConj_assoc, ← add_add_four_eq_add hoff, pointsTo32_pair]

/-- Concatenated little-endian bytes of a list of 64-bit words. -/
def unpackL (ws : List (BitVec 64)) : List (BitVec 8) :=
  ws.flatMap unpack64

@[simp]
theorem unpackL_length (ws : List (BitVec 64)) : (unpackL ws).length = 8 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [unpackL, List.flatMap_cons, List.length_append, unpack64_length] at ih ⊢
    rw [ih, List.length_cons]; omega

/-- Any byte list of length `8 * k` is `unpackL ws` for some `k`-element word list `ws`. -/
theorem exists_unpackL : ∀ (k : Nat) (bs : List (BitVec 8)), bs.length = 8 * k →
    ∃ ws : List (BitVec 64), ws.length = k ∧ bs = unpackL ws
  | 0, bs, h => ⟨[], rfl, by simp at h; simp [h, unpackL]⟩
  | k + 1, bs, h => by
    obtain ⟨w, hw⟩ := exists_unpack64_of_length_8 (bs := bs.take 8) (by simp; omega)
    obtain ⟨ws, hl, hws⟩ := exists_unpackL k (bs.drop 8) (by simp; omega)
    refine ⟨w :: ws, by simp [hl], ?_⟩
    conv => lhs; rw [← List.take_append_drop 8 bs]
    rw [hw, hws]; simp [unpackL]

theorem bytesLE_eight_eq_unpack64 (v : BitVec 64) :
    Obj.bytesLE 8 v = unpack64 v := rfl

/-- Unpack a 32-bit word into its 4 big-endian bytes. -/
def unpack32BE (w : BitVec 32) : List (BitVec 8) :=
  [w.extractLsb' 24 8, w.extractLsb' 16 8, w.extractLsb' 8 8, w.extractLsb' 0 8]

@[simp]
theorem unpack32BE_length (w : BitVec 32) : (unpack32BE w).length = 4 := rfl

/-- Unpack a 64-bit word into its 8 big-endian bytes. -/
def unpack64BE (v : BitVec 64) : List (BitVec 8) :=
  [v.extractLsb' 56 8, v.extractLsb' 48 8, v.extractLsb' 40 8, v.extractLsb' 32 8,
   v.extractLsb' 24 8, v.extractLsb' 16 8, v.extractLsb' 8 8, v.extractLsb' 0 8]

@[simp]
theorem unpack64BE_length (v : BitVec 64) : (unpack64BE v).length = 8 := rfl

/-- Combine two adjacent 8-bit cells into one 16-bit cell. -/
theorem pointsTo8_pair (a : BitVec 64) (b0 b1 : BitVec 8) :
    ((a ↦₈ b0) ∗ ((a + 1#64) ↦₈ b1)) = (a ↦₁₆ (b1 ++ b0)) := by
  rw [← pointsToBytes2_eq_pointsTo16, pointsToBytes_cons, pointsToBytes_singleton]

abbrev pointsTo8_pair_eq_pointsTo16 := @pointsTo8_pair

/-- Split a 16-bit points-to cell into two adjacent 8-bit points-to cells. -/
theorem pointsTo16_split8 (a : BitVec 64) (w : BitVec 16) :
    (a ↦₁₆ w) = ((a ↦₈ w.extractLsb' 0 8) ∗ ((a + 1#64) ↦₈ w.extractLsb' 8 8)) := by
  rw [pointsTo16_eq_pointsToBytes, unpack16, pointsToBytes_cons, pointsToBytes_singleton]

abbrev pointsTo16_eq_pointsTo8_pair := @pointsTo16_split8

theorem unpack32_append16 (lo hi : BitVec 16) :
    unpack32 (hi ++ lo) = unpack16 lo ++ unpack16 hi := by
  simp only [unpack32, unpack16, List.cons_append, List.nil_append, List.cons.injEq, and_true]
  exact ⟨by bv_bits, by bv_bits, by bv_bits, by bv_bits⟩

/-- Combine two adjacent 16-bit cells into one 32-bit cell. -/
theorem pointsTo16_pair (a : BitVec 64) (lo hi : BitVec 16) :
    ((a ↦₁₆ lo) ∗ ((a + 2#64) ↦₁₆ hi)) = (a ↦₃₂ (hi ++ lo)) := by
  rw [pointsTo16_eq_pointsToBytes, pointsTo16_eq_pointsToBytes, pointsTo32_eq_pointsToBytes,
      unpack32_append16, pointsToBytes_append, unpack16_length]

abbrev pointsTo16_pair_eq_pointsTo32 := @pointsTo16_pair

/-- Split a 32-bit points-to cell into two adjacent 16-bit points-to cells. -/
theorem pointsTo32_split16 (a : BitVec 64) (v : BitVec 32) :
    (a ↦₃₂ v) = ((a ↦₁₆ v.extractLsb' 0 16) ∗ ((a + 2#64) ↦₁₆ v.extractLsb' 16 16)) := by
  rw [pointsTo16_pair]
  congr 1
  bv_bits

abbrev pointsTo32_eq_pointsTo16_pair := @pointsTo32_split16

/-- Combine four adjacent 8-bit cells into one 32-bit cell. -/
theorem pointsTo8_quad (a : BitVec 64) (b0 b1 b2 b3 : BitVec 8) :
    ((a ↦₈ b0) ∗ ((a + 1#64) ↦₈ b1) ∗ ((a + 2#64) ↦₈ b2) ∗ ((a + 3#64) ↦₈ b3)) =
      (a ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) := by
  rw [← pointsToBytes4_eq_pointsTo32, pointsToBytes_cons, pointsToBytes_cons, pointsToBytes_cons,
      pointsToBytes_singleton]
  have h2 : a + 1#64 + 1#64 = a + 2#64 := by bv_arith
  have h3 : a + 2#64 + 1#64 = a + 3#64 := by bv_arith
  rw [h2, h3]


/-- Split a 32-bit points-to cell into four adjacent 8-bit points-to cells. -/
theorem pointsTo32_split8 (a : BitVec 64) (v : BitVec 32) :
    (a ↦₃₂ v) =
      ((a ↦₈ v.extractLsb' 0 8) ∗ ((a + 1#64) ↦₈ v.extractLsb' 8 8) ∗
       ((a + 2#64) ↦₈ v.extractLsb' 16 8) ∗ ((a + 3#64) ↦₈ v.extractLsb' 24 8)) := by
  rw [pointsTo32_eq_pointsToBytes, unpack32, pointsToBytes_cons, pointsToBytes_cons,
      pointsToBytes_cons, pointsToBytes_singleton]
  have h2 : a + 1#64 + 1#64 = a + 2#64 := by bv_arith
  have h3 : a + 2#64 + 1#64 = a + 3#64 := by bv_arith
  rw [h2, h3]


/-- Combine four adjacent 16-bit cells into one 64-bit cell. -/
theorem pointsTo16_quad (a : BitVec 64) (h0 h1 h2 h3 : BitVec 16) :
    ((a ↦₁₆ h0) ∗ ((a + 2#64) ↦₁₆ h1) ∗ ((a + 4#64) ↦₁₆ h2) ∗ ((a + 6#64) ↦₁₆ h3)) =
      (a ↦₆₄ ((h3 ++ h2) ++ (h1 ++ h0))) := by
  have ha4 : a + 4#64 + 2#64 = a + 6#64 := by bv_arith
  rw [← sepConj_assoc, pointsTo16_pair a h0 h1, ← ha4,
      pointsTo16_pair (a + 4#64) h2 h3, pointsTo32_pair]

/-- Split a 64-bit points-to cell into four adjacent 16-bit points-to cells. -/
theorem pointsTo64_split16 (a v : BitVec 64) :
    (a ↦₆₄ v) =
      ((a ↦₁₆ v.extractLsb' 0 16) ∗
       ((a + 2#64) ↦₁₆ v.extractLsb' 16 16) ∗
       ((a + 4#64) ↦₁₆ v.extractLsb' 32 16) ∗
       ((a + 6#64) ↦₁₆ v.extractLsb' 48 16)) := by
  rw [pointsTo16_quad]
  congr 1
  bv_bits

/-- Split a 64-bit points-to cell at `st + off` into two adjacent 32-bit points-to cells. -/
theorem pointsTo64_split32_at (st off : BitVec 64) (v : BitVec 64) :
    ((st + off) ↦₆₄ v) =
      (((st + off) ↦₃₂ v.truncate 32) ∗ ((st + (off + 4#64)) ↦₃₂ v.extractLsb' 32 32)) := by
  rw [pointsTo64_split32', BitVec.add_assoc]

theorem extractLsb_hi32_append (v : BitVec 64) (lo : BitVec 32) :
    v.extractLsb' 32 32 ++ lo = (v &&& 0xffffffff00000000#64) ||| lo.zeroExtend 64 := by
  have hmask : ∀ i : Fin 64, (0xffffffff00000000#64)[i.val] = decide (32 ≤ i.val) := by decide
  ext i hi
  have hm : (0xffffffff00000000#64)[i] = decide (32 ≤ i) := hmask ⟨i, hi⟩
  simp only [BitVec.getElem_append, BitVec.getElem_extractLsb', BitVec.getElem_or,
    BitVec.getElem_and, BitVec.zeroExtend_eq_setWidth, BitVec.getElem_setWidth, hm]
  by_cases h : i < 32
  · have hge : ¬(32 ≤ i) := by omega
    simp [h, hge]
  · have hge : 32 ≤ i := by omega
    have hadd : 32 + (i - 32) = i := by omega
    simp [h, hge, hadd, BitVec.getLsbD_eq_getElem hi]

/-- Merge an updated low 32-bit cell `a ↦₃₂ lo` with the high 32-bit half `(a + 4) ↦₃₂ v.extractLsb' 32 32`. -/
theorem pointsTo32_merge64_lo (a v : BitVec 64) (lo : BitVec 32) :
    ((a ↦₃₂ lo) ∗ ((a + 4#64) ↦₃₂ v.extractLsb' 32 32)) =
      (a ↦₆₄ ((v &&& 0xffffffff00000000#64) ||| lo.zeroExtend 64)) := by
  rw [pointsTo32_pair, extractLsb_hi32_append]

/-- Offset-indexed version of `pointsTo32_merge64_lo` at `st + off`. -/
theorem pointsTo32_merge64_lo_at (st off : BitVec 64) (v : BitVec 64) (lo : BitVec 32) :
    (((st + off) ↦₃₂ lo) ∗ ((st + (off + 4#64)) ↦₃₂ v.extractLsb' 32 32)) =
      ((st + off) ↦₆₄ ((v &&& 0xffffffff00000000#64) ||| lo.zeroExtend 64)) := by
  rw [← BitVec.add_assoc, pointsTo32_merge64_lo]


/-! ## Subslice, `listMove`, and Zero-Initialized Region Lemmas -/

/-- Functional model of `memmove(buf + dst, buf + src, len)` on a byte list `buf`. -/
def listMove (buf : List (BitVec 8)) (dst src len : Nat) : List (BitVec 8) :=
  buf.take dst ++ (buf.drop src).take len ++ buf.drop (dst + len)

/-- Split `base ↦ₛ buf` into `(base + off) ↦ₛ (buf.drop off).take len` and its prefix/suffix frame. -/
theorem pointsToBytes_split3 (base : BitVec 64) (buf : List (BitVec 8)) (off len : Nat)
    (hle : off + len ≤ buf.length) :
    (base ↦ₛ buf) =
      ((base + BitVec.ofNat 64 off) ↦ₛ (buf.drop off).take len) ∗
      ((base ↦ₛ buf.take off) ∗
       ((base + BitVec.ofNat 64 (off + len)) ↦ₛ buf.drop (off + len))) := by
  have hbuf : buf = buf.take off ++ ((buf.drop off).take len ++ buf.drop (off + len)) := by
    rw [← List.drop_drop, List.take_append_drop, List.take_append_drop]
  conv => lhs; rw [hbuf]
  rw [pointsToBytes_append, pointsToBytes_append]
  have h1 : (buf.take off).length = off := List.length_take_of_le (by omega)
  have h2 : ((buf.drop off).take len).length = len := by
    rw [List.length_take, List.length_drop]; omega
  rw [h1, h2]
  have hadj : base + BitVec.ofNat 64 off + BitVec.ofNat 64 len =
      base + BitVec.ofNat 64 (off + len) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [hadj]
  ac_rfl

/-- Split `base ↦ᵣ buf` into `(base + off) ↦ᵣ (buf.drop off).take len` and its prefix/suffix frame. -/
theorem pointsToBytesRO_split3 (base : BitVec 64) (buf : List (BitVec 8)) (off len : Nat)
    (hle : off + len ≤ buf.length) :
    (base ↦ᵣ buf) =
      ((base + BitVec.ofNat 64 off) ↦ᵣ (buf.drop off).take len) ∗
      ((base ↦ᵣ buf.take off) ∗
       ((base + BitVec.ofNat 64 (off + len)) ↦ᵣ buf.drop (off + len))) := by
  have hbuf : buf = buf.take off ++ ((buf.drop off).take len ++ buf.drop (off + len)) := by
    rw [← List.drop_drop, List.take_append_drop, List.take_append_drop]
  conv => lhs; rw [hbuf]
  rw [pointsToBytesRO_append, pointsToBytesRO_append]
  have h1 : (buf.take off).length = off := List.length_take_of_le (by omega)
  have h2 : ((buf.drop off).take len).length = len := by
    rw [List.length_take, List.length_drop]; omega
  rw [h1, h2]
  have hadj : base + BitVec.ofNat 64 off + BitVec.ofNat 64 len =
      base + BitVec.ofNat 64 (off + len) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [hadj]
  ac_rfl

theorem List.drop_eq_getD_cons {α : Type _} (xs : List α) (off : Nat) (d : α)
    (h : off < xs.length) :
    xs.drop off = xs.getD off d :: xs.drop (off + 1) := by
  induction xs generalizing off with
  | nil => contradiction
  | cons x xs ih =>
    cases off with
    | zero => rfl
    | succ k =>
      simp only [List.length_cons] at h
      exact ih k (by omega)

theorem List.set_eq_take_cons_drop {α : Type _} (xs : List α) (off : Nat) (v : α)
    (h : off < xs.length) :
    xs.set off v = xs.take off ++ (v :: xs.drop (off + 1)) := by
  induction xs generalizing off with
  | nil => contradiction
  | cons x xs ih =>
    cases off with
    | zero => rfl
    | succ k =>
      simp only [List.length_cons] at h
      simp only [List.set_cons_succ, List.take_succ_cons, List.drop_succ_cons, List.cons_append]
      congr 1
      exact ih k (by omega)

theorem List.take_succ_eq_take_append_getD {α : Type _} (xs : List α) (off : Nat) (d : α)
    (h : off < xs.length) :
    xs.take (off + 1) = xs.take off ++ [xs.getD off d] := by
  induction xs generalizing off with
  | nil => contradiction
  | cons x xs ih =>
    cases off with
    | zero => rfl
    | succ k =>
      simp only [List.length_cons] at h
      simp only [List.take_succ_cons, List.cons_append]
      congr 1
      exact ih k (by omega)

theorem List.getD_set_eq {α : Type _} (xs : List α) (i : Nat) (v d : α)
    (hi : i < xs.length) :
    (xs.set i v).getD i d = v := by
  induction xs generalizing i with
  | nil => contradiction
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ k =>
      simp only [List.length_cons] at hi
      exact ih k (by omega)

theorem List.set_ofFn {α : Type _} {n : Nat} (f : Fin n → α) (i : Nat) (v : α) :
    (List.ofFn f).set i v =
      List.ofFn (fun k : Fin n => if k.val = i then v else f k) := by
  apply List.ext_getElem (by simp)
  intro j h1 h2
  rw [List.getElem_set, List.getElem_ofFn, List.getElem_ofFn]
  by_cases hj : i = j
  · simp [hj]
  · have : ¬ j = i := fun h => hj h.symm
    simp [hj, this]

theorem List.getD_ofFn {α : Type _} {n : Nat} (f : Fin n → α) (i : Nat) (d : α)
    (hi : i < n) :
    (List.ofFn f).getD i d = f ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hi),
      List.getElem_ofFn, Option.getD_some]

theorem List.splice_length {α : Type _} (xs sub : List α) (off : Nat)
    (hle : off + sub.length ≤ xs.length) :
    (xs.take off ++ sub ++ xs.drop (off + sub.length)).length = xs.length := by
  simp only [List.length_append, List.length_take, List.length_drop]
  omega

theorem List.splice_drop_take_eq {α : Type _} (xs : List α) (off len : Nat) :
    xs.take off ++ (xs.drop off).take len ++ xs.drop (off + len) = xs := by
  rw [List.append_assoc, ← List.drop_drop, List.take_append_drop, List.take_append_drop]

/-- Pack 2 little-endian bytes into a 16-bit halfword. -/
def pack16 (b0 b1 : BitVec 8) : BitVec 16 :=
  b1 ++ b0

/-- Pack 4 little-endian bytes into a 32-bit word. -/
def pack32 (b0 b1 b2 b3 : BitVec 8) : BitVec 32 :=
  b3 ++ b2 ++ b1 ++ b0

/-- Pack 8 little-endian bytes into a 64-bit word. -/
def pack64 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) : BitVec 64 :=
  b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0

theorem pack16_zeroExtend64 (b0 b1 : BitVec 8) :
    (pack16 b0 b1).zeroExtend 64 =
      b0.zeroExtend 64 ||| ((b1.zeroExtend 64) <<< 8) := by
  unfold pack16
  bv_bits

private theorem append24_8_zeroExtend (x : BitVec 24) (b0 : BitVec 8) :
    (x ++ b0).zeroExtend 64 =
      b0.zeroExtend 64 ||| ((x.zeroExtend 64) <<< 8) := by
  bv_bits

private theorem append16_8_zeroExtend_8 (y : BitVec 16) (b1 : BitVec 8) :
    ((y ++ b1).zeroExtend 64) <<< 8 =
      ((b1.zeroExtend 64) <<< 8) ||| ((y.zeroExtend 64) <<< 16) := by
  bv_bits

private theorem append8_8_zeroExtend_16 (b3 b2 : BitVec 8) :
    ((b3 ++ b2).zeroExtend 64) <<< 16 =
      ((b2.zeroExtend 64) <<< 16) ||| ((b3.zeroExtend 64) <<< 24) := by
  bv_bits

theorem pack32_zeroExtend64 (b0 b1 b2 b3 : BitVec 8) :
    (pack32 b0 b1 b2 b3).zeroExtend 64 =
      b0.zeroExtend 64 ||| ((b1.zeroExtend 64) <<< 8) |||
      ((b2.zeroExtend 64) <<< 16) ||| ((b3.zeroExtend 64) <<< 24) := by
  unfold pack32
  rw [append24_8_zeroExtend, append16_8_zeroExtend_8, append8_8_zeroExtend_16]
  simp only [BitVec.or_assoc]

theorem pack16_reconstruct (w : BitVec 16) :
    pack16 (w.extractLsb' 0 8) (w.extractLsb' 8 8) = w := by
  unfold pack16
  bv_bits

theorem pointsToBytes_take1_eq_pointsTo8 (a : BitVec 64) (bs : List (BitVec 8)) (off : Nat)
    (h : off + 1 ≤ bs.length) :
    (a ↦ₛ (bs.drop off).take 1) = (a ↦₈ bs.getD off 0#8) := by
  have hd0 := List.drop_eq_getD_cons bs off 0#8 (by omega)
  rw [hd0, List.take_succ_cons, List.take_zero, pointsToBytes_singleton]

theorem pointsToBytesRO_take1_eq_pointsTo8RO (a : BitVec 64) (bs : List (BitVec 8)) (off : Nat)
    (h : off + 1 ≤ bs.length) :
    (a ↦ᵣ (bs.drop off).take 1) = (a ↦₈ᵣ bs.getD off 0#8) := by
  have hd0 := List.drop_eq_getD_cons bs off 0#8 (by omega)
  rw [hd0, List.take_succ_cons, List.take_zero, pointsToBytesRO_singleton]

theorem pointsToBytes_take2_eq_pointsTo16 (a : BitVec 64) (bs : List (BitVec 8)) (off : Nat)
    (h : off + 2 ≤ bs.length) :
    (a ↦ₛ (bs.drop off).take 2) = (a ↦₁₆ pack16 (bs.getD off 0#8) (bs.getD (off + 1) 0#8)) := by
  have hd0 := List.drop_eq_getD_cons bs off 0#8 (by omega)
  have hd1 := List.drop_eq_getD_cons bs (off + 1) 0#8 (by omega)
  rw [hd0, List.take_succ_cons, hd1, List.take_succ_cons, List.take_zero]
  exact pointsToBytes2_eq_pointsTo16 a _ _

theorem pointsToBytesRO_take2_eq_pointsTo16RO (a : BitVec 64) (bs : List (BitVec 8)) (off : Nat)
    (h : off + 2 ≤ bs.length) :
    (a ↦ᵣ (bs.drop off).take 2) = (a ↦₁₆ᵣ pack16 (bs.getD off 0#8) (bs.getD (off + 1) 0#8)) := by
  have hd0 := List.drop_eq_getD_cons bs off 0#8 (by omega)
  have hd1 := List.drop_eq_getD_cons bs (off + 1) 0#8 (by omega)
  rw [hd0, List.take_succ_cons, hd1, List.take_succ_cons, List.take_zero]
  exact pointsToBytesRO2_eq_pointsTo16RO a _ _

theorem pointsToBytes_take4_eq_pointsTo32 (a : BitVec 64) (bs : List (BitVec 8)) (off : Nat)
    (h : off + 4 ≤ bs.length) :
    (a ↦ₛ (bs.drop off).take 4) =
      (a ↦₃₂ pack32 (bs.getD off 0#8) (bs.getD (off + 1) 0#8)
        (bs.getD (off + 2) 0#8) (bs.getD (off + 3) 0#8)) := by
  have hd0 := List.drop_eq_getD_cons bs off 0#8 (by omega)
  have hd1 := List.drop_eq_getD_cons bs (off + 1) 0#8 (by omega)
  have hd2 := List.drop_eq_getD_cons bs (off + 2) 0#8 (by omega)
  have hd3 := List.drop_eq_getD_cons bs (off + 3) 0#8 (by omega)
  rw [hd0, List.take_succ_cons, hd1, List.take_succ_cons, hd2, List.take_succ_cons,
      hd3, List.take_succ_cons, List.take_zero]
  exact pointsToBytes4_eq_pointsTo32 a _ _ _ _

theorem pointsToBytesRO_take4_eq_pointsTo32RO (a : BitVec 64) (bs : List (BitVec 8)) (off : Nat)
    (h : off + 4 ≤ bs.length) :
    (a ↦ᵣ (bs.drop off).take 4) =
      (a ↦₃₂ᵣ pack32 (bs.getD off 0#8) (bs.getD (off + 1) 0#8)
        (bs.getD (off + 2) 0#8) (bs.getD (off + 3) 0#8)) := by
  have hd0 := List.drop_eq_getD_cons bs off 0#8 (by omega)
  have hd1 := List.drop_eq_getD_cons bs (off + 1) 0#8 (by omega)
  have hd2 := List.drop_eq_getD_cons bs (off + 2) 0#8 (by omega)
  have hd3 := List.drop_eq_getD_cons bs (off + 3) 0#8 (by omega)
  rw [hd0, List.take_succ_cons, hd1, List.take_succ_cons, hd2, List.take_succ_cons,
      hd3, List.take_succ_cons, List.take_zero]
  exact pointsToBytesRO4_eq_pointsTo32RO a _ _ _ _

theorem pointsToBytes_take8_eq_pointsTo64 (a : BitVec 64) (bs : List (BitVec 8)) (off : Nat)
    (h : off + 8 ≤ bs.length) :
    (a ↦ₛ (bs.drop off).take 8) =
      (a ↦₆₄ pack64 (bs.getD off 0#8) (bs.getD (off + 1) 0#8)
        (bs.getD (off + 2) 0#8) (bs.getD (off + 3) 0#8)
        (bs.getD (off + 4) 0#8) (bs.getD (off + 5) 0#8)
        (bs.getD (off + 6) 0#8) (bs.getD (off + 7) 0#8)) := by
  have hd0 := List.drop_eq_getD_cons bs off 0#8 (by omega)
  have hd1 := List.drop_eq_getD_cons bs (off + 1) 0#8 (by omega)
  have hd2 := List.drop_eq_getD_cons bs (off + 2) 0#8 (by omega)
  have hd3 := List.drop_eq_getD_cons bs (off + 3) 0#8 (by omega)
  have hd4 := List.drop_eq_getD_cons bs (off + 4) 0#8 (by omega)
  have hd5 := List.drop_eq_getD_cons bs (off + 5) 0#8 (by omega)
  have hd6 := List.drop_eq_getD_cons bs (off + 6) 0#8 (by omega)
  have hd7 := List.drop_eq_getD_cons bs (off + 7) 0#8 (by omega)
  rw [hd0, List.take_succ_cons, hd1, List.take_succ_cons, hd2, List.take_succ_cons,
      hd3, List.take_succ_cons, hd4, List.take_succ_cons, hd5, List.take_succ_cons,
      hd6, List.take_succ_cons, hd7, List.take_succ_cons, List.take_zero]
  exact pointsToBytes8_eq_pointsTo64 a _ _ _ _ _ _ _ _

theorem pointsToBytesRO_take8_eq_pointsTo64RO (a : BitVec 64) (bs : List (BitVec 8)) (off : Nat)
    (h : off + 8 ≤ bs.length) :
    (a ↦ᵣ (bs.drop off).take 8) =
      (a ↦₆₄ᵣ pack64 (bs.getD off 0#8) (bs.getD (off + 1) 0#8)
        (bs.getD (off + 2) 0#8) (bs.getD (off + 3) 0#8)
        (bs.getD (off + 4) 0#8) (bs.getD (off + 5) 0#8)
        (bs.getD (off + 6) 0#8) (bs.getD (off + 7) 0#8)) := by
  have hd0 := List.drop_eq_getD_cons bs off 0#8 (by omega)
  have hd1 := List.drop_eq_getD_cons bs (off + 1) 0#8 (by omega)
  have hd2 := List.drop_eq_getD_cons bs (off + 2) 0#8 (by omega)
  have hd3 := List.drop_eq_getD_cons bs (off + 3) 0#8 (by omega)
  have hd4 := List.drop_eq_getD_cons bs (off + 4) 0#8 (by omega)
  have hd5 := List.drop_eq_getD_cons bs (off + 5) 0#8 (by omega)
  have hd6 := List.drop_eq_getD_cons bs (off + 6) 0#8 (by omega)
  have hd7 := List.drop_eq_getD_cons bs (off + 7) 0#8 (by omega)
  rw [hd0, List.take_succ_cons, hd1, List.take_succ_cons, hd2, List.take_succ_cons,
      hd3, List.take_succ_cons, hd4, List.take_succ_cons, hd5, List.take_succ_cons,
      hd6, List.take_succ_cons, hd7, List.take_succ_cons, List.take_zero]
  exact pointsToBytesRO8_eq_pointsTo64RO a _ _ _ _ _ _ _ _

theorem pointsToBytes_focus8 (base : BitVec 64) (bs : List (BitVec 8)) (off : Nat)
    (h : off < bs.length) :
    (base ↦ₛ bs) =
      ((base + BitVec.ofNat 64 off) ↦₈ bs.getD off 0#8) ∗
      ((base ↦ₛ bs.take off) ∗
       ((base + BitVec.ofNat 64 (off + 1)) ↦ₛ bs.drop (off + 1))) := by
  rw [pointsToBytes_split3 base bs off 1 (by omega),
      pointsToBytes_take1_eq_pointsTo8 (base + BitVec.ofNat 64 off) bs off (by omega)]

theorem pointsToBytes_focus16 (base : BitVec 64) (bs : List (BitVec 8)) (off : Nat)
    (h : off + 2 ≤ bs.length) :
    (base ↦ₛ bs) =
      ((base + BitVec.ofNat 64 off) ↦₁₆ pack16 (bs.getD off 0#8) (bs.getD (off + 1) 0#8)) ∗
      ((base ↦ₛ bs.take off) ∗
       ((base + BitVec.ofNat 64 (off + 2)) ↦ₛ bs.drop (off + 2))) := by
  rw [pointsToBytes_split3 base bs off 2 h,
      pointsToBytes_take2_eq_pointsTo16 (base + BitVec.ofNat 64 off) bs off h]

theorem pointsToBytes_focus32 (base : BitVec 64) (bs : List (BitVec 8)) (off : Nat)
    (h : off + 4 ≤ bs.length) :
    (base ↦ₛ bs) =
      ((base + BitVec.ofNat 64 off) ↦₃₂
        pack32 (bs.getD off 0#8) (bs.getD (off + 1) 0#8)
          (bs.getD (off + 2) 0#8) (bs.getD (off + 3) 0#8)) ∗
      ((base ↦ₛ bs.take off) ∗
       ((base + BitVec.ofNat 64 (off + 4)) ↦ₛ bs.drop (off + 4))) := by
  rw [pointsToBytes_split3 base bs off 4 h,
      pointsToBytes_take4_eq_pointsTo32 (base + BitVec.ofNat 64 off) bs off h]

theorem pointsToBytes_focus64 (base : BitVec 64) (bs : List (BitVec 8)) (off : Nat)
    (h : off + 8 ≤ bs.length) :
    (base ↦ₛ bs) =
      ((base + BitVec.ofNat 64 off) ↦₆₄
        pack64 (bs.getD off 0#8) (bs.getD (off + 1) 0#8)
          (bs.getD (off + 2) 0#8) (bs.getD (off + 3) 0#8)
          (bs.getD (off + 4) 0#8) (bs.getD (off + 5) 0#8)
          (bs.getD (off + 6) 0#8) (bs.getD (off + 7) 0#8)) ∗
      ((base ↦ₛ bs.take off) ∗
       ((base + BitVec.ofNat 64 (off + 8)) ↦ₛ bs.drop (off + 8))) := by
  rw [pointsToBytes_split3 base bs off 8 h,
      pointsToBytes_take8_eq_pointsTo64 (base + BitVec.ofNat 64 off) bs off h]

theorem pointsToBytes_split_at (base : BitVec 64) (bs : List (BitVec 8)) (off : Nat)
    (h : off < bs.length) :
    (base ↦ₛ bs) =
      (base ↦ₛ bs.take off) ∗
      ((base + BitVec.ofNat 64 off) ↦₈ bs.getD off 0#8) ∗
      ((base + BitVec.ofNat 64 (off + 1)) ↦ₛ bs.drop (off + 1)) := by
  rw [pointsToBytes_focus8 base bs off h]
  ac_rfl

theorem pointsToBytes_merge_at (base : BitVec 64) (bs : List (BitVec 8)) (off : Nat)
    (v : BitVec 8) (h : off < bs.length) :
    ((base ↦ₛ bs.take off) ∗
     ((base + BitVec.ofNat 64 off) ↦₈ v) ∗
     ((base + BitVec.ofNat 64 (off + 1)) ↦ₛ bs.drop (off + 1))) =
      (base ↦ₛ bs.set off v) := by
  rw [List.set_eq_take_cons_drop bs off v h, pointsToBytes_append, pointsToBytes_cons]
  have hl : (bs.take off).length = off := List.length_take_of_le (by omega)
  rw [hl]
  have hadj : base + BitVec.ofNat 64 off + 1#64 = base + BitVec.ofNat 64 (off + 1) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [hadj]

theorem pointsToBytes_split_at32 (base : BitVec 64) (bs : List (BitVec 8)) (off : Nat)
    (h : off + 4 ≤ bs.length) :
    (base ↦ₛ bs) =
      (base ↦ₛ bs.take off) ∗
      ((base + BitVec.ofNat 64 off) ↦₃₂
        pack32 (bs.getD off 0#8) (bs.getD (off + 1) 0#8)
          (bs.getD (off + 2) 0#8) (bs.getD (off + 3) 0#8)) ∗
      ((base + BitVec.ofNat 64 (off + 4)) ↦ₛ bs.drop (off + 4)) := by
  rw [pointsToBytes_focus32 base bs off h]
  ac_rfl

/-- Reassemble `base ↦ₛ listMove buf dst src len` after writing `(buf.drop src).take len` at `base + dst`. -/
theorem pointsToBytes_listMove (base : BitVec 64) (buf : List (BitVec 8)) (dst src len : Nat)
    (hdst : dst + len ≤ buf.length) (hsrc : src + len ≤ buf.length) :
    (((base + BitVec.ofNat 64 dst) ↦ₛ (buf.drop src).take len) ∗
      ((base ↦ₛ buf.take dst) ∗
       ((base + BitVec.ofNat 64 (dst + len)) ↦ₛ buf.drop (dst + len)))) =
    (base ↦ₛ listMove buf dst src len) := by
  unfold listMove
  rw [List.append_assoc, pointsToBytes_append, pointsToBytes_append]
  have h1 : (buf.take dst).length = dst := List.length_take_of_le (by omega)
  have h2 : ((buf.drop src).take len).length = len := by
    rw [List.length_take, List.length_drop]; omega
  rw [h1, h2]
  have hadj : base + BitVec.ofNat 64 dst + BitVec.ofNat 64 len =
      base + BitVec.ofNat 64 (dst + len) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [hadj]
  ac_rfl

theorem List.replicate_add {α : Type _} (n k : Nat) (b : α) :
    List.replicate (n + k) b = List.replicate n b ++ List.replicate k b := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_add, List.replicate_succ, List.replicate_succ, List.cons_append, ih]

/-- Split a byte slice `a ↦ₛ List.replicate (m + k) b` into two adjacent slices. -/
theorem pointsToBytes_replicate_split (a : BitVec 64) (m k : Nat) (b : BitVec 8) :
    (a ↦ₛ List.replicate (m + k) b) =
      ((a ↦ₛ List.replicate m b) ∗ ((a + BitVec.ofNat 64 m) ↦ₛ List.replicate k b)) := by
  rw [List.replicate_add, pointsToBytes_append, List.length_replicate]

/-- Split a byte slice at an offset `(a + off) ↦ₛ List.replicate (m + k) b`. -/
theorem pointsToBytes_replicate_split_off (a : BitVec 64) (off m k : Nat) (b : BitVec 8) :
    ((a + BitVec.ofNat 64 off) ↦ₛ List.replicate (m + k) b) =
      (((a + BitVec.ofNat 64 off) ↦ₛ List.replicate m b) ∗
       ((a + BitVec.ofNat 64 (off + m)) ↦ₛ List.replicate k b)) := by
  rw [pointsToBytes_replicate_split]
  have h : a + BitVec.ofNat 64 off + BitVec.ofNat 64 m = a + BitVec.ofNat 64 (off + m) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [h]

theorem pointsToBytes_replicate4_zero (a : BitVec 64) :
    (a ↦ₛ List.replicate 4 0#8) = (a ↦₃₂ 0#32) := by
  rw [pointsTo32_eq_pointsToBytes]; rfl

theorem pointsToBytes_replicate8_zero (a : BitVec 64) :
    (a ↦ₛ List.replicate 8 0#8) = (a ↦₆₄ 0#64) := by
  rw [pointsTo64_eq_pointsToBytes]; rfl

/-! ## `Memory.writeBytes` and `Memory.readBytes` Bridges -/

/-- Writing `bs` to `memRegion a bs.length` under frame `R` yields `(a ↦ₛ bs) ∗ R`. -/
theorem satisfies_writeBytes {m : Memory} {a : BitVec 64} (bs : List (BitVec 8)) {R : SepProp}
    (hlen : bs.length ≤ 2 ^ 64) (hm : m ⊨ memRegion a bs.length ∗ R) :
    m.writeBytes a bs ⊨ (a ↦ₛ bs) ∗ R := by
  induction bs generalizing m a R with
  | nil =>
    rw [Memory.writeBytes, pointsToBytes_nil]
    rwa [List.length_nil, memRegion_zero] at hm
  | cons b bs ih =>
    simp only [List.length_cons] at hlen
    rw [List.length_cons, show bs.length + 1 = 1 + bs.length by omega,
      memRegion_split a 1 bs.length (by omega), sepConj_assoc] at hm
    have hm1 : m.write8 a b ⊨ (a ↦₈ b) ∗ (memRegion (a + 1#64) bs.length ∗ R) :=
      (IsBlock.memRegion a 1).update (IsBlock.pointsTo8 a b) (by decide) hm
        ((AgreesOutside.rfl' m a 1).write8 (by simp [InRegion]))
        (Memory.read8_write8_same m a b)
    rw [sepConj_comm (a ↦₈ b), sepConj_assoc] at hm1
    have hm2 := ih (R := R ∗ (a ↦₈ b)) (by omega) hm1
    rw [Memory.writeBytes, pointsToBytes_cons]
    refine Eq.mp (congrArg (fun P => (m.write8 a b).writeBytes (a + 1#64) bs ⊨ P) ?_) hm2
    ac_rfl

/-- Writing `bs` over an owned slice `a ↦ₛ bs₀` of equal length under frame `R` yields `(a ↦ₛ bs) ∗ R`. -/
theorem writeBytes_satisfies {m : Memory} {a : BitVec 64} {bs₀ bs : List (BitVec 8)} {R : SepProp}
    (hlen : bs₀.length = bs.length) (h : m ⊨ (a ↦ₛ bs₀) ∗ R) :
    m.writeBytes a bs ⊨ (a ↦ₛ bs) ∗ R := by
  induction bs₀ generalizing m a bs R with
  | nil =>
    cases bs with
    | nil => simpa using h
    | cons _ _ => simp at hlen
  | cons b₀ bs₀ ih =>
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      rw [pointsToBytes_cons, sepConj_assoc] at h
      have hw := IsBlock.write8 (IsBlock.pointsTo8 a b₀) h b
      rw [sepConj_left_comm] at hw
      have hw' := ih hlen hw
      rw [sepConj_left_comm, ← sepConj_assoc, ← pointsToBytes_cons] at hw'
      simpa using hw'

/-- Writing `bs` over an existing byte slice `(a ↦ₛ bs₀) ∗ R` of the same length produces `(a ↦ₛ bs) ∗ R`. -/
theorem satisfies_writeBytes_step {m : Memory} {a : BitVec 64} {bs₀ bs : List (BitVec 8)}
    {R : SepProp}
    (h : m ⊨ (a ↦ₛ bs₀) ∗ R)
    (hlen_eq : bs₀.length = bs.length) :
    m.writeBytes a bs ⊨ (a ↦ₛ bs) ∗ R :=
  writeBytes_satisfies hlen_eq h

/-- Writing `bs` to an owned `memRegion a bs.length` keeps all frozen bytes unchanged. -/
theorem keepsFrozen_writeBytes_of_memRegion {m : Memory} {a : BitVec 64} (bs : List (BitVec 8))
    {R : SepProp} (hlen : bs.length ≤ 2 ^ 64) (hm : m ⊨ memRegion a bs.length ∗ R) :
    m.KeepsFrozen (m.writeBytes a bs) :=
  Memory.keepsFrozen_writeBytes bs ((IsBlock.memRegion a bs.length).canWrite hlen hm)

theorem _root_.Arm64.Memory.readBytes_add (m : Memory) (base : BitVec 64) (a b : Nat) :
    m.readBytes base (a + b) =
      m.readBytes base a ++ m.readBytes (base + BitVec.ofNat 64 a) b := by
  induction a generalizing base with
  | zero =>
    simp [Memory.readBytes]
  | succ a ih =>
    have hadd : base + 1#64 + BitVec.ofNat 64 a = base + BitVec.ofNat 64 (a + 1) := by bv_arith
    simp only [Nat.succ_add, Memory.readBytes, List.cons_append, ih (base + 1#64), hadd]

theorem _root_.Arm64.Memory.readBytes_take_drop (m : Memory) (base : BitVec 64)
    (buf : List (BitVec 8)) (hbytes : m.readBytes base buf.length = buf)
    (off k : Nat) (hk : off + k ≤ buf.length) :
    m.readBytes (base + BitVec.ofNat 64 off) k = (buf.drop off).take k := by
  have hsplit1 : buf.length = off + (k + (buf.length - (off + k))) := by omega
  have hb1 := hbytes
  rw [hsplit1, Memory.readBytes_add, Memory.readBytes_add] at hb1
  rw [← hb1]
  rw [List.drop_left' (Memory.readBytes_length m base off)]
  rw [List.take_left' (Memory.readBytes_length m (base + BitVec.ofNat 64 off) k)]

theorem _root_.Arm64.Memory.readBytes_writeBytes_slice (m : Memory) (addr : BitVec 64)
    (bs : List (BitVec 8)) (off len : Nat) (hle : off + len ≤ bs.length)
    (hwrap : bs.length ≤ 2 ^ 64) :
    (m.writeBytes addr bs).readBytes (addr + BitVec.ofNat 64 off) len =
      (bs.drop off).take len :=
  Memory.readBytes_take_drop (m.writeBytes addr bs) addr bs
    (Memory.readBytes_writeBytes_same m addr bs hwrap) off len hle

theorem _root_.Arm64.Memory.readBytes_writeBytes_take (m : Memory) (addr : BitVec 64)
    (bs : List (BitVec 8)) (len : Nat) (hle : len ≤ bs.length)
    (hwrap : bs.length ≤ 2 ^ 64) :
    (m.writeBytes addr bs).readBytes addr len = bs.take len := by
  have h := Memory.readBytes_writeBytes_slice m addr bs 0 len (by omega) hwrap
  simpa using h

theorem _root_.Arm64.Memory.readBytes_writeBytes_prefix (m : Memory) (addr : BitVec 64)
    (bs1 bs2 : List (BitVec 8)) (hwrap : bs1.length + bs2.length ≤ 2 ^ 64) :
    (m.writeBytes addr (bs1 ++ bs2)).readBytes addr bs1.length = bs1 := by
  rw [Memory.readBytes_writeBytes_take m addr (bs1 ++ bs2) bs1.length (by simp)
    (by simpa using hwrap)]
  exact List.take_left

theorem _root_.Arm64.Memory.readBytes_eq_of_read8_eq (m m₀ : Memory) (dst src : BitVec 64) (len : Nat)
    (h : ∀ i < len, m.read8 (dst + BitVec.ofNat 64 i) = m₀.read8 (src + BitVec.ofNat 64 i)) :
    m.readBytes dst len = m₀.readBytes src len := by
  induction len generalizing dst src with
  | zero => rfl
  | succ n ih =>
    simp only [Memory.readBytes, List.cons.injEq]
    constructor
    · have h0 := h 0 (by omega)
      simpa using h0
    · apply ih (dst + 1#64) (src + 1#64)
      intro i hi
      have hi1 := h (i + 1) (by omega)
      have h_dst : dst + 1#64 + BitVec.ofNat 64 i = dst + BitVec.ofNat 64 (i + 1) := by bv_arith
      have h_src : src + 1#64 + BitVec.ofNat 64 i = src + BitVec.ofNat 64 (i + 1) := by bv_arith
      rw [h_dst, h_src, hi1]

theorem _root_.Arm64.Memory.read8_of_readBytes (m : Memory) (base : BitVec 64)
    (bs : List (BitVec 8)) (hread : m.readBytes base bs.length = bs)
    (k : Nat) (hk : k < bs.length) :
    m.read8 (base + BitVec.ofNat 64 k) = bs.getD k 0#8 := by
  have htd := Memory.readBytes_take_drop m base bs hread k 1 (by omega)
  rw [List.drop_eq_getD_cons bs k 0#8 hk, List.take_succ_cons, List.take_zero] at htd
  simpa [Memory.readBytes] using htd

theorem _root_.Arm64.Memory.read16_of_readBytes (m : Memory) (base : BitVec 64)
    (bs : List (BitVec 8)) (hread : m.readBytes base bs.length = bs)
    (k : Nat) (hk : k + 2 ≤ bs.length) :
    m.read16 (base + BitVec.ofNat 64 k) =
      pack16 (bs.getD k 0#8) (bs.getD (k + 1) 0#8) := by
  have h0 := Memory.read8_of_readBytes m base bs hread k (by omega)
  have h1 := Memory.read8_of_readBytes m base bs hread (k + 1) (by omega)
  have hadd0 : base + BitVec.ofNat 64 k + 0#64 = base + BitVec.ofNat 64 k := by bv_arith
  have hadd1 : base + BitVec.ofNat 64 k + 1#64 = base + BitVec.ofNat 64 (k + 1) := by bv_arith
  unfold Memory.read16 pack16
  rw [hadd0, hadd1, h0, h1]

theorem _root_.Arm64.Memory.read32_of_readBytes (m : Memory) (base : BitVec 64)
    (bs : List (BitVec 8)) (hread : m.readBytes base bs.length = bs)
    (k : Nat) (hk : k + 4 ≤ bs.length) :
    m.read32 (base + BitVec.ofNat 64 k) =
      pack32 (bs.getD k 0#8) (bs.getD (k + 1) 0#8)
        (bs.getD (k + 2) 0#8) (bs.getD (k + 3) 0#8) := by
  have h0 := Memory.read8_of_readBytes m base bs hread k (by omega)
  have h1 := Memory.read8_of_readBytes m base bs hread (k + 1) (by omega)
  have h2 := Memory.read8_of_readBytes m base bs hread (k + 2) (by omega)
  have h3 := Memory.read8_of_readBytes m base bs hread (k + 3) (by omega)
  have hadd0 : base + BitVec.ofNat 64 k + 0#64 = base + BitVec.ofNat 64 k := by bv_arith
  have hadd1 : base + BitVec.ofNat 64 k + 1#64 = base + BitVec.ofNat 64 (k + 1) := by bv_arith
  have hadd2 : base + BitVec.ofNat 64 k + 2#64 = base + BitVec.ofNat 64 (k + 2) := by bv_arith
  have hadd3 : base + BitVec.ofNat 64 k + 3#64 = base + BitVec.ofNat 64 (k + 3) := by bv_arith
  unfold Memory.read32 pack32
  rw [hadd0, hadd1, hadd2, hadd3, h0, h1, h2, h3]


theorem _root_.Arm64.Memory.read64_of_readBytes (m : Memory) (base : BitVec 64)
    (bs : List (BitVec 8)) (hread : m.readBytes base bs.length = bs)
    (k : Nat) (hk : k + 8 ≤ bs.length) :
    m.read64 (base + BitVec.ofNat 64 k) =
      pack64 (bs.getD k 0#8) (bs.getD (k + 1) 0#8)
        (bs.getD (k + 2) 0#8) (bs.getD (k + 3) 0#8)
        (bs.getD (k + 4) 0#8) (bs.getD (k + 5) 0#8)
        (bs.getD (k + 6) 0#8) (bs.getD (k + 7) 0#8) := by
  have h0 := Memory.read8_of_readBytes m base bs hread k (by omega)
  have h1 := Memory.read8_of_readBytes m base bs hread (k + 1) (by omega)
  have h2 := Memory.read8_of_readBytes m base bs hread (k + 2) (by omega)
  have h3 := Memory.read8_of_readBytes m base bs hread (k + 3) (by omega)
  have h4 := Memory.read8_of_readBytes m base bs hread (k + 4) (by omega)
  have h5 := Memory.read8_of_readBytes m base bs hread (k + 5) (by omega)
  have h6 := Memory.read8_of_readBytes m base bs hread (k + 6) (by omega)
  have h7 := Memory.read8_of_readBytes m base bs hread (k + 7) (by omega)
  have hadd0 : base + BitVec.ofNat 64 k + 0#64 = base + BitVec.ofNat 64 k := by bv_arith
  have hadd1 : base + BitVec.ofNat 64 k + 1#64 = base + BitVec.ofNat 64 (k + 1) := by bv_arith
  have hadd2 : base + BitVec.ofNat 64 k + 2#64 = base + BitVec.ofNat 64 (k + 2) := by bv_arith
  have hadd3 : base + BitVec.ofNat 64 k + 3#64 = base + BitVec.ofNat 64 (k + 3) := by bv_arith
  have hadd4 : base + BitVec.ofNat 64 k + 4#64 = base + BitVec.ofNat 64 (k + 4) := by bv_arith
  have hadd5 : base + BitVec.ofNat 64 k + 5#64 = base + BitVec.ofNat 64 (k + 5) := by bv_arith
  have hadd6 : base + BitVec.ofNat 64 k + 6#64 = base + BitVec.ofNat 64 (k + 6) := by bv_arith
  have hadd7 : base + BitVec.ofNat 64 k + 7#64 = base + BitVec.ofNat 64 (k + 7) := by bv_arith
  unfold Memory.read64 pack64
  rw [hadd0, hadd1, hadd2, hadd3, hadd4, hadd5, hadd6, hadd7, h0, h1, h2, h3, h4, h5, h6, h7]

theorem _root_.Arm64.Memory.read64_of_readBytes_eq_unpack64 (m : Memory) (a : BitVec 64) (w : BitVec 64)
    (h : m.readBytes a 8 = unpack64 w) :
    m.read64 a = w := by
  have h0 := Memory.read64_of_readBytes m a (unpack64 w) (by simpa [unpack64] using h) 0 (by simp)
  have ha0 : a + BitVec.ofNat 64 0 = a := by bv_arith
  rw [ha0] at h0
  rw [h0]
  unfold pack64 unpack64
  simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
  bv_bits

/-- A 64-bit cell splits into its low byte and 7 bytes of padding. -/
theorem cell_entails_lowByte_pad (a w : BitVec 64) :
    (a ↦₆₄ w) ⊢ (a ↦₈ w.extractLsb' 0 8) ∗ memRegion (a + 1#64) 7 := by
  rw [pointsTo64_eq_pointsToBytes, unpack64, pointsToBytes_cons]
  exact sepConj_mono_right (pointsToBytes_entails_memRegion _ _)

/-- A 64-bit cell split into its low byte (as a 1-byte slice) and its 7 upper bytes. -/
theorem cell_split_byte (a v : BitVec 64) :
    (a ↦₆₄ v) = (a ↦ₛ [v.extractLsb' 0 8]) ∗ ((a + 1#64) ↦ₛ (unpack64 v).tail) := by
  rw [pointsTo64_eq_pointsToBytes, unpack64, pointsToBytes_cons, pointsToBytes_singleton]
  rfl

/-- Reassociate three 64-bit cells at `p, p+8, p+16` into unaligned 64-bit cells at `p+2, p+10`. -/
theorem triple_to_offset2 (p w0 w1 w2 : BitVec 64) :
    ((p ↦₆₄ w0) ∗ ((p + 8#64) ↦₆₄ w1) ∗ ((p + 16#64) ↦₆₄ w2)) =
      ((p ↦₁₆ w0.extractLsb' 0 16) ∗
       ((p + 2#64) ↦₆₄ (w1.extractLsb' 0 16 ++ w0.extractLsb' 16 48)) ∗
       ((p + 10#64) ↦₆₄ (w2.extractLsb' 0 16 ++ w1.extractLsb' 16 48)) ∗
       ((p + 18#64) ↦₁₆ w2.extractLsb' 16 16) ∗
       ((p + 20#64) ↦₃₂ w2.extractLsb' 32 32)) := by
  have lhs : ((p ↦₆₄ w0) ∗ ((p + 8#64) ↦₆₄ w1) ∗ ((p + 16#64) ↦₆₄ w2)) =
      (p ↦ₛ (unpack64 w0 ++ unpack64 w1 ++ unpack64 w2)) := by
    rw [pointsToBytes_append, pointsToBytes_append]
    simp only [List.length_append, unpack64_length, Nat.reduceAdd,
      ← pointsTo64_eq_pointsToBytes, sepConj_assoc]
  have rhs : ((p ↦₁₆ w0.extractLsb' 0 16) ∗
       ((p + 2#64) ↦₆₄ (w1.extractLsb' 0 16 ++ w0.extractLsb' 16 48)) ∗
       ((p + 10#64) ↦₆₄ (w2.extractLsb' 0 16 ++ w1.extractLsb' 16 48)) ∗
       ((p + 18#64) ↦₁₆ w2.extractLsb' 16 16) ∗
       ((p + 20#64) ↦₃₂ w2.extractLsb' 32 32)) =
      (p ↦ₛ (unpack16 (w0.extractLsb' 0 16) ++
        unpack64 (w1.extractLsb' 0 16 ++ w0.extractLsb' 16 48) ++
        unpack64 (w2.extractLsb' 0 16 ++ w1.extractLsb' 16 48) ++
        unpack16 (w2.extractLsb' 16 16) ++
        unpack32 (w2.extractLsb' 32 32))) := by
    rw [pointsToBytes_append, pointsToBytes_append, pointsToBytes_append, pointsToBytes_append]
    simp only [List.length_append, unpack16_length, unpack64_length, Nat.reduceAdd,
      ← pointsTo16_eq_pointsToBytes, ← pointsTo32_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes,
      sepConj_assoc]
  rw [lhs, rhs]
  congr 1
  simp only [unpack64, unpack32, unpack16, List.cons_append, List.nil_append, List.cons.injEq,
    and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩ <;> bv_bits

/-- Recombine unaligned cells at `p, p+2, p+10, p+18, p+20` into three 64-bit cells at `p, p+8, p+16`. -/
theorem offset2_to_triple (p : BitVec 64) (h16 : BitVec 16)
    (w0 w1 w2 : BitVec 64) (t16 : BitVec 16) (t32 : BitVec 32) :
    ((p ↦₁₆ h16) ∗
     ((p + 2#64) ↦₆₄ (w1.extractLsb' 0 16 ++ w0.extractLsb' 16 48)) ∗
     ((p + 10#64) ↦₆₄ (w2.extractLsb' 0 16 ++ w1.extractLsb' 16 48)) ∗
     ((p + 18#64) ↦₁₆ t16) ∗
     ((p + 20#64) ↦₃₂ t32)) =
    ((p ↦₆₄ (w0.extractLsb' 16 48 ++ h16)) ∗
     ((p + 8#64) ↦₆₄ w1) ∗
     ((p + 16#64) ↦₆₄ (t32 ++ t16 ++ w2.extractLsb' 0 16))) := by
  have h := triple_to_offset2 p (w0.extractLsb' 16 48 ++ h16) w1 (t32 ++ t16 ++ w2.extractLsb' 0 16)
  have e1 : (w0.extractLsb' 16 48 ++ h16).extractLsb' 0 16 = h16 := by bv_bits
  have e2 : (w0.extractLsb' 16 48 ++ h16).extractLsb' 16 48 = w0.extractLsb' 16 48 := by bv_bits
  have e3 : (t32 ++ t16 ++ w2.extractLsb' 0 16).extractLsb' 0 16 = w2.extractLsb' 0 16 := by bv_bits
  have e4 : (t32 ++ t16 ++ w2.extractLsb' 0 16).extractLsb' 16 16 = t16 := by bv_bits
  have e5 : (t32 ++ t16 ++ w2.extractLsb' 0 16).extractLsb' 32 32 = t32 := by bv_bits
  rw [e1, e2, e3, e4, e5] at h
  exact h.symm

theorem rejoin64_16_48 (w : BitVec 64) : w.extractLsb' 16 48 ++ w.extractLsb' 0 16 = w := by
  bv_bits

theorem rejoin64_32_16_16 (w : BitVec 64) :
    w.extractLsb' 32 32 ++ w.extractLsb' 16 16 ++ w.extractLsb' 0 16 = w := by
  bv_bits

theorem zeroExtend8_16 (x : BitVec 16) : BitVec.zeroExtend 8 x = x.extractLsb' 0 8 := by
  bv_bits

theorem zeroExtend8_16_hi (x : BitVec 16) :
    BitVec.zeroExtend 8 (BitVec.zeroExtend 64 x >>> 8) = x.extractLsb' 8 8 := by
  bv_bits

abbrev readBytes_add := @Memory.readBytes_add
abbrev readBytes_take_drop := @Memory.readBytes_take_drop
abbrev readBytes_writeBytes_slice := @Memory.readBytes_writeBytes_slice
abbrev readBytes_writeBytes_take := @Memory.readBytes_writeBytes_take
abbrev readBytes_writeBytes_prefix := @Memory.readBytes_writeBytes_prefix
abbrev readBytes_eq_of_read8_eq := @Memory.readBytes_eq_of_read8_eq
abbrev read8_of_readBytes := @Memory.read8_of_readBytes
abbrev read16_of_readBytes := @Memory.read16_of_readBytes
abbrev read32_of_readBytes := @Memory.read32_of_readBytes
abbrev read64_of_readBytes := @Memory.read64_of_readBytes
abbrev read64_of_readBytes_eq_unpack64 := @Memory.read64_of_readBytes_eq_unpack64

set_option allowUnsafeReducibility true in
attribute [local semireducible]
  SepProp.Satisfies SepProp.sepConj Heap.Disjoint Heap.union regionHeap regionHeapRO in
/-- A read-only byte slice separated from a nonempty writable region has length `< 2 ^ 64`. -/
theorem pointsToBytesRO_len_lt_of_sepConj_memRegion {m : Memory} {a b : BitVec 64}
    {bs : List (BitVec 8)} {n : Nat} {R : SepProp}
    (hn : 0 < n) (h : m ⊨ (a ↦ᵣ bs) ∗ (memRegion b n ∗ R)) :
    bs.length < 2 ^ 64 := by
  apply Classical.byContradiction
  intro hge
  have hge' : 2 ^ 64 ≤ bs.length := by omega
  have htk : (bs.take (2 ^ 64)).length = 2 ^ 64 := by simp; omega
  rw [← List.take_append_drop (2 ^ 64) bs, pointsToBytesRO_append, sepConj_assoc] at h
  simp only [SepProp.satisfies_iff, SepProp.holds_sepConj_iff] at h
  rcases h with ⟨_, ⟨h₁, h₂, hd, rfl, hp₁, ⟨h₃, h₄, hd2, rfl, _, ⟨h₅, h₆, _, rfl, hp₅, _⟩⟩⟩, _⟩
  obtain ⟨m₀, _, rfl⟩ :=
    ((IsBlockRO.pointsToBytesRO a (bs.take (2 ^ 64)) (by omega)).iff _).mp hp₁
  have hcov := (IsBlock.memRegion b n).covers hp₅
  unfold Heap.CoversRegion at hcov
  obtain ⟨v, hv⟩ := hcov b
    (by simp only [InRegion, BitVec.sub_self, BitVec.toNat_zero]; omega)
  have hin : InRegion a (bs.take (2 ^ 64)).length b := by
    rw [htk]; exact (b - a).isLt
  have h56 : (h₅.union h₆).phys b = some (.rw v) := by simp [Heap.union, hv]
  have h3 : h₃.phys b = none := by
    unfold Heap.Disjoint at hd2
    rcases hd2.1 b with h | h | ⟨c, _, h⟩
    · exact h
    · rw [h56] at h; cases h
    · rw [h56] at h; cases h
  have hU : (h₃.union (h₅.union h₆)).phys b = some (.rw v) := by
    simp only [Heap.union] at h56 ⊢; rw [h3]; exact h56
  have hR : (regionHeapRO a (bs.take (2 ^ 64)).length m₀).phys b = some (.ro (m₀.read8 b)) := by
    simp only [regionHeapRO, hin, ↓reduceIte]
  unfold Heap.Disjoint at hd
  rcases hd.1 b with h | h | ⟨c, _, h⟩
  · rw [hR] at h; cases h
  · rw [hU] at h; cases h
  · rw [hU] at h; cases h

end ProofLib
