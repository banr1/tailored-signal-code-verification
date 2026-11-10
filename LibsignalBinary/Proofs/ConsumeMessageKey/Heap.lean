/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.Bytes
public import LibsignalBinary.Specifications.LibsignalSessionRepr
import ProofLib.VCGen

/-!
# Separation-Logic Lemmas for `Vec<T>`, `MessageKey`, and `RatchetState`

Structural `SepProp` lemmas for `vecHeader`, `arrayAt`, `vecBuf`, `messageKeyAt`, and `ratchetAt`.
Separates each 104-byte `chain::MessageKey` slot (four 24-byte `Vec<u8>` headers, 4-byte `counter`,
and 4-byte tail padding) from its four detached inner `Vec<u8>` heap buffers (`messageKeyHeap`),
supporting `grow_one`, `insert(0)`, `remove(p)`, `pop`, and receiver-chain updates.
-/

@[expose] public section

namespace CryptoVerification.RustHeap

open Arm64 ProofLib

/-! ## `vecHeader` Byte Representation -/

/-- The 24 little-endian bytes of a `Vec` header `{cap, ptr, len}`. -/
def vecHeaderBytes (cap ptr len : BitVec 64) : List (BitVec 8) :=
  unpack64 cap ++ unpack64 ptr ++ unpack64 len

@[scoped simp]
theorem vecHeaderBytes_length (cap ptr len : BitVec 64) :
    (vecHeaderBytes cap ptr len).length = 24 := by
  simp [vecHeaderBytes]

theorem vecHeader_eq_pointsToBytes (v cap ptr len : BitVec 64) :
    vecHeader v cap ptr len = (v ↦ₛ vecHeaderBytes cap ptr len) := by
  unfold vecHeader vecHeaderBytes
  rw [List.append_assoc, pointsToBytes_append, pointsToBytes_append]
  simp only [unpack64_length]
  rw [← pointsTo64_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes]
  have h16 : v + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 = v + 16#64 := by bv_arith
  rw [h16]

theorem vecHeader_entails_memRegion (v cap ptr len : BitVec 64) :
    vecHeader v cap ptr len ⊢ memRegion v 24 := by
  rw [vecHeader_eq_pointsToBytes]
  have h := pointsToBytes_entails_memRegion v (vecHeaderBytes cap ptr len)
  rwa [vecHeaderBytes_length] at h

theorem memRegion_24_eq_exists_vecHeader (v : BitVec 64) :
    memRegion v 24 = ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ∃∗ len : BitVec 64,
      vecHeader v cap ptr len := by
  rw [show (24 : Nat) = 8 + 16 from rfl, memRegion_split v 8 16 (by decide),
      show (16 : Nat) = 8 + 8 from rfl, memRegion_split (v + 8#64) 8 8 (by decide)]
  have h16 : v + 8#64 + 8#64 = v + 16#64 := by bv_arith
  rw [h16, memRegion_eight v, sepExists_sepConj_left]
  apply congrArg SepProp.sepExists; funext cap
  rw [memRegion_eight (v + 8#64), sepExists_sepConj_left, sepExists_sepConj_right]
  apply congrArg SepProp.sepExists; funext ptr
  rw [memRegion_eight (v + 16#64), sepExists_sepConj_right, sepExists_sepConj_right]
  rfl

/-! ## `arrayAt` Structural Lemmas -/

@[scoped simp]
theorem arrayAt_nil {α : Type} (elem : α → BitVec 64 → SepProp) (stride : Nat) (base : BitVec 64) :
    arrayAt elem stride base [] = emp := rfl

@[scoped simp]
theorem arrayAt_cons {α : Type} (elem : α → BitVec 64 → SepProp) (stride : Nat)
    (base : BitVec 64) (x : α) (xs : List α) :
    arrayAt elem stride base (x :: xs) =
      elem x base ∗ arrayAt elem stride (base + BitVec.ofNat 64 stride) xs := rfl

theorem arrayAt_singleton {α : Type} (elem : α → BitVec 64 → SepProp) (stride : Nat)
    (base : BitVec 64) (x : α) :
    arrayAt elem stride base [x] = elem x base := by
  simp [arrayAt]

theorem arrayAt_congr {α : Type} {elem₁ elem₂ : α → BitVec 64 → SepProp} (stride : Nat)
    (base : BitVec 64) {xs : List α}
    (h : ∀ x ∈ xs, ∀ a, elem₁ x a = elem₂ x a) :
    arrayAt elem₁ stride base xs = arrayAt elem₂ stride base xs := by
  induction xs generalizing base with
  | nil => rfl
  | cons x xs ih =>
    simp only [arrayAt_cons]
    rw [h x (List.Mem.head _) base,
        ih (base + BitVec.ofNat 64 stride) (fun y hy => h y (List.Mem.tail _ hy))]

theorem arrayAt_mono {α : Type} {elem₁ elem₂ : α → BitVec 64 → SepProp} (stride : Nat)
    (base : BitVec 64) {xs : List α}
    (h : ∀ x ∈ xs, ∀ a, elem₁ x a ⊢ elem₂ x a) :
    arrayAt elem₁ stride base xs ⊢ arrayAt elem₂ stride base xs := by
  induction xs generalizing base with
  | nil => exact Entails.refl _
  | cons x xs ih =>
    simp only [arrayAt_cons]
    exact sepConj_mono (h x (List.Mem.head _) base)
      (ih (base + BitVec.ofNat 64 stride) (fun y hy => h y (List.Mem.tail _ hy)))

private theorem addr_stride_succ (base : BitVec 64) (n stride : Nat) :
    base + BitVec.ofNat 64 stride + BitVec.ofNat 64 (n * stride) =
      base + BitVec.ofNat 64 ((n + 1) * stride) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  have h : stride + n * stride = (n + 1) * stride := by
    rw [Nat.succ_mul, Nat.add_comm]
  rw [h]

theorem arrayAt_append {α : Type} (elem : α → BitVec 64 → SepProp) (stride : Nat)
    (base : BitVec 64) (xs ys : List α) :
    arrayAt elem stride base (xs ++ ys) =
      arrayAt elem stride base xs ∗
        arrayAt elem stride (base + BitVec.ofNat 64 (xs.length * stride)) ys := by
  induction xs generalizing base with
  | nil =>
    simp [arrayAt]
  | cons x xs ih =>
    rw [List.cons_append, arrayAt_cons, arrayAt_cons, ih, sepConj_assoc]
    simp only [List.length_cons]
    rw [addr_stride_succ]

theorem arrayAt_append' {α : Type} (elem : α → BitVec 64 → SepProp) (stride : Nat)
    (base : BitVec 64) (xs ys : List α) :
    arrayAt elem stride base (xs ++ ys) =
      arrayAt elem stride base xs ∗
        arrayAt elem stride (base + BitVec.ofNat 64 (stride * xs.length)) ys := by
  rw [Nat.mul_comm stride xs.length, arrayAt_append]

theorem arrayAt_concat {α : Type} (elem : α → BitVec 64 → SepProp) (stride : Nat)
    (base : BitVec 64) (xs : List α) (x : α) :
    arrayAt elem stride base (xs ++ [x]) =
      arrayAt elem stride base xs ∗
        elem x (base + BitVec.ofNat 64 (xs.length * stride)) := by
  rw [arrayAt_append, arrayAt_singleton]

theorem arrayAt_take_drop {α : Type} (elem : α → BitVec 64 → SepProp) (stride : Nat)
    (base : BitVec 64) (xs : List α) (i : Nat) :
    arrayAt elem stride base xs =
      arrayAt elem stride base (xs.take i) ∗
        arrayAt elem stride (base + BitVec.ofNat 64 ((xs.take i).length * stride)) (xs.drop i) := by
  conv => lhs; rw [← List.take_append_drop i xs]
  exact arrayAt_append elem stride base (xs.take i) (xs.drop i)

theorem arrayAt_take_drop_of_le {α : Type} (elem : α → BitVec 64 → SepProp) (stride : Nat)
    (base : BitVec 64) (xs : List α) {i : Nat} (hi : i ≤ xs.length) :
    arrayAt elem stride base xs =
      arrayAt elem stride base (xs.take i) ∗
        arrayAt elem stride (base + BitVec.ofNat 64 (i * stride)) (xs.drop i) := by
  rw [arrayAt_take_drop elem stride base xs i, List.length_take_of_le hi]

/-- Split `arrayAt` at index `i < xs.length` in spatial order: prefix `xs.take i`, element `xs[i]`,
and suffix `xs.drop (i + 1)`. -/
theorem arrayAt_split_at_ordered {α : Type} (elem : α → BitVec 64 → SepProp) (stride : Nat)
    (base : BitVec 64) (xs : List α) {i : Nat} (hi : i < xs.length) :
    arrayAt elem stride base xs =
      arrayAt elem stride base (xs.take i) ∗
        elem xs[i] (base + BitVec.ofNat 64 (i * stride)) ∗
        arrayAt elem stride (base + BitVec.ofNat 64 ((i + 1) * stride)) (xs.drop (i + 1)) := by
  rw [arrayAt_take_drop_of_le elem stride base xs (Nat.le_of_lt hi)]
  have hdrop : xs.drop i = xs[i] :: xs.drop (i + 1) := List.drop_eq_getElem_cons hi
  rw [hdrop, arrayAt_cons]
  have hadj : base + BitVec.ofNat 64 (i * stride) + BitVec.ofNat 64 stride =
      base + BitVec.ofNat 64 ((i + 1) * stride) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.succ_mul]
  rw [hadj]

/-- Split `arrayAt` at index `i < xs.length`, focusing `elem xs[i] (base + BitVec.ofNat 64 (i * stride))`
on the left and grouping the prefix and suffix frame on the right. -/
theorem arrayAt_split_at {α : Type} (elem : α → BitVec 64 → SepProp) (stride : Nat)
    (base : BitVec 64) (xs : List α) {i : Nat} (hi : i < xs.length) :
    arrayAt elem stride base xs =
      elem xs[i] (base + BitVec.ofNat 64 (i * stride)) ∗
        (arrayAt elem stride base (xs.take i) ∗
         arrayAt elem stride (base + BitVec.ofNat 64 ((i + 1) * stride)) (xs.drop (i + 1))) := by
  rw [arrayAt_split_at_ordered elem stride base xs hi]
  ac_rfl

/-- Reassemble `arrayAt` after replacing element `i < xs.length` with `x'` (`xs.set i x'`). -/
theorem arrayAt_set {α : Type} (elem : α → BitVec 64 → SepProp) (stride : Nat)
    (base : BitVec 64) (xs : List α) {i : Nat} (hi : i < xs.length) (x' : α) :
    (elem x' (base + BitVec.ofNat 64 (i * stride)) ∗
      (arrayAt elem stride base (xs.take i) ∗
       arrayAt elem stride (base + BitVec.ofNat 64 ((i + 1) * stride)) (xs.drop (i + 1)))) =
      arrayAt elem stride base (xs.set i x') := by
  have hi' : i < (xs.set i x').length := by simp [hi]
  rw [arrayAt_split_at elem stride base (xs.set i x') hi']
  simp [List.take_set_of_le, List.drop_set_of_lt]

theorem arrayAt_set_ordered {α : Type} (elem : α → BitVec 64 → SepProp) (stride : Nat)
    (base : BitVec 64) (xs : List α) {i : Nat} (hi : i < xs.length) (x' : α) :
    (arrayAt elem stride base (xs.take i) ∗
      elem x' (base + BitVec.ofNat 64 (i * stride)) ∗
      arrayAt elem stride (base + BitVec.ofNat 64 ((i + 1) * stride)) (xs.drop (i + 1))) =
      arrayAt elem stride base (xs.set i x') := by
  rw [← arrayAt_set elem stride base xs hi x']
  ac_rfl

/-- `arrayAt` over `xs.eraseIdx p` (`p < xs.length`) splits into `xs.take p` at `base` and
`xs.drop (p + 1)` at `base + BitVec.ofNat 64 (p * stride)`. -/
theorem arrayAt_eraseIdx {α : Type} (elem : α → BitVec 64 → SepProp) (stride : Nat)
    (base : BitVec 64) (xs : List α) {p : Nat} (hp : p < xs.length) :
    arrayAt elem stride base (xs.eraseIdx p) =
      arrayAt elem stride base (xs.take p) ∗
        arrayAt elem stride (base + BitVec.ofNat 64 (p * stride)) (xs.drop (p + 1)) := by
  rw [List.eraseIdx_eq_take_drop_succ, arrayAt_append, List.length_take_of_le (Nat.le_of_lt hp)]

/-- Split `arrayAt` at the last element when `xs.length = n + 1` (for `Vec::pop`). -/
theorem arrayAt_split_of_length_succ {α : Type} (elem : α → BitVec 64 → SepProp) (stride : Nat)
    (base : BitVec 64) (xs : List α) {n : Nat} (hlen : xs.length = n + 1) :
    arrayAt elem stride base xs =
      arrayAt elem stride base (xs.take n) ∗
        elem (xs[n]'(by omega)) (base + BitVec.ofNat 64 (n * stride)) := by
  have hn : n < xs.length := by omega
  rw [arrayAt_split_at_ordered elem stride base xs hn]
  have hdrop : xs.drop (n + 1) = [] := List.drop_eq_nil_of_le (by omega)
  rw [hdrop, arrayAt_nil, sepConj_emp]

theorem arrayAt_split_last {α : Type} (elem : α → BitVec 64 → SepProp) (stride : Nat)
    (base : BitVec 64) (xs : List α) (hne : xs ≠ []) :
    arrayAt elem stride base xs =
      arrayAt elem stride base (xs.take (xs.length - 1)) ∗
        elem (xs[xs.length - 1]'(Nat.sub_one_lt (List.length_pos_of_ne_nil hne).ne'))
          (base + BitVec.ofNat 64 ((xs.length - 1) * stride)) := by
  have hpos : 0 < xs.length := List.length_pos_of_ne_nil hne
  exact arrayAt_split_of_length_succ elem stride base xs (n := xs.length - 1) (by omega)

theorem arrayAt_split_dropLast {α : Type} (elem : α → BitVec 64 → SepProp) (stride : Nat)
    (base : BitVec 64) (xs : List α) (hne : xs ≠ []) :
    arrayAt elem stride base xs =
      arrayAt elem stride base xs.dropLast ∗
        elem (xs.getLast hne) (base + BitVec.ofNat 64 (xs.dropLast.length * stride)) := by
  conv => lhs; rw [← List.dropLast_append_getLast hne]
  exact arrayAt_concat elem stride base xs.dropLast (xs.getLast hne)

/-- `a ↦ₛ bs` agrees with `arrayAt` of 1-byte cells `fun b addr => addr ↦₈ b` with stride 1. -/
theorem pointsToBytes_eq_arrayAt (a : BitVec 64) (bs : List (BitVec 8)) :
    (a ↦ₛ bs) = arrayAt (fun b addr => addr ↦₈ b) 1 a bs := by
  induction bs generalizing a with
  | nil => rw [pointsToBytes_nil, arrayAt_nil]
  | cons b bs ih =>
    rw [pointsToBytes_cons, arrayAt_cons, ih]

/-! ## `vecBuf`, `vecAt`, `vecU8Buf`, and `vecU8At` Lemmas -/

/-- When `cap = 0`, `vecBuf` holds iff `xs = []` and `ptr ≠ 0` (the dangling pointer). -/
theorem vecBuf_zero {α : Type} (A : RustAlloc) (stride align : Nat)
    (elem : α → BitVec 64 → SepProp) (ptr : BitVec 64) (xs : List α) :
    vecBuf A stride align elem 0 ptr xs = ⌜xs = [] ∧ ptr ≠ 0⌝ := by
  unfold vecBuf
  simp only [↓reduceIte, sepConj_emp]
  congr 1
  apply propext
  change (xs.length ≤ 0 ∧ 0 * stride < 2 ^ 63 ∧ ptr ≠ 0) ↔ (xs = [] ∧ ptr ≠ 0)
  constructor
  · rintro ⟨hlen, _, hptr⟩
    exact ⟨List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hlen), hptr⟩
  · rintro ⟨rfl, hptr⟩
    exact ⟨Nat.le_refl 0, by omega, hptr⟩

theorem vecBuf_of_ne_zero {α : Type} (A : RustAlloc) (stride align : Nat)
    (elem : α → BitVec 64 → SepProp) (cap ptr : BitVec 64) (xs : List α) (hcap : cap ≠ 0) :
    vecBuf A stride align elem cap ptr xs =
      ⌜xs.length ≤ cap.toNat ∧ cap.toNat * stride < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        A.live ptr (cap.toNat * stride) align ∗ arrayAt elem stride ptr xs ∗
        memRegion (ptr + BitVec.ofNat 64 (xs.length * stride)) ((cap.toNat - xs.length) * stride) := by
  unfold vecBuf
  simp only [hcap, ↓reduceIte]

/-- Pull `arrayAt elem stride ptr xs` and `xs.length * stride < 2 ^ 63` outside the `if cap = 0`
branch of `vecBuf` (valid for any `cap`, since `cap = 0` forces `xs = []`). -/
theorem vecBuf_expose_arrayAt {α : Type} (A : RustAlloc) (stride align : Nat)
    (elem : α → BitVec 64 → SepProp) (cap ptr : BitVec 64) (xs : List α) :
    vecBuf A stride align elem cap ptr xs ⊢
      ⌜xs.length ≤ cap.toNat ∧ cap.toNat * stride < 2 ^ 63 ∧ xs.length * stride < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        arrayAt elem stride ptr xs ∗
        (if cap = 0 then emp
         else A.live ptr (cap.toNat * stride) align ∗
           memRegion (ptr + BitVec.ofNat 64 (xs.length * stride)) ((cap.toNat - xs.length) * stride)) := by
  unfold vecBuf
  apply Entails.pure_left
  rintro ⟨hlen, hlt, hptr⟩
  have hxs_lt : xs.length * stride < 2 ^ 63 :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_right stride hlen) hlt
  apply Entails.pure_right ⟨hlen, hlt, hxs_lt, hptr⟩
  by_cases hcap : cap = 0
  · subst hcap
    have hnil : xs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    subst hnil
    simp only [↓reduceIte, arrayAt_nil, emp_sepConj]
    exact Entails.refl _
  · simp only [hcap, ↓reduceIte]
    have hpull :
        (A.live ptr (cap.toNat * stride) align ∗ arrayAt elem stride ptr xs ∗
          memRegion (ptr + BitVec.ofNat 64 (xs.length * stride)) ((cap.toNat - xs.length) * stride)) =
        (arrayAt elem stride ptr xs ∗
          (A.live ptr (cap.toNat * stride) align ∗
            memRegion (ptr + BitVec.ofNat 64 (xs.length * stride)) ((cap.toNat - xs.length) * stride))) := by
      ac_rfl
    rw [hpull]
    exact Entails.refl _

/-- Extract element `i < xs.length` from `vecBuf` (since `i < xs.length`, `cap ≠ 0` holds automatically). -/
theorem vecBuf_split_at {α : Type} (A : RustAlloc) (stride align : Nat)
    (elem : α → BitVec 64 → SepProp) (cap ptr : BitVec 64) (xs : List α)
    {i : Nat} (hi : i < xs.length) :
    vecBuf A stride align elem cap ptr xs ⊢
      elem xs[i] (ptr + BitVec.ofNat 64 (i * stride)) ∗
        (⌜xs.length ≤ cap.toNat ∧ cap.toNat * stride < 2 ^ 63 ∧ ptr ≠ 0 ∧ cap ≠ 0⌝ ∗
          A.live ptr (cap.toNat * stride) align ∗
          (arrayAt elem stride ptr (xs.take i) ∗
           arrayAt elem stride (ptr + BitVec.ofNat 64 ((i + 1) * stride)) (xs.drop (i + 1))) ∗
          memRegion (ptr + BitVec.ofNat 64 (xs.length * stride)) ((cap.toNat - xs.length) * stride)) := by
  unfold vecBuf
  apply Entails.pure_left
  rintro ⟨hlen, hlt, hptr⟩
  have hcap : cap ≠ 0 := by intro h0; rw [h0] at hlen; change xs.length ≤ 0 at hlen; omega
  simp only [hcap, ↓reduceIte, arrayAt_split_at elem stride ptr xs hi]
  have hpull :
      (A.live ptr (cap.toNat * stride) align ∗
        (elem xs[i] (ptr + BitVec.ofNat 64 (i * stride)) ∗
          (arrayAt elem stride ptr (xs.take i) ∗
           arrayAt elem stride (ptr + BitVec.ofNat 64 ((i + 1) * stride)) (xs.drop (i + 1)))) ∗
        memRegion (ptr + BitVec.ofNat 64 (xs.length * stride)) ((cap.toNat - xs.length) * stride)) =
      (elem xs[i] (ptr + BitVec.ofNat 64 (i * stride)) ∗
        (A.live ptr (cap.toNat * stride) align ∗
          (arrayAt elem stride ptr (xs.take i) ∗
           arrayAt elem stride (ptr + BitVec.ofNat 64 ((i + 1) * stride)) (xs.drop (i + 1))) ∗
          memRegion (ptr + BitVec.ofNat 64 (xs.length * stride)) ((cap.toNat - xs.length) * stride))) := by
    ac_rfl
  rw [hpull]
  exact sepConj_mono_right (Entails.pure_right ⟨hlen, hlt, hptr, hcap⟩ (Entails.refl _))

/-- Reassemble `vecBuf` after replacing element `i < xs.length` with `x'` (`xs.set i x'`). -/
theorem vecBuf_set {α : Type} (A : RustAlloc) (stride align : Nat)
    (elem : α → BitVec 64 → SepProp) (cap ptr : BitVec 64) (xs : List α)
    {i : Nat} (hi : i < xs.length) (x' : α) :
    (elem x' (ptr + BitVec.ofNat 64 (i * stride)) ∗
      (⌜xs.length ≤ cap.toNat ∧ cap.toNat * stride < 2 ^ 63 ∧ ptr ≠ 0 ∧ cap ≠ 0⌝ ∗
        A.live ptr (cap.toNat * stride) align ∗
        (arrayAt elem stride ptr (xs.take i) ∗
         arrayAt elem stride (ptr + BitVec.ofNat 64 ((i + 1) * stride)) (xs.drop (i + 1))) ∗
        memRegion (ptr + BitVec.ofNat 64 (xs.length * stride)) ((cap.toNat - xs.length) * stride))) ⊢
      vecBuf A stride align elem cap ptr (xs.set i x') := by
  rw [sepConj_pure_left_comm]
  apply Entails.pure_left
  rintro ⟨hlen, hlt, hptr, hcap⟩
  rw [vecBuf_of_ne_zero A stride align elem cap ptr (xs.set i x') hcap,
      List.length_set, ← arrayAt_set elem stride ptr xs hi x']
  apply Entails.pure_right ⟨hlen, hlt, hptr⟩
  have hpull :
      (elem x' (ptr + BitVec.ofNat 64 (i * stride)) ∗
        (A.live ptr (cap.toNat * stride) align ∗
          (arrayAt elem stride ptr (xs.take i) ∗
           arrayAt elem stride (ptr + BitVec.ofNat 64 ((i + 1) * stride)) (xs.drop (i + 1))) ∗
          memRegion (ptr + BitVec.ofNat 64 (xs.length * stride)) ((cap.toNat - xs.length) * stride))) =
      (A.live ptr (cap.toNat * stride) align ∗
        (elem x' (ptr + BitVec.ofNat 64 (i * stride)) ∗
          (arrayAt elem stride ptr (xs.take i) ∗
           arrayAt elem stride (ptr + BitVec.ofNat 64 ((i + 1) * stride)) (xs.drop (i + 1)))) ∗
        memRegion (ptr + BitVec.ofNat 64 (xs.length * stride)) ((cap.toNat - xs.length) * stride)) := by
    ac_rfl
  rw [hpull]
  exact Entails.refl _

theorem vecAt_entails_vecOf {α : Type} (A : RustAlloc) (stride align : Nat)
    (elem : α → BitVec 64 → SepProp) (v cap ptr : BitVec 64) (xs : List α) :
    vecAt A stride align elem v cap ptr xs ⊢ vecOf A stride align elem v xs := by
  unfold vecOf
  exact Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.refl _))

/-- Heap buffer of a `Vec<u8>` detached from its 24-byte `vecHeader`, invariant under moving or
copying the header. -/
def vecU8Buf (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))

/-- `vecU8At` splits into its 24-byte `vecHeader` at `v` and its detached heap buffer `vecU8Buf`. -/
theorem vecU8At_eq_header_sep_buf (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs = vecHeader v cap ptr (BitVec.ofNat 64 bs.length) ∗ vecU8Buf A cap ptr bs := by
  unfold vecU8At vecU8Buf
  ac_rfl

/-- `vecU8At` agrees with `vecAt` at `stride = 1` and `align = 1`. -/
theorem vecU8At_eq_vecAt (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs = vecAt A 1 1 (fun b addr => addr ↦₈ b) v cap ptr bs := by
  unfold vecU8At vecAt vecBuf
  simp only [Nat.mul_one, ← pointsToBytes_eq_arrayAt]

theorem vecU8At_entails_vecU8 (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs ⊢ vecU8 A v bs := by
  unfold vecU8
  exact Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.refl _))

/-- A `vecU8Buf` collapses its contents and spare capacity into a single `memRegion ptr cap.toNat`
for `__rust_dealloc` (`rustDeallocSpec A`). -/
theorem vecU8Buf_entails_dealloc (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8Buf A cap ptr bs ⊢
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (if cap = 0 then emp else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) := by
  unfold vecU8Buf
  apply Entails.pure_left
  rintro ⟨hlen, hcap_lt, hptr⟩
  apply Entails.pure_right ⟨hlen, hcap_lt, hptr⟩
  by_cases hcap : cap = 0
  · simp only [hcap, ↓reduceIte]
    exact Entails.refl _
  · simp only [hcap, ↓reduceIte]
    apply sepConj_mono_right
    have hsplit : cap.toNat = bs.length + (cap.toNat - bs.length) := by omega
    conv => rhs; rw [hsplit, memRegion_split ptr bs.length (cap.toNat - bs.length) (by omega)]
    exact sepConj_mono_left (pointsToBytes_entails_memRegion ptr bs)

/-- `vecU8At` exposes its header and collapses its heap buffer for `__rust_dealloc`. -/
theorem vecU8At_entails_dealloc (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs ⊢
      vecHeader v cap ptr (BitVec.ofNat 64 bs.length) ∗
        (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
          (if cap = 0 then emp else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat)) := by
  rw [vecU8At_eq_header_sep_buf]
  exact sepConj_mono_right (vecU8Buf_entails_dealloc A cap ptr bs)

end CryptoVerification.RustHeap

namespace CryptoVerification.LibsignalSessionRepr

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap

/-! ## `messageKeyAt` Flat-Byte and Detached-Heap Decomposition -/

/-- The 100-byte struct header of a stored `chain::MessageKey` (before its 4-byte tail padding):
four 24-byte `Vec<u8>` headers (`cipher`, `mac`, `iv` with length 0; `seed` with length
`gk.2.seed.length`) followed by the 4-byte little-endian `counter`. -/
def messageKeyHeaderBytes (gk : MessageKeyGhost × MessageKeyGenerator) : List (BitVec 8) :=
  vecHeaderBytes gk.1.cipher.cap gk.1.cipher.ptr 0#64 ++
    (vecHeaderBytes gk.1.mac.cap gk.1.mac.ptr 0#64 ++
      (vecHeaderBytes gk.1.iv.cap gk.1.iv.ptr 0#64 ++
        (vecHeaderBytes gk.1.seed.cap gk.1.seed.ptr (BitVec.ofNat 64 gk.2.seed.length) ++
          unpack32 gk.2.counter)))

@[local simp]
theorem messageKeyHeaderBytes_length (gk : MessageKeyGhost × MessageKeyGenerator) :
    (messageKeyHeaderBytes gk).length = 100 := by
  simp [messageKeyHeaderBytes]

/-- The full 104-byte in-buffer representation of a `chain::MessageKey` with 4-byte tail padding `pad`. -/
def messageKeyBytes (gk : MessageKeyGhost × MessageKeyGenerator) (pad : List (BitVec 8)) :
    List (BitVec 8) :=
  messageKeyHeaderBytes gk ++ pad

theorem messageKeyBytes_length (gk : MessageKeyGhost × MessageKeyGenerator) {pad : List (BitVec 8)}
    (hpad : pad.length = 4) :
    (messageKeyBytes gk pad).length = 104 := by
  simp [messageKeyBytes, hpad]

/-- Detached heap allocations owned by the four inner `Vec<u8>` fields of a `chain::MessageKey`
together with `gk.2.seed ≠ []`, independent of the struct's buffer address. -/
def messageKeyHeap (A : RustAlloc) (gk : MessageKeyGhost × MessageKeyGenerator) : SepProp :=
  ⌜gk.2.seed ≠ []⌝ ∗
    vecU8Buf A gk.1.cipher.cap gk.1.cipher.ptr [] ∗
    vecU8Buf A gk.1.mac.cap gk.1.mac.ptr [] ∗
    vecU8Buf A gk.1.iv.cap gk.1.iv.ptr [] ∗
    vecU8Buf A gk.1.seed.cap gk.1.seed.ptr gk.2.seed

/-- The 100-byte slice `a ↦ₛ messageKeyHeaderBytes gk` is equal to the four `vecHeader`s at
offsets `+0`, `+24`, `+48`, `+72` and the 32-bit `counter` at `+96`. -/
theorem pointsToBytes_messageKeyHeaderBytes (gk : MessageKeyGhost × MessageKeyGenerator)
    (a : BitVec 64) :
    (a ↦ₛ messageKeyHeaderBytes gk) =
      vecHeader a gk.1.cipher.cap gk.1.cipher.ptr 0#64 ∗
        vecHeader (a + 24#64) gk.1.mac.cap gk.1.mac.ptr 0#64 ∗
        vecHeader (a + 48#64) gk.1.iv.cap gk.1.iv.ptr 0#64 ∗
        vecHeader (a + 72#64) gk.1.seed.cap gk.1.seed.ptr (BitVec.ofNat 64 gk.2.seed.length) ∗
        ((a + 96#64) ↦₃₂ gk.2.counter) := by
  unfold messageKeyHeaderBytes
  rw [pointsToBytes_append, pointsToBytes_append, pointsToBytes_append, pointsToBytes_append]
  simp only [vecHeaderBytes_length]
  rw [← vecHeader_eq_pointsToBytes, ← vecHeader_eq_pointsToBytes,
      ← vecHeader_eq_pointsToBytes, ← vecHeader_eq_pointsToBytes,
      ← pointsTo32_eq_pointsToBytes]
  have h24 : a + BitVec.ofNat 64 24 = a + 24#64 := rfl
  have h48 : a + BitVec.ofNat 64 24 + BitVec.ofNat 64 24 = a + 48#64 := by bv_arith
  have h72 : a + BitVec.ofNat 64 24 + BitVec.ofNat 64 24 + BitVec.ofNat 64 24 = a + 72#64 := by bv_arith
  have h96 : a + BitVec.ofNat 64 24 + BitVec.ofNat 64 24 + BitVec.ofNat 64 24 + BitVec.ofNat 64 24 =
      a + 96#64 := by bv_arith
  rw [h96, h72, h48, h24]

/-- The 100-byte header plus 4-byte padding `memRegion (a + 100#64) 4` equals an existential
104-byte slice `a ↦ₛ messageKeyBytes gk pad` with `pad.length = 4`. -/
theorem messageKeyHeader_pad_eq_exists_bytes (gk : MessageKeyGhost × MessageKeyGenerator)
    (a : BitVec 64) :
    ((a ↦ₛ messageKeyHeaderBytes gk) ∗ memRegion (a + 100#64) 4) =
      ∃∗ pad : List (BitVec 8), ⌜pad.length = 4⌝ ∗ (a ↦ₛ messageKeyBytes gk pad) := by
  rw [memRegion_eq_exists_bytes (a + 100#64) 4 (by decide), sepExists_sepConj_right]
  apply congrArg SepProp.sepExists
  funext pad
  have h100 : a + 100#64 = a + BitVec.ofNat 64 (messageKeyHeaderBytes gk).length := by
    rw [messageKeyHeaderBytes_length]
  rw [sepConj_pure_left_comm, h100, ← pointsToBytes_append]
  rfl

/-- Decompose `messageKeyAt A gk a` into its four 24-byte `vecHeader`s, 32-bit `counter`,
4-byte padding `memRegion`, and the detached heap buffers `messageKeyHeap A gk`. -/
theorem messageKeyAt_eq_headers_sep_heap (A : RustAlloc)
    (gk : MessageKeyGhost × MessageKeyGenerator) (a : BitVec 64) :
    messageKeyAt A gk a =
      (vecHeader a gk.1.cipher.cap gk.1.cipher.ptr 0#64 ∗
        vecHeader (a + 24#64) gk.1.mac.cap gk.1.mac.ptr 0#64 ∗
        vecHeader (a + 48#64) gk.1.iv.cap gk.1.iv.ptr 0#64 ∗
        vecHeader (a + 72#64) gk.1.seed.cap gk.1.seed.ptr (BitVec.ofNat 64 gk.2.seed.length) ∗
        ((a + 96#64) ↦₃₂ gk.2.counter) ∗ memRegion (a + 100#64) 4) ∗
      messageKeyHeap A gk := by
  unfold messageKeyAt messageKeyHeap
  rw [vecU8At_eq_header_sep_buf A a,
      vecU8At_eq_header_sep_buf A (a + 24#64),
      vecU8At_eq_header_sep_buf A (a + 48#64),
      vecU8At_eq_header_sep_buf A (a + 72#64)]
  simp only [List.length_nil]
  ac_rfl

/-- Decompose `messageKeyAt A gk a` into a 104-byte block `a ↦ₛ messageKeyBytes gk pad`
(with `pad.length = 4`) and the detached inner `Vec<u8>` buffers `messageKeyHeap A gk`. -/
theorem messageKeyAt_eq_exists_bytes (A : RustAlloc)
    (gk : MessageKeyGhost × MessageKeyGenerator) (a : BitVec 64) :
    messageKeyAt A gk a =
      (∃∗ pad : List (BitVec 8), ⌜pad.length = 4⌝ ∗ (a ↦ₛ messageKeyBytes gk pad)) ∗
        messageKeyHeap A gk := by
  rw [messageKeyAt_eq_headers_sep_heap]
  have hhdr :
      vecHeader a gk.1.cipher.cap gk.1.cipher.ptr 0#64 ∗
        vecHeader (a + 24#64) gk.1.mac.cap gk.1.mac.ptr 0#64 ∗
        vecHeader (a + 48#64) gk.1.iv.cap gk.1.iv.ptr 0#64 ∗
        vecHeader (a + 72#64) gk.1.seed.cap gk.1.seed.ptr (BitVec.ofNat 64 gk.2.seed.length) ∗
        ((a + 96#64) ↦₃₂ gk.2.counter) ∗ memRegion (a + 100#64) 4 =
      (a ↦ₛ messageKeyHeaderBytes gk) ∗ memRegion (a + 100#64) 4 := by
    rw [pointsToBytes_messageKeyHeaderBytes]
    ac_rfl
  rw [hhdr, messageKeyHeader_pad_eq_exists_bytes]

/-- Reassemble `messageKeyAt A gk a` from a 104-byte slice `a ↦ₛ messageKeyBytes gk pad`
(`pad.length = 4`) and `messageKeyHeap A gk`. -/
theorem messageKeyAt_of_bytes (A : RustAlloc) (gk : MessageKeyGhost × MessageKeyGenerator)
    (a : BitVec 64) {pad : List (BitVec 8)} (hpad : pad.length = 4) :
    ((a ↦ₛ messageKeyBytes gk pad) ∗ messageKeyHeap A gk) ⊢ messageKeyAt A gk a := by
  rw [messageKeyAt_eq_exists_bytes]
  apply sepConj_mono_left
  exact Entails.sepExists_right pad (Entails.pure_right hpad (Entails.refl _))

/-- Reassemble `messageKeyAt A gk a` from the 100-byte header `a ↦ₛ messageKeyHeaderBytes gk`,
4-byte padding `memRegion (a + 100#64) 4`, and `messageKeyHeap A gk`. -/
theorem messageKeyAt_of_header_bytes (A : RustAlloc) (gk : MessageKeyGhost × MessageKeyGenerator)
    (a : BitVec 64) :
    (((a ↦ₛ messageKeyHeaderBytes gk) ∗ memRegion (a + 100#64) 4) ∗ messageKeyHeap A gk) ⊢
      messageKeyAt A gk a := by
  rw [messageKeyAt_eq_exists_bytes, messageKeyHeader_pad_eq_exists_bytes]
  exact Entails.refl _

/-- Forgetting the 104-byte in-buffer contents of `messageKeyAt` leaves `memRegion a 104`
and the detached inner `Vec<u8>` heap buffers `messageKeyHeap A gk`. -/
theorem messageKeyAt_entails_memRegion_sep_heap (A : RustAlloc)
    (gk : MessageKeyGhost × MessageKeyGenerator) (a : BitVec 64) :
    messageKeyAt A gk a ⊢ memRegion a 104 ∗ messageKeyHeap A gk := by
  rw [messageKeyAt_eq_exists_bytes]
  apply sepConj_mono_left
  apply Entails.sepExists_elim
  intro pad
  apply Entails.pure_left
  intro hpad
  have h := pointsToBytes_entails_memRegion a (messageKeyBytes gk pad)
  rwa [messageKeyBytes_length gk hpad] at h

/-- Collapse the four inner `Vec<u8>` heap buffers of `messageKeyHeap A gk` into their
`__rust_dealloc` preconditions (`if cap = 0 then emp else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat`). -/
theorem messageKeyHeap_entails_dealloc (A : RustAlloc)
    (gk : MessageKeyGhost × MessageKeyGenerator) :
    messageKeyHeap A gk ⊢
      ⌜gk.2.seed ≠ []⌝ ∗
        (⌜0 ≤ gk.1.cipher.cap.toNat ∧ gk.1.cipher.cap.toNat < 2 ^ 63 ∧ gk.1.cipher.ptr ≠ 0⌝ ∗
          (if gk.1.cipher.cap = 0 then emp
           else A.live gk.1.cipher.ptr gk.1.cipher.cap.toNat 1 ∗
             memRegion gk.1.cipher.ptr gk.1.cipher.cap.toNat)) ∗
        (⌜0 ≤ gk.1.mac.cap.toNat ∧ gk.1.mac.cap.toNat < 2 ^ 63 ∧ gk.1.mac.ptr ≠ 0⌝ ∗
          (if gk.1.mac.cap = 0 then emp
           else A.live gk.1.mac.ptr gk.1.mac.cap.toNat 1 ∗
             memRegion gk.1.mac.ptr gk.1.mac.cap.toNat)) ∗
        (⌜0 ≤ gk.1.iv.cap.toNat ∧ gk.1.iv.cap.toNat < 2 ^ 63 ∧ gk.1.iv.ptr ≠ 0⌝ ∗
          (if gk.1.iv.cap = 0 then emp
           else A.live gk.1.iv.ptr gk.1.iv.cap.toNat 1 ∗
             memRegion gk.1.iv.ptr gk.1.iv.cap.toNat)) ∗
        (⌜gk.2.seed.length ≤ gk.1.seed.cap.toNat ∧ gk.1.seed.cap.toNat < 2 ^ 63 ∧ gk.1.seed.ptr ≠ 0⌝ ∗
          (if gk.1.seed.cap = 0 then emp
           else A.live gk.1.seed.ptr gk.1.seed.cap.toNat 1 ∗
             memRegion gk.1.seed.ptr gk.1.seed.cap.toNat)) := by
  unfold messageKeyHeap
  apply sepConj_mono_right
  apply sepConj_mono (vecU8Buf_entails_dealloc A gk.1.cipher.cap gk.1.cipher.ptr [])
  apply sepConj_mono (vecU8Buf_entails_dealloc A gk.1.mac.cap gk.1.mac.ptr [])
  exact sepConj_mono (vecU8Buf_entails_dealloc A gk.1.iv.cap gk.1.iv.ptr [])
    (vecU8Buf_entails_dealloc A gk.1.seed.cap gk.1.seed.ptr gk.2.seed)

/-- Detached heap buffers of a list of stored `MessageKey`s, in order. -/
def messageKeyHeaps (A : RustAlloc) : List (MessageKeyGhost × MessageKeyGenerator) → SepProp
  | [] => emp
  | gk :: gks => messageKeyHeap A gk ∗ messageKeyHeaps A gks

@[local simp]
theorem messageKeyHeaps_nil (A : RustAlloc) : messageKeyHeaps A [] = emp := rfl

@[local simp]
theorem messageKeyHeaps_cons (A : RustAlloc) (gk : MessageKeyGhost × MessageKeyGenerator)
    (gks : List (MessageKeyGhost × MessageKeyGenerator)) :
    messageKeyHeaps A (gk :: gks) = messageKeyHeap A gk ∗ messageKeyHeaps A gks := rfl

theorem messageKeyHeaps_append (A : RustAlloc)
    (gks₁ gks₂ : List (MessageKeyGhost × MessageKeyGenerator)) :
    messageKeyHeaps A (gks₁ ++ gks₂) = messageKeyHeaps A gks₁ ∗ messageKeyHeaps A gks₂ := by
  induction gks₁ with
  | nil => simp [messageKeyHeaps]
  | cons gk gks₁ ih =>
    simp only [List.cons_append, messageKeyHeaps_cons, ih, sepConj_assoc]

theorem messageKeyHeaps_take_drop (A : RustAlloc)
    (gks : List (MessageKeyGhost × MessageKeyGenerator)) (i : Nat) :
    messageKeyHeaps A gks =
      messageKeyHeaps A (gks.take i) ∗ messageKeyHeaps A (gks.drop i) := by
  conv => lhs; rw [← List.take_append_drop i gks]
  exact messageKeyHeaps_append A (gks.take i) (gks.drop i)

theorem messageKeyHeaps_split_at (A : RustAlloc)
    (gks : List (MessageKeyGhost × MessageKeyGenerator)) {i : Nat} (hi : i < gks.length) :
    messageKeyHeaps A gks =
      messageKeyHeap A gks[i] ∗ messageKeyHeaps A (gks.eraseIdx i) := by
  rw [messageKeyHeaps_take_drop A gks i, List.drop_eq_getElem_cons hi, messageKeyHeaps_cons,
      List.eraseIdx_eq_take_drop_succ, messageKeyHeaps_append]
  ac_rfl

theorem messageKeyHeaps_split_of_length_succ (A : RustAlloc)
    (gks : List (MessageKeyGhost × MessageKeyGenerator)) {n : Nat} (hlen : gks.length = n + 1) :
    messageKeyHeaps A gks =
      messageKeyHeaps A (gks.take n) ∗ messageKeyHeap A (gks[n]'(by omega)) := by
  have hn : n < gks.length := by omega
  rw [messageKeyHeaps_take_drop A gks n, List.drop_eq_getElem_cons hn, messageKeyHeaps_cons]
  have hdrop : gks.drop (n + 1) = [] := List.drop_eq_nil_of_le (by omega)
  rw [hdrop, messageKeyHeaps_nil, sepConj_emp]

/-- Relates stored `MessageKey`s `gks` to their concatenated 104-byte struct slices `bs`. -/
inductive MessageKeyArrayBytes :
    List (MessageKeyGhost × MessageKeyGenerator) → List (BitVec 8) → Prop
  | nil : MessageKeyArrayBytes [] []
  | cons {gk : MessageKeyGhost × MessageKeyGenerator}
      {gks : List (MessageKeyGhost × MessageKeyGenerator)}
      {pad bs : List (BitVec 8)}
      (hpad : pad.length = 4)
      (hrest : MessageKeyArrayBytes gks bs) :
      MessageKeyArrayBytes (gk :: gks) (messageKeyBytes gk pad ++ bs)

namespace MessageKeyArrayBytes

theorem length_eq {gks : List (MessageKeyGhost × MessageKeyGenerator)} {bs : List (BitVec 8)}
    (h : MessageKeyArrayBytes gks bs) :
    bs.length = gks.length * 104 := by
  induction h with
  | nil => rfl
  | @cons gk gks pad bs hpad _ ih =>
    rw [List.length_append, messageKeyBytes_length gk hpad, ih, List.length_cons, Nat.succ_mul]
    omega

theorem nil_iff {bs : List (BitVec 8)} :
    MessageKeyArrayBytes [] bs ↔ bs = [] := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .nil

theorem append {gks₁ gks₂ : List (MessageKeyGhost × MessageKeyGenerator)}
    {bs₁ bs₂ : List (BitVec 8)}
    (h₁ : MessageKeyArrayBytes gks₁ bs₁) (h₂ : MessageKeyArrayBytes gks₂ bs₂) :
    MessageKeyArrayBytes (gks₁ ++ gks₂) (bs₁ ++ bs₂) := by
  induction h₁ with
  | nil => simpa using h₂
  | @cons gk gks₁ pad bs₁ hpad _ ih =>
    rw [List.cons_append, List.append_assoc]
    exact .cons hpad ih

theorem take_drop {gks : List (MessageKeyGhost × MessageKeyGenerator)} {bs : List (BitVec 8)}
    (h : MessageKeyArrayBytes gks bs) (i : Nat) :
    MessageKeyArrayBytes (gks.take i) (bs.take (i * 104)) ∧
      MessageKeyArrayBytes (gks.drop i) (bs.drop (i * 104)) := by
  induction h generalizing i with
  | nil =>
    simp [MessageKeyArrayBytes.nil]
  | @cons gk gks pad bs' hpad hrest ih =>
    cases i with
    | zero =>
      simp [MessageKeyArrayBytes.nil, MessageKeyArrayBytes.cons hpad hrest]
    | succ k =>
      have hlen : (messageKeyBytes gk pad).length = 104 := messageKeyBytes_length gk hpad
      have hmul : (k + 1) * 104 = (messageKeyBytes gk pad).length + k * 104 := by
        rw [hlen, Nat.succ_mul, Nat.add_comm]
      have hle : (messageKeyBytes gk pad).length ≤ (messageKeyBytes gk pad).length + k * 104 :=
        Nat.le_add_right _ _
      rw [List.take_succ_cons, List.drop_succ_cons, hmul,
          List.take_append, List.drop_append,
          List.take_of_length_le hle, List.drop_eq_nil_of_le hle,
          Nat.add_sub_cancel_left, List.nil_append]
      obtain ⟨ht, hd⟩ := ih k
      exact ⟨.cons hpad ht, hd⟩

theorem take {gks : List (MessageKeyGhost × MessageKeyGenerator)} {bs : List (BitVec 8)}
    (h : MessageKeyArrayBytes gks bs) (i : Nat) :
    MessageKeyArrayBytes (gks.take i) (bs.take (i * 104)) :=
  (h.take_drop i).1

theorem drop {gks : List (MessageKeyGhost × MessageKeyGenerator)} {bs : List (BitVec 8)}
    (h : MessageKeyArrayBytes gks bs) (i : Nat) :
    MessageKeyArrayBytes (gks.drop i) (bs.drop (i * 104)) :=
  (h.take_drop i).2

theorem eraseIdx {gks : List (MessageKeyGhost × MessageKeyGenerator)} {bs : List (BitVec 8)}
    (h : MessageKeyArrayBytes gks bs) {p : Nat} (hp : p < gks.length) :
    MessageKeyArrayBytes (gks.eraseIdx p)
      (bs.take (p * 104) ++ (bs.drop ((p + 1) * 104)).take ((gks.length - 1 - p) * 104)) := by
  rw [List.eraseIdx_eq_take_drop_succ]
  have ht := h.take p
  have hd := h.drop (p + 1)
  have hd_len : (bs.drop ((p + 1) * 104)).length = (gks.length - 1 - p) * 104 := by
    rw [hd.length_eq, List.length_drop]
    have : gks.length - (p + 1) = gks.length - 1 - p := by omega
    rw [this]
  rw [← hd_len, List.take_length]
  exact ht.append hd

private theorem drop_append_mul_104 {α : Type} {l₁ l₂ : List α} (hlen : l₁.length = 104) (m : Nat) :
    (l₁ ++ l₂).drop ((m + 1) * 104) = l₂.drop (m * 104) := by
  rw [Nat.succ_mul, Nat.add_comm, ← hlen, ← List.drop_drop, List.drop_append_length]

/-- Decompose `bs` at element index `p < gks.length` into the prefix `bs.take (p * 104)`,
the 104-byte element `messageKeyBytes gks[p] pad`, and the suffix `bs.drop ((p + 1) * 104)`. -/
theorem split_at {gks : List (MessageKeyGhost × MessageKeyGenerator)} {bs : List (BitVec 8)}
    (h : MessageKeyArrayBytes gks bs) {p : Nat} (hp : p < gks.length) :
    ∃ pad : List (BitVec 8),
      pad.length = 4 ∧
      bs.drop (p * 104) = messageKeyBytes gks[p] pad ++ bs.drop ((p + 1) * 104) := by
  induction h generalizing p with
  | nil => simp at hp
  | @cons gk gks pad₀ bs₀ hpad₀ hrest ih =>
    have hlen : (messageKeyBytes gk pad₀).length = 104 := messageKeyBytes_length gk hpad₀
    cases p with
    | zero =>
      refine ⟨pad₀, hpad₀, ?_⟩
      simp only [Nat.zero_mul, List.drop_zero, List.getElem_cons_zero]
      rw [drop_append_mul_104 hlen 0, Nat.zero_mul, List.drop_zero]
    | succ k =>
      have hk : k < gks.length := Nat.lt_of_succ_lt_succ hp
      obtain ⟨pad, hpad, ih_eq⟩ := ih hk
      refine ⟨pad, hpad, ?_⟩
      rw [drop_append_mul_104 hlen k, drop_append_mul_104 hlen (k + 1), List.getElem_cons_succ]
      exact ih_eq

end MessageKeyArrayBytes

/-- `arrayAt (messageKeyAt A) 104 base gks` entails a flat `(gks.length * 104)`-byte slice
`base ↦ₛ bs` (`MessageKeyArrayBytes gks bs`) separated from `messageKeyHeaps A gks`. -/
theorem arrayAt_messageKeyAt_entails_bytes (A : RustAlloc) (base : BitVec 64)
    (gks : List (MessageKeyGhost × MessageKeyGenerator)) :
    arrayAt (messageKeyAt A) 104 base gks ⊢
      (∃∗ bs : List (BitVec 8), ⌜MessageKeyArrayBytes gks bs⌝ ∗ (base ↦ₛ bs)) ∗
        messageKeyHeaps A gks := by
  induction gks generalizing base with
  | nil =>
    simp only [arrayAt_nil, messageKeyHeaps_nil, sepConj_emp]
    apply Entails.sepExists_right []
    apply Entails.pure_right MessageKeyArrayBytes.nil
    rw [pointsToBytes_nil]
    exact Entails.refl _
  | cons gk gks ih =>
    rw [arrayAt_cons, messageKeyAt_eq_exists_bytes, messageKeyHeaps_cons]
    refine Entails.trans (sepConj_mono_right (ih (base + BitVec.ofNat 64 104))) ?_
    have hpull :
        (((∃∗ pad : List (BitVec 8), ⌜pad.length = 4⌝ ∗ (base ↦ₛ messageKeyBytes gk pad)) ∗
           messageKeyHeap A gk) ∗
         ((∃∗ bs : List (BitVec 8), ⌜MessageKeyArrayBytes gks bs⌝ ∗
            ((base + BitVec.ofNat 64 104) ↦ₛ bs)) ∗
          messageKeyHeaps A gks)) =
        (((∃∗ pad : List (BitVec 8), ⌜pad.length = 4⌝ ∗ (base ↦ₛ messageKeyBytes gk pad)) ∗
          (∃∗ bs : List (BitVec 8), ⌜MessageKeyArrayBytes gks bs⌝ ∗
            ((base + BitVec.ofNat 64 104) ↦ₛ bs))) ∗
         (messageKeyHeap A gk ∗ messageKeyHeaps A gks)) := by
      ac_rfl
    rw [hpull]
    apply sepConj_mono_left
    rw [sepExists_sepConj_left]
    apply Entails.sepExists_elim
    intro pad
    rw [sepExists_sepConj_right]
    apply Entails.sepExists_elim
    intro bs'
    have hpull2 :
        ((⌜pad.length = 4⌝ ∗ (base ↦ₛ messageKeyBytes gk pad)) ∗
          (⌜MessageKeyArrayBytes gks bs'⌝ ∗ ((base + BitVec.ofNat 64 104) ↦ₛ bs'))) =
        (⌜pad.length = 4⌝ ∗
          (⌜MessageKeyArrayBytes gks bs'⌝ ∗
            ((base ↦ₛ messageKeyBytes gk pad) ∗ ((base + BitVec.ofNat 64 104) ↦ₛ bs')))) := by
      ac_rfl
    rw [hpull2]
    apply Entails.pure_left
    intro hpad
    apply Entails.pure_left
    intro hrest
    apply Entails.sepExists_right (messageKeyBytes gk pad ++ bs')
    apply Entails.pure_right (.cons hpad hrest)
    rw [pointsToBytes_append, messageKeyBytes_length gk hpad]
    exact Entails.refl _

/-- Reassemble `arrayAt (messageKeyAt A) 104 base gks` from `(base ↦ₛ bs) ∗ messageKeyHeaps A gks`
given `MessageKeyArrayBytes gks bs`. -/
theorem arrayAt_messageKeyAt_of_bytes (A : RustAlloc) (base : BitVec 64)
    {gks : List (MessageKeyGhost × MessageKeyGenerator)} {bs : List (BitVec 8)}
    (hbs : MessageKeyArrayBytes gks bs) :
    ((base ↦ₛ bs) ∗ messageKeyHeaps A gks) ⊢ arrayAt (messageKeyAt A) 104 base gks := by
  induction hbs generalizing base with
  | nil =>
    simp only [pointsToBytes_nil, messageKeyHeaps_nil, arrayAt_nil, emp_sepConj]
    exact Entails.refl _
  | @cons gk gks pad bs' hpad _ ih =>
    rw [pointsToBytes_append, messageKeyBytes_length gk hpad, messageKeyHeaps_cons, arrayAt_cons]
    have hpull :
        (((base ↦ₛ messageKeyBytes gk pad) ∗ ((base + BitVec.ofNat 64 104) ↦ₛ bs')) ∗
          (messageKeyHeap A gk ∗ messageKeyHeaps A gks)) =
        (((base ↦ₛ messageKeyBytes gk pad) ∗ messageKeyHeap A gk) ∗
          (((base + BitVec.ofNat 64 104) ↦ₛ bs') ∗ messageKeyHeaps A gks)) := by
      ac_rfl
    rw [hpull]
    exact sepConj_mono (messageKeyAt_of_bytes A gk base hpad) (ih (base + BitVec.ofNat 64 104))

theorem exists_bytes_entails_arrayAt_messageKeyAt (A : RustAlloc) (base : BitVec 64)
    (gks : List (MessageKeyGhost × MessageKeyGenerator)) :
    ((∃∗ bs : List (BitVec 8), ⌜MessageKeyArrayBytes gks bs⌝ ∗ (base ↦ₛ bs)) ∗
      messageKeyHeaps A gks) ⊢
      arrayAt (messageKeyAt A) 104 base gks := by
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim
  intro bs
  rw [sepConj_assoc]
  apply Entails.pure_left
  intro hbs
  exact arrayAt_messageKeyAt_of_bytes A base hbs

/-- Prepending a newly written `messageKeyAt A gk₀ base` in front of a shifted byte slice
`((base + 104#64) ↦ₛ bs)` and `messageKeyHeaps A gks` yields
`arrayAt (messageKeyAt A) 104 base (gk₀ :: gks)`. -/
theorem arrayAt_messageKeyAt_cons_of_bytes (A : RustAlloc) (base : BitVec 64)
    (gk₀ : MessageKeyGhost × MessageKeyGenerator)
    {gks : List (MessageKeyGhost × MessageKeyGenerator)} {bs : List (BitVec 8)}
    (hbs : MessageKeyArrayBytes gks bs) :
    (messageKeyAt A gk₀ base ∗ ((base + 104#64) ↦ₛ bs) ∗ messageKeyHeaps A gks) ⊢
      arrayAt (messageKeyAt A) 104 base (gk₀ :: gks) := by
  rw [arrayAt_cons]
  exact sepConj_mono_right (arrayAt_messageKeyAt_of_bytes A (base + 104#64) hbs)

/-! ## `Vec<MessageKey>` Buffer Operations (`grow_one`, `insert(0)`, `remove(p)`, `pop`) -/

/-- Expose `vecBuf A 104 8 (messageKeyAt A) cap ptr gks` (when `cap ≠ 0`) as a flat byte slice
`ptr ↦ₛ bs` (`MessageKeyArrayBytes gks bs`), the spare capacity `memRegion`, `A.live`, and
`messageKeyHeaps A gks`. -/
theorem vecBuf_messageKeyAt_entails_bytes (A : RustAlloc) (cap ptr : BitVec 64)
    (gks : List (MessageKeyGhost × MessageKeyGenerator)) (hcap : cap ≠ 0) :
    vecBuf A 104 8 (messageKeyAt A) cap ptr gks ⊢
      ∃∗ bs : List (BitVec 8),
        ⌜MessageKeyArrayBytes gks bs ∧ bs.length = gks.length * 104 ∧
          gks.length ≤ cap.toNat ∧ cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        A.live ptr (cap.toNat * 104) 8 ∗
        (ptr ↦ₛ bs) ∗
        memRegion (ptr + BitVec.ofNat 64 (gks.length * 104)) ((cap.toNat - gks.length) * 104) ∗
        messageKeyHeaps A gks := by
  rw [vecBuf_of_ne_zero A 104 8 (messageKeyAt A) cap ptr gks hcap]
  apply Entails.pure_left
  rintro ⟨hlen, hcap_lt, hptr⟩
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_left (arrayAt_messageKeyAt_entails_bytes A ptr gks))) ?_
  rw [sepExists_sepConj_left, sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim
  intro bs
  have hpull :
      (A.live ptr (cap.toNat * 104) 8 ∗
        (((⌜MessageKeyArrayBytes gks bs⌝ ∗ (ptr ↦ₛ bs)) ∗ messageKeyHeaps A gks) ∗
         memRegion (ptr + BitVec.ofNat 64 (gks.length * 104)) ((cap.toNat - gks.length) * 104))) =
      (⌜MessageKeyArrayBytes gks bs⌝ ∗
        (A.live ptr (cap.toNat * 104) 8 ∗
         (ptr ↦ₛ bs) ∗
         memRegion (ptr + BitVec.ofNat 64 (gks.length * 104)) ((cap.toNat - gks.length) * 104) ∗
         messageKeyHeaps A gks)) := by
    ac_rfl
  rw [hpull]
  apply Entails.pure_left
  intro hbs
  apply Entails.sepExists_right bs
  exact Entails.pure_right ⟨hbs, hbs.length_eq, hlen, hcap_lt, hptr⟩ (Entails.refl _)

/-- Reassemble `vecBuf A 104 8 (messageKeyAt A) cap ptr gks` (when `cap ≠ 0`) from `(ptr ↦ₛ bs)`,
`messageKeyHeaps A gks`, `A.live`, and the spare `memRegion`. -/
theorem vecBuf_messageKeyAt_of_bytes (A : RustAlloc) (cap ptr : BitVec 64)
    {gks : List (MessageKeyGhost × MessageKeyGenerator)} {bs : List (BitVec 8)}
    (hcap : cap ≠ 0)
    (hbs : MessageKeyArrayBytes gks bs)
    (hlen : gks.length ≤ cap.toNat)
    (hcap_lt : cap.toNat * 104 < 2 ^ 63)
    (hptr : ptr ≠ 0) :
    (A.live ptr (cap.toNat * 104) 8 ∗
      (ptr ↦ₛ bs) ∗
      memRegion (ptr + BitVec.ofNat 64 (gks.length * 104)) ((cap.toNat - gks.length) * 104) ∗
      messageKeyHeaps A gks) ⊢
      vecBuf A 104 8 (messageKeyAt A) cap ptr gks := by
  rw [vecBuf_of_ne_zero A 104 8 (messageKeyAt A) cap ptr gks hcap]
  apply Entails.pure_right ⟨hlen, hcap_lt, hptr⟩
  have hpull :
      (A.live ptr (cap.toNat * 104) 8 ∗
        (ptr ↦ₛ bs) ∗
        memRegion (ptr + BitVec.ofNat 64 (gks.length * 104)) ((cap.toNat - gks.length) * 104) ∗
        messageKeyHeaps A gks) =
      (A.live ptr (cap.toNat * 104) 8 ∗
        (((ptr ↦ₛ bs) ∗ messageKeyHeaps A gks) ∗
         memRegion (ptr + BitVec.ofNat 64 (gks.length * 104)) ((cap.toNat - gks.length) * 104))) := by
    ac_rfl
  rw [hpull]
  exact sepConj_mono_right (sepConj_mono_left (arrayAt_messageKeyAt_of_bytes A ptr hbs))

/-! ### `grow_one` -/

/-- Precondition bridge for `growOneSpec`: when `gks.length = cap.toNat` (whether `cap = 0` or
`cap ≠ 0`), `vecBuf A 104 8 (messageKeyAt A) cap ptr gks` exposes the exact `(if cap = 0 ...)`
precondition required by `growOneSpec`, separated from `messageKeyHeaps A gks`. -/
theorem vecBuf_messageKeyAt_full_entails_grow_one (A : RustAlloc) (cap ptr : BitVec 64)
    (gks : List (MessageKeyGhost × MessageKeyGenerator)) (hfull : gks.length = cap.toNat) :
    vecBuf A 104 8 (messageKeyAt A) cap ptr gks ⊢
      ∃∗ bs : List (BitVec 8),
        ⌜MessageKeyArrayBytes gks bs ∧ bs.length = cap.toNat * 104⌝ ∗
        (⌜cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
          (if cap = 0 then emp
           else A.live ptr (cap.toNat * 104) 8 ∗ (ptr ↦ₛ bs) ∗ ⌜bs.length = cap.toNat * 104⌝)) ∗
        messageKeyHeaps A gks := by
  by_cases hcap : cap = 0
  · subst hcap
    have hgks : gks = [] := List.eq_nil_of_length_eq_zero (by simpa using hfull)
    subst hgks
    rw [vecBuf_zero, ← sepConj_emp ⌜([] : List (MessageKeyGhost × MessageKeyGenerator)) = [] ∧ ptr ≠ 0⌝]
    apply Entails.pure_left
    rintro ⟨_, hptr⟩
    apply Entails.sepExists_right []
    simp only [↓reduceIte, messageKeyHeaps_nil, sepConj_emp]
    apply Entails.pure_right ⟨.nil, rfl⟩
    exact Entails.pure_right_only ⟨by decide, hptr⟩ (Entails.refl _)
  · refine Entails.trans (vecBuf_messageKeyAt_entails_bytes A cap ptr gks hcap) ?_
    apply Entails.sepExists_elim
    intro bs
    apply Entails.pure_left
    rintro ⟨hbs, hbs_len, _, hcap_lt, hptr⟩
    have hbs_cap : bs.length = cap.toNat * 104 := by rw [hbs_len, hfull]
    have hrem : (cap.toNat - gks.length) * 104 = 0 := by omega
    rw [hrem, memRegion_zero]
    apply Entails.sepExists_right bs
    simp only [hcap, ↓reduceIte]
    apply Entails.pure_right ⟨hbs, hbs_cap⟩
    have hpull :
        (A.live ptr (cap.toNat * 104) 8 ∗ (ptr ↦ₛ bs) ∗ emp ∗ messageKeyHeaps A gks) =
        ((A.live ptr (cap.toNat * 104) 8 ∗ (ptr ↦ₛ bs)) ∗ messageKeyHeaps A gks) := by
      ac_rfl
    rw [hpull]
    apply sepConj_mono_left
    apply Entails.pure_right ⟨hcap_lt, hptr⟩
    apply sepConj_mono_right
    rw [sepConj_comm (ptr ↦ₛ bs)]
    exact Entails.pure_right hbs_cap (Entails.refl _)

/-- After `growOneSpec`, the new capacity `max (2 * cap.toNat) 4` strictly exceeds `gks.length`
(when `gks.length = cap.toNat`), and fits in `BitVec 64` without truncation. -/
theorem grow_one_newCap_props {cap : BitVec 64} {len : Nat}
    (hfull : len = cap.toNat)
    (hnew_lt : max (2 * cap.toNat) 4 * 104 < 2 ^ 63) :
    let newCap := max (2 * cap.toNat) 4
    BitVec.ofNat 64 newCap ≠ 0 ∧
      (BitVec.ofNat 64 newCap).toNat = newCap ∧
      len < (BitVec.ofNat 64 newCap).toNat ∧
      (BitVec.ofNat 64 newCap).toNat * 104 < 2 ^ 63 := by
  intro newCap
  have hpos : 4 ≤ newCap := Nat.le_max_right (2 * cap.toNat) 4
  have hgt : len < newCap := by
    have : 2 * cap.toNat ≤ newCap := Nat.le_max_left (2 * cap.toNat) 4
    omega
  have hlt64 : newCap < 2 ^ 64 := by omega
  have htoNat : (BitVec.ofNat 64 newCap).toNat = newCap := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64]
  refine ⟨?_, htoNat, ?_, ?_⟩
  · intro h0
    have : (BitVec.ofNat 64 newCap).toNat = 0 := by rw [h0]; rfl
    omega
  · omega
  · omega

/-- Postcondition bridge for `growOneSpec`: reassembles `vecBuf A 104 8 (messageKeyAt A)` at the
new capacity `BitVec.ofNat 64 (max (2 * cap.toNat) 4)` and pointer `newPtr` from the postcondition
of `growOneSpec` and the framed `messageKeyHeaps A gks`. -/
theorem vecBuf_messageKeyAt_of_grow_one (A : RustAlloc) (cap newPtr : BitVec 64)
    {gks : List (MessageKeyGhost × MessageKeyGenerator)} {bs : List (BitVec 8)}
    (hfull : gks.length = cap.toNat)
    (hbs : MessageKeyArrayBytes gks bs)
    (hnewPtr : newPtr ≠ 0)
    (hnew_lt : max (2 * cap.toNat) 4 * 104 < 2 ^ 63) :
    let newCap := max (2 * cap.toNat) 4
    (A.live newPtr (newCap * 104) 8 ∗
      (newPtr ↦ₛ bs) ∗
      memRegion (newPtr + BitVec.ofNat 64 (cap.toNat * 104)) ((newCap - cap.toNat) * 104) ∗
      messageKeyHeaps A gks) ⊢
      vecBuf A 104 8 (messageKeyAt A) (BitVec.ofNat 64 newCap) newPtr gks := by
  intro newCap
  obtain ⟨hne0, htoNat, hlen_lt, hcap_lt⟩ := grow_one_newCap_props hfull hnew_lt
  have h := vecBuf_messageKeyAt_of_bytes A (BitVec.ofNat 64 newCap) newPtr hne0 hbs
    (Nat.le_of_lt hlen_lt) hcap_lt hnewPtr
  rw [htoNat, hfull] at h
  exact h

/-! ### `insert(0)` via `listMove` -/

/-- When `gks.length < cap.toNat`, `vecBuf A 104 8 (messageKeyAt A) cap ptr gks` exposes a flat
`((gks.length + 1) * 104)`-byte slice `ptr ↦ₛ (bs ++ slotBs)` (the active elements `bs` followed by
one 104-byte spare slot `slotBs`) ready for `memmove(ptr + 104, ptr, gks.length * 104)`, plus the
remaining spare region `memRegion (ptr + (gks.length + 1) * 104) ((cap.toNat - (gks.length + 1)) * 104)`
and `messageKeyHeaps A gks`. -/
theorem vecBuf_messageKeyAt_expose_for_insert0 (A : RustAlloc) (cap ptr : BitVec 64)
    (gks : List (MessageKeyGhost × MessageKeyGenerator))
    (hlen_lt : gks.length < cap.toNat) :
    vecBuf A 104 8 (messageKeyAt A) cap ptr gks ⊢
      ∃∗ bs : List (BitVec 8), ∃∗ slotBs : List (BitVec 8),
        ⌜MessageKeyArrayBytes gks bs ∧ bs.length = gks.length * 104 ∧ slotBs.length = 104 ∧
          cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        A.live ptr (cap.toNat * 104) 8 ∗
        (ptr ↦ₛ (bs ++ slotBs)) ∗
        memRegion (ptr + BitVec.ofNat 64 ((gks.length + 1) * 104))
          ((cap.toNat - (gks.length + 1)) * 104) ∗
        messageKeyHeaps A gks := by
  have hcap : cap ≠ 0 := by
    intro h0; rw [h0] at hlen_lt; change gks.length < 0 at hlen_lt; omega
  refine Entails.trans (vecBuf_messageKeyAt_entails_bytes A cap ptr gks hcap) ?_
  apply Entails.sepExists_elim
  intro bs
  apply Entails.pure_left
  rintro ⟨hbs, hbs_len, _, hcap_lt, hptr⟩
  have hsplit_len : (cap.toNat - gks.length) * 104 =
      104 + (cap.toNat - (gks.length + 1)) * 104 := by
    have : cap.toNat - gks.length = 1 + (cap.toNat - (gks.length + 1)) := by omega
    rw [this, Nat.add_mul, Nat.one_mul]
  have hbound : 104 + (cap.toNat - (gks.length + 1)) * 104 ≤ 2 ^ 64 := by omega
  have hoff :
      ptr + BitVec.ofNat 64 (gks.length * 104) + BitVec.ofNat 64 104 =
        ptr + BitVec.ofNat 64 ((gks.length + 1) * 104) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
    omega
  rw [hsplit_len, memRegion_split (ptr + BitVec.ofNat 64 (gks.length * 104)) 104 _ hbound, hoff]
  have hpull0 :
      (A.live ptr (cap.toNat * 104) 8 ∗
        (ptr ↦ₛ bs) ∗
        (memRegion (ptr + BitVec.ofNat 64 (gks.length * 104)) 104 ∗
         memRegion (ptr + BitVec.ofNat 64 ((gks.length + 1) * 104))
           ((cap.toNat - (gks.length + 1)) * 104)) ∗
        messageKeyHeaps A gks) =
      (memRegion (ptr + BitVec.ofNat 64 (gks.length * 104)) 104 ∗
        (A.live ptr (cap.toNat * 104) 8 ∗
         (ptr ↦ₛ bs) ∗
         memRegion (ptr + BitVec.ofNat 64 ((gks.length + 1) * 104))
           ((cap.toNat - (gks.length + 1)) * 104) ∗
         messageKeyHeaps A gks)) := by
    ac_rfl
  rw [hpull0, memRegion_eq_exists_bytes (ptr + BitVec.ofNat 64 (gks.length * 104)) 104 (by decide),
      sepExists_sepConj_left]
  apply Entails.sepExists_elim
  intro slotBs
  rw [sepConj_assoc]
  apply Entails.pure_left
  intro hslot
  apply Entails.sepExists_right bs
  apply Entails.sepExists_right slotBs
  apply Entails.pure_right ⟨hbs, hbs_len, hslot, hcap_lt, hptr⟩
  have hpull :
      (((ptr + BitVec.ofNat 64 (gks.length * 104)) ↦ₛ slotBs) ∗
        (A.live ptr (cap.toNat * 104) 8 ∗
         (ptr ↦ₛ bs) ∗
         memRegion (ptr + BitVec.ofNat 64 ((gks.length + 1) * 104))
           ((cap.toNat - (gks.length + 1)) * 104) ∗
         messageKeyHeaps A gks)) =
      (A.live ptr (cap.toNat * 104) 8 ∗
        ((ptr ↦ₛ bs) ∗ ((ptr + BitVec.ofNat 64 (gks.length * 104)) ↦ₛ slotBs)) ∗
        memRegion (ptr + BitVec.ofNat 64 ((gks.length + 1) * 104))
          ((cap.toNat - (gks.length + 1)) * 104) ∗
        messageKeyHeaps A gks) := by
    ac_rfl
  rw [hpull, ← hbs_len, ← pointsToBytes_append]
  exact Entails.refl _

/-- Pure `listMove` equation for shifting `len * 104` bytes right by 104 bytes inside
`bs ++ slotBs`: the result is the 104-byte prefix `(bs ++ slotBs).take 104` followed by `bs`. -/
theorem listMove_insert0 {bs slotBs : List (BitVec 8)} {len : Nat}
    (hbs : bs.length = len * 104) (hslot : slotBs.length = 104) :
    listMove (bs ++ slotBs) 104 0 (len * 104) =
      (bs ++ slotBs).take 104 ++ bs := by
  unfold listMove
  simp only [List.drop_zero]
  have htake : (bs ++ slotBs).take (len * 104) = bs := by
    rw [← hbs, List.take_left]
  have hdrop : (bs ++ slotBs).drop (104 + len * 104) = [] := by
    apply List.drop_eq_nil_of_le
    rw [List.length_append, hbs, hslot]
    omega
  rw [htake, hdrop, List.append_nil]

/-- After `memmove(ptr + 104, ptr, gks.length * 104)` produces
`ptr ↦ₛ listMove (bs ++ slotBs) 104 0 (gks.length * 104)`, it splits into a 104-byte writable
region `memRegion ptr 104` (at index 0) and the shifted elements `((ptr + 104#64) ↦ₛ bs)`. -/
theorem pointsToBytes_listMove_insert0 (ptr : BitVec 64) {bs slotBs : List (BitVec 8)} {len : Nat}
    (hbs : bs.length = len * 104) (hslot : slotBs.length = 104) :
    (ptr ↦ₛ listMove (bs ++ slotBs) 104 0 (len * 104)) ⊢
      memRegion ptr 104 ∗ ((ptr + 104#64) ↦ₛ bs) := by
  rw [listMove_insert0 hbs hslot, pointsToBytes_append]
  have hlen104 : ((bs ++ slotBs).take 104).length = 104 := by
    rw [List.length_take, List.length_append, hbs, hslot]
    omega
  rw [hlen104]
  have h := pointsToBytes_entails_memRegion ptr ((bs ++ slotBs).take 104)
  rw [hlen104] at h
  exact sepConj_mono_left h

/-- Further split `memRegion ptr 104` at index 0 into four 24-byte `vecHeader` slots
(for writing `cipher`, `mac`, `iv`, `seed` at `ptr + {0, 24, 48, 72}`), a 32-bit `counter` slot
at `ptr + 96`, and the 4-byte padding `memRegion (ptr + 100) 4`. -/
theorem memRegion_104_entails_messageKey_slots (ptr : BitVec 64) :
    memRegion ptr 104 ⊢
      memRegion ptr 24 ∗
        memRegion (ptr + 24#64) 24 ∗
        memRegion (ptr + 48#64) 24 ∗
        memRegion (ptr + 72#64) 24 ∗
        memRegion (ptr + 96#64) 4 ∗
        memRegion (ptr + 100#64) 4 := by
  rw [show (104 : Nat) = 24 + 80 from rfl, memRegion_split ptr 24 80 (by decide),
      show (80 : Nat) = 24 + 56 from rfl, memRegion_split (ptr + 24#64) 24 56 (by decide),
      show (56 : Nat) = 24 + 32 from rfl, memRegion_split (ptr + 24#64 + 24#64) 24 32 (by decide),
      show (32 : Nat) = 24 + 8 from rfl, memRegion_split (ptr + 24#64 + 24#64 + 24#64) 24 8 (by decide),
      show (8 : Nat) = 4 + 4 from rfl, memRegion_split (ptr + 24#64 + 24#64 + 24#64 + 24#64) 4 4 (by decide)]
  have h48 : ptr + 24#64 + 24#64 = ptr + 48#64 := by bv_arith
  have h72 : ptr + 24#64 + 24#64 + 24#64 = ptr + 72#64 := by bv_arith
  have h96 : ptr + 24#64 + 24#64 + 24#64 + 24#64 = ptr + 96#64 := by bv_arith
  have h100 : ptr + 24#64 + 24#64 + 24#64 + 24#64 + 4#64 = ptr + 100#64 := by bv_arith
  rw [h100, h96, h72, h48]
  exact Entails.refl _

/-- Reassemble `vecBuf A 104 8 (messageKeyAt A) cap ptr (gk₀ :: gks)` after `insert(0)` from
`messageKeyAt A gk₀ ptr` at index 0, the shifted byte block `((ptr + 104#64) ↦ₛ bs)`,
`messageKeyHeaps A gks`, `A.live`, and the remaining spare `memRegion`. -/
theorem vecBuf_messageKeyAt_of_insert0 (A : RustAlloc) (cap ptr : BitVec 64)
    (gk₀ : MessageKeyGhost × MessageKeyGenerator)
    {gks : List (MessageKeyGhost × MessageKeyGenerator)} {bs : List (BitVec 8)}
    (hbs : MessageKeyArrayBytes gks bs)
    (hlen_lt : gks.length < cap.toNat)
    (hcap_lt : cap.toNat * 104 < 2 ^ 63)
    (hptr : ptr ≠ 0) :
    (A.live ptr (cap.toNat * 104) 8 ∗
      messageKeyAt A gk₀ ptr ∗
      ((ptr + 104#64) ↦ₛ bs) ∗
      memRegion (ptr + BitVec.ofNat 64 ((gks.length + 1) * 104))
        ((cap.toNat - (gks.length + 1)) * 104) ∗
      messageKeyHeaps A gks) ⊢
      vecBuf A 104 8 (messageKeyAt A) cap ptr (gk₀ :: gks) := by
  have hcap : cap ≠ 0 := by intro h0; rw [h0] at hlen_lt; change gks.length < 0 at hlen_lt; omega
  rw [vecBuf_of_ne_zero A 104 8 (messageKeyAt A) cap ptr (gk₀ :: gks) hcap]
  simp only [List.length_cons]
  apply Entails.pure_right ⟨by omega, hcap_lt, hptr⟩
  have hpull :
      (A.live ptr (cap.toNat * 104) 8 ∗
        messageKeyAt A gk₀ ptr ∗
        ((ptr + 104#64) ↦ₛ bs) ∗
        memRegion (ptr + BitVec.ofNat 64 ((gks.length + 1) * 104))
          ((cap.toNat - (gks.length + 1)) * 104) ∗
        messageKeyHeaps A gks) =
      (A.live ptr (cap.toNat * 104) 8 ∗
        (messageKeyAt A gk₀ ptr ∗ ((ptr + 104#64) ↦ₛ bs) ∗ messageKeyHeaps A gks) ∗
        memRegion (ptr + BitVec.ofNat 64 ((gks.length + 1) * 104))
          ((cap.toNat - (gks.length + 1)) * 104)) := by
    ac_rfl
  rw [hpull]
  exact sepConj_mono_right (sepConj_mono_left (arrayAt_messageKeyAt_cons_of_bytes A ptr gk₀ hbs))

/-! ### `remove(p)` via `listMove` -/

/-- Expose `vecBuf A 104 8 (messageKeyAt A) cap ptr gks` for removing element `p < gks.length`:
splits out `messageKeyHeap A gks[p]` (for the removed `MessageKey` returned to the caller) from
`messageKeyHeaps A (gks.eraseIdx p)` while exposing the flat byte buffer `ptr ↦ₛ bs` for `memmove`. -/
theorem vecBuf_messageKeyAt_expose_for_remove (A : RustAlloc) (cap ptr : BitVec 64)
    (gks : List (MessageKeyGhost × MessageKeyGenerator))
    {p : Nat} (hp : p < gks.length) :
    vecBuf A 104 8 (messageKeyAt A) cap ptr gks ⊢
      ∃∗ bs : List (BitVec 8),
        ⌜MessageKeyArrayBytes gks bs ∧ bs.length = gks.length * 104 ∧
          gks.length ≤ cap.toNat ∧ cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        A.live ptr (cap.toNat * 104) 8 ∗
        (ptr ↦ₛ bs) ∗
        memRegion (ptr + BitVec.ofNat 64 (gks.length * 104)) ((cap.toNat - gks.length) * 104) ∗
        messageKeyHeap A gks[p] ∗
        messageKeyHeaps A (gks.eraseIdx p) := by
  have hcap_or : cap = 0 ∨ cap ≠ 0 := Classical.em _
  rcases hcap_or with rfl | hcap
  · unfold vecBuf
    apply Entails.pure_left
    rintro ⟨hlen, _, _⟩
    change gks.length ≤ 0 at hlen
    omega
  · refine Entails.trans (vecBuf_messageKeyAt_entails_bytes A cap ptr gks hcap) ?_
    apply Entails.sepExists_elim
    intro bs
    apply Entails.pure_left
    rintro ⟨hbs, hbs_len, hlen, hcap_lt, hptr⟩
    rw [messageKeyHeaps_split_at A gks hp]
    apply Entails.sepExists_right bs
    apply Entails.pure_right ⟨hbs, hbs_len, hlen, hcap_lt, hptr⟩
    exact Entails.refl _

/-- After `memmove(ptr + p * 104, ptr + (p + 1) * 104, (gks.length - 1 - p) * 104)` produces
`ptr ↦ₛ listMove bs (p * 104) ((p + 1) * 104) ((gks.length - 1 - p) * 104)`, it splits into
the active elements of `gks.eraseIdx p` and a new 104-byte spare `memRegion` at index `gks.length - 1`. -/
theorem pointsToBytes_listMove_remove (ptr : BitVec 64)
    {gks : List (MessageKeyGhost × MessageKeyGenerator)} {bs : List (BitVec 8)}
    (hbs : MessageKeyArrayBytes gks bs) {p : Nat} (hp : p < gks.length) :
    (ptr ↦ₛ listMove bs (p * 104) ((p + 1) * 104) ((gks.length - 1 - p) * 104)) ⊢
      (∃∗ bs' : List (BitVec 8),
        ⌜MessageKeyArrayBytes (gks.eraseIdx p) bs'⌝ ∗ (ptr ↦ₛ bs')) ∗
      memRegion (ptr + BitVec.ofNat 64 ((gks.length - 1) * 104)) 104 := by
  unfold listMove
  set bs' := bs.take (p * 104) ++ (bs.drop ((p + 1) * 104)).take ((gks.length - 1 - p) * 104)
  set tail := bs.drop (p * 104 + (gks.length - 1 - p) * 104)
  have hbs' : MessageKeyArrayBytes (gks.eraseIdx p) bs' := hbs.eraseIdx hp
  have herase_len : (gks.eraseIdx p).length = gks.length - 1 := List.length_eraseIdx_of_lt hp
  have hbs'_len : bs'.length = (gks.length - 1) * 104 := by
    rw [hbs'.length_eq, herase_len]
  have htail_len : tail.length = 104 := by
    simp only [tail, List.length_drop, hbs.length_eq]
    have : p * 104 + (gks.length - 1 - p) * 104 = (gks.length - 1) * 104 := by
      have : p + (gks.length - 1 - p) = gks.length - 1 := by omega
      calc p * 104 + (gks.length - 1 - p) * 104
        _ = (p + (gks.length - 1 - p)) * 104 := by rw [Nat.add_mul]
        _ = (gks.length - 1) * 104 := by rw [this]
    omega
  rw [pointsToBytes_append, hbs'_len]
  apply sepConj_mono
  · exact Entails.sepExists_right bs' (Entails.pure_right hbs' (Entails.refl _))
  · have h := pointsToBytes_entails_memRegion
      (ptr + BitVec.ofNat 64 ((gks.length - 1) * 104)) tail
    rwa [htail_len] at h

/-- Reassemble `vecBuf A 104 8 (messageKeyAt A) cap ptr (gks.eraseIdx p)` after `remove(p)` from
`ptr ↦ₛ listMove bs (p * 104) ((p + 1) * 104) ((gks.length - 1 - p) * 104)`, `A.live`, the old
spare `memRegion`, and `messageKeyHeaps A (gks.eraseIdx p)`. -/
theorem vecBuf_messageKeyAt_of_remove (A : RustAlloc) (cap ptr : BitVec 64)
    {gks : List (MessageKeyGhost × MessageKeyGenerator)} {bs : List (BitVec 8)}
    (hbs : MessageKeyArrayBytes gks bs) {p : Nat} (hp : p < gks.length)
    (hlen : gks.length ≤ cap.toNat)
    (hcap_lt : cap.toNat * 104 < 2 ^ 63)
    (hptr : ptr ≠ 0) :
    (A.live ptr (cap.toNat * 104) 8 ∗
      (ptr ↦ₛ listMove bs (p * 104) ((p + 1) * 104) ((gks.length - 1 - p) * 104)) ∗
      memRegion (ptr + BitVec.ofNat 64 (gks.length * 104)) ((cap.toNat - gks.length) * 104) ∗
      messageKeyHeaps A (gks.eraseIdx p)) ⊢
      vecBuf A 104 8 (messageKeyAt A) cap ptr (gks.eraseIdx p) := by
  have hcap : cap ≠ 0 := by intro h0; rw [h0] at hlen; change gks.length ≤ 0 at hlen; omega
  have herase_len : (gks.eraseIdx p).length = gks.length - 1 := List.length_eraseIdx_of_lt hp
  rw [vecBuf_of_ne_zero A 104 8 (messageKeyAt A) cap ptr (gks.eraseIdx p) hcap]
  apply Entails.pure_right ⟨by omega, hcap_lt, hptr⟩
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_left (pointsToBytes_listMove_remove ptr hbs hp))) ?_
  have hpull :
      (A.live ptr (cap.toNat * 104) 8 ∗
        ((∃∗ bs' : List (BitVec 8),
          ⌜MessageKeyArrayBytes (gks.eraseIdx p) bs'⌝ ∗ (ptr ↦ₛ bs')) ∗
         memRegion (ptr + BitVec.ofNat 64 ((gks.length - 1) * 104)) 104) ∗
        memRegion (ptr + BitVec.ofNat 64 (gks.length * 104)) ((cap.toNat - gks.length) * 104) ∗
        messageKeyHeaps A (gks.eraseIdx p)) =
      (A.live ptr (cap.toNat * 104) 8 ∗
        (((∃∗ bs' : List (BitVec 8),
            ⌜MessageKeyArrayBytes (gks.eraseIdx p) bs'⌝ ∗ (ptr ↦ₛ bs')) ∗
          messageKeyHeaps A (gks.eraseIdx p)) ∗
         (memRegion (ptr + BitVec.ofNat 64 ((gks.length - 1) * 104)) 104 ∗
          memRegion (ptr + BitVec.ofNat 64 (gks.length * 104))
            ((cap.toNat - gks.length) * 104)))) := by
    ac_rfl
  rw [hpull]
  apply sepConj_mono_right
  apply sepConj_mono
  · exact exists_bytes_entails_arrayAt_messageKeyAt A ptr (gks.eraseIdx p)
  · rw [herase_len]
    have hsplit_len : (cap.toNat - (gks.length - 1)) * 104 =
        104 + (cap.toNat - gks.length) * 104 := by
      have : cap.toNat - (gks.length - 1) = 1 + (cap.toNat - gks.length) := by omega
      rw [this, Nat.add_mul, Nat.one_mul]
    have hoff :
        ptr + BitVec.ofNat 64 ((gks.length - 1) * 104) + BitVec.ofNat 64 104 =
          ptr + BitVec.ofNat 64 (gks.length * 104) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      congr 2
      omega
    rw [hsplit_len,
        memRegion_split (ptr + BitVec.ofNat 64 ((gks.length - 1) * 104)) 104 _ (by omega),
        hoff]
    exact Entails.refl _

/-! ### `pop` at Length `n + 1` -/

/-- Split `vecBuf A 104 8 (messageKeyAt A) cap ptr gks` when `gks.length = n + 1` (e.g. `2001`)
into the first `n` elements `arrayAt (messageKeyAt A) 104 ptr (gks.take n)`, the popped `n`-th
element `messageKeyAt A gks[n] (ptr + BitVec.ofNat 64 (n * 104))`, `A.live`, and the spare
`memRegion`. -/
theorem vecBuf_messageKeyAt_pop_split (A : RustAlloc) (cap ptr : BitVec 64)
    (gks : List (MessageKeyGhost × MessageKeyGenerator)) {n : Nat} (hlen_eq : gks.length = n + 1) :
    vecBuf A 104 8 (messageKeyAt A) cap ptr gks ⊢
      ⌜n + 1 ≤ cap.toNat ∧ cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        A.live ptr (cap.toNat * 104) 8 ∗
        arrayAt (messageKeyAt A) 104 ptr (gks.take n) ∗
        messageKeyAt A (gks[n]'(by omega)) (ptr + BitVec.ofNat 64 (n * 104)) ∗
        memRegion (ptr + BitVec.ofNat 64 ((n + 1) * 104)) ((cap.toNat - (n + 1)) * 104) := by
  unfold vecBuf
  apply Entails.pure_left
  rintro ⟨hlen, hcap_lt, hptr⟩
  have hcap : cap ≠ 0 := by intro h0; rw [h0] at hlen; change gks.length ≤ 0 at hlen; omega
  simp only [hcap, ↓reduceIte, arrayAt_split_of_length_succ (messageKeyAt A) 104 ptr gks hlen_eq]
  simp only [hlen_eq] at hlen ⊢
  apply Entails.pure_right ⟨hlen, hcap_lt, hptr⟩
  have hpull :
      (A.live ptr (cap.toNat * 104) 8 ∗
        (arrayAt (messageKeyAt A) 104 ptr (gks.take n) ∗
          messageKeyAt A (gks[n]'(by omega)) (ptr + BitVec.ofNat 64 (n * 104))) ∗
        memRegion (ptr + BitVec.ofNat 64 ((n + 1) * 104)) ((cap.toNat - (n + 1)) * 104)) =
      (A.live ptr (cap.toNat * 104) 8 ∗
        arrayAt (messageKeyAt A) 104 ptr (gks.take n) ∗
        messageKeyAt A (gks[n]'(by omega)) (ptr + BitVec.ofNat 64 (n * 104)) ∗
        memRegion (ptr + BitVec.ofNat 64 ((n + 1) * 104)) ((cap.toNat - (n + 1)) * 104)) := by
    ac_rfl
  rw [hpull]
  exact Entails.refl _

/-- Reassemble `vecBuf A 104 8 (messageKeyAt A) cap ptr (gks.take n)` after popping and dropping the
`n`-th element (leaving `memRegion (ptr + BitVec.ofNat 64 (n * 104)) 104` in its slot). -/
theorem vecBuf_messageKeyAt_pop_reassemble (A : RustAlloc) (cap ptr : BitVec 64)
    (gks : List (MessageKeyGhost × MessageKeyGenerator)) {n : Nat}
    (hlen_eq : gks.length = n + 1)
    (hlen : n + 1 ≤ cap.toNat)
    (hcap_lt : cap.toNat * 104 < 2 ^ 63)
    (hptr : ptr ≠ 0) :
    (A.live ptr (cap.toNat * 104) 8 ∗
      arrayAt (messageKeyAt A) 104 ptr (gks.take n) ∗
      memRegion (ptr + BitVec.ofNat 64 (n * 104)) 104 ∗
      memRegion (ptr + BitVec.ofNat 64 ((n + 1) * 104)) ((cap.toNat - (n + 1)) * 104)) ⊢
      vecBuf A 104 8 (messageKeyAt A) cap ptr (gks.take n) := by
  have hcap : cap ≠ 0 := by intro h0; rw [h0] at hlen; change n + 1 ≤ 0 at hlen; omega
  have htake_len : (gks.take n).length = n := by rw [List.length_take]; omega
  rw [vecBuf_of_ne_zero A 104 8 (messageKeyAt A) cap ptr (gks.take n) hcap, htake_len]
  apply Entails.pure_right ⟨by omega, hcap_lt, hptr⟩
  have hpull :
      (A.live ptr (cap.toNat * 104) 8 ∗
        arrayAt (messageKeyAt A) 104 ptr (gks.take n) ∗
        memRegion (ptr + BitVec.ofNat 64 (n * 104)) 104 ∗
        memRegion (ptr + BitVec.ofNat 64 ((n + 1) * 104)) ((cap.toNat - (n + 1)) * 104)) =
      (A.live ptr (cap.toNat * 104) 8 ∗
        arrayAt (messageKeyAt A) 104 ptr (gks.take n) ∗
        (memRegion (ptr + BitVec.ofNat 64 (n * 104)) 104 ∗
          memRegion (ptr + BitVec.ofNat 64 ((n + 1) * 104)) ((cap.toNat - (n + 1)) * 104))) := by
    ac_rfl
  rw [hpull]
  apply sepConj_mono_right
  apply sepConj_mono_right
  have hsplit_len : (cap.toNat - n) * 104 = 104 + (cap.toNat - (n + 1)) * 104 := by
    have : cap.toNat - n = 1 + (cap.toNat - (n + 1)) := by omega
    rw [this, Nat.add_mul, Nat.one_mul]
  have hoff :
      ptr + BitVec.ofNat 64 (n * 104) + BitVec.ofNat 64 104 =
        ptr + BitVec.ofNat 64 ((n + 1) * 104) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
    omega
  rw [hsplit_len, memRegion_split (ptr + BitVec.ofNat 64 (n * 104)) 104 _ (by omega), hoff]
  exact Entails.refl _

/-! ## `optChainKeyAt`, `chainAt`, `ratchetAt`, and `RatchetGhost.AgreeExcept` -/

@[local simp]
theorem length_keyToBytes32 (k : BitVec 256) : (keyToBytes32 k).length = 32 := by
  simp [keyToBytes32]

@[local simp]
theorem optChainKeyAt_none (A : RustAlloc) (pin : VecPin) (a : BitVec 64) :
    optChainKeyAt A pin none a = (a ↦₆₄ optChainKeyNone) ∗ memRegion (a + 8#64) 24 := rfl

@[local simp]
theorem optChainKeyAt_some (A : RustAlloc) (pin : VecPin) (ck : ChainKey) (a : BitVec 64) :
    optChainKeyAt A pin (some ck) a =
      vecU8At A a pin.cap pin.ptr (keyToBytes32 ck.key) ∗ ((a + 24#64) ↦₃₂ ck.index) ∗
        memRegion (a + 28#64) 4 := rfl

/-- Expose the header and deallocation resources of `optChainKeyAt A pin (some ck) a` when
replacing a `Some` chain key in `set_receiver_chain_key`. -/
theorem optChainKeyAt_some_entails_dealloc (A : RustAlloc) (pin : VecPin) (ck : ChainKey)
    (a : BitVec 64) :
    optChainKeyAt A pin (some ck) a ⊢
      vecHeader a pin.cap pin.ptr 32#64 ∗
        ((a + 24#64) ↦₃₂ ck.index) ∗ memRegion (a + 28#64) 4 ∗
        (⌜32 ≤ pin.cap.toNat ∧ pin.cap.toNat < 2 ^ 63 ∧ pin.ptr ≠ 0⌝ ∗
          (if pin.cap = 0 then emp
           else A.live pin.ptr pin.cap.toNat 1 ∗ memRegion pin.ptr pin.cap.toNat)) := by
  rw [optChainKeyAt_some]
  refine Entails.trans (sepConj_mono_left (vecU8At_entails_dealloc A a pin.cap pin.ptr (keyToBytes32 ck.key))) ?_
  simp only [length_keyToBytes32]
  have hpull :
      ((vecHeader a pin.cap pin.ptr (BitVec.ofNat 64 32) ∗
        (⌜32 ≤ pin.cap.toNat ∧ pin.cap.toNat < 2 ^ 63 ∧ pin.ptr ≠ 0⌝ ∗
          (if pin.cap = 0 then emp
           else A.live pin.ptr pin.cap.toNat 1 ∗ memRegion pin.ptr pin.cap.toNat))) ∗
       ((a + 24#64) ↦₃₂ ck.index) ∗ memRegion (a + 28#64) 4) =
      (vecHeader a pin.cap pin.ptr 32#64 ∗
        ((a + 24#64) ↦₃₂ ck.index) ∗ memRegion (a + 28#64) 4 ∗
        (⌜32 ≤ pin.cap.toNat ∧ pin.cap.toNat < 2 ^ 63 ∧ pin.ptr ≠ 0⌝ ∗
          (if pin.cap = 0 then emp
           else A.live pin.ptr pin.cap.toNat 1 ∗ memRegion pin.ptr pin.cap.toNat))) := by
    ac_rfl
  rw [hpull]
  exact Entails.refl _

/-- Split `optChainKeyAt A pin none a` into a 24-byte `vecHeader` slot at `a`, a 4-byte `index`
slot at `a + 24`, and 4 bytes of padding at `a + 28` (for overwriting `None` with `Some ck`). -/
theorem optChainKeyAt_none_entails_slots (A : RustAlloc) (pin : VecPin) (a : BitVec 64) :
    optChainKeyAt A pin none a ⊢
      memRegion a 24 ∗ memRegion (a + 24#64) 4 ∗ memRegion (a + 28#64) 4 := by
  rw [optChainKeyAt_none]
  have h8 := pointsTo64_entails_memRegion a optChainKeyNone
  refine Entails.trans (sepConj_mono_left h8) ?_
  rw [← memRegion_split a 8 24 (by decide),
      show (8 + 24 : Nat) = 24 + 8 from rfl,
      memRegion_split a 24 8 (by decide),
      show (8 : Nat) = 4 + 4 from rfl,
      memRegion_split (a + 24#64) 4 4 (by decide)]
  have h28 : a + 24#64 + 4#64 = a + 28#64 := by bv_arith
  rw [h28]
  exact Entails.refl _

/-- Update `message_keys` (`mkCap`, `mkPtr`, `keys`, `messageKeys`) in `chainAt` while keeping
`srk`, `priv`, and `ck`/`chainKey` unchanged. -/
theorem chainAt_of_update_messageKeys (A : RustAlloc)
    (g : ChainGhost) (c : ReceiverChain) (a : BitVec 64)
    (mkCap' mkPtr' : BitVec 64)
    (keys' : List MessageKeyGhost) (messageKeys' : List MessageKeyGenerator)
    (hsrk : PublicKey.deserialize g.srk.bytes = .ok c.senderRatchetKey)
    (hmax : messageKeys'.length ≤ maxMessageKeys)
    (hklen : keys'.length = messageKeys'.length)
    (hsrk_len : g.srk.bytes.length = 33)
    (hpriv : g.priv.bytes = []) :
    (vecGhostAt A g.srk a ∗
      vecGhostAt A g.priv (a + 24#64) ∗
      vecAt A 104 8 (messageKeyAt A) (a + 48#64) mkCap' mkPtr' (keys'.zip messageKeys') ∗
      optChainKeyAt A g.ck c.chainKey (a + 72#64)) ⊢
      chainAt A
        ({ g with mkCap := mkCap', mkPtr := mkPtr', keys := keys' },
         { c with messageKeys := messageKeys' }) a := by
  unfold chainAt
  exact Entails.pure_right ⟨hsrk, hmax, hklen, hsrk_len, hpriv⟩ (Entails.refl _)

/-- Update `chain_key` (`ck`, `chainKey`) in `chainAt` while keeping `srk`, `priv`, and
`message_keys` unchanged. -/
theorem chainAt_of_update_chainKey (A : RustAlloc)
    (g : ChainGhost) (c : ReceiverChain) (a : BitVec 64)
    (ckPin' : VecPin) (chainKey' : Option ChainKey)
    (hsrk : PublicKey.deserialize g.srk.bytes = .ok c.senderRatchetKey)
    (hmax : c.messageKeys.length ≤ maxMessageKeys)
    (hklen : g.keys.length = c.messageKeys.length)
    (hsrk_len : g.srk.bytes.length = 33)
    (hpriv : g.priv.bytes = []) :
    (vecGhostAt A g.srk a ∗
      vecGhostAt A g.priv (a + 24#64) ∗
      vecAt A 104 8 (messageKeyAt A) (a + 48#64) g.mkCap g.mkPtr (g.keys.zip c.messageKeys) ∗
      optChainKeyAt A ckPin' chainKey' (a + 72#64)) ⊢
      chainAt A
        ({ g with ck := ckPin' },
         { c with chainKey := chainKey' }) a := by
  unfold chainAt
  exact Entails.pure_right ⟨hsrk, hmax, hklen, hsrk_len, hpriv⟩ (Entails.refl _)

/-- Update both `message_keys` and `chain_key` in `chainAt` while keeping `srk` and `priv`
unchanged. -/
theorem chainAt_of_update_both (A : RustAlloc)
    (g : ChainGhost) (c : ReceiverChain) (a : BitVec 64)
    (mkCap' mkPtr' : BitVec 64)
    (keys' : List MessageKeyGhost) (messageKeys' : List MessageKeyGenerator)
    (ckPin' : VecPin) (chainKey' : Option ChainKey)
    (hsrk : PublicKey.deserialize g.srk.bytes = .ok c.senderRatchetKey)
    (hmax : messageKeys'.length ≤ maxMessageKeys)
    (hklen : keys'.length = messageKeys'.length)
    (hsrk_len : g.srk.bytes.length = 33)
    (hpriv : g.priv.bytes = []) :
    (vecGhostAt A g.srk a ∗
      vecGhostAt A g.priv (a + 24#64) ∗
      vecAt A 104 8 (messageKeyAt A) (a + 48#64) mkCap' mkPtr' (keys'.zip messageKeys') ∗
      optChainKeyAt A ckPin' chainKey' (a + 72#64)) ⊢
      chainAt A
        ({ g with mkCap := mkCap', mkPtr := mkPtr', keys := keys', ck := ckPin' },
         { c with messageKeys := messageKeys', chainKey := chainKey' }) a := by
  unfold chainAt
  exact Entails.pure_right ⟨hsrk, hmax, hklen, hsrk_len, hpriv⟩ (Entails.refl _)

def RatchetGhost.setChain (G : RatchetGhost) (i : Nat) (g' : ChainGhost) : RatchetGhost :=
  { G with chains := G.chains.set i g' }

def _root_.CryptoGames.LibsignalSession.RatchetState.setChain
    (st : RatchetState) (i : Nat) (c' : ReceiverChain) : RatchetState :=
  { st with receiverChains := st.receiverChains.set i c' }

theorem zip_set_eq {α β : Type} (xs : List α) (ys : List β) (i : Nat) (x' : α) (y' : β) :
    (xs.set i x').zip (ys.set i y') = (xs.zip ys).set i (x', y') := by
  induction xs generalizing ys i with
  | nil => simp
  | cons x xs ih =>
    cases ys with
    | nil => simp
    | cons y ys =>
      cases i with
      | zero => simp
      | succ k => simp [ih]

namespace RatchetGhost.AgreeExcept

theorem refl (G : RatchetGhost) (i : Option Nat) : G.AgreeExcept G i := by
  refine ⟨rfl, rfl, rfl, rfl, fun j _ _ => ?_⟩
  split <;> simp

theorem refl_none (G : RatchetGhost) : G.AgreeExcept G none :=
  refl G none

theorem of_none {G G' : RatchetGhost} (i : Option Nat) (h : G.AgreeExcept G' none) :
    G.AgreeExcept G' i := by
  obtain ⟨hcap, hptr, hpad, hlen, hj⟩ := h
  refine ⟨hcap, hptr, hpad, hlen, fun j hj1 hj2 => ?_⟩
  have heq : G'.chains[j] = G.chains[j] := by
    have := hj j hj1 hj2
    simpa using this
  split
  · exact ⟨congrArg ChainGhost.srk heq, congrArg ChainGhost.priv heq⟩
  · exact heq

theorem trans {G₁ G₂ G₃ : RatchetGhost} {i : Option Nat}
    (h₁₂ : G₁.AgreeExcept G₂ i) (h₂₃ : G₂.AgreeExcept G₃ i) :
    G₁.AgreeExcept G₃ i := by
  obtain ⟨hcap1, hptr1, hpad1, hlen1, hj1⟩ := h₁₂
  obtain ⟨hcap2, hptr2, hpad2, hlen2, hj2⟩ := h₂₃
  refine ⟨hcap2.trans hcap1, hptr2.trans hptr1, hpad2.trans hpad1, hlen2.trans hlen1,
    fun j h1 h3 => ?_⟩
  have h2 : j < G₂.chains.length := by omega
  have q1 := hj1 j h1 h2
  have q2 := hj2 j h2 h3
  split at q1 <;> rename_i hsplit
  · simp only [hsplit, ↓reduceIte] at q2 ⊢
    exact ⟨q2.1.trans q1.1, q2.2.trans q1.2⟩
  · simp only [hsplit, ↓reduceIte] at q2 ⊢
    exact q2.trans q1

theorem setChain (G : RatchetGhost) {i : Nat} (hi : i < G.chains.length) (g' : ChainGhost)
    (hsrk : g'.srk = G.chains[i].srk) (hpriv : g'.priv = G.chains[i].priv) :
    G.AgreeExcept (G.setChain i g') (some i) := by
  refine ⟨rfl, rfl, rfl, List.length_set .., fun j hj hj' => ?_⟩
  by_cases hij : i = j
  · subst hij
    simp [RatchetGhost.setChain, hsrk, hpriv]
  · have hne : some i ≠ some j := by simp [hij]
    simp [RatchetGhost.setChain, hij, hne]

theorem setChain_of_agreeExcept {G G₁ : RatchetGhost} {i : Nat}
    (h₁ : G.AgreeExcept G₁ (some i)) (hi : i < G₁.chains.length) (g' : ChainGhost)
    (hsrk : g'.srk = G₁.chains[i].srk) (hpriv : g'.priv = G₁.chains[i].priv) :
    G.AgreeExcept (G₁.setChain i g') (some i) :=
  h₁.trans (setChain G₁ hi g' hsrk hpriv)

end RatchetGhost.AgreeExcept

/-- Split `ratchetAt A self G st` at receiver chain `i < st.receiverChains.length`, exposing
`chainAt A (G.chains[i], st.receiverChains[i]) (G.chainsPtr + BitVec.ofNat 64 (i * 104))`
and the remaining `RatchetState` resources. -/
theorem ratchetAt_split_chain (A : RustAlloc) (self : BitVec 64) (G : RatchetGhost)
    (st : RatchetState) {i : Nat} (hi : i < st.receiverChains.length)
    (hgi : i < G.chains.length) :
    ratchetAt A self G st ⊢
      ⌜G.chains.length = st.receiverChains.length ∧ G.senderPad.length = 100 ∧
        st.maxForwardJumps < 2 ^ 64 ∧
        st.receiverChains.length ≤ G.chainsCap.toNat ∧
        G.chainsCap.toNat * 104 < 2 ^ 63 ∧ G.chainsPtr ≠ 0 ∧ G.chainsCap ≠ 0⌝ ∗
      vecHeader self G.chainsCap G.chainsPtr (BitVec.ofNat 64 st.receiverChains.length) ∗
      A.live G.chainsPtr (G.chainsCap.toNat * 104) 8 ∗
      chainAt A (G.chains[i], st.receiverChains[i])
        (G.chainsPtr + BitVec.ofNat 64 (i * 104)) ∗
      arrayAt (chainAt A) 104 G.chainsPtr ((G.chains.zip st.receiverChains).take i) ∗
      arrayAt (chainAt A) 104 (G.chainsPtr + BitVec.ofNat 64 ((i + 1) * 104))
        ((G.chains.zip st.receiverChains).drop (i + 1)) ∗
      memRegion (G.chainsPtr + BitVec.ofNat 64 (st.receiverChains.length * 104))
        ((G.chainsCap.toNat - st.receiverChains.length) * 104) ∗
      ((self + 24#64) ↦ₛ optSenderChainBytes st.senderChain G.senderPad) ∗
      ((self + 128#64) ↦ₛ keyToBytes32 st.rootKey) ∗
      ((self + 160#64) ↦₆₄ BitVec.ofNat 64 st.maxForwardJumps) ∗
      ((self + 168#64) ↦₃₂ st.previousCounter) ∗ memRegion (self + 172#64) 4 := by
  unfold ratchetAt vecAt vecBuf
  apply Entails.pure_left
  rintro ⟨hchains_len, hpad_len, hmax_jumps⟩
  have hzip_len : (G.chains.zip st.receiverChains).length = st.receiverChains.length := by
    simp [hchains_len]
  have hi_zip : i < (G.chains.zip st.receiverChains).length := by
    rw [hzip_len]; exact hi
  rw [hzip_len]
  have hpull1 :
      ((vecHeader self G.chainsCap G.chainsPtr (BitVec.ofNat 64 st.receiverChains.length) ∗
        (⌜st.receiverChains.length ≤ G.chainsCap.toNat ∧
          G.chainsCap.toNat * 104 < 2 ^ 63 ∧ G.chainsPtr ≠ 0⌝ ∗
         if G.chainsCap = 0 then emp
         else
           A.live G.chainsPtr (G.chainsCap.toNat * 104) 8 ∗
             arrayAt (chainAt A) 104 G.chainsPtr (G.chains.zip st.receiverChains) ∗
             memRegion (G.chainsPtr + BitVec.ofNat 64 (st.receiverChains.length * 104))
               ((G.chainsCap.toNat - st.receiverChains.length) * 104))) ∗
       ((self + 24#64) ↦ₛ optSenderChainBytes st.senderChain G.senderPad) ∗
       ((self + 128#64) ↦ₛ keyToBytes32 st.rootKey) ∗
       ((self + 160#64) ↦₆₄ BitVec.ofNat 64 st.maxForwardJumps) ∗
       ((self + 168#64) ↦₃₂ st.previousCounter) ∗ memRegion (self + 172#64) 4) =
      (⌜st.receiverChains.length ≤ G.chainsCap.toNat ∧
        G.chainsCap.toNat * 104 < 2 ^ 63 ∧ G.chainsPtr ≠ 0⌝ ∗
       (vecHeader self G.chainsCap G.chainsPtr (BitVec.ofNat 64 st.receiverChains.length) ∗
        (if G.chainsCap = 0 then emp
         else
           A.live G.chainsPtr (G.chainsCap.toNat * 104) 8 ∗
             arrayAt (chainAt A) 104 G.chainsPtr (G.chains.zip st.receiverChains) ∗
             memRegion (G.chainsPtr + BitVec.ofNat 64 (st.receiverChains.length * 104))
               ((G.chainsCap.toNat - st.receiverChains.length) * 104)) ∗
        ((self + 24#64) ↦ₛ optSenderChainBytes st.senderChain G.senderPad) ∗
        ((self + 128#64) ↦ₛ keyToBytes32 st.rootKey) ∗
        ((self + 160#64) ↦₆₄ BitVec.ofNat 64 st.maxForwardJumps) ∗
        ((self + 168#64) ↦₃₂ st.previousCounter) ∗ memRegion (self + 172#64) 4)) := by
    ac_rfl
  rw [hpull1]
  apply Entails.pure_left
  rintro ⟨hcap_le, hcap_lt, hptr_ne⟩
  have hcap_ne : G.chainsCap ≠ 0 := by
    intro h0; rw [h0] at hcap_le; change st.receiverChains.length ≤ 0 at hcap_le; omega
  simp only [hcap_ne, ↓reduceIte,
    arrayAt_split_at (chainAt A) 104 G.chainsPtr (G.chains.zip st.receiverChains) hi_zip]
  have hget : (G.chains.zip st.receiverChains)[i] = (G.chains[i], st.receiverChains[i]) :=
    List.getElem_zip
  rw [hget]
  apply Entails.pure_right
    ⟨hchains_len, hpad_len, hmax_jumps, hcap_le, hcap_lt, hptr_ne, hcap_ne⟩
  have hpull :
      (vecHeader self G.chainsCap G.chainsPtr (BitVec.ofNat 64 st.receiverChains.length) ∗
        (A.live G.chainsPtr (G.chainsCap.toNat * 104) 8 ∗
          (chainAt A (G.chains[i], st.receiverChains[i])
            (G.chainsPtr + BitVec.ofNat 64 (i * 104)) ∗
           (arrayAt (chainAt A) 104 G.chainsPtr ((G.chains.zip st.receiverChains).take i) ∗
            arrayAt (chainAt A) 104 (G.chainsPtr + BitVec.ofNat 64 ((i + 1) * 104))
              ((G.chains.zip st.receiverChains).drop (i + 1)))) ∗
          memRegion (G.chainsPtr + BitVec.ofNat 64 (st.receiverChains.length * 104))
            ((G.chainsCap.toNat - st.receiverChains.length) * 104)) ∗
        ((self + 24#64) ↦ₛ optSenderChainBytes st.senderChain G.senderPad) ∗
        ((self + 128#64) ↦ₛ keyToBytes32 st.rootKey) ∗
        ((self + 160#64) ↦₆₄ BitVec.ofNat 64 st.maxForwardJumps) ∗
        ((self + 168#64) ↦₃₂ st.previousCounter) ∗ memRegion (self + 172#64) 4) =
      (vecHeader self G.chainsCap G.chainsPtr (BitVec.ofNat 64 st.receiverChains.length) ∗
        A.live G.chainsPtr (G.chainsCap.toNat * 104) 8 ∗
        chainAt A (G.chains[i], st.receiverChains[i])
          (G.chainsPtr + BitVec.ofNat 64 (i * 104)) ∗
        arrayAt (chainAt A) 104 G.chainsPtr ((G.chains.zip st.receiverChains).take i) ∗
        arrayAt (chainAt A) 104 (G.chainsPtr + BitVec.ofNat 64 ((i + 1) * 104))
          ((G.chains.zip st.receiverChains).drop (i + 1)) ∗
        memRegion (G.chainsPtr + BitVec.ofNat 64 (st.receiverChains.length * 104))
          ((G.chainsCap.toNat - st.receiverChains.length) * 104) ∗
        ((self + 24#64) ↦ₛ optSenderChainBytes st.senderChain G.senderPad) ∗
        ((self + 128#64) ↦ₛ keyToBytes32 st.rootKey) ∗
        ((self + 160#64) ↦₆₄ BitVec.ofNat 64 st.maxForwardJumps) ∗
        ((self + 168#64) ↦₃₂ st.previousCounter) ∗ memRegion (self + 172#64) 4) := by
    ac_rfl
  rw [hpull]
  exact Entails.refl _

/-- Reassemble `ratchetAt A self (G.setChain i g') (st.setChain i c')` after updating receiver
chain `i` in place from `chainAt A (G.chains[i], st.receiverChains[i])` to `chainAt A (g', c')`. -/
theorem ratchetAt_set_chain (A : RustAlloc) (self : BitVec 64) (G : RatchetGhost)
    (st : RatchetState) {i : Nat} (hi : i < st.receiverChains.length)
    (g' : ChainGhost) (c' : ReceiverChain)
    (hchains_len : G.chains.length = st.receiverChains.length)
    (hpad_len : G.senderPad.length = 100)
    (hmax_jumps : st.maxForwardJumps < 2 ^ 64)
    (hcap_le : st.receiverChains.length ≤ G.chainsCap.toNat)
    (hcap_lt : G.chainsCap.toNat * 104 < 2 ^ 63)
    (hptr_ne : G.chainsPtr ≠ 0) :
    (vecHeader self G.chainsCap G.chainsPtr (BitVec.ofNat 64 st.receiverChains.length) ∗
      A.live G.chainsPtr (G.chainsCap.toNat * 104) 8 ∗
      chainAt A (g', c') (G.chainsPtr + BitVec.ofNat 64 (i * 104)) ∗
      arrayAt (chainAt A) 104 G.chainsPtr ((G.chains.zip st.receiverChains).take i) ∗
      arrayAt (chainAt A) 104 (G.chainsPtr + BitVec.ofNat 64 ((i + 1) * 104))
        ((G.chains.zip st.receiverChains).drop (i + 1)) ∗
      memRegion (G.chainsPtr + BitVec.ofNat 64 (st.receiverChains.length * 104))
        ((G.chainsCap.toNat - st.receiverChains.length) * 104) ∗
      ((self + 24#64) ↦ₛ optSenderChainBytes st.senderChain G.senderPad) ∗
      ((self + 128#64) ↦ₛ keyToBytes32 st.rootKey) ∗
      ((self + 160#64) ↦₆₄ BitVec.ofNat 64 st.maxForwardJumps) ∗
      ((self + 168#64) ↦₃₂ st.previousCounter) ∗ memRegion (self + 172#64) 4) ⊢
      ratchetAt A self (G.setChain i g') (st.setChain i c') := by
  have hcap_ne : G.chainsCap ≠ 0 := by
    intro h0; rw [h0] at hcap_le; change st.receiverChains.length ≤ 0 at hcap_le; omega
  have hzip_len : (G.chains.zip st.receiverChains).length = st.receiverChains.length := by
    simp [hchains_len]
  have hi_zip : i < (G.chains.zip st.receiverChains).length := by
    rw [hzip_len]; exact hi
  unfold ratchetAt RatchetGhost.setChain RatchetState.setChain vecAt
  simp only [List.length_set]
  apply Entails.pure_right ⟨hchains_len, hpad_len, hmax_jumps⟩
  rw [zip_set_eq, vecBuf_of_ne_zero A 104 8 (chainAt A) _ _ _ hcap_ne]
  simp only [List.length_set, hzip_len]
  rw [← arrayAt_set (chainAt A) 104 G.chainsPtr (G.chains.zip st.receiverChains) hi_zip (g', c')]
  have hpull :
      (vecHeader self G.chainsCap G.chainsPtr (BitVec.ofNat 64 st.receiverChains.length) ∗
        A.live G.chainsPtr (G.chainsCap.toNat * 104) 8 ∗
        chainAt A (g', c') (G.chainsPtr + BitVec.ofNat 64 (i * 104)) ∗
        arrayAt (chainAt A) 104 G.chainsPtr ((G.chains.zip st.receiverChains).take i) ∗
        arrayAt (chainAt A) 104 (G.chainsPtr + BitVec.ofNat 64 ((i + 1) * 104))
          ((G.chains.zip st.receiverChains).drop (i + 1)) ∗
        memRegion (G.chainsPtr + BitVec.ofNat 64 (st.receiverChains.length * 104))
          ((G.chainsCap.toNat - st.receiverChains.length) * 104) ∗
        ((self + 24#64) ↦ₛ optSenderChainBytes st.senderChain G.senderPad) ∗
        ((self + 128#64) ↦ₛ keyToBytes32 st.rootKey) ∗
        ((self + 160#64) ↦₆₄ BitVec.ofNat 64 st.maxForwardJumps) ∗
        ((self + 168#64) ↦₃₂ st.previousCounter) ∗ memRegion (self + 172#64) 4) =
      ((vecHeader self G.chainsCap G.chainsPtr (BitVec.ofNat 64 st.receiverChains.length) ∗
        (A.live G.chainsPtr (G.chainsCap.toNat * 104) 8 ∗
          (chainAt A (g', c') (G.chainsPtr + BitVec.ofNat 64 (i * 104)) ∗
           (arrayAt (chainAt A) 104 G.chainsPtr ((G.chains.zip st.receiverChains).take i) ∗
            arrayAt (chainAt A) 104 (G.chainsPtr + BitVec.ofNat 64 ((i + 1) * 104))
              ((G.chains.zip st.receiverChains).drop (i + 1)))) ∗
          memRegion (G.chainsPtr + BitVec.ofNat 64 (st.receiverChains.length * 104))
            ((G.chainsCap.toNat - st.receiverChains.length) * 104))) ∗
        ((self + 24#64) ↦ₛ optSenderChainBytes st.senderChain G.senderPad) ∗
        ((self + 128#64) ↦ₛ keyToBytes32 st.rootKey) ∗
        ((self + 160#64) ↦₆₄ BitVec.ofNat 64 st.maxForwardJumps) ∗
        ((self + 168#64) ↦₃₂ st.previousCounter) ∗ memRegion (self + 172#64) 4) := by
    ac_rfl
  rw [hpull]
  apply sepConj_mono_left
  apply sepConj_mono_right
  exact Entails.pure_right ⟨hcap_le, hcap_lt, hptr_ne⟩ (Entails.refl _)

end CryptoVerification.LibsignalSessionRepr

