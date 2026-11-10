/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Abi.Rust.Heap.Alloc
public import ProofLib.SepLogic.Bytes
public import ProofLib.SepLogic.Region
public import ProofLib.SepLogic.SliceArray
public import ProofLib.BV.Arith

/-!
# Rust `Vec<T>`, `Vec<u8>`, and `Box<[T]>` Representation

Separation-logic representation predicates and structural lemmas for AArch64 Rust `Vec<T>`,
`Vec<u8>`, `String`, and `Box<[T]>` over `RustAlloc`: 24-byte `{cap, ptr, len}` headers
(`vecHeader`), fixed-stride element arrays (`arrayAt`), and heap-backed buffers (`vecBuf`,
`vecAt`, `vecU8Buf`, `vecU8At`, `boxAt`, `boxU8At`).
-/

@[expose] public section

namespace ProofLib.RustHeap

open Arm64 ProofLib

/-! ## Core Representation Predicates -/

/-- The 24-byte `Vec` header `{cap, ptr, len}` at `v` (`cap` at `+0`, `ptr` at `+8`, `len` at `+16`). -/
def vecHeader (v cap ptr len : BitVec 64) : SepProp :=
  (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ len)

/-- The elements `xs` laid out from `base` with byte stride `stride`:
    `elem x₀ base ∗ elem x₁ (base + stride) ∗ ...` (an iterated separating conjunction). -/
def arrayAt {α : Type} (elem : α → BitVec 64 → SepProp) (stride : Nat) :
    BitVec 64 → List α → SepProp
  | _, [] => emp
  | base, x :: xs => elem x base ∗ arrayAt elem stride (base + BitVec.ofNat 64 stride) xs

/-- The heap buffer of a `Vec<T>` (element byte size `stride`, alignment `align`) with capacity
    `cap` at `ptr`, holding `xs`: the elements, the spare capacity, and the allocation's `live`
    token (none when `cap = 0`, where `ptr` is a non-null dangling pointer). -/
def vecBuf {α : Type} (A : RustAlloc) (stride align : Nat) (elem : α → BitVec 64 → SepProp)
    (cap ptr : BitVec 64) (xs : List α) : SepProp :=
  ⌜xs.length ≤ cap.toNat ∧ cap.toNat * stride < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    (if cap = 0 then emp
     else A.live ptr (cap.toNat * stride) align ∗ arrayAt elem stride ptr xs ∗
       memRegion (ptr + BitVec.ofNat 64 (xs.length * stride)) ((cap.toNat - xs.length) * stride))

/-- A `Vec<T>` at `v` with capacity `cap` and buffer `ptr` holding `xs`. -/
def vecAt {α : Type} (A : RustAlloc) (stride align : Nat) (elem : α → BitVec 64 → SepProp)
    (v cap ptr : BitVec 64) (xs : List α) : SepProp :=
  vecHeader v cap ptr (BitVec.ofNat 64 xs.length) ∗ vecBuf A stride align elem cap ptr xs


/-- The heap buffer of a `Vec<u8>` (capacity `cap`, pointer `ptr`, bytes `bs`), detached from its
    24-byte `vecHeader`. Moving or copying the 24-byte header leaves `vecU8Buf` untouched. -/
def vecU8Buf (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))

/-- A `Vec<u8>` at `v` with capacity `cap`, buffer `ptr`, and contents `bs`. Same layout as `vecAt`
    with `stride = align = 1`, written with a contiguous byte slice `ptr ↦ₛ bs`. -/
def vecU8At (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  vecHeader v cap ptr (BitVec.ofNat 64 bs.length) ∗
    ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))


/-- A `Box<[T]>` `(ptr, xs.length)` holding `xs` with element stride `stride` and alignment
    `align`. When `xs = []`, `ptr` is a non-null dangling pointer and no heap block is owned. -/
def boxAt {α : Type} (A : RustAlloc) (stride align : Nat) (elem : α → BitVec 64 → SepProp)
    (ptr : BitVec 64) (xs : List α) : SepProp :=
  ⌜xs.length * stride < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    (if xs = [] then emp
     else A.live ptr (xs.length * stride) align ∗ arrayAt elem stride ptr xs)

/-- A `Box<[u8]>` (or `Box<str>`) `(ptr, bs.length)` holding `bs`. -/
def boxU8At (A : RustAlloc) (ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    (if bs = [] then emp else A.live ptr bs.length 1 ∗ (ptr ↦ₛ bs))

/-! ## `vecHeader` Byte Representation and Region Bridges -/

/-- The 24 little-endian bytes of a `Vec` header `{cap, ptr, len}`. -/
def vecHeaderBytes (cap ptr len : BitVec 64) : List (BitVec 8) :=
  unpack64 cap ++ unpack64 ptr ++ unpack64 len

@[scoped simp]
theorem vecHeaderBytes_length (cap ptr len : BitVec 64) :
    (vecHeaderBytes cap ptr len).length = 24 := by
  simp [vecHeaderBytes]

/-- `vecHeader v cap ptr len` is equivalent to the 24-byte slice `v ↦ₛ vecHeaderBytes cap ptr len`. -/
theorem vecHeader_eq_pointsToBytes (v cap ptr len : BitVec 64) :
    vecHeader v cap ptr len = (v ↦ₛ vecHeaderBytes cap ptr len) := by
  unfold vecHeader vecHeaderBytes
  rw [List.append_assoc, pointsToBytes_append, pointsToBytes_append]
  simp only [unpack64_length]
  rw [← pointsTo64_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes]
  have h16 : v + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 = v + 16#64 := by bv_arith
  rw [h16]

/-- Forgetting the values in `vecHeader v cap ptr len` yields `memRegion v 24`. -/
theorem vecHeader_entails_memRegion (v cap ptr len : BitVec 64) :
    vecHeader v cap ptr len ⊢ memRegion v 24 := by
  rw [vecHeader_eq_pointsToBytes]
  have h := pointsToBytes_entails_memRegion v (vecHeaderBytes cap ptr len)
  rwa [vecHeaderBytes_length] at h

/-! ## `arrayAt` Structural Lemmas -/

@[scoped simp]
theorem arrayAt_nil {α : Type} (elem : α → BitVec 64 → SepProp) (stride : Nat) (base : BitVec 64) :
    arrayAt elem stride base [] = emp := rfl

@[scoped simp]
theorem arrayAt_cons {α : Type} (elem : α → BitVec 64 → SepProp) (stride : Nat)
    (base : BitVec 64) (x : α) (xs : List α) :
    arrayAt elem stride base (x :: xs) =
      elem x base ∗ arrayAt elem stride (base + BitVec.ofNat 64 stride) xs := rfl

private theorem addr_stride_succ (base : BitVec 64) (n stride : Nat) :
    base + BitVec.ofNat 64 stride + BitVec.ofNat 64 (n * stride) =
      base + BitVec.ofNat 64 ((n + 1) * stride) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  have h : stride + n * stride = (n + 1) * stride := by
    rw [Nat.succ_mul, Nat.add_comm]
  rw [h]

/-- `arrayAt` over `xs ++ ys` splits at `base + BitVec.ofNat 64 (xs.length * stride)`. -/
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

/-- Split `arrayAt` at any index `i` into `xs.take i` and `xs.drop i`. -/
theorem arrayAt_take_drop {α : Type} (elem : α → BitVec 64 → SepProp) (stride : Nat)
    (base : BitVec 64) (xs : List α) (i : Nat) :
    arrayAt elem stride base xs =
      arrayAt elem stride base (xs.take i) ∗
        arrayAt elem stride (base + BitVec.ofNat 64 ((xs.take i).length * stride)) (xs.drop i) := by
  conv => lhs; rw [← List.take_append_drop i xs]
  exact arrayAt_append elem stride base (xs.take i) (xs.drop i)

/-- Split `arrayAt` at index `i ≤ xs.length` into `xs.take i` and `xs.drop i`. -/
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

/-- `a ↦ₛ bs` agrees with `arrayAt` of 1-byte cells `fun b addr => addr ↦₈ b` with stride 1. -/
theorem pointsToBytes_eq_arrayAt (a : BitVec 64) (bs : List (BitVec 8)) :
    (a ↦ₛ bs) = arrayAt (fun b addr => addr ↦₈ b) 1 a bs := by
  induction bs generalizing a with
  | nil => rw [pointsToBytes_nil, arrayAt_nil]
  | cons b bs ih =>
    rw [pointsToBytes_cons, arrayAt_cons, ih]

/-! ## `vecBuf`, `vecAt`, `vecU8Buf`, `vecU8At`, and `boxU8At` Lemmas -/

/-- Unfold `vecBuf` when `cap ≠ 0`. -/
theorem vecBuf_of_ne_zero {α : Type} (A : RustAlloc) (stride align : Nat)
    (elem : α → BitVec 64 → SepProp) (cap ptr : BitVec 64) (xs : List α) (hcap : cap ≠ 0) :
    vecBuf A stride align elem cap ptr xs =
      ⌜xs.length ≤ cap.toNat ∧ cap.toNat * stride < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        A.live ptr (cap.toNat * stride) align ∗ arrayAt elem stride ptr xs ∗
        memRegion (ptr + BitVec.ofNat 64 (xs.length * stride)) ((cap.toNat - xs.length) * stride) := by
  unfold vecBuf
  simp only [hcap, ↓reduceIte]


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


/-- `vecU8At` splits into its 24-byte `vecHeader` at `v` and its detached heap buffer `vecU8Buf`. -/
theorem vecU8At_eq_header_sep_buf (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs = vecHeader v cap ptr (BitVec.ofNat 64 bs.length) ∗ vecU8Buf A cap ptr bs := by
  unfold vecU8At vecU8Buf
  ac_rfl


/-- `vecU8At` agrees with the generic `vecAt` at `stride = 1`, `align = 1`,
    `elem = (fun b addr => addr ↦₈ b)`. -/
theorem vecU8At_eq_vecAt (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs = vecAt A 1 1 (fun b addr => addr ↦₈ b) v cap ptr bs := by
  unfold vecU8At vecAt vecBuf
  simp only [Nat.mul_one, ← pointsToBytes_eq_arrayAt]

/-- `boxU8At` agrees with the generic `boxAt` at `stride = 1`, `align = 1`,
    `elem = (fun b addr => addr ↦₈ b)`. -/
theorem boxU8At_eq_boxAt (A : RustAlloc) (ptr : BitVec 64) (bs : List (BitVec 8)) :
    boxU8At A ptr bs = boxAt A 1 1 (fun b addr => addr ↦₈ b) ptr bs := by
  unfold boxU8At boxAt
  simp only [Nat.mul_one, ← pointsToBytes_eq_arrayAt]


/-- A `vecU8Buf` collapses its contents and spare capacity into a single `memRegion ptr cap.toNat`
    for `__rust_dealloc` (`rustDeallocIdealSpec A`). -/
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

end ProofLib.RustHeap

end
