/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.RustHeap.Alloc

/-!
# Separation-Logic Representation of Rust `Vec<T>` and `Vec<u8>`

**Checked by Lean.** Separation-logic predicates (`vecHeader`, `arrayAt`, `vecBuf`, `vecAt`,
`vecOf`, `vecU8At`, `vecU8`) modeling `alloc::vec::Vec<T>` (`{cap @ +0, ptr @ +8, len @ +16}`,
24 bytes on `aarch64`, `rustc` 1.98) with heap ownership tracked through `RustAlloc`. When
`cap = 0`, `ptr` is a non-null dangling pointer with no live heap block; spare capacity
`[len, cap)` is owned uninitialized memory (`memRegion`). See `Computational/docs/TRUSTED_BASE.md`.
-/

@[expose] public section

namespace CryptoVerification.RustHeap

open Arm64

/-- The 24-byte `Vec` header `{cap, ptr, len}` at `v`. -/
def vecHeader (v cap ptr len : BitVec 64) : SepProp :=
  (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ len)

/-- The elements `xs` laid out from `base` with stride `stride`: `elem x₀ base ∗ elem x₁ (base +
stride) ∗ …` (an iterated separating conjunction). -/
def arrayAt {α : Type} (elem : α → BitVec 64 → SepProp) (stride : Nat) :
    BitVec 64 → List α → SepProp
  | _, [] => emp
  | base, x :: xs => elem x base ∗ arrayAt elem stride (base + BitVec.ofNat 64 stride) xs

/-- The heap buffer of a `Vec<T>` (element size `stride`, alignment `align`) with capacity `cap` at
`ptr`, holding `xs`: the elements, the spare capacity, and the allocation's `live` token (none when
`cap = 0`, where `ptr` is dangling). -/
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

/-- Some `Vec<T>` at `v` holding `xs` (capacity and buffer existential). -/
def vecOf {α : Type} (A : RustAlloc) (stride align : Nat) (elem : α → BitVec 64 → SepProp)
    (v : BitVec 64) (xs : List α) : SepProp :=
  ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, vecAt A stride align elem v cap ptr xs

/-- A `Vec<u8>` at `v` with capacity `cap`, buffer `ptr` and contents `bs`. Same layout as
`vecAt` with `stride = align = 1`, but the contents are one byte block `ptr ↦ₛ bs` (the form of the libc
`memcpy` / `memmove` contracts, `ProofLib.Hoare.LibcHooks`). -/
def vecU8At (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  vecHeader v cap ptr (BitVec.ofNat 64 bs.length) ∗
    ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))

/-- Some `Vec<u8>` (or `String`) at `v` with contents `bs`. -/
def vecU8 (A : RustAlloc) (v : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, vecU8At A v cap ptr bs

end CryptoVerification.RustHeap
