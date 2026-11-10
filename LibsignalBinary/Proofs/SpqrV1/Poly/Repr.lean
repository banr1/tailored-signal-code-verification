/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.Poly
public import LibsignalBinary.Specifications.LibsignalSessionRepr

/-!
# AArch64 Memory Layouts for `GF16`, `Pt`, `SortedSet<Pt>`, and `Poly`

**Checked by Lean.**

AArch64 field offsets and separation-logic representation predicates for `GF16` (2 B, align 2),
`Pt` (`{ x: GF16 @ +0, y: GF16 @ +2 }`, 4 B, align 2), `SortedSet<Pt>` (24-byte `Vec<Pt>` header,
stride 4, align 2), and `Poly` (24-byte `Vec<GF16>` header, stride 2, align 2).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Poly

open Arm64 ProofLib
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalSpqrV1

/-! ## Layout constants and field offsets -/

/-- Byte size of `GF16` (`size_of::<GF16>() == 2`). -/
abbrev gf16Stride : Nat := 2

/-- Alignment of `GF16` in bytes (`align_of::<GF16>() == 2`). -/
abbrev gf16Align : Nat := 2

/-- Byte size of `Pt` (`size_of::<Pt>() == 4`). -/
abbrev ptStride : Nat := 4

/-- Alignment of `Pt` in bytes (`align_of::<Pt>() == 2`). -/
abbrev ptAlign : Nat := 2

/-- Byte offset of `Pt.x` (`GF16`, `u16`) within `Pt` (`+0`). -/
abbrev ptXOff : Nat := 0

/-- Byte offset of `Pt.y` (`GF16`, `u16`) within `Pt` (`+2`). -/
abbrev ptYOff : Nat := 2

/-- Byte size of `Poly` (`coefficients: Vec<GF16>`) and `SortedSet<Pt>` (`vec: Vec<Pt>`) (`24` bytes). -/
abbrev vecHeaderBytes : Nat := 24

abbrev polyStride : Nat := 24

/-- Alignment of `Poly` in bytes (`align_of::<Poly>() == 8`). -/
abbrev polyAlign : Nat := 8

abbrev sortedSetPtStride : Nat := 24

/-- Alignment of `SortedSet<Pt>` in bytes (`align_of::<SortedSet<Pt>>() == 8`). -/
abbrev sortedSetPtAlign : Nat := 8

/-- Byte offset of `cap` (`usize`) in a `Vec<T>` / `Poly` / `SortedSet<Pt>` header (`+0`). -/
abbrev vecCapOff : Nat := 0

/-- Byte offset of `ptr` (`NonNull<T>`) in a `Vec<T>` / `Poly` / `SortedSet<Pt>` header (`+8`). -/
abbrev vecPtrOff : Nat := 8

/-- Byte offset of `len` (`usize`) in a `Vec<T>` / `Poly` / `SortedSet<Pt>` header (`+16`). -/
abbrev vecLenOff : Nat := 16

/-- Number of polynomials / point sets in `PolyEncoder` / `PolyDecoder` (`NUM_POLYS = 16`). -/
abbrev numPolys : Nat := 16

/-- Byte size of `[Poly; 16]` or `[SortedSet<Pt>; 16]` (`16 * 24 = 384 = 0x180`). -/
abbrev polyArrayBytes : Nat := 384

/-! ## `GF16` element and slice representation predicates -/

/-- A read-write `GF16` element at address `a` (`a ↦₁₆ g.value`). -/
def gf16At (g : GF16) (a : BitVec 64) : SepProp :=
  a ↦₁₆ g.value

/-- A read-only `GF16` element at address `a` (`a ↦₁₆ᵣ g.value`). -/
def gf16RoAt (g : GF16) (a : BitVec 64) : SepProp :=
  a ↦₁₆ᵣ g.value

/-- Contiguous read-write slice of `GF16` elements (`&mut [GF16]`) starting at `ptr` (stride 2). -/
def gf16SliceAt (ptr : BitVec 64) (cs : List GF16) : SepProp :=
  arrayAt gf16At gf16Stride ptr cs

/-- Contiguous read-only slice of `GF16` elements (`&[GF16]`) starting at `ptr` (stride 2). -/
def gf16SliceRoAt (ptr : BitVec 64) (cs : List GF16) : SepProp :=
  arrayAt gf16RoAt gf16Stride ptr cs

/-! ## `Pt` element and slice representation predicates -/

/-- A read-write `Pt` (`{ x: GF16, y: GF16 }`, 4 bytes) at address `a`:
`x` at `a + 0`, `y` at `a + 2`. -/
def ptAt (pt : Pt) (a : BitVec 64) : SepProp :=
  (a ↦₁₆ pt.x.value) ∗ ((a + 2#64) ↦₁₆ pt.y.value)

/-- A read-only `Pt` (`{ x: GF16, y: GF16 }`, 4 bytes) at address `a`:
`x` at `a + 0`, `y` at `a + 2`. -/
def ptRoAt (pt : Pt) (a : BitVec 64) : SepProp :=
  (a ↦₁₆ᵣ pt.x.value) ∗ ((a + 2#64) ↦₁₆ᵣ pt.y.value)

/-- Contiguous read-write slice of `Pt` elements (`&mut [Pt]`) starting at `ptr` (stride 4). -/
def ptSliceAt (ptr : BitVec 64) (pts : List Pt) : SepProp :=
  arrayAt ptAt ptStride ptr pts

/-- Contiguous read-only slice of `Pt` elements (`&[Pt]`) starting at `ptr` (stride 4). -/
def ptSliceRoAt (ptr : BitVec 64) (pts : List Pt) : SepProp :=
  arrayAt ptRoAt ptStride ptr pts

/-! ## `SortedSet<Pt>` (`sorted_vec::SortedSet<Pt>`) representation predicates -/

/-- Heap buffer of a `SortedSet<Pt>` (`Vec<Pt>`, stride 4, alignment 2) with capacity `cap` at `ptr`
holding `s.vec`. -/
def sortedSetPtBuf (A : RustAlloc) (cap ptr : BitVec 64) (s : SortedSetPt) : SepProp :=
  vecBuf A ptStride ptAlign ptAt cap ptr s.vec

/-- A `SortedSet<Pt>` at address `v` with pinned capacity `cap` and buffer pointer `ptr` holding
`s.vec`: 24-byte `Vec<Pt>` header `(cap, ptr, s.vec.length)` at `(v + 0, v + 8, v + 16)` plus its
heap buffer `sortedSetPtBuf`. -/
def sortedSetPtAt (A : RustAlloc) (v cap ptr : BitVec 64) (s : SortedSetPt) : SepProp :=
  vecAt A ptStride ptAlign ptAt v cap ptr s.vec

/-- A `SortedSet<Pt>` at address `v` with ghost pin `pin : VecPin` holding `s`. -/
def sortedSetPtPinAt (A : RustAlloc) (pin : VecPin) (s : SortedSetPt) (v : BitVec 64) : SepProp :=
  sortedSetPtAt A v pin.cap pin.ptr s

/-- Some `SortedSet<Pt>` at address `v` holding `s` (capacity and buffer pointer existentially
quantified). -/
def sortedSetPtOf (A : RustAlloc) (v : BitVec 64) (s : SortedSetPt) : SepProp :=
  vecOf A ptStride ptAlign ptAt v s.vec

/-! ## `Poly` (`spqr::encoding::polynomial::Poly`) representation predicates -/

/-- Heap buffer of a `Poly` (`coefficients: Vec<GF16>`, stride 2, alignment 2) with capacity `cap`
at `ptr` holding `p.coefficients`. -/
def polyBuf (A : RustAlloc) (cap ptr : BitVec 64) (p : Poly) : SepProp :=
  vecBuf A gf16Stride gf16Align gf16At cap ptr p.coefficients

/-- A `Poly` at address `v` with pinned capacity `cap` and buffer pointer `ptr` holding
`p.coefficients`: 24-byte `Vec<GF16>` header `(cap, ptr, p.coefficients.length)` at
`(v + 0, v + 8, v + 16)` plus its heap buffer `polyBuf`. -/
def polyAt (A : RustAlloc) (v cap ptr : BitVec 64) (p : Poly) : SepProp :=
  vecAt A gf16Stride gf16Align gf16At v cap ptr p.coefficients

/-- A `Poly` at address `v` with ghost pin `pin : VecPin` holding `p`. -/
def polyPinAt (A : RustAlloc) (pin : VecPin) (p : Poly) (v : BitVec 64) : SepProp :=
  polyAt A v pin.cap pin.ptr p

/-- Some `Poly` at address `v` holding `p` (capacity and buffer pointer existentially quantified). -/
def polyOf (A : RustAlloc) (v : BitVec 64) (p : Poly) : SepProp :=
  vecOf A gf16Stride gf16Align gf16At v p.coefficients

end CryptoVerification.SpqrV1.Poly
