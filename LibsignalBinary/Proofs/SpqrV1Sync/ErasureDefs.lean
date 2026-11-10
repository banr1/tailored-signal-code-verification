/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Mathlib.LinearAlgebra.Lagrange
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Poly
public import LibsignalBinary.Proofs.SpqrV1Sync.GF16Field

set_option warningAsError false

/-!
# Specification Definitions for the SPQR V1 Polynomial Erasure Code

Mathematical specification objects for the 16-lane `GF(2 ^ 16)` polynomial erasure code in
`LibsignalBinary.Specifications.LibsignalSpqrV1.Poly`:

An even-length message `msg` (`L = msg.length`) is split into `L / 2` big-endian `u16` field
elements `msgVal msg i`, striped across 16 polynomials (`j = i % 16`, node index `k = i / 16`).
Polynomial `j` (`msgPoly msg j`) is the degree-`< needed L j` Lagrange interpolant through
`(idxPt k, msgVal msg (16 * k + j))`, where `idxPt k = GF16.new (BitVec.ofNat 16 k)` uses the raw
16-bit pattern of `k` rather than `Nat.cast`. Chunk `idx` carries all 16 evaluations at
`idxPt idx.toNat` packed big-endian into 32 bytes (`chunkData msg idx`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1Sync.Erasure

open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1Sync.GF16Field
open Polynomial
/-- Evaluates a coefficient list as a polynomial `∑ k, C cs[k] * X ^ k` over `GF16`. -/
noncomputable def polyOf (cs : List GF16) : GF16[X] :=
  ∑ k ∈ Finset.range cs.length, C (cs.getD k GF16.ZERO) * X ^ k

/-- Evaluation node `k` of the erasure code: `GF16.new (BitVec.ofNat 16 k)`. -/
def idxPt (k : Nat) : GF16 :=
  GF16.new (BitVec.ofNat 16 k)

/-- The `i`-th big-endian `u16` word of `msg` as an element of `GF16`. -/
def msgVal (msg : List (BitVec 8)) (i : Nat) : GF16 :=
  GF16.new (((msg.getD (2 * i) 0#8).zeroExtend 16 <<< 8) + (msg.getD (2 * i + 1) 0#8).zeroExtend 16)

/-- Number of interpolation points required for lane `j` on an `len`-byte message. -/
def needed (len j : Nat) : Nat :=
  if j < len / 2 % 16 then len / 2 / 16 + 1 else len / 2 / 16

/-- Lane `j` polynomial: Lagrange interpolant through `(idxPt k, msgVal msg (16 * k + j))` for
`k < needed msg.length j`. -/
noncomputable def msgPoly (msg : List (BitVec 8)) (j : Nat) : GF16[X] :=
  Lagrange.interpolate (Finset.range (needed msg.length j)) idxPt (fun k => msgVal msg (16 * k + j))

/-- Evaluation of lane `j` polynomial at chunk index `idx`. -/
noncomputable def chunkVal (msg : List (BitVec 8)) (idx : BitVec 16) (j : Nat) : GF16 :=
  (msgPoly msg j).eval (idxPt idx.toNat)

/-- The 32 big-endian payload bytes of honest chunk `idx`. -/
noncomputable def chunkData (msg : List (BitVec 8)) (idx : BitVec 16) : List.Vector (BitVec 8) 32 :=
  List.Vector.ofFn fun b : Fin 32 =>
    let v := (chunkVal msg idx (b.val / 2)).value
    if b.val % 2 = 0 then (v >>> 8).setWidth 8 else v.setWidth 8

/-- Initial `Points` layout of `PolyEncoder` striped across the 16 lanes. -/
def msgPoints (msg : List (BitVec 8)) : List Point :=
  (List.range 16).map fun j =>
    ⟨(List.range (needed msg.length j)).map fun k => msgVal msg (16 * k + j)⟩

/-- Reachable encoder invariant for `msg`: either the initial `Points` layout or the 16
interpolated polynomials. -/
def EncInv (msg : List (BitVec 8)) (e : PolyEncoder) : Prop :=
  e.s = .points (msgPoints msg) ∨
  ∃ polys : List Poly, e.s = .polys polys ∧ polys.length = 16 ∧
    ∀ j (h : j < polys.length), polys[j].coefficients.length = needed msg.length j ∧
      polyOf polys[j].coefficients = msgPoly msg j

/-- Reachable decoder invariant after adding honest chunks of `msg` with index set `S`: 16
strictly `x`-sorted point sets lying on `msgPoly msg j` at nodes in `S`, each of cardinality at
least `min S.card (needed msg.length j)`. -/
structure DecInv (msg : List (BitVec 8)) (S : Finset Nat) (dec : PolyDecoder) : Prop where
  ptsNeeded : dec.ptsNeeded = msg.length / 2
  notComplete : dec.isComplete = false
  len : dec.pts.length = 16
  sorted : ∀ j (h : j < dec.pts.length),
    (dec.pts[j].vec.map fun pt => pt.x.value.toNat).Pairwise (· < ·)
  onPoly : ∀ j (h : j < dec.pts.length), ∀ pt ∈ dec.pts[j].vec, pt.y = (msgPoly msg j).eval pt.x
  atNode : ∀ j (h : j < dec.pts.length), ∀ pt ∈ dec.pts[j].vec,
    ∃ c ∈ S, c < 2 ^ 16 ∧ pt.x = idxPt c
  enough : ∀ j (h : j < dec.pts.length), min S.card (needed msg.length j) ≤ dec.pts[j].vec.length


/-! ## Decoder point-count equivalence -/

section MoveCompat
theorem necessaryPoints_eq (dec : PolyDecoder) (len : Nat) (h : dec.ptsNeeded = len / 2) (j : Nat) :
    dec.necessaryPoints j = needed len j := by
  simp only [PolyDecoder.necessaryPoints, needed, h]

end MoveCompat

end CryptoVerification.SpqrV1Sync.Erasure
