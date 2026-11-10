/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.GF16
import all Init.Data.List.Control
public import Mathlib.Data.Vector.Basic

/-!
# SPQR V1: polynomial erasure coding (`src/encoding/polynomial.rs`, `src/encoding.rs`)

**Trusted in part.** The theorems of `Computational/Theorems/` use only part of this file (see
`Computational/docs/TRUSTED_BASE.md`): the rest (the `OptionEncoder` / `OptionDecoder` functions,
the `run*Guard` self-tests, `isOkEq` / `isErrEq` / `isOkErrEq`, `PolyConst.wf` and `Pt.eq`) is
checked by Lean.

Models SPQR's 32-byte chunk erasure code (`Chunk`) over $\mathrm{GF}(2^{16})$ with explicit panic
(`PolyPanic`) and error (`PolynomialError`, `EncodingError`) values:
* `Pt` (`cmp`, `eq` comparing `x` only) and `SortedSetPt` (`len`, `replace`, `push`, where pushing
  an existing `x` overwrites the stored `Pt`);
* `Poly` (`zero`, `lagrangeInterpolate`, `fromCompletePoints`, `computeAt`) and fixed-length
  `PolyConst` (`PolyConst.wf`) for precomputed complete-point Lagrange bases;
* `PolyEncoder` (`encodeBytes`, `chunkAt`, `nextChunk`, `intoPb`, `fromPb` via
  `ProtoPolynomialEncoder`) and `PolyDecoder` (`new`, `addChunk`, `decodedMessage`, `intoPb`,
  `fromPb` via `ProtoPolynomialDecoder`);
* kernel-checked guard theorems (`pt_serialize_and_ord_guard`, …, `option_encoder_decoder_guard`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalSpqrV1

/-! ## Panic and Error types -/

/-- Rust panic sites in `src/encoding/polynomial.rs` and `src/encoding.rs`, represented as values. -/
inductive PolyPanic where
  | boundsCheck
  | sliceIndexFail
  | unwrapFailed
  | expectFailed
  | addOverflow
  | subOverflow
  | mulOverflow
  | explicitPanic
  deriving DecidableEq, Repr, Inhabited

namespace PolyPanic

def toSpqrPanic : PolyPanic → SpqrPanic
  | .boundsCheck => .site "src/encoding/polynomial.rs: slice/vec index bounds_check"
  | .sliceIndexFail => .site "src/encoding/polynomial.rs:120,241: slice range slice_index_fail"
  | .unwrapFailed => .site "src/encoding.rs:64,84,94 / src/encoding/polynomial.rs:44–45,51: unwrap_failed"
  | .expectFailed => .site "src/encoding/polynomial.rs:675,969: expect_failed"
  | .addOverflow => .site "src/encoding/polynomial.rs:137,154: usize add_overflow"
  | .subOverflow => .site "src/encoding/polynomial.rs:184,221,224,431: usize sub_overflow"
  | .mulOverflow => .site "src/encoding/polynomial.rs:946: usize mul_overflow"
  | .explicitPanic => .site "src/encoding/polynomial.rs:432: overflow in const mult_xdiff"

end PolyPanic

/-- `PolynomialError` (`src/encoding/polynomial.rs:16–24`). -/
inductive PolynomialError where
  | messageLengthEven
  | messageLengthTooLong
  | serializationInvalid
  deriving DecidableEq, Repr, Inhabited

/-- `EncodingError` (`src/encoding.rs:8–22`). -/
inductive EncodingError where
  | polynomialError (e : PolynomialError)
  | chunkIndexDecodingError
  | chunkDataDecodingError
  deriving DecidableEq, Repr, Inhabited

namespace EncodingError

end EncodingError

/-! ## Constants and `Chunk` (`src/encoding.rs:24–28`, `src/encoding/polynomial.rs:73–79, 530–532`) -/

def CHUNK_SIZE : Nat := 32

/-- Number of $\mathrm{GF}(2^{16})$ polynomials or point sets per message (`CHUNK_SIZE / 2 = 16`). -/
def NUM_POLYS : Nat := CHUNK_SIZE / 2

def USIZE_MAX : Nat := (1 <<< 64) - 1

/-- 32-byte erasure-coded chunk (`src/encoding.rs:24–28`) with 16-bit chunk `index`. -/
structure Chunk where
  index : BitVec 16
  data : List.Vector (BitVec 8) 32
  deriving DecidableEq

instance : Inhabited Chunk where
  default := { index := 0#16, data := List.Vector.replicate 32 0#8 }

/-! ## Big-endian `u16` byte conversion helpers -/

def u16ToBeBytes (v : BitVec 16) : List (BitVec 8) :=
  [(v >>> 8).setWidth 8, v.setWidth 8]

def u16FromBeBytes (b0 b1 : BitVec 8) : BitVec 16 :=
  (b0.zeroExtend 16 <<< 8) ||| b1.zeroExtend 16

/-! ## `Pt` (`src/encoding/polynomial.rs:26–68`) -/

/-- Point `(x, y)` in $\mathrm{GF}(2^{16}) \times \mathrm{GF}(2^{16})$ (`src/encoding/polynomial.rs:30–33`).
Derived `DecidableEq` checks both coordinates, while Rust's `Ord` and `PartialEq` compare only `x`
(`Pt.cmp`, `Pt.eq`). -/
structure Pt where
  x : GF16
  y : GF16
  deriving DecidableEq, Repr, Inhabited

namespace Pt

/-- 4-byte big-endian encoding `[x_hi, x_lo, y_hi, y_lo]` (`Pt::serialize`). -/
def serialize (self : Pt) : List (BitVec 8) :=
  u16ToBeBytes self.x.value ++ u16ToBeBytes self.y.value

/-- `Pt::deserialize` (`src/encoding/polynomial.rs:42–47`); panics with `.unwrapFailed` unless
`s.length = 4`. -/
def deserialize (s : List (BitVec 8)) : Except PolyPanic Pt :=
  match s with
  | [b0, b1, b2, b3] =>
    .ok { x := GF16.new (u16FromBeBytes b0 b1), y := GF16.new (u16FromBeBytes b2 b3) }
  | _ => .error .unwrapFailed

/-- `<Pt as Ord>::cmp` (`src/encoding/polynomial.rs:50–54`), comparing `x` only. -/
def cmp (self other : Pt) : Ordering :=
  Ord.compare self.x.value.toNat other.x.value.toNat

/-- `<Pt as PartialEq>::eq` (`src/encoding/polynomial.rs:64–68`), comparing `x` only. -/
def eq (self other : Pt) : Bool :=
  self.x.value == other.x.value

end Pt

/-! ## `sorted_vec::SortedSet<Pt>` (`sorted-vec-0.8.11/src/lib.rs:38–44, 366–438`) -/

/-- Forward sorted set of `Pt` ordered and deduplicated by `x` (`sorted_vec::SortedSet<Pt>`). -/
structure SortedSetPt where
  vec : List Pt
  deriving DecidableEq, Repr, Inhabited

namespace SortedSetPt

def new : SortedSetPt :=
  { vec := [] }

def withCapacity (_capacity : Nat) : SortedSetPt :=
  { vec := [] }

def len (self : SortedSetPt) : Nat :=
  self.vec.length

def asSlice (self : SortedSetPt) : List Pt :=
  self.vec

def binarySearchAux (target : Pt) : Nat → List Pt → Except Nat Nat
  | idx, [] => .error idx
  | idx, pt :: rest =>
    match Pt.cmp pt target with
    | .lt => binarySearchAux target (idx + 1) rest
    | .eq => .ok idx
    | .gt => .error idx

/-- `slice::binary_search` on `SortedSet<Pt>` by `Pt.cmp`, returning `.ok idx` on an `x`-match or
`.error insertIdx` at the insertion position. -/
def binarySearch (self : SortedSetPt) (target : Pt) : Except Nat Nat :=
  binarySearchAux target 0 self.vec

/-- `SortedSet::replace` (`sorted-vec-0.8.11/src/lib.rs:386–402`): overwrites an existing point with
matching `x` and returns `some old`, or inserts in `x`-order and returns `none`. -/
def replace (self : SortedSetPt) (element : Pt) : SortedSetPt × Nat × Option Pt :=
  match self.binarySearch element with
  | .ok existingIndex =>
    let old := self.vec[existingIndex]?
    ({ vec := self.vec.set existingIndex element }, existingIndex, old)
  | .error insertIndex =>
    let vec' := self.vec.take insertIndex ++ (element :: self.vec.drop insertIndex)
    ({ vec := vec' }, insertIndex, none)

/-- `SortedSet::push` (`sorted-vec-0.8.11/src/lib.rs:413–438`): appends at the back when
`element.x > last.x`, replaces `last` when `element.x == last.x`, and delegates to `replace` when
`element.x < last.x`. -/
def push (self : SortedSetPt) (element : Pt) : SortedSetPt × Nat × Option Pt :=
  match self.vec.getLast? with
  | some last =>
    match Pt.cmp element last with
    | .gt =>
      let newVec := self.vec ++ [element]
      ({ vec := newVec }, newVec.length - 1, none)
    | .eq =>
      let newVec := self.vec.dropLast ++ [element]
      ({ vec := newVec }, newVec.length - 1, some last)
    | .lt =>
      self.replace element
  | none =>
    ({ vec := [element] }, 0, none)

end SortedSetPt

/-! ## `Poly` (`src/encoding/polynomial.rs:83–367`) -/

/-- Polynomial over $\mathrm{GF}(2^{16})$ with coefficients in ascending degree order
(`coefficients[k]` is the coefficient of $x^k$). -/
structure Poly where
  coefficients : List GF16
  deriving DecidableEq, Repr, Inhabited

namespace Poly

def zero (_capacity : Nat := 0) : Poly :=
  { coefficients := [] }

def multXdiffAssignTrailingLoop (difference : GF16) : Nat → Nat → List GF16 → Except PolyPanic (List GF16)
  | _, 0, coeffs => .ok coeffs
  | i, rem + 1, coeffs =>
    if i == 0 then
      .error .subOverflow
    else
      match coeffs[i]?, coeffs[i - 1]? with
      | some ci, some ciPrev =>
        let delta := GF16.mul ci difference
        let coeffs' := coeffs.set (i - 1) (GF16.sub ciPrev delta)
        multXdiffAssignTrailingLoop difference (i + 1) rem coeffs'
      | _, _ => .error .boundsCheck

/-- `Poly::mult_xdiff_assign_trailing` (`src/encoding/polynomial.rs:179–186`): multiplies
`self[start..]` by $(x - \mathrm{difference})$, propagating carry into `self[start - 1]`
(`.subOverflow` if `start == 0` and `self.coefficients` is non-empty). -/
def multXdiffAssignTrailing (self : Poly) (start : Nat) (difference : GF16) : Except PolyPanic Poly := do
  let l := self.coefficients.length
  if start >= l then
    return self
  else
    let coeffs' ← multXdiffAssignTrailingLoop difference start (l - start) self.coefficients
    return { coefficients := coeffs' }

def lagrangeInterpolatePrepareLoop (pts : List Pt) (offset : Nat) : Nat → Nat → Poly → Except PolyPanic Poly
  | _, 0, p => .ok p
  | i, rem + 1, p => do
    let some pi := pts[i]? | .error .boundsCheck
    if i > offset then
      .error .subOverflow
    else
      let p' ← p.multXdiffAssignTrailing (offset - i) pi.x
      lagrangeInterpolatePrepareLoop pts offset (i + 1) rem p'

/-- `Poly::lagrange_interpolate_prepare` (`src/encoding/polynomial.rs:148–168`): computes
$\prod_i (x - \mathrm{pts}[i].x)$ of degree `pts.length`. -/
def lagrangeInterpolatePrepare (pts : List Pt) : Except PolyPanic Poly := do
  let offset := pts.length
  if offset + 1 > USIZE_MAX then
    .error .addOverflow
  else
    let p0 : Poly := { coefficients := List.replicate offset GF16.ZERO ++ [GF16.ONE] }
    lagrangeInterpolatePrepareLoop pts offset 0 offset p0

def lagrangeDenominator (pix : GF16) (pts : List Pt) : GF16 :=
  pts.foldl (fun denominator pj =>
    if pix == pj.x then
      denominator
    else
      GF16.mul denominator (GF16.sub pix pj.x)) GF16.ONE

def lagrangeCompleteDivLoop (pix scale : GF16) (len : Nat) : Nat → Nat → List GF16 → Except PolyPanic (List GF16)
  | _, 0, coeffs => .ok coeffs
  | j, rem + 1, coeffs =>
    if j > len then
      .error .subOverflow
    else
      let idx := len - j
      if idx == 0 then
        .error .subOverflow
      else
        match coeffs[idx]?, coeffs[idx - 1]? with
        | some cIdx, some cPrev =>
          let negativeDelta := GF16.mul cIdx pix
          let coeffs1 := coeffs.set idx (GF16.mul cIdx scale)
          let coeffs2 := coeffs1.set (idx - 1) (GF16.add cPrev negativeDelta)
          lagrangeCompleteDivLoop pix scale len (j + 1) rem coeffs2
        | _, _ => .error .boundsCheck

/-- `Poly::lagrange_interpolate_complete` (`src/encoding/polynomial.rs:202–228`): divides
$(x - \mathrm{pts}[i].x)$ out of `self` into upper coefficients `[1..]` and scales by
$\mathrm{pts}[i].y / \prod_{p_j.x \ne \mathrm{pts}[i].x} (\mathrm{pts}[i].x - p_j.x)$. -/
def lagrangeInterpolateComplete (self : Poly) (pts : List Pt) (i : Nat) : Except PolyPanic Poly := do
  let some pi := pts[i]? | .error .boundsCheck
  let denominator := lagrangeDenominator pi.x pts
  let scale := GF16.div pi.y denominator
  let len := self.coefficients.length
  if len <= 1 then
    return self
  else
    let coeffs' ← lagrangeCompleteDivLoop pi.x scale len 1 (len - 1) self.coefficients
    return { coefficients := coeffs' }

def lagrangeAccumulateCoeffs : Nat → Nat → List GF16 → List GF16 → Except PolyPanic (List GF16)
  | _, 0, outCoeffs, _ => .ok outCoeffs
  | j, rem + 1, outCoeffs, workingCoeffs =>
    if j + 1 > USIZE_MAX then
      .error .addOverflow
    else
      match outCoeffs[j]?, workingCoeffs[j + 1]? with
      | some o, some w =>
        lagrangeAccumulateCoeffs (j + 1) rem (outCoeffs.set j (GF16.add o w)) workingCoeffs
      | _, _ => .error .boundsCheck

def lagrangeInterpolateLoop (template : Poly) (pts : List Pt) :
    Nat → Nat → List GF16 → Except PolyPanic (List GF16)
  | _, 0, outCoeffs => .ok outCoeffs
  | i, rem + 1, outCoeffs => do
    let working ← template.lagrangeInterpolateComplete pts i
    let outCoeffs' ← lagrangeAccumulateCoeffs 0 outCoeffs.length outCoeffs working.coefficients
    lagrangeInterpolateLoop template pts (i + 1) rem outCoeffs'

/-- `Poly::lagrange_interpolate` (`src/encoding/polynomial.rs:110–141`): returns the Lagrange
interpolating polynomial of degree `< pts.length`. -/
def lagrangeInterpolate (pts : List Pt) : Except PolyPanic Poly := do
  if pts.isEmpty then
    return Poly.zero pts.length
  else
    let template ← Poly.lagrangeInterpolatePrepare pts
    let working0 ← template.lagrangeInterpolateComplete pts 0
    match working0.coefficients with
    | [] => .error .sliceIndexFail
    | _ :: rest0 =>
      let outCoeffs ← lagrangeInterpolateLoop template pts 1 (pts.length - 1) rest0
      return { coefficients := outCoeffs }

/-- `Poly::lagrange_interpolate_pt` (`src/encoding/polynomial.rs:236–242`): Lagrange basis
polynomial for `pts[i]`. -/
def lagrangeInterpolatePt (pts : List Pt) (i : Nat) : Except PolyPanic Poly := do
  let result ← Poly.lagrangeInterpolatePrepare pts
  let result ← result.lagrangeInterpolateComplete pts i
  match result.coefficients with
  | [] => .error .sliceIndexFail
  | _ :: rest => return { coefficients := rest }

def addAssignCoeffs : List GF16 → List GF16 → List GF16
  | selfCoeffs, [] => selfCoeffs
  | [], otherCoeffs => otherCoeffs
  | c :: cs, o :: os => GF16.add c o :: addAssignCoeffs cs os

def addAssign (self other : Poly) : Poly :=
  { coefficients := addAssignCoeffs self.coefficients other.coefficients }

def multAssign (self : Poly) (m : GF16) : Poly :=
  { coefficients := parallelMult m self.coefficients }

def computeAtPowersLoop : Nat → Nat → List GF16 → Except PolyPanic (List GF16)
  | _, 0, xs => .ok xs
  | i, rem + 1, xs =>
    match xs[i / 2]?, xs[(i / 2) + (i % 2)]? with
    | some a, some b =>
      computeAtPowersLoop (i + 1) rem (xs ++ [GF16.mul a b])
    | _, _ => .error .boundsCheck

/-- `Poly::compute_at` (`src/encoding/polynomial.rs:261–278`): evaluates `self` at `x`. -/
def computeAt (self : Poly) (x : GF16) : Except PolyPanic GF16 := do
  let len := self.coefficients.length
  let xs0 : List GF16 := [GF16.ONE, x]
  let xs ← if len <= 2 then .ok xs0 else computeAtPowersLoop 2 (len - 2) xs0
  let pairs := self.coefficients.zip xs
  return pairs.foldl (fun out (a, b) => GF16.add out (GF16.mul a b)) GF16.ZERO

/-- `Poly::lagrange_sum` (`src/encoding/polynomial.rs:282–290`): $\sum_i \mathrm{polys}[i] \cdot \mathrm{pts}[i].y$. -/
def lagrangeSum (pts : List Pt) (polys : List Poly) : Poly :=
  (pts.zip polys).foldl (fun out (pt, poly) =>
    let p := poly.multAssign pt.y
    out.addAssign p) (Poly.zero pts.length)

end Poly

/-! ## `PolyConst<N>` and precomputed complete-point Lagrange bases (`src/encoding/polynomial.rs:370–527`) -/

/-- Fixed-length polynomial of `n` coefficients (`PolyConst<N>`, `src/encoding/polynomial.rs:370–372`). -/
structure PolyConst (n : Nat) where
  coefficients : List GF16
  deriving DecidableEq, Repr, Inhabited

namespace PolyConst

def wf {n : Nat} (self : PolyConst n) : Prop :=
  self.coefficients.length = n

def mult {n : Nat} (self : PolyConst n) (m : GF16) : PolyConst n :=
  { coefficients := self.coefficients.map (fun c => GF16.constMul c m) }

/-- `PolyConst::<N>::mult_xdiff` (`src/encoding/polynomial.rs:428–467`): multiplies `self` by
$(x - \mathrm{difference})$ within `n` coefficients; panics on `n == 0` (`.subOverflow`) or
non-zero top coefficient (`.explicitPanic`). -/
def multXdiff {n : Nat} (self : PolyConst n) (difference : GF16) : Except PolyPanic (PolyConst n) := do
  if n == 0 then
    .error .subOverflow
  else
    let some top := self.coefficients[n - 1]? | .error .boundsCheck
    if top != GF16.ZERO then
      .error .explicitPanic
    else
      let xp : List GF16 := GF16.ZERO :: self.coefficients.take (n - 1)
      let dp : List GF16 := self.coefficients.map (fun c => GF16.constMul c difference)
      let out : List GF16 := (xp.zip dp).map (fun (a, b) => GF16.constSub a b)
      return { coefficients := out }

def lagrangeInterpolatePtLoop (n : Nat) (pts : List Pt) (pix : GF16) :
    Nat → Nat → PolyConst n → GF16 → Except PolyPanic (PolyConst n × GF16)
  | _, 0, p, denominator => .ok (p, denominator)
  | j, rem + 1, p, denominator => do
    let some pj := pts[j]? | .error .boundsCheck
    if pix == pj.x then
      lagrangeInterpolatePtLoop n pts pix (j + 1) rem p denominator
    else
      let p' ← p.multXdiff pj.x
      let denominator' := GF16.constMul denominator (GF16.constSub pix pj.x)
      lagrangeInterpolatePtLoop n pts pix (j + 1) rem p' denominator'

/-- `PolyConst::<N>::lagrange_interpolate_pt` (`src/encoding/polynomial.rs:383–408`). -/
def lagrangeInterpolatePt (n : Nat) (pts : List Pt) (i : Nat) : Except PolyPanic (PolyConst n) := do
  let some pi := pts[i]? | .error .boundsCheck
  if n == 0 then
    .error .boundsCheck
  else
    let p0 : PolyConst n := { coefficients := GF16.ONE :: List.replicate (n - 1) GF16.ZERO }
    let (p, denominator) ← lagrangeInterpolatePtLoop n pts pi.x 0 n p0 GF16.ONE
    return p.mult (GF16.constDiv pi.y denominator)

def toPoly {n : Nat} (self : PolyConst n) : Poly :=
  { coefficients := self.coefficients }

end PolyConst

def constPolysToPolys {n : Nat} (cps : List (PolyConst n)) : List Poly :=
  cps.map PolyConst.toPoly

/-- Precomputes the `n` Lagrange basis polynomials for $x = 0, \dots, n - 1$ (`src/encoding/polynomial.rs:491–518`). -/
def lagrangePolysForCompletePoints (n : Nat) : Except PolyPanic (List (PolyConst n)) := do
  let ones : List Pt := (List.range n).map (fun i => { x := GF16.new (BitVec.ofNat 16 i), y := GF16.ONE })
  (List.range n).mapM (fun i => PolyConst.lagrangeInterpolatePt n ones i)

def COMPLETE_POINTS_POLYS_1 : Except PolyPanic (List (PolyConst 1)) :=
  lagrangePolysForCompletePoints 1

def COMPLETE_POINTS_POLYS_3 : Except PolyPanic (List (PolyConst 3)) :=
  lagrangePolysForCompletePoints 3

def COMPLETE_POINTS_POLYS_5 : Except PolyPanic (List (PolyConst 5)) :=
  lagrangePolysForCompletePoints 5

def COMPLETE_POINTS_POLYS_30 : Except PolyPanic (List (PolyConst 30)) :=
  lagrangePolysForCompletePoints 30

def COMPLETE_POINTS_POLYS_34 : Except PolyPanic (List (PolyConst 34)) :=
  lagrangePolysForCompletePoints 34

def COMPLETE_POINTS_POLYS_36 : Except PolyPanic (List (PolyConst 36)) :=
  lagrangePolysForCompletePoints 36

namespace Poly

def checkCompletePoints : Nat → List Pt → Bool
  | _, [] => true
  | i, pt :: rest =>
    if pt.x != GF16.new (BitVec.ofNat 16 i) then
      false
    else
      checkCompletePoints (i + 1) rest

/-- `Poly::from_complete_points` (`src/encoding/polynomial.rs:297–330`): interpolates `pts` when
`pts[i].x == i`, using `COMPLETE_POINTS_POLYS_{1,3,5,30,34,36}` for matching lengths and
`Poly.lagrangeInterpolatePt` otherwise. -/
def fromCompletePoints (pts : List Pt) : Except PolyPanic (Except Unit Poly) := do
  if !checkCompletePoints 0 pts then
    return .error ()
  else
    let n := pts.length
    let polys : List Poly ←
      if n == 0 then
        pure []
      else if n == 1 then do
        let cps ← COMPLETE_POINTS_POLYS_1
        pure (constPolysToPolys cps)
      else if n == 3 then do
        let cps ← COMPLETE_POINTS_POLYS_3
        pure (constPolysToPolys cps)
      else if n == 5 then do
        let cps ← COMPLETE_POINTS_POLYS_5
        pure (constPolysToPolys cps)
      else if n == 30 then do
        let cps ← COMPLETE_POINTS_POLYS_30
        pure (constPolysToPolys cps)
      else if n == 34 then do
        let cps ← COMPLETE_POINTS_POLYS_34
        pure (constPolysToPolys cps)
      else if n == 36 then do
        let cps ← COMPLETE_POINTS_POLYS_36
        pure (constPolysToPolys cps)
      else do
        let ones : List Pt := pts.map (fun pt => { x := pt.x, y := GF16.ONE })
        (List.range n).mapM (fun i => Poly.lagrangeInterpolatePt ones i)
    return .ok (Poly.lagrangeSum pts polys)

/-- `Poly::serialize` (`src/encoding/polynomial.rs:332–344`): big-endian 2-byte coefficients. -/
def serialize (self : Poly) : List (BitVec 8) :=
  self.coefficients.flatMap (fun c => u16ToBeBytes c.value)

def bytesToGF16List : List (BitVec 8) → Except PolyPanic (List GF16)
  | [] => .ok []
  | [ _ ] => .error .boundsCheck
  | b0 :: b1 :: rest => do
    let tail ← bytesToGF16List rest
    return GF16.new (u16FromBeBytes b0 b1) :: tail

/-- `Poly::deserialize` (`src/encoding/polynomial.rs:346–366`): rejects empty or odd-length inputs
with `.serializationInvalid`, otherwise decodes big-endian `GF16` coefficients. -/
def deserialize (serialized : List (BitVec 8)) : Except PolyPanic (Except PolynomialError Poly) := do
  if serialized.isEmpty || serialized.length % 2 == 1 then
    return .error .serializationInvalid
  else
    let coefficients ← bytesToGF16List serialized
    return .ok { coefficients }

end Poly

/-! ## `Point`, `EncoderState`, `ProtoPolynomialEncoder`, and `PolyEncoder` (`src/encoding/polynomial.rs:536–763`) -/

/-- Buffered `GF16` points for one of the 16 encoder polynomials (`src/encoding/polynomial.rs:536–539`). -/
structure Point where
  value : List GF16
  deriving DecidableEq, Repr, Inhabited

/-- Encoder state (`src/encoding/polynomial.rs:542–548`): 16 `Point` buffers or 16 interpolated `Poly`s. -/
inductive EncoderState where
  | points (pts : List Point)
  | polys (polys : List Poly)
  deriving DecidableEq, Repr, Inhabited

/-- `pqrpb::PolynomialEncoder` (`src/proto/pq_ratchet.proto:8–16`). -/
structure ProtoPolynomialEncoder where
  idx : BitVec 32
  pts : List (List (BitVec 8))
  polys : List (List (BitVec 8))
  deriving DecidableEq, Repr, Inhabited

/-- Erasure-code encoder (`src/encoding/polynomial.rs:551–554`): next chunk index `idx` and
`EncoderState`. -/
structure PolyEncoder where
  idx : BitVec 32
  s : EncoderState
  deriving DecidableEq, Repr, Inhabited

namespace PolyEncoder

/-- `PolyEncoder::into_pb` (`src/encoding/polynomial.rs:563–596`). -/
def intoPb (self : PolyEncoder) : ProtoPolynomialEncoder :=
  match self.s with
  | .points points =>
    { idx := self.idx
      pts := points.map (fun pt => pt.value.flatMap (fun g => u16ToBeBytes g.value))
      polys := [] }
  | .polys polys =>
    { idx := self.idx
      pts := []
      polys := polys.map Poly.serialize }

def decodePbPoints : List (List (BitVec 8)) → Except PolyPanic (Except PolynomialError (List Point))
  | [] => .ok (.ok [])
  | pts :: rest => do
    if pts.length % 2 != 0 then
      return .error .serializationInvalid
    else
      let v ← Poly.bytesToGF16List pts
      let tailRes ← decodePbPoints rest
      match tailRes with
      | .error e => return .error e
      | .ok tail => return .ok ({ value := v } :: tail)

def decodePbPolys : List (List (BitVec 8)) → Except PolyPanic (Except PolynomialError (List Poly))
  | [] => .ok (.ok [])
  | polyBytes :: rest => do
    let pRes ← Poly.deserialize polyBytes
    match pRes with
    | .error e => return .error e
    | .ok p =>
      let tailRes ← decodePbPolys rest
      match tailRes with
      | .error e => return .error e
      | .ok tail => return .ok (p :: tail)

/-- `PolyEncoder::from_pb` (`src/encoding/polynomial.rs:598–641`): decodes an encoder from its
protobuf form; requires exactly one of `pts` or `polys` to have `NUM_POLYS` (`16`) entries. -/
def fromPb (pb : ProtoPolynomialEncoder) : Except PolyPanic (Except PolynomialError PolyEncoder) := do
  if !pb.pts.isEmpty then
    if !pb.polys.isEmpty then
      return .error .serializationInvalid
    else if pb.pts.length != NUM_POLYS then
      return .error .serializationInvalid
    else
      let ptsRes ← decodePbPoints pb.pts
      match ptsRes with
      | .error e => return .error e
      | .ok out => return .ok { idx := pb.idx, s := .points out }
  else if pb.polys.length == NUM_POLYS then
    let polysRes ← decodePbPolys pb.polys
    match polysRes with
    | .error e => return .error e
    | .ok out => return .ok { idx := pb.idx, s := .polys out }
  else
    return .error .serializationInvalid

def enumeratePts : Nat → List GF16 → List Pt
  | _, [] => []
  | x, y :: rest => { x := GF16.new (BitVec.ofNat 16 x), y := y } :: enumeratePts (x + 1) rest

def pointsToPolysLoop (pts : List Point) : Nat → Nat → List Poly → Except PolyPanic (List Poly)
  | _, 0, acc => .ok acc
  | i, rem + 1, acc => do
    let some ptList := pts[i]? | .error .boundsCheck
    let ptVec : List Pt := enumeratePts 0 ptList.value
    let res ← Poly.fromCompletePoints ptVec
    match res with
    | .error () => .error .expectFailed
    | .ok p => pointsToPolysLoop pts (i + 1) rem (acc ++ [p])

/-- `PolyEncoder::point_at` (`src/encoding/polynomial.rs:645–688`): reads `pts[poly].value[idx]`
directly when in `.points` and in bounds; otherwise interpolates all 16 polynomials into `.polys`
and evaluates `polys[poly]` at `idx`. -/
def pointAt (self : PolyEncoder) (poly : Nat) (idx : Nat) : Except PolyPanic (PolyEncoder × GF16) := do
  let self ←
    match self.s with
    | .points pts => do
      let some pt := pts[poly]? | .error .boundsCheck
      match pt.value[idx]? with
      | some val => return (self, val)
      | none =>
        let polys ← pointsToPolysLoop pts 0 NUM_POLYS []
        pure { self with s := .polys polys }
    | .polys _ => pure self
  match self.s with
  | .polys polys =>
    let some p := polys[poly]? | .error .boundsCheck
    let val ← p.computeAt (GF16.new (BitVec.ofNat 16 idx))
    return (self, val)
  | .points _ =>
    .error .explicitPanic

def distributeMsgChunks : Nat → List (BitVec 8) → List Point → Except PolyPanic (List Point)
  | _, [], pts => .ok pts
  | _, [ _ ], _ => .error .boundsCheck
  | i, c0 :: c1 :: rest, pts => do
    let poly := i % pts.length
    let some pt := pts[poly]? | .error .boundsCheck
    let gf := GF16.new ((c0.zeroExtend 16 <<< 8) + c1.zeroExtend 16)
    let pts' := pts.set poly { value := pt.value ++ [gf] }
    distributeMsgChunks (i + 1) rest pts'

/-- `PolyEncoder::encode_bytes_base` (`src/encoding/polynomial.rs:691–712`): rejects odd-length or
overlong (`> 2^16 * 16` bytes) messages and distributes big-endian `GF16` pairs across 16 `Point`
buffers. -/
def encodeBytesBase (msg : List (BitVec 8)) : Except PolyPanic (Except EncodingError PolyEncoder) := do
  if msg.length % 2 != 0 then
    return .error (.polynomialError .messageLengthEven)
  else if msg.length > (1 <<< 16) * NUM_POLYS then
    return .error (.polynomialError .messageLengthTooLong)
  else
    let initPts : List Point := List.replicate NUM_POLYS { value := [] }
    let pts ← distributeMsgChunks 0 msg initPts
    return .ok { idx := 0#32, s := .points pts }

/-- `<PolyEncoder as Encoder>::encode_bytes` (`src/encoding/polynomial.rs:754–756`). -/
def encodeBytes (msg : List (BitVec 8)) : Except PolyPanic (Except EncodingError PolyEncoder) :=
  encodeBytesBase msg

def chunkAtLoop (idx : BitVec 16) :
    (i : Nat) → (rem : Nat) → PolyEncoder →
      Except PolyPanic (PolyEncoder × List.Vector (BitVec 8) (2 * rem))
  | _, 0, self => .ok (self, List.Vector.nil)
  | i, rem + 1, self => do
    let totalIdx := idx.toNat * 16 + i
    let poly := totalIdx % 16
    let polyIdx := totalIdx / 16
    let (self', p) ← self.pointAt poly polyIdx
    let (self'', tail) ← chunkAtLoop idx (i + 1) rem self'
    let b0 : BitVec 8 := (p.value >>> 8).setWidth 8
    let b1 : BitVec 8 := p.value.setWidth 8
    return (self'', b0 ::ᵥ b1 ::ᵥ tail)

/-- `PolyEncoder::chunk_at` (`src/encoding/polynomial.rs:715–734`): emits the 32-byte chunk at
16-bit `idx` (one `GF16` value per polynomial). -/
def chunkAt (self : PolyEncoder) (idx : BitVec 16) : Except PolyPanic (PolyEncoder × Chunk) := do
  let (self', data) ← chunkAtLoop idx 0 16 self
  return (self', { index := idx, data := data })

/-- `<PolyEncoder as Encoder>::next_chunk` (`src/encoding/polynomial.rs:758–762`): emits
`chunkAt (self.idx as u16)` and increments `self.idx` wrapping modulo $2^{32}$. -/
def nextChunk (self : PolyEncoder) : Except PolyPanic (PolyEncoder × Chunk) := do
  let (self', out) ← self.chunkAt (self.idx.setWidth 16)
  return ({ self' with idx := self'.idx + 1#32 }, out)

end PolyEncoder

/-! ## `ProtoPolynomialDecoder` and `PolyDecoder` (`src/encoding/polynomial.rs:766–977`) -/

/-- `pqrpb::PolynomialDecoder` (`src/proto/pq_ratchet.proto:18–23`). -/
structure ProtoPolynomialDecoder where
  ptsNeeded : BitVec 32
  polys : BitVec 32
  pts : List (List (BitVec 8))
  isComplete : Bool
  deriving DecidableEq, Repr, Inhabited

/-- Erasure-code decoder (`src/encoding/polynomial.rs:766–785`): target 2-byte point count
`ptsNeeded`, 16 `SortedSetPt` sets `pts`, and `isComplete` flag. -/
structure PolyDecoder where
  ptsNeeded : Nat
  pts : List SortedSetPt
  isComplete : Bool
  deriving DecidableEq, Repr, Inhabited

namespace PolyDecoder

/-- `PolyDecoder::necessary_points` (`src/encoding/polynomial.rs:795–803`). -/
def necessaryPoints (self : PolyDecoder) (poly : Nat) : Nat :=
  let pointsPerPoly := self.ptsNeeded / 16
  let pointsRemaining := self.ptsNeeded % 16
  if poly < pointsRemaining then
    pointsPerPoly + 1
  else
    pointsPerPoly

/-- `PolyDecoder::new_with_poly_count` (`src/encoding/polynomial.rs:806–815`); rejects odd
`lenBytes` with `.messageLengthEven`. -/
def newWithPolyCount (lenBytes : Nat) (_polys : Nat) :
    Except PolyPanic (Except EncodingError PolyDecoder) := do
  if lenBytes % 2 != 0 then
    return .error (.polynomialError .messageLengthEven)
  else
    return .ok
      { ptsNeeded := lenBytes / 2
        pts := List.replicate 16 SortedSetPt.new
        isComplete := false }

/-- `<PolyDecoder as Decoder>::new` (`src/encoding/polynomial.rs:886–888`). -/
def new (lenBytes : Nat) : Except PolyPanic (Except EncodingError PolyDecoder) :=
  newWithPolyCount lenBytes 16

/-- `PolyDecoder::into_pb` (`src/encoding/polynomial.rs:817–838`). -/
def intoPb (self : PolyDecoder) : ProtoPolynomialDecoder :=
  { ptsNeeded := BitVec.ofNat 32 self.ptsNeeded
    polys := 16#32
    isComplete := self.isComplete
    pts := self.pts.map (fun s => s.vec.flatMap Pt.serialize) }

def pushChunksExact4 : List (BitVec 8) → SortedSetPt → Except PolyPanic SortedSetPt
  | [], v => .ok v
  | b0 :: b1 :: b2 :: b3 :: rest, v => do
    let pt ← Pt.deserialize [b0, b1, b2, b3]
    let (v', _, _) := v.push pt
    pushChunksExact4 rest v'
  | _, _ => .error .unwrapFailed

def decodeDecoderPbPts : List (List (BitVec 8)) →
    Except PolyPanic (Except PolynomialError (List SortedSetPt))
  | [] => .ok (.ok [])
  | pts :: rest => do
    if pts.length % 4 != 0 then
      return .error .serializationInvalid
    else
      let v ← pushChunksExact4 pts (SortedSetPt.withCapacity (pts.length / 4))
      let tailRes ← decodeDecoderPbPts rest
      match tailRes with
      | .error e => return .error e
      | .ok tail => return .ok (v :: tail)

/-- `PolyDecoder::from_pb` (`src/encoding/polynomial.rs:842–866`): requires 16 point sets whose byte
lengths are multiples of 4. -/
def fromPb (pb : ProtoPolynomialDecoder) : Except PolyPanic (Except PolynomialError PolyDecoder) := do
  if pb.pts.length != 16 then
    return .error .serializationInvalid
  else
    let ptsRes ← decodeDecoderPbPts pb.pts
    match ptsRes with
    | .error e => return .error e
    | .ok outPts =>
      return .ok
        { ptsNeeded := pb.ptsNeeded.toNat
          isComplete := pb.isComplete
          pts := outPts }

def addChunkLoop (chunk : Chunk) :
    Nat → Nat → PolyDecoder → Except PolyPanic PolyDecoder
  | _, 0, self => .ok self
  | i, rem + 1, self => do
    let totalIdx := chunk.index.toNat * 16 + i
    let poly := totalIdx % 16
    let polyIdx := totalIdx / 16
    let x := GF16.new (BitVec.ofNat 16 polyIdx)
    let y1 := chunk.data.get ⟨(i * 2) % 32, Nat.mod_lt _ (by decide)⟩
    let y2 := chunk.data.get ⟨(i * 2 + 1) % 32, Nat.mod_lt _ (by decide)⟩
    let y := GF16.new ((y1.zeroExtend 16 <<< 8) + y2.zeroExtend 16)
    let some polyPts := self.pts[poly]? | .error .boundsCheck
    let nec := self.necessaryPoints i
    let self' :=
      if polyIdx < nec || polyPts.len < nec then
        let (polyPts', _, _) := polyPts.push { x := x, y := y }
        { self with pts := self.pts.set poly polyPts' }
      else
        self
    addChunkLoop chunk (i + 1) rem self'

/-- `<PolyDecoder as Decoder>::add_chunk` (`src/encoding/polynomial.rs:891–916`). -/
def addChunk (self : PolyDecoder) (chunk : Chunk) : Except PolyPanic PolyDecoder :=
  addChunkLoop chunk 0 16 self

def collectPointsVecs (self : PolyDecoder) :
    Nat → Nat → Bool → List (List Pt) → Except PolyPanic (Bool × List (List Pt))
  | _, 0, retNone, pointsVecs => .ok (retNone, pointsVecs)
  | i, rem + 1, retNone, pointsVecs => do
    let some pts := self.pts[i]? | .error .boundsCheck
    let nec := self.necessaryPoints i
    if pts.len < nec then
      collectPointsVecs self (i + 1) rem true pointsVecs
    else
      collectPointsVecs self (i + 1) rem retNone (pointsVecs ++ [pts.asSlice.take nec])

def decodedMessageLoop (self : PolyDecoder) (pointsVecs : List (List Pt)) :
    Nat → Nat → List (Option Poly) → List (BitVec 8) →
      Except PolyPanic (List (Option Poly) × List (BitVec 8))
  | _, 0, polys, out => .ok (polys, out)
  | i, rem + 1, polys, out => do
    let poly := i % 16
    let polyIdx := i / 16
    let pt : Pt := { x := GF16.new (BitVec.ofNat 16 polyIdx), y := GF16.ZERO }
    let some polyPts := self.pts[poly]? | .error .boundsCheck
    let (polys', y) ←
      match polyPts.binarySearch pt with
      | .ok idx =>
        let some foundPt := polyPts.vec[idx]? | .error .boundsCheck
        pure (polys, foundPt.y)
      | .error _ =>
        let some optPoly := polys[poly]? | .error .boundsCheck
        let polys1 ←
          match optPoly with
          | some _ => pure polys
          | none =>
            let some ptsSlice := pointsVecs[poly]? | .error .boundsCheck
            let interp ← Poly.lagrangeInterpolate ptsSlice
            pure (polys.set poly (some interp))
        let some (some p) := polys1[poly]? | .error .expectFailed
        let yVal ← p.computeAt pt.x
        pure (polys1, yVal)
    let out' := out ++ u16ToBeBytes y.value
    decodedMessageLoop self pointsVecs (i + 1) rem polys' out'

/-- `<PolyDecoder as Decoder>::decoded_message` (`src/encoding/polynomial.rs:923–976`): returns
`none` if `isComplete` is set or any polynomial lacks `necessaryPoints` points, otherwise
reconstructs the message via direct lookup or Lagrange interpolation. -/
def decodedMessage (self : PolyDecoder) : Except PolyPanic (Option (List (BitVec 8))) := do
  if self.isComplete then
    return none
  else
    let (retNone, pointsVecs) ← collectPointsVecs self 0 self.pts.length false []
    if retNone then
      return none
    else if self.ptsNeeded * 2 > USIZE_MAX then
      .error .mulOverflow
    else
      let initPolys : List (Option Poly) := List.replicate 16 none
      let (_, out) ← decodedMessageLoop self pointsVecs 0 self.ptsNeeded initPolys []
      return some out

end PolyDecoder

/-! ## `Option<T>` implementations of `Encoder` and `Decoder` (`src/encoding.rs:53–101`) -/

namespace OptionEncoder

def encodeBytes (msg : List (BitVec 8)) :
    Except PolyPanic (Except EncodingError (Option PolyEncoder)) := do
  let res ← PolyEncoder.encodeBytes msg
  match res with
  | .error e => return .error e
  | .ok enc => return .ok (some enc)

/-- `<Option<PolyEncoder> as Encoder>::next_chunk` (`src/encoding.rs:63–71`); panics with
`.unwrapFailed` on `none`. -/
def nextChunk (self : Option PolyEncoder) :
    Except PolyPanic (Option PolyEncoder × Chunk) := do
  let some tmp := self | .error .unwrapFailed
  let (tmp', chunk) ← tmp.nextChunk
  return (some tmp', chunk)

end OptionEncoder

namespace OptionDecoder

def new (lenBytes : Nat) :
    Except PolyPanic (Except EncodingError (Option PolyDecoder)) := do
  let res ← PolyDecoder.new lenBytes
  match res with
  | .error e => return .error e
  | .ok dec => return .ok (some dec)

/-- `<Option<PolyDecoder> as Decoder>::add_chunk` (`src/encoding.rs:83–90`); panics with
`.unwrapFailed` on `none`. -/
def addChunk (self : Option PolyDecoder) (chunk : Chunk) :
    Except PolyPanic (Option PolyDecoder) := do
  let some tmp := self | .error .unwrapFailed
  let tmp' ← tmp.addChunk chunk
  return some tmp'

/-- `<Option<PolyDecoder> as Decoder>::decoded_message` (`src/encoding.rs:93–100`); panics with
`.unwrapFailed` on `none`. -/
def decodedMessage (self : Option PolyDecoder) :
    Except PolyPanic (Option (List (BitVec 8))) := do
  let some value := self | .error .unwrapFailed
  value.decodedMessage

end OptionDecoder

/-! ## Kernel-checked self-tests -/

 def isOkEq {ε α : Type} [DecidableEq α] (r : Except ε α) (expected : α) : Bool :=
  match r with
  | .ok v => decide (v = expected)
  | .error _ => false

 def isErrEq {ε α : Type} [DecidableEq ε] (r : Except ε α) (expected : ε) : Bool :=
  match r with
  | .ok _ => false
  | .error e => decide (e = expected)

 def isOkErrEq {ε₁ ε₂ α : Type} [DecidableEq ε₂] (r : Except ε₁ (Except ε₂ α)) (expected : ε₂) : Bool :=
  match r with
  | .ok (.error e) => decide (e = expected)
  | _ => false

 def runPtSerializeAndOrdGuard : Bool :=
  let pt : Pt := { x := ⟨0x1234#16⟩, y := ⟨0x5678#16⟩ }
  let ptSameX : Pt := { x := ⟨0x1234#16⟩, y := ⟨0x9abc#16⟩ }
  let ptLargerX : Pt := { x := ⟨0x2000#16⟩, y := ⟨0x0001#16⟩ }
  isOkEq (Pt.deserialize (Pt.serialize pt)) pt &&
    isErrEq (Pt.deserialize [0x12#8, 0x34#8]) PolyPanic.unwrapFailed &&
    Pt.eq pt ptSameX &&
    decide (Pt.cmp pt ptSameX = .eq) &&
    decide (Pt.cmp pt ptLargerX = .lt)

theorem pt_serialize_and_ord_guard : runPtSerializeAndOrdGuard = true := by
  decide +kernel

 def runSortedSetPtSemanticsGuard : Bool :=
  let p1 : Pt := { x := ⟨1#16⟩, y := ⟨10#16⟩ }
  let p3 : Pt := { x := ⟨3#16⟩, y := ⟨30#16⟩ }
  let p2 : Pt := { x := ⟨2#16⟩, y := ⟨20#16⟩ }
  let p3New : Pt := { x := ⟨3#16⟩, y := ⟨300#16⟩ }
  let p1New : Pt := { x := ⟨1#16⟩, y := ⟨100#16⟩ }
  let (s, _, _) := SortedSetPt.new.push p1
  let (s, _, _) := s.push p3
  let (s, _, _) := s.push p2
  let (sPushBack, idxBack, oldBack) := s.push p3New
  let (sPushMid, idxMid, oldMid) := sPushBack.push p1New
  decide (s.vec = [p1, p2, p3]) &&
    decide (idxBack = 2) && decide (oldBack = some p3) && decide (sPushBack.vec = [p1, p2, p3New]) &&
    decide (idxMid = 0) && decide (oldMid = some p1) && decide (sPushMid.vec = [p1New, p2, p3New])

theorem sortedSetPt_semantics_guard : runSortedSetPtSemanticsGuard = true := by
  decide +kernel

 def runPolyLagrangeInterpolateGuard : Bool :=
  let pts : List Pt :=
    [ { x := ⟨0#16⟩, y := ⟨0x1357#16⟩ }
    , { x := ⟨1#16⟩, y := ⟨0x2468#16⟩ }
    , { x := ⟨2#16⟩, y := ⟨0xabcd#16⟩ }
    , { x := ⟨3#16⟩, y := ⟨0xdead#16⟩ }
    , { x := ⟨4#16⟩, y := ⟨0xbeef#16⟩ } ]
  isOkEq (do
    let p ← Poly.lagrangeInterpolate pts
    let ok1 ← pts.allM (fun (pt : Pt) => do
      let v ← p.computeAt pt.x
      return (v == pt.y))
    let pts2 ← (List.range 5).mapM (fun i => do
      let x : GF16 := GF16.new (BitVec.ofNat 16 (i + 5))
      let y ← p.computeAt x
      return ({ x := x, y := y } : Pt))
    let p2 ← Poly.lagrangeInterpolate pts2
    let ok2 ← pts.allM (fun (pt : Pt) => do
      let v ← p2.computeAt pt.x
      return (v == pt.y))
    let fromComp ← Poly.fromCompletePoints pts
    return (ok1 && ok2 && decide (p = p2) && isOkEq fromComp p)) true

theorem poly_lagrange_interpolate_guard : runPolyLagrangeInterpolateGuard = true := by
  decide +kernel

 def runPolyConstAndPanicGuards : Bool :=
  COMPLETE_POINTS_POLYS_1.isOk &&
    COMPLETE_POINTS_POLYS_3.isOk &&
    COMPLETE_POINTS_POLYS_5.isOk &&
    isErrEq (({ coefficients := [⟨1#16⟩, ⟨2#16⟩] } : Poly).multXdiffAssignTrailing 0 ⟨1#16⟩)
      PolyPanic.subOverflow &&
    isErrEq (({ coefficients := [⟨1#16⟩, ⟨2#16⟩] } : Poly).lagrangeInterpolateComplete
      [{ x := ⟨0#16⟩, y := ⟨1#16⟩ }] 1) PolyPanic.boundsCheck &&
    isErrEq (({ coefficients := [⟨0#16⟩, ⟨1#16⟩] } : PolyConst 2).multXdiff ⟨1#16⟩)
      PolyPanic.explicitPanic &&
    isOkErrEq (Poly.deserialize []) PolynomialError.serializationInvalid &&
    isOkErrEq (Poly.deserialize [1#8, 2#8, 3#8]) PolynomialError.serializationInvalid

theorem poly_const_and_panic_guards : runPolyConstAndPanicGuards = true := by
  decide +kernel

 def runEncodeAndDecodeSmallGuard : Bool :=
  let msg : List (BitVec 8) :=
    [0x61#8, 0x62#8, 0x63#8, 0x64#8, 0x65#8, 0x66#8, 0x67#8, 0x68#8, 0x69#8, 0x6a#8]
  isOkEq (do
    let .ok encoder ← PolyEncoder.encodeBytes msg | return false
    let .ok decoder ← PolyDecoder.new 10 | return false
    let (encoder, c1) ← encoder.chunkAt 1#16
    let (_encoder, c2) ← encoder.chunkAt 2#16
    let decoder ← decoder.addChunk c1
    let decoder ← decoder.addChunk c2
    let decoded ← decoder.decodedMessage
    return (decoded == some msg)) true

theorem encode_and_decode_small_guard : runEncodeAndDecodeSmallGuard = true := by
  decide +kernel

 def runPolyEncoderDecoderRoundtripsGuard : Bool :=
  let msg : List (BitVec 8) := (List.range 96).map (fun i => BitVec.ofNat 8 (i + 1))
  isOkEq (do
    let .ok enc1 ← PolyEncoder.encodeBytes msg | return false
    let .ok dec1 ← PolyDecoder.new 96 | return false
    let (enc1, c0) ← enc1.nextChunk
    let (enc1, c1) ← enc1.nextChunk
    let (_enc1, c2) ← enc1.nextChunk
    let dec1 ← dec1.addChunk c0
    let dec1 ← dec1.addChunk c1
    let .none ← dec1.decodedMessage | return false
    let dec1 ← dec1.addChunk c2
    let .some m1 ← dec1.decodedMessage | return false
    let .ok enc2 ← PolyEncoder.encodeBytes msg | return false
    let .ok dec2 ← PolyDecoder.new 96 | return false
    let .ok enc2 ← PolyEncoder.fromPb enc2.intoPb | return false
    let (enc2, c4) ← enc2.chunkAt 4#16
    let (enc2, c2') ← enc2.chunkAt 2#16
    let dec2 ← dec2.addChunk c4
    let dec2 ← dec2.addChunk c2'
    let .ok enc2 ← PolyEncoder.fromPb enc2.intoPb | return false
    let .ok dec2 ← PolyDecoder.fromPb dec2.intoPb | return false
    let (_enc2, c1') ← enc2.chunkAt 1#16
    let dec2 ← dec2.addChunk c2'
    let dec2 ← dec2.addChunk c1'
    let .some m2 ← dec2.decodedMessage | return false
    return (m1 == msg && m2 == msg)) true

theorem poly_encoder_decoder_roundtrips_guard : runPolyEncoderDecoderRoundtripsGuard = true := by
  decide +kernel

 def runOptionEncoderDecoderGuard : Bool :=
  let msg : List (BitVec 8) := (List.range 64).map (fun i => BitVec.ofNat 8 (i + 10))
  isOkEq (do
    let p1 := isErrEq (OptionEncoder.nextChunk none) PolyPanic.unwrapFailed
    let p2 := isErrEq (OptionDecoder.decodedMessage none) PolyPanic.unwrapFailed
    let .ok optEnc ← OptionEncoder.encodeBytes msg | return false
    let .ok optDec ← OptionDecoder.new 64 | return false
    let (optEnc, c0) ← OptionEncoder.nextChunk optEnc
    let (_optEnc, c1) ← OptionEncoder.nextChunk optEnc
    let optDec ← OptionDecoder.addChunk optDec c1
    let .none ← OptionDecoder.decodedMessage optDec | return false
    let optDec ← OptionDecoder.addChunk optDec c0
    let .some decoded ← OptionDecoder.decodedMessage optDec | return false
    return (p1 && p2 && (decoded == msg))) true

theorem option_encoder_decoder_guard : runOptionEncoderDecoderGuard = true := by
  decide +kernel

end CryptoVerification.LibsignalSpqrV1
