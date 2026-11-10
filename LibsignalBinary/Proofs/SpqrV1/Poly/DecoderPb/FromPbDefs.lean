/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.Defs
public import LibsignalBinary.Proofs.SpqrV1.Drop.Poly

/-!
# `<spqr::encoding::polynomial::PolyDecoder>::from_pb`: Definitions and Specifications

**Checked by Lean.**

Total pure model (`fromPbDecResult`) and AArch64 separation-logic contracts (`fromPbDecSpec`,
`fromPbDecSpecX`) for `<PolyDecoder>::from_pb` (`0x62b1c`, Block `376`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Poly.DecoderPb

open Arm64 ProofLib
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Drop

/-! ## Symbol Names and Stack Budgets -/

abbrev fromPbDecName : String :=
  "<spqr::encoding::polynomial::PolyDecoder>::from_pb"

/-- Own stack frame of `<PolyDecoder>::from_pb` (`96 + 448 = 544` bytes). -/
abbrev fromPbDecFrame : Nat := 544

/-- Stack budget of `<PolyDecoder>::from_pb` (`1024 + dropGluePoly16Stack = 1056 + allocHookStack`,
    matching `States.FromPb.decoderFromPbStack`). -/
abbrev fromPbDecStack : Nat := 1024 + dropGluePoly16Stack

/-- Extended-stack budget of `<PolyDecoder>::from_pb` (`544 + extHookStack`). -/
abbrev fromPbDecStackX : Nat := fromPbDecFrame + extHookStack

/-! ## Total Pure Model for `PolyDecoder.fromPb` -/

/-- Total version of `PolyDecoder.pushChunksExact4` (when `pts.length % 4 = 0`). -/
def pushChunks4Total : List (BitVec 8) → SortedSetPt → SortedSetPt
  | b0 :: b1 :: b2 :: b3 :: rest, v =>
    let pt : Pt := { x := GF16.new (u16FromBeBytes b0 b1), y := GF16.new (u16FromBeBytes b2 b3) }
    pushChunks4Total rest (v.push pt).1
  | _, v => v

theorem pushChunks4_eq_ok :
    ∀ (pts : List (BitVec 8)) (v : SortedSetPt),
      pts.length % 4 = 0 →
      PolyDecoder.pushChunksExact4 pts v = .ok (pushChunks4Total pts v)
  | [], v, _ => rfl
  | [_], _, hmod => by simp at hmod
  | [_, _], _, hmod => by simp at hmod
  | [_, _, _], _, hmod => by simp at hmod
  | b0 :: b1 :: b2 :: b3 :: rest, v, hmod => by
    have hrest : rest.length % 4 = 0 := by
      simp only [List.length_cons] at hmod
      omega
    unfold PolyDecoder.pushChunksExact4 pushChunks4Total
    change (do
      let pt ← Pt.deserialize [b0, b1, b2, b3]
      let (v', _, _) := v.push pt
      PolyDecoder.pushChunksExact4 rest v') = _
    have hpt : Pt.deserialize [b0, b1, b2, b3] =
        .ok { x := GF16.new (u16FromBeBytes b0 b1), y := GF16.new (u16FromBeBytes b2 b3) } := rfl
    rw [hpt]
    exact pushChunks4_eq_ok rest _ hrest

theorem replace_vec_length_le_succ (v : SortedSetPt) (pt : Pt) :
    (v.replace pt).1.vec.length ≤ v.vec.length + 1 := by
  unfold SortedSetPt.replace
  dsimp only []
  split
  · simp
  · rw [List.length_append, List.length_cons, List.length_take, List.length_drop]
    omega

theorem push_vec_length_le_succ (v : SortedSetPt) (pt : Pt) :
    (v.push pt).1.vec.length ≤ v.vec.length + 1 := by
  unfold SortedSetPt.push
  dsimp only []
  split
  · split
    · simp
    · simp [List.length_dropLast]
    · exact replace_vec_length_le_succ v pt
  · simp

theorem pushChunks4Total_length_le :
    ∀ (pts : List (BitVec 8)) (v : SortedSetPt),
      (pushChunks4Total pts v).vec.length ≤ v.vec.length + pts.length / 4
  | [], v => by simp [pushChunks4Total]
  | [_], v => by simp [pushChunks4Total]
  | [_, _], v => by simp [pushChunks4Total]
  | [_, _, _], v => by simp [pushChunks4Total]
  | b0 :: b1 :: b2 :: b3 :: rest, v => by
    unfold pushChunks4Total
    have ih := pushChunks4Total_length_le rest
      (v.push { x := GF16.new (u16FromBeBytes b0 b1), y := GF16.new (u16FromBeBytes b2 b3) }).1
    have hp := push_vec_length_le_succ v
      { x := GF16.new (u16FromBeBytes b0 b1), y := GF16.new (u16FromBeBytes b2 b3) }
    simp only [List.length_cons]
    omega

theorem pushChunks4Total_strictSorted :
    ∀ (pts : List (BitVec 8)) (v : SortedSetPt),
      SortedSetPtStrictSorted v →
      SortedSetPtStrictSorted (pushChunks4Total pts v)
  | [], v, hs => by simpa [pushChunks4Total] using hs
  | [_], v, hs => by simpa [pushChunks4Total] using hs
  | [_, _], v, hs => by simpa [pushChunks4Total] using hs
  | [_, _, _], v, hs => by simpa [pushChunks4Total] using hs
  | b0 :: b1 :: b2 :: b3 :: rest, v, hs => by
    unfold pushChunks4Total
    apply pushChunks4Total_strictSorted rest
    have ⟨heq, hsort'⟩ :=
      bsearchPush_eq_push v
        { x := GF16.new (u16FromBeBytes b0 b1), y := GF16.new (u16FromBeBytes b2 b3) } hs
    rw [← heq]
    exact hsort'

/-- Total version of `PolyDecoder.decodeDecoderPbPts`. -/
def decodePbPtsTotal : List (List (BitVec 8)) → Except PolynomialError (List SortedSetPt)
  | [] => .ok []
  | pts :: rest =>
    if pts.length % 4 != 0 then
      .error .serializationInvalid
    else
      let v := pushChunks4Total pts (SortedSetPt.withCapacity (pts.length / 4))
      match decodePbPtsTotal rest with
      | .error e => .error e
      | .ok vs => .ok (v :: vs)

theorem decodePbPts_eq_ok :
    ∀ (ptsList : List (List (BitVec 8))),
      PolyDecoder.decodeDecoderPbPts ptsList = .ok (decodePbPtsTotal ptsList)
  | [] => rfl
  | pts :: rest => by
    unfold PolyDecoder.decodeDecoderPbPts decodePbPtsTotal
    by_cases hmod : pts.length % 4 = 0
    · have hne : (pts.length % 4 != 0) = false := by simp [hmod]
      simp only [hne, Bool.false_eq_true, ↓reduceIte, Bind.bind, Except.bind,
        pushChunks4_eq_ok pts _ hmod, decodePbPts_eq_ok rest]
      rcases decodePbPtsTotal rest with e | vs <;> rfl
    · have hne : (pts.length % 4 != 0) = true := by simp [hmod]
      simp only [hne, ↓reduceIte]
      rfl

theorem decodePbPtsTotal_length :
    ∀ {ptsList : List (List (BitVec 8))} {vs : List SortedSetPt},
      decodePbPtsTotal ptsList = .ok vs →
      vs.length = ptsList.length
  | [], vs, h => by
    simp only [decodePbPtsTotal, Except.ok.injEq] at h
    subst h; rfl
  | pts :: rest, vs, h => by
    unfold decodePbPtsTotal at h
    split at h
    · contradiction
    · split at h
      · contradiction
      · rename_i vs' hrest
        simp only [Except.ok.injEq] at h
        subst h
        simp [decodePbPtsTotal_length hrest]

theorem decodePbPtsTotal_strictSorted :
    ∀ {ptsList : List (List (BitVec 8))} {vs : List SortedSetPt},
      decodePbPtsTotal ptsList = .ok vs →
      ∀ s ∈ vs, SortedSetPtStrictSorted s
  | [], vs, h => by
    simp only [decodePbPtsTotal, Except.ok.injEq] at h
    subst h
    intro s hs; simp at hs
  | pts :: rest, vs, h => by
    unfold decodePbPtsTotal at h
    split at h
    · contradiction
    · split at h
      · contradiction
      · rename_i vs' hrest
        simp only [Except.ok.injEq] at h
        subst h
        intro s hs
        rcases List.mem_cons.mp hs with rfl | hmem
        · apply pushChunks4Total_strictSorted
          simp [SortedSetPtStrictSorted, PtListStrictSorted, SortedSetPt.withCapacity]
        · exact decodePbPtsTotal_strictSorted hrest s hmem

/-- Total result of `<PolyDecoder>::from_pb`. -/
def fromPbDecResult (pb : ProtoPolynomialDecoder) : Except PolynomialError PolyDecoder :=
  if pb.pts.length != 16 then
    .error .serializationInvalid
  else
    match decodePbPtsTotal pb.pts with
    | .error e => .error e
    | .ok outPts =>
      .ok {
        ptsNeeded := pb.ptsNeeded.toNat
        isComplete := pb.isComplete
        pts := outPts
      }

theorem fromPbDec_eq_ok (pb : ProtoPolynomialDecoder) :
    PolyDecoder.fromPb pb = .ok (fromPbDecResult pb) := by
  unfold PolyDecoder.fromPb fromPbDecResult
  by_cases hlen : (pb.pts.length != 16) = true
  · simp only [hlen, ↓reduceIte]; rfl
  · simp only [hlen, Bool.false_eq_true, ↓reduceIte, Bind.bind, Except.bind,
      decodePbPts_eq_ok pb.pts]
    rcases decodePbPtsTotal pb.pts with e | outPts <;> rfl

theorem fromPbDecResult_strictSorted {pb : ProtoPolynomialDecoder} {dec : PolyDecoder}
    (h : fromPbDecResult pb = .ok dec) :
    PolyDecoderStrictSorted dec := by
  unfold fromPbDecResult at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · rename_i outPts hout
      simp only [Except.ok.injEq] at h
      subst h
      exact decodePbPtsTotal_strictSorted hout

theorem fromPbDecResult_pts_length {pb : ProtoPolynomialDecoder} {dec : PolyDecoder}
    (h : fromPbDecResult pb = .ok dec) :
    dec.pts.length = NUM_POLYS := by
  unfold fromPbDecResult at h
  split at h
  · contradiction
  · rename_i hlen
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hlen
    split at h
    · contradiction
    · rename_i outPts hout
      simp only [Except.ok.injEq] at h
      subst h
      have h16 : NUM_POLYS = 16 := rfl
      rw [h16, ← hlen]
      exact decodePbPtsTotal_length hout

/-! ## Specifications of `<spqr::encoding::polynomial::PolyDecoder>::from_pb` (`0x62b1c`) -/

/-- Ghost arguments of `<PolyDecoder>::from_pb` (`0x62b1c`). -/
structure FromPbDecGhost where
  /-- Sret pointer (`x0`, 400-byte `Result<PolyDecoder, PolynomialError>` output). -/
  out : BitVec 64
  /-- Pointer to the 40-byte `ProtoPolynomialDecoder` moved by value (`x1`). -/
  pbA : BitVec 64
  /-- Logical `ProtoPolynomialDecoder` value at `pbA`. -/
  pb : ProtoPolynomialDecoder

/-- Specification of `<PolyDecoder>::from_pb` (`0x62b1c`): consumes `protoPolynomialDecoderAt A pbA pb` at `x1` into `memRegion pbA 40` and writes `resultPolyDecoderFromPbAt A out (fromPbDecResult pb)` to `x0 = out` (or panics on OOM). -/
def fromPbDecSpec (A : RustAlloc) : Spec FromPbDecGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.pbA⌝ ∗
      memRegion x.out polyDecoderSize ∗
      protoPolynomialDecoderAt A x.pbA x.pb ∗
      A.pool ∗ stackAt s.sp fromPbDecStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      resultPolyDecoderFromPbAt A x.out (fromPbDecResult x.pb) ∗
      memRegion x.pbA protoPolynomialDecoderSize ∗
      A.pool ∗ stackAt s0.sp fromPbDecStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Extended-stack variant of `fromPbDecSpec` (`fromPbDecStackX = 544 + extHookStack`). -/
def fromPbDecSpecX (A : RustAlloc) : Spec FromPbDecGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.pbA⌝ ∗
      memRegion x.out polyDecoderSize ∗
      protoPolynomialDecoderAt A x.pbA x.pb ∗
      A.pool ∗ stackAt s.sp fromPbDecStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      resultPolyDecoderFromPbAt A x.out (fromPbDecResult x.pb) ∗
      memRegion x.pbA protoPolynomialDecoderSize ∗
      A.pool ∗ stackAt s0.sp fromPbDecStackX
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def FromPbDecOkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr fromPbDecName)
    (fromPbDecSpec A)

def FromPbDecOkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr fromPbDecName)
    ((fromPbDecSpecX A).inImage img)

def FromPbDecPlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
    (blkPl_376).base
    (fromPbDecSpec A)

def FromPbDecPlacedOkX [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
    (blkPl_376).base
    (fromPbDecSpecX A)

end CryptoVerification.SpqrV1.Poly.DecoderPb
