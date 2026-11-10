/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.Repr
public import LibsignalBinary.Specifications.LibsignalTripleRatchetRepr

/-!
# AArch64 Memory Layouts for `Chunk`, `PolyEncoder`, and `PolyDecoder`

**Checked by Lean.**

AArch64 field offsets, `Option`/`Result` niche encodings, and separation-logic representation
predicates for `Point` (24 B), `Chunk` (34 B), `PolyEncoder` (400 B, niche tag `2` at `+0x00`),
`PolyDecoder` (400 B, niche `pts[0].cap = usize::MAX` at `+0x00`), `ProtoPolynomialEncoder` (56 B),
and `ProtoPolynomialDecoder` (40 B).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Poly

open Arm64 ProofLib
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1

/-! ## 1. `Point` (`spqr::encoding::polynomial::Point`, `24` bytes, align `8`) -/

/-- Heap buffer of a `Point` (`value: Vec<GF16>`, stride 2, alignment 2) with capacity `cap`
    at `ptr` holding `pt.value`. -/
def pointBuf (A : RustAlloc) (cap ptr : BitVec 64) (pt : Point) : SepProp :=
  vecBuf A gf16Stride gf16Align gf16At cap ptr pt.value

/-- A `Point` at address `v` with pinned capacity `cap` and buffer pointer `ptr` holding `pt.value`. -/
def pointAt (A : RustAlloc) (v cap ptr : BitVec 64) (pt : Point) : SepProp :=
  vecAt A gf16Stride gf16Align gf16At v cap ptr pt.value

/-- A `Point` at address `v` with ghost pin `pin : VecPin` holding `pt`. -/
def pointPinAt (A : RustAlloc) (pin : VecPin) (pt : Point) (v : BitVec 64) : SepProp :=
  pointAt A v pin.cap pin.ptr pt

/-- Some `Point` at address `v` holding `pt` (capacity and buffer pointer existentially quantified). -/
def pointOf (A : RustAlloc) (v : BitVec 64) (pt : Point) : SepProp :=
  vecOf A gf16Stride gf16Align gf16At v pt.value

/-! ## 2. `Chunk` (`spqr::encoding::Chunk`, `34` bytes, align `2`) -/

/-- Byte size of `spqr::encoding::Chunk` (`34` bytes = `0x22`). -/
def chunkSize : Nat := 34

def chunkSizeBV : BitVec 64 := 0x22#64

/-- Byte alignment of `Chunk` (`2` bytes). -/
def chunkAlign : BitVec 64 := 2#64

/-- Offset of `data: [u8; 32]` within `Chunk` (`+0x00`). -/
def chunkDataOff : BitVec 64 := 0x00#64

/-- Offset of `index: u16` within `Chunk` (`+0x20`). -/
def chunkIndexOff : BitVec 64 := 0x20#64

/-- Read-write `spqr::encoding::Chunk` at `a` (`34` bytes, align `2`):
    * `a + 0x00..0x20`: `data: [u8; 32]` (`a ↦ₛ c.data.toList`)
    * `a + 0x20..0x22`: `index: u16` (`(a + 0x20#64) ↦₁₆ c.index`) -/
def chunkAt (a : BitVec 64) (c : Chunk) : SepProp :=
  (a ↦ₛ c.data.toList) ∗ ((a + chunkIndexOff) ↦₁₆ c.index)

/-! ## 3. `PolynomialError` and `EncodingError` Discriminant (`u8`) -/

/-- `spqr::encoding::polynomial::PolynomialError` `u8` discriminant in `Result<T, PolynomialError>`:
    * `0#8`: `MessageLengthEven` (`encode_bytes @ 0x6b704: strb wzr, [x19, #0x8]`)
    * `1#8`: `MessageLengthTooLong` (`encode_bytes @ 0x6b6f4: mov w8, #1; strb w8, [x19, #0x8]`)
    * `2#8`: `SerializationInvalid` (`PolyEncoder::from_pb @ 0x62730: mov w8, #2; strb w8, [x0, #0x8]`) -/
def polynomialErrorByte : PolynomialError → BitVec 8
  | .messageLengthEven => 0#8
  | .messageLengthTooLong => 1#8
  | .serializationInvalid => 2#8

/-- `spqr::encoding::EncodingError` `u8` discriminant in `Result<T, EncodingError>`:
    * `0#8..2#8`: `PolynomialError(e)`
    * `3#8`: `ChunkIndexDecodingError`
    * `4#8`: `ChunkDataDecodingError` -/
def encodingErrorByte : EncodingError → BitVec 8
  | .polynomialError e => polynomialErrorByte e
  | .chunkIndexDecodingError => 3#8
  | .chunkDataDecodingError => 4#8

/-! ## 4. `PolyEncoder` (`400` bytes = `0x190`, align `8`), `Option<PolyEncoder>`, and `Result<PolyEncoder, _>` -/

/-- Byte size of `spqr::encoding::polynomial::PolyEncoder` (`400` bytes = `0x190`). -/
def polyEncoderSize : Nat := 400

def polyEncoderSizeBV : BitVec 64 := 0x190#64

/-- Byte alignment of `PolyEncoder` (`8` bytes). -/
def polyEncoderAlign : BitVec 64 := 8#64

/-- Offset of the 8-byte `EncoderState` discriminant within `PolyEncoder` (`+0x00`). -/
def polyEncoderTagOff : BitVec 64 := 0x00#64

/-- Offset of the 384-byte (`0x180`) payload `[Point; 16]` / `[Poly; 16]` within `PolyEncoder` (`+0x08`). -/
def polyEncoderVecsOff : BitVec 64 := 0x08#64

/-- Byte size of the 16-element `Vec` array `[Point; 16]` or `[Poly; 16]` (`384` bytes = `0x180`). -/
def polyEncoderVecsSize : Nat := 384

/-- Offset of `idx: u32` within `PolyEncoder` (`+0x188`). -/
def polyEncoderIdxOff : BitVec 64 := 0x188#64

/-- Offset of the 4-byte trailing padding within `PolyEncoder` (`+0x18c`). -/
def polyEncoderPadOff : BitVec 64 := 0x18c#64

def polyEncoderPadSize : Nat := 4

/-- `EncoderState::Points([Point; 16])` discriminant (`0#64`). -/
def polyEncoderPointsTag : BitVec 64 := 0#64

/-- `EncoderState::Polys([Poly; 16])` discriminant (`1#64`). -/
def polyEncoderPolysTag : BitVec 64 := 1#64

/-- Niche discriminant (`2#64`) at `+0x00` for `Option<PolyEncoder>::None` and
    `Result<PolyEncoder, _>::Err`. -/
def polyEncoderNicheTag : BitVec 64 := 2#64

/-- Offset of the error discriminant byte within `Result<PolyEncoder, _>::Err` (`+0x08`). -/
def resultPolyEncoderErrByteOff : BitVec 64 := 0x08#64

/-- Uninitialized tail byte count after `+0x08` in `Option<PolyEncoder>::None` (`392` bytes). -/
def optPolyEncoderNoneTailSize : Nat := 392

/-- Uninitialized tail byte count after `+0x09` in `Result<PolyEncoder, _>::Err` (`391` bytes). -/
def resultPolyEncoderErrTailSize : Nat := 391

/-- Pinned array of `Point` (`Vec<GF16>`) headers at `base` with stride `24` bytes. -/
def pointListPinAt (A : RustAlloc) : BitVec 64 → List VecPin → List Point → SepProp
  | _, _, [] => emp
  | _, [], _ :: _ => ⌜False⌝
  | base, pin :: pins, pt :: pts =>
    pointPinAt A pin pt base ∗ pointListPinAt A (base + 24#64) pins pts

/-- Unpinned array of `Point` (`Vec<GF16>`) headers at `base` with stride `24` bytes. -/
def pointListOf (A : RustAlloc) : BitVec 64 → List Point → SepProp :=
  arrayAt (fun pt addr => pointOf A addr pt) vecHeaderBytes

/-- Pinned array of `Poly` (`Vec<GF16>`) headers at `base` with stride `24` bytes. -/
def polyListPinAt (A : RustAlloc) : BitVec 64 → List VecPin → List LibsignalSpqrV1.Poly → SepProp
  | _, _, [] => emp
  | _, [], _ :: _ => ⌜False⌝
  | base, pin :: pins, p :: ps =>
    polyPinAt A pin p base ∗ polyListPinAt A (base + 24#64) pins ps

/-- Unpinned array of `Poly` (`Vec<GF16>`) headers at `base` with stride `24` bytes. -/
def polyListOf (A : RustAlloc) : BitVec 64 → List LibsignalSpqrV1.Poly → SepProp :=
  arrayAt (fun p addr => polyOf A addr p) vecHeaderBytes

/-- Ghost pins for the 16 `Vec<GF16>` fields of a `PolyEncoder`. -/
structure PolyEncoderGhost where
  /-- The 16 `(cap, ptr)` pins for `[Point; 16]` or `[Poly; 16]`. -/
  pins : List VecPin

/-- Pinned `EncoderState` at `a` (`392` bytes = `0x188` at `+0x00..+0x188`):
    * `.points pts`: `pts.length = 16`, `(a ↦₆₄ 0#64) ∗ pointListPinAt A (a + 8#64) g.pins pts`
    * `.polys polys`: `polys.length = 16`, `(a ↦₆₄ 1#64) ∗ polyListPinAt A (a + 8#64) g.pins polys` -/
def encoderStatePinnedAt (A : RustAlloc) (g : PolyEncoderGhost) (a : BitVec 64) :
    EncoderState → SepProp
  | .points pts =>
    ⌜pts.length = NUM_POLYS ∧ g.pins.length = NUM_POLYS ∧
      (∀ pt ∈ pts, pt.value.length ≤ 0x0555555555555555)⌝ ∗
      (a ↦₆₄ polyEncoderPointsTag) ∗
      pointListPinAt A (a + polyEncoderVecsOff) g.pins pts
  | .polys polys =>
    ⌜polys.length = NUM_POLYS ∧ g.pins.length = NUM_POLYS⌝ ∗
      (a ↦₆₄ polyEncoderPolysTag) ∗
      polyListPinAt A (a + polyEncoderVecsOff) g.pins polys

/-- Unpinned `EncoderState` at `a` (`392` bytes = `0x188` at `+0x00..+0x188`). -/
def encoderStateAt (A : RustAlloc) (a : BitVec 64) : EncoderState → SepProp
  | .points pts =>
    ⌜pts.length = NUM_POLYS ∧ (∀ pt ∈ pts, pt.value.length ≤ 0x0555555555555555)⌝ ∗
      (a ↦₆₄ polyEncoderPointsTag) ∗
      pointListOf A (a + polyEncoderVecsOff) pts
  | .polys polys =>
    ⌜polys.length = NUM_POLYS⌝ ∗
      (a ↦₆₄ polyEncoderPolysTag) ∗
      polyListOf A (a + polyEncoderVecsOff) polys

/-- Pinned `spqr::encoding::polynomial::PolyEncoder` at `a` (`400` bytes = `0x190`, align `8`):
    * `a + 0x00..0x188`: `s: EncoderState` (tag at `+0x00`, 16 `Vec<GF16>` headers at `+0x08..+0x188`)
    * `a + 0x188..0x18c`: `idx: u32`
    * `a + 0x18c..0x190`: 4 bytes trailing padding (`memRegion (a + 0x18c#64) 4`) -/
def polyEncoderPinnedAt (A : RustAlloc) (g : PolyEncoderGhost) (a : BitVec 64)
    (enc : PolyEncoder) : SepProp :=
  encoderStatePinnedAt A g a enc.s ∗
    ((a + polyEncoderIdxOff) ↦₃₂ enc.idx) ∗
    memRegion (a + polyEncoderPadOff) polyEncoderPadSize

/-- Unpinned `spqr::encoding::polynomial::PolyEncoder` at `a` (`400` bytes = `0x190`, align `8`). -/
def polyEncoderAt (A : RustAlloc) (a : BitVec 64) (enc : PolyEncoder) : SepProp :=
  encoderStateAt A a enc.s ∗
    ((a + polyEncoderIdxOff) ↦₃₂ enc.idx) ∗
    memRegion (a + polyEncoderPadOff) polyEncoderPadSize

/-- Pinned `Option<PolyEncoder>` at `a` (`400` bytes = `0x190`, align `8`):
    * `none`: `(a ↦₆₄ 2#64) ∗ memRegion (a + 8#64) 392`
    * `some enc`: `polyEncoderPinnedAt A g a enc` -/
def optPolyEncoderPinnedAt (A : RustAlloc) (g : PolyEncoderGhost) (a : BitVec 64) :
    Option PolyEncoder → SepProp
  | none => (a ↦₆₄ polyEncoderNicheTag) ∗ memRegion (a + 8#64) optPolyEncoderNoneTailSize
  | some enc => polyEncoderPinnedAt A g a enc

/-- Unpinned `Option<PolyEncoder>` at `a` (`400` bytes = `0x190`, align `8`). -/
def optPolyEncoderAt (A : RustAlloc) (a : BitVec 64) : Option PolyEncoder → SepProp
  | none => (a ↦₆₄ polyEncoderNicheTag) ∗ memRegion (a + 8#64) optPolyEncoderNoneTailSize
  | some enc => polyEncoderAt A a enc

/-- Pinned `Result<PolyEncoder, EncodingError>` at `a` (`400` bytes = `0x190`, align `8`):
    * `.ok enc`: `polyEncoderPinnedAt A g a enc`
    * `.error err`: `(a ↦₆₄ 2#64) ∗ ((a + 8#64) ↦₈ encodingErrorByte err) ∗ memRegion (a + 9#64) 391` -/
def resultPolyEncoderPinnedAt (A : RustAlloc) (g : PolyEncoderGhost) (a : BitVec 64) :
    Except EncodingError PolyEncoder → SepProp
  | .ok enc => polyEncoderPinnedAt A g a enc
  | .error err =>
    (a ↦₆₄ polyEncoderNicheTag) ∗
      ((a + resultPolyEncoderErrByteOff) ↦₈ encodingErrorByte err) ∗
      memRegion (a + 9#64) resultPolyEncoderErrTailSize

/-- Unpinned `Result<PolyEncoder, EncodingError>` at `a` (`400` bytes = `0x190`, align `8`). -/
def resultPolyEncoderAt (A : RustAlloc) (a : BitVec 64) :
    Except EncodingError PolyEncoder → SepProp
  | .ok enc => polyEncoderAt A a enc
  | .error err =>
    (a ↦₆₄ polyEncoderNicheTag) ∗
      ((a + resultPolyEncoderErrByteOff) ↦₈ encodingErrorByte err) ∗
      memRegion (a + 9#64) resultPolyEncoderErrTailSize

/-- Pinned `Result<PolyEncoder, PolynomialError>` at `a` (`400` bytes = `0x190`, align `8`,
    returned by `PolyEncoder::from_pb`). -/
def resultPolyEncoderFromPbPinnedAt (A : RustAlloc) (g : PolyEncoderGhost) (a : BitVec 64) :
    Except PolynomialError PolyEncoder → SepProp
  | .ok enc => polyEncoderPinnedAt A g a enc
  | .error err =>
    (a ↦₆₄ polyEncoderNicheTag) ∗
      ((a + resultPolyEncoderErrByteOff) ↦₈ polynomialErrorByte err) ∗
      memRegion (a + 9#64) resultPolyEncoderErrTailSize

/-- Unpinned `Result<PolyEncoder, PolynomialError>` at `a` (`400` bytes = `0x190`, align `8`). -/
def resultPolyEncoderFromPbAt (A : RustAlloc) (a : BitVec 64) :
    Except PolynomialError PolyEncoder → SepProp
  | .ok enc => polyEncoderAt A a enc
  | .error err =>
    (a ↦₆₄ polyEncoderNicheTag) ∗
      ((a + resultPolyEncoderErrByteOff) ↦₈ polynomialErrorByte err) ∗
      memRegion (a + 9#64) resultPolyEncoderErrTailSize

/-! ## 5. `PolyDecoder` (`400` bytes = `0x190`, align `8`), `Option<PolyDecoder>`, and `Result<PolyDecoder, _>` -/

/-- Byte size of `spqr::encoding::polynomial::PolyDecoder` (`400` bytes = `0x190`). -/
def polyDecoderSize : Nat := 400

def polyDecoderSizeBV : BitVec 64 := 0x190#64

/-- Byte alignment of `PolyDecoder` (`8` bytes). -/
def polyDecoderAlign : BitVec 64 := 8#64

/-- Offset of `pts: [SortedSet<Pt>; 16]` (`384` bytes = `0x180`) within `PolyDecoder` (`+0x00`).
    Note: `pts[0].cap` at `+0x00` is the niche word (`noneCap = 0xFFFFFFFFFFFFFFFF#64`) for
    `Option<PolyDecoder>` and `Result<PolyDecoder, _>`. -/
def polyDecoderPtsOff : BitVec 64 := 0x00#64

/-- Byte size of `pts: [SortedSet<Pt>; 16]` (`384` bytes = `0x180`). -/
def polyDecoderPtsSize : Nat := 384

/-- Offset of `pts_needed: usize` (`8` bytes) within `PolyDecoder` (`+0x180`). -/
def polyDecoderPtsNeededOff : BitVec 64 := 0x180#64

/-- Offset of `is_complete: bool` (`1` byte: `0#8` or `1#8`) within `PolyDecoder` (`+0x188`). -/
def polyDecoderIsCompleteOff : BitVec 64 := 0x188#64

/-- Offset of the 7-byte trailing padding within `PolyDecoder` (`+0x189`). -/
def polyDecoderPadOff : BitVec 64 := 0x189#64

def polyDecoderPadSize : Nat := 7

/-- Offset of the error discriminant byte within `Result<PolyDecoder, _>::Err` (`+0x08`). -/
def resultPolyDecoderErrByteOff : BitVec 64 := 0x08#64

/-- Uninitialized tail byte count after `+0x08` in `Option<PolyDecoder>::None` (`392` bytes). -/
def optPolyDecoderNoneTailSize : Nat := 392

/-- Uninitialized tail byte count after `+0x09` in `Result<PolyDecoder, _>::Err` (`391` bytes). -/
def resultPolyDecoderErrTailSize : Nat := 391

/-- Pinned array of `SortedSet<Pt>` headers at `base` with stride `24` bytes. -/
def sortedSetPtListPinAt (A : RustAlloc) : BitVec 64 → List VecPin → List SortedSetPt → SepProp
  | _, _, [] => emp
  | _, [], _ :: _ => ⌜False⌝
  | base, pin :: pins, s :: ss =>
    sortedSetPtPinAt A pin s base ∗ sortedSetPtListPinAt A (base + 24#64) pins ss

/-- Unpinned array of `SortedSet<Pt>` headers at `base` with stride `24` bytes. -/
def sortedSetPtListOf (A : RustAlloc) : BitVec 64 → List SortedSetPt → SepProp :=
  arrayAt (fun s addr => sortedSetPtOf A addr s) vecHeaderBytes

/-- Ghost pins for the 16 `SortedSet<Pt>` fields of a `PolyDecoder`. -/
structure PolyDecoderGhost where
  /-- The 16 `(cap, ptr)` pins for `pts: [SortedSet<Pt>; 16]`. -/
  pins : List VecPin

/-- Encode `Bool` as the 1-byte Rust `bool` (`0#8` for `false`, `1#8` for `true`). -/
def boolByte (b : Bool) : BitVec 8 :=
  if b then 1#8 else 0#8

/-- Pinned `spqr::encoding::polynomial::PolyDecoder` at `a` (`400` bytes = `0x190`, align `8`):
    * `a + 0x00..0x180`: `pts: [SortedSet<Pt>; 16]` (16 `Vec<Pt>` headers of 24 bytes each)
    * `a + 0x180..0x188`: `pts_needed: usize` (`BitVec.ofNat 64 dec.ptsNeeded`)
    * `a + 0x188..0x189`: `is_complete: bool` (`boolByte dec.isComplete`)
    * `a + 0x189..0x190`: 7 bytes trailing padding (`memRegion (a + 0x189#64) 7`) -/
def polyDecoderPinnedAt (A : RustAlloc) (g : PolyDecoderGhost) (a : BitVec 64)
    (dec : PolyDecoder) : SepProp :=
  ⌜dec.pts.length = NUM_POLYS ∧ g.pins.length = NUM_POLYS ∧ dec.ptsNeeded < 2 ^ 64⌝ ∗
    sortedSetPtListPinAt A a g.pins dec.pts ∗
    ((a + polyDecoderPtsNeededOff) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
    ((a + polyDecoderIsCompleteOff) ↦₈ boolByte dec.isComplete) ∗
    memRegion (a + polyDecoderPadOff) polyDecoderPadSize

/-- Unpinned `spqr::encoding::polynomial::PolyDecoder` at `a` (`400` bytes = `0x190`, align `8`). -/
def polyDecoderAt (A : RustAlloc) (a : BitVec 64) (dec : PolyDecoder) : SepProp :=
  ⌜dec.pts.length = NUM_POLYS ∧ dec.ptsNeeded < 2 ^ 64⌝ ∗
    sortedSetPtListOf A a dec.pts ∗
    ((a + polyDecoderPtsNeededOff) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
    ((a + polyDecoderIsCompleteOff) ↦₈ boolByte dec.isComplete) ∗
    memRegion (a + polyDecoderPadOff) polyDecoderPadSize

/-- Pinned `Option<PolyDecoder>` at `a` (`400` bytes = `0x190`, align `8`):
    * `none`: `(a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 392` (`pts[0].cap = usize::MAX` niche)
    * `some dec`: `polyDecoderPinnedAt A g a dec` -/
def optPolyDecoderPinnedAt (A : RustAlloc) (g : PolyDecoderGhost) (a : BitVec 64) :
    Option PolyDecoder → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) optPolyDecoderNoneTailSize
  | some dec => polyDecoderPinnedAt A g a dec

/-- Unpinned `Option<PolyDecoder>` at `a` (`400` bytes = `0x190`, align `8`). -/
def optPolyDecoderAt (A : RustAlloc) (a : BitVec 64) : Option PolyDecoder → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) optPolyDecoderNoneTailSize
  | some dec => polyDecoderAt A a dec

/-- Pinned `Result<PolyDecoder, EncodingError>` at `a` (`400` bytes = `0x190`, align `8`):
    * `.ok dec`: `polyDecoderPinnedAt A g a dec`
    * `.error err`: `(a ↦₆₄ noneCap) ∗ ((a + 8#64) ↦₈ encodingErrorByte err) ∗ memRegion (a + 9#64) 391` -/
def resultPolyDecoderPinnedAt (A : RustAlloc) (g : PolyDecoderGhost) (a : BitVec 64) :
    Except EncodingError PolyDecoder → SepProp
  | .ok dec => polyDecoderPinnedAt A g a dec
  | .error err =>
    (a ↦₆₄ noneCap) ∗
      ((a + resultPolyDecoderErrByteOff) ↦₈ encodingErrorByte err) ∗
      memRegion (a + 9#64) resultPolyDecoderErrTailSize

/-- Unpinned `Result<PolyDecoder, EncodingError>` at `a` (`400` bytes = `0x190`, align `8`). -/
def resultPolyDecoderAt (A : RustAlloc) (a : BitVec 64) :
    Except EncodingError PolyDecoder → SepProp
  | .ok dec => polyDecoderAt A a dec
  | .error err =>
    (a ↦₆₄ noneCap) ∗
      ((a + resultPolyDecoderErrByteOff) ↦₈ encodingErrorByte err) ∗
      memRegion (a + 9#64) resultPolyDecoderErrTailSize

/-- Pinned `Result<PolyDecoder, PolynomialError>` at `a` (`400` bytes = `0x190`, align `8`,
    returned by `PolyDecoder::from_pb`). -/
def resultPolyDecoderFromPbPinnedAt (A : RustAlloc) (g : PolyDecoderGhost) (a : BitVec 64) :
    Except PolynomialError PolyDecoder → SepProp
  | .ok dec => polyDecoderPinnedAt A g a dec
  | .error err =>
    (a ↦₆₄ noneCap) ∗
      ((a + resultPolyDecoderErrByteOff) ↦₈ polynomialErrorByte err) ∗
      memRegion (a + 9#64) resultPolyDecoderErrTailSize

/-- Unpinned `Result<PolyDecoder, PolynomialError>` at `a` (`400` bytes = `0x190`, align `8`). -/
def resultPolyDecoderFromPbAt (A : RustAlloc) (a : BitVec 64) :
    Except PolynomialError PolyDecoder → SepProp
  | .ok dec => polyDecoderAt A a dec
  | .error err =>
    (a ↦₆₄ noneCap) ∗
      ((a + resultPolyDecoderErrByteOff) ↦₈ polynomialErrorByte err) ∗
      memRegion (a + 9#64) resultPolyDecoderErrTailSize

/-! ## 6. `ProtoPolynomialEncoder` (`56` bytes = `0x38`, align `8`) and `Option<ProtoPolynomialEncoder>` -/

/-- Byte size of `spqr::proto::pq_ratchet::PolynomialEncoder` (`56` bytes = `0x38`). -/
def protoPolynomialEncoderSize : Nat := 56

def protoPolynomialEncoderSizeBV : BitVec 64 := 0x38#64

/-- Byte alignment of `ProtoPolynomialEncoder` (`8` bytes). -/
def protoPolynomialEncoderAlign : BitVec 64 := 8#64

/-- Offset of `pts: Vec<Vec<u8>>` (tag 2, 24 bytes) within `ProtoPolynomialEncoder` (`+0x00`).
    Also `pts.cap` at `+0x00` is the `noneCap` niche word for `Option<ProtoPolynomialEncoder>`. -/
def protoPolynomialEncoderPtsOff : BitVec 64 := 0x00#64

/-- Offset of `polys: Vec<Vec<u8>>` (tag 3, 24 bytes) within `ProtoPolynomialEncoder` (`+0x18`). -/
def protoPolynomialEncoderPolysOff : BitVec 64 := 0x18#64

/-- Offset of `idx: u32` (tag 1, 4 bytes) within `ProtoPolynomialEncoder` (`+0x30`). -/
def protoPolynomialEncoderIdxOff : BitVec 64 := 0x30#64

/-- Offset of the 4-byte trailing padding within `ProtoPolynomialEncoder` (`+0x34`). -/
def protoPolynomialEncoderPadOff : BitVec 64 := 0x34#64

def protoPolynomialEncoderPadSize : Nat := 4

/-- Uninitialized tail byte count after `+0x08` in `Option<ProtoPolynomialEncoder>::None` (`48` bytes). -/
def optProtoPolynomialEncoderNoneTailSize : Nat := 48

/-- Pinned `Vec<Vec<u8>>` at `v` (24-byte header `{cap, ptr, len}`, element stride `24`, align `8`). -/
def vecVecU8PinnedAt (A : RustAlloc) (pin : VecPin) (v : BitVec 64)
    (bss : List (List (BitVec 8))) : SepProp :=
  vecAt A vecHeaderBytes 8 (fun bs addr => vecU8 A addr bs) v pin.cap pin.ptr bss

/-- Unpinned `Vec<Vec<u8>>` at `v` (24-byte header `{cap, ptr, len}`, element stride `24`, align `8`). -/
def vecVecU8At (A : RustAlloc) (v : BitVec 64) (bss : List (List (BitVec 8))) : SepProp :=
  vecOf A vecHeaderBytes 8 (fun bs addr => vecU8 A addr bs) v bss

/-- Ghost `(cap, ptr)` pins for the top-level `pts` and `polys` `Vec<Vec<u8>>` fields of a
    `ProtoPolynomialEncoder` (`56` bytes). -/
structure ProtoPolynomialEncoderGhost where
  /-- Pin for `pts: Vec<Vec<u8>>` at `+0x00` (tag 2). -/
  pts : VecPin
  /-- Pin for `polys: Vec<Vec<u8>>` at `+0x18` (tag 3). -/
  polys : VecPin

/-- Pinned `spqr::proto::pq_ratchet::PolynomialEncoder` at `a` (`56` bytes = `0x38`, align `8`):
    * `a + 0x00..0x18`: `pts: Vec<Vec<u8>>` (tag 2, 24B)
    * `a + 0x18..0x30`: `polys: Vec<Vec<u8>>` (tag 3, 24B)
    * `a + 0x30..0x34`: `idx: u32` (tag 1, 4B)
    * `a + 0x34..0x38`: 4 bytes trailing padding (`memRegion (a + 0x34#64) 4`) -/
def protoPolynomialEncoderPinnedAt (A : RustAlloc) (g : ProtoPolynomialEncoderGhost)
    (a : BitVec 64) (pb : ProtoPolynomialEncoder) : SepProp :=
  vecVecU8PinnedAt A g.pts a pb.pts ∗
    vecVecU8PinnedAt A g.polys (a + protoPolynomialEncoderPolysOff) pb.polys ∗
    ((a + protoPolynomialEncoderIdxOff) ↦₃₂ pb.idx) ∗
    memRegion (a + protoPolynomialEncoderPadOff) protoPolynomialEncoderPadSize

/-- Unpinned `spqr::proto::pq_ratchet::PolynomialEncoder` at `a` (`56` bytes = `0x38`, align `8`). -/
def protoPolynomialEncoderAt (A : RustAlloc) (a : BitVec 64)
    (pb : ProtoPolynomialEncoder) : SepProp :=
  vecVecU8At A a pb.pts ∗
    vecVecU8At A (a + protoPolynomialEncoderPolysOff) pb.polys ∗
    ((a + protoPolynomialEncoderIdxOff) ↦₃₂ pb.idx) ∗
    memRegion (a + protoPolynomialEncoderPadOff) protoPolynomialEncoderPadSize

/-- Pinned `Option<spqr::proto::pq_ratchet::PolynomialEncoder>` at `a` (`56` bytes = `0x38`, align `8`):
    * `none`: `(a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 48` (`pts.cap = usize::MAX` niche)
    * `some pb`: `protoPolynomialEncoderPinnedAt A g a pb` -/
def optProtoPolynomialEncoderPinnedAt (A : RustAlloc) (g : ProtoPolynomialEncoderGhost)
    (a : BitVec 64) : Option ProtoPolynomialEncoder → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) optProtoPolynomialEncoderNoneTailSize
  | some pb => protoPolynomialEncoderPinnedAt A g a pb

/-- Unpinned `Option<spqr::proto::pq_ratchet::PolynomialEncoder>` at `a` (`56` bytes = `0x38`, align `8`). -/
def optProtoPolynomialEncoderAt (A : RustAlloc) (a : BitVec 64) :
    Option ProtoPolynomialEncoder → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) optProtoPolynomialEncoderNoneTailSize
  | some pb => protoPolynomialEncoderAt A a pb

/-! ## 7. `ProtoPolynomialDecoder` (`40` bytes = `0x28`, align `8`) and `Option<ProtoPolynomialDecoder>` -/

/-- Byte size of `spqr::proto::pq_ratchet::PolynomialDecoder` (`40` bytes = `0x28`). -/
def protoPolynomialDecoderSize : Nat := 40

def protoPolynomialDecoderSizeBV : BitVec 64 := 0x28#64

/-- Byte alignment of `ProtoPolynomialDecoder` (`8` bytes). -/
def protoPolynomialDecoderAlign : BitVec 64 := 8#64

/-- Offset of `pts: Vec<Vec<u8>>` (tag 2, 24 bytes) within `ProtoPolynomialDecoder` (`+0x00`).
    Also `pts.cap` at `+0x00` is the `noneCap` niche word for `Option<ProtoPolynomialDecoder>`. -/
def protoPolynomialDecoderPtsOff : BitVec 64 := 0x00#64

/-- Offset of `pts_needed: u32` (tag 1, 4 bytes) within `ProtoPolynomialDecoder` (`+0x18`). -/
def protoPolynomialDecoderPtsNeededOff : BitVec 64 := 0x18#64

/-- Offset of `polys: u32` (tag 3, 4 bytes) within `ProtoPolynomialDecoder` (`+0x1c`). -/
def protoPolynomialDecoderPolysOff : BitVec 64 := 0x1c#64

/-- Offset of `is_complete: bool` (tag 4, 1 byte) within `ProtoPolynomialDecoder` (`+0x20`). -/
def protoPolynomialDecoderIsCompleteOff : BitVec 64 := 0x20#64

/-- Offset of the 7-byte trailing padding within `ProtoPolynomialDecoder` (`+0x21`). -/
def protoPolynomialDecoderPadOff : BitVec 64 := 0x21#64

def protoPolynomialDecoderPadSize : Nat := 7

/-- Uninitialized tail byte count after `+0x08` in `Option<ProtoPolynomialDecoder>::None` (`32` bytes). -/
def optProtoPolynomialDecoderNoneTailSize : Nat := 32

/-- Ghost `(cap, ptr)` pin for the `pts: Vec<Vec<u8>>` field of a `ProtoPolynomialDecoder` (`40` bytes). -/
structure ProtoPolynomialDecoderGhost where
  /-- Pin for `pts: Vec<Vec<u8>>` at `+0x00` (tag 2). -/
  pts : VecPin

/-- Pinned `spqr::proto::pq_ratchet::PolynomialDecoder` at `a` (`40` bytes = `0x28`, align `8`):
    * `a + 0x00..0x18`: `pts: Vec<Vec<u8>>` (tag 2, 24B)
    * `a + 0x18..0x1c`: `pts_needed: u32` (tag 1, 4B)
    * `a + 0x1c..0x20`: `polys: u32` (tag 3, 4B)
    * `a + 0x20..0x21`: `is_complete: bool` (tag 4, 1B)
    * `a + 0x21..0x28`: 7 bytes trailing padding (`memRegion (a + 0x21#64) 7`) -/
def protoPolynomialDecoderPinnedAt (A : RustAlloc) (g : ProtoPolynomialDecoderGhost)
    (a : BitVec 64) (pb : ProtoPolynomialDecoder) : SepProp :=
  vecVecU8PinnedAt A g.pts a pb.pts ∗
    ((a + protoPolynomialDecoderPtsNeededOff) ↦₃₂ pb.ptsNeeded) ∗
    ((a + protoPolynomialDecoderPolysOff) ↦₃₂ pb.polys) ∗
    ((a + protoPolynomialDecoderIsCompleteOff) ↦₈ boolByte pb.isComplete) ∗
    memRegion (a + protoPolynomialDecoderPadOff) protoPolynomialDecoderPadSize

/-- Unpinned `spqr::proto::pq_ratchet::PolynomialDecoder` at `a` (`40` bytes = `0x28`, align `8`). -/
def protoPolynomialDecoderAt (A : RustAlloc) (a : BitVec 64)
    (pb : ProtoPolynomialDecoder) : SepProp :=
  vecVecU8At A a pb.pts ∗
    ((a + protoPolynomialDecoderPtsNeededOff) ↦₃₂ pb.ptsNeeded) ∗
    ((a + protoPolynomialDecoderPolysOff) ↦₃₂ pb.polys) ∗
    ((a + protoPolynomialDecoderIsCompleteOff) ↦₈ boolByte pb.isComplete) ∗
    memRegion (a + protoPolynomialDecoderPadOff) protoPolynomialDecoderPadSize

/-- Pinned `Option<spqr::proto::pq_ratchet::PolynomialDecoder>` at `a` (`40` bytes = `0x28`, align `8`):
    * `none`: `(a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 32` (`pts.cap = usize::MAX` niche)
    * `some pb`: `protoPolynomialDecoderPinnedAt A g a pb` -/
def optProtoPolynomialDecoderPinnedAt (A : RustAlloc) (g : ProtoPolynomialDecoderGhost)
    (a : BitVec 64) : Option ProtoPolynomialDecoder → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) optProtoPolynomialDecoderNoneTailSize
  | some pb => protoPolynomialDecoderPinnedAt A g a pb

/-- Unpinned `Option<spqr::proto::pq_ratchet::PolynomialDecoder>` at `a` (`40` bytes = `0x28`, align `8`). -/
def optProtoPolynomialDecoderAt (A : RustAlloc) (a : BitVec 64) :
    Option ProtoPolynomialDecoder → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) optProtoPolynomialDecoderNoneTailSize
  | some pb => protoPolynomialDecoderAt A a pb

end CryptoVerification.SpqrV1.Poly
