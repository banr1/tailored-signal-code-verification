/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Hooks2
public import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.PolyPart1CodeSym
public import LibsignalBinary.Proofs.SpqrV1.Drop.Poly
import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym -- shake: keep

/-!
# `<spqr::encoding::polynomial::PolyDecoder>::into_pb`: Definitions and Specifications

**Checked by Lean.**

Separation-logic specifications (`decoderIntoPbSpec`, `decoderIntoPbSpecX`) for
`<PolyDecoder>::into_pb` (`0x63030`, Block `377`), consuming `PolyDecoder` via
`drop_glue::<[SortedSet<Pt>; 16]>` and writing `ProtoPolynomialDecoder` at `x0`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Poly.DecoderPb

open Arm64 ProofLib
open CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Drop
export CryptoVerification.SpqrV1.Alloc (spqrHandleErrorSym spqrRustNoAllocShimSym spqrRustAllocSym spqrMemcpySym spqrMemmoveSym)

abbrev spqrRustDeallocSym : String := "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"

/-! ## Symbol Names and Stack Budgets -/

abbrev dropGlueSortedSetPt16Name : String := Drop.dropSortedSetPt16Name

abbrev decoderIntoPbName : String :=
  "<spqr::encoding::polynomial::PolyDecoder>::into_pb"

/-- Stack budget of `<PolyDecoder>::into_pb` (`0xa0 = 160` B own frame + `dropGluePoly16Stack` = `192 + allocHookStack`). -/
abbrev decoderIntoPbStack : Nat := 160 + dropGluePoly16Stack

/-- Extended-stack budget of `<PolyDecoder>::into_pb` (`160 + extHookStack`). -/
abbrev decoderIntoPbStackX : Nat := 160 + extHookStack

/-! ## Specification of `<spqr::encoding::polynomial::PolyDecoder>::into_pb` (`0x63030`) -/

/-- Ghost arguments of `<PolyDecoder>::into_pb` (`0x63030`). -/
structure DecoderIntoPbGhost where
  /-- Sret pointer (`x0`, 40-byte `ProtoPolynomialDecoder` output). -/
  out : BitVec 64
  /-- Pointer to the 400-byte `PolyDecoder` moved by value (`x1`). -/
  decA : BitVec 64
  /-- Logical `PolyDecoder` value at `decA`. -/
  dec : PolyDecoder

/-- Specification of `<PolyDecoder>::into_pb` (`0x63030`): consumes `polyDecoderAt A decA dec` at `x1` into `memRegion decA 400` and writes `protoPolynomialDecoderAt A out dec.intoPb` to `x0 = out` (or panics on OOM). -/
def decoderIntoPbSpec (A : RustAlloc) : Spec DecoderIntoPbGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.decA⌝ ∗
      memRegion x.out protoPolynomialDecoderSize ∗
      polyDecoderAt A x.decA x.dec ∗
      A.pool ∗ stackAt s.sp decoderIntoPbStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      protoPolynomialDecoderAt A x.out x.dec.intoPb ∗
      memRegion x.decA polyDecoderSize ∗
      A.pool ∗ stackAt s0.sp decoderIntoPbStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Extended-stack variant of `decoderIntoPbSpec` (`decoderIntoPbStackX = 160 + extHookStack`). -/
def decoderIntoPbSpecX (A : RustAlloc) : Spec DecoderIntoPbGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.decA⌝ ∗
      memRegion x.out protoPolynomialDecoderSize ∗
      polyDecoderAt A x.decA x.dec ∗
      A.pool ∗ stackAt s.sp decoderIntoPbStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      protoPolynomialDecoderAt A x.out x.dec.intoPb ∗
      memRegion x.decA polyDecoderSize ∗
      A.pool ∗ stackAt s0.sp decoderIntoPbStackX
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def DecoderIntoPbOkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr decoderIntoPbName)
    (decoderIntoPbSpec A)

def DecoderIntoPbOkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr decoderIntoPbName)
    ((decoderIntoPbSpecX A).inImage img)

def DecoderIntoPbPlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_377).rebase (blkPl_377).base (Rust.withPanics ext))
    (blkPl_377).base
    (decoderIntoPbSpec A)

def DecoderIntoPbPlacedOkX [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_377).rebase (blkPl_377).base (Rust.withPanics ext))
    (blkPl_377).base
    (decoderIntoPbSpecX A)

end CryptoVerification.SpqrV1.Poly.DecoderPb

