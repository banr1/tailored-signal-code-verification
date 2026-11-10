/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.GrowOneSpecs
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Hooks
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefs

/-!
# Intermediate Specification for `spqr::encode_varint` (`0x54040`, 164 insns)

Defines the separation-logic specification `spqrEncodeVarintSpecX` for `spqr::encode_varint`
(`0x54040`, 164 instructions) against the pure LEB128 varint encoder `encode_varint`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.EncodeVarint

open Arm64 ProofLib
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost

/-! ## Symbol Name & Stack Budget -/

/-- `spqr::encode_varint` (`0x54040`, 164 instructions). -/
abbrev spqrEncodeVarintName : String := "spqr::encode_varint"

/-- Stack budget for `spqr::encode_varint` (`0x54040`):
* own frame `0x50 = 80` bytes (`+0x000: stp x29, x30, [sp, #-0x50]!`);
* calls `<alloc::raw_vec::RawVec<u8>>::grow_one` (`0x78b98`), which uses `extHookStack` (`16384` bytes). -/
abbrev spqrEncodeVarintStackX : Nat := 0x50 + extHookStack

/-! ## Equivalence of `LibsignalSpqrV1.encode_varint` and `LibsignalProtoCodec.encodeVarint` -/

private theorem truncate8_and_7f_of_lt (a : BitVec 64) (h : a < 0x80#64) :
    (a &&& 0x7f#64).truncate 8 = a.setWidth 8 := by
  have h1 : a.ult 0x80#64 = true := by
    rw [BitVec.ult_eq_decide, decide_eq_true_eq]
    exact h
  bv_bits

private theorem or_80_truncate8_and_7f (a : BitVec 64) :
    0x80#8 ||| (a &&& 0x7f#64).truncate 8 = ((a &&& 0x7F#64) ||| 0x80#64).setWidth 8 := by
  bv_bits

/-- `LibsignalSpqrV1.encodeVarintLoop` is identical to `LibsignalProtoCodec.encodeVarintAux`. -/
theorem encodeVarintLoop_eq_encodeVarintAux (fuel : Nat) (a : BitVec 64) :
    encodeVarintLoop fuel a = CryptoVerification.LibsignalProtoCodec.encodeVarintAux fuel a := by
  induction fuel generalizing a with
  | zero => rfl
  | succ fuel ih =>
    simp only [encodeVarintLoop, CryptoVerification.LibsignalProtoCodec.encodeVarintAux]
    have hlt_iff : (a < 0x80#64) ↔ (a.toNat < 0x80) := BitVec.lt_def
    by_cases h : a < 0x80#64
    · have h' : a.toNat < 0x80 := hlt_iff.mp h
      simp only [h, h', ↓reduceIte, truncate8_and_7f_of_lt a h]
    · have h' : ¬ a.toNat < 0x80 := fun hc => h (hlt_iff.mpr hc)
      simp only [h, h', ↓reduceIte, or_80_truncate8_and_7f a, ih (a >>> 7)]
      rfl

/-- `LibsignalSpqrV1.encode_varint a into` equals `into ++ LibsignalProtoCodec.encodeVarint a`. -/
theorem spqr_encode_varint_eq (a : BitVec 64) (into : Bytes) :
    CryptoVerification.LibsignalSpqrV1.encode_varint a into =
      into ++ CryptoVerification.LibsignalProtoCodec.encodeVarint a := by
  simp only [CryptoVerification.LibsignalSpqrV1.encode_varint, MAX_VARINT_BYTES_LEN,
    CryptoVerification.LibsignalProtoCodec.encodeVarint,
    encodeVarintLoop_eq_encodeVarintAux]

/-! ## Callee Hypothesis & Specification of `spqr::encode_varint` (`0x54040`) -/

/-- `<alloc::raw_vec::RawVec<u8>>::grow_one` (`0x78b98`) meets `growOneU8Spec A` on
`tripleRatchetProgAtExt b ext`. -/
def GrowOneU8OkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr growOneU8Name)
    (growOneU8Spec A)

/-- Specification of `spqr::encode_varint` (`0x54040`, 164 instructions):
* `x0 = x.val` (`mut a: u64`), `x1 = x.v` (`into: &mut SerializedMessage = &mut Vec<u8>`).
* Appends the 1..10 LEB128 varint bytes of `x.val` (`encodeVarintLoop 10 x.val`) to `into`,
  yielding `vecU8At A x.v cap' ptr' (encode_varint x.val x.bs)`.
* Preserves `cap' = x.cap ∧ ptr' = x.ptr` whenever `x.bs.length + (encodeVarintLoop 10 x.val).length ≤ x.cap.toNat`,
  and never shrinks capacity (`x.cap.toNat ≤ cap'.toNat`).
* Panics only on OOM inside `<RawVec<u8>>::grow_one`. -/
def spqrEncodeVarintSpecX (A : RustAlloc) : Spec EncodeVarintGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.val ∧ s.readReg64 .x1 = x.v ∧
      (x.bs.length + 10 ≤ x.cap.toNat ∨ x.bs.length + 10 < 2 ^ 62)⌝ ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s.sp spqrEncodeVarintStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodeVarintLoop MAX_VARINT_BYTES_LEN x.val).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          vecU8At A x.v cap' ptr' (CryptoVerification.LibsignalSpqrV1.encode_varint x.val x.bs)) ∗
      A.pool ∗ stackAt s0.sp spqrEncodeVarintStackX
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- `spqr::encode_varint` (`0x54040`) meets `spqrEncodeVarintSpecX A` on
`tripleRatchetProgAtExt b ext`. -/
def SpqrEncodeVarintOkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr spqrEncodeVarintName)
    (spqrEncodeVarintSpecX A)

/-- `spqr::encode_varint` (`0x54040`) meets `(spqrEncodeVarintSpecX A).inImage img` on
`tripleRatchetProgAtExt img.base ext`. -/
def SpqrEncodeVarintOkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr spqrEncodeVarintName)
    ((spqrEncodeVarintSpecX A).inImage img)

abbrev EncodeVarintOkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  SpqrEncodeVarintOkX img A ext

end CryptoVerification.SpqrV1.Top.EncodeVarint
