/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Prost.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs

/-!
# Specification of `prost::encoding::bytes::merge::<Vec<u8>, &mut &[u8]>`

Relates `prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]` (`0x2788`) to
the pure protobuf codec model `mergeBytes`, tracking capacity monotonicity (`BytesMergeCapOk`) and
the two-level slice cursor `&mut &mut &[u8]`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Prost

open Arm64 ProofLib CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec

/-! ## Symbol name and stack budget -/

/-- `prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]`
(image offset `0x2788`, 271 instructions). -/
abbrev bytesMergeName : String :=
  "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]"

/-- Stack budget for `prost::encoding::bytes::merge::<Vec<u8>, &mut &[u8]> [local#1]`: `0xe0` local frame plus `decodeVarintSliceStack`. -/
abbrev bytesMergeStack : Nat := 0xe0 + decodeVarintSliceStack

/-! ## Ghost state and specification -/

/-- Ghost arguments of `prost::encoding::bytes::merge::<Vec<u8>, &mut &[u8]> [local#1]`. -/
structure BytesMergeGhost where
  /-- Wire type (`w0` low byte). -/
  wt : WireType
  /-- Destination `value: &mut Vec<u8>` header address (`x1`, 24 bytes). -/
  valPtr : BitVec 64
  /-- Initial capacity word of `*valPtr` (`[valPtr + 0x0]`). -/
  valCap : BitVec 64
  /-- Initial buffer pointer of `*valPtr` (`[valPtr + 0x8]`). -/
  valBuf : BitVec 64
  /-- Initial contents of `*valPtr` (`[valPtr + 0x10] = valBs.length`). -/
  valBs : List (BitVec 8)
  /-- Outer cursor reference `buf: &mut &mut &[u8]` (`x2`, 8 bytes holding `slot`). -/
  bufRef : BitVec 64
  /-- Slice header address (`*bufRef`, 16 bytes holding `(ptr, bs.length)`). -/
  slot : BitVec 64
  /-- Slice data pointer (`[slot + 0x0]`). -/
  ptr : BitVec 64
  /-- Remaining input bytes (`[slot + 0x8] = bs.length`). -/
  bs : List (BitVec 8)

/-- Capacity-vs-remaining-slice invariant for `prost::encoding::bytes::merge` on `< 2 ^ 63`-byte
slices: holds at `cap = 0` or whenever `bsLen < 2 ^ 32`, is monotone as `bs` shrinks, and ensures
`reserveCap cap.toNat 0 v.length < 2 ^ 63` whenever `cap.toNat < v.length`. -/
def BytesMergeCapOk (cap : BitVec 64) (bsLen : Nat) : Prop :=
  cap.toNat = 0 ∨
  (cap.toNat = 8 ∧ bsLen ≤ 2 ^ 63 - 3) ∨
  (cap.toNat = 16 ∧ bsLen ≤ 2 ^ 63 - 13) ∨
  (cap.toNat = 32 ∧ bsLen ≤ 2 ^ 63 - 31) ∨
  cap.toNat + bsLen < 2 ^ 63 ∨
  bsLen < 2 ^ 32

theorem bytesMergeCapOk_zero {n : Nat} : BytesMergeCapOk 0#64 n :=
  Or.inl rfl

/-- Any initial capacity satisfies `BytesMergeCapOk` when the input slice has length `< 2 ^ 32`. -/
theorem bytesMergeCapOk_of_len_lt32 {cap : BitVec 64} {n : Nat} (hn : n < 2 ^ 32) :
    BytesMergeCapOk cap n := by
  unfold BytesMergeCapOk; omega

theorem bytesMergeCapOk_of_lt32 {cap : BitVec 64} {n : Nat}
    (hcap : cap.toNat < 2 ^ 32) (hn : n < 2 ^ 32) :
    BytesMergeCapOk cap n := by
  exact (fun _ => bytesMergeCapOk_of_len_lt32 hn) hcap

theorem bytesMergeCapOk_mono {cap : BitVec 64} {n m : Nat}
    (h : BytesMergeCapOk cap n) (hle : m ≤ n) :
    BytesMergeCapOk cap m := by
  unfold BytesMergeCapOk at h ⊢; omega

theorem bytesMergeCapOk_reserveCap_bound {cap : BitVec 64} {vLen restLen bsLen : Nat}
    (h : BytesMergeCapOk cap bsLen) (hult : cap.toNat < vLen)
    (hsum : 1 + vLen + restLen ≤ bsLen) (hbs : bsLen < 2 ^ 63) :
    reserveCap cap.toNat 0 vLen ≤ 9223372036854775807 := by
  unfold BytesMergeCapOk at h
  dsimp [reserveCap]
  omega

theorem bytesMergeCapOk_after_reserve {cap : BitVec 64} {vLen restLen bsLen : Nat}
    (h : BytesMergeCapOk cap bsLen) (hult : cap.toNat < vLen)
    (hsum : 1 + vLen + restLen ≤ bsLen) (hbs : bsLen < 2 ^ 63) :
    BytesMergeCapOk (BitVec.ofNat 64 (reserveCap cap.toNat 0 vLen)) restLen := by
  have hb := bytesMergeCapOk_reserveCap_bound h hult hsum hbs
  have htoNat : (BitVec.ofNat 64 (reserveCap cap.toNat 0 vLen)).toNat =
      reserveCap cap.toNat 0 vLen := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  unfold BytesMergeCapOk at h ⊢
  rw [htoNat]
  dsimp [reserveCap] at hb ⊢
  omega

/-- Raw contract of `prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]`
(image offset `0x2788`, 271 instructions; `prost-0.14.4/src/encoding.rs:670–724`). -/
def bytesMergeRawSpec (A : RustAlloc) : Spec BytesMergeGhost where
  pre := fun x s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.valPtr ∧ s.readReg64 .x2 = x.bufRef ∧ x.bs.length < 2 ^ 63 ∧
      BytesMergeCapOk x.valCap x.bs.length⌝ ∗
      vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool ∗ stackAt s.sp bytesMergeStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗ A.pool ∗ stackAt s0.sp bytesMergeStack ∗
      match mergeBytes x.wt x.bs with
      | some (v, rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗
          (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
            ⌜BytesMergeCapOk cap' rest.length⌝ ∗ vecU8At A x.valPtr cap' ptr' v) ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗ decodeErrorAtStackLen A (sf.readReg64 .x0) 0 ∗
          vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Specification of `prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]`
(`0x2788`) in a loaded image `img` (`Spec.inImage` supplies `.rodata` vtable access and `Bytes` callees). -/
def bytesMergeSpec (A : RustAlloc) (img : Obj.Image) : Spec BytesMergeGhost :=
  (bytesMergeRawSpec A).inImage img

/-! ## Target `subroutine_ok` proposition -/

/-- `prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]` meets
`bytesMergeSpec A img` on `tripleRatchetProgAt img.base`. -/
def BytesMergeOk (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
    ((tripleRatchetProgAt img.base C ctl abs).fnAddr bytesMergeName) (bytesMergeSpec A img)

/-! ## Extended-stack variant (`bytesMergeSpecX`) -/

/-- Stack budget for `prost::encoding::bytes::merge::<Vec<u8>, &mut &[u8]> [local#1]` with `decodeVarintSliceStackX`. -/
abbrev bytesMergeStackX : Nat := 0xe0 + decodeVarintSliceStackX

/-- Raw contract of `prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]`
with `bytesMergeStackX`. -/
def bytesMergeRawSpecX (A : RustAlloc) : Spec BytesMergeGhost where
  pre := fun x s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.valPtr ∧ s.readReg64 .x2 = x.bufRef ∧ x.bs.length < 2 ^ 63 ∧
      BytesMergeCapOk x.valCap x.bs.length⌝ ∗
      vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool ∗ stackAt s.sp bytesMergeStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗ A.pool ∗ stackAt s0.sp bytesMergeStackX ∗
      match mergeBytes x.wt x.bs with
      | some (v, rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗
          (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
            ⌜BytesMergeCapOk cap' rest.length⌝ ∗ vecU8At A x.valPtr cap' ptr' v) ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗ decodeErrorAtStackLen A (sf.readReg64 .x0) 0 ∗
          vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Contract of `prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]`
(`0x2788`) in a loaded image `img` with `bytesMergeStackX`. -/
def bytesMergeSpecX (A : RustAlloc) (img : Obj.Image) : Spec BytesMergeGhost :=
  (bytesMergeRawSpecX A).inImage img

end CryptoVerification.LibsignalTripleRatchet.Prost
