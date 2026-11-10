/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefs
public import LibsignalBinary.Proofs.TripleRatchet.Prost.ProstCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.Keys.Defs

/-!
# `contractProg` (`externStack = 16384`) Prost Decoding Leaf Specifications

Defines the `contractProg b ext` and `[LibsignalPlacement]` contracts for the `prost` decoding
leaves (`drop_glue::<DecodeError>`, `decode_varint_slice`, `int32::merge`, `skip_field`,
`bytes::merge`, and `DecodeError::from` / `push` hooks) with stack budgets augmented by
`externStack = 16384` and slice-length bounds weakened to `< 2 ^ 63` (`< 2 ^ 62` for `bytes::merge`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.LibsignalTripleRatchet.Prost.X
open CryptoVerification.LibsignalTripleRatchet.Prost

open Arm64 ProofLib CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec

theorem L1_DefsW : True := trivial

/-! ## Stack budgets (`+ externStack`) -/

/-- `DecodeError::from` / `push` budget with X externs (`decodeErrorHookStack + 16384`). -/
abbrev decodeErrorHookStackW : Nat := decodeErrorHookStack + CryptoVerification.LibsignalTripleRatchet.extHookStack

/-- `decode_varint_slice` (`0x23008`) budget with X externs (`0x50 + decodeErrorHookStackW`). -/
abbrev decodeVarintSliceStackW : Nat := 0x50 + decodeErrorHookStackW

/-- `int32::merge` (`0x2bc4`) budget with X externs (`0x50 + decodeVarintSliceStackW`). -/
abbrev int32MergeStackW : Nat := 0x50 + decodeVarintSliceStackW

/-- `skip_field` (`0x1b34`) budget at recursion limit `depth` with X externs. -/
abbrev skipFieldStackW (depth : Nat) : Nat :=
  (depth + 1) * 0x60 + decodeVarintSliceStackW

/-- `bytes::merge` (`0x2788`) budget with X externs (`0xe0 + decodeVarintSliceStackW`). -/
abbrev bytesMergeStackW : Nat := 0xe0 + decodeVarintSliceStackW

/-- `drop_glue::<DecodeError>` (`0x242c`) budget with X externs (`dropDecodeErrorStack + 16384`). -/
abbrev dropDecodeErrorStackW : Nat := dropDecodeErrorStack + CryptoVerification.LibsignalTripleRatchet.extHookStack

theorem decodeVarintSliceStackX_eq : decodeVarintSliceStackW = decodeVarintSliceStack + 16384 := rfl

theorem int32MergeStackX_eq : int32MergeStackW = int32MergeStack + 16384 := rfl

theorem skipFieldStackX_eq (d : Nat) : skipFieldStackW d = skipFieldStack d + 16384 := by
  simp only [skipFieldStackW, skipFieldStack, decodeVarintSliceStackW, decodeVarintSliceStack,
    decodeErrorHookStackW, decodeErrorHookStack, CryptoVerification.LibsignalTripleRatchet.extHookStack]
  omega

theorem bytesMergeStackX_eq : bytesMergeStackW = bytesMergeStack + 16384 := rfl

theorem dropDecodeErrorStackX_eq : dropDecodeErrorStackW = dropDecodeErrorStack + 16384 := rfl

/-! ## `DecodeError::from` and `DecodeError::push` hooks -/

/-- `decodeErrorFromSpec` (frozen) at `decodeErrorHookStackW`. -/
def decodeErrorFromSpecX (A : RustAlloc) : Spec (BitVec 64 × BitVec 64) where
  pre := fun (k, w) s =>
    ⌜s.readReg64 .x0 = k ∧ KindNoHeap w⌝ ∗ (k ↦₆₄ w) ∗ memRegion (k + 8#64) 40 ∗
      A.pool ∗ stackAt s.sp decodeErrorHookStackW
  post := fun (k, _) s0 sf =>
    ⌜sf.readReg64 .x0 ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗ decodeErrorAtStackLen A (sf.readReg64 .x0) 0 ∗
      memRegion k 48 ∗ A.pool ∗ stackAt s0.sp decodeErrorHookStackW
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- `decodeErrorPushSpec` (frozen) at `decodeErrorHookStackW`. -/
def decodeErrorPushSpecX (A : RustAlloc) : Spec (BitVec 64 × BitVec 64 × Nat) where
  pre := fun (d, e, n) s =>
    ⌜s.readReg64 .x0 = d ∧ n < 2 ^ 32⌝ ∗ (d ↦₆₄ e) ∗ decodeErrorAtStackLen A e n ∗
      A.pool ∗ stackAt s.sp decodeErrorHookStackW
  post := fun (d, e, n) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (d ↦₆₄ e) ∗ decodeErrorAtStackLen A e (n + 1) ∗
      A.pool ∗ stackAt s0.sp decodeErrorHookStackW
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-! ## `drop_glue::<DecodeError>` (`0x242c`) -/

/-- `dropDecodeErrorSpec` at `dropDecodeErrorStackW` (no length bound involved). -/
def dropDecodeErrorSpecW (A : RustAlloc) : Spec (BitVec 64) where
  pre := fun e s =>
    ⌜s.readReg64 .x0 = e⌝ ∗ decodeErrorAt A e ∗ A.pool ∗ stackAt s.sp dropDecodeErrorStackW
  post := fun _ s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ A.pool ∗ stackAt s0.sp dropDecodeErrorStackW

/-! ## `decode_varint_slice` (`0x23008`) -/

/-- `decodeVarintSliceSpec` with `x.bs.length < 2 ^ 63` at `decodeVarintSliceStackW`. -/
def decodeVarintSliceSpecW (A : RustAlloc) : Spec DecodeVarintSliceGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.ptr ∧
      (s.readReg64 .x2).toNat = x.bs.length ∧ x.bs.length < 2 ^ 63 ∧ VarintSlicePre x.bs⌝ ∗
      memRegion x.ret 24 ∗ (x.ptr ↦ₛ x.bs) ∗ A.pool ∗ stackAt s.sp decodeVarintSliceStackW
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ varintSliceResultAt A x.ret x.bs (decodeVarint x.bs) ∗
      (x.ptr ↦ₛ x.bs) ∗ A.pool ∗ stackAt s0.sp decodeVarintSliceStackW
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-! ## `int32::merge::<&mut &[u8]>` (`0x2bc4`) -/

/-- `int32MergeSpec` with `x.bs.length < 2 ^ 63` at `int32MergeStackW`. -/
def int32MergeSpecW (A : RustAlloc) : Spec Int32MergeGhost where
  pre := fun x s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.valPtr ∧ s.readReg64 .x2 = x.bufRef ∧ x.bs.length < 2 ^ 63⌝ ∗
      memRegion x.valPtr 4 ∗ (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool ∗ stackAt s.sp int32MergeStackW
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗ A.pool ∗ stackAt s0.sp int32MergeStackW ∗
      match mergeUint32 x.wt x.bs with
      | some (v, rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗ (x.valPtr ↦₃₂ v) ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗ decodeErrorAtStackLen A (sf.readReg64 .x0) 0 ∗
          memRegion x.valPtr 4 ∗ memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-! ## `skip_field::<&mut &[u8]> [local#1]` (`0x1b34`) -/

/-- `skipFieldSpec` with `x.bs.length < 2 ^ 63` at `skipFieldStackW x.depth`; the tag / depth
`< 2 ^ 32` value hypotheses are unchanged. -/
def skipFieldSpecW (A : RustAlloc) : Spec SkipFieldGhost where
  pre := fun x s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      (s.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 x.tag ∧ x.tag < 2 ^ 32 ∧
      s.readReg64 .x2 = x.bufRef ∧
      (s.readReg64 .x3).setWidth 32 = BitVec.ofNat 32 x.depth ∧ x.depth < 2 ^ 32 ∧
      x.bs.length < 2 ^ 63⌝ ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool ∗ stackAt s.sp (skipFieldStackW x.depth)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗ A.pool ∗
      stackAt s0.sp (skipFieldStackW x.depth) ∗
      match skipField (2 * x.bs.length + 2) x.depth x.tag x.wt x.bs with
      | some rest =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗ sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗ decodeErrorAtStackLen A (sf.readReg64 .x0) 0 ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-! ## `bytes::merge::<Vec<u8>, &mut &[u8]> [local#1]` (`0x2788`) -/

/-- `bytesMergeRawSpec` with `x.bs.length < 2 ^ 62` at `bytesMergeStackW`.

The bound is `2 ^ 62` (not `2 ^ 63`): `bytes::merge` does `Vec::clear` + `reserve(len)`, and the
amortized growth `max (len, 2 * cap, 8)` of `do_reserve_and_handle` only stays `< 2 ^ 63` (no
capacity-overflow panic) when `cap < len < 2 ^ 62`. -/
def bytesMergeRawSpecW (A : RustAlloc) : Spec BytesMergeGhost where
  pre := fun x s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.valPtr ∧ s.readReg64 .x2 = x.bufRef ∧ x.bs.length < 2 ^ 62⌝ ∗
      vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool ∗ stackAt s.sp bytesMergeStackW
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗ A.pool ∗ stackAt s0.sp bytesMergeStackW ∗
      match mergeBytes x.wt x.bs with
      | some (v, rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗
          (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64, vecU8At A x.valPtr cap' ptr' v) ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗ decodeErrorAtStackLen A (sf.readReg64 .x0) 0 ∗
          vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- `bytesMergeRawSpecW A` in a loaded image `img`. -/
def bytesMergeSpecW (A : RustAlloc) (img : Obj.Image) : Spec BytesMergeGhost :=
  (bytesMergeRawSpecW A).inImage img

/-! ## `subroutine_ok` obligations on `contractProg img.base ext` -/

/-- `drop_glue::<DecodeError>` meets `dropDecodeErrorSpecW` on `contractProg img.base ext`. -/
def DropDecodeErrorOkW (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (contractProg img.base ext)
    ((contractProg img.base ext).fnAddr dropDecodeErrorName) ((dropDecodeErrorSpecW A).inImage img)

/-- `decode_varint_slice` meets `decodeVarintSliceSpecW` on `contractProg img.base ext`. -/
def DecodeVarintSliceOkW (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (contractProg img.base ext)
    ((contractProg img.base ext).fnAddr decodeVarintSliceName)
    ((decodeVarintSliceSpecW A).inImage img)

/-- `int32::merge` meets `int32MergeSpecW` on `contractProg img.base ext`. -/
def Int32MergeOkW (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (contractProg img.base ext)
    ((contractProg img.base ext).fnAddr int32MergeName) ((int32MergeSpecW A).inImage img)

/-- `skip_field` meets `skipFieldSpecW` on `contractProg img.base ext`. -/
def SkipFieldOkW (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (contractProg img.base ext)
    ((contractProg img.base ext).fnAddr skipFieldName) ((skipFieldSpecW A).inImage img)

/-- `bytes::merge` meets `bytesMergeSpecW A img` on `contractProg img.base ext`. -/
def BytesMergeOkW (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (contractProg img.base ext)
    ((contractProg img.base ext).fnAddr bytesMergeName) (bytesMergeSpecW A img)

/-! ## Relocatable `[LibsignalPlacement]` specifications -/

section Placed

open CryptoVerification

/-- `bytesMergeRawSpecW A` under `LibsignalCodeRoLoaded lsmpl`. -/
def bytesMergePlacedSpecW [LibsignalPlacement] (A : RustAlloc) : Spec BytesMergeGhost :=
  CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (bytesMergeRawSpecW A)

/-- `drop_glue::<DecodeError>` (Block `5`) meets `dropDecodeErrorSpecW` under `[LibsignalPlacement]`. -/
def DropDecodeErrorPlacedOkW [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop :=
  subroutine_ok ((blkPC_4).rebase (blkPl_4).base H)
    (blkPl_4).base (withLsCodeLoaded lsmpl (dropDecodeErrorSpecW A))

/-- `decode_varint_slice` (Block `76`) meets `decodeVarintSliceSpecW` under `[LibsignalPlacement]`. -/
def DecodeVarintSlicePlacedOkW [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop :=
  subroutine_ok ((blkPC_76).rebase (blkPl_76).base H)
    (blkPl_76).base (withLsCodeLoaded lsmpl (decodeVarintSliceSpecW A))

/-- `int32::merge` (Block `8`) meets `int32MergeSpecW` under `[LibsignalPlacement]`. -/
def Int32MergePlacedOkW [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop :=
  subroutine_ok ((blkPC_8).rebase (blkPl_8).base H)
    (blkPl_8).base (withLsCodeLoaded lsmpl (int32MergeSpecW A))

/-- `skip_field` (Block `1`) meets `skipFieldSpecW` under `[LibsignalPlacement]`. -/
def SkipFieldPlacedOkW [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop :=
  subroutine_ok ((blkPC_1).rebase (blkPl_1).base H)
    (blkPl_1).base (withLsCodeLoaded lsmpl (skipFieldSpecW A))

/-- `bytes::merge` (Block `7`) meets `bytesMergePlacedSpecW` under `[LibsignalPlacement]`. -/
def BytesMergePlacedOkW [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop :=
  subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
    (blkPl_7).base (bytesMergePlacedSpecW A)

end Placed

end CryptoVerification.LibsignalTripleRatchet.Prost.X
