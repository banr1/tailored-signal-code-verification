/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Prog
public import LibsignalBinary.Specifications.LibsignalTripleRatchetProst

/-!
# Specifications for `prost` Decoding Leaves

Separation-logic contracts, cursor predicates, and stack budgets relating the compiled `prost`
protobuf decoding leaves to `Specifications/LibsignalProtoCodec.lean`:
- `core::ptr::drop_glue::<prost::error::DecodeError>` (`dropDecodeErrorSpec`);
- `prost::encoding::varint::decode_varint_slice` (`decodeVarintSliceSpec` ↔ `decodeVarint`);
- `prost::encoding::int32::merge::<&mut &[u8]>` (`int32MergeSpec` ↔ `mergeUint32`);
- `prost::encoding::skip_field::<&mut &[u8]> [local#1]` (`skipFieldSpec` ↔ `skipField`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Prost

open Arm64 ProofLib CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec

/-! ## Symbol names -/

abbrev decodeVarintSliceName : String :=
  "prost::encoding::varint::decode_varint_slice"

abbrev int32MergeName : String :=
  "prost::encoding::int32::merge::<&mut &[u8]>"

abbrev skipFieldName : String :=
  "prost::encoding::skip_field::<&mut &[u8]> [local#1]"

abbrev dropDecodeErrorName : String :=
  "core::ptr::drop_glue::<prost::error::DecodeError> [local#1]"

/-! ## Stack budgets -/

/-- Stack budget for `drop_glue::<DecodeError>`: 32-byte frame (`0x20`) plus `allocHookStack`. -/
abbrev dropDecodeErrorStack : Nat := 0x20 + allocHookStack

/-- Stack budget for `decode_varint_slice`: 80-byte frame (`0x50`) plus `decodeErrorHookStack`. -/
abbrev decodeVarintSliceStack : Nat := 0x50 + decodeErrorHookStack

/-- Stack budget for `int32::merge::<&mut &[u8]>`: 80-byte frame (`0x50`) plus
`decodeVarintSliceStack`. -/
abbrev int32MergeStack : Nat := 0x50 + decodeVarintSliceStack

/-- Stack budget for `skip_field::<&mut &[u8]>` at recursion limit `depth`: up to `depth + 1`
active 96-byte frames (`0x60`) plus `decodeVarintSliceStack`. -/
abbrev skipFieldStack (depth : Nat) : Nat :=
  (depth + 1) * 0x60 + decodeVarintSliceStack

/-! ## Shared cursor and result predicates -/

/-- 16-byte `&[u8]` slice header `(ptr, bs.length)` at `slot` together with the read-only backing
bytes `ptr ↦ₛ bs`. -/
def sliceCursorAt (slot ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  (slot ↦₆₄ ptr) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ (ptr ↦ₛ bs)

/-- Slice cursor at `slot` after advancing by `bs.length - rest.length` bytes to the suffix
`rest`, preserving `ptr ↦ₛ bs`. -/
def sliceCursorAfter (slot ptr : BitVec 64) (bs rest : List (BitVec 8)) : SepProp :=
  (slot ↦₆₄ (ptr + BitVec.ofNat 64 (bs.length - rest.length))) ∗
    ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 rest.length) ∗ (ptr ↦ₛ bs)

/-! ## `core::ptr::drop_glue::<prost::error::DecodeError>` -/

/-- Contract of `core::ptr::drop_glue::<prost::error::DecodeError>(x0 = e)`: deallocates any
non-empty context `Vec` and the 72-byte `Box<Inner>` of `decodeErrorAt A e` without panicking. -/
def dropDecodeErrorSpec (A : RustAlloc) : Spec (BitVec 64) where
  pre := fun e s =>
    ⌜s.readReg64 .x0 = e⌝ ∗ decodeErrorAt A e ∗ A.pool ∗ stackAt s.sp dropDecodeErrorStack
  post := fun _ s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ A.pool ∗ stackAt s0.sp dropDecodeErrorStack

/-! ## `prost::encoding::varint::decode_varint_slice` -/

/-- Fast-path precondition of `decode_varint_slice`: either `11 ≤ bs.length`, or `bs` is
non-empty and its last byte has MSB `0` (`≤ 0x7F`). -/
def VarintSlicePre (bs : List (BitVec 8)) : Prop :=
  11 ≤ bs.length ∨ ∃ h : bs ≠ [], (bs.getLast h).toNat ≤ 0x7F

/-- Ghost arguments of `decode_varint_slice`. -/
structure DecodeVarintSliceGhost where
  /-- Result buffer (`x0`, 24 bytes). -/
  ret : BitVec 64
  /-- Slice base pointer (`x1`). -/
  ptr : BitVec 64
  /-- Slice bytes (`x2 = bs.length`). -/
  bs : List (BitVec 8)

/-- 24-byte `Result<(u64, usize), DecodeError>` layout at `ret`:
- `some (v, rest)`: tag `0` at `ret`, decoded `u64` `v` at `ret + 8`, and consumed byte count
  `bs.length - rest.length` at `ret + 16`;
- `none`: tag `1` at `ret` and `e` at `ret + 8` owning `decodeErrorAtStackLen A e 0`. -/
def varintSliceResultAt (A : RustAlloc) (ret : BitVec 64) (bs : List (BitVec 8)) :
    Option (BitVec 64 × List (BitVec 8)) → SepProp
  | some (v, rest) =>
    (ret ↦₆₄ 0#64) ∗ ((ret + 8#64) ↦₆₄ v) ∗
      ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 (bs.length - rest.length))
  | none =>
    (ret ↦₆₄ 1#64) ∗
      (∃∗ e : BitVec 64, ⌜e ≠ 0#64⌝ ∗ ((ret + 8#64) ↦₆₄ e) ∗ decodeErrorAtStackLen A e 0) ∗
      memRegion (ret + 16#64) 8

/-- Contract of `prost::encoding::varint::decode_varint_slice(x0 = ret, x1 = ptr, x2 = bs.length)`:
under `VarintSlicePre x.bs`, writes `varintSliceResultAt A x.ret x.bs (decodeVarint x.bs)`,
panicking only on allocator failure inside `DecodeError::from`. -/
def decodeVarintSliceSpec (A : RustAlloc) : Spec DecodeVarintSliceGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.ptr ∧
      (s.readReg64 .x2).toNat = x.bs.length ∧ x.bs.length < 2 ^ 63 ∧ VarintSlicePre x.bs⌝ ∗
      memRegion x.ret 24 ∗ (x.ptr ↦ₛ x.bs) ∗ A.pool ∗ stackAt s.sp decodeVarintSliceStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ varintSliceResultAt A x.ret x.bs (decodeVarint x.bs) ∗
      (x.ptr ↦ₛ x.bs) ∗ A.pool ∗ stackAt s0.sp decodeVarintSliceStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-! ## `prost::encoding::int32::merge::<&mut &[u8]>` -/

/-- Ghost arguments of `int32::merge::<&mut &[u8]>`. -/
structure Int32MergeGhost where
  /-- Wire type (`w0` low byte). -/
  wt : WireType
  /-- Destination `&mut u32` pointer (`x1`, 4 bytes). -/
  valPtr : BitVec 64
  /-- Outer cursor reference `buf: &mut &mut &[u8]` (`x2`, 8 bytes holding `slot`). -/
  bufRef : BitVec 64
  /-- Slice header address (`*bufRef`, 16 bytes holding `(ptr, bs.length)`). -/
  slot : BitVec 64
  /-- Slice data pointer. -/
  ptr : BitVec 64
  /-- Remaining input bytes. -/
  bs : List (BitVec 8)

/-- Contract of `prost::encoding::int32::merge::<&mut &[u8]>(w0 = wt, x1 = valPtr, x2 = bufRef)`:
matches `mergeUint32 x.wt x.bs`, storing `v` at `x.valPtr` and advancing `x.slot` to `rest` with
`x0 = 0` on `some (v, rest)`, or returning `x0 ≠ 0` owning `decodeErrorAtStackLen A x0 0` on
`none`. -/
def int32MergeSpec (A : RustAlloc) : Spec Int32MergeGhost where
  pre := fun x s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.valPtr ∧ s.readReg64 .x2 = x.bufRef ∧ x.bs.length < 2 ^ 63⌝ ∗
      memRegion x.valPtr 4 ∗ (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool ∗ stackAt s.sp int32MergeStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗ A.pool ∗ stackAt s0.sp int32MergeStack ∗
      match mergeUint32 x.wt x.bs with
      | some (v, rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗ (x.valPtr ↦₃₂ v) ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗ decodeErrorAtStackLen A (sf.readReg64 .x0) 0 ∗
          memRegion x.valPtr 4 ∗ memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-! ## `prost::encoding::skip_field::<&mut &[u8]> [local#1]` -/

/-- Ghost arguments of `skip_field::<&mut &[u8]>`. -/
structure SkipFieldGhost where
  /-- Wire type (`w0` low byte). -/
  wt : WireType
  /-- Field tag (`w1`, `< 2^32`). -/
  tag : Nat
  /-- Remaining recursion depth (`w3`, `< 2^32`). -/
  depth : Nat
  /-- Outer cursor reference `buf: &mut &mut &[u8]` (`x2`, 8 bytes holding `slot`). -/
  bufRef : BitVec 64
  /-- Slice header address (`*bufRef`, 16 bytes holding `(ptr, bs.length)`). -/
  slot : BitVec 64
  /-- Slice data pointer. -/
  ptr : BitVec 64
  /-- Remaining input bytes. -/
  bs : List (BitVec 8)

/-- Contract of `prost::encoding::skip_field::<&mut &[u8]>(w0 = wt, w1 = tag, x2 = bufRef,
w3 = depth)`: matches `skipField (2 * x.bs.length + 2) x.depth x.tag x.wt x.bs`, advancing
`x.slot` to `rest` with `x0 = 0` on `some rest`, or returning `x0 ≠ 0` owning
`decodeErrorAtStackLen A x0 0` on `none`. -/
def skipFieldSpec (A : RustAlloc) : Spec SkipFieldGhost where
  pre := fun x s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      (s.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 x.tag ∧ x.tag < 2 ^ 32 ∧
      s.readReg64 .x2 = x.bufRef ∧
      (s.readReg64 .x3).setWidth 32 = BitVec.ofNat 32 x.depth ∧ x.depth < 2 ^ 32 ∧
      x.bs.length < 2 ^ 63⌝ ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool ∗ stackAt s.sp (skipFieldStack x.depth)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗ A.pool ∗
      stackAt s0.sp (skipFieldStack x.depth) ∗
      match skipField (2 * x.bs.length + 2) x.depth x.tag x.wt x.bs with
      | some rest =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗ sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗ decodeErrorAtStackLen A (sf.readReg64 .x0) 0 ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-! ## Target `subroutine_ok` propositions -/

def DropDecodeErrorOk (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr dropDecodeErrorName)
    (dropDecodeErrorSpec A)

def DecodeVarintSliceOk (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr decodeVarintSliceName)
    (decodeVarintSliceSpec A)

def Int32MergeOk (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr int32MergeName)
    (int32MergeSpec A)

def SkipFieldOk (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr skipFieldName)
    (skipFieldSpec A)

/-! ## `Stage2ContractsX` / `AllocContractsX` Stack Budgets and Specifications -/

/-- Scaled `decodeErrorHookStack` (`2 * extHookStack = 32768`) for `Stage2ContractsX`. -/
abbrev decodeErrorHookStackX : Nat := 2 * extHookStack

/-- `drop_glue::<DecodeError>` stack budget under `AllocContractsX` (`0x20 + extHookStack = 16416`). -/
abbrev dropDecodeErrorStackX : Nat := 0x20 + extHookStack

/-- `decode_varint_slice` stack budget under `Stage2ContractsX` (`0x50 + decodeErrorHookStackX = 32848`). -/
abbrev decodeVarintSliceStackX : Nat := 0x50 + decodeErrorHookStackX

/-- `int32::merge` stack budget under `Stage2ContractsX` (`0x50 + decodeVarintSliceStackX = 32928`). -/
abbrev int32MergeStackX : Nat := 0x50 + decodeVarintSliceStackX

/-- `skip_field` stack budget under `Stage2ContractsX` (`(depth + 1) * 0x60 + decodeVarintSliceStackX`). -/
abbrev skipFieldStackX (depth : Nat) : Nat :=
  (depth + 1) * 0x60 + decodeVarintSliceStackX

def dropDecodeErrorSpecX (A : RustAlloc) : Spec (BitVec 64) where
  pre := fun e s =>
    ⌜s.readReg64 .x0 = e⌝ ∗ decodeErrorAt A e ∗ A.pool ∗ stackAt s.sp dropDecodeErrorStackX
  post := fun _ s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ A.pool ∗ stackAt s0.sp dropDecodeErrorStackX

def decodeVarintSliceSpecX (A : RustAlloc) : Spec DecodeVarintSliceGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.ptr ∧
      (s.readReg64 .x2).toNat = x.bs.length ∧ x.bs.length < 2 ^ 63 ∧ VarintSlicePre x.bs⌝ ∗
      memRegion x.ret 24 ∗ (x.ptr ↦ₛ x.bs) ∗ A.pool ∗ stackAt s.sp decodeVarintSliceStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ varintSliceResultAt A x.ret x.bs (decodeVarint x.bs) ∗
      (x.ptr ↦ₛ x.bs) ∗ A.pool ∗ stackAt s0.sp decodeVarintSliceStackX
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def int32MergeSpecX (A : RustAlloc) : Spec Int32MergeGhost where
  pre := fun x s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.valPtr ∧ s.readReg64 .x2 = x.bufRef ∧ x.bs.length < 2 ^ 63⌝ ∗
      memRegion x.valPtr 4 ∗ (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool ∗ stackAt s.sp int32MergeStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗ A.pool ∗ stackAt s0.sp int32MergeStackX ∗
      match mergeUint32 x.wt x.bs with
      | some (v, rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗ (x.valPtr ↦₃₂ v) ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗ decodeErrorAtStackLen A (sf.readReg64 .x0) 0 ∗
          memRegion x.valPtr 4 ∗ memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def skipFieldSpecX (A : RustAlloc) : Spec SkipFieldGhost where
  pre := fun x s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      (s.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 x.tag ∧ x.tag < 2 ^ 32 ∧
      s.readReg64 .x2 = x.bufRef ∧
      (s.readReg64 .x3).setWidth 32 = BitVec.ofNat 32 x.depth ∧ x.depth < 2 ^ 32 ∧
      x.bs.length < 2 ^ 63⌝ ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool ∗ stackAt s.sp (skipFieldStackX x.depth)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗ A.pool ∗
      stackAt s0.sp (skipFieldStackX x.depth) ∗
      match skipField (2 * x.bs.length + 2) x.depth x.tag x.wt x.bs with
      | some rest =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗ sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗ decodeErrorAtStackLen A (sf.readReg64 .x0) 0 ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

end CryptoVerification.LibsignalTripleRatchet.Prost

