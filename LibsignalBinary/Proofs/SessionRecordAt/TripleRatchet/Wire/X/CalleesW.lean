/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Prost.DefsW
public import LibsignalBinary.Proofs.TripleRatchet.Getters.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.Getters.GettersCodeSym
public import LibsignalBinary.Proofs.RecordCodecs.RecordCodecsCodeSymB

/-!
# Callee Contracts for `SignalMessage::try_from`

Specifications and `subroutine_ok` predicates for the internal callees of `SignalMessage::try_from`
(`DecodeError::from`, `DecodeError::push`, `decode_varint_slow`, `drop_glue<SignalProtocolError>`,
`Vec<u8>::into_boxed_slice`, and `Box<[u8]>::try_clone_from_ref_in`) with stack budgets raised by
`externStack = 16384`, both on `contractProg img.base ext` and under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.LibsignalTripleRatchet.WireX

open Arm64 ProofLib CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Prost.X
open CryptoVerification.LibsignalTripleRatchet.Getters

theorem L1_CalleesW : True := trivial

/-! ## Stack budgets (legacy `+ externStack`) -/

/-- `decode_varint_slow` budget with X externs (`varintSlowStack + 16384`). -/
abbrev varintSlowStackX : Nat := varintSlowStack + CryptoVerification.LibsignalTripleRatchet.extHookStack

/-- `drop_glue<SignalProtocolError>` budget with X externs (`dropSpeStack + 16384`). -/
abbrev dropSpeStackX : Nat := dropSpeStack + CryptoVerification.LibsignalTripleRatchet.extHookStack

/-- `into_boxed_slice` budget with X externs (`intoBoxedSliceStack + 16384`). -/
abbrev intoBoxedSliceStackX : Nat := intoBoxedSliceStack + CryptoVerification.LibsignalTripleRatchet.extHookStack

/-- `try_clone_from_ref_in` budget with X externs (`tryCloneFromRefStack + 16384`). -/
abbrev tryCloneFromRefStackX : Nat :=
  tryCloneFromRefStack + CryptoVerification.LibsignalTripleRatchet.extHookStack

theorem varintSlowStackX_eq : varintSlowStackX = 64 + decodeErrorHookStackW := rfl

/-! ## Specifications -/

def decodeVarintSlowSpecX (A : RustAlloc) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (slotA, slot, ptr, bs) s =>
    ⌜s.readReg64 .x0 = slotA ∧ bs.length < 2 ^ 64⌝ ∗
      (slotA ↦₆₄ slot) ∗ (slot ↦₆₄ ptr) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      (ptr ↦ₛ bs) ∗ A.pool ∗ stackAt s.sp varintSlowStackX
  post := fun (slotA, slot, ptr, bs) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (slotA ↦₆₄ slot) ∗ (ptr ↦ₛ bs) ∗ A.pool ∗ stackAt s0.sp varintSlowStackX ∗
      match varintSlow bs with
      | some (v, k) =>
        ⌜sf.readReg64 .x0 = 0#64 ∧ sf.readReg64 .x1 = v⌝ ∗
          (slot ↦₆₄ (ptr + BitVec.ofNat 64 k)) ∗
          ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - k))
      | none =>
        ⌜sf.readReg64 .x0 = 1#64 ∧ sf.readReg64 .x1 ≠ 0#64⌝ ∗
          decodeErrorAtStackLen A (sf.readReg64 .x1) 0 ∗
          (slot ↦₆₄ (ptr + BitVec.ofNat 64 (min 10 bs.length))) ∗
          ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - min 10 bs.length))
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def dropSpeSpecX (A : RustAlloc) : Spec DropSpeGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a⌝ ∗
      speAt A x.fnName x.a x.e ∗ A.pool ∗ stackAt s.sp dropSpeStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.a 48 ∗ A.pool ∗ stackAt s0.sp dropSpeStackX

def intoBoxedSliceSpecX (A : RustAlloc) : Spec VecArg where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.v⌝ ∗ x.at A ∗ A.pool ∗ stackAt s.sp intoBoxedSliceStackX
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length ∧ sf.trace = s0.trace⌝ ∗
    vecHeader x.v x.cap x.ptr (BitVec.ofNat 64 x.bytes.length) ∗
    boxU8Buf A (sf.readReg64 .x0) x.bytes ∗ A.pool ∗ stackAt s0.sp intoBoxedSliceStackX
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def tryCloneFromRefSpecX (A : RustAlloc) : Spec TryCloneSliceCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.src ∧ (s.readReg64 .x1).toNat = x.bs.length ∧
      x.bs.length + 1 ≤ 2 ^ 63⌝ ∗
    (x.src ↦ₛ x.bs) ∗ A.pool ∗ stackAt s.sp tryCloneFromRefStackX
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x1 = BitVec.ofNat 64 x.bs.length⌝ ∗ (x.src ↦ₛ x.bs) ∗
    (if sf.readReg64 .x0 = 0#64 then
      ⌜x.bs ≠ [] ∧ sf.trace = s0.trace ++ [allocFailedEvent]⌝
     else
      ⌜sf.trace = s0.trace⌝ ∗ boxU8Buf A (sf.readReg64 .x0) x.bs) ∗
    A.pool ∗ stackAt s0.sp tryCloneFromRefStackX

/-! ## `subroutine_ok` obligations on `contractProg img.base ext` -/

/-- `DecodeError::from` meets `decodeErrorFromSpecX` on `contractProg img.base ext`. -/
def DecodeErrorFromOkW (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (contractProg img.base ext)
    ((contractProg img.base ext).fnAddr decodeErrorFromName) ((decodeErrorFromSpecX A).inImage img)

/-- `DecodeError::push` meets `decodeErrorPushSpecX` on `contractProg img.base ext`. -/
def DecodeErrorPushOkW (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (contractProg img.base ext)
    ((contractProg img.base ext).fnAddr decodeErrorPushName) ((decodeErrorPushSpecX A).inImage img)

/-- `decode_varint_slow` meets `decodeVarintSlowSpecX` on `contractProg img.base ext`. -/
def DecodeVarintSlowOkW (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (contractProg img.base ext)
    ((contractProg img.base ext).fnAddr varintSlowName) ((decodeVarintSlowSpecX A).inImage img)

/-- `drop_glue<SignalProtocolError>` meets `dropSpeSpecX` on `contractProg img.base ext`. -/
def DropSpeOkW (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (contractProg img.base ext)
    ((contractProg img.base ext).fnAddr dropSpeName) ((dropSpeSpecX A).inImage img)

/-- `Vec<u8>::into_boxed_slice` meets `intoBoxedSliceSpecX` on `contractProg img.base ext`. -/
def IntoBoxedSliceOkW (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (contractProg img.base ext)
    ((contractProg img.base ext).fnAddr intoBoxedSliceName) ((intoBoxedSliceSpecX A).inImage img)

/-- `Box<[u8]>::try_clone_from_ref_in` meets `tryCloneFromRefSpecX` on `contractProg img.base ext`. -/
def TryCloneFromRefOkW (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (contractProg img.base ext)
    ((contractProg img.base ext).fnAddr tryCloneFromRefName)
    ((tryCloneFromRefSpecX A).inImage img)

/-! ## Relocatable `[LibsignalPlacement]` Proofs -/

section Placed

open CryptoVerification

/-- `DecodeError::from` (Block `261`) meets `decodeErrorFromSpecX` under `[LibsignalPlacement]`. -/
def DecodeErrorFromPlacedOkW [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop :=
  subroutine_ok ((blkPC_261).rebase (blkPl_261).base H)
    (blkPl_261).base (withLsCodeLoaded lsmpl (decodeErrorFromSpecX A))

/-- `DecodeError::push` (Block `257`) meets `decodeErrorPushSpecX` under `[LibsignalPlacement]`. -/
def DecodeErrorPushPlacedOkW [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop :=
  subroutine_ok
    ((CryptoVerification.RecordCodecs.Placed.blkPC_257).rebase
      (CryptoVerification.RecordCodecs.Placed.blkPl_257).base H)
    (CryptoVerification.RecordCodecs.Placed.blkPl_257).base
    (withLsCodeLoaded lsmpl (decodeErrorPushSpecX A))

/-- `decode_varint_slow` (Block `293`) meets `decodeVarintSlowSpecX` under `[LibsignalPlacement]`. -/
def DecodeVarintSlowPlacedOkW [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop :=
  subroutine_ok ((blkPC_293).rebase (blkPl_293).base H)
    (blkPl_293).base (withLsCodeLoaded lsmpl (decodeVarintSlowSpecX A))

/-- `drop_glue<SignalProtocolError>` (Block `4`) meets `dropSpeSpecX` under `[LibsignalPlacement]`. -/
def DropSpePlacedOkW [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop :=
  subroutine_ok ((Getters.blkPC_5).rebase (Getters.blkPl_5).base H)
    (Getters.blkPl_5).base (withLsCodeLoaded lsmpl (dropSpeSpecX A))

/-- `Vec<u8>::into_boxed_slice` (Block `56`) meets `intoBoxedSliceSpecX` under `[LibsignalPlacement]`. -/
def IntoBoxedSlicePlacedOkW [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop :=
  subroutine_ok ((blkPC_56).rebase (blkPl_56).base H)
    (blkPl_56).base (withLsCodeLoaded lsmpl (intoBoxedSliceSpecX A))

/-- `Box<[u8]>::try_clone_from_ref_in` (Block `23`) meets `tryCloneFromRefSpecX` under `[LibsignalPlacement]`. -/
def TryCloneFromRefPlacedOkW [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop :=
  subroutine_ok ((blkPC_23).rebase (blkPl_23).base H)
    (blkPl_23).base (withLsCodeLoaded lsmpl (tryCloneFromRefSpecX A))

end Placed

end CryptoVerification.LibsignalTripleRatchet.WireX
