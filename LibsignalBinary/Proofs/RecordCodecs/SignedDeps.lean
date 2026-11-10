/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.RecordCodecsBinary.SignedPreKey
public import LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3
public import LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.Proof
public import LibsignalBinary.Proofs.RecordCodecs.RecordCodecsCodeSymB
public import LibsignalBinary.Proofs.RecordCodecs.RecordCodecsCodeSymC
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.SigTryFrom.DecodeErrorFrom
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.SigTryFrom.DecodeErrorPush
import ProofLib.SepLogic.WPp

/-!
# Callee Contracts for the Signed and Kyber Pre-Key Record Decoder

Defines the prost callee bundles (`SignedPortDeps`, `SignedPortDepsX`, `SignedPortDepsPlaced`),
allocator/error hook bundles (`SignedHooks`, `SignedHooksX`, `SignedHooksPlaced`), and inner/outer
decoder contracts (`signedDecodeSpec`, `signedDecodePlacedSpec` on Block `562`,
`decodeKyberPreKeyPlacedSpec` and `decodeSignedPreKeyPlacedSpec` on Block `595`), plus the
relocatable proof of `drop_glue::<prost::error::DecodeError> [local#3]` (Block `555`).
-/

@[expose] public section

namespace CryptoVerification.RecordCodecsBinary

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.RecordCodecs

/-! ## CLI-Instantiated Symbol Names -/

/-- The CLI-local `<SignedPreKeyRecordStructure as prost::Message>::decode::<&[u8]>` (prost's
provided `Message::decode`, instantiated in the CLI crate; 824 bytes, frame `0xe0`). -/
abbrev signedDecodeName : String :=
  "<libsignal_protocol::proto::storage::SignedPreKeyRecordStructure as prost::message::Message>::decode::<&[u8]>"

/-- The CLI-local `prost::encoding::varint::decode_varint::<&mut &[u8]>` (copy of `[local#2]`). -/
abbrev decodeVarint6Name : String :=
  "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#5]"

/-- The CLI-local `prost::encoding::skip_field::<&mut &[u8]>` (copy of `[local#3]`). -/
abbrev skipField7Name : String :=
  "prost::encoding::skip_field::<&mut &[u8]> [local#6]"

/-- The CLI-local `prost::encoding::bytes::merge::<Vec<u8>, &mut &[u8]>` (copy of `[local#3]`). -/
abbrev bytesMerge7Name : String :=
  "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#6]"

/-- The CLI-local `core::ptr::drop_glue::<prost::error::DecodeError>` (copy of `[local#1]`). -/
abbrev dropDecodeError3Name : String :=
  "core::ptr::drop_glue::<prost::error::DecodeError> [local#3]"

/-! ## Contracts -/

/-- Prost callee contracts: the CLI-local prost instances meet the specs of the proved instances
they copy, on `tripleRatchetProgAtExt img.base ext`. -/
structure SignedPortDeps (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop where
  /-- `decode_varint [local#6]` (copy of `[local#2]`, `decodeVarint2_ok_of_contracts`). -/
  decodeVarint6 :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decodeVarint6Name)
      (SpqrV1.Varint.decodeVarint2Spec A)
  /-- `skip_field [local#7]` (copy of `[local#3]`, `skipField3_ok_of_contracts`). -/
  skipField7 :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr skipField7Name)
      (SpqrV1.Varint.skipField3Spec A)
  /-- `bytes::merge [local#7]` (copy of `[local#3]`, `bytes_merge_3_ok_of_contracts`). -/
  bytesMerge7 :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr bytesMerge7Name)
      (SpqrV1.Prost.BytesMerge.bytesMerge3Spec A img)
  /-- `drop_glue::<DecodeError> [local#3]` (copy of `[local#1]`, `dropDecodeError_ok_of_contract`). -/
  dropDecodeError3 :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dropDecodeError3Name)
      (Prost.dropDecodeErrorSpec A)

/-- The hooks the decode loop calls directly: the allocator bundle (for `__rust_dealloc` of
the partial `Vec`s on the error path), `DecodeError::from` and `DecodeError::push`. These are
fields of `Stage2Contracts` (`SignedHooks.of_stage2`). -/
structure SignedHooks (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) :
    Prop where
  alloc : AllocContracts b A ext
  decodeErrorFrom :
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr decodeErrorFromName)
      (decodeErrorFromSpec A)
  decodeErrorPush :
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr decodeErrorPushName)
      (decodeErrorPushSpec A)

/-- `Stage2Contracts` gives `SignedHooks`. -/
theorem SignedHooks.of_stage2 {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel} {ext : String → Option (State → State)}
    (hC : Stage2Contracts b C A ctl parse S ext) : SignedHooks b A ext :=
  ⟨hC.toAllocContracts, hC.decode_error_from, hC.decode_error_push⟩

/-! ## The inner decoder's contract -/

/-- Stack budget of the inner decoder: its frame (`sub sp, sp, #0xe0`) plus its deepest callee,
`skip_field` with recursion budget `100` (`+0x130: mov w3, #100`), whose budget covers
`bytes::merge` (`bytesMerge3Stack`), `decode_varint`, `from` / `push` and `__rust_dealloc`. -/
abbrev signedDecodeStack : Nat := 0xe0 + SpqrV1.Varint.skipField3Stack 100

-- The callee budgets fit in the inner decoder's (`decide`).
example : SpqrV1.Prost.BytesMerge.bytesMerge3Stack ≤ SpqrV1.Varint.skipField3Stack 100 ∧
    SpqrV1.Varint.decodeVarint2Stack ≤ SpqrV1.Varint.skipField3Stack 100 ∧
    decodeErrorHookStack ≤ SpqrV1.Varint.skipField3Stack 100 := by decide

-- The wrapper's frame (`sub sp, sp, #128`) plus the inner decoder's budget fit in `smallRootStack`.
example : 0x80 + signedDecodeStack ≤ smallRootStack := by decide

/-- `Result<SignedPreKeyRecordStructure, DecodeError>` at `r` (88 bytes), for the model
`SignedPreKeyRecordStructure.decode`: `some m` = the structure in place (the decoder's `Ok` exit
`+0x2f8..+0x31c`); `none` = `errTag` (`-1`) @0, an owned `DecodeError` box @8, 72 bytes
unspecified (`+0x2a0..+0x2a4: mov x9, #-1; stp x9, x1, [x19]`, after the three partial `Vec`s are
freed, `+0x2a8..+0x2dc`). -/
def signedDecodeResultAt (A : RustAlloc) (r : BitVec 64) :
    Option SignedPreKeyRecordStructure → SepProp
  | some m => signedPreKeyStructAt A r m
  | none =>
    (r ↦₆₄ errTag) ∗ (∃∗ e : BitVec 64, ((r + 8#64) ↦₆₄ e) ∗ decodeErrorAt A e) ∗
      memRegion (r + 16#64) 72

/-- Contract of the inner decoder `<SignedPreKeyRecordStructure as Message>::decode::<&[u8]>`
(`x0` = out, `x1` = ptr, `x2` = len): the 88 bytes at `x0` hold
`SignedPreKeyRecordStructure.decode bytes` for nonempty `bytes` (`0 < x.bytes.length`: every
CLI caller passes a nonempty slice, and on `[]` the compiled code returns `Err`, see
`SignedPreKeyDecode.signedDecode_empty_disproof`), the input is given back, every partial
allocation is freed or moved into the result; the only panic is an allocation failure. Not a
statement of the CLI theorem (only `decodeKyberPreKeySpec` is); it is the interface between the
two hops. -/
def signedDecodeSpec (A : RustAlloc) (img : Obj.Image) : Spec DecodeGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.bytesA ∧
          (s.readReg64 .x2).toNat = x.bytes.length ∧
          0 < x.bytes.length ∧ x.bytes.length < 2 ^ 32⌝ ∗
          (x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 88 ∗ stackAt s.sp signedDecodeStack ∗ A.pool
      post := fun x s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗
          signedDecodeResultAt A x.ret (SignedPreKeyRecordStructure.decode x.bytes) ∗
          (x.bytesA ↦ₛ x.bytes) ∗ stackAt s0.sp signedDecodeStack ∗ A.pool
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

/-! ## X-form (`AllocContractsX`) hooks, callee contracts, and inner decoder spec -/

/-- Stack budget of `prost::encoding::skip_field::<&mut &[u8]>` at recursion budget `depth`
under `AllocContractsX` (`decodeVarint2StackX`). -/
abbrev skipField3StackX (depth : Nat) : Nat :=
  (depth + 1) * 0x60 + SpqrV1.Varint.decodeVarint2StackX

/-- X-form contract of `prost::encoding::skip_field::<&mut &[u8]>` (`skipField3StackX`). -/
def skipField3SpecX (A : RustAlloc) : Spec Prost.SkipFieldGhost where
  pre := fun x s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      (s.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 x.tag ∧ x.tag < 2 ^ 32 ∧
      s.readReg64 .x2 = x.bufRef ∧
      (s.readReg64 .x3).setWidth 32 = BitVec.ofNat 32 x.depth ∧ x.depth < 2 ^ 32 ∧
      x.bs.length < 2 ^ 63⌝ ∗
      (x.bufRef ↦₆₄ x.slot) ∗ Prost.sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool ∗ stackAt s.sp (skipField3StackX x.depth)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗ A.pool ∗
      stackAt s0.sp (skipField3StackX x.depth) ∗
      match CryptoVerification.LibsignalProtoCodec.skipField (2 * x.bs.length + 2) x.depth x.tag x.wt x.bs with
      | some rest =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗ Prost.sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗ decodeErrorAtStackLen A (sf.readReg64 .x0) 0 ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Stack budget of `prost::encoding::bytes::merge::<Vec<u8>, &mut &[u8]>` under
`AllocContractsX`: own frame `0xe0` (`224`) bytes plus `decodeVarint2StackX`. -/
abbrev bytesMerge3StackX : Nat := 0xe0 + SpqrV1.Varint.decodeVarint2StackX

/-- Raw X-form contract of `prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]>`. -/
def bytesMerge3RawSpecX (A : RustAlloc) : Spec Prost.BytesMergeGhost where
  pre := fun x s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.valPtr ∧ s.readReg64 .x2 = x.bufRef ∧ x.bs.length < 2 ^ 63 ∧
      Prost.BytesMergeCapOk x.valCap x.bs.length⌝ ∗
      vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
      (x.bufRef ↦₆₄ x.slot) ∗ Prost.sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool ∗ stackAt s.sp bytesMerge3StackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗ A.pool ∗ stackAt s0.sp bytesMerge3StackX ∗
      match CryptoVerification.LibsignalProtoCodec.mergeBytes x.wt x.bs with
      | some (v, rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗
          (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
            ⌜Prost.BytesMergeCapOk cap' rest.length⌝ ∗ vecU8At A x.valPtr cap' ptr' v) ∗
          Prost.sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗ decodeErrorAtStackLen A (sf.readReg64 .x0) 0 ∗
          vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- In-image X-form contract of `prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]>`. -/
def bytesMerge3SpecX (A : RustAlloc) (img : Obj.Image) : Spec Prost.BytesMergeGhost :=
  (bytesMerge3RawSpecX A).inImage img

/-- X-form hooks (`AllocContractsX` + `.inImage img`, `2 * extHookStack`) for the signed /
Kyber pre-key record decoder, eliminating `trTrapExterns` and zero-stack `AllocContracts`. -/
structure SignedHooksX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop where
  alloc : AllocContractsX img A ext
  decodeErrorFrom :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decodeErrorFromName)
      ((decodeErrorFromSpecWithStack A (2 * extHookStack)).inImage img)
  decodeErrorPush :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decodeErrorPushName)
      ((decodeErrorPushExternSpecWithStack A (2 * extHookStack)).inImage img)

/-- `AllocContractsX` directly discharges `SignedHooksX` (no `trTrapExterns` needed). -/
theorem SignedHooksX.of_alloc {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    SignedHooksX img A ext where
  alloc := hA
  decodeErrorFrom :=
    CryptoVerification.SignalSession.Cli.RunProofs.SigTryFromHelpers.decodeErrorFrom_ok_ext_x hA
  decodeErrorPush :=
    CryptoVerification.SignalSession.Cli.RunProofs.SigTryFromHelpers.decodeErrorPush_ok_ext_x hA

/-- X-form prost callee contracts: the CLI-local prost instances at `AllocContractsX` stack budgets and
`.inImage img` on `tripleRatchetProgAtExt img.base ext`. -/
structure SignedPortDepsX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop where
  /-- `decode_varint [local#6]` (`decodeVarint2_ok_of_contracts_x`). -/
  decodeVarint6 :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decodeVarint6Name)
      ((SpqrV1.Varint.decodeVarint2SpecX A).inImage img)
  /-- `skip_field [local#7]` at `skipField3SpecX`. -/
  skipField7 :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr skipField7Name)
      ((skipField3SpecX A).inImage img)
  /-- `bytes::merge [local#7]` at `bytesMerge3SpecX`. -/
  bytesMerge7 :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr bytesMerge7Name)
      (bytesMerge3SpecX A img)
  /-- `drop_glue::<DecodeError> [local#3]` (`dropDecodeError_ok_ext_x`). -/
  dropDecodeError3 :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dropDecodeError3Name)
      ((Prost.dropDecodeErrorSpecX A).inImage img)

/-- X-form stack budget of the inner decoder: own frame `0xe0` plus `skipField3StackX 100`. -/
abbrev signedDecodeStackX : Nat := 0xe0 + skipField3StackX 100

example : bytesMerge3StackX ≤ skipField3StackX 100 ∧
    SpqrV1.Varint.decodeVarint2StackX ≤ skipField3StackX 100 ∧
    2 * extHookStack ≤ skipField3StackX 100 ∧
    extHookStack ≤ skipField3StackX 100 ∧
    Prost.dropDecodeErrorStackX ≤ signedDecodeStackX ∧
    0x80 + signedDecodeStackX ≤ smallRootStack := by decide

/-- X-form contract of the inner decoder `<SignedPreKeyRecordStructure as Message>::decode::<&[u8]>`
at stack budget `signedDecodeStackX` (`≤ smallRootStack - 0x80`). -/
def signedDecodeSpecX (A : RustAlloc) (img : Obj.Image) : Spec DecodeGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.bytesA ∧
          (s.readReg64 .x2).toNat = x.bytes.length ∧
          0 < x.bytes.length ∧ x.bytes.length < 2 ^ 32⌝ ∗
          (x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 88 ∗ stackAt s.sp signedDecodeStackX ∗ A.pool
      post := fun x s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗
          signedDecodeResultAt A x.ret (SignedPreKeyRecordStructure.decode x.bytes) ∗
          (x.bytesA ↦ₛ x.bytes) ∗ stackAt s0.sp signedDecodeStackX ∗ A.pool
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

/-! ## Relocatable `[LibsignalPlacement]` Contracts -/

section Placed

open CryptoVerification.RecordCodecs.Placed
open CryptoVerification.LibsignalTripleRatchet.Prost

/-- Image-free raw contract of `<SignedPreKeyRecordStructure as Message>::decode::<&[u8]>`. -/
def signedDecodeRawSpec (A : RustAlloc) : Spec DecodeGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.bytesA ∧
      (s.readReg64 .x2).toNat = x.bytes.length ∧
      0 < x.bytes.length ∧ x.bytes.length < 2 ^ 32⌝ ∗
      (x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 88 ∗ stackAt s.sp signedDecodeStack ∗ A.pool
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      signedDecodeResultAt A x.ret (SignedPreKeyRecordStructure.decode x.bytes) ∗
      (x.bytesA ↦ₛ x.bytes) ∗ stackAt s0.sp signedDecodeStack ∗ A.pool
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Relocatable `[LibsignalPlacement]` contract of `<SignedPreKeyRecordStructure as Message>::decode::<&[u8]>`
(block `562`), carrying `LibsignalCodeRoLoaded lsmpl` for transitive `bytes::merge` vtable reads. -/
abbrev signedDecodePlacedSpec [LibsignalPlacement] (A : RustAlloc) : Spec DecodeGhost :=
  LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (signedDecodeRawSpec A)

/-- Image-free raw contract of `signal_session::stores::decode_kyber_pre_key`. -/
def decodeKyberPreKeyRawSpec (A : RustAlloc) : Spec DecodeGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.bytesA ∧
      (s.readReg64 .x2).toNat = x.bytes.length ∧
      0 < x.bytes.length ∧ x.bytes.length < 2 ^ 32⌝ ∗
      (x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 88 ∗ stackAt s.sp smallRootStack ∗ A.pool
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ kyberPreKeyResultAt A x.ret (KyberPreKeyRecord.deserialize x.bytes) ∗
      (x.bytesA ↦ₛ x.bytes) ∗ stackAt s0.sp smallRootStack ∗ A.pool
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Relocatable `[LibsignalPlacement]` contract of `decode_kyber_pre_key` (block `595`). -/
abbrev decodeKyberPreKeyPlacedSpec [LibsignalPlacement] (A : RustAlloc) : Spec DecodeGhost :=
  LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (decodeKyberPreKeyRawSpec A)

/-- Image-free raw contract of `decode_kyber_pre_key` called as `decode_signed_pre_key`. -/
def decodeSignedPreKeyRawSpec (A : RustAlloc) : Spec DecodeGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.bytesA ∧
      (s.readReg64 .x2).toNat = x.bytes.length ∧
      0 < x.bytes.length ∧ x.bytes.length < 2 ^ 32⌝ ∗
      (x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 88 ∗ stackAt s.sp smallRootStack ∗ A.pool
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      signedPreKeyResultAt A x.ret (SignedPreKeyRecord.deserialize x.bytes) ∗
      (x.bytesA ↦ₛ x.bytes) ∗ stackAt s0.sp smallRootStack ∗ A.pool
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Relocatable `[LibsignalPlacement]` contract of `decode_signed_pre_key` (block `595`). -/
abbrev decodeSignedPreKeyPlacedSpec [LibsignalPlacement] (A : RustAlloc) : Spec DecodeGhost :=
  LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (decodeSignedPreKeyRawSpec A)

/-- Relocatable `[LibsignalPlacement]` counterpart of `SignedHooks`: `__rust_dealloc`,
`DecodeError::from` (block `261`), and `DecodeError::push` (block `257`). -/
structure SignedHooksPlaced [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop where
  dealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A)
  decodeErrorFrom :
    subroutine_ok ((blkPC_261).rebase (blkPl_261).base H) (blkPl_261).base
      (withLsCodeLoaded lsmpl (decodeErrorFromSpec A))
  decodeErrorPush :
    subroutine_ok (lsProg_257 H) (blkPl_257).base
      (withLsCodeLoaded lsmpl (decodeErrorPushSpec A))

/-- Relocatable `[LibsignalPlacement]` counterpart of `SignedPortDeps`: the CLI-instantiated `[local#...]`
prost callees (`559`, `546`, `558`, `555`). -/
structure SignedPortDepsPlaced [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) :
    Prop where
  /-- `decode_varint [local#5]` (block `559`). -/
  decodeVarint6 :
    subroutine_ok (lsProg_559 H) (blkPl_559).base
      (withLsCodeLoaded lsmpl (SpqrV1.Varint.decodeVarint2Spec A))
  /-- `skip_field [local#6]` (block `546`). -/
  skipField7 :
    subroutine_ok (lsProg_546 H) (blkPl_546).base
      (withLsCodeLoaded lsmpl (SpqrV1.Varint.skipField3Spec A))
  /-- `bytes::merge [local#6]` (block `558`). -/
  bytesMerge7 :
    subroutine_ok (lsProg_558 H) (blkPl_558).base
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (SpqrV1.Prost.BytesMerge.bytesMerge3RawSpec A))
  /-- `drop_glue::<DecodeError> [local#3]` (block `555`). -/
  dropDecodeError3 :
    subroutine_ok (lsProg_551 H) (blkPl_551).base
      (Prost.dropDecodeErrorSpec A)

section DropDecodeError3Placed

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit

/-- Relocatable `[LibsignalPlacement]` verification of `core::ptr::drop_glue::<prost::error::DecodeError> [local#3]`
(block `555`, 41 instructions), parameterized by `dStack`. -/
theorem drop_decode_error_3_placed_ok_gen [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {dStack : Nat} (hd : 0x20 + dStack ≤ 2 ^ 64 := by decide)
    (hdealloc : subroutine_ok (lsProg_551 H) (lsρ lsRustDeallocSym)
      (rustDeallocExternSpecWithStack A dStack)) :
    subroutine_ok (lsProg_551 H) (blkPl_551).base
      (dropDecodeErrorSpecGen A dStack) := by
  simp only [dropDecodeErrorSpecGen, decodeErrorAt, decodeErrorAtStackLen, vecOf, vecAt,
    vecHeader, vecBuf, stackAt_dropDecodeErrorGen hd, sepExists_sepConj_left, sepExists_sepConj_right,
    List.length_replicate]
  simp only [rustDeallocExternSpecWithStack] at hdealloc
  wp_init e s0
  have hkv : KindNoHeap v_stk_5 := by assumption
  have hbr := kindNoHeap_branch_false hkv
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have h_len_le : v_stk_4 ≤ v_stk_6.toNat := by assumption
  have h_cap_lt : v_stk_6.toNat * 32 < 2 ^ 63 := by assumption
  by_cases hcap0 : v_stk_6 = 0
  · subst hcap0
    simp only [ite_true, emp_sepConj]
    wp_steps
    apply SepWP.fold (box72_entails_memRegion e 0 v_stk_7 (BitVec.ofNat 64 v_stk_4) v_stk_5)
      (by sep_focus)
    apply SepWP.fold (stackAt_dropDecodeErrorGen_tail hd s0.sp _ _ _ _) (by sep_focus)
    wp_call hdealloc (e, 72, 8)
    apply SepWP.fold (Entails.of_eq (stackAt_dropDecodeErrorGen_post hd s0.sp)) (by sep_focus)
    wp_done
  · have hcap_beq : (v_stk_6 == 0#64) = false := beq_eq_false_iff_ne.mpr hcap0
    have hshl : (v_stk_6 <<< 5).toNat = v_stk_6.toNat * 32 := shl5_toNat h_cap_lt
    have hlay_vec : LayoutOk (v_stk_6.toNat * 32) 8 := layoutOk_mul32_8 hcap0 h_cap_lt
    have hpos_vec : 0 < v_stk_6.toNat * 32 := hlay_vec.1
    have hsum_vec : v_stk_6.toNat * 32 + 8 ≤ 2 ^ 63 := hlay_vec.2.2
    simp only [hcap0, ite_false, stackVec_buf_memRegion h_len_le h_cap_lt]
    wp_steps
    wp_call hdealloc (v_stk_7, v_stk_6.toNat * 32, 8)
    wp_steps
    apply SepWP.fold (box72_entails_memRegion e v_stk_6 v_stk_7 (BitVec.ofNat 64 v_stk_4) v_stk_5)
      (by sep_focus)
    apply SepWP.fold (stackAt_dropDecodeErrorGen_tail hd s0.sp _ _ _ _) (by sep_focus)
    wp_call hdealloc (e, 72, 8)
    apply SepWP.fold (Entails.of_eq (stackAt_dropDecodeErrorGen_post hd s0.sp)) (by sep_focus)
    wp_done

/-- Relocatable `[LibsignalPlacement]` verification of `drop_glue::<DecodeError> [local#3]`
(block `555`) against `Prost.dropDecodeErrorSpec A` directly from `HookSat H lsRustDeallocSym`. -/
theorem drop_decode_error_3_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok (lsProg_551 H) (blkPl_551).base
      (Prost.dropDecodeErrorSpec A) := by
  refine drop_decode_error_3_placed_ok_gen (dStack := allocHookStack) (by decide) ?_
  obtain ⟨k, hlt, hk⟩ := List.getElem_of_mem (a := lsRustDeallocSym)
    (l := libsignalSessionExterns) (by decide)
  exact rustDeallocExternWithStack_of_rustDealloc
    (ls_hook_ok (k := k) (by rw [List.getElem?_eq_getElem hlt, hk]) hdealloc)

end DropDecodeError3Placed

/-- Smart constructor for `SignedPortDepsPlaced` discharging `dropDecodeError3` (block `555`)
automatically from `hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A)`. -/
theorem SignedPortDepsPlaced.of_prost [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hVarint : subroutine_ok (lsProg_559 H) (blkPl_559).base
      (withLsCodeLoaded lsmpl (SpqrV1.Varint.decodeVarint2Spec A)))
    (hSkip : subroutine_ok (lsProg_546 H) (blkPl_546).base
      (withLsCodeLoaded lsmpl (SpqrV1.Varint.skipField3Spec A)))
    (hBytes : subroutine_ok (lsProg_558 H) (blkPl_558).base
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (SpqrV1.Prost.BytesMerge.bytesMerge3RawSpec A))) :
    SignedPortDepsPlaced A H :=
  ⟨hVarint, hSkip, hBytes, drop_decode_error_3_placed_ok hdealloc⟩

end Placed

end CryptoVerification.RecordCodecsBinary

