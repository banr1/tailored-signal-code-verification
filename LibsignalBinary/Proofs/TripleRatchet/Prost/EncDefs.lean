/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs

/-!
# Prost Varint and `SignalMessage` Encoding Specifications

Specifications relating the compiled Prost 0.14.4 encoding routines `encode_varint::<Vec<u8>>`
(`0x30a0`) and `<wire::SignalMessage as Message>::encoded_len` (`0x28f50`) to the pure protobuf
codec models `encodeVarint` and `(encode m).length`, together with the 112-byte memory layout
predicate `wireSignalMessageAt` for `libsignal_protocol::proto::wire::SignalMessage`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Prost

open Arm64 ProofLib CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec

/-! ## Symbol names -/

/-- `prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]`
(image offset `0x30a0`, 266 instructions). -/
abbrev encodeVarintName : String :=
  "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]"

/-- `<libsignal_protocol::proto::wire::SignalMessage as prost::message::Message>::encoded_len`
(image offset `0x28f50`, 100 instructions). -/
abbrev encodedLenName : String :=
  "<libsignal_protocol::proto::wire::SignalMessage as prost::message::Message>::encoded_len"

/-! ## Stack budgets -/

/-- Stack budget for `encode_varint::<Vec<u8>> [local#1]`: `0x30` local frame plus `doReserveStack`. -/
abbrev encodeVarintStack : Nat := 0x30 + doReserveStack

/-- Stack budget for `encode_varint::<Vec<u8>> [local#1]` with `doReserveStackX`. -/
abbrev encodeVarintStackX : Nat := 0x30 + doReserveStackX

/-- Stack budget for `<wire::SignalMessage as Message>::encoded_len`: `0x10` local frame (leaf under `WireLengthsFit`). -/
abbrev encodedLenStack : Nat := 0x10

/-! ## Varint length formula (`prost::encoding::encoded_len_varint`) -/

/-- Byte length (`1..10`) of the LEB128 varint encoding of `v : BitVec 64`, computed as
`(((clz (v ||| 1) ^^^ 0x3f) * 9 + 73) / 64)`. -/
def varintLen (v : BitVec 64) : Nat :=
  (((v ||| 1#64).clz ^^^ 0x3f#64).toNat * 9 + 73) / 64

/-! ## `libsignal_protocol::proto::wire::SignalMessage` layout (`wireSignalMessageAt`, 112 bytes) -/

/-- 24-byte `Option<Vec<u8>>` at `a` with pinned `(cap, ptr)`: niche `cap = noneCap` (`usize::MAX`)
when `none`, and `vecU8At A a pin.cap pin.ptr bs` when `some bs`. -/
def optVecU8At (A : RustAlloc) (pin : VecPin) (a : BitVec 64) :
    Option (List (BitVec 8)) → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 16
  | some bs => vecU8At A a pin.cap pin.ptr bs

/-- 8-byte `Option<u32>` at `a`: tag `0#32` with 4 uninitialized trailing bytes when `none`,
or tag `1#32` followed by `v` at `a + 4` when `some v`. -/
def optU32At (a : BitVec 64) : Option (BitVec 32) → SepProp
  | none => (a ↦₃₂ 0#32) ∗ memRegion (a + 4#64) 4
  | some v => (a ↦₃₂ 1#32) ∗ ((a + 4#64) ↦₃₂ v)

/-- Ghost `(cap, ptr)` pins for the four `Option<Vec<u8>>` fields of a 112-byte `wire::SignalMessage`. -/
structure WireSignalMessageGhost where
  /-- Pin for `ratchet_key: Option<Vec<u8>>` at `+0x00`. -/
  rk : VecPin
  /-- Pin for `ciphertext: Option<Vec<u8>>` at `+0x18`. -/
  ct : VecPin
  /-- Pin for `pq_ratchet: Option<Vec<u8>>` at `+0x30`. -/
  pq : VecPin
  /-- Pin for `addresses: Option<Vec<u8>>` at `+0x48`. -/
  addr : VecPin

/-- Memory layout of the 112-byte `libsignal_protocol::proto::wire::SignalMessage` at `a`
representing `m : ProtoSignalMessage` with `Vec` pins `g`:
* `a + 0x00`: `ratchet_key: Option<Vec<u8>>` (tag 1, 24 B);
* `a + 0x18`: `ciphertext: Option<Vec<u8>>` (tag 4, 24 B);
* `a + 0x30`: `pq_ratchet: Option<Vec<u8>>` (tag 5, 24 B);
* `a + 0x48`: `addresses: Option<Vec<u8>>` (tag 6, 24 B);
* `a + 0x60`: `counter: Option<u32>` (tag 2, 8 B);
* `a + 0x68`: `previous_counter: Option<u32>` (tag 3, 8 B). -/
def wireSignalMessageAt (A : RustAlloc) (g : WireSignalMessageGhost) (a : BitVec 64)
    (m : ProtoSignalMessage) : SepProp :=
  optVecU8At A g.rk a m.ratchetKey ∗
    optVecU8At A g.ct (a + 0x18#64) m.ciphertext ∗
    optVecU8At A g.pq (a + 0x30#64) m.pqRatchet ∗
    optVecU8At A g.addr (a + 0x48#64) m.addresses ∗
    optU32At (a + 0x60#64) m.counter ∗
    optU32At (a + 0x68#64) m.previousCounter

/-- Unpinned 112-byte `wire::SignalMessage` at `a`, existentially quantifying over `WireSignalMessageGhost`. -/
def wireSignalMessageOf (A : RustAlloc) (a : BitVec 64) (m : ProtoSignalMessage) : SepProp :=
  ∃∗ g : WireSignalMessageGhost, wireSignalMessageAt A g a m

/-- Size bound `(encode m).length < 2 ^ 64` ensuring no intermediate field-length partial sum in
`encoded_len` overflows `u64`, making `panic_const_add_overflow` unreachable. -/
def WireLengthsFit (m : ProtoSignalMessage) : Prop :=
  (encode m).length < 2 ^ 64

/-! ## `prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]` -/

/-- Ghost arguments of `encode_varint::<Vec<u8>> [local#1]`. -/
structure EncodeVarintGhost where
  /-- The `u64` value to encode (`x0`). -/
  val : BitVec 64
  /-- Address of `buf: &mut Vec<u8>` (`x1`, 24-byte `Vec` header). -/
  v : BitVec 64
  /-- Initial capacity word (`[v + 0x0]`). -/
  cap : BitVec 64
  /-- Initial buffer pointer (`[v + 0x8]`). -/
  ptr : BitVec 64
  /-- Initial contents of the `Vec<u8>` (`[v + 0x10] = bs.length`). -/
  bs : List (BitVec 8)

/-- Specification of `prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]` (`0x30a0`).
Under `x.bs.length + 10 < 2 ^ 62`, appends `encodeVarint x.val` (1..10 LEB128 bytes) to the `Vec<u8>`
at `x.v` with non-shrinking capacity (preserving `(x.cap, x.ptr)` whenever spare capacity suffices);
panics only on allocator failure in `do_reserve_and_handle`. -/
def encodeVarintSpec (A : RustAlloc) : Spec EncodeVarintGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.val ∧ s.readReg64 .x1 = x.v ∧
      (x.bs.length + 10 ≤ x.cap.toNat ∨ x.bs.length + 10 < 2 ^ 62)⌝ ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s.sp encodeVarintStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodeVarint x.val).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          vecU8At A x.v cap' ptr' (x.bs ++ encodeVarint x.val)) ∗
      A.pool ∗ stackAt s0.sp encodeVarintStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Variant of `encodeVarintSpec` with stack budget `encodeVarintStackX`. -/
def encodeVarintSpecX (A : RustAlloc) : Spec EncodeVarintGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.val ∧ s.readReg64 .x1 = x.v ∧
      (x.bs.length + 10 ≤ x.cap.toNat ∨ x.bs.length + 10 < 2 ^ 62)⌝ ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s.sp encodeVarintStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodeVarint x.val).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          vecU8At A x.v cap' ptr' (x.bs ++ encodeVarint x.val)) ∗
      A.pool ∗ stackAt s0.sp encodeVarintStackX
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-! ## `<libsignal_protocol::proto::wire::SignalMessage as prost::message::Message>::encoded_len` -/

/-- Ghost arguments of `<wire::SignalMessage as Message>::encoded_len`. -/
structure EncodedLenGhost where
  /-- Pointer to `&wire::SignalMessage` (`x0`, 112 bytes). -/
  a : BitVec 64
  /-- `Vec` pins of the four `Option<Vec<u8>>` fields. -/
  g : WireSignalMessageGhost
  /-- The protobuf message value. -/
  m : ProtoSignalMessage

/-- Specification of `<libsignal_protocol::proto::wire::SignalMessage as prost::message::Message>::encoded_len` (`0x28f50`).
Under `WireLengthsFit x.m`, returns `(encode x.m).length` in `x0` without panicking while preserving
`wireSignalMessageAt A x.g x.a x.m` and the execution trace. -/
def encodedLenSpec (A : RustAlloc) : Spec EncodedLenGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a ∧ WireLengthsFit x.m⌝ ∗
      wireSignalMessageAt A x.g x.a x.m ∗ stackAt s.sp encodedLenStack
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 (encode x.m).length ∧ sf.trace = s0.trace⌝ ∗
      wireSignalMessageAt A x.g x.a x.m ∗ stackAt s0.sp encodedLenStack

/-! ## Target `subroutine_ok` propositions -/

/-- Synonym for `tripleRatchetProgAtExt b abs` parameterized uniformly over `(C, ctl, parse)`. -/
noncomputable abbrev tripleRatchetProgAtP (b : BitVec 64) (_C : Crypto) (_ctl : BitVec 64)
    (_parse : UuidParser) (abs : String → Option (State → State)) : Program :=
  tripleRatchetProgAtExt b abs

/-- `prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]` meets
`encodeVarintSpec` on `tripleRatchetProgAtExt`. -/
def EncodeVarintOkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr encodeVarintName)
    (encodeVarintSpec A)

/-- `prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]` meets
`(encodeVarintSpecX A).inImage img` on `tripleRatchetProgAtExt img.base ext`. -/
def EncodeVarintOkExtX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr encodeVarintName)
    ((encodeVarintSpecX A).inImage img)

/-- `prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]` meets
`encodeVarintSpec` on `trTrapProgAt`. -/
def EncodeVarintOk_trap (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt b C abs) ((trTrapProgAt b C abs).fnAddr encodeVarintName)
    (encodeVarintSpec A)

/-- `prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]` meets
`encodeVarintSpec` on `tripleRatchetProgAt`. -/
def EncodeVarintOk (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr encodeVarintName)
    (encodeVarintSpec A)

/-- `<libsignal_protocol::proto::wire::SignalMessage as prost::message::Message>::encoded_len`
meets `encodedLenSpec` on `tripleRatchetProgAtExt`. -/
def EncodedLenOkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr encodedLenName)
    (encodedLenSpec A)

/-- `<libsignal_protocol::proto::wire::SignalMessage as prost::message::Message>::encoded_len`
meets `encodedLenSpec` on `trTrapProgAt`. -/
def EncodedLenOk_trap (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt b C abs) ((trTrapProgAt b C abs).fnAddr encodedLenName)
    (encodedLenSpec A)

/-- `<libsignal_protocol::proto::wire::SignalMessage as prost::message::Message>::encoded_len`
meets `encodedLenSpec` on `tripleRatchetProgAt`. -/
def EncodedLenOk (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr encodedLenName)
    (encodedLenSpec A)

end CryptoVerification.LibsignalTripleRatchet.Prost
