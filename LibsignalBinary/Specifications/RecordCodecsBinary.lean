/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalTripleRatchet
public import LibsignalBinary.Specifications.RecordCodecs

/-!
# Binary Specifications for Key-Record Codecs (`RecordCodecsBinary`)

**Checked by Lean.** Separation-logic result layouts (`preKeyResultAt`, `identityKeyPairResultAt`,
`identityKeyResultAt`) and ARM64 Hoare specifications (`preKeyDeserializeSpec`,
`identityKeyPairTryFromSpec`, `identityKeyDecodeSpec`) relating `<PreKeyRecord>::deserialize`,
`<IdentityKeyPair as TryFrom<&[u8]>>::try_from`, and `<IdentityKey>::decode` to the models in
`RecordCodecs.lean`, along with serialization layout helpers (`vecOkResultAt`, `boxU8Owned`).
-/

@[expose] public section

namespace CryptoVerification.RecordCodecsBinary

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.RecordCodecs

/-! ## Entry points -/

/-- `<PreKeyRecord>::deserialize` (`protocol/src/state/prekey.rs:44–49`). -/
abbrev preKeyDeserializeName : String :=
  "<libsignal_protocol::state::prekey::PreKeyRecord>::deserialize"

/-- `<IdentityKeyPair as TryFrom<&[u8]>>::try_from` (`protocol/src/identity_key.rs:181–192`). -/
abbrev identityKeyPairTryFromName : String :=
  "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from"

/-- `<IdentityKey>::decode` (`protocol/src/identity_key.rs:52–55`). -/
abbrev identityKeyDecodeName : String :=
  "<libsignal_protocol::identity_key::IdentityKey>::decode"

/-! ## Layouts -/

/-- **A `PreKeyRecord` at `a` (56 bytes)**: `public_key: Vec<u8>` @0, `private_key: Vec<u8>` @0x18,
`id: u32` @0x30, 4 bytes padding. Each `Vec` is owned, with any capacity and buffer (prost's
`bytes::merge` replaces the contents and may keep a larger buffer); `vecU8At`'s `cap < 2^63`
keeps word 0 off the `Err` niche `errTag`. -/
def preKeyRecordAt (A : RustAlloc) (a : BitVec 64) (r : PreKeyRecord) : SepProp :=
  vecU8 A a r.preKey.publicKey ∗ vecU8 A (a + 0x18#64) r.preKey.privateKey ∗
    ((a + 0x30#64) ↦₃₂ r.preKey.id) ∗ memRegion (a + 0x34#64) 4

/-- `Result<PreKeyRecord, SignalProtocolError>` at `r` (56 bytes): `Ok` = a fresh owned record at
`r`; `Err` = `errResultAt` (word 0 `errTag`, the SPE at +8). -/
def preKeyResultAt (A : RustAlloc) (r : BitVec 64) :
    Except SignalProtocolError PreKeyRecord → SepProp
  | .ok rec => preKeyRecordAt A r rec
  | .error e => errResultAt A [] 56 r e

/-- `Result<IdentityKeyPair, SignalProtocolError>` at `r` (72 bytes): `Ok` = tag byte `0`, the
public key bytes @1, the private key bytes @0x21, 7 bytes unspecified; `Err` = tag byte `1`,
7 bytes unspecified, the SPE @8, 16 bytes unspecified. -/
def identityKeyPairResultAt (A : RustAlloc) (r : BitVec 64) :
    Except SignalProtocolError IdentityKeyPair → SepProp
  | .ok kp =>
    (r ↦₈ 0#8) ∗ ((r + 1#64) ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
      ((r + 0x21#64) ↦ₛ kp.privateKey.bytes.toList) ∗ memRegion (r + 0x41#64) 7
  | .error e =>
    (r ↦₈ 1#8) ∗ memRegion (r + 1#64) 7 ∗ speAt A [] (r + 8#64) e ∗ memRegion (r + 0x38#64) 16

/-- `Result<IdentityKey, SignalProtocolError>` at `r` (48 bytes): `Ok` = `okTagVec` (`-2`), the 32
key bytes @8, 8 bytes unspecified; `Err` = the SPE in place. -/
def identityKeyResultAt (A : RustAlloc) (r : BitVec 64) :
    Except SignalProtocolError IdentityKey → SepProp
  | .ok ik =>
    (r ↦₆₄ okTagVec) ∗ ((r + 8#64) ↦ₛ ik.publicKey.bytes.toList) ∗ memRegion (r + 0x28#64) 8
  | .error e => speAt A [] r e

/-! ## Binding specs -/

/-- Ghost of a decode call: the input bytes (`x0`, `x1`) and the sret (`x8`). -/
structure DecodeGhost where
  bytesA : BitVec 64
  bytes : List (BitVec 8)
  ret : BitVec 64

/-- **The binding spec of `PreKeyRecord::deserialize`**: the sret holds
`PreKeyRecord.deserialize bytes` (every prost decode error is `InvalidProtobufEncoding`; the empty
input is the default record), the input bytes are given back, and every intermediate allocation is
freed or moved into the result. The only panic is an allocation failure (`bytes::merge`'s `Vec`
growth); malformed input never panics. -/
def preKeyDeserializeSpec (A : RustAlloc) (img : Obj.Image) : Spec DecodeGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.bytesA ∧ (s.readReg64 .x1).toNat = x.bytes.length ∧
          x.bytes.length < 2 ^ 32 ∧ s.readReg64 .x8 = x.ret⌝ ∗
          (x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 56 ∗ stackAt s.sp smallRootStack ∗ A.pool
      post := fun x s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗ preKeyResultAt A x.ret (PreKeyRecord.deserialize x.bytes) ∗
          (x.bytesA ↦ₛ x.bytes) ∗ stackAt s0.sp smallRootStack ∗ A.pool
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

/-- **The binding spec of `<IdentityKeyPair as TryFrom<&[u8]>>::try_from`**: the sret holds
`IdentityKeyPair.tryFrom bytes` (prost decode, then `PublicKey::deserialize` of field 1, then
`PrivateKey::deserialize` of field 2, in this order), the input bytes are given back, and both
decoded `Vec`s are freed. `logOff img`: `PublicKey::try_from` logs only when logging is enabled. -/
def identityKeyPairTryFromSpec (A : RustAlloc) (img : Obj.Image) : Spec DecodeGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.bytesA ∧ (s.readReg64 .x1).toNat = x.bytes.length ∧
          x.bytes.length < 2 ^ 32 ∧ s.readReg64 .x8 = x.ret⌝ ∗
          (x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 72 ∗ logOff img ∗
          stackAt s.sp smallRootStack ∗ A.pool
      post := fun x s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗
          identityKeyPairResultAt A x.ret (IdentityKeyPair.tryFrom x.bytes) ∗
          (x.bytesA ↦ₛ x.bytes) ∗ logOff img ∗ stackAt s0.sp smallRootStack ∗ A.pool
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

/-- **The binding spec of `IdentityKey::decode`**, for any input: the sret holds
`decodeIdentityKey bytes` (`NoKeyTypeIdentifier` on empty input, `BadKeyType t` on a type byte
other than `0x05`, `BadKeyLength n` on fewer than 33 bytes, else the key; trailing bytes are
accepted). No allocation and no panic (`onPanic` is the default `False`); its own 0x60-byte frame
is the only stack it uses. -/
def identityKeyDecodeSpec (A : RustAlloc) (img : Obj.Image) : Spec DecodeGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.bytesA ∧ (s.readReg64 .x1).toNat = x.bytes.length ∧
          s.readReg64 .x8 = x.ret⌝ ∗
          (x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 48 ∗ logOff img ∗ stackAt s.sp 0x60
      post := fun x s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗ identityKeyResultAt A x.ret (decodeIdentityKey x.bytes) ∗
          (x.bytesA ↦ₛ x.bytes) ∗ logOff img ∗ stackAt s0.sp 0x60 }
    img

/-! ## Serialization layout helpers -/

/-- `Result<Vec<u8>, SignalProtocolError>` at `r` (48 bytes) holding `Ok bs`: `okTagVec` @0, an
owned `Vec<u8>` @8, 16 bytes unspecified (the `Ok` arm of `vecResultAt`). -/
def vecOkResultAt (A : RustAlloc) (r : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  vecResultAt A r (.ok bs)

/-- The heap part of an owned `Box<[u8]>` with pointer `ptr` holding `bs` (`boxU8At` without its
16-byte header): a live block of exactly `bs.length` bytes with alignment 1, or, if `bs` is empty,
a dangling non-null pointer and no block. -/
def boxU8Owned (A : RustAlloc) (ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜ptr ≠ 0 ∧ bs.length < 2 ^ 63⌝ ∗ (if bs = [] then emp else A.live ptr bs.length 1 ∗ (ptr ↦ₛ bs))

end CryptoVerification.RecordCodecsBinary
