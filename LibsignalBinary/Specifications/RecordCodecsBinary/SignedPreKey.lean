/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.RecordCodecsBinary

/-!
# Binary Specification for `decode_kyber_pre_key` / `decode_signed_pre_key`

**Checked by Lean.** Result layouts (`signedPreKeyStructAt`, `kyberPreKeyResultAt`,
`signedPreKeyResultAt`) and ARM64 Hoare specifications (`decodeKyberPreKeySpec`,
`decodeSignedPreKeySpec`) for `libsignal_cli::stores::decode_kyber_pre_key` in the `libsignal-cli`
crate against `KyberPreKeyRecord.deserialize` and `SignedPreKeyRecord.deserialize`
(`RecordCodecs/Proto.lean`).

Both record types wrap `SignedPreKeyRecordStructure` and share `GenericSignedPreKey::deserialize`,
which LLVM merges into `decode_kyber_pre_key` (`x0` output pointer, `(x1, x2)` non-empty input
slice).
-/

@[expose] public section

namespace CryptoVerification.RecordCodecsBinary

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.RecordCodecs

/-! ## Entry point -/

/-- `libsignal_cli::stores::decode_kyber_pre_key` (`stores.rs:183–186`), which LLVM also uses
for `decode_signed_pre_key` (`stores.rs:173–176`). -/
abbrev decodeKyberPreKeyName : String :=
  "libsignal_cli::stores::decode_kyber_pre_key"

/-! ## Layouts -/

/-- **A `SignedPreKeyRecordStructure` at `a` (88 bytes)**: `public_key: Vec<u8>` @0,
`private_key: Vec<u8>` @0x18, `signature: Vec<u8>` @0x30, `timestamp: u64` @0x48, `id: u32`
@0x50, 4 bytes padding. Each `Vec` is owned, with any capacity and buffer (`vecU8`'s
`cap < 2^63` keeps word 0 off the `Err` niche `errTag`). -/
def signedPreKeyStructAt (A : RustAlloc) (a : BitVec 64) (m : SignedPreKeyRecordStructure) :
    SepProp :=
  vecU8 A a m.publicKey ∗ vecU8 A (a + 0x18#64) m.privateKey ∗ vecU8 A (a + 0x30#64) m.signature ∗
    ((a + 0x48#64) ↦₆₄ m.timestamp) ∗ ((a + 0x50#64) ↦₃₂ m.id) ∗ memRegion (a + 0x54#64) 4

/-- `Result<KyberPreKeyRecord, SignalProtocolError>` at `r` (88 bytes): `Ok` = the record's
structure in place; `Err` = `errResultAt` (word 0 `errTag`, the SPE at +8, the rest
unspecified). -/
def kyberPreKeyResultAt (A : RustAlloc) (r : BitVec 64) :
    Except SignalProtocolError KyberPreKeyRecord → SepProp
  | .ok rec => signedPreKeyStructAt A r rec.signedPreKey
  | .error e => errResultAt A [] 88 r e

/-- `Result<SignedPreKeyRecord, SignalProtocolError>` at `r` (88 bytes): the same layout as
`kyberPreKeyResultAt`. -/
def signedPreKeyResultAt (A : RustAlloc) (r : BitVec 64) :
    Except SignalProtocolError SignedPreKeyRecord → SepProp
  | .ok rec => signedPreKeyStructAt A r rec.signedPreKey
  | .error e => errResultAt A [] 88 r e

/-! ## Binding specs -/

/-- **The binding spec of `decode_kyber_pre_key`** (as `KyberPreKeyRecord::deserialize`):
the 88 bytes at `x0` hold `KyberPreKeyRecord.deserialize bytes` (every prost decode error is
`InvalidProtobufEncoding`), the input bytes (`x1`, `x2`) are given back, and every intermediate
allocation is freed or moved into the result. The input is never empty (`0 < x.bytes.length`):
`record` (`stores.rs:163–169`) maps an empty file to `Ok(None)` and decodes only nonempty bytes,
and the compiled code relies on it (LLVM folded the inner decoder's empty-input branch,
`SignedPreKeyDecode.signedDecode_empty_disproof`). The only panic is an allocation failure
(`bytes::merge`'s `Vec` growth); malformed input never panics. The ghost's `ret` is the `x0`
output pointer (not an `x8` sret). -/
def decodeKyberPreKeySpec (A : RustAlloc) (img : Obj.Image) : Spec DecodeGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.bytesA ∧
          (s.readReg64 .x2).toNat = x.bytes.length ∧
          0 < x.bytes.length ∧ x.bytes.length < 2 ^ 32⌝ ∗
          (x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 88 ∗ stackAt s.sp smallRootStack ∗ A.pool
      post := fun x s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗ kyberPreKeyResultAt A x.ret (KyberPreKeyRecord.deserialize x.bytes) ∗
          (x.bytesA ↦ₛ x.bytes) ∗ stackAt s0.sp smallRootStack ∗ A.pool
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

/-- **The binding spec of `decode_kyber_pre_key` called as `decode_signed_pre_key`**
(`SignedPreKeyRecord::deserialize`): `decodeKyberPreKeySpec` with the signed model. -/
def decodeSignedPreKeySpec (A : RustAlloc) (img : Obj.Image) : Spec DecodeGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.bytesA ∧
          (s.readReg64 .x2).toNat = x.bytes.length ∧
          0 < x.bytes.length ∧ x.bytes.length < 2 ^ 32⌝ ∗
          (x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 88 ∗ stackAt s.sp smallRootStack ∗ A.pool
      post := fun x s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗
          signedPreKeyResultAt A x.ret (SignedPreKeyRecord.deserialize x.bytes) ∗
          (x.bytesA ↦ₛ x.bytes) ∗ stackAt s0.sp smallRootStack ∗ A.pool
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

end CryptoVerification.RecordCodecsBinary
