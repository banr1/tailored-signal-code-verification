/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Chain.Defs

/-!
# Specifications for `spqr::chain_from_version_negotiation` (`0x545e4`)

Memory layouts (`optChainParamsPBAt`, `versionNegotiationPBAt`, `chainErrorAt`, `chainResultAt`)
and contracts (`chainFromVersionNegotiationSpecX`, `chainFromVersionNegotiationSpecExt`) for
`spqr::chain_from_version_negotiation` (`0x545e4`, 18 instructions).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation

open Arm64 ProofLib
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SpqrV1.ChainProofs

/-! ## Symbol Name, Niche Constant, and Stack Budget -/

abbrev chainFromVersionNegotiationName : String :=
  "spqr::chain_from_version_negotiation"

/-- Niche value `0xFFFFFFFFFFFFFFFF#64` (`usize::MAX`) used in `Vec.cap` / `VecDeque.cap` for
`Option::None` and `Result::Err`. -/
abbrev noneCap : BitVec 64 := 0xFFFFFFFFFFFFFFFF#64

/-- Stack budget for `spqr::chain_from_version_negotiation` (`0x545e4`):
no stack frame of its own; tail-calls `<spqr::chain::Chain>::new` (`0x5fea4`),
which uses `chainNewStackX` (`224 + extHookStack` bytes). -/
abbrev chainFromVersionNegotiationStackX : Nat := chainNewStackX

/-! ## Protobuf Layouts (`Option<ChainParams>` and `VersionNegotiation`) -/

/-- `Option<spqr::proto::pq_ratchet::ChainParams>` at `a` (12 bytes, align 4):
- `none`: `(a ↦₃₂ 0#32) ∗ memRegion (a + 4#64) 8`
- `some cp`: `(a ↦₃₂ 1#32) ∗ ((a + 4#64) ↦₃₂ cp.maxJump) ∗ ((a + 8#64) ↦₃₂ cp.maxOooKeys)` -/
def optChainParamsPBAt (a : BitVec 64) : Option ChainParamsPB → SepProp
  | none => (a ↦₃₂ 0#32) ∗ memRegion (a + 4#64) 8
  | some cp =>
    (a ↦₃₂ 1#32) ∗ ((a + 4#64) ↦₃₂ cp.maxJump) ∗ ((a + 8#64) ↦₃₂ cp.maxOooKeys)

/-- `spqr::proto::pq_ratchet::pq_ratchet_state::VersionNegotiation` at `a` (48 bytes = `0x30`, align 8):
- `+0x00..+0x18` (24B): `auth_key: Vec<u8>` (`vecU8At A a pin.cap pin.ptr v.authKey`)
- `+0x18..+0x24` (12B): `chain_params: Option<ChainParams>` (`optChainParamsPBAt (a + 0x18#64) v.chainParams`)
- `+0x24..+0x28` (4B): `direction: i32` (`(a + 0x24#64) ↦₃₂ v.direction`)
- `+0x28..+0x2c` (4B): `min_version: i32` (`(a + 0x28#64) ↦₃₂ v.minVersion`)
- `+0x2c..+0x30` (4B): trailing padding (`memRegion (a + 0x2c#64) 4`) -/
def versionNegotiationPBAt (A : RustAlloc) (pin : VecPin) (a : BitVec 64)
    (v : VersionNegotiationPB) : SepProp :=
  vecU8At A a pin.cap pin.ptr v.authKey ∗
    optChainParamsPBAt (a + 0x18#64) v.chainParams ∗
    ((a + 0x24#64) ↦₃₂ v.direction) ∗
    ((a + 0x28#64) ↦₃₂ v.minVersion) ∗
    memRegion (a + 0x2c#64) 4

/-! ## `Result<Chain, spqr::Error>` (`88` bytes) Representation -/

/-- Discriminant byte written at `out + 8` of `Result<Chain, spqr::Error>` for `Error`
(`src/lib.rs:96–130`):
- `0#8` = `Error::StateDecode`
- `15#8` = `Error::ChainNotAvailable` -/
def spqrErrorTag : Error → BitVec 8
  | .stateDecode => 0#8
  | .notImplemented => 1#8
  | .msgDecode => 2#8
  | .macVerifyFailed => 3#8
  | .epochOutOfRange _ => 4#8
  | .encodingDecoding => 5#8
  | .serialization => 6#8
  | .versionMismatch => 7#8
  | .minimumVersion => 8#8
  | .keyJump _ _ => 9#8
  | .keyTrimmed _ => 10#8
  | .keyAlreadyRequested _ => 11#8
  | .erroneousDataReceived => 12#8
  | .sendKeyEpochDecreased _ _ => 13#8
  | .invalidParams _ => 14#8
  | .chainNotAvailable => 15#8

/-- Error variant of `Result<Chain, spqr::Error>` at `out` (88 bytes):
- `+0x00..+0x08` (8B): niche tag `0xFFFFFFFFFFFFFFFF#64` (`noneCap` in `links.cap`)
- `+0x08..+0x20` (24B): `spqr::Error` payload (`q0 : BitVec 128` at `+0x08` whose low byte
  `BitVec.truncate 8 q0` is `spqrErrorTag err`, followed by `w2 : BitVec 64` at `+0x18`)
- `+0x20..+0x58` (56B): remaining uninitialized bytes (`memRegion (out + 0x20#64) 56`) -/
def chainErrorAt (out : BitVec 64) (err : Error) : SepProp :=
  ∃∗ q0 : BitVec 128, ∃∗ w2 : BitVec 64,
    ⌜BitVec.truncate 8 q0 = spqrErrorTag err⌝ ∗
    (out ↦₆₄ noneCap) ∗
    ((out + 0x08#64) ↦₁₂₈ q0) ∗
    ((out + 0x18#64) ↦₆₄ w2) ∗
    memRegion (out + 0x20#64) 56

/-- Representation of `Except Error Chain` (`Result<Chain, spqr::Error>`, 88 bytes) at `out`:
- `.ok ch`: `chainRepr A out ch` (where `[out + 0x00] = g.linksCap < 2^63`, hence `≠ noneCap`)
- `.error err`: `chainErrorAt out err` (where `[out + 0x00] = noneCap = 0xFFFFFFFFFFFFFFFF#64`) -/
def chainResultAt (A : RustAlloc) (out : BitVec 64) : Except Error Chain → SepProp
  | .ok ch => chainRepr A out ch
  | .error err => chainErrorAt out err

/-! ## Specification of `spqr::chain_from_version_negotiation` (`0x545e4`, 18 insns) -/

/-- Ghost arguments of `spqr::chain_from_version_negotiation` (`0x545e4`):
- `out`: 88-byte `Result<Chain, Error>` return pointer in `x8`
- `vPtr`: `&VersionNegotiationPB` pointer in `x0`
- `pin`: `(cap, ptr)` pin of `v.authKey`
- `v`: pure `VersionNegotiationPB` value -/
structure ChainFromVersionNegotiationCall where
  out : BitVec 64
  vPtr : BitVec 64
  pin : VecPin
  v : VersionNegotiationPB

/-- Contract of `spqr::chain_from_version_negotiation` (`0x545e4`, 18 instructions) at
`chainFromVersionNegotiationStackX`, related to `chainFromVersionNegotiation hkdf x.v`. -/
def chainFromVersionNegotiationSpecX (hkdf : HkdfFn) (A : RustAlloc) :
    Spec ChainFromVersionNegotiationCall where
  pre := fun x s =>
    ⌜s.readReg64 .x8 = x.out ∧
      s.readReg64 .x0 = x.vPtr⌝ ∗
    memRegion x.out 88 ∗
    versionNegotiationPBAt A x.pin x.vPtr x.v ∗
    A.pool ∗
    stackAt s.sp chainFromVersionNegotiationStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    chainResultAt A x.out (chainFromVersionNegotiation hkdf x.v) ∗
    versionNegotiationPBAt A x.pin x.vPtr x.v ∗
    A.pool ∗
    stackAt s0.sp chainFromVersionNegotiationStackX
  onPanic := fun _ s0 sf =>
    ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Callee-contract predicate for `spqr::chain_from_version_negotiation` (`0x545e4`). -/
def ChainFromVersionNegotiationOkX (img : Obj.Image) (hkdf : HkdfFn) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr chainFromVersionNegotiationName)
    ((chainFromVersionNegotiationSpecX hkdf A).inImage img)

/-! ## Contract-Backed (`*Ext`) Specifications (`chainFromVersionNegotiationStackExt = 17840` B) -/

/-- Stack budget for `spqr::chain_from_version_negotiation` under `CliExternsOk` (`chainNewStackExt = 17840` B). -/
abbrev chainFromVersionNegotiationStackExt : Nat := chainNewStackExt

/-- Contract-backed spec of `spqr::chain_from_version_negotiation` (`0x545e4`, 18 instructions) at
`chainFromVersionNegotiationStackExt` (`17840` B). No extra `ikmRO` precondition is needed since
`v.authKey` is a RW `Vec<u8>`. -/
def chainFromVersionNegotiationSpecExt (hkdf : HkdfFn) (A : RustAlloc) :
    Spec ChainFromVersionNegotiationCall where
  pre := fun x s =>
    ⌜s.readReg64 .x8 = x.out ∧
      s.readReg64 .x0 = x.vPtr⌝ ∗
    memRegion x.out 88 ∗
    versionNegotiationPBAt A x.pin x.vPtr x.v ∗
    A.pool ∗
    stackAt s.sp chainFromVersionNegotiationStackExt
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    chainResultAt A x.out (chainFromVersionNegotiation hkdf x.v) ∗
    versionNegotiationPBAt A x.pin x.vPtr x.v ∗
    A.pool ∗
    stackAt s0.sp chainFromVersionNegotiationStackExt
  onPanic := fun _ s0 sf =>
    ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Contract-backed callee-contract predicate for `spqr::chain_from_version_negotiation` (`0x545e4`). -/
def ChainFromVersionNegotiationOkExt (img : Obj.Image) (hkdf : HkdfFn) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr chainFromVersionNegotiationName)
    ((chainFromVersionNegotiationSpecExt hkdf A).inImage img)

end CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation
