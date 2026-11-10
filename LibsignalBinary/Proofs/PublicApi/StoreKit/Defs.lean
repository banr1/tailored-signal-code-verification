/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.CodeLayout
public import LibsignalBinary.Specifications.LibsignalPublicApi
public import LibsignalBinary.Proofs.PublicApi.StoreSession.StoreCallSite -- shake: keep

/-!
# In-Image `async_trait` Store Shim and Future Poll Specifications

Specifications for the in-image `load_session`, `save_identity`, and `is_trusted_identity`
`async_trait` shims (`0x42e0c`, `0x42f08`, `0x42f68`) and future polls (`0x42a48`, `0x42c04`,
`0x42c8c`) shared by `MessageDecrypt` and `MessageEncrypt`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.StoreKit

open Arm64 ProofLib CryptoVerification.RustHeap CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoGames CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalPublicApi.StoreSession

/-! ## Stack Budgets -/

/-- Stack budget of the `load_session` shim (`allocHookStack + 32`). -/
abbrev loadSessionShimStack : Nat := allocHookStack + 32
/-- Stack budget of the `save_identity` and `is_trusted_identity` shims (`allocHookStack + 48`). -/
abbrev identityShimStack : Nat := allocHookStack + 48
/-- Stack budget of the `load_session` poll (`storeHookStack + 0x310`). -/
abbrev loadSessionPollStack : Nat := storeHookStack + 0x310
/-- Stack budget of the `save_identity` and `is_trusted_identity` polls (`storeHookStack + 32`). -/
abbrev identityPollStack : Nat := storeHookStack + 32

/-! ## Future Shims -/

/-- Arguments to the `load_session` shim: `self` (`x0`) and `addrA` (`x1`). -/
structure LoadShimCall where
  self : BitVec 64
  addrA : BitVec 64

/-- Contract of the `load_session` shim (`0x42e0c`): allocates a 24-byte future box
`[self, addrA, state = 0]` and returns `(box, b + 0x4dae0)` in `(x0, x1)`, panicking only on
allocation failure. -/
def loadSessionShimSpec (A : RustAlloc) (b : BitVec 64) : Spec LoadShimCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x1 = x.addrA⌝ ∗ A.pool ∗
      stackAt s.sp loadSessionShimStack
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x1 = b + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair::{closure#0}") - 16) ∧ sf.readReg64 .x0 ≠ 0#64 ∧
      (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
      A.live (sf.readReg64 .x0) 24 8 ∗
      (sf.readReg64 .x0 ↦₆₄ x.self) ∗ ((sf.readReg64 .x0 + 8#64) ↦₆₄ x.addrA) ∗
      ((sf.readReg64 .x0 + 0x10#64) ↦₈ 0#8) ∗ memRegion (sf.readReg64 .x0 + 0x11#64) 7 ∗
      A.pool ∗ stackAt s0.sp loadSessionShimStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Arguments to an identity-store shim: `self` (`x0`), `addrA` (`x1`), and `keyA` (`x2`). -/
structure IdentityShimCall where
  self : BitVec 64
  addrA : BitVec 64
  keyA : BitVec 64

/-- Contract of the `save_identity` shim (`0x42f08`): allocates a 32-byte future box
`[self, addrA, keyA, state = 0]` and returns `(box, b + 0x4db40)` in `(x0, x1)`. -/
def saveIdentityShimSpec (A : RustAlloc) (b : BitVec 64) : Spec IdentityShimCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x1 = x.addrA ∧ s.readReg64 .x2 = x.keyA⌝ ∗
      A.pool ∗ stackAt s.sp identityShimStack
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x1 = b + bv% (ls_xref% (ls_off% "<libsignal_protocol::protocol::PlaintextContent as core::convert::From<libsignal_protocol::protocol::DecryptionErrorMessage>>::from" + 600) (ls_off% "<libsignal_protocol::protocol::PlaintextContent as core::convert::From<libsignal_protocol::protocol::DecryptionErrorMessage>>::from" + 604) + 8) ∧ sf.readReg64 .x0 ≠ 0#64 ∧
      (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
      A.live (sf.readReg64 .x0) 32 8 ∗
      (sf.readReg64 .x0 ↦₆₄ x.self) ∗ ((sf.readReg64 .x0 + 8#64) ↦₆₄ x.addrA) ∗
      ((sf.readReg64 .x0 + 0x10#64) ↦₆₄ x.keyA) ∗ ((sf.readReg64 .x0 + 0x18#64) ↦₈ 0#8) ∗
      memRegion (sf.readReg64 .x0 + 0x19#64) 7 ∗ A.pool ∗ stackAt s0.sp identityShimStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Contract of the `is_trusted_identity` shim (`0x42f68`): allocates a 32-byte future box
`[self, addrA, keyA, state = 0, dir]` and returns `(box, b + 0x4db60)` in `(x0, x1)`. -/
def isTrustedShimSpec (A : RustAlloc) (b : BitVec 64) : Spec (IdentityShimCall × BitVec 8) where
  pre := fun (x, d) s =>
    ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x1 = x.addrA ∧ s.readReg64 .x2 = x.keyA ∧
      (s.readReg64 .x3).setWidth 8 = d⌝ ∗ A.pool ∗ stackAt s.sp identityShimStack
  post := fun (x, d) s0 sf =>
    ⌜sf.readReg64 .x1 = b + bv% (ls_xref% (ls_off% "<libsignal_protocol::proto::fingerprint::CombinedFingerprints as core::fmt::Debug>::fmt" + 60) (ls_off% "<libsignal_protocol::proto::fingerprint::CombinedFingerprints as core::fmt::Debug>::fmt" + 64) + 16) ∧ sf.readReg64 .x0 ≠ 0#64 ∧
      (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
      A.live (sf.readReg64 .x0) 32 8 ∗
      (sf.readReg64 .x0 ↦₆₄ x.self) ∗ ((sf.readReg64 .x0 + 8#64) ↦₆₄ x.addrA) ∗
      ((sf.readReg64 .x0 + 0x10#64) ↦₆₄ x.keyA) ∗ ((sf.readReg64 .x0 + 0x18#64) ↦₈ 0#8) ∗
      ((sf.readReg64 .x0 + 0x19#64) ↦₈ d) ∗
      memRegion (sf.readReg64 .x0 + 0x1a#64) 6 ∗ A.pool ∗ stackAt s0.sp identityShimStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-! ## Future Polls -/

/-- Shared `ApplicationCallbackError("store hook", Box<HookStoreError>)` payload tail at
`out + 0x10 .. out + 0x28` written by the `save_identity` and `is_trusted_identity` polls. -/
def errTailAt (b out : BitVec 64) : SepProp :=
  ((out + 0x10#64) ↦₆₄ 10#64) ∗ ((out + 0x18#64) ↦₆₄ 1#64) ∗
    ((out + 0x20#64) ↦₆₄ (b + bv% (ls_xref% (ls_off% "<libsignal_protocol::fingerprint::ScannableFingerprint>::serialize" + 620) (ls_off% "<libsignal_protocol::fingerprint::ScannableFingerprint>::serialize" + 624) + 16))) ∗ ((b + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))) ↦ᵣ storeHookStr)

/-- Ghost state of a `load_session` future poll: box `fut` (`x0`), 368-byte `sret` `out` (`x8`),
and remote address. -/
structure LoadPollCall where
  fut : BitVec 64
  out : BitVec 64
  addrA : BitVec 64
  addr : AddrGhost

/-- 368-byte `Poll<Result<Option<SessionRecord>, SignalProtocolError>>` layout at `out`,
parameterized by the loaded-record predicate `Scope`: `Ok(Some r)` stores `sessionRecordAt`,
`Ok(None)` stores word 0 = `-1`, and `Err(())` stores word 0 = `-2` followed by
`ApplicationCallbackError`. -/
def loadPollOutAtS (Scope : SessionRecord (List (BitVec 8)) → Prop) (A : RustAlloc)
    (b out : BitVec 64) :
    Except Unit (Option (SessionRecord (List (BitVec 8)))) → SepProp
  | .ok (some r) => ⌜Scope r⌝ ∗ ∃∗ g : RecordGhost, sessionRecordAt A out g r
  | .ok none => (out ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ memRegion (out + 8#64) 360
  | .error () =>
    (out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ ((out + 8#64) ↦₆₄ 0x800000000000001A#64) ∗
      ((out + 0x10#64) ↦₆₄ (b + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}")))) ∗ ((out + 0x18#64) ↦₆₄ 10#64) ∗
      ((out + 0x20#64) ↦₆₄ 1#64) ∗ ((out + 0x28#64) ↦₆₄ (b + bv% (ls_xref% (ls_off% "<libsignal_protocol::fingerprint::ScannableFingerprint>::serialize" + 620) (ls_off% "<libsignal_protocol::fingerprint::ScannableFingerprint>::serialize" + 624) + 16))) ∗
      ((b + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))) ↦ᵣ storeHookStr) ∗
      memRegion (out + 0x30#64) 320

/-- `loadPollOutAtS` specialized to `RecordInScope`. -/
abbrev loadPollOutAt (A : RustAlloc) (b out : BitVec 64) :
    Except Unit (Option (SessionRecord (List (BitVec 8)))) → SepProp :=
  loadPollOutAtS RecordInScope A b out

/-- Contract of the `load_session` future poll (`0x42a48`), parameterized by `Scope`. -/
def loadSessionPollSpecS (Scope : SessionRecord (List (BitVec 8)) → Prop) (A : RustAlloc)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) (b : BitVec 64) :
    Spec LoadPollCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out⌝ ∗
      ((x.fut + 8#64) ↦₆₄ x.addrA) ∗ ((x.fut + 0x10#64) ↦₈ 0#8) ∗ memRegion x.out 368 ∗
      protocolAddressAt A x.addr x.addrA ∗ A.pool ∗ stackAt s.sp loadSessionPollStack
  post := fun x s0 sf =>
    ∃∗ ans : Except Unit (Option (SessionRecord (List (BitVec 8)))),
      ⌜sf.trace = s0.trace ++ [loadEvent encRecord x.addr.val ans]⌝ ∗
      ((x.fut + 8#64) ↦₆₄ x.addrA) ∗ ((x.fut + 0x10#64) ↦₈ 1#8) ∗
      loadPollOutAtS Scope A b x.out ans ∗
      protocolAddressAt A x.addr x.addrA ∗ A.pool ∗ stackAt s0.sp loadSessionPollStack

/-- `loadSessionPollSpecS` specialized to `RecordInScope`. -/
abbrev loadSessionPollSpec (A : RustAlloc)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) (b : BitVec 64) :
    Spec LoadPollCall :=
  loadSessionPollSpecS RecordInScope A encRecord b

/-- `load_session` hook contract generalized to an arbitrary record predicate `Scope`. -/
def loadSessionSpecS (Scope : SessionRecord (List (BitVec 8)) → Prop) (A : RustAlloc)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) : Spec LoadCall where
  pre := (loadSessionSpec A encRecord).pre
  post := fun x s0 sf =>
    ∃∗ ans : Except Unit (Option (SessionRecord (List (BitVec 8)))),
      ⌜StatusIs ((sf.readReg64 .x0).setWidth 32) (loadClass ans) ∧
        sf.trace = s0.trace ++ [loadEvent encRecord x.addr.val ans]⌝ ∗
      (match ans with
       | .ok (some r) => ⌜Scope r⌝ ∗ ∃∗ g : RecordGhost, sessionRecordAt A x.out g r
       | _ => memRegion x.out 368) ∗
      protocolAddressAt A x.addr x.addrA ∗ A.pool ∗ stackAt s0.sp storeHookStack

theorem loadSessionSpecS_inScope (A : RustAlloc)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) :
    loadSessionSpecS RecordInScope A encRecord = loadSessionSpec A encRecord := rfl

/-- Ghost state of an identity-store future poll: box `fut` (`x0`), 48-byte `sret` `out` (`x8`),
and hook call arguments. -/
structure IdentityPollCall where
  fut : BitVec 64
  out : BitVec 64
  call : IdentityCall

/-- Future-box fields read by `save_identity` and `is_trusted_identity` polls (`addrA` at `+8`,
`keyA` at `+0x10`, state byte at `+0x18`). -/
def identityBoxAt (x : IdentityPollCall) (st : BitVec 8) : SepProp :=
  ((x.fut + 8#64) ↦₆₄ x.call.addrA) ∗ ((x.fut + 0x10#64) ↦₆₄ x.call.keyA) ∗
    ((x.fut + 0x18#64) ↦₈ st)

/-- Contract of the `save_identity` future poll (`0x42c04`): emits `saveEvent`, sets the future
state byte to `1`, and writes the 48-byte `Poll<Result<IdentityChange, SignalProtocolError>>` at
`x.out`. -/
def saveIdentityPollSpec (A : RustAlloc) (b : BitVec 64) : Spec IdentityPollCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out⌝ ∗ identityBoxAt x 0#8 ∗
      memRegion x.out 48 ∗ protocolAddressAt A x.call.addr x.call.addrA ∗
      (x.call.keyA ↦ₛ x.call.key.publicKey.bytes.toList) ∗ A.pool ∗
      stackAt s.sp identityPollStack
  post := fun x s0 sf =>
    ∃∗ ans : Except Unit IdentityChange,
      ⌜sf.trace = s0.trace ++ [saveEvent x.call.addr.val x.call.key ans]⌝ ∗
      identityBoxAt x 1#8 ∗
      (match ans with
       | .ok c =>
         (x.out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗
           ((x.out + 8#64) ↦₃₂ (if c == .replacedExisting then 1#32 else 0#32)) ∗
           memRegion (x.out + 0xc#64) 4
       | .error () =>
         (x.out ↦₆₄ 0x800000000000001A#64) ∗ ((x.out + 8#64) ↦₆₄ (b + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))))) ∗
      errTailAt b x.out ∗ memRegion (x.out + 0x28#64) 8 ∗
      protocolAddressAt A x.call.addr x.call.addrA ∗
      (x.call.keyA ↦ₛ x.call.key.publicKey.bytes.toList) ∗ A.pool ∗
      stackAt s0.sp identityPollStack

/-- Contract of the `is_trusted_identity` future poll (`0x42c8c`): reads direction byte `d` at
`x.fut + 0x19`, emits `trustEvent`, sets the future state byte to `1`, and writes the 48-byte
`Poll<Result<bool, SignalProtocolError>>` at `x.out`. -/
def isTrustedPollSpec (A : RustAlloc) (b : BitVec 64) : Spec (IdentityPollCall × Direction) where
  pre := fun (x, d) s =>
    ⌜s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out⌝ ∗ identityBoxAt x 0#8 ∗
      ((x.fut + 0x19#64) ↦₈ directionByte d) ∗ memRegion x.out 48 ∗
      protocolAddressAt A x.call.addr x.call.addrA ∗
      (x.call.keyA ↦ₛ x.call.key.publicKey.bytes.toList) ∗ A.pool ∗
      stackAt s.sp identityPollStack
  post := fun (x, d) s0 sf =>
    ∃∗ ans : Except Unit Bool,
      ⌜sf.trace = s0.trace ++ [trustEvent x.call.addr.val x.call.key d ans]⌝ ∗
      identityBoxAt x 1#8 ∗ ((x.fut + 0x19#64) ↦₈ directionByte d) ∗
      (match ans with
       | .ok t =>
         (x.out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ ((x.out + 8#64) ↦₈ (if t then 1#8 else 0#8)) ∗
           memRegion (x.out + 9#64) 7
       | .error () =>
         (x.out ↦₆₄ 0x800000000000001A#64) ∗ ((x.out + 8#64) ↦₆₄ (b + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))))) ∗
      errTailAt b x.out ∗ memRegion (x.out + 0x28#64) 8 ∗
      protocolAddressAt A x.call.addr x.call.addrA ∗
      (x.call.keyA ↦ₛ x.call.key.publicKey.bytes.toList) ∗ A.pool ∗
      stackAt s0.sp identityPollStack

end CryptoVerification.LibsignalPublicApi.StoreKit
