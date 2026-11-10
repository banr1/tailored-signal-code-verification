/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.CodeLayout
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Specs.SpeOwned
import GeneratedLean.LibsignalSessionCode -- shake: keep

/-!
# CLI Store Callback Names, Future Boxes, and Bundled Specifications

Symbol names, future-box layouts (`idOwnFutBoxAt`), sret layouts (`idKeyPairOutAt`,
`idRegIdOutAt`), and the `InitStoreCallees` specification bundle for `IdentityFiles` and
`SessionFiles`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.StoreDefs

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunProofs

/-! ## PQ `IdentityFiles` Callback Symbol Names -/

abbrev idKeyPairShimName : String :=
  "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair"

abbrev idKeyPairPollName : String :=
  "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair::{closure#0}"

abbrev idRegIdShimName : String :=
  "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id"

abbrev idRegIdPollName : String :=
  "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id::{closure#0}"

theorem idKeyPairShim_fnOff :
    libsignalSessionCode.fnOff idKeyPairShimName =
      num% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair")

theorem idKeyPairPoll_fnOff :
    libsignalSessionCode.fnOff idKeyPairPollName =
      num% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair::{closure#0}") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair::{closure#0}")

theorem idRegIdShim_fnOff :
    libsignalSessionCode.fnOff idRegIdShimName =
      num% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id")

theorem idRegIdPoll_fnOff :
    libsignalSessionCode.fnOff idRegIdPollName =
      num% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id::{closure#0}") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id::{closure#0}")

/-! ## Future Boxes and Specifications -/

abbrev idKeyPairFutVtOff : BitVec 64 :=
  bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair::{closure#0}") - 0x18)

abbrev idRegIdFutVtOff : BitVec 64 :=
  bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id::{closure#0}") - 0x18)

/-- 16-byte future box allocated by `get_identity_key_pair` and `get_local_registration_id` shims:
`self` @0, `state` byte @8, 7 bytes uninitialized. -/
def idOwnFutBoxAt (box self : BitVec 64) (st : BitVec 8) : SepProp :=
  (box ↦₆₄ self) ∗ ((box + 8#64) ↦₈ st) ∗ memRegion (box + 9#64) 7

def idOwnShimSpec (futVtOff : BitVec 64) (A : RustAlloc) (img : Obj.Image)
    (stk : Nat) : Spec (BitVec 64) :=
  Spec.inImage
    { pre := fun self s =>
        ⌜s.readReg64 .x0 = self⌝ ∗ A.pool ∗ stackAt s.sp stk
      post := fun self s0 sf =>
        ⌜sf.readReg64 .x1 = img.base + futVtOff ∧ sf.readReg64 .x0 ≠ 0#64 ∧
          (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
          A.live (sf.readReg64 .x0) 16 8 ∗
          idOwnFutBoxAt (sf.readReg64 .x0) self 0#8 ∗
          A.pool ∗ stackAt s0.sp stk
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

structure IdOwnPollGhost where
  fut : BitVec 64
  out : BitVec 64
  self : BitVec 64
  own : DirGhost

/-- 72-byte sret of `get_identity_key_pair::{closure#0}`: the closure copies the 72-byte local
`Result<IdentityKeyPair, SignalProtocolError>` (laid out as `identityKeyPairResultAt` in
`Specifications/RecordCodecsBinary.lean`, which `<IdentityKeyPair as TryFrom<&[u8]>>::try_from` writes)
to `out`:
- `.ok kp`: tag byte `0`, the public key bytes @1, the private key bytes @0x21, 7 bytes unspecified.
- `.error ()`: tag byte `1`, 7 bytes unspecified, `RunDrop.SpeOwned` @8 (`InvalidState("read", _)`
  from `Dir::get`, or the error of `try_from`), 16 bytes unspecified. -/
def idKeyPairOutAt (A : RustAlloc) (out : BitVec 64) :
    Except Unit IdentityKeyPair → SepProp
  | .ok kp =>
    (out ↦₈ 0#8) ∗ ((out + 1#64) ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
      ((out + 0x21#64) ↦ₛ kp.privateKey.bytes.toList) ∗ memRegion (out + 0x41#64) 7
  | .error () =>
    (out ↦₈ 1#8) ∗ memRegion (out + 1#64) 7 ∗
      (∃∗ k : RunDrop.SpeOwned, RunDrop.speOwnedAt A (out + 8#64) k) ∗
      memRegion (out + 0x38#64) 16

def idKeyPairPollSpec (rd : ReadRule) (pathOk : List (BitVec 8) → Prop) (A : RustAlloc)
    (img : Obj.Image) (stk : Nat) : Spec IdOwnPollGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧
          x.own.path.length < 2 ^ 32 ∧
          pathOk (pathOf x.own.path (utf8 "identity-key-pair")) ∧
          ∀ bs, x.own.get rd s.fs.files (utf8 "identity-key-pair") = .ok bs →
            bs.length < 2 ^ 32⌝ ∗
          idOwnFutBoxAt x.fut x.self 0#8 ∗ dirAt A x.self x.own ∗
          memRegion x.out 72 ∗ logOff img ∗ A.pool ∗ stackAt s.sp stk
      post := fun x s0 sf =>
        (∃∗ ans : Except Unit IdentityKeyPair,
          ⌜ans = (IdGhost.mk x.own (.new [])).keyPair rd s0.fs.files ∧ sf.trace = s0.trace⌝ ∗
          idKeyPairOutAt A x.out ans) ∗
          idOwnFutBoxAt x.fut x.self 1#8 ∗ dirAt A x.self x.own ∗
          logOff img ∗ A.pool ∗ stackAt s0.sp stk
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

/-- 48-byte sret of `get_local_registration_id::{closure#0}`:
- `.ok reg`: word 0 `-2`, `u32` `reg` at `out + 8`, 36 bytes uninitialized.
- `.error ()`: `RunDrop.SpeOwned` at `out`: `InvalidState("read", _)` from `Dir::get`, or
  `InvalidState("registration-id", "malformed file")` when the file's length is not 4. -/
def idRegIdOutAt (A : RustAlloc) (out : BitVec 64) : Except Unit (BitVec 32) → SepProp
  | .ok reg =>
    (out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ ((out + 8#64) ↦₃₂ reg) ∗ memRegion (out + 12#64) 36
  | .error () => ∃∗ k : RunDrop.SpeOwned, RunDrop.speOwnedAt A out k

def idRegIdPollSpec (rd : ReadRule) (pathOk : List (BitVec 8) → Prop) (A : RustAlloc)
    (img : Obj.Image) (stk : Nat) : Spec IdOwnPollGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧
          x.own.path.length < 2 ^ 32 ∧
          pathOk (pathOf x.own.path (utf8 "registration-id"))⌝ ∗
          idOwnFutBoxAt x.fut x.self 0#8 ∗ dirAt A x.self x.own ∗
          memRegion x.out 48 ∗ A.pool ∗ stackAt s.sp stk
      post := fun x s0 sf =>
        (∃∗ ans : Except Unit (BitVec 32),
          ⌜ans = (IdGhost.mk x.own (.new [])).regId rd s0.fs.files ∧ sf.trace = s0.trace⌝ ∗
          idRegIdOutAt A x.out ans) ∗
          idOwnFutBoxAt x.fut x.self 1#8 ∗ dirAt A x.self x.own ∗
          A.pool ∗ stackAt s0.sp stk
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

/-! ## Bundled CLI Store Contracts -/

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.StoreDefs
