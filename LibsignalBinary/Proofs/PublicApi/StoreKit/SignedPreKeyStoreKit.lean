/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKit
public import LibsignalBinary.Specifications.RecordCodecsBinary.SignedPreKey

/-!
# Generic `SignedPreKeyStore` Contract (`SignedPreKeyStoreSpec`)

Abstract separation-logic interface for `libsignal_protocol::storage::traits::SignedPreKeyStore`
covering `get_signed_pre_key` (`spk_vt + 0x18`) and the 88-byte
`Poll::Ready<Result<SignedPreKeyRecord, SignalProtocolError>>` output layout (`spkGetPollOutAt`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.LibsignalPublicApi.StoreKit

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.LibsignalPublicApi.StoreKit

/-- Pure data, trace projections, answer relation, and separation-logic predicates of a
    `SignedPreKeyStore` implementation (`get_signed_pre_key` at `spk_vt + 0x18`). -/
structure SignedPreKeyStoreSpec (A : RustAlloc) (b : BitVec 64) where
  /-- `dyn SignedPreKeyStore` trait-object vtable address. -/
  spk_vt : BitVec 64
  /-- Logical state of the signed pre-key store. -/
  SpkState : Type
  /-- Separation-logic predicate for the signed pre-key store object at `self`. -/
  storeAt : BitVec 64 → SpkState → SepProp
  /-- Pure well-formedness predicate carried by every returned `SignedPreKeyRecord`. -/
  RecOk : SignedPreKeyRecord → Prop := fun _ => True
  /-- Pure precondition on the key id passed to `get_signed_pre_key`'s poll. -/
  idOk : BitVec 32 → Prop := fun _ => True
  /-- Entry file-system predicate required by the poll (`True` for in-memory stores;
      `(· = F0)` for the CLI's file-backed store). -/
  envOk : FsFiles → Prop := fun _ => True
  /-- Point-wise file-descriptor predicate carried across the store's ops (`True` by default for
      in-memory stores; `FdsGe3Closed` for the CLI's file-backed store). -/
  fdsOk : FsState → Prop := fun _ => True
  /-- Kit witness type for `get_signed_pre_key` `Err` returns (`PEmpty` when infallible). -/
  GetErr : Type
  /-- 48-byte `SignalProtocolError` layout for `GetErr`. -/
  getErr : SpeErrSpec GetErr
  /-- Post-`get_signed_pre_key` state transition (defaults to identity since `&dyn` is shared). -/
  getUpdate : SpkState → BitVec 32 → Except GetErr SignedPreKeyRecord → SpkState :=
    fun st _ _ => st
  /-- Pure relation tying `(st0, id)` to the `get_signed_pre_key` answer. -/
  getRel : SpkState → BitVec 32 → Except GetErr SignedPreKeyRecord → Prop
  /-- Trace events emitted by a `get_signed_pre_key` call. -/
  getEvs : BitVec 32 → Except GetErr SignedPreKeyRecord → List TraceEvent := fun _ _ => []
  /-- Slot target offset for `get_signed_pre_key` (`spk_vt + 0x18 ↦ b + getShimOff`). -/
  getShimOff : BitVec 64
  /-- Future vtable offset for `get_signed_pre_key` (`b + getFutVtOff`). -/
  getFutVtOff : BitVec 64
  /-- Poll entrypoint offset for `get_signed_pre_key` (`b + getPollOff`). -/
  getPollOff : BitVec 64
  /-- Drop entrypoint offset for `get_signed_pre_key`'s future (`b + getFutDropOff`). -/
  getFutDropOff : BitVec 64
  /-- Heap box size in bytes for `get_signed_pre_key`'s future (`16` in CLI and `OneKeyStore`). -/
  getBoxSize : Nat
  /-- Stack budget for `get_signed_pre_key` shim. -/
  getShimStack : Nat
  /-- Stack budget for `get_signed_pre_key` poll. -/
  getPollStack : Nat
  /-- Future box predicate for `get_signed_pre_key` (`st = 0#8` before first poll, `1#8` after). -/
  getBoxAt : (box self : BitVec 64) → (id : BitVec 32) → (state : BitVec 8) → SepProp
  /-- Any `getBoxAt` state entails raw `memRegion` of `getBoxSize` bytes for deallocation. -/
  getBoxAt_memRegion : ∀ box self id st, getBoxAt box self id st ⊢ memRegion box getBoxSize
  /-- `getBoxSize` is non-zero as a 64-bit word. -/
  getBoxSize_ne_zero : BitVec.ofNat 64 getBoxSize ≠ 0#64
  /-- `getBoxSize` fits in 64 bits. -/
  getBoxSize_lt : getBoxSize < 2 ^ 64
  /-- `b + getFutDropOff` is non-zero for page-aligned `b`. -/
  getFutDrop_ne_zero : b &&& 0xfff#64 = 0#64 → b + getFutDropOff ≠ 0#64

/-- Alias matching the `*Kit` naming convention alongside `SignedPreKeyStoreSpec`. -/
abbrev SignedPreKeyStoreKit := SignedPreKeyStoreSpec

/-- The 88-byte `Poll::Ready<Result<SignedPreKeyRecord, SignalProtocolError>>` written to `out` by
    `get_signed_pre_key`'s future poll:
    * `.ok r`: `kit.RecOk r` and `signedPreKeyStructAt A out r.signedPreKey` (`88` B);
    * `.error e`: word 0 is `-1` (`errTag`), bytes `8..56` hold `speErrAt kit.getErr (out + 8) e`,
      and bytes `56..88` are uninspected (`memRegion (out + 0x38) 32`). -/
def spkGetPollOutAt {A : RustAlloc} {b : BitVec 64} (kit : SignedPreKeyStoreSpec A b)
    (out : BitVec 64) : Except kit.GetErr SignedPreKeyRecord → SepProp
  | .ok r => ⌜kit.RecOk r⌝ ∗ signedPreKeyStructAt A out r.signedPreKey
  | .error e =>
    (out ↦₆₄ errTag) ∗ speErrAt kit.getErr (out + 8#64) e ∗ memRegion (out + 0x38#64) 32

/-- Generic `get_signed_pre_key` shim spec parameterized by `kit : SignedPreKeyStoreSpec A b`. -/
def kitSpkGetShimSpec {A : RustAlloc} {b : BitVec 64} (kit : SignedPreKeyStoreSpec A b) :
    Spec PreKeyShimCall where
  pre := fun x s =>
    ⌜(b &&& 0xfff#64) = 0#64 ∧ s.readReg64 .x0 = x.self ∧ s.readReg32 .x1 = x.id⌝ ∗
      A.pool ∗ stackAt s.sp kit.getShimStack
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x1 = b + kit.getFutVtOff ∧ sf.readReg64 .x0 ≠ 0#64 ∧
      (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
      A.live (sf.readReg64 .x0) kit.getBoxSize 8 ∗
      kit.getBoxAt (sf.readReg64 .x0) x.self x.id 0#8 ∗
      A.pool ∗ stackAt s0.sp kit.getShimStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Generic `get_signed_pre_key` poll spec parameterized by `kit : SignedPreKeyStoreSpec A b`. -/
def kitSpkGetPollSpec {A : RustAlloc} {b : BitVec 64} (kit : SignedPreKeyStoreSpec A b) :
    Spec (PreKeyPollCall × kit.SpkState) where
  pre := fun (x, st0) s =>
    ⌜(b &&& 0xfff#64) = 0#64 ∧ s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧
      kit.idOk x.id⌝ ∗
      kit.getBoxAt x.fut x.self x.id 0#8 ∗
      kit.storeAt x.self st0 ∗ memRegion x.out 88 ∗
      A.pool ∗ stackAt s.sp kit.getPollStack
  post := fun (x, st0) s0 sf =>
    ∃∗ ans : Except kit.GetErr SignedPreKeyRecord,
      ⌜kit.getRel st0 x.id ans ∧ sf.trace = s0.trace ++ kit.getEvs x.id ans⌝ ∗
      kit.getBoxAt x.fut x.self x.id 1#8 ∗
      kit.storeAt x.self (kit.getUpdate st0 x.id ans) ∗
      spkGetPollOutAt kit x.out ans ∗
      A.pool ∗ stackAt s0.sp kit.getPollStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- `get_signed_pre_key` poll spec with `kit.envOk` on the entry files. -/
abbrev kitSpkGetPollSpecE {A : RustAlloc} {b : BitVec 64} (kit : SignedPreKeyStoreSpec A b) :
    Spec (PreKeyPollCall × kit.SpkState) :=
  withEnvPre (kitSpkGetPollSpec kit) fun s => kit.envOk s.fs.files

/-- The signed pre-key store's own trace events contain no file-system event (`FsCtx`'s `Q`). -/
def SignedPreKeyStoreSpec.Quiet {A : RustAlloc} {b : BitVec 64}
    (kit : SignedPreKeyStoreSpec A b) : Prop :=
  ∀ id ans, NoFsEv (kit.getEvs id ans)

/-- Read-only `.rodata` vtable slots required by `kit : SignedPreKeyStoreSpec A img.base` under
    `img.FrozenLoaded`. Store `drop_in_place` and `save_signed_pre_key` (`+0x20`) are never called
    by `decrypt_prekey`. -/
structure SignedPreKeyVtablesOk {A : RustAlloc} (img : Obj.Image)
    (kit : SignedPreKeyStoreSpec A img.base) : Prop where
  getSlot : ∀ {s : State} {P : SepProp}, img.FrozenLoaded s → (s.mem ⊨ P) →
    s.mem ⊨ ((kit.spk_vt + 0x18#64) ↦₆₄ᵣ (img.base + kit.getShimOff)) ∗ P
  getFutDrop : ∀ {s : State} {P : SepProp}, img.FrozenLoaded s → (s.mem ⊨ P) →
    s.mem ⊨ ((img.base + kit.getFutVtOff) ↦₆₄ᵣ (img.base + kit.getFutDropOff)) ∗ P
  getFutSize : ∀ {s : State} {P : SepProp}, img.FrozenLoaded s → (s.mem ⊨ P) →
    s.mem ⊨ ((img.base + kit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.getBoxSize) ∗ P
  getFutAlign : ∀ {s : State} {P : SepProp}, img.FrozenLoaded s → (s.mem ⊨ P) →
    s.mem ⊨ ((img.base + kit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗ P
  getFutPoll : ∀ {s : State} {P : SepProp}, img.FrozenLoaded s → (s.mem ⊨ P) →
    s.mem ⊨ ((img.base + kit.getFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + kit.getPollOff)) ∗ P

/-- Code-contract bundle for `kit : SignedPreKeyStoreSpec A b` (without `img.FrozenLoaded`). -/
structure SignedPreKeyStoreKitOk {A : RustAlloc} {b : BitVec 64}
    (kit : SignedPreKeyStoreSpec A b) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop where
  getShim : subroutine_ok (tripleRatchetProgAt b C ctl abs) (b + kit.getShimOff)
    (kitSpkGetShimSpec kit)
  getPoll : subroutine_ok (tripleRatchetProgAt b C ctl abs) (b + kit.getPollOff)
    (kitSpkGetPollSpecE kit)
  getFutDrop : subroutine_ok (tripleRatchetProgAt b C ctl abs) (b + kit.getFutDropOff)
    futDropSpec

/-- Image-relocated code-contract bundle (`Spec.inImage ... img`, providing `img.FrozenLoaded`
    to shim, poll, and future drop). -/
structure SignedPreKeyStoreKitOkImg {A : RustAlloc} (img : Obj.Image)
    (kit : SignedPreKeyStoreSpec A img.base) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop where
  getShim : subroutine_ok (tripleRatchetProgAt img.base C ctl abs) (img.base + kit.getShimOff)
    ((kitSpkGetShimSpec kit).inImage img)
  getPoll : subroutine_ok (tripleRatchetProgAt img.base C ctl abs) (img.base + kit.getPollOff)
    ((kitSpkGetPollSpecE kit).inImage img)
  getFutDrop : subroutine_ok (tripleRatchetProgAt img.base C ctl abs) (img.base + kit.getFutDropOff)
    (futDropSpec.inImage img)

end CryptoVerification.LibsignalPublicApi.StoreKit
