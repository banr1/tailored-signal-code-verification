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
# Abstract `KyberPreKeyStore` Interface (`KyberPreKeyStoreSpec`)

Store-kit interface for the `dyn KyberPreKeyStore` methods invoked by `decrypt_prekey`:
* `get_kyber_pre_key` (`kpk_vt + 0x18`), writing 88-byte
  `Poll::Ready<Result<KyberPreKeyRecord, SignalProtocolError>>` (`kpkGetPollOutAt`);
* `mark_kyber_pre_key_used` (`kpk_vt + 0x28`), writing 48-byte
  `Poll::Ready<Result<(), SignalProtocolError>>` (`kpkMarkPollOutAt`).
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

/-! ## `mark_kyber_pre_key_used` Shim and Poll Call Records -/

/-- Arguments of `mark_kyber_pre_key_used`'s shim: `self` (`x0`), `id` (`w1`), `signedId` (`w2`),
    and borrowed `base_key: &PublicKey` pointer `baseKeyA` (`x3`). -/
structure KyberMarkShimCall where
  self : BitVec 64
  id : BitVec 32
  signedId : BitVec 32
  baseKeyA : BitVec 64

/-- Ghost call record for `mark_kyber_pre_key_used`'s future poll (`fut` in `x0`, `sret` in `x8`,
    with borrowed `baseKey` at `baseKeyA`). -/
structure KyberMarkPollCall where
  fut : BitVec 64
  out : BitVec 64
  self : BitVec 64
  baseKeyA : BitVec 64
  id : BitVec 32
  signedId : BitVec 32
  baseKey : PublicKey

/-! ## `KyberPreKeyStoreSpec` -/

/-- Pure data, trace projections, answer relations, and separation-logic predicates of a
    `KyberPreKeyStore` implementation (`get_kyber_pre_key` at `kpk_vt + 0x18`,
    `mark_kyber_pre_key_used` at `kpk_vt + 0x28`). -/
structure KyberPreKeyStoreSpec (A : RustAlloc) (b : BitVec 64) where
  /-- `dyn KyberPreKeyStore` trait-object vtable address. -/
  kpk_vt : BitVec 64
  /-- Logical state of the Kyber pre-key store. -/
  KpkState : Type
  /-- Separation-logic predicate for the Kyber pre-key store object at `self`. -/
  storeAt : BitVec 64 → KpkState → SepProp
  /-- Pure well-formedness predicate carried by every returned `KyberPreKeyRecord`. -/
  RecOk : KyberPreKeyRecord → Prop := fun _ => True
  /-- Pure precondition on the key id passed to `get_kyber_pre_key`'s poll. -/
  getIdOk : BitVec 32 → Prop := fun _ => True
  /-- Pure precondition on `(id, signedId, baseKey)` passed to `mark_kyber_pre_key_used`'s poll. -/
  markOk : BitVec 32 → BitVec 32 → PublicKey → Prop := fun _ _ _ => True
  /-- Entry file-system predicate required by the polls (`True` for in-memory stores;
      `(· = F0)` for the CLI's file-backed store). -/
  envOk : FsFiles → Prop := fun _ => True
  /-- Point-wise file-descriptor predicate carried across the store's ops (`True` by default for
      in-memory stores; `FdsGe3Closed` for the CLI's file-backed store). -/
  fdsOk : FsState → Prop := fun _ => True
  /-- Kit witness type for `get_kyber_pre_key` `Err` returns (`PEmpty` when infallible). -/
  GetErr : Type
  /-- Kit witness type for `mark_kyber_pre_key_used` `Err` returns (`PEmpty` when infallible). -/
  MarkErr : Type
  /-- 48-byte `SignalProtocolError` layout for `GetErr`. -/
  getErr : SpeErrSpec GetErr
  /-- 48-byte `SignalProtocolError` layout for `MarkErr`. -/
  markErr : SpeErrSpec MarkErr
  /-- Post-`get_kyber_pre_key` state transition (`fun st _ _ => st` for read-only `get`). -/
  getUpdate : KpkState → BitVec 32 → Except GetErr KyberPreKeyRecord → KpkState := fun st _ _ => st
  /-- Post-`mark_kyber_pre_key_used` state transition. -/
  markUpdate : KpkState → BitVec 32 → BitVec 32 → PublicKey → Except MarkErr Unit → KpkState
  /-- Pure relation tying `(st0, id)` to the `get_kyber_pre_key` answer. -/
  getRel : KpkState → BitVec 32 → Except GetErr KyberPreKeyRecord → Prop
  /-- Pure relation tying `(st0, id, signedId, baseKey)` to the `mark_kyber_pre_key_used`
      answer (including refusal when `baseKey` was already seen). -/
  markRel : KpkState → BitVec 32 → BitVec 32 → PublicKey → Except MarkErr Unit → Prop
  /-- Trace events emitted by a `get_kyber_pre_key` call. -/
  getEvs : BitVec 32 → Except GetErr KyberPreKeyRecord → List TraceEvent := fun _ _ => []
  /-- Trace events emitted by a `mark_kyber_pre_key_used` call. -/
  markEvs : BitVec 32 → BitVec 32 → PublicKey → Except MarkErr Unit → List TraceEvent :=
    fun _ _ _ _ => []
  /-- Slot target offset for `get_kyber_pre_key` (`kpk_vt + 0x18 ↦ b + getShimOff`). -/
  getShimOff : BitVec 64
  /-- Future vtable offset for `get_kyber_pre_key` (`b + getFutVtOff`). -/
  getFutVtOff : BitVec 64
  /-- Poll entrypoint offset for `get_kyber_pre_key` (`b + getPollOff`). -/
  getPollOff : BitVec 64
  /-- Drop entrypoint offset for `get_kyber_pre_key`'s future (`b + getFutDropOff`). -/
  getFutDropOff : BitVec 64
  /-- Heap box size in bytes for `get_kyber_pre_key`'s future (`16` in CLI and `OneKeyStore`). -/
  getBoxSize : Nat
  /-- Slot target offset for `mark_kyber_pre_key_used` (`kpk_vt + 0x28 ↦ b + markShimOff`). -/
  markShimOff : BitVec 64
  /-- Future vtable offset for `mark_kyber_pre_key_used` (`b + markFutVtOff`). -/
  markFutVtOff : BitVec 64
  /-- Poll entrypoint offset for `mark_kyber_pre_key_used` (`b + markPollOff`). -/
  markPollOff : BitVec 64
  /-- Drop entrypoint offset for `mark_kyber_pre_key_used`'s future (`b + markFutDropOff`). -/
  markFutDropOff : BitVec 64
  /-- Heap box size in bytes for `mark_kyber_pre_key_used`'s future (`32` in CLI and `OneKeyStore`). -/
  markBoxSize : Nat
  /-- Stack budget for `get_kyber_pre_key` shim. -/
  getShimStack : Nat
  /-- Stack budget for `get_kyber_pre_key` poll. -/
  getPollStack : Nat
  /-- Stack budget for `mark_kyber_pre_key_used` shim. -/
  markShimStack : Nat
  /-- Stack budget for `mark_kyber_pre_key_used` poll. -/
  markPollStack : Nat
  /-- Future box predicate for `get_kyber_pre_key` (`st = 0#8` before first poll, `1#8` after). -/
  getBoxAt : (box self : BitVec 64) → (id : BitVec 32) → (state : BitVec 8) → SepProp
  /-- Future box predicate for `mark_kyber_pre_key_used` (`st = 0#8` before first poll, `1#8` after). -/
  markBoxAt : (box self baseKeyA : BitVec 64) → (id signedId : BitVec 32) →
    (state : BitVec 8) → SepProp
  /-- Any `getBoxAt` state entails raw `memRegion` of `getBoxSize` bytes for deallocation. -/
  getBoxAt_memRegion : ∀ box self id st, getBoxAt box self id st ⊢ memRegion box getBoxSize
  /-- Any `markBoxAt` state entails raw `memRegion` of `markBoxSize` bytes for deallocation. -/
  markBoxAt_memRegion : ∀ box self baseKeyA id signedId st,
    markBoxAt box self baseKeyA id signedId st ⊢ memRegion box markBoxSize
  /-- `getBoxSize` is non-zero as a 64-bit word. -/
  getBoxSize_ne_zero : BitVec.ofNat 64 getBoxSize ≠ 0#64
  /-- `markBoxSize` is non-zero as a 64-bit word. -/
  markBoxSize_ne_zero : BitVec.ofNat 64 markBoxSize ≠ 0#64
  /-- `getBoxSize` fits in 64 bits. -/
  getBoxSize_lt : getBoxSize < 2 ^ 64
  /-- `markBoxSize` fits in 64 bits. -/
  markBoxSize_lt : markBoxSize < 2 ^ 64
  /-- `b + getFutDropOff` is non-zero for page-aligned `b`. -/
  getFutDrop_ne_zero : b &&& 0xfff#64 = 0#64 → b + getFutDropOff ≠ 0#64
  /-- `b + markFutDropOff` is non-zero for page-aligned `b`. -/
  markFutDrop_ne_zero : b &&& 0xfff#64 = 0#64 → b + markFutDropOff ≠ 0#64

abbrev KyberPreKeyStoreKit := KyberPreKeyStoreSpec

/-- The 88-byte `Poll::Ready<Result<KyberPreKeyRecord, SignalProtocolError>>` written to `out` by
    `get_kyber_pre_key`'s future poll:
    * `.ok r`: `kit.RecOk r` and `signedPreKeyStructAt A out r.signedPreKey` (`88` B);
    * `.error e`: word 0 is `-1` (`errTag`), bytes `8..56` hold `speErrAt kit.getErr (out + 8) e`,
      and bytes `56..88` are uninspected (`memRegion (out + 0x38) 32`). -/
def kpkGetPollOutAt {A : RustAlloc} {b : BitVec 64} (kit : KyberPreKeyStoreSpec A b)
    (out : BitVec 64) : Except kit.GetErr KyberPreKeyRecord → SepProp
  | .ok r => ⌜kit.RecOk r⌝ ∗ signedPreKeyStructAt A out r.signedPreKey
  | .error e =>
    (out ↦₆₄ errTag) ∗ speErrAt kit.getErr (out + 8#64) e ∗ memRegion (out + 0x38#64) 32

/-- The 48-byte `Poll::Ready<Result<(), SignalProtocolError>>` written to `out` by
    `mark_kyber_pre_key_used`'s future poll. -/
abbrev kpkMarkPollOutAt {A : RustAlloc} {b : BitVec 64} (kit : KyberPreKeyStoreSpec A b)
    (out : BitVec 64) : Except kit.MarkErr Unit → SepProp :=
  unitSpePollOutAt kit.markErr out

/-- Generic `get_kyber_pre_key` shim spec parameterized by `kit : KyberPreKeyStoreSpec A b`. -/
def kitKpkGetShimSpec {A : RustAlloc} {b : BitVec 64} (kit : KyberPreKeyStoreSpec A b) :
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

/-- Generic `mark_kyber_pre_key_used` shim spec parameterized by `kit : KyberPreKeyStoreSpec A b`. -/
def kitKpkMarkShimSpec {A : RustAlloc} {b : BitVec 64} (kit : KyberPreKeyStoreSpec A b) :
    Spec KyberMarkShimCall where
  pre := fun x s =>
    ⌜(b &&& 0xfff#64) = 0#64 ∧ s.readReg64 .x0 = x.self ∧ s.readReg32 .x1 = x.id ∧
      s.readReg32 .x2 = x.signedId ∧ s.readReg64 .x3 = x.baseKeyA⌝ ∗
      A.pool ∗ stackAt s.sp kit.markShimStack
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x1 = b + kit.markFutVtOff ∧ sf.readReg64 .x0 ≠ 0#64 ∧
      (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
      A.live (sf.readReg64 .x0) kit.markBoxSize 8 ∗
      kit.markBoxAt (sf.readReg64 .x0) x.self x.baseKeyA x.id x.signedId 0#8 ∗
      A.pool ∗ stackAt s0.sp kit.markShimStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Generic `get_kyber_pre_key` poll spec parameterized by `kit : KyberPreKeyStoreSpec A b`. -/
def kitKpkGetPollSpec {A : RustAlloc} {b : BitVec 64} (kit : KyberPreKeyStoreSpec A b) :
    Spec (PreKeyPollCall × kit.KpkState) where
  pre := fun (x, st0) s =>
    ⌜(b &&& 0xfff#64) = 0#64 ∧ s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧
      kit.getIdOk x.id⌝ ∗
      kit.getBoxAt x.fut x.self x.id 0#8 ∗
      kit.storeAt x.self st0 ∗ memRegion x.out 88 ∗
      A.pool ∗ stackAt s.sp kit.getPollStack
  post := fun (x, st0) s0 sf =>
    ∃∗ ans : Except kit.GetErr KyberPreKeyRecord,
      ⌜kit.getRel st0 x.id ans ∧ sf.trace = s0.trace ++ kit.getEvs x.id ans⌝ ∗
      kit.getBoxAt x.fut x.self x.id 1#8 ∗
      kit.storeAt x.self (kit.getUpdate st0 x.id ans) ∗
      kpkGetPollOutAt kit x.out ans ∗
      A.pool ∗ stackAt s0.sp kit.getPollStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Generic `mark_kyber_pre_key_used` poll spec parameterized by `kit : KyberPreKeyStoreSpec A b`.
    The borrowed 32-byte EC `PublicKey` at `x.baseKeyA` (`x.baseKeyA ↦ₛ x.baseKey.bytes.toList`,
    matching `IdentityStoreKit` and `publicKeySerializeSpec`) is preserved across the poll. -/
def kitKpkMarkPollSpec {A : RustAlloc} {b : BitVec 64} (kit : KyberPreKeyStoreSpec A b) :
    Spec (KyberMarkPollCall × kit.KpkState) where
  pre := fun (x, st0) s =>
    ⌜(b &&& 0xfff#64) = 0#64 ∧ s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧
      kit.markOk x.id x.signedId x.baseKey⌝ ∗
      kit.markBoxAt x.fut x.self x.baseKeyA x.id x.signedId 0#8 ∗
      kit.storeAt x.self st0 ∗ memRegion x.out 48 ∗
      (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗
      A.pool ∗ stackAt s.sp kit.markPollStack
  post := fun (x, st0) s0 sf =>
    ∃∗ ans : Except kit.MarkErr Unit,
      ⌜kit.markRel st0 x.id x.signedId x.baseKey ans ∧
        sf.trace = s0.trace ++ kit.markEvs x.id x.signedId x.baseKey ans⌝ ∗
      kit.markBoxAt x.fut x.self x.baseKeyA x.id x.signedId 1#8 ∗
      kit.storeAt x.self (kit.markUpdate st0 x.id x.signedId x.baseKey ans) ∗
      kpkMarkPollOutAt kit x.out ans ∗
      (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗
      A.pool ∗ stackAt s0.sp kit.markPollStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- `get_kyber_pre_key` poll spec with `kit.envOk` on the entry files. -/
abbrev kitKpkGetPollSpecE {A : RustAlloc} {b : BitVec 64} (kit : KyberPreKeyStoreSpec A b) :
    Spec (PreKeyPollCall × kit.KpkState) :=
  withEnvPre (kitKpkGetPollSpec kit) fun s => kit.envOk s.fs.files

/-- `mark_kyber_pre_key_used` poll spec with `kit.envOk` on the entry files. -/
abbrev kitKpkMarkPollSpecE {A : RustAlloc} {b : BitVec 64} (kit : KyberPreKeyStoreSpec A b) :
    Spec (KyberMarkPollCall × kit.KpkState) :=
  withEnvPre (kitKpkMarkPollSpec kit) fun s => kit.envOk s.fs.files

/-- The Kyber pre-key store's own trace events contain no file-system event (`FsCtx`'s `Q`). -/
def KyberPreKeyStoreSpec.Quiet {A : RustAlloc} {b : BitVec 64}
    (kit : KyberPreKeyStoreSpec A b) : Prop :=
  (∀ id ans, NoFsEv (kit.getEvs id ans)) ∧
    (∀ id signedId bk ans, NoFsEv (kit.markEvs id signedId bk ans))

/-- Read-only `.rodata` vtable slots required by `kit : KyberPreKeyStoreSpec A img.base` under
    `img.FrozenLoaded`. Store `drop_in_place` and `save_kyber_pre_key` (`+0x20`) are never called
    by `decrypt_prekey`. -/
structure KyberPreKeyVtablesOk {A : RustAlloc} (img : Obj.Image)
    (kit : KyberPreKeyStoreSpec A img.base) : Prop where
  getSlot : ∀ {s : State} {P : SepProp}, img.FrozenLoaded s → (s.mem ⊨ P) →
    s.mem ⊨ ((kit.kpk_vt + 0x18#64) ↦₆₄ᵣ (img.base + kit.getShimOff)) ∗ P
  markSlot : ∀ {s : State} {P : SepProp}, img.FrozenLoaded s → (s.mem ⊨ P) →
    s.mem ⊨ ((kit.kpk_vt + 0x28#64) ↦₆₄ᵣ (img.base + kit.markShimOff)) ∗ P
  getFutDrop : ∀ {s : State} {P : SepProp}, img.FrozenLoaded s → (s.mem ⊨ P) →
    s.mem ⊨ ((img.base + kit.getFutVtOff) ↦₆₄ᵣ (img.base + kit.getFutDropOff)) ∗ P
  getFutSize : ∀ {s : State} {P : SepProp}, img.FrozenLoaded s → (s.mem ⊨ P) →
    s.mem ⊨ ((img.base + kit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.getBoxSize) ∗ P
  getFutAlign : ∀ {s : State} {P : SepProp}, img.FrozenLoaded s → (s.mem ⊨ P) →
    s.mem ⊨ ((img.base + kit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗ P
  getFutPoll : ∀ {s : State} {P : SepProp}, img.FrozenLoaded s → (s.mem ⊨ P) →
    s.mem ⊨ ((img.base + kit.getFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + kit.getPollOff)) ∗ P
  markFutDrop : ∀ {s : State} {P : SepProp}, img.FrozenLoaded s → (s.mem ⊨ P) →
    s.mem ⊨ ((img.base + kit.markFutVtOff) ↦₆₄ᵣ (img.base + kit.markFutDropOff)) ∗ P
  markFutSize : ∀ {s : State} {P : SepProp}, img.FrozenLoaded s → (s.mem ⊨ P) →
    s.mem ⊨ ((img.base + kit.markFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.markBoxSize) ∗ P
  markFutAlign : ∀ {s : State} {P : SepProp}, img.FrozenLoaded s → (s.mem ⊨ P) →
    s.mem ⊨ ((img.base + kit.markFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗ P
  markFutPoll : ∀ {s : State} {P : SepProp}, img.FrozenLoaded s → (s.mem ⊨ P) →
    s.mem ⊨ ((img.base + kit.markFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + kit.markPollOff)) ∗ P

/-- Code-contract bundle for `kit : KyberPreKeyStoreSpec A b` (without `img.FrozenLoaded`). -/
structure KyberPreKeyStoreKitOk {A : RustAlloc} {b : BitVec 64}
    (kit : KyberPreKeyStoreSpec A b) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop where
  getShim : subroutine_ok (tripleRatchetProgAt b C ctl abs) (b + kit.getShimOff)
    (kitKpkGetShimSpec kit)
  getPoll : subroutine_ok (tripleRatchetProgAt b C ctl abs) (b + kit.getPollOff)
    (kitKpkGetPollSpecE kit)
  getFutDrop : subroutine_ok (tripleRatchetProgAt b C ctl abs) (b + kit.getFutDropOff)
    futDropSpec
  markShim : subroutine_ok (tripleRatchetProgAt b C ctl abs) (b + kit.markShimOff)
    (kitKpkMarkShimSpec kit)
  markPoll : subroutine_ok (tripleRatchetProgAt b C ctl abs) (b + kit.markPollOff)
    (kitKpkMarkPollSpecE kit)
  markFutDrop : subroutine_ok (tripleRatchetProgAt b C ctl abs) (b + kit.markFutDropOff)
    futDropSpec

/-- Image-relocated code-contract bundle (`Spec.inImage ... img`, providing `img.FrozenLoaded`
    to every shim, poll, and future drop). -/
structure KyberPreKeyStoreKitOkImg {A : RustAlloc} (img : Obj.Image)
    (kit : KyberPreKeyStoreSpec A img.base) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop where
  getShim : subroutine_ok (tripleRatchetProgAt img.base C ctl abs) (img.base + kit.getShimOff)
    ((kitKpkGetShimSpec kit).inImage img)
  getPoll : subroutine_ok (tripleRatchetProgAt img.base C ctl abs) (img.base + kit.getPollOff)
    ((kitKpkGetPollSpecE kit).inImage img)
  getFutDrop : subroutine_ok (tripleRatchetProgAt img.base C ctl abs) (img.base + kit.getFutDropOff)
    (futDropSpec.inImage img)
  markShim : subroutine_ok (tripleRatchetProgAt img.base C ctl abs) (img.base + kit.markShimOff)
    ((kitKpkMarkShimSpec kit).inImage img)
  markPoll : subroutine_ok (tripleRatchetProgAt img.base C ctl abs) (img.base + kit.markPollOff)
    ((kitKpkMarkPollSpecE kit).inImage img)
  markFutDrop : subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
    (img.base + kit.markFutDropOff) (futDropSpec.inImage img)

end CryptoVerification.LibsignalPublicApi.StoreKit
