/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.StoreKit.Fs
public import LibsignalBinary.Specifications.RecordCodecsBinary
public import LibsignalBinary.Proofs.PublicApi.StoreSession.StoreCallSite

/-!
# Generic `PreKeyStore` Contract (`PreKeyStoreSpec`)

Abstract separation-logic interface for `libsignal_protocol::storage::traits::PreKeyStore`:
* Shared 48-byte `SignalProtocolError` representation (`speWordsAt`, `SpeErrSpec`, `speErrAt`,
  `unitSpePollOutAt`) separating the six inline words (`w0..w5`, distinct from niche tags
  `-1`, `-2`, `-3`) from address-independent `heap` ownership.
* `PreKeyStoreSpec` (`PreKeyStoreKit`): store state, vtable/shim/poll/drop offsets, future box
  predicates, and `subroutine_ok` bundles for `get_pre_key` (`pk_vt + 0x18`) and `remove_pre_key`
  (`pk_vt + 0x28`).
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

/-! ## Shared 48-byte `SignalProtocolError` & `Result<(), SPE>` sret layouts -/

/-- Six consecutive 64-bit words (`48` B) at `p`: the inline representation of a
    `libsignal_protocol::SignalProtocolError` value on stack or in an `sret` slot. -/
def speWordsAt (p w0 w1 w2 w3 w4 w5 : BitVec 64) : SepProp :=
  (p ↦₆₄ w0) ∗
  ((p + 0x08#64) ↦₆₄ w1) ∗
  ((p + 0x10#64) ↦₆₄ w2) ∗
  ((p + 0x18#64) ↦₆₄ w3) ∗
  ((p + 0x20#64) ↦₆₄ w4) ∗
  ((p + 0x28#64) ↦₆₄ w5)

/-- Representation of kit-specific `SignalProtocolError` values `E : Type`:
    * `w0..w5`: the six inline 64-bit words (`48` B);
    * `heap`: address-independent heap or `.rodata` ownership detached from the inline slot;
    * `w0_ne_err`, `w0_ne_ok`, `w0_ne_pending`: word 0 never collides with the `-1` (`errTag`),
      `-2` (`okTagVec`, `Result<(), SPE>::Ok`), or `-3` (`Poll::Pending`) enum niches. -/
structure SpeErrSpec (E : Type) where
  w0 : E → BitVec 64
  w1 : E → BitVec 64
  w2 : E → BitVec 64
  w3 : E → BitVec 64
  w4 : E → BitVec 64
  w5 : E → BitVec 64
  heap : E → SepProp
  w0_ne_err : ∀ e, w0 e ≠ errTag
  w0_ne_ok : ∀ e, w0 e ≠ okTagVec
  w0_ne_pending : ∀ e, w0 e ≠ 0xFFFFFFFFFFFFFFFD#64

/-- The 48-byte `SignalProtocolError` value `e` at address `p`. -/
def speErrAt {E : Type} (S : SpeErrSpec E) (p : BitVec 64) (e : E) : SepProp :=
  speWordsAt p (S.w0 e) (S.w1 e) (S.w2 e) (S.w3 e) (S.w4 e) (S.w5 e) ∗ S.heap e

/-- Canonical empty `SpeErrSpec` for infallible store implementations (such as `OneKeyStore`). -/
def pemptySpeErrSpec : SpeErrSpec PEmpty where
  w0 := fun e => e.elim
  w1 := fun e => e.elim
  w2 := fun e => e.elim
  w3 := fun e => e.elim
  w4 := fun e => e.elim
  w5 := fun e => e.elim
  heap := fun e => e.elim
  w0_ne_err := fun e => e.elim
  w0_ne_ok := fun e => e.elim
  w0_ne_pending := fun e => e.elim

/-- The 48-byte `Poll::Ready<Result<(), SignalProtocolError>>` written to `out` by
    `remove_pre_key` and `mark_kyber_pre_key_used` future polls:
    * `.ok ()`: word 0 is `-2` (`okTagVec`), bytes `8..48` are uninspected (`memRegion`);
    * `.error e`: the 48-byte `SignalProtocolError` `speErrAt S out e`. -/
def unitSpePollOutAt {E : Type} (S : SpeErrSpec E) (out : BitVec 64) : Except E Unit → SepProp
  | .ok () => (out ↦₆₄ okTagVec) ∗ memRegion (out + 8#64) 40
  | .error e => speErrAt S out e

/-! ## Shared shim / poll argument records for `(self, id : u32)` methods -/

/-- Arguments of a `(self, id : u32)` pre-key shim (`get_pre_key`, `remove_pre_key`,
    `get_signed_pre_key`, `get_kyber_pre_key`): `self` in `x0`, `id` in `w1`. -/
structure PreKeyShimCall where
  self : BitVec 64
  id : BitVec 32

/-- Ghost call record for polling a `(self, id : u32)` future (`fut` in `x0`, `sret` in `x8`). -/
structure PreKeyPollCall where
  fut : BitVec 64
  out : BitVec 64
  self : BitVec 64
  id : BitVec 32

/-! ## `PreKeyStoreSpec` (`PreKeyStore`) -/

/-- Pure data, trace projections, answer relations, and separation-logic predicates of a
    `PreKeyStore` implementation (`get_pre_key` at `pk_vt + 0x18`, `remove_pre_key` at
    `pk_vt + 0x28`). -/
structure PreKeyStoreSpec (A : RustAlloc) (b : BitVec 64) where
  /-- `dyn PreKeyStore` trait-object vtable address. -/
  pk_vt : BitVec 64
  /-- Logical state of the pre-key store. -/
  PkState : Type
  /-- Separation-logic predicate for the pre-key store object at `self`. -/
  storeAt : BitVec 64 → PkState → SepProp
  /-- Pure well-formedness predicate carried by every returned `PreKeyRecord`. -/
  RecOk : PreKeyRecord → Prop := fun _ => True
  /-- Pure precondition on the key id passed to `get_pre_key`'s poll. -/
  getIdOk : BitVec 32 → Prop := fun _ => True
  /-- Pure precondition on the key id passed to `remove_pre_key`'s poll. -/
  removeIdOk : BitVec 32 → Prop := fun _ => True
  /-- Entry file-system predicate required by the polls (`True` for in-memory stores;
      `(· = F0)` for the CLI's file-backed stores). -/
  envOk : FsFiles → Prop := fun _ => True
  /-- Point-wise file-descriptor predicate carried across the store's ops (`True` by default for
      in-memory stores; `FdsGe3Closed` for the CLI's file-backed stores). -/
  fdsOk : FsState → Prop := fun _ => True
  /-- Kit witness type for `get_pre_key` `Err` returns (`PEmpty` when infallible). -/
  GetErr : Type
  /-- Kit witness type for `remove_pre_key` `Err` returns (`PEmpty` when infallible). -/
  RemoveErr : Type
  /-- 48-byte `SignalProtocolError` layout for `GetErr`. -/
  getErr : SpeErrSpec GetErr
  /-- 48-byte `SignalProtocolError` layout for `RemoveErr`. -/
  removeErr : SpeErrSpec RemoveErr
  /-- Post-`get_pre_key` state transition (`fun st _ _ => st` for read-only `get_pre_key`). -/
  getUpdate : PkState → BitVec 32 → Except GetErr PreKeyRecord → PkState := fun st _ _ => st
  /-- Post-`remove_pre_key` state transition. -/
  removeUpdate : PkState → BitVec 32 → Except RemoveErr Unit → PkState
  /-- Pure relation tying `(st0, id)` to the `get_pre_key` answer. -/
  getRel : PkState → BitVec 32 → Except GetErr PreKeyRecord → Prop
  /-- Pure relation tying `(st0, id)` to the `remove_pre_key` answer. -/
  removeRel : PkState → BitVec 32 → Except RemoveErr Unit → Prop
  /-- Trace events emitted by a `get_pre_key` call. -/
  getEvs : BitVec 32 → Except GetErr PreKeyRecord → List TraceEvent := fun _ _ => []
  /-- Trace events emitted by a `remove_pre_key` call. -/
  removeEvs : BitVec 32 → Except RemoveErr Unit → List TraceEvent := fun _ _ => []
  /-- Slot target offset for `get_pre_key` (`pk_vt + 0x18 ↦ b + getShimOff`). -/
  getShimOff : BitVec 64
  /-- Future vtable offset for `get_pre_key` (`b + getFutVtOff`). -/
  getFutVtOff : BitVec 64
  /-- Poll entrypoint offset for `get_pre_key` (`b + getPollOff`). -/
  getPollOff : BitVec 64
  /-- Drop entrypoint offset for `get_pre_key`'s future (`b + getFutDropOff`). -/
  getFutDropOff : BitVec 64
  /-- Heap box size in bytes for `get_pre_key`'s future (`16` in CLI and `OneKeyStore`). -/
  getBoxSize : Nat
  /-- Slot target offset for `remove_pre_key` (`pk_vt + 0x28 ↦ b + removeShimOff`). -/
  removeShimOff : BitVec 64
  /-- Future vtable offset for `remove_pre_key` (`b + removeFutVtOff`). -/
  removeFutVtOff : BitVec 64
  /-- Poll entrypoint offset for `remove_pre_key` (`b + removePollOff`). -/
  removePollOff : BitVec 64
  /-- Drop entrypoint offset for `remove_pre_key`'s future (`b + removeFutDropOff`). -/
  removeFutDropOff : BitVec 64
  /-- Heap box size in bytes for `remove_pre_key`'s future (`16` in CLI and `OneKeyStore`). -/
  removeBoxSize : Nat
  /-- Stack budget for `get_pre_key` shim. -/
  getShimStack : Nat
  /-- Stack budget for `get_pre_key` poll. -/
  getPollStack : Nat
  /-- Stack budget for `remove_pre_key` shim. -/
  removeShimStack : Nat
  /-- Stack budget for `remove_pre_key` poll. -/
  removePollStack : Nat
  /-- Future box predicate for `get_pre_key` (`st = 0#8` before first poll, `1#8` after). -/
  getBoxAt : (box self : BitVec 64) → (id : BitVec 32) → (state : BitVec 8) → SepProp
  /-- Future box predicate for `remove_pre_key` (`st = 0#8` before first poll, `1#8` after). -/
  removeBoxAt : (box self : BitVec 64) → (id : BitVec 32) → (state : BitVec 8) → SepProp
  /-- Any `getBoxAt` state entails raw `memRegion` of `getBoxSize` bytes for deallocation. -/
  getBoxAt_memRegion : ∀ box self id st, getBoxAt box self id st ⊢ memRegion box getBoxSize
  /-- Any `removeBoxAt` state entails raw `memRegion` of `removeBoxSize` bytes for deallocation. -/
  removeBoxAt_memRegion : ∀ box self id st,
    removeBoxAt box self id st ⊢ memRegion box removeBoxSize
  /-- `getBoxSize` is non-zero as a 64-bit word (so `cbz` before `__rust_dealloc` does not skip). -/
  getBoxSize_ne_zero : BitVec.ofNat 64 getBoxSize ≠ 0#64
  /-- `removeBoxSize` is non-zero as a 64-bit word. -/
  removeBoxSize_ne_zero : BitVec.ofNat 64 removeBoxSize ≠ 0#64
  /-- `getBoxSize` fits in 64 bits. -/
  getBoxSize_lt : getBoxSize < 2 ^ 64
  /-- `removeBoxSize` fits in 64 bits. -/
  removeBoxSize_lt : removeBoxSize < 2 ^ 64
  /-- `b + getFutDropOff` is non-zero for page-aligned `b`. -/
  getFutDrop_ne_zero : b &&& 0xfff#64 = 0#64 → b + getFutDropOff ≠ 0#64
  /-- `b + removeFutDropOff` is non-zero for page-aligned `b`. -/
  removeFutDrop_ne_zero : b &&& 0xfff#64 = 0#64 → b + removeFutDropOff ≠ 0#64

/-- Alias matching the `*Kit` naming convention alongside `PreKeyStoreSpec`. -/
abbrev PreKeyStoreKit := PreKeyStoreSpec

/-- The 56-byte `Poll::Ready<Result<PreKeyRecord, SignalProtocolError>>` written to `out` by
    `get_pre_key`'s future poll:
    * `.ok r`: `RecOk r` and `preKeyRecordAt A out r` (`56` B);
    * `.error e`: word 0 is `-1` (`errTag`) followed by `speErrAt kit.getErr (out + 8) e` (`48` B). -/
def preKeyGetPollOutAt {A : RustAlloc} {b : BitVec 64} (kit : PreKeyStoreSpec A b)
    (out : BitVec 64) : Except kit.GetErr PreKeyRecord → SepProp
  | .ok r => ⌜kit.RecOk r⌝ ∗ preKeyRecordAt A out r
  | .error e => (out ↦₆₄ errTag) ∗ speErrAt kit.getErr (out + 8#64) e

/-- The 48-byte `Poll::Ready<Result<(), SignalProtocolError>>` written to `out` by
    `remove_pre_key`'s future poll. -/
abbrev preKeyRemovePollOutAt {A : RustAlloc} {b : BitVec 64} (kit : PreKeyStoreSpec A b)
    (out : BitVec 64) : Except kit.RemoveErr Unit → SepProp :=
  unitSpePollOutAt kit.removeErr out

/-- Generic `get_pre_key` shim spec parameterized by `kit : PreKeyStoreSpec A b`. -/
def kitPreKeyGetShimSpec {A : RustAlloc} {b : BitVec 64} (kit : PreKeyStoreSpec A b) :
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

/-- Generic `remove_pre_key` shim spec parameterized by `kit : PreKeyStoreSpec A b`. -/
def kitPreKeyRemoveShimSpec {A : RustAlloc} {b : BitVec 64} (kit : PreKeyStoreSpec A b) :
    Spec PreKeyShimCall where
  pre := fun x s =>
    ⌜(b &&& 0xfff#64) = 0#64 ∧ s.readReg64 .x0 = x.self ∧ s.readReg32 .x1 = x.id⌝ ∗
      A.pool ∗ stackAt s.sp kit.removeShimStack
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x1 = b + kit.removeFutVtOff ∧ sf.readReg64 .x0 ≠ 0#64 ∧
      (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
      A.live (sf.readReg64 .x0) kit.removeBoxSize 8 ∗
      kit.removeBoxAt (sf.readReg64 .x0) x.self x.id 0#8 ∗
      A.pool ∗ stackAt s0.sp kit.removeShimStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Generic `get_pre_key` poll spec parameterized by `kit : PreKeyStoreSpec A b`. -/
def kitPreKeyGetPollSpec {A : RustAlloc} {b : BitVec 64} (kit : PreKeyStoreSpec A b) :
    Spec (PreKeyPollCall × kit.PkState) where
  pre := fun (x, st0) s =>
    ⌜(b &&& 0xfff#64) = 0#64 ∧ s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧
      kit.getIdOk x.id⌝ ∗
      kit.getBoxAt x.fut x.self x.id 0#8 ∗
      kit.storeAt x.self st0 ∗ memRegion x.out 56 ∗
      A.pool ∗ stackAt s.sp kit.getPollStack
  post := fun (x, st0) s0 sf =>
    ∃∗ ans : Except kit.GetErr PreKeyRecord,
      ⌜kit.getRel st0 x.id ans ∧ sf.trace = s0.trace ++ kit.getEvs x.id ans⌝ ∗
      kit.getBoxAt x.fut x.self x.id 1#8 ∗
      kit.storeAt x.self (kit.getUpdate st0 x.id ans) ∗
      preKeyGetPollOutAt kit x.out ans ∗
      A.pool ∗ stackAt s0.sp kit.getPollStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Generic `remove_pre_key` poll spec parameterized by `kit : PreKeyStoreSpec A b`. -/
def kitPreKeyRemovePollSpec {A : RustAlloc} {b : BitVec 64} (kit : PreKeyStoreSpec A b) :
    Spec (PreKeyPollCall × kit.PkState) where
  pre := fun (x, st0) s =>
    ⌜(b &&& 0xfff#64) = 0#64 ∧ s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧
      kit.removeIdOk x.id⌝ ∗
      kit.removeBoxAt x.fut x.self x.id 0#8 ∗
      kit.storeAt x.self st0 ∗ memRegion x.out 48 ∗
      A.pool ∗ stackAt s.sp kit.removePollStack
  post := fun (x, st0) s0 sf =>
    ∃∗ ans : Except kit.RemoveErr Unit,
      ⌜kit.removeRel st0 x.id ans ∧ sf.trace = s0.trace ++ kit.removeEvs x.id ans⌝ ∗
      kit.removeBoxAt x.fut x.self x.id 1#8 ∗
      kit.storeAt x.self (kit.removeUpdate st0 x.id ans) ∗
      preKeyRemovePollOutAt kit x.out ans ∗
      A.pool ∗ stackAt s0.sp kit.removePollStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- `get_pre_key` poll spec with `kit.envOk` on the entry files. -/
abbrev kitPreKeyGetPollSpecE {A : RustAlloc} {b : BitVec 64} (kit : PreKeyStoreSpec A b) :
    Spec (PreKeyPollCall × kit.PkState) :=
  withEnvPre (kitPreKeyGetPollSpec kit) fun s => kit.envOk s.fs.files

/-- `remove_pre_key` poll spec with `kit.envOk` on the entry files. -/
abbrev kitPreKeyRemovePollSpecE {A : RustAlloc} {b : BitVec 64} (kit : PreKeyStoreSpec A b) :
    Spec (PreKeyPollCall × kit.PkState) :=
  withEnvPre (kitPreKeyRemovePollSpec kit) fun s => kit.envOk s.fs.files

/-- The pre-key store's own trace events contain no file-system event (`FsCtx`'s `Q`). -/
def PreKeyStoreSpec.Quiet {A : RustAlloc} {b : BitVec 64} (kit : PreKeyStoreSpec A b) : Prop :=
  (∀ id ans, NoFsEv (kit.getEvs id ans)) ∧
    (∀ id ans, NoFsEv (kit.removeEvs id ans))

/-- Read-only `.rodata` vtable slots required by `kit : PreKeyStoreSpec A img.base` under
    `img.FrozenLoaded`. Store `drop_in_place` and `save_pre_key` (`+0x20`) are never called by
    `decrypt_prekey`. -/
structure PreKeyVtablesOk {A : RustAlloc} (img : Obj.Image)
    (kit : PreKeyStoreSpec A img.base) : Prop where
  getSlot : ∀ {s : State} {P : SepProp}, img.FrozenLoaded s → (s.mem ⊨ P) →
    s.mem ⊨ ((kit.pk_vt + 0x18#64) ↦₆₄ᵣ (img.base + kit.getShimOff)) ∗ P
  removeSlot : ∀ {s : State} {P : SepProp}, img.FrozenLoaded s → (s.mem ⊨ P) →
    s.mem ⊨ ((kit.pk_vt + 0x28#64) ↦₆₄ᵣ (img.base + kit.removeShimOff)) ∗ P
  getFutDrop : ∀ {s : State} {P : SepProp}, img.FrozenLoaded s → (s.mem ⊨ P) →
    s.mem ⊨ ((img.base + kit.getFutVtOff) ↦₆₄ᵣ (img.base + kit.getFutDropOff)) ∗ P
  getFutSize : ∀ {s : State} {P : SepProp}, img.FrozenLoaded s → (s.mem ⊨ P) →
    s.mem ⊨ ((img.base + kit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.getBoxSize) ∗ P
  getFutAlign : ∀ {s : State} {P : SepProp}, img.FrozenLoaded s → (s.mem ⊨ P) →
    s.mem ⊨ ((img.base + kit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗ P
  getFutPoll : ∀ {s : State} {P : SepProp}, img.FrozenLoaded s → (s.mem ⊨ P) →
    s.mem ⊨ ((img.base + kit.getFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + kit.getPollOff)) ∗ P
  removeFutDrop : ∀ {s : State} {P : SepProp}, img.FrozenLoaded s → (s.mem ⊨ P) →
    s.mem ⊨ ((img.base + kit.removeFutVtOff) ↦₆₄ᵣ (img.base + kit.removeFutDropOff)) ∗ P
  removeFutSize : ∀ {s : State} {P : SepProp}, img.FrozenLoaded s → (s.mem ⊨ P) →
    s.mem ⊨ ((img.base + kit.removeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.removeBoxSize) ∗ P
  removeFutAlign : ∀ {s : State} {P : SepProp}, img.FrozenLoaded s → (s.mem ⊨ P) →
    s.mem ⊨ ((img.base + kit.removeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗ P
  removeFutPoll : ∀ {s : State} {P : SepProp}, img.FrozenLoaded s → (s.mem ⊨ P) →
    s.mem ⊨ ((img.base + kit.removeFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + kit.removePollOff)) ∗ P

/-- Code-contract bundle for `kit : PreKeyStoreSpec A b` (without `img.FrozenLoaded`, as used by
    in-memory E2E stores). -/
structure PreKeyStoreKitOk {A : RustAlloc} {b : BitVec 64} (kit : PreKeyStoreSpec A b)
    (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop where
  getShim : subroutine_ok (tripleRatchetProgAt b C ctl abs) (b + kit.getShimOff)
    (kitPreKeyGetShimSpec kit)
  getPoll : subroutine_ok (tripleRatchetProgAt b C ctl abs) (b + kit.getPollOff)
    (kitPreKeyGetPollSpecE kit)
  getFutDrop : subroutine_ok (tripleRatchetProgAt b C ctl abs) (b + kit.getFutDropOff)
    futDropSpec
  removeShim : subroutine_ok (tripleRatchetProgAt b C ctl abs) (b + kit.removeShimOff)
    (kitPreKeyRemoveShimSpec kit)
  removePoll : subroutine_ok (tripleRatchetProgAt b C ctl abs) (b + kit.removePollOff)
    (kitPreKeyRemovePollSpecE kit)
  removeFutDrop : subroutine_ok (tripleRatchetProgAt b C ctl abs) (b + kit.removeFutDropOff)
    futDropSpec

/-- Image-relocated code-contract bundle (`Spec.inImage ... img`, providing `img.FrozenLoaded`
    to every shim, poll, and future drop, as satisfied directly by the CLI store specs). -/
structure PreKeyStoreKitOkImg {A : RustAlloc} (img : Obj.Image)
    (kit : PreKeyStoreSpec A img.base) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop where
  getShim : subroutine_ok (tripleRatchetProgAt img.base C ctl abs) (img.base + kit.getShimOff)
    ((kitPreKeyGetShimSpec kit).inImage img)
  getPoll : subroutine_ok (tripleRatchetProgAt img.base C ctl abs) (img.base + kit.getPollOff)
    ((kitPreKeyGetPollSpecE kit).inImage img)
  getFutDrop : subroutine_ok (tripleRatchetProgAt img.base C ctl abs) (img.base + kit.getFutDropOff)
    (futDropSpec.inImage img)
  removeShim : subroutine_ok (tripleRatchetProgAt img.base C ctl abs) (img.base + kit.removeShimOff)
    ((kitPreKeyRemoveShimSpec kit).inImage img)
  removePoll : subroutine_ok (tripleRatchetProgAt img.base C ctl abs) (img.base + kit.removePollOff)
    ((kitPreKeyRemovePollSpecE kit).inImage img)
  removeFutDrop : subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
    (img.base + kit.removeFutDropOff) (futDropSpec.inImage img)

end CryptoVerification.LibsignalPublicApi.StoreKit
