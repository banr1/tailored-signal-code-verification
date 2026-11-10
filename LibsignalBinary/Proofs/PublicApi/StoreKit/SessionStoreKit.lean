/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.StoreKit.Defs
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Fs
public import LibsignalBinary.Proofs.PublicApi.StoreSession.StoreCallSite

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.StoreKit

open Arm64 ProofLib CryptoVerification.RustHeap CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoGames CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalPublicApi.StoreSession

/-!
# Abstract `SessionStore` Interface (`SessionStoreSpec`)

Parameterizes `session_message_decrypt_signal_with_stores` and
`session_message_encrypt_with_stores` over a `SessionStore` implementation:
1. Vtable addresses (`ss_vt`, `id_vt`).
2. `load_session` (`ss_vt + 0x18`) and `store_session` (`ss_vt + 0x20`) shims, future vtables,
   box sizes, poll/drop entrypoints, stack budgets, and `subroutine_ok` contracts.
3. Trace projections (`loadEvs`, `storeEvs`, `traceOf`) for `StoreCall` sequences.
4. Abstract `StoreState`, `storeAt`, answer relations (`loadRel`, `storeRel`), and `storeUpdate`.
-/

/-- Hook bundle omitting `load_session` and `store_session` hooks for generic
    `MessageDecrypt` / `MessageEncrypt` callers backed by concrete `SessionStore` implementations. -/
structure PublicApiHooksNoSessionStore (C : Crypto) (A : RustAlloc) (S : SpqrModel)
    (abs : String → Option (State → State)) : Prop extends TripleRatchetHooks C A S abs where
  isTrusted : HookSat abs isTrustedHookName (isTrustedSpec A)
  saveIdentity : HookSat abs saveIdentityHookName (saveIdentitySpec A)
  timeAdd : HookSat abs timeAddHookName timeAddSpec
  durationSince : HookSat abs durationSinceHookName durationSinceSpec
  stringClone : HookSat abs stringCloneHookName (stringCloneSpec A)

theorem PublicApiHooks.toNoSessionStore {C : Crypto} {A : RustAlloc} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (h : PublicApiHooks C A S encRecord abs) : PublicApiHooksNoSessionStore C A S abs where
  toTripleRatchetHooks := h.toTripleRatchetHooks
  isTrusted := h.isTrusted
  saveIdentity := h.saveIdentity
  timeAdd := h.timeAdd
  durationSince := h.durationSince
  stringClone := h.stringClone

/-- The 48-byte `Poll<Result<(), SPE>>` written by `store_session`'s future poll:
    on `Ok(())`, word 0 is `-2` (`0xFFFFFFFFFFFFFFFE`) and bytes `8..48` are uninspected;
    on `Err(())`, word 0 is `speWord 26` followed by the `ApplicationCallbackError` payload. -/
def storePollOutAt (b out : BitVec 64) : Except Unit Unit → SepProp
  | .ok () => (out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ memRegion (out + 8#64) 40
  | .error () =>
    -- Hook-store error description string (`"store hook"`, unreachable for infallible in-memory kits)
    (out ↦₆₄ 0x800000000000001A#64) ∗ ((out + 8#64) ↦₆₄ (b + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}")))) ∗
      ((out + 0x10#64) ↦₆₄ 10#64) ∗ ((out + 0x18#64) ↦₆₄ 1#64) ∗
      ((out + 0x20#64) ↦₆₄ (b + bv% (ls_xref% (ls_off% "<libsignal_protocol::fingerprint::ScannableFingerprint>::serialize" + 620) (ls_off% "<libsignal_protocol::fingerprint::ScannableFingerprint>::serialize" + 624) + 16))) ∗ ((b + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))) ↦ᵣ storeHookStr) ∗
      memRegion (out + 0x28#64) 8

/-- Pure data, trace projections, answer relations, and separation-logic predicates of a
    `SessionStore` implementation. -/
structure SessionStoreSpec (A : RustAlloc) (b : BitVec 64) where
  /-- `SessionStore` trait-object vtable address (`E₀`: `b + 0x4dbf8#64`). -/
  ss_vt : BitVec 64
  /-- `IdentityKeyStore` trait-object vtable address (`E₀`: `b + 0x4dc20#64`). -/
  id_vt : BitVec 64
  /-- Logical state of the session store (`Unit` for `E₀`). -/
  StoreState : Type
  /-- Separation-logic predicate for the session store object at `self` (`emp` for `E₀`). -/
  storeAt : BitVec 64 → StoreState → SepProp
  /-- Store-side remote address invariant required by `load_session` / `store_session` polls
      (`fun _ => True` for `E₀`, `rem = peer.val` for `InMem`). -/
  addrOk : AddrVal → Prop := fun _ => True
  /-- Files the store's polls read (`True` for `E₀` / `InMem`; `(· = F0)` for the CLI's Files kits,
      whose `loadRel` is stated on the files `F0` at the libsignal call's entry). Required by the
      polls through `kitStorePollSpecE`; see `StoreKit/Fs.lean`. -/
  envOk : FsFiles → Prop := fun _ => True
  /-- Point-wise file-descriptor predicate carried across the store's ops (`True` by default for
      `E₀` / `InMem`; `FdsGe3Closed` for the CLI's file-backed kits). -/
  fdsOk : FsState → Prop := fun _ => True
  /-- Store-side record invariant required by `store_session` poll (`fun _ => True` for `E₀`,
      `L2anks` / `RecordInScope` for `M`). -/
  RecOk : SessionRecord (List (BitVec 8)) → Prop
  /-- Post-`store_session` state update (`fun _ _ _ _ => ()` for `E₀`). -/
  storeUpdate : StoreState → AddrVal → SessionRecord (List (BitVec 8)) → Except Unit Unit → StoreState
  /-- Pure relation tying the initial store state `st0` and remote address to the `load_session`
      answer (`fun _ _ _ => True` for `E₀`). -/
  loadRel : StoreState → AddrVal → Except Unit (Option (SessionRecord (List (BitVec 8)))) → Prop
  /-- Pure relation tying the store state `st0`, remote address, and record to the `store_session`
      answer (`fun _ _ _ _ => True` for `E₀`). -/
  storeRel : StoreState → AddrVal → SessionRecord (List (BitVec 8)) → Except Unit Unit → Prop
  /-- Trace events emitted by a `load_session` call. -/
  loadEvs : (SessionRecord (List (BitVec 8)) → List (BitVec 8)) →
    AddrVal → Except Unit (Option (SessionRecord (List (BitVec 8)))) → List TraceEvent
  /-- Trace events emitted by a `store_session` call. -/
  storeEvs : (SessionRecord (List (BitVec 8)) → List (BitVec 8)) →
    AddrVal → SessionRecord (List (BitVec 8)) → Except Unit Unit → List TraceEvent
  /-- Trace events emitted by a list of `StoreCall`s. -/
  traceOf : (SessionRecord (List (BitVec 8)) → List (BitVec 8)) →
    StoreAnswers (List (BitVec 8)) Unit → List (StoreCall AddrVal (List (BitVec 8))) → List TraceEvent
  /-- Coherence of `traceOf` on `[.loadSession rem]`. -/
  traceOf_load : ∀ encRecord ans rem,
    traceOf encRecord ans [.loadSession rem] = loadEvs encRecord rem ans.loadSession
  /-- Coherence of `traceOf` on `[.loadSession rem, .isTrustedIdentity rem k dir]`. -/
  traceOf_load_trust : ∀ encRecord ans rem k dir,
    traceOf encRecord ans [.loadSession rem, .isTrustedIdentity rem k dir] =
      loadEvs encRecord rem ans.loadSession ++
      [trustEvent rem k dir ans.isTrustedIdentity]
  /-- Coherence of `traceOf` on `[.loadSession rem, .isTrustedIdentity rem k dir, .saveIdentity rem k]`. -/
  traceOf_load_trust_save : ∀ encRecord ans rem k dir,
    traceOf encRecord ans [.loadSession rem, .isTrustedIdentity rem k dir, .saveIdentity rem k] =
      loadEvs encRecord rem ans.loadSession ++
      [trustEvent rem k dir ans.isTrustedIdentity,
       saveEvent rem k ans.saveIdentity]
  /-- Coherence of `traceOf` on all 4 store calls. -/
  traceOf_all4 : ∀ encRecord ans rem k dir r',
    traceOf encRecord ans
      [.loadSession rem, .isTrustedIdentity rem k dir, .saveIdentity rem k, .storeSession rem r'] =
      loadEvs encRecord rem ans.loadSession ++
      [trustEvent rem k dir ans.isTrustedIdentity,
       saveEvent rem k ans.saveIdentity] ++
      storeEvs encRecord rem r' ans.storeSession
  /-- Coherence of `traceOf` on `[.loadSession rem, .storeSession rem r']` (used in MessageEncrypt Signal path). -/
  traceOf_load_store : ∀ encRecord ans rem r',
    traceOf encRecord ans [.loadSession rem, .storeSession rem r'] =
      loadEvs encRecord rem ans.loadSession ++
      storeEvs encRecord rem r' ans.storeSession
  /-- Slot target offset for `load_session` (`ss_vt + 0x18 ↦ b + loadShimOff`). -/
  loadShimOff : BitVec 64
  /-- Future vtable offset for `load_session` (`b + loadFutVtOff`). -/
  loadFutVtOff : BitVec 64
  /-- Poll entrypoint offset for `load_session` (`b + loadPollOff`). -/
  loadPollOff : BitVec 64
  /-- Drop entrypoint offset for `load_session` future (`0x42a44` in `E₀`). -/
  loadFutDropOff : BitVec 64
  /-- Box allocation size in bytes for `load_session` future (`24` in `E₀`). -/
  loadBoxSize : Nat
  /-- Slot target offset for `store_session` (`ss_vt + 0x20 ↦ b + storeShimOff`). -/
  storeShimOff : BitVec 64
  /-- Future vtable offset for `store_session` (`b + storeFutVtOff`). -/
  storeFutVtOff : BitVec 64
  /-- Poll entrypoint offset for `store_session` (`b + storePollOff`). -/
  storePollOff : BitVec 64
  /-- Drop entrypoint offset for `store_session` future (`0x42a44` in `E₀`). -/
  storeFutDropOff : BitVec 64
  /-- Box allocation size in bytes for `store_session` future (`32` in `E₀`). -/
  storeBoxSize : Nat
  /-- Stack budget for `load_session` shim. -/
  loadShimStack : Nat
  /-- Stack budget for `load_session` poll. -/
  loadPollStack : Nat
  /-- Stack budget for `store_session` shim. -/
  storeShimStack : Nat
  /-- Stack budget for `store_session` poll. -/
  storePollStack : Nat
  /-- Separation-logic predicate for the `load_session` future box contents (excluding `A.live`). -/
  loadBoxAt : (box self addrA : BitVec 64) → (state : BitVec 8) → SepProp
  /-- Separation-logic predicate for the `store_session` future box contents (excluding `A.live`). -/
  storeBoxAt : (box self addrA recA : BitVec 64) → (state : BitVec 8) → SepProp
  /-- Any `loadBoxAt` state entails raw `memRegion` of `loadBoxSize` bytes for deallocation. -/
  loadBoxAt_memRegion : ∀ box self addrA st,
    loadBoxAt box self addrA st ⊢ memRegion box loadBoxSize
  /-- Any `storeBoxAt` state entails raw `memRegion` of `storeBoxSize` bytes for deallocation. -/
  storeBoxAt_memRegion : ∀ box self addrA recA st,
    storeBoxAt box self addrA recA st ⊢ memRegion box storeBoxSize
  /-- `loadBoxSize` is non-zero as a 64-bit word (so `__rust_dealloc` is not skipped by `cbz`). -/
  loadBoxSize_ne_zero : BitVec.ofNat 64 loadBoxSize ≠ 0#64
  /-- `storeBoxSize` is non-zero as a 64-bit word (so `__rust_dealloc` is not skipped by `cbz`). -/
  storeBoxSize_ne_zero : BitVec.ofNat 64 storeBoxSize ≠ 0#64
  /-- `loadBoxSize` fits in 64 bits. -/
  loadBoxSize_lt : loadBoxSize < 2 ^ 64
  /-- `storeBoxSize` fits in 64 bits. -/
  storeBoxSize_lt : storeBoxSize < 2 ^ 64
  /-- `b + loadFutDropOff` is non-zero for page-aligned `b` (so `cbz` before `futDrop` does not skip). -/
  loadFutDrop_ne_zero : b &&& 0xfff#64 = 0#64 → b + loadFutDropOff ≠ 0#64
  /-- `b + storeFutDropOff` is non-zero for page-aligned `b` (so `cbz` before `futDrop` does not skip). -/
  storeFutDrop_ne_zero : b &&& 0xfff#64 = 0#64 → b + storeFutDropOff ≠ 0#64

namespace SessionStoreSpec

variable {A : RustAlloc} {b : BitVec 64} (kit : SessionStoreSpec A b)

/-- Resulting `StoreState` after executing a list of `StoreCall`s starting from `st0`:
    `storeUpdate st0 rem r' ans.storeSession` when `.storeSession rem r'` ran, and `st0` otherwise. -/
def storeFinal (st0 : kit.StoreState) (ans : StoreAnswers (List (BitVec 8)) Unit) :
    List (StoreCall AddrVal (List (BitVec 8))) → kit.StoreState
  | [] => st0
  | .storeSession rem r' :: cs =>
      storeFinal (kit.storeUpdate st0 rem r' ans.storeSession) ans cs
  | _ :: cs => storeFinal st0 ans cs

/-- Pure relation tying `st0` and `ans` across a list of `StoreCall`s: requires `kit.loadRel`
    on every `.loadSession` call and `kit.storeRel` on every `.storeSession` call. -/
def callsRel (st0 : kit.StoreState) (ans : StoreAnswers (List (BitVec 8)) Unit) :
    List (StoreCall AddrVal (List (BitVec 8))) → Prop
  | [] => True
  | .loadSession rem :: cs => kit.loadRel st0 rem ans.loadSession ∧ callsRel st0 ans cs
  | .storeSession rem r' :: cs => kit.storeRel st0 rem r' ans.storeSession ∧ callsRel st0 ans cs
  | _ :: cs => callsRel st0 ans cs

/-- Combined scope predicate on a loaded record `r`: both `Scope r` (from `loadPollOutAtS Scope`)
    and `kit.loadRel st0 rem (.ok (some r))` (from `kitLoadPollSpecS`). -/
def ScopeAt (Scope : SessionRecord (List (BitVec 8)) → Prop) (st0 : kit.StoreState)
    (rem : AddrVal) (r : SessionRecord (List (BitVec 8))) : Prop :=
  Scope r ∧ kit.loadRel st0 rem (.ok (some r))

end SessionStoreSpec

theorem hookLoadBoxAt_memRegion (box self addrA : BitVec 64) (st : BitVec 8) :
    (box ↦₆₄ self) ∗ ((box + 8#64) ↦₆₄ addrA) ∗ ((box + 0x10#64) ↦₈ st) ∗
      memRegion (box + 0x11#64) 7 ⊢ memRegion box 24 := by
  rw [show (24 : Nat) = 8 + (8 + (1 + 7)) from rfl,
    memRegion_split box 8 16 (by decide),
    memRegion_split (box + 8#64) 8 8 (by decide),
    memRegion_split (box + 8#64 + 8#64) 1 7 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono_left (pointsTo8_entails_memRegion _ _)))

theorem hookStoreBoxAt_memRegion (box self addrA recA : BitVec 64) (st : BitVec 8) :
    (box ↦₆₄ self) ∗ ((box + 8#64) ↦₆₄ addrA) ∗ ((box + 16#64) ↦₆₄ recA) ∗
      ((box + 24#64) ↦₈ st) ∗ memRegion (box + 25#64) 7 ⊢ memRegion box 32 := by
  rw [show (32 : Nat) = 8 + (8 + (8 + (1 + 7))) from rfl,
    memRegion_split box 8 24 (by decide),
    memRegion_split (box + 8#64) 8 16 (by decide),
    memRegion_split (box + 8#64 + 8#64) 8 8 (by decide),
    memRegion_split (box + 8#64 + 8#64 + 8#64) 1 7 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono_left (pointsTo8_entails_memRegion _ _))))

/-- Canonical `E₀` (`HookSessionStore`) instance of `SessionStoreSpec`. -/
def hookSessionStoreSpec (A : RustAlloc) (b : BitVec 64) : SessionStoreSpec A b where
  ss_vt := b + bv% (ls_xref% (ls_off% "<libsignal_protocol::proto::wire::PreKeySignalMessage as core::fmt::Debug>::fmt" + 100) (ls_off% "<libsignal_protocol::proto::wire::PreKeySignalMessage as core::fmt::Debug>::fmt" + 104) + 8)
  id_vt := b + bv% (ls_xref% (ls_off% "<libsignal_protocol::proto::wire::PreKeySignalMessage as core::fmt::Debug>::fmt" + 136) (ls_off% "<libsignal_protocol::proto::wire::PreKeySignalMessage as core::fmt::Debug>::fmt" + 140) + 16)
  StoreState := Unit
  storeAt := fun _ _ => .emp
  RecOk := fun _ => True
  storeUpdate := fun _ _ _ _ => ()
  loadRel := fun _ _ _ => True
  storeRel := fun _ _ _ _ => True
  loadEvs := fun encRecord rem ans => [loadEvent encRecord rem ans]
  storeEvs := fun encRecord rem r' ans => [storeSessionEvent encRecord rem r' ans]
  traceOf := fun encRecord ans calls => calls.map (storeEvent encRecord ans)
  traceOf_load := fun _ _ _ => rfl
  traceOf_load_trust := fun _ _ _ _ _ => rfl
  traceOf_load_trust_save := fun _ _ _ _ _ => rfl
  traceOf_all4 := fun _ _ _ _ _ _ => rfl
  traceOf_load_store := fun _ _ _ _ => rfl
  loadShimOff := bv% (ls_off% "<[u8] as subtle::ConstantTimeEq>::ct_eq" + 16712)
  loadFutVtOff := bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair::{closure#0}") - 16)
  loadPollOff := bv% (ls_off% "<[u8] as subtle::ConstantTimeEq>::ct_eq" + 15748)
  loadFutDropOff := bv% (ls_off% "<[u8] as subtle::ConstantTimeEq>::ct_eq" + 15744)
  loadBoxSize := 24
  storeShimOff := bv% (ls_off% "<[u8] as subtle::ConstantTimeEq>::ct_eq" + 16792)
  storeFutVtOff := bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id::{closure#0}") - 16)
  storePollOff := bv% (ls_off% "<[u8] as subtle::ConstantTimeEq>::ct_eq" + 15988)
  storeFutDropOff := bv% (ls_off% "<[u8] as subtle::ConstantTimeEq>::ct_eq" + 15744)
  storeBoxSize := 32
  loadShimStack := loadSessionShimStack
  loadPollStack := loadSessionPollStack
  storeShimStack := storeSessionShimStack
  storePollStack := storeSessionPollStack
  loadBoxAt := fun box self addrA st =>
    (box ↦₆₄ self) ∗ ((box + 8#64) ↦₆₄ addrA) ∗ ((box + 0x10#64) ↦₈ st) ∗
      memRegion (box + 0x11#64) 7
  storeBoxAt := fun box self addrA recA st =>
    (box ↦₆₄ self) ∗ ((box + 8#64) ↦₆₄ addrA) ∗ ((box + 16#64) ↦₆₄ recA) ∗
      ((box + 24#64) ↦₈ st) ∗ memRegion (box + 25#64) 7
  loadBoxAt_memRegion := hookLoadBoxAt_memRegion
  storeBoxAt_memRegion := hookStoreBoxAt_memRegion
  loadBoxSize_ne_zero := by decide
  storeBoxSize_ne_zero := by decide
  loadBoxSize_lt := by decide
  storeBoxSize_lt := by decide
  loadFutDrop_ne_zero := fun hb h => by
    rw [show b = 0#64 - bv% (ls_off% "<[u8] as subtle::ConstantTimeEq>::ct_eq" + 15744) by rw [← h, BitVec.add_sub_cancel]] at hb
    exact absurd hb (by decide)
  storeFutDrop_ne_zero := fun hb h => by
    rw [show b = 0#64 - bv% (ls_off% "<[u8] as subtle::ConstantTimeEq>::ct_eq" + 15744) by rw [← h, BitVec.add_sub_cancel]] at hb
    exact absurd hb (by decide)

theorem hookSessionStoreSpec_callsRel_true {A : RustAlloc} {b : BitVec 64}
    (ans : StoreAnswers (List (BitVec 8)) Unit) :
    ∀ calls, (hookSessionStoreSpec A b).callsRel () ans calls := by
  intro calls
  induction calls with
  | nil => trivial
  | cons c cs ih =>
    cases c
    · exact ⟨trivial, ih⟩
    · exact ih
    · exact ih
    · exact ⟨trivial, ih⟩

/-- Generic `load_session` shim spec parameterized by `kit : SessionStoreSpec A b`. -/
def kitLoadShimSpec {A : RustAlloc} {b : BitVec 64} (kit : SessionStoreSpec A b) :
    Spec LoadShimCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x1 = x.addrA⌝ ∗ A.pool ∗
      stackAt s.sp kit.loadShimStack
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x1 = b + kit.loadFutVtOff ∧ sf.readReg64 .x0 ≠ 0#64 ∧
      (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
      A.live (sf.readReg64 .x0) kit.loadBoxSize 8 ∗
      kit.loadBoxAt (sf.readReg64 .x0) x.self x.addrA 0#8 ∗
      A.pool ∗ stackAt s0.sp kit.loadShimStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Generic `store_session` shim spec parameterized by `kit : SessionStoreSpec A b`. -/
def kitStoreShimSpec {A : RustAlloc} {b : BitVec 64} (kit : SessionStoreSpec A b) :
    Spec StoreShimCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x1 = x.addrA ∧ s.readReg64 .x2 = x.recA⌝ ∗
      A.pool ∗ stackAt s.sp kit.storeShimStack
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x1 = b + kit.storeFutVtOff ∧ sf.readReg64 .x0 ≠ 0#64 ∧
      (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
      A.live (sf.readReg64 .x0) kit.storeBoxSize 8 ∗
      kit.storeBoxAt (sf.readReg64 .x0) x.self x.addrA x.recA 0#8 ∗
      A.pool ∗ stackAt s0.sp kit.storeShimStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Generic `load_session` poll spec parameterized by `kit : SessionStoreSpec A img.base`. -/
def kitLoadPollSpecS {A : RustAlloc} (img : Obj.Image) (kit : SessionStoreSpec A img.base)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) :
    Spec (LoadPollCall × BitVec 64 × kit.StoreState) where
  pre := fun (x, self, st0) s =>
    ⌜img.FrozenLoaded s ∧ s.symtab = img.symtab ∧
      s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧ kit.addrOk x.addr.val⌝ ∗
      kit.loadBoxAt x.fut self x.addrA 0#8 ∗ kit.storeAt self st0 ∗ memRegion x.out 368 ∗
      protocolAddressAt A x.addr x.addrA ∗ A.pool ∗ stackAt s.sp kit.loadPollStack
  post := fun (x, self, st0) s0 sf =>
    ∃∗ ans : Except Unit (Option (SessionRecord (List (BitVec 8)))),
      ⌜kit.loadRel st0 x.addr.val ans ∧
        sf.trace = s0.trace ++ kit.loadEvs encRecord x.addr.val ans⌝ ∗
      kit.loadBoxAt x.fut self x.addrA 1#8 ∗ kit.storeAt self st0 ∗
      loadPollOutAtS Scope A img.base x.out ans ∗
      protocolAddressAt A x.addr x.addrA ∗ A.pool ∗ stackAt s0.sp kit.loadPollStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Generic `store_session` poll spec parameterized by `kit : SessionStoreSpec A b`. -/
def kitStorePollSpec {A : RustAlloc} {b : BitVec 64} (kit : SessionStoreSpec A b)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) :
    Spec (StorePollCall × BitVec 64 × kit.StoreState) where
  pre := fun (x, self, st0) s =>
    ⌜s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧ kit.RecOk x.call.record ∧
      kit.addrOk x.call.addr.val⌝ ∗
      kit.storeBoxAt x.fut self x.call.addrA x.call.recA 0#8 ∗
      kit.storeAt self st0 ∗ memRegion x.out 48 ∗
      protocolAddressAt A x.call.addr x.call.addrA ∗
      sessionRecordAt A x.call.recA x.call.g x.call.record ∗
      A.pool ∗ stackAt s.sp kit.storePollStack
  post := fun (x, self, st0) s0 sf =>
    ∃∗ ans : Except Unit Unit,
      ⌜kit.storeRel st0 x.call.addr.val x.call.record ans ∧
        sf.trace = s0.trace ++ kit.storeEvs encRecord x.call.addr.val x.call.record ans⌝ ∗
      kit.storeBoxAt x.fut self x.call.addrA x.call.recA 1#8 ∗
      kit.storeAt self (kit.storeUpdate st0 x.call.addr.val x.call.record ans) ∗
      storePollOutAt b x.out ans ∗
      protocolAddressAt A x.call.addr x.call.addrA ∗
      sessionRecordAt A x.call.recA x.call.g x.call.record ∗
      A.pool ∗ stackAt s0.sp kit.storePollStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- The `load_session` poll spec with `kit.envOk` on the entry files. -/
abbrev kitLoadPollSpecSE {A : RustAlloc} (img : Obj.Image) (kit : SessionStoreSpec A img.base)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) :
    Spec (LoadPollCall × BitVec 64 × kit.StoreState) :=
  withEnvPre (kitLoadPollSpecS img kit Scope encRecord) fun s => kit.envOk s.fs.files

/-- The `store_session` poll spec with `kit.envOk` on the entry files. -/
abbrev kitStorePollSpecE {A : RustAlloc} {b : BitVec 64} (kit : SessionStoreSpec A b)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) :
    Spec (StorePollCall × BitVec 64 × kit.StoreState) :=
  withEnvPre (kitStorePollSpec kit encRecord) fun s => kit.envOk s.fs.files

/-- The session store's own trace events contain no file system event (`FsCtx`'s `Q`). -/
def SessionStoreSpec.Quiet {A : RustAlloc} {b : BitVec 64} (kit : SessionStoreSpec A b) : Prop :=
  (∀ encRecord rem ans, NoFsEv (kit.loadEvs encRecord rem ans)) ∧
    (∀ encRecord rem r ans, NoFsEv (kit.storeEvs encRecord rem r ans))

/-- Read-only `.rodata` vtable slots required by `kit : SessionStoreSpec A img.base` under
    `img.FrozenLoaded`. -/
structure KitVtablesOk {A : RustAlloc} (img : Obj.Image) (kit : SessionStoreSpec A img.base) : Prop where
  loadSlot : ∀ {s : State} {P : SepProp}, img.FrozenLoaded s → (s.mem ⊨ P) →
    s.mem ⊨ ((kit.ss_vt + 0x18#64) ↦₆₄ᵣ (img.base + kit.loadShimOff)) ∗ P
  storeSlot : ∀ {s : State} {P : SepProp}, img.FrozenLoaded s → (s.mem ⊨ P) →
    s.mem ⊨ ((kit.ss_vt + 0x20#64) ↦₆₄ᵣ (img.base + kit.storeShimOff)) ∗ P
  saveSlot : ∀ {s : State} {P : SepProp}, img.FrozenLoaded s → (s.mem ⊨ P) →
    s.mem ⊨ ((kit.id_vt + 0x28#64) ↦₆₄ᵣ (img.base + bv% (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#3]" + 88))) ∗ P
  trustSlot : ∀ {s : State} {P : SepProp}, img.FrozenLoaded s → (s.mem ⊨ P) →
    s.mem ⊨ ((kit.id_vt + 0x30#64) ↦₆₄ᵣ (img.base + bv% (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#3]" + 184))) ∗ P
  loadFutDrop : ∀ {s : State} {P : SepProp}, img.FrozenLoaded s → (s.mem ⊨ P) →
    s.mem ⊨ ((img.base + kit.loadFutVtOff) ↦₆₄ᵣ (img.base + kit.loadFutDropOff)) ∗ P
  loadFutSize : ∀ {s : State} {P : SepProp}, img.FrozenLoaded s → (s.mem ⊨ P) →
    s.mem ⊨ ((img.base + kit.loadFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.loadBoxSize) ∗ P
  loadFutAlign : ∀ {s : State} {P : SepProp}, img.FrozenLoaded s → (s.mem ⊨ P) →
    s.mem ⊨ ((img.base + kit.loadFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗ P
  loadFutPoll : ∀ {s : State} {P : SepProp}, img.FrozenLoaded s → (s.mem ⊨ P) →
    s.mem ⊨ ((img.base + kit.loadFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + kit.loadPollOff)) ∗ P
  storeFutDrop : ∀ {s : State} {P : SepProp}, img.FrozenLoaded s → (s.mem ⊨ P) →
    s.mem ⊨ ((img.base + kit.storeFutVtOff) ↦₆₄ᵣ (img.base + kit.storeFutDropOff)) ∗ P
  storeFutSize : ∀ {s : State} {P : SepProp}, img.FrozenLoaded s → (s.mem ⊨ P) →
    s.mem ⊨ ((img.base + kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗ P
  storeFutAlign : ∀ {s : State} {P : SepProp}, img.FrozenLoaded s → (s.mem ⊨ P) →
    s.mem ⊨ ((img.base + kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗ P
  storeFutPoll : ∀ {s : State} {P : SepProp}, img.FrozenLoaded s → (s.mem ⊨ P) →
    s.mem ⊨ ((img.base + kit.storeFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + kit.storePollOff)) ∗ P

/-- Full `SessionStoreKitOkS` bundle for a `SessionStoreSpec` at scope `Scope`. -/
structure SessionStoreKitOkS {A : RustAlloc} {img : Obj.Image} (kit : SessionStoreSpec A img.base)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (C : Crypto) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop where
  loadShim : subroutine_ok (tripleRatchetProgAt img.base C ctl abs) (img.base + kit.loadShimOff)
    ((kitLoadShimSpec kit).inImage img)
  loadPoll : subroutine_ok (tripleRatchetProgAt img.base C ctl abs) (img.base + kit.loadPollOff)
    (kitLoadPollSpecSE img kit Scope encRecord)
  loadFutDrop : subroutine_ok (tripleRatchetProgAt img.base C ctl abs) (img.base + kit.loadFutDropOff)
    futDropSpec
  storeShim : subroutine_ok (tripleRatchetProgAt img.base C ctl abs) (img.base + kit.storeShimOff)
    ((kitStoreShimSpec kit).inImage img)
  storePoll : subroutine_ok (tripleRatchetProgAt img.base C ctl abs) (img.base + kit.storePollOff)
    ((kitStorePollSpecE kit encRecord).inImage img)
  storeFutDrop : subroutine_ok (tripleRatchetProgAt img.base C ctl abs) (img.base + kit.storeFutDropOff)
    futDropSpec
  trustShim : subroutine_ok (tripleRatchetProgAt img.base C ctl abs) (img.base + bv% (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#3]" + 184))
    (isTrustedShimSpec A img.base)
  trustPoll : subroutine_ok (tripleRatchetProgAt img.base C ctl abs) (img.base + bv% (ls_off% "<[u8] as subtle::ConstantTimeEq>::ct_eq" + 16328))
    (isTrustedPollSpec A img.base)
  saveShim : subroutine_ok (tripleRatchetProgAt img.base C ctl abs) (img.base + bv% (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#3]" + 88))
    (saveIdentityShimSpec A img.base)
  savePoll : subroutine_ok (tripleRatchetProgAt img.base C ctl abs) (img.base + bv% (ls_off% "<[u8] as subtle::ConstantTimeEq>::ct_eq" + 16192))
    (saveIdentityPollSpec A img.base)
  idFutDrop : subroutine_ok (tripleRatchetProgAt img.base C ctl abs) (img.base + bv% (ls_off% "<[u8] as subtle::ConstantTimeEq>::ct_eq" + 15744)) futDropSpec

abbrev SessionStoreKitOk {A : RustAlloc} {img : Obj.Image} (kit : SessionStoreSpec A img.base)
    (C : Crypto) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  SessionStoreKitOkS kit RecordInScope C encRecord ctl abs

end CryptoVerification.LibsignalPublicApi.StoreKit
