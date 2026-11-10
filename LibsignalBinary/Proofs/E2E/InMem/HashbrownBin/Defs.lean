/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.InMem.HashbrownModel.FindInsert
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
public import LibsignalBinary.Proofs.E2E.InMem.SipHashModel.Model
public import LibsignalBinary.Proofs.E2E.Record.Serialization.Defs
public import LibsignalBinary.Specifications.AsmConstants
import GeneratedLean.LibsignalSessionCode -- shake: keep


/-!
# Representation Predicates and Key-Independence for Compiled `hashbrown` Tables

Defines 4-bucket `RawTable` separation-logic predicates (`emptyTableAt`, `table4At`, `table4EmptyAt`,
`table4SingleAt`) for `InMemSessionStore` (400-byte stride) and `InMemIdentityKeyStore` (64-byte
stride), and proves that lookup outcomes on `≤ 1`-item tables are independent of the SipHash keys
`(k0, k1)`.
-/

@[expose] public section

namespace CryptoVerification.E2E.InMem.HashbrownBin

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.Serialization
open CryptoVerification.E2E.InMem.HashbrownModel
open CryptoVerification.E2E.InMem.SipHashModel


abbrev HookMap : Type := String → Option (Arm64.State → Arm64.State)

/-- `libsignalSessionCode` rebased at `b` with extern table `ext`. -/
noncomputable abbrev RebasedProg (b : BitVec 64) (ext : HookMap) : Program :=
  libsignalSessionCode.rebase b ext

/-! ## Symbol Names and Table Layout Constants -/

/-- Out-of-line `<hashbrown::raw::RawTableInner>::fallible_with_capacity::<alloc::alloc::Global>`
(`0x01798 = 6040`, 412 bytes, 103 instructions). -/
abbrev fallibleWithCapacityName : String :=
  "<hashbrown::raw::RawTableInner>::fallible_with_capacity::<alloc::alloc::Global>"

/-- Out-of-line `<RawTable<(ProtocolAddress, IdentityKey)>>::reserve_rehash`
(`0x0081c = 2076`, 552 bytes, 138 instructions). -/
abbrev reserveRehashIdName : String :=
  "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey, std::hash::random::RandomState>::{closure#0}>"

/-- Out-of-line `<RawTable<(ProtocolAddress, SessionRecord)>>::reserve_rehash`
(`0x00a44 = 2628`, 564 bytes, 141 instructions). -/
abbrev reserveRehashSessionName : String :=
  "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord, std::hash::random::RandomState>::{closure#0}>"

/-- Out-of-line `<hashbrown::raw::RawTableInner>::rehash_in_place`
(`0x1f0b0 = 127152`, 516 bytes, 129 instructions; unreachable on `≤ 1`-item E2E paths). -/
abbrev rehashInPlaceName : String :=
  "<hashbrown::raw::RawTableInner>::rehash_in_place"

/-- Out-of-line `<std::collections::hash::map::HashMap<ProtocolAddress, IdentityKey>>::insert`
(`0x14ee0 = 85728`, 592 bytes, 148 instructions). -/
abbrev hashMapIdInsertName : String :=
  "<std::collections::hash::map::HashMap<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey>>::insert"

/-- `<InMemIdentityKeyStore as IdentityKeyStore>::get_identity::{closure#0}`
(`0x07658 = 30296`, 372 bytes, 93 instructions). -/
abbrev getIdentityClosureName : String :=
  "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}"

/-- `<InMemIdentityKeyStore as IdentityKeyStore>::save_identity::{closure#0}`
(`0x077cc = 30668`, 504 bytes, 126 instructions). -/
abbrev saveIdentityClosureName : String :=
  "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"

/-- `<InMemIdentityKeyStore as IdentityKeyStore>::is_trusted_identity::{closure#0}`
(`0x079c4 = 31172`, 368 bytes, 92 instructions). -/
abbrev isTrustedIdentityClosureName : String :=
  "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity::{closure#0}"

/-- `<InMemSessionStore as SessionStore>::load_session::{closure#0}`
(`0x08ce4 = 36068`, 512 bytes, 128 instructions). -/
abbrev loadSessionClosureName : String :=
  "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}"

/-- `<InMemSessionStore as SessionStore>::store_session::{closure#0}`
(`0x08ee4 = 36580`, 912 bytes, 228 instructions). -/
abbrev storeSessionClosureName : String :=
  "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}"

theorem fallibleWithCapacity_fnOff :
    libsignalSessionCode.fnOff fallibleWithCapacityName = num% (ls_off% "<hashbrown::raw::RawTableInner>::fallible_with_capacity::<alloc::alloc::Global>") :=
  (ls_lemma% fnOff "<hashbrown::raw::RawTableInner>::fallible_with_capacity::<alloc::alloc::Global>")

theorem reserveRehashId_fnOff :
    libsignalSessionCode.fnOff reserveRehashIdName = num% (ls_off% "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey, std::hash::random::RandomState>::{closure#0}>") :=
  (ls_lemma% fnOff "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey, std::hash::random::RandomState>::{closure#0}>")

theorem reserveRehashSession_fnOff :
    libsignalSessionCode.fnOff reserveRehashSessionName = num% (ls_off% "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord, std::hash::random::RandomState>::{closure#0}>") :=
  (ls_lemma% fnOff "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord, std::hash::random::RandomState>::{closure#0}>")

theorem rehashInPlace_fnOff :
    libsignalSessionCode.fnOff rehashInPlaceName = num% (ls_off% "<hashbrown::raw::RawTableInner>::rehash_in_place") :=
  (ls_lemma% fnOff "<hashbrown::raw::RawTableInner>::rehash_in_place")

theorem hashMapIdInsert_fnOff :
    libsignalSessionCode.fnOff hashMapIdInsertName = num% (ls_off% "<std::collections::hash::map::HashMap<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey>>::insert") :=
  (ls_lemma% fnOff "<std::collections::hash::map::HashMap<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey>>::insert")

theorem getIdentityClosure_fnOff :
    libsignalSessionCode.fnOff getIdentityClosureName = num% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}") :=
  (ls_lemma% fnOff "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}")

theorem saveIdentityClosure_fnOff :
    libsignalSessionCode.fnOff saveIdentityClosureName = num% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}") :=
  (ls_lemma% fnOff "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}")

theorem isTrustedIdentityClosure_fnOff :
    libsignalSessionCode.fnOff isTrustedIdentityClosureName = num% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity::{closure#0}") :=
  (ls_lemma% fnOff "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity::{closure#0}")

theorem loadSessionClosure_fnOff :
    libsignalSessionCode.fnOff loadSessionClosureName = num% (ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}") :=
  (ls_lemma% fnOff "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}")

theorem storeSessionClosure_fnOff :
    libsignalSessionCode.fnOff storeSessionClosureName = num% (ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}") :=
  (ls_lemma% fnOff "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}")

/-- `size_of::<(ProtocolAddress, SessionRecord)>() = 0x190` (400 bytes). -/
abbrev sessionBucketStride : Nat := AsmConstants.sessionBucketStride

/-- `offset_of!((ProtocolAddress, SessionRecord), 1) = 0x20` (32 bytes). -/
abbrev sessionBucketValueOff : Nat := AsmConstants.sessionBucketValueOff

/-- `size_of::<(ProtocolAddress, IdentityKey)>() = 0x40` (64 bytes). -/
abbrev identityBucketStride : Nat := AsmConstants.identityBucketStride

/-- `offset_of!((ProtocolAddress, IdentityKey), 1) = 0x20` (32 bytes). -/
abbrev identityBucketValueOff : Nat := AsmConstants.identityBucketValueOff

/-- Static empty control group offset in `.rodata` (`0x4a5f0` in the E2E image: 8 bytes of `0xff`,
    `Group::WIDTH = 8` on ARM64 NEON, pointed to by the relocated word 0 of the `0x4a658`
    `.data.rel.ro` `RawTableInner::NEW` template). -/
abbrev emptyCtrlGroupOff : Nat := num% (ls_bytes% "ffffffffffffffff67726f75705f6964")

set_option maxRecDepth 2000000 in
open ProofLib.ProgramReflection in
/-- The 8 `.rodata` bytes at `emptyCtrlGroupOff` (`0x4a5f0`) equal `0xff` (`emptyTag`). -/
theorem rodata_emptyCtrlGroup_eq :
    (libsignalSessionImage.data.drop (num% (ls_bytes% "ffffffffffffffff67726f75705f6964") - libsignalSessionImage.dataOff)).take 8 =
      List.replicate 8 0xff#8 := by
  rfl_kernel

/-- Address of bucket `i` growing downward from `ctrl`: `ctrl - (i + 1) * stride`. -/
def bucketAddr (ctrl : BitVec 64) (stride i : Nat) : BitVec 64 :=
  ctrl - BitVec.ofNat 64 ((i + 1) * stride)

/-- Base address of the heap allocation for an `n`-bucket table (`n = mask.toNat + 1`):
`ctrl - n * stride`. -/
def tableAllocBase (ctrl : BitVec 64) (numBuckets stride : Nat) : BitVec 64 :=
  ctrl - BitVec.ofNat 64 (numBuckets * stride)

/-- Total byte size of the heap allocation for an `n`-bucket table (`n * stride + n + 8`). -/
def tableAllocSize (numBuckets stride : Nat) : Nat :=
  numBuckets * stride + numBuckets + asm% hashbrownGroupWidth


/-! ## Representation Predicates (`emptyTableAt`, `table4At`) -/

/-- Unallocated empty `HashMap<K, V, RandomState>` at `mp`: `ctrl` points to the static 8-byte
`0xff` group at `base + emptyCtrlGroupOff`, `bucket_mask = growth_left = items = 0`, and
`RandomState { k0, k1 }` sits at `mp + 32..48`. -/
def emptyTableAt (base mp k0 k1 : BitVec 64) : SepProp :=
  (mp ↦₆₄ (base + BitVec.ofNat 64 emptyCtrlGroupOff)) ∗
  ((mp + asm64% tableMaskOff) ↦₆₄ 0#64) ∗
  ((mp + asm64% tableGrowthLeftOff) ↦₆₄ 0#64) ∗
  ((mp + asm64% tableItemsOff) ↦₆₄ 0#64) ∗
  ((mp + asm64% tableHasherOff) ↦₆₄ k0) ∗
  ((mp + asm64% tableHasherOff + 8#64) ↦₆₄ k1)

/-- Allocated 4-bucket `HashMap<K, V, RandomState>` at `mp` with SipHash keys `(k0, k1)`, 12-byte
control array `cbs`, `growth_left = growth`, and active bucket indices `full`; buckets grow downward
from `ctrl` at `bucketAddr ctrl stride i = ctrl - (i + 1) * stride`. -/
def table4At (A : RustAlloc) (stride : Nat) (mp k0 k1 growth : BitVec 64)
    (cbs : List (BitVec 8)) (full : List Nat) (entry : Nat → BitVec 64 → SepProp) : SepProp :=
  ∃∗ ctrl : BitVec 64,
    ⌜ctrl ≠ 0#64 ∧ ctrl.toNat % 8 = 0 ∧
      4 * stride ≤ ctrl.toNat ∧ ctrl.toNat + 12 < 2 ^ 64 ∧
      (full.length = 4 → growth = 0#64) ∧
      CtrlMirrorInv 3#64 cbs ∧ FullBucketsInv 3#64 cbs full⌝ ∗
    (mp ↦₆₄ ctrl) ∗
    ((mp + asm64% tableMaskOff) ↦₆₄ 3#64) ∗
    ((mp + asm64% tableGrowthLeftOff) ↦₆₄ growth) ∗
    ((mp + asm64% tableItemsOff) ↦₆₄ BitVec.ofNat 64 full.length) ∗
    ((mp + asm64% tableHasherOff) ↦₆₄ k0) ∗
    ((mp + asm64% tableHasherOff + 8#64) ↦₆₄ k1) ∗
    A.live (ctrl - BitVec.ofNat 64 (4 * stride)) (tableAllocSize 4 stride) (asm% hashbrownTableAlign) ∗
    (ctrl ↦ₛ cbs) ∗
    arrayAt
      (fun i a => if i ∈ full then entry i a else memRegion a stride) stride
      (ctrl - BitVec.ofNat 64 (4 * stride)) (List.range 4).reverse

/-- Specialization of `table4At` for an allocated but empty 4-bucket table (`cbs = emptyCtrl4`,
`full = []`, `growth = 3#64`), as produced right after `reserve_rehash` on an empty table. -/
def table4EmptyAt (A : RustAlloc) (stride : Nat) (mp k0 k1 : BitVec 64) : SepProp :=
  table4At A stride mp k0 k1 3#64 emptyCtrl4 [] (fun _ a => memRegion a stride)

/-- Specialization of `table4At` for a 4-bucket table holding a single entry at bucket
`k < 4` (`cbs = singleCtrl4 k (h2Tag (hashAddrBv k0 k1 peerName peerDev))`, `full = [k]`,
`growth = 2#64`). -/
def table4SingleAt (A : RustAlloc) (stride : Nat) (mp k0 k1 : BitVec 64)
    (k : Nat) (peerName : List (BitVec 8)) (peerDev : BitVec 8)
    (entryAt : BitVec 64 → SepProp) : SepProp :=
  ⌜k < 4⌝ ∗
  table4At A stride mp k0 k1 2#64
    (singleCtrl4 k (h2Tag (hashAddrBv k0 k1 peerName peerDev))) [k]
    (fun _ a => entryAt a)

/-- Bucket entry predicate for `RawTable<(ProtocolAddress, SessionRecord)>`:
at bucket address `a`, `+0..+32` is `protocolAddressAt A g a` and `+32..+400` is
`sessionRecordAt A (a + 0x20) ⟨0#64, 8#64, some G⟩ ⟨some ss⟩` (empty `previous_sessions`
`Vec<Vec<u8>>` at `+0x20` and `sessionStateReprAt A (a + 0x38) G ss`) with `CanonSession G ss`. -/
def sessionBucketEntryAt (A : RustAlloc) (g : AddrGhost)
    (G : SessionGhost) (ss : Session (List (BitVec 8))) (a : BitVec 64) : SepProp :=
  ⌜CanonSession G ss⌝ ∗
    protocolAddressAt A g a ∗
    sessionRecordAt A (a + asm64% sessionBucketValueOff) ⟨0#64, 8#64, some G⟩ ⟨some ss⟩


/-- Bucket entry predicate for `RawTable<(ProtocolAddress, IdentityKey)>`:
at bucket address `a`, `+0..+32` is `protocolAddressAt A g a` and `+32..+64` is the 32-byte
compressed public key `keyBytes` (`keyBytes.length = 32`). -/
def identityBucketEntryAt (A : RustAlloc) (g : AddrGhost) (keyBytes : List (BitVec 8))
    (a : BitVec 64) : SepProp :=
  ⌜keyBytes.length = 32⌝ ∗
  protocolAddressAt A g a ∗ ((a + asm64% identityBucketValueOff) ↦ₛ keyBytes)

/-! ## SipHash `h2Bv` and `hashbrown` `h2Tag` Equivalence -/

/-- The SipHash model's `h2Bv hash` is identical to the `hashbrown` model's `h2Tag hash` (`(hash >>> 57).truncate 8`). -/
theorem h2Bv_eq_h2Tag (hash : BitVec 64) : h2Bv hash = h2Tag hash := by
  apply BitVec.eq_of_toNat_eq
  have hlhs : (h2Bv hash).toNat = ((hash.toNat >>> 57) % 256) &&& 127 := by
    change (((UInt64.ofBitVec hash) >>> 57).toUInt8 &&& 0x7f).toNat = _
    rw [UInt8.toNat_and, UInt64.toNat_toUInt8, UInt64.toNat_shiftRight]
    rfl
  rw [hlhs]
  unfold h2Tag
  simp

attribute [simp] h2Bv_eq_h2Tag



/-! ## SipHash Key-Independence on `≤ 1`-Item Tables -/

/-- `find4` on `emptyCtrl4` returns `none` for every SipHash key pair `(k0, k1)`. -/
theorem find4_empty_key_independent (k0 k1 : BitVec 64)
    (qName : List (BitVec 8)) (qDev : BitVec 8) (eqAt : Nat → Bool) :
    find4 emptyCtrl4 (hashAddrBv k0 k1 qName qDev) eqAt = none :=
  find4_emptyCtrl4 (hashAddrBv k0 k1 qName qDev) eqAt

/-- On a 4-bucket table with a single full bucket `k < 4` tagged with
`h2Tag (hashAddrBv k0 k1 peerName peerDev)` and exact key callback `eqAt`, `find4` returns `some k`
iff `(qName, qDev) = (peerName, peerDev)`, independent of `(k0, k1)`. -/
theorem find4_single_key_independent
    (k0 k1 : BitVec 64)
    (k : Nat) (hk : k < 4)
    (peerName qName : List (BitVec 8)) (peerDev qDev : BitVec 8)
    (eqAt : Nat → Bool)
    (heqAt : eqAt k = decide (qName = peerName ∧ qDev = peerDev)) :
    let peerHash := hashAddrBv k0 k1 peerName peerDev
    let qHash := hashAddrBv k0 k1 qName qDev
    find4 (singleCtrl4 k (h2Tag peerHash)) qHash eqAt =
      if qName = peerName ∧ qDev = peerDev then some k else none := by
  dsimp only
  rw [find4_singleCtrl4 k hk (h2Tag (hashAddrBv k0 k1 peerName peerDev))
        (hashAddrBv k0 k1 qName qDev) eqAt, heqAt]
  by_cases hmatch : qName = peerName ∧ qDev = peerDev
  · rcases hmatch with ⟨rfl, rfl⟩
    simp
  · simp [hmatch]

/-- Mapping `find4` on a 1-item 4-bucket table to the value at bucket `k` yields
`if qName = peerName ∧ qDev = peerDev then some val else none`, independent of `(k0, k1)`. -/
theorem find4_single_value_key_independent {V : Type}
    (k0 k1 : BitVec 64)
    (k : Nat) (hk : k < 4)
    (peerName qName : List (BitVec 8)) (peerDev qDev : BitVec 8)
    (val : V) (getBucketVal : Nat → V) (hval : getBucketVal k = val)
    (eqAt : Nat → Bool)
    (heqAt : eqAt k = decide (qName = peerName ∧ qDev = peerDev)) :
    ((find4 (singleCtrl4 k (h2Tag (hashAddrBv k0 k1 peerName peerDev)))
        (hashAddrBv k0 k1 qName qDev) eqAt).map getBucketVal) =
      if qName = peerName ∧ qDev = peerDev then some val else none := by
  rw [find4_single_key_independent k0 k1 k hk peerName qName peerDev qDev eqAt heqAt]
  split <;> simp [hval]

/-! ## External Hook Specifications -/


abbrev bcmpName : String := "bcmp"

abbrev randomKeysName : String := "std::sys::random::linux::hashmap_random_keys"

export CryptoVerification.LibsignalTripleRatchet (extHookStack)

/-- Ghost state for a `bcmp(a = x0, b = x1, n = x2)` call on two byte slices of equal length `n`. -/
structure BcmpCall where
  a : BitVec 64
  b : BitVec 64
  bsA : List (BitVec 8)
  bsB : List (BitVec 8)

abbrev _root_.Arm64.State.vec (s : Arm64.State) : VRegFile := s.vregs

/-- `bcmp(a = x0, b = x1, n = x2) -> w0`: compares `n` bytes at `a` and `b` without modifying them,
returning `w0 = 0` iff `bsA = bsB`. -/
def e2eBcmpSpec : Spec BcmpCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a ∧ s.readReg64 .x1 = x.b ∧
      (s.readReg64 .x2).toNat = x.bsA.length ∧ x.bsB.length = x.bsA.length⌝ ∗
      (x.a ↦ₛ x.bsA) ∗ (x.b ↦ₛ x.bsB) ∗ stackAt s.sp extHookStack
  post := fun x s0 sf =>
    ⌜((sf.readReg64 .x0).setWidth 32 = 0#32 ↔ x.bsA = x.bsB) ∧
      sf.vregs = s0.vregs ∧ sf.trace = s0.trace⌝ ∗
      (x.a ↦ₛ x.bsA) ∗ (x.b ↦ₛ x.bsB) ∗ stackAt s0.sp extHookStack

/-- `RandomState::new` key-generation hook (`x0, x1` returned as two `u64` SipHash keys;
    no constraint on `x0`/`x1` in the postcondition so any deterministic hook satisfies `HookOk`). -/
def randomKeysSpec : Spec Unit where
  pre := fun _ s => stackAt s.sp extHookStack
  post := fun _ s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ stackAt s0.sp extHookStack

/-- `__rust_alloc(size = x0, align = x1)` with non-wrapping upper bound
`(sf.readReg64 .x0).toNat + size < 2 ^ 64` on non-null return. -/
def rustAllocNWSpec (A : RustAlloc) : Spec (Nat × Nat) where
  pre := (rustAllocSpec A).pre
  post := fun (size, align) s0 sf =>
    A.pool ∗ stackAt s0.sp allocHookStack ∗
      (if sf.readReg64 .x0 = 0 then ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝
       else ⌜(sf.readReg64 .x0).toNat % align = 0 ∧
         (sf.readReg64 .x0).toNat + size < 2 ^ 64 ∧ sf.trace = s0.trace⌝ ∗
         A.live (sf.readReg64 .x0) size align ∗ memRegion (sf.readReg64 .x0) size)
  onPanic := (rustAllocSpec A).onPanic

theorem hookOk_rustAllocSpec_of_NW {A : RustAlloc} {f : Arm64.State → Arm64.State}
    (h : HookOk f (rustAllocNWSpec A)) :
    HookOk f (rustAllocSpec A) := by
  intro (size, align) R s0 hrun hpre hsp
  obtain ⟨hkf, hsp_eq, Out⟩ := h (size, align) R s0 hrun hpre hsp
  refine ⟨hkf, hsp_eq, ?_⟩
  rcases Out with ⟨hret, hregs, hpost⟩ | hpan
  · refine Or.inl ⟨hret, hregs, ?_⟩
    refine Satisfies.mono (sepConj_mono_left ?_) hpost
    dsimp only [rustAllocNWSpec, rustAllocSpec]
    refine sepConj_mono_right (sepConj_mono_right ?_)
    split
    · exact Entails.refl _
    · exact Entails.pure_left fun ⟨hal, _, htr⟩ => Entails.pure_right ⟨hal, htr⟩ (Entails.refl _)
  · exact Or.inr hpan

theorem hookSat_rustAllocSpec_of_NW {A : RustAlloc} {ext : HookMap} {name : String}
    (h : HookSat ext name (rustAllocNWSpec A)) :
    HookSat ext name (rustAllocSpec A) := by
  rcases h with ⟨f, hf, hok⟩
  exact ⟨f, hf, hookOk_rustAllocSpec_of_NW hok⟩

abbrev stringCloneHookName : String := "<alloc::string::String as core::clone::Clone>::clone"

abbrev stringCloneName : String := stringCloneHookName

/-- `<String as Clone>::clone(&self) -> String` (`x0` = `&self`, sret `x8`, 24 bytes):
produces a fresh `String` with the same bytes (`vecU8 A ret g.bytes`), keeping `self` (`vecGhostAt A g p`)
unchanged, or panics on allocation failure. -/
def stringCloneSpec (A : RustAlloc) : Spec (BitVec 64 × BitVec 64 × VecGhost) where
  pre := fun (p, ret, g) s =>
    ⌜s.readReg64 .x0 = p ∧ s.readReg64 .x8 = ret⌝ ∗ vecGhostAt A g p ∗ memRegion ret 24 ∗
      A.pool ∗ stackAt s.sp extHookStack
  post := fun (p, ret, g) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ vecGhostAt A g p ∗ vecU8 A ret g.bytes ∗ A.pool ∗
      stackAt s0.sp extHookStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

abbrev fallibilityAllocErrName : String := "<hashbrown::raw::Fallibility>::alloc_err#1"

/-- External hook bundle for `HashbrownBin` proofs, combining allocator, `bcmp`, `randomKeys`,
`stringClone`, memory/panic stubs, and `tripleRatchetProgAt` compatibility. -/
structure HashbrownBinHooks (A : RustAlloc) (ext : String → Option (Arm64.State → Arm64.State)) : Prop where
  alloc : AllocHooks A ext
  allocNW : HookSat ext "__rustc::__rust_alloc" (rustAllocNWSpec A)
  bcmp : HookSat ext bcmpName e2eBcmpSpec
  randomKeys : HookSat ext randomKeysName randomKeysSpec
  stringClone : HookSat ext stringCloneHookName (stringCloneSpec A)
  shim : ext "__rustc::__rust_no_alloc_shim_is_unstable_v2" = some hookNoop
  memset : ext "memset" = some hookMemset
  memcpy : ext "memcpy" = some hookMemcpy
  blackBox : ext "subtle::black_box::<u8>" = some CryptoVerification.LibsignalSession.blackBoxHook
  fallibilityAllocErr : ext fallibilityAllocErrName = some Rust.panicked
  rawVecHandleError : ext "alloc::raw_vec::handle_error" = some Rust.panicked
  panicAsyncFnResumed : ext "core::panicking::panic_const::panic_const_async_fn_resumed" = some Rust.panicked
  istripleRatchetProgAt : ∃ C ctl abs,
    ext = Rust.withPanics (tripleRatchetExterns C ctl abs) ∧ AllocHooks A abs

theorem HashbrownBinHooks.alloc_sat {A : RustAlloc} {ext : HookMap} (h : HashbrownBinHooks A ext) :
    HookSat ext "__rustc::__rust_alloc" (rustAllocSpec A) :=
  hookSat_rustAllocSpec_of_NW h.allocNW

private theorem hookSat_withPanics_tripleRatchetExterns {α : Type}
    (C : Crypto) (ctl : BitVec 64) (abs : HookMap)
    {sym : String} {spec : Spec α}
    (heq : Rust.withPanics (tripleRatchetExterns C ctl abs) sym = abs sym)
    (h : HookSat abs sym spec) :
    HookSat (Rust.withPanics (tripleRatchetExterns C ctl abs)) sym spec := by
  unfold HookSat at *; rwa [heq]

private theorem withPanics_of_isPanicSymbol (hooks : HookMap) (sym : String)
    (h : Rust.isPanicSymbol sym = true) :
    Rust.withPanics hooks sym = some Rust.panicked := by
  simp [Rust.withPanics, h]

private theorem withPanics_tripleRatchetExterns_fallibilityAllocErr
    (C : Crypto) (ctl : BitVec 64) (abs : HookMap) :
    Rust.withPanics (tripleRatchetExterns C ctl abs) fallibilityAllocErrName =
      abs fallibilityAllocErrName := by
  have hnp : Rust.isPanicSymbol fallibilityAllocErrName = false := by decide +kernel
  simp [Rust.withPanics, hnp]
  rfl

/-- Constructs `HashbrownBinHooks A` for `Rust.withPanics (tripleRatchetExterns C ctl abs)`. -/
theorem hashbrownBinHooks_of_tripleRatchetProgAt (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : HookMap)
    (hAlloc : AllocHooks A abs)
    (hAllocNW : HookSat abs "__rustc::__rust_alloc" (rustAllocNWSpec A))
    (hAllocErr : abs fallibilityAllocErrName = some Rust.panicked)
    (hStringClone : HookSat abs stringCloneHookName (stringCloneSpec A))
    (hBcmp : HookSat abs bcmpName e2eBcmpSpec)
    (hRandomKeys : HookSat abs randomKeysName randomKeysSpec) :
    HashbrownBinHooks A (Rust.withPanics (tripleRatchetExterns C ctl abs)) where
  alloc :=
    { alloc := hookSat_withPanics_tripleRatchetExterns C ctl abs
        (by have h : Rust.isPanicSymbol "__rustc::__rust_alloc" = false := by decide +kernel
            simp [Rust.withPanics, h]; rfl) hAlloc.alloc
      dealloc := hookSat_withPanics_tripleRatchetExterns C ctl abs
        (by have h : Rust.isPanicSymbol "__rustc::__rust_dealloc" = false := by decide +kernel
            simp [Rust.withPanics, h]; rfl) hAlloc.dealloc
      realloc := hookSat_withPanics_tripleRatchetExterns C ctl abs
        (by have h : Rust.isPanicSymbol "__rustc::__rust_realloc" = false := by decide +kernel
            simp [Rust.withPanics, h]; rfl) hAlloc.realloc }
  allocNW := hookSat_withPanics_tripleRatchetExterns C ctl abs
    (by have h : Rust.isPanicSymbol "__rustc::__rust_alloc" = false := by decide +kernel
        simp [Rust.withPanics, h]; rfl) hAllocNW
  bcmp := hookSat_withPanics_tripleRatchetExterns C ctl abs
    (by have h : Rust.isPanicSymbol bcmpName = false := by decide +kernel
        simp [Rust.withPanics, h]; rfl) hBcmp
  randomKeys := hookSat_withPanics_tripleRatchetExterns C ctl abs
    (by have h : Rust.isPanicSymbol randomKeysName = false := by decide +kernel
        simp [Rust.withPanics, h]; rfl) hRandomKeys
  stringClone := hookSat_withPanics_tripleRatchetExterns C ctl abs
    (by have h : Rust.isPanicSymbol stringCloneHookName = false := by decide +kernel
        simp [Rust.withPanics, h]; rfl) hStringClone
  shim := by
    have h : Rust.isPanicSymbol "__rustc::__rust_no_alloc_shim_is_unstable_v2" = false := by decide +kernel
    simp [Rust.withPanics, h]; rfl
  memset := by
    have h : Rust.isPanicSymbol "memset" = false := by decide +kernel
    simp [Rust.withPanics, h]; rfl
  memcpy := by
    have h : Rust.isPanicSymbol "memcpy" = false := by decide +kernel
    simp [Rust.withPanics, h]; rfl
  blackBox := by
    have h : Rust.isPanicSymbol "subtle::black_box::<u8>" = false := by decide +kernel
    simp [Rust.withPanics, h]; rfl
  fallibilityAllocErr := by
    rw [withPanics_tripleRatchetExterns_fallibilityAllocErr]
    exact hAllocErr
  rawVecHandleError := withPanics_of_isPanicSymbol _ _ (by decide +kernel)
  panicAsyncFnResumed := withPanics_of_isPanicSymbol _ _ (by decide +kernel)
  istripleRatchetProgAt := ⟨C, ctl, abs, rfl, hAlloc⟩

end CryptoVerification.E2E.InMem.HashbrownBin





