/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.Defs

/-!
# Specifications for Compiled `hashbrown` Operations on `InMem` Tables

Machine-level specifications for `fallible_with_capacity` (`0x01798`), `reserve_rehash` (`0x0081c`,
`0x00a44`), `HashMap<ProtocolAddress, IdentityKey>::insert` (`0x14ee0`), and the five
`InMemIdentityKeyStore` and `InMemSessionStore` future closures (`0x07658`, `0x079c4`, `0x077cc`,
`0x08ce4`, `0x08ee4`). Lookup and state-transition outcomes on `≤ 1`-item tables are independent of
the SipHash keys `(k0, k1)`.
-/

@[expose] public section

namespace CryptoVerification.E2E.InMem.HashbrownBin

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.Serialization
open CryptoVerification.E2E.InMem.HashbrownModel
open CryptoVerification.E2E.InMem.SipHashModel


/-! ## Stack Budgets -/

/-- `fallible_with_capacity` (`0x01798`, prologue `0x40` bytes) + `allocHookStack` (`4096`). -/
abbrev fallibleWithCapacityStack : Nat := allocHookStack + 128

/-- `reserve_rehash` (`0x0081c` / `0x00a44`, prologue `0xb0 = 176` bytes) + `fallibleWithCapacityStack` (`allocHookStack + 128`). -/
abbrev reserveRehashStack : Nat := allocHookStack + 320

/-- `HashMap<ProtocolAddress, IdentityKey>::insert` (`0x14ee0`, prologue `0xe0 = 224` bytes) + `extHookStack` (`2 ^ 14`). -/
abbrev hashMapIdInsertStack : Nat := extHookStack + 544

/-- `InMemIdentityKeyStore::get_identity::{closure#0}` (`0x07658`, prologue `0xa0 = 160` bytes) + `extHookStack`. -/
abbrev getIdentityClosureStack : Nat := extHookStack + 256

/-- `InMemIdentityKeyStore::save_identity::{closure#0}` (`0x077cc`, prologue `0xf0 = 240` bytes) + `hashMapIdInsertStack`. -/
abbrev saveIdentityClosureStack : Nat := extHookStack + 800

/-- `InMemIdentityKeyStore::is_trusted_identity::{closure#0}` (`0x079c4`, prologue `0x80 = 128` bytes) + `extHookStack`. -/
abbrev isTrustedIdentityClosureStack : Nat := extHookStack + 256

/-- `InMemSessionStore::load_session::{closure#0}` (`0x08ce4`, prologue `0x440 = 1088` bytes) + `extHookStack` (`extHookStack + 3072 = 19456` B). -/
abbrev loadSessionClosureStack : Nat := extHookStack + 3072

/-- `InMemSessionStore::store_session::{closure#0}` (`0x08ee4`, prologue `0x4b0 = 1200` bytes) + `extHookStack` (`extHookStack + 3072 = 19456` B). -/
abbrev storeSessionClosureStack : Nat := extHookStack + 3072


/-! ## `<RawTableInner>::fallible_with_capacity::<Global>` (`0x01798`) -/

/-- Freshly allocated 4-bucket `RawTableInner` at `sret` (32 bytes): `(ctrl, 3, 3, 0)` at
`sret + 0x00..0x20`, `4 * stride + 12` live heap bytes at `ctrl - 4 * stride`, `emptyCtrl4` at
`ctrl`, and 4 uninitialized buckets below `ctrl`. -/
def rawTableInner4EmptyAt (A : RustAlloc) (stride : Nat) (sret : BitVec 64) : SepProp :=
  ∃∗ ctrl : BitVec 64,
    ⌜ctrl ≠ 0#64 ∧ ctrl.toNat % 8 = 0 ∧
      4 * stride ≤ ctrl.toNat ∧ ctrl.toNat + 12 < 2 ^ 64⌝ ∗
    (sret ↦₆₄ ctrl) ∗
    ((sret + 8#64) ↦₆₄ 3#64) ∗
    ((sret + 16#64) ↦₆₄ 3#64) ∗
    ((sret + 24#64) ↦₆₄ 0#64) ∗
    A.live (ctrl - BitVec.ofNat 64 (4 * stride)) (tableAllocSize 4 stride) (asm% hashbrownTableAlign) ∗
    (ctrl ↦ₛ emptyCtrl4) ∗
    arrayAt (fun _ a => memRegion a stride) stride
      (ctrl - BitVec.ofNat 64 (4 * stride)) (List.range 4).reverse

/-- Ghost arguments `(sret, stride, capacity, fallibility)` for `fallible_with_capacity` (`0x01798`). -/
structure FallibleWithCapacityGhost where
  sret : BitVec 64
  stride : Nat
  capacity : Nat

/-- `<RawTableInner>::fallible_with_capacity::<Global>` (`0x01798`) for `1 ≤ capacity < 4` and
8-byte-aligned `stride` under `Fallibility::Infallible` (`x3 = 1#64`). -/
def fallibleWithCapacity4Spec (A : RustAlloc) : Spec FallibleWithCapacityGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.sret ∧
      (s.readReg64 .x1).toNat = x.stride ∧
      (s.readReg64 .x2).toNat = x.capacity ∧
      s.readReg64 .x3 = 1#64 ∧
      1 ≤ x.capacity ∧ x.capacity < 4 ∧
      0 < x.stride ∧ x.stride ≤ 0x1000 ∧ x.stride % 8 = 0⌝ ∗
      memRegion x.sret 32 ∗ A.pool ∗ stackAt s.sp fallibleWithCapacityStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      rawTableInner4EmptyAt A x.stride x.sret ∗
      A.pool ∗ stackAt s0.sp fallibleWithCapacityStack
  onPanic := fun _ s0 sf =>
    ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-! ## `<RawTable<T>>::reserve_rehash` (`0x0081c`, `0x00a44`) -/

/-- Ghost arguments for `RawTable<T>::reserve_rehash` on `emptyTableAt base mp k0 k1`. -/
structure ReserveRehashEmptyGhost where
  base : BitVec 64
  mp : BitVec 64
  rsPtr : BitVec 64
  k0 : BitVec 64
  k1 : BitVec 64

/-- `<RawTable<T>>::reserve_rehash` (`0x0081c` for `stride = 64`, `0x00a44` for `stride = 400`) on
`emptyTableAt base mp k0 k1` with `additional = 1` and `Fallibility::Infallible`, establishing
`table4EmptyAt A stride mp k0 k1`. -/
def reserveRehashEmptySpec (A : RustAlloc) (stride : Nat) : Spec ReserveRehashEmptyGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.mp ∧
      s.readReg64 .x1 = 1#64 ∧
      s.readReg64 .x2 = x.rsPtr ∧
      s.readReg64 .x3 = 1#64⌝ ∗
      emptyTableAt x.base x.mp x.k0 x.k1 ∗
      A.pool ∗ stackAt s.sp reserveRehashStack
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x0 = 0xffffffffffffffff#64 ∧ sf.trace = s0.trace⌝ ∗
      table4EmptyAt A stride x.mp x.k0 x.k1 ∗
      A.pool ∗ stackAt s0.sp reserveRehashStack
  onPanic := fun _ s0 sf =>
    ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

abbrev reserveRehashIdentityEmptySpec (A : RustAlloc) : Spec ReserveRehashEmptyGhost :=
  reserveRehashEmptySpec A identityBucketStride

abbrev reserveRehashSessionEmptySpec (A : RustAlloc) : Spec ReserveRehashEmptyGhost :=
  reserveRehashEmptySpec A sessionBucketStride

/-! ## `<HashMap<ProtocolAddress, IdentityKey>>::insert` (`0x14ee0`) -/

/-- 33-byte `Option<IdentityKey>` at `sret`: byte `0` is `0#8` (`None`) or `1#8` (`Some`) followed
by 32 compressed public-key bytes at `sret + 1..33`. -/
def optIdentityKeyAt (sret : BitVec 64) : Option (List (BitVec 8)) → SepProp
  | none => (sret ↦₈ 0#8) ∗ memRegion (sret + 1#64) 32
  | some keyBytes => ⌜keyBytes.length = 32⌝ ∗ (sret ↦₈ 1#8) ∗ ((sret + 1#64) ↦ₛ keyBytes)

/-- Ghost arguments for `HashMap<ProtocolAddress, IdentityKey>::insert` (`0x14ee0`) on `emptyTableAt`. -/
structure HashMapIdInsertEmptyGhost where
  sret : BitVec 64
  base : BitVec 64
  mp : BitVec 64
  kPtr : BitVec 64
  vPtr : BitVec 64
  k0 : BitVec 64
  k1 : BitVec 64
  g : AddrGhost
  keyBytes : List (BitVec 8)

/-- `<HashMap<ProtocolAddress, IdentityKey>>::insert` (`0x14ee0`) on `emptyTableAt`: allocates a
4-bucket table via `reserve_rehash`, moves `(*kPtr, *vPtr)` into bucket `(hash &&& 3#64).toNat`,
and writes `None` at `sret`. -/
def hashMapIdInsertEmptySpec (A : RustAlloc) : Spec HashMapIdInsertEmptyGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.sret ∧
      s.readReg64 .x1 = x.mp ∧
      s.readReg64 .x2 = x.kPtr ∧
      s.readReg64 .x3 = x.vPtr ∧
      x.g.name.bytes.length = 36 ∧
      x.keyBytes.length = 32⌝ ∗
      emptyTableAt x.base x.mp x.k0 x.k1 ∗
      protocolAddressAt A x.g x.kPtr ∗
      (x.vPtr ↦ₛ x.keyBytes) ∗
      memRegion x.sret 33 ∗
      A.pool ∗ stackAt s.sp hashMapIdInsertStack
  post := fun x s0 sf =>
    let hash := hashAddrBv x.k0 x.k1 x.g.name.bytes x.g.device
    let k := (hash &&& 3#64).toNat
    ⌜sf.trace = s0.trace⌝ ∗
      table4SingleAt A identityBucketStride x.mp x.k0 x.k1 k
        x.g.name.bytes x.g.device (identityBucketEntryAt A x.g x.keyBytes) ∗
      memRegion x.kPtr 32 ∗
      (x.vPtr ↦ₛ x.keyBytes) ∗
      optIdentityKeyAt x.sret none ∗
      A.pool ∗ stackAt s0.sp hashMapIdInsertStack
  onPanic := fun _ s0 sf =>
    ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Ghost arguments for `HashMap<ProtocolAddress, IdentityKey>::insert` (`0x14ee0`) on a 1-item hit. -/
structure HashMapIdInsertSingleHitGhost where
  sret : BitVec 64
  mp : BitVec 64
  kPtr : BitVec 64
  vPtr : BitVec 64
  k0 : BitVec 64
  k1 : BitVec 64
  k : Nat
  oldG : AddrGhost
  newG : AddrGhost
  oldKeyBytes : List (BitVec 8)
  newKeyBytes : List (BitVec 8)

/-- `<HashMap<ProtocolAddress, IdentityKey>>::insert` (`0x14ee0`) on a 1-item hit: keeps the
existing key in bucket `k`, drops the incoming `String` buffer at `kPtr`, replaces `bucket + 0x20`
with `newKeyBytes`, and writes `Some(oldKeyBytes)` at `sret`. -/
def hashMapIdInsertSingleHitSpec (A : RustAlloc) : Spec HashMapIdInsertSingleHitGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.sret ∧
      s.readReg64 .x1 = x.mp ∧
      s.readReg64 .x2 = x.kPtr ∧
      s.readReg64 .x3 = x.vPtr ∧
      x.k < 4 ∧
      x.oldG.name.bytes.length = 36 ∧
      x.newG.name.bytes = x.oldG.name.bytes ∧
      x.newG.device = x.oldG.device ∧
      x.oldKeyBytes.length = 32 ∧
      x.newKeyBytes.length = 32⌝ ∗
      table4SingleAt A identityBucketStride x.mp x.k0 x.k1 x.k
        x.oldG.name.bytes x.oldG.device (identityBucketEntryAt A x.oldG x.oldKeyBytes) ∗
      protocolAddressAt A x.newG x.kPtr ∗
      (x.vPtr ↦ₛ x.newKeyBytes) ∗
      memRegion x.sret 33 ∗
      A.pool ∗ stackAt s.sp hashMapIdInsertStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      table4SingleAt A identityBucketStride x.mp x.k0 x.k1 x.k
        x.oldG.name.bytes x.oldG.device (identityBucketEntryAt A x.oldG x.newKeyBytes) ∗
      memRegion x.kPtr 32 ∗
      (x.vPtr ↦ₛ x.newKeyBytes) ∗
      optIdentityKeyAt x.sret (some x.oldKeyBytes) ∗
      A.pool ∗ stackAt s0.sp hashMapIdInsertStack

/-! ## `InMemIdentityKeyStore` Future Closures (`0x07658`, `0x079c4`, `0x077cc`) -/


/-- 48-byte `Poll::Ready(Ok(Option<IdentityKey>))` at `sret`: word `0` is `-2#64`, byte `8` is the
`Option` discriminant, and bytes `9..41` hold the 32-byte key in the `Some` case. -/
def pollOptIdentityKeyResultAt (sret : BitVec 64) : Option (List (BitVec 8)) → SepProp
  | none =>
    (sret ↦₆₄ 0xfffffffffffffffe#64) ∗ ((sret + 8#64) ↦₈ 0#8) ∗ memRegion (sret + 9#64) 39
  | some keyBytes =>
    ⌜keyBytes.length = 32⌝ ∗ (sret ↦₆₄ 0xfffffffffffffffe#64) ∗ ((sret + 8#64) ↦₈ 1#8) ∗
      ((sret + 9#64) ↦ₛ keyBytes) ∗ memRegion (sret + 41#64) 7

/-- 48-byte `Poll::Ready(Ok(bool))` at `sret`: word `0` is `-2#64` and byte `8` is `1#8` or `0#8`. -/
def pollBoolResultAt (sret : BitVec 64) (b : Bool) : SepProp :=
  (sret ↦₆₄ 0xfffffffffffffffe#64) ∗ ((sret + 8#64) ↦₈ (if b then 1#8 else 0#8)) ∗
    memRegion (sret + 9#64) 39

/-- 48-byte `Poll::Ready(Ok(IdentityChange))` at `sret`: word `0` is `-2#64` and the `u32` at
`sret + 8` is `1#32` (`ReplacedExisting`) or `0#32` (`NewOrUnchanged`). -/
def pollIdentityChangeResultAt (sret : BitVec 64) (replaced : Bool) : SepProp :=
  (sret ↦₆₄ 0xfffffffffffffffe#64) ∗
    ((sret + 8#64) ↦₃₂ (if replaced then 1#32 else 0#32)) ∗
    memRegion (sret + 12#64) 36

structure GetIdentitySingleGhost where
  futPtr : BitVec 64
  sret : BitVec 64
  mp : BitVec 64
  k0 : BitVec 64
  k1 : BitVec 64
  k : Nat
  peerG : AddrGhost
  peerKeyBytes : List (BitVec 8)
  qAddrPtr : BitVec 64
  qG : AddrGhost

/-- `InMemIdentityKeyStore::get_identity::{closure#0}` (`0x07658`) on `table4SingleAt`, returning
`Ready(Ok(Some(peerKeyBytes)))` iff `(qG.name.bytes, qG.device) = (peerG.name.bytes, peerG.device)`. -/
def getIdentitySingleSpec (A : RustAlloc) : Spec GetIdentitySingleGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.futPtr ∧ s.readReg64 .x8 = x.sret ∧
      x.k < 4 ∧ x.peerG.name.bytes.length = 36 ∧ x.qG.name.bytes.length = 36 ∧
      x.peerKeyBytes.length = 32⌝ ∗
      (x.futPtr ↦₆₄ x.mp) ∗ ((x.futPtr + 8#64) ↦₆₄ x.qAddrPtr) ∗ ((x.futPtr + 16#64) ↦₈ 0#8) ∗
      table4SingleAt A identityBucketStride x.mp x.k0 x.k1 x.k
        x.peerG.name.bytes x.peerG.device (identityBucketEntryAt A x.peerG x.peerKeyBytes) ∗
      protocolAddressAt A x.qG x.qAddrPtr ∗
      memRegion x.sret 48 ∗
      stackAt s.sp getIdentityClosureStack
  post := fun x s0 sf =>
    let res := if x.qG.name.bytes = x.peerG.name.bytes ∧ x.qG.device = x.peerG.device
               then some x.peerKeyBytes else none
    ⌜sf.trace = s0.trace⌝ ∗
      (x.futPtr ↦₆₄ x.mp) ∗ ((x.futPtr + 8#64) ↦₆₄ x.qAddrPtr) ∗ ((x.futPtr + 16#64) ↦₈ 1#8) ∗
      table4SingleAt A identityBucketStride x.mp x.k0 x.k1 x.k
        x.peerG.name.bytes x.peerG.device (identityBucketEntryAt A x.peerG x.peerKeyBytes) ∗
      protocolAddressAt A x.qG x.qAddrPtr ∗
      pollOptIdentityKeyResultAt x.sret res ∗
      stackAt s0.sp getIdentityClosureStack

structure IsTrustedIdentitySingleGhost where
  futPtr : BitVec 64
  sret : BitVec 64
  mp : BitVec 64
  k0 : BitVec 64
  k1 : BitVec 64
  k : Nat
  peerG : AddrGhost
  peerKeyBytes : List (BitVec 8)
  qAddrPtr : BitVec 64
  qG : AddrGhost
  qKeyPtr : BitVec 64
  qKeyBytes : List (BitVec 8)
  direction : BitVec 8

/-- `InMemIdentityKeyStore::is_trusted_identity::{closure#0}` (`0x079c4`) on `table4SingleAt`,
returning `Ready(Ok(decide (qG = peerG → peerKeyBytes = qKeyBytes)))`. -/
def isTrustedIdentitySingleSpec (A : RustAlloc) : Spec IsTrustedIdentitySingleGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.futPtr ∧ s.readReg64 .x8 = x.sret ∧
      x.k < 4 ∧ x.peerG.name.bytes.length = 36 ∧ x.qG.name.bytes.length = 36 ∧
      x.peerKeyBytes.length = 32 ∧ x.qKeyBytes.length = 32⌝ ∗
      (x.futPtr ↦₆₄ x.mp) ∗ ((x.futPtr + 8#64) ↦₆₄ x.qAddrPtr) ∗
      ((x.futPtr + 16#64) ↦₆₄ x.qKeyPtr) ∗ ((x.futPtr + 24#64) ↦₈ 0#8) ∗
      ((x.futPtr + 25#64) ↦₈ x.direction) ∗
      table4SingleAt A identityBucketStride x.mp x.k0 x.k1 x.k
        x.peerG.name.bytes x.peerG.device (identityBucketEntryAt A x.peerG x.peerKeyBytes) ∗
      protocolAddressAt A x.qG x.qAddrPtr ∗
      (x.qKeyPtr ↦ₛ x.qKeyBytes) ∗
      memRegion x.sret 48 ∗
      stackAt s.sp isTrustedIdentityClosureStack
  post := fun x s0 sf =>
    let trusted := decide ((x.qG.name.bytes = x.peerG.name.bytes ∧ x.qG.device = x.peerG.device) →
      x.peerKeyBytes = x.qKeyBytes)
    ⌜sf.trace = s0.trace⌝ ∗
      (x.futPtr ↦₆₄ x.mp) ∗ ((x.futPtr + 8#64) ↦₆₄ x.qAddrPtr) ∗
      ((x.futPtr + 16#64) ↦₆₄ x.qKeyPtr) ∗ ((x.futPtr + 24#64) ↦₈ 1#8) ∗
      ((x.futPtr + 25#64) ↦₈ x.direction) ∗
      table4SingleAt A identityBucketStride x.mp x.k0 x.k1 x.k
        x.peerG.name.bytes x.peerG.device (identityBucketEntryAt A x.peerG x.peerKeyBytes) ∗
      protocolAddressAt A x.qG x.qAddrPtr ∗
      (x.qKeyPtr ↦ₛ x.qKeyBytes) ∗
      pollBoolResultAt x.sret trusted ∗
      stackAt s0.sp isTrustedIdentityClosureStack

structure SaveIdentityEmptyGhost where
  futPtr : BitVec 64
  sret : BitVec 64
  base : BitVec 64
  mp : BitVec 64
  k0 : BitVec 64
  k1 : BitVec 64
  qAddrPtr : BitVec 64
  qG : AddrGhost
  qKeyPtr : BitVec 64
  qKeyBytes : List (BitVec 8)

/-- `InMemIdentityKeyStore::save_identity::{closure#0}` (`0x077cc`) on `emptyTableAt`: clones
`*qAddrPtr`, inserts into bucket `(hash &&& 3#64).toNat`, and writes `NewOrUnchanged` at `sret`. -/
def saveIdentityEmptySpec (A : RustAlloc) : Spec SaveIdentityEmptyGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.futPtr ∧ s.readReg64 .x8 = x.sret ∧
      x.qG.name.bytes.length = 36 ∧ x.qKeyBytes.length = 32⌝ ∗
      (x.futPtr ↦₆₄ x.mp) ∗ ((x.futPtr + 8#64) ↦₆₄ x.qAddrPtr) ∗
      ((x.futPtr + 16#64) ↦₆₄ x.qKeyPtr) ∗ ((x.futPtr + 24#64) ↦₈ 0#8) ∗
      emptyTableAt x.base x.mp x.k0 x.k1 ∗
      protocolAddressAt A x.qG x.qAddrPtr ∗
      (x.qKeyPtr ↦ₛ x.qKeyBytes) ∗
      memRegion x.sret 48 ∗
      A.pool ∗ stackAt s.sp saveIdentityClosureStack
  post := fun x s0 sf =>
    let hash := hashAddrBv x.k0 x.k1 x.qG.name.bytes x.qG.device
    let k := (hash &&& 3#64).toNat
    ⌜sf.trace = s0.trace⌝ ∗
      (x.futPtr ↦₆₄ x.mp) ∗ ((x.futPtr + 8#64) ↦₆₄ x.qAddrPtr) ∗
      ((x.futPtr + 16#64) ↦₆₄ x.qKeyPtr) ∗ ((x.futPtr + 24#64) ↦₈ 1#8) ∗
      (∃∗ clonedG : AddrGhost,
        ⌜clonedG.name.bytes = x.qG.name.bytes ∧ clonedG.device = x.qG.device⌝ ∗
        table4SingleAt A identityBucketStride x.mp x.k0 x.k1 k
          x.qG.name.bytes x.qG.device (identityBucketEntryAt A clonedG x.qKeyBytes)) ∗
      protocolAddressAt A x.qG x.qAddrPtr ∗
      (x.qKeyPtr ↦ₛ x.qKeyBytes) ∗
      pollIdentityChangeResultAt x.sret false ∗
      A.pool ∗ stackAt s0.sp saveIdentityClosureStack
  onPanic := fun _ s0 sf =>
    ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

structure SaveIdentitySingleHitGhost where
  futPtr : BitVec 64
  sret : BitVec 64
  mp : BitVec 64
  k0 : BitVec 64
  k1 : BitVec 64
  k : Nat
  peerG : AddrGhost
  oldKeyBytes : List (BitVec 8)
  qAddrPtr : BitVec 64
  qG : AddrGhost
  qKeyPtr : BitVec 64
  newKeyBytes : List (BitVec 8)

/-- `InMemIdentityKeyStore::save_identity::{closure#0}` (`0x077cc`) on a 1-item hit: compares keys
via `ConstantTimeEq` (`0x3ebe0`), updates bucket `k` iff `oldKeyBytes ≠ newKeyBytes`, and writes the
resulting `IdentityChange` at `sret`. -/
def saveIdentitySingleHitSpec (A : RustAlloc) : Spec SaveIdentitySingleHitGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.futPtr ∧ s.readReg64 .x8 = x.sret ∧
      x.k < 4 ∧ x.peerG.name.bytes.length = 36 ∧
      x.qG.name.bytes = x.peerG.name.bytes ∧ x.qG.device = x.peerG.device ∧
      x.oldKeyBytes.length = 32 ∧ x.newKeyBytes.length = 32⌝ ∗
      (x.futPtr ↦₆₄ x.mp) ∗ ((x.futPtr + 8#64) ↦₆₄ x.qAddrPtr) ∗
      ((x.futPtr + 16#64) ↦₆₄ x.qKeyPtr) ∗ ((x.futPtr + 24#64) ↦₈ 0#8) ∗
      table4SingleAt A identityBucketStride x.mp x.k0 x.k1 x.k
        x.peerG.name.bytes x.peerG.device (identityBucketEntryAt A x.peerG x.oldKeyBytes) ∗
      protocolAddressAt A x.qG x.qAddrPtr ∗
      (x.qKeyPtr ↦ₛ x.newKeyBytes) ∗
      memRegion x.sret 48 ∗
      A.pool ∗ stackAt s.sp saveIdentityClosureStack
  post := fun x s0 sf =>
    let replaced := decide (x.oldKeyBytes ≠ x.newKeyBytes)
    ⌜sf.trace = s0.trace⌝ ∗
      (x.futPtr ↦₆₄ x.mp) ∗ ((x.futPtr + 8#64) ↦₆₄ x.qAddrPtr) ∗
      ((x.futPtr + 16#64) ↦₆₄ x.qKeyPtr) ∗ ((x.futPtr + 24#64) ↦₈ 1#8) ∗
      table4SingleAt A identityBucketStride x.mp x.k0 x.k1 x.k
        x.peerG.name.bytes x.peerG.device (identityBucketEntryAt A x.peerG x.newKeyBytes) ∗
      protocolAddressAt A x.qG x.qAddrPtr ∗
      (x.qKeyPtr ↦ₛ x.newKeyBytes) ∗
      pollIdentityChangeResultAt x.sret replaced ∗
      A.pool ∗ stackAt s0.sp saveIdentityClosureStack
  onPanic := fun _ s0 sf =>
    ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-! ## `InMemSessionStore` Future Closures (`0x08ce4`, `0x08ee4`) -/

open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.Serialization

/-- 368-byte `Poll::Ready(Ok(Option<SessionRecord>))` at `sret`: `-1#64` at `sret` for `None`, or a
cloned 368-byte `SessionRecord` with niche `previous_sessions.cap = 0` at `sret` for `Some`. -/
def pollOptSessionRecordResultAt (A : RustAlloc) (sret : BitVec 64) :
    Option (Session (List (BitVec 8))) → SepProp
  | none =>
    (sret ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (sret + 8#64) 360
  | some ss =>
    ∃∗ G' : SessionGhost,
      ⌜CanonSession G' ss⌝ ∗
      sessionRecordAt A sret ⟨0#64, 8#64, some G'⟩ ⟨some ss⟩

/-- 48-byte `Poll::Ready(Ok(()))` at `sret` (word `0` equal to `-2#64`). -/
def pollUnitResultAt (sret : BitVec 64) : SepProp :=
  (sret ↦₆₄ 0xfffffffffffffffe#64) ∗ memRegion (sret + 8#64) 40

structure LoadSessionSingleGhost where
  futPtr : BitVec 64
  sret : BitVec 64
  mp : BitVec 64
  k0 : BitVec 64
  k1 : BitVec 64
  k : Nat
  peerG : AddrGhost
  recG : SessionGhost
  ss : Session (List (BitVec 8))
  qAddrPtr : BitVec 64
  qG : AddrGhost

abbrev LoadSessionGhost := LoadSessionSingleGhost

/-- `InMemSessionStore::load_session::{closure#0}` (`0x08ce4`) on `table4SingleAt`, cloning the
stored `SessionRecord` into `sret` iff `(qG.name.bytes, qG.device) = (peerG.name.bytes, peerG.device)`. -/
def loadSessionSingleSpec (A : RustAlloc) : Spec LoadSessionSingleGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.futPtr ∧ s.readReg64 .x8 = x.sret ∧
      x.k < 4 ∧ x.peerG.name.bytes.length = 36 ∧ x.qG.name.bytes.length = 36⌝ ∗
      (x.futPtr ↦₆₄ x.mp) ∗ ((x.futPtr + 8#64) ↦₆₄ x.qAddrPtr) ∗ ((x.futPtr + 16#64) ↦₈ 0#8) ∗
      table4SingleAt A sessionBucketStride x.mp x.k0 x.k1 x.k
        x.peerG.name.bytes x.peerG.device (sessionBucketEntryAt A x.peerG x.recG x.ss) ∗
      protocolAddressAt A x.qG x.qAddrPtr ∗
      memRegion x.sret 368 ∗
      A.pool ∗ stackAt s.sp loadSessionClosureStack
  post := fun x s0 sf =>
    let res := if x.qG.name.bytes = x.peerG.name.bytes ∧ x.qG.device = x.peerG.device
               then some x.ss else none
    ⌜sf.trace = s0.trace⌝ ∗
      (x.futPtr ↦₆₄ x.mp) ∗ ((x.futPtr + 8#64) ↦₆₄ x.qAddrPtr) ∗ ((x.futPtr + 16#64) ↦₈ 1#8) ∗
      table4SingleAt A sessionBucketStride x.mp x.k0 x.k1 x.k
        x.peerG.name.bytes x.peerG.device (sessionBucketEntryAt A x.peerG x.recG x.ss) ∗
      protocolAddressAt A x.qG x.qAddrPtr ∗
      pollOptSessionRecordResultAt A x.sret res ∗
      A.pool ∗ stackAt s0.sp loadSessionClosureStack
  onPanic := fun _ s0 sf =>
    ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

structure StoreSessionEmptyGhost where
  futPtr : BitVec 64
  sret : BitVec 64
  base : BitVec 64
  mp : BitVec 64
  k0 : BitVec 64
  k1 : BitVec 64
  qAddrPtr : BitVec 64
  qG : AddrGhost
  recPtr : BitVec 64
  recG : SessionGhost
  ss : Session (List (BitVec 8))
  prevCap : BitVec 64 := 0#64
  prevPtr : BitVec 64 := 8#64

/-- `InMemSessionStore::store_session::{closure#0}` (`0x08ee4`) on `emptyTableAt`: clones key and
record, allocates a 4-bucket table via `reserve_rehash` (`0x00a44`), and copies the 400-byte entry
into bucket `(hash &&& 3#64).toNat`. -/
def storeSessionEmptySpec (A : RustAlloc) : Spec StoreSessionEmptyGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.futPtr ∧ s.readReg64 .x8 = x.sret ∧
      x.qG.name.bytes.length = 36 ∧ CanonSession x.recG x.ss⌝ ∗
      (x.futPtr ↦₆₄ x.mp) ∗ ((x.futPtr + 8#64) ↦₆₄ x.qAddrPtr) ∗
      ((x.futPtr + 16#64) ↦₆₄ x.recPtr) ∗ ((x.futPtr + 24#64) ↦₈ 0#8) ∗
      emptyTableAt x.base x.mp x.k0 x.k1 ∗
      protocolAddressAt A x.qG x.qAddrPtr ∗
      sessionRecordAt A x.recPtr ⟨x.prevCap, x.prevPtr, some x.recG⟩ ⟨some x.ss⟩ ∗
      memRegion x.sret 48 ∗
      A.pool ∗ stackAt s.sp storeSessionClosureStack
  post := fun x s0 sf =>
    let hash := hashAddrBv x.k0 x.k1 x.qG.name.bytes x.qG.device
    let k := (hash &&& 3#64).toNat
    ⌜sf.trace = s0.trace⌝ ∗
      (x.futPtr ↦₆₄ x.mp) ∗ ((x.futPtr + 8#64) ↦₆₄ x.qAddrPtr) ∗
      ((x.futPtr + 16#64) ↦₆₄ x.recPtr) ∗ ((x.futPtr + 24#64) ↦₈ 1#8) ∗
      (∃∗ clonedG : AddrGhost, ∃∗ clonedRecG : SessionGhost,
        ⌜clonedG.name.bytes = x.qG.name.bytes ∧ clonedG.device = x.qG.device ∧
          CanonSession clonedRecG x.ss⌝ ∗
        table4SingleAt A sessionBucketStride x.mp x.k0 x.k1 k
          x.qG.name.bytes x.qG.device (sessionBucketEntryAt A clonedG clonedRecG x.ss)) ∗
      protocolAddressAt A x.qG x.qAddrPtr ∗
      sessionRecordAt A x.recPtr ⟨x.prevCap, x.prevPtr, some x.recG⟩ ⟨some x.ss⟩ ∗
      pollUnitResultAt x.sret ∗
      A.pool ∗ stackAt s0.sp storeSessionClosureStack
  onPanic := fun _ s0 sf =>
    ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

structure StoreSessionSingleHitGhost where
  futPtr : BitVec 64
  sret : BitVec 64
  mp : BitVec 64
  k0 : BitVec 64
  k1 : BitVec 64
  k : Nat
  peerG : AddrGhost
  oldRecG : SessionGhost
  oldSs : Session (List (BitVec 8))
  qAddrPtr : BitVec 64
  qG : AddrGhost
  recPtr : BitVec 64
  newRecG : SessionGhost
  newSs : Session (List (BitVec 8))
  newPrevCap : BitVec 64 := 0#64
  newPrevPtr : BitVec 64 := 8#64

abbrev StoreSessionHitGhost := StoreSessionSingleHitGhost

/-- `InMemSessionStore::store_session::{closure#0}` (`0x08ee4`) on a 1-item hit: clones key and
record, replaces bucket `k` in place, drops the replaced key buffer and old `SessionRecord`, and
writes `Ready(Ok(()))` at `sret`. -/
def storeSessionSingleHitSpec (A : RustAlloc) : Spec StoreSessionSingleHitGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.futPtr ∧ s.readReg64 .x8 = x.sret ∧
      x.k < 4 ∧ x.peerG.name.bytes.length = 36 ∧
      x.qG.name.bytes = x.peerG.name.bytes ∧ x.qG.device = x.peerG.device ∧
      CanonSession x.newRecG x.newSs⌝ ∗
      (x.futPtr ↦₆₄ x.mp) ∗ ((x.futPtr + 8#64) ↦₆₄ x.qAddrPtr) ∗
      ((x.futPtr + 16#64) ↦₆₄ x.recPtr) ∗ ((x.futPtr + 24#64) ↦₈ 0#8) ∗
      table4SingleAt A sessionBucketStride x.mp x.k0 x.k1 x.k
        x.peerG.name.bytes x.peerG.device (sessionBucketEntryAt A x.peerG x.oldRecG x.oldSs) ∗
      protocolAddressAt A x.qG x.qAddrPtr ∗
      sessionRecordAt A x.recPtr ⟨x.newPrevCap, x.newPrevPtr, some x.newRecG⟩ ⟨some x.newSs⟩ ∗
      memRegion x.sret 48 ∗
      A.pool ∗ stackAt s.sp storeSessionClosureStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (x.futPtr ↦₆₄ x.mp) ∗ ((x.futPtr + 8#64) ↦₆₄ x.qAddrPtr) ∗
      ((x.futPtr + 16#64) ↦₆₄ x.recPtr) ∗ ((x.futPtr + 24#64) ↦₈ 1#8) ∗
      (∃∗ clonedG : AddrGhost, ∃∗ clonedRecG : SessionGhost,
        ⌜clonedG.name.bytes = x.peerG.name.bytes ∧ clonedG.device = x.peerG.device ∧
          CanonSession clonedRecG x.newSs⌝ ∗
        table4SingleAt A sessionBucketStride x.mp x.k0 x.k1 x.k
          x.peerG.name.bytes x.peerG.device (sessionBucketEntryAt A clonedG clonedRecG x.newSs)) ∗
      protocolAddressAt A x.qG x.qAddrPtr ∗
      sessionRecordAt A x.recPtr ⟨x.newPrevCap, x.newPrevPtr, some x.newRecG⟩ ⟨some x.newSs⟩ ∗
      pollUnitResultAt x.sret ∗
      A.pool ∗ stackAt s0.sp storeSessionClosureStack
  onPanic := fun _ s0 sf =>
    ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

end CryptoVerification.E2E.InMem.HashbrownBin

