/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.Specs
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.FallibleWithCapacity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.HashMapIdInsertProof
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.GetIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.IsTrusted
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.ReserveRehash
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.LoadSingle
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreEmpty
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreSingleHit
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.Transport

/-!
# Call-Site Glue and Top-Level Entry Points for Compiled `hashbrown` Tables

Re-exports compiled `hashbrown` and `InMem` store future-closure theorems (`fallible_with_capacity`,
`reserve_rehash`, `HashMap::insert`, `InMemIdentityKeyStore`, and `InMemSessionStore`) along with
relative-offset call-site transport corollaries over `RebasedProg b ext`.
-/

@[expose] public section

namespace CryptoVerification.E2E.InMem.HashbrownBin

open Arm64 ProofLib CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E.InMem.HashbrownModel
open CryptoVerification.E2E.InMem.SipHashModel

/-! ## Call-Distance Transport Helpers -/

/-! ## Out-of-Line Allocation and Resize Call-Site Glue (`0x01798`, `0x0081c`, `0x00a44`) -/

theorem fallibleWithCapacity4_ok_at_reserveRehashId
    (b : BitVec 64) (ext : HookMap) (A : RustAlloc) (hHooks : HashbrownBinHooks A ext) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr reserveRehashIdName + bv% (ls_off% "<hashbrown::raw::RawTableInner>::fallible_with_capacity::<alloc::alloc::Global>" - ls_off% "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey, std::hash::random::RandomState>::{closure#0}>"))
      (fallibleWithCapacity4Spec A) :=
  inImage_ok_at (k := num% (ls_off% "<hashbrown::raw::RawTableInner>::fallible_with_capacity::<alloc::alloc::Global>" - ls_off% "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey, std::hash::random::RandomState>::{closure#0}>"))
    (by rw [reserveRehashId_fnOff, fallibleWithCapacity_fnOff])
    (fallibleWithCapacity4_ok b ext A hHooks)

theorem fallibleWithCapacity4_ok_at_reserveRehashSession
    (b : BitVec 64) (ext : HookMap) (A : RustAlloc) (hHooks : HashbrownBinHooks A ext) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr reserveRehashSessionName + bv% (ls_off% "<hashbrown::raw::RawTableInner>::fallible_with_capacity::<alloc::alloc::Global>" - ls_off% "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord, std::hash::random::RandomState>::{closure#0}>"))
      (fallibleWithCapacity4Spec A) :=
  inImage_ok_at (k := num% (ls_off% "<hashbrown::raw::RawTableInner>::fallible_with_capacity::<alloc::alloc::Global>" - ls_off% "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord, std::hash::random::RandomState>::{closure#0}>"))
    (by rw [reserveRehashSession_fnOff, fallibleWithCapacity_fnOff])
    (fallibleWithCapacity4_ok b ext A hHooks)

theorem reserveRehashIdentityEmpty_ok_at_hashMapIdInsert
    (b : BitVec 64) (ext : HookMap) (A : RustAlloc) (hHooks : HashbrownBinHooks A ext) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr hashMapIdInsertName - bv% (ls_off% "<libsignal_protocol::sender_keys::SenderKeyRecord>::serialize" + 1016))
      (reserveRehashIdentityEmptySpec A) :=
  inImage_ok_back hashMapIdInsert_fnOff reserveRehashId_fnOff (d := num% (ls_off% "<libsignal_protocol::sender_keys::SenderKeyRecord>::serialize" + 1016)) (by decide)
    (reserveRehashIdentityEmpty_ok b ext A hHooks)

theorem reserveRehashSessionEmpty_ok_at_storeSessionClosure
    (b : BitVec 64) (ext : HookMap) (A : RustAlloc) (hHooks : HashbrownBinHooks A ext) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr storeSessionClosureName - bv% (ls_off% "<libsignal_protocol::storage::inmem::InMemSignedPreKeyStore as libsignal_protocol::storage::traits::SignedPreKeyStore>::save_signed_pre_key::{closure#0}" + 324))
      (reserveRehashSessionEmptySpec A) :=
  inImage_ok_back storeSessionClosure_fnOff reserveRehashSession_fnOff (d := num% (ls_off% "<libsignal_protocol::storage::inmem::InMemSignedPreKeyStore as libsignal_protocol::storage::traits::SignedPreKeyStore>::save_signed_pre_key::{closure#0}" + 324)) (by decide)
    (reserveRehashSessionEmpty_ok b ext A hHooks)

/-! ## `<HashMap<ProtocolAddress, IdentityKey>>::insert` (`0x14ee0`) -/

/-- `<HashMap<ProtocolAddress, IdentityKey>>::insert` (`0x14ee0`) on `emptyTableAt`: allocates a
4-bucket table via `reserve_rehash` (`0x0081c`), inserts at `k = (hash &&& 3).toNat`, and returns
`None`. -/
theorem hashMapIdInsertEmpty_ok (b : BitVec 64) (ext : HookMap) (A : RustAlloc)
    (hHooks : HashbrownBinHooks A ext) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr hashMapIdInsertName)
      (hashMapIdInsertEmptySpec A) :=
  hashMapIdInsertEmpty_ok' b ext A hHooks

theorem hashMapIdInsertEmpty_ok_at_saveIdentityClosure
    (b : BitVec 64) (ext : HookMap) (A : RustAlloc) (hHooks : HashbrownBinHooks A ext) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr saveIdentityClosureName + bv% (ls_off% "<std::collections::hash::map::HashMap<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey>>::insert" - ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))
      (hashMapIdInsertEmptySpec A) :=
  inImage_ok_at (k := num% (ls_off% "<std::collections::hash::map::HashMap<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey>>::insert" - ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))
    (by rw [saveIdentityClosure_fnOff, hashMapIdInsert_fnOff])
    (hashMapIdInsertEmpty_ok b ext A hHooks)

/-- `<HashMap<ProtocolAddress, IdentityKey>>::insert` (`0x14ee0`) on a 1-item hit: replaces
`oldKeyBytes` in place with `newKeyBytes`, deallocates `newG`'s `String` buffer, and returns
`Some(oldKeyBytes)`. -/
theorem hashMapIdInsertSingleHit_ok (b : BitVec 64) (ext : HookMap) (A : RustAlloc)
    (hHooks : HashbrownBinHooks A ext) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr hashMapIdInsertName)
      (hashMapIdInsertSingleHitSpec A) :=
  hashMapIdInsertSingleHit_ok' b ext A hHooks

theorem hashMapIdInsertSingleHit_ok_at_saveIdentityClosure
    (b : BitVec 64) (ext : HookMap) (A : RustAlloc) (hHooks : HashbrownBinHooks A ext) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr saveIdentityClosureName + bv% (ls_off% "<std::collections::hash::map::HashMap<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey>>::insert" - ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))
      (hashMapIdInsertSingleHitSpec A) :=
  inImage_ok_at (k := num% (ls_off% "<std::collections::hash::map::HashMap<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey>>::insert" - ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))
    (by rw [saveIdentityClosure_fnOff, hashMapIdInsert_fnOff])
    (hashMapIdInsertSingleHit_ok b ext A hHooks)

/-! ## `InMemIdentityKeyStore` Future Closures (`0x07658`, `0x079c4`, `0x077cc`) -/

/-- `InMemIdentityKeyStore::get_identity::{closure#0}` (`0x07658`) on `table4SingleAt`: returns
`Ready(Ok(Some(peerKeyBytes)))` iff `qG = peerG`, and `Ready(Ok(None))` otherwise. -/
theorem getIdentitySingle_ok (b : BitVec 64) (ext : HookMap) (A : RustAlloc)
    (_hHooks : HashbrownBinHooks A ext) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr getIdentityClosureName)
      (getIdentitySingleSpec A) :=
  IdentityKeyStoreFutures.GetIdentity.getIdentitySingle_ok' b ext A _hHooks

/-- `InMemIdentityKeyStore::is_trusted_identity::{closure#0}` (`0x079c4`) on `table4SingleAt`:
returns `Ready(Ok(decide (qG = peerG → peerKeyBytes = qKeyBytes)))`. -/
theorem isTrustedIdentitySingle_ok (b : BitVec 64) (ext : HookMap) (A : RustAlloc)
    (_hHooks : HashbrownBinHooks A ext) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr isTrustedIdentityClosureName)
      (isTrustedIdentitySingleSpec A) :=
  IdentityKeyStoreFutures.isTrustedIdentitySingle_ok' b ext A _hHooks

/-- `InMemIdentityKeyStore::save_identity::{closure#0}` (`0x077cc`) on `emptyTableAt`: clones
`*qAddrPtr`, inserts via `HashMap::insert`, and returns `Ready(Ok(false))`. -/
theorem saveIdentityEmpty_ok (b : BitVec 64) (ext : HookMap) (A : RustAlloc)
    (hHooks : HashbrownBinHooks A ext) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr saveIdentityClosureName)
      (saveIdentityEmptySpec A) :=
  IdentityKeyStoreFutures.SaveIdentity.saveIdentityEmpty_ok'_of_insert b ext A hHooks
    (hashMapIdInsertEmpty_ok b ext A hHooks)

/-- `InMemIdentityKeyStore::save_identity::{closure#0}` (`0x077cc`) on a 1-item hit: compares keys
in constant time (`0x3ebe0`), updates bucket `k` iff `oldKeyBytes ≠ newKeyBytes`, and returns
`Ready(Ok(decide (oldKeyBytes ≠ newKeyBytes)))`. -/
theorem saveIdentitySingleHit_ok (b : BitVec 64) (ext : HookMap) (A : RustAlloc)
    (hHooks : HashbrownBinHooks A ext) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr saveIdentityClosureName)
      (saveIdentitySingleHitSpec A) :=
  IdentityKeyStoreFutures.SaveIdentity.saveIdentitySingleHit_ok'_of_insert b ext A hHooks
    (hashMapIdInsertSingleHit_ok b ext A hHooks)

/-! ## `InMemSessionStore` Future Closures (`0x08ce4`, `0x08ee4`) -/

/-- `InMemSessionStore::load_session::{closure#0}` (`0x08ce4`) on `table4SingleAt`: clones the
stored `SessionRecord` on key match and returns `Ready(Ok(None))` otherwise. -/
theorem loadSessionSingle_ok (b : BitVec 64) (ext : HookMap) (A : RustAlloc)
    (_hHooks : HashbrownBinHooks A ext) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr loadSessionClosureName)
      (loadSessionSingleSpec A) :=
  SessionStoreFutures.LoadSingle.loadSessionSingle_ok' b ext A _hHooks

/-- `InMemSessionStore::store_session::{closure#0}` (`0x08ee4`) on `emptyTableAt`: clones key and
record, allocates a 4-bucket table via `reserve_rehash` (`0x00a44`), and stores into bucket
`(hash &&& 3).toNat`. -/
theorem storeSessionEmpty_ok (b : BitVec 64) (ext : HookMap) (A : RustAlloc)
    (_hHooks : HashbrownBinHooks A ext) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr storeSessionClosureName)
      (storeSessionEmptySpec A) :=
  SessionStoreFutures.storeSessionEmpty_ok' b ext A _hHooks
    (reserveRehashSessionEmpty_ok_at_storeSessionClosure b ext A _hHooks)

/-- `InMemSessionStore::store_session::{closure#0}` (`0x08ee4`) on a 1-item hit: clones key and
record, replaces bucket `k` in place, drops the old record and duplicate key buffer, and returns
`Ready(Ok(()))`. -/
theorem storeSessionSingleHit_ok (b : BitVec 64) (ext : HookMap) (A : RustAlloc)
    (_hHooks : HashbrownBinHooks A ext) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr storeSessionClosureName)
      (storeSessionSingleHitSpec A) :=
  SessionStoreFutures.storeSessionSingleHit_ok' b ext A _hHooks

end CryptoVerification.E2E.InMem.HashbrownBin
