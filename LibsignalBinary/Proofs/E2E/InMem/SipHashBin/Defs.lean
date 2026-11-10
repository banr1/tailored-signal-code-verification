/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Aesop.BuiltinRules
public import GeneratedLean.LibsignalSessionCode -- shake: keep
public import LibsignalBinary.Proofs.E2E.InMem.SipHashModel.Model
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Tactic.ToDual
public import ProofLib.SepLogic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import VCVio.Prelude.Core

/-!
# Compiled SipHash-1-3 Definitions and Memory Layouts

Symbol names, stack budgets, and separation-logic layouts (`sipStateAt`, `sipHasher13At`,
`randomStateAt`, `addrBorrowAt`) for `SipHasher13::write`,
`RandomState::hash_one::<&ProtocolAddress>`, and the `RawTable::reserve_rehash` closures.
-/

@[expose] public section

namespace CryptoVerification.E2E.InMem.SipHashBin

open Arm64 ProofLib
open CryptoVerification.E2E.InMem.SipHashModel

abbrev HookMap : Type := String → Option (Arm64.State → Arm64.State)

/-- `libsignalSessionCode` rebased at `b` with extern hook table `ext`. Because the
SipHash routines make no extern calls, contracts proved on `RebasedProg b ext` apply under
any extern table. -/
noncomputable abbrev RebasedProg (b : BitVec 64) (ext : HookMap) : Program :=
  libsignalSessionCode.rebase b ext

/-! ## Symbol Names -/

abbrev sipWriteName : String :=
  "<core::hash::sip::Hasher<core::hash::sip::Sip13Rounds> as core::hash::Hasher>::write"

abbrev hashOneAddrName : String :=
  "<std::hash::random::RandomState as core::hash::BuildHasher>::hash_one::<&libsignal_core::address::ProtocolAddress>"

/-- Inner hasher closure in `RawTable<(ProtocolAddress, IdentityKey)>::reserve_rehash`. -/
abbrev rehashIdClosureName : String :=
  "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey, std::hash::random::RandomState>::{closure#0}>::{closure#0}"

/-- Inner hasher closure in `RawTable<(ProtocolAddress, SessionRecord)>::reserve_rehash`. -/
abbrev rehashSessionClosureName : String :=
  "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord, std::hash::random::RandomState>::{closure#0}>::{closure#0}"

abbrev getIdentityClosureName : String :=
  "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}"

abbrev saveIdentityClosureName : String :=
  "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"

abbrev isTrustedIdentityClosureName : String :=
  "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity::{closure#0}"

abbrev loadSessionClosureName : String :=
  "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}"

abbrev storeSessionClosureName : String :=
  "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}"

abbrev hashMapIdInsertName : String :=
  "<std::collections::hash::map::HashMap<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey>>::insert"

abbrev reserveRehashIdName : String :=
  "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey, std::hash::random::RandomState>::{closure#0}>"

abbrev reserveRehashSessionName : String :=
  "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord, std::hash::random::RandomState>::{closure#0}>"

/-! ## Stack Budgets -/

abbrev sipWriteStack : Nat := 0

abbrev hashOneAddrStack : Nat := 112

abbrev rehashIdClosureStack : Nat := hashOneAddrStack

abbrev rehashSessionClosureStack : Nat := hashOneAddrStack

/-! ## Memory Layouts -/

/-- Layout of the 32-byte SipHash state (`#[repr(C)] struct State { v0, v2, v1, v3 }`) at `a`:
`v0` at `+0x00`, `v2` at `+0x08`, `v1` at `+0x10`, `v3` at `+0x18`. -/
def sipStateAt (a : BitVec 64) (st : SipHashModel.State) : SepProp :=
  (a ↦₆₄ st.v0.toBitVec) ∗
  ((a + 8#64) ↦₆₄ st.v2.toBitVec) ∗
  ((a + 16#64) ↦₆₄ st.v1.toBitVec) ∗
  ((a + 24#64) ↦₆₄ st.v3.toBitVec)

/-- Layout of `core::hash::sip::Hasher<Sip13Rounds>` (72 B) at `a`:
`state` (`+0x00..0x20`), `k0` (`+0x20`), `k1` (`+0x28`), `length` (`+0x30`),
`tail` (`+0x38`), and `ntail` (`+0x40`). -/
def sipHasher13At (a : BitVec 64) (h : SipHasher13) : SepProp :=
  ⌜h.length < 2 ^ 64 ∧ h.ntail < 8⌝ ∗
  sipStateAt a h.state ∗
  ((a + 0x20#64) ↦₆₄ h.k0.toBitVec) ∗
  ((a + 0x28#64) ↦₆₄ h.k1.toBitVec) ∗
  ((a + 0x30#64) ↦₆₄ BitVec.ofNat 64 h.length) ∗
  ((a + 0x38#64) ↦₆₄ h.tail.toBitVec) ∗
  ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 h.ntail)

/-- Layout of `std::hash::random::RandomState { k0, k1 }` (16 B) at `a`. -/
def randomStateAt (a : BitVec 64) (k0 k1 : BitVec 64) : SepProp :=
  (a ↦₆₄ k0) ∗ ((a + 8#64) ↦₆₄ k1)

/-- Borrowed `ProtocolAddress` footprint read by `hash_one::<&ProtocolAddress>`:
`name.ptr` (`+0x08`), `name.len` (`+0x10`), `device_id` (`+0x18`), and the `name` slice at `ptr`. -/
def addrBorrowAt (addr ptr : BitVec 64) (name : List (BitVec 8)) (dev : BitVec 8) : SepProp :=
  ((addr + 8#64) ↦₆₄ ptr) ∗
  ((addr + 16#64) ↦₆₄ BitVec.ofNat 64 name.length) ∗
  ((addr + 24#64) ↦₈ dev) ∗
  (ptr ↦ₛ name)

end CryptoVerification.E2E.InMem.SipHashBin
