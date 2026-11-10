/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import VCVio.Prelude.Core

/-!
# Instruction Decode Lemmas for Compiled `hashbrown` Routines

Generates `fetchDecodeAt` decode theorems for `fallible_with_capacity` (`0x01798`),
`reserve_rehash` (`0x0081c`, `0x00a44`), and `HashMap<ProtocolAddress, IdentityKey>::insert`
(`0x14ee0`).
-/

@[expose] public section

namespace CryptoVerification.E2E.InMem.HashbrownBin

open Arm64 ProofLib ProofLib.ProgramReflection

/-! ## `fallible_with_capacity` (`0x1798`, 412 bytes) -/

gen_decodes libsignalSessionCode_tree libsignalSessionBin [(ls_off% "<hashbrown::raw::RawTableInner>::fallible_with_capacity::<alloc::alloc::Global>") → (ls_off% "<hashbrown::raw::RawTableInner>::fallible_with_capacity::<alloc::alloc::Global>" + 188), raw (ls_off% "<hashbrown::raw::RawTableInner>::fallible_with_capacity::<alloc::alloc::Global>" + 192),
    (ls_off% "<hashbrown::raw::RawTableInner>::fallible_with_capacity::<alloc::alloc::Global>" + 196) → (ls_off% "<hashbrown::raw::RawTableInner>::fallible_with_capacity::<alloc::alloc::Global>" + 408)]

/-! ## `reserve_rehash_id` (`0x81c`, 552 bytes) -/

gen_decodes libsignalSessionCode_tree libsignalSessionBin [(ls_off% "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey, std::hash::random::RandomState>::{closure#0}>") → (ls_off% "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey, std::hash::random::RandomState>::{closure#0}>" + 500), raw (ls_off% "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey, std::hash::random::RandomState>::{closure#0}>" + 504), (ls_off% "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey, std::hash::random::RandomState>::{closure#0}>" + 508) → (ls_off% "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey, std::hash::random::RandomState>::{closure#0}>" + 548)]

/-! ## `reserve_rehash_session` (`0xa44`, 564 bytes) -/

gen_decodes libsignalSessionCode_tree libsignalSessionBin [(ls_off% "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord, std::hash::random::RandomState>::{closure#0}>") → (ls_off% "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord, std::hash::random::RandomState>::{closure#0}>" + 512), raw (ls_off% "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord, std::hash::random::RandomState>::{closure#0}>" + 516), (ls_off% "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord, std::hash::random::RandomState>::{closure#0}>" + 520) → (ls_off% "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord, std::hash::random::RandomState>::{closure#0}>" + 560)]

/-! ## `hashmap_id_insert` (`0x14ee0`, 592 bytes) -/

gen_decodes libsignalSessionCode_tree libsignalSessionBin [(ls_off% "<std::collections::hash::map::HashMap<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey>>::insert") → (ls_off% "<std::collections::hash::map::HashMap<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey>>::insert" + 588)]

end CryptoVerification.E2E.InMem.HashbrownBin
