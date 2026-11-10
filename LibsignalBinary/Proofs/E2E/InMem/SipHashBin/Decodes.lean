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
# Compiled SipHash-1-3 Instruction Decodes

Kernel-checked `fetchDecodeAt` lemmas for `RandomState::hash_one::<&ProtocolAddress>`,
the `RawTable::reserve_rehash` hasher closures, and `SipHasher13::write`.
-/

@[expose] public section

namespace CryptoVerification.E2E.InMem.SipHashBin

open Arm64 ProofLib ProofLib.ProgramReflection

gen_decodes libsignalSessionCode_tree libsignalSessionBin [(ls_off% "<std::hash::random::RandomState as core::hash::BuildHasher>::hash_one::<&libsignal_core::address::ProtocolAddress>") → (ls_off% "<std::hash::random::RandomState as core::hash::BuildHasher>::hash_one::<&libsignal_core::address::ProtocolAddress>" + 376), (ls_off% "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey, std::hash::random::RandomState>::{closure#0}>::{closure#0}") → (ls_off% "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey, std::hash::random::RandomState>::{closure#0}>::{closure#0}" + 20),
    raw (ls_off% "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey, std::hash::random::RandomState>::{closure#0}>::{closure#0}" + 24), (ls_off% "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord, std::hash::random::RandomState>::{closure#0}>::{closure#0}") → (ls_off% "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord, std::hash::random::RandomState>::{closure#0}>::{closure#0}" + 28), raw (ls_off% "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord, std::hash::random::RandomState>::{closure#0}>::{closure#0}" + 32), (ls_off% "<core::hash::sip::Hasher<core::hash::sip::Sip13Rounds> as core::hash::Hasher>::write") → (ls_off% "<core::hash::sip::Hasher<core::hash::sip::Sip13Rounds> as core::hash::Hasher>::write" + 72), raw (ls_off% "<core::hash::sip::Hasher<core::hash::sip::Sip13Rounds> as core::hash::Hasher>::write" + 76), (ls_off% "<core::hash::sip::Hasher<core::hash::sip::Sip13Rounds> as core::hash::Hasher>::write" + 80) → (ls_off% "<core::hash::sip::Hasher<core::hash::sip::Sip13Rounds> as core::hash::Hasher>::write" + 292),
    raw (ls_off% "<core::hash::sip::Hasher<core::hash::sip::Sip13Rounds> as core::hash::Hasher>::write" + 296), (ls_off% "<core::hash::sip::Hasher<core::hash::sip::Sip13Rounds> as core::hash::Hasher>::write" + 300) → (ls_off% "<core::hash::sip::Hasher<core::hash::sip::Sip13Rounds> as core::hash::Hasher>::write" + 304), raw (ls_off% "<core::hash::sip::Hasher<core::hash::sip::Sip13Rounds> as core::hash::Hasher>::write" + 308), (ls_off% "<core::hash::sip::Hasher<core::hash::sip::Sip13Rounds> as core::hash::Hasher>::write" + 312) → (ls_off% "<core::hash::sip::Hasher<core::hash::sip::Sip13Rounds> as core::hash::Hasher>::write" + 376), raw (ls_off% "<core::hash::sip::Hasher<core::hash::sip::Sip13Rounds> as core::hash::Hasher>::write" + 380), (ls_off% "<core::hash::sip::Hasher<core::hash::sip::Sip13Rounds> as core::hash::Hasher>::write" + 384) → (ls_off% "<core::hash::sip::Hasher<core::hash::sip::Sip13Rounds> as core::hash::Hasher>::write" + 392),
    raw (ls_off% "<core::hash::sip::Hasher<core::hash::sip::Sip13Rounds> as core::hash::Hasher>::write" + 396), (ls_off% "<core::hash::sip::Hasher<core::hash::sip::Sip13Rounds> as core::hash::Hasher>::write" + 400) → (ls_off% "<core::hash::sip::Hasher<core::hash::sip::Sip13Rounds> as core::hash::Hasher>::write" + 484)]

end CryptoVerification.E2E.InMem.SipHashBin
