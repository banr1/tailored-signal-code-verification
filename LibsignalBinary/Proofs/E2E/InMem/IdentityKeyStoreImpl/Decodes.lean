/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout

/-!
# In-Memory Identity Key Store Instruction Decodes

Kernel-checked `fetchDecodeAt` lemmas for `<InMemIdentityKeyStore as IdentityKeyStore>`
methods (`save_identity`, `is_trusted_identity`) and the shared trivial future `drop_glue`.
-/

@[expose] public section

namespace CryptoVerification.E2E.InMem.IdentityKeyStoreImpl

open Arm64 ProofLib ProofLib.ProgramReflection

/-! ## Future Drop -/

gen_decodes libsignalSessionCode_tree identityKeyStoreBin [(ls_off% "core::ptr::drop_glue::<<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}>")]

/-! ## `InMemIdentityKeyStore::save_identity` -/

gen_decodes libsignalSessionCode_tree identityKeyStoreBin [(ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity") → (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity" + 92)]

/-! ## `InMemIdentityKeyStore::is_trusted_identity` -/

gen_decodes libsignalSessionCode_tree identityKeyStoreBin [(ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity") → (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity" + 100)]

end CryptoVerification.E2E.InMem.IdentityKeyStoreImpl
