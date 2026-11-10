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
# Instruction Fetch Helpers for `try_decrypt_from_record` Callees

Re-exports generated decode and fetch lemmas for `drop_glue<SessionStructure> [local#2]` and
`try_decrypt_from_record::{closure#0}`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.FromRecordCallees

open Arm64 ProofLib ProofLib.ProgramReflection

set_option maxHeartbeats 0

set_option maxRecDepth 2000000

gen_decodes libsignalSessionCode_tree fromRecordCalleesBinCli [(ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#3]" + 0) → (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#3]" + 272)]

gen_decodes libsignalSessionCode_tree fromRecordCalleesBinCli [(ls_off% "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_cli_ratchet::Coins>::{closure#0}" + 0) → (ls_off% "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_cli_ratchet::Coins>::{closure#0}" + 44)]

gen_decodes libsignalSessionCode_tree fromRecordCalleesBinCli [(ls_off% "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_cli_ratchet::Coins>::{closure#0}" + 412) → (ls_off% "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_cli_ratchet::Coins>::{closure#0}" + 432)]

end CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
