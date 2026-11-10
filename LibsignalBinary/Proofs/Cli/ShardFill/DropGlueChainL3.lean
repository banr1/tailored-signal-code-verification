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
# Instruction Decodes for `drop_glue::<Chain> [local#2]`

Generates instruction decode theorems (`libsignalTripleRatchetBinCli`, `0..248`) for
`core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#2]` in
`libsignalSessionCode_tree`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib.ProgramReflection

set_option maxHeartbeats 0

gen_decodes libsignalSessionCode_tree libsignalTripleRatchetBinCli [(ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#2]" + 0) → (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#2]" + 248)]

end CryptoVerification.LibsignalTripleRatchet
