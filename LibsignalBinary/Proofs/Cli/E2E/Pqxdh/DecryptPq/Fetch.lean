/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.Fetch -- shake: keep

/-!
# Instruction Fetch Table for CLI `try_decrypt_with_state::<Coins>`

Instruction-fetch table for `try_decrypt_with_state::<signal_session_handshake::Coins>` in
`libsignalSessionImage`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib.ProgramReflection

set_option maxHeartbeats 0

/-! ## `try_decrypt_with_state::<Coins>` (`0x6eff8..0x6fccc`, 3288 bytes) -/

gen_decodes libsignalSessionCode_tree libsignalTripleRatchetBinCli [(ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>" + 0) → (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>" + 3284)]

end CryptoVerification.LibsignalTripleRatchet
