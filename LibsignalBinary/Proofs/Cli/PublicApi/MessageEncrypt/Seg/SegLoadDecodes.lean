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
# CLI `SegLoad` Instruction Decodes

Pre-decoded instruction tables for the `SegLoad` segment (`+0x000..+0x20c`, `+0x41c..+0x458`) of
`session_message_encrypt_with_stores`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad

open Arm64 ProofLib ProofLib.ProgramReflection

/-! ## Entry and Load-Dispatch Ranges (`+0x000..+0x20c`) -/

gen_decodes libsignalSessionCode_tree messageEncryptLoadBinCli [(ls_off% "libsignal_cli_ratchet::encrypt" + 0) → (ls_off% "libsignal_cli_ratchet::encrypt" + 520)]

gen_decodes libsignalSessionCode_tree messageEncryptLoadBinCli [(ls_off% "libsignal_cli_ratchet::encrypt" + 1052) → (ls_off% "libsignal_cli_ratchet::encrypt" + 1112)]

gen_decodes libsignalSessionCode_tree messageEncryptLoadBinCli [(ls_off% "libsignal_cli_ratchet::encrypt" + 1632) → (ls_off% "libsignal_cli_ratchet::encrypt" + 1660)]

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad
