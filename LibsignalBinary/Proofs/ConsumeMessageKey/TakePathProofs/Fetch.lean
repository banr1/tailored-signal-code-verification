/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout

@[expose] public section

namespace CryptoVerification.LibsignalSession.TakePath

open Arm64 ProofLib.ProgramReflection

gen_decodes libsignalSessionCode_tree libsignalSessionBin [(ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key" + 92) → (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key" + 204), (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key" + 336) → (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key" + 364),
    (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key" + 1508) → (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key" + 1944)]

end CryptoVerification.LibsignalSession.TakePath
