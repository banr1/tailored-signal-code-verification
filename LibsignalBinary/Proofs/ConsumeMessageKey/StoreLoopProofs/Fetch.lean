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

namespace CryptoVerification.LibsignalSession.StoreLoop

open Arm64 ProofLib.ProgramReflection

gen_decodes libsignalSessionCode_tree libsignalSessionBin [(ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key" + 820) → (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key" + 1240), (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key" + 2484) → (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key" + 2492)]

end CryptoVerification.LibsignalSession.StoreLoop
