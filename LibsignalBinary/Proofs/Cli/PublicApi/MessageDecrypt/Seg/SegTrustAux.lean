/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop

/-!
# CLI `SegTrust` Instruction Decodes

Instruction decode tables (`+0x1fcc..`) for `SegTrust` in `signal_session_ratchet::decrypt_signal`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegTrust

open Arm64 ProofLib ProofLib.ProgramReflection CryptoVerification.RustHeap CryptoGames.LibsignalSession

open CryptoVerification.LibsignalSessionRepr


open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession

open CryptoGames


open CryptoVerification.LibsignalPublicApi.MessageDecrypt

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Instruction decode lemmas -/

gen_decodes libsignalSessionCode_tree segTrustBinCli [(ls_off% "libsignal_cli_ratchet::decrypt_signal" + 8140) → (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 8216), (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 8432) → (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 8524), (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 8592) → (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 8620)]

end CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegTrust
