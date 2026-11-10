/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.LibsignalSessionCode -- shake: keep
public import LibsignalBinary.Proofs.Cli.Specifications.LibsignalPublicApi

/-!
# CLI `SegFinish` Instruction Decodes

Pre-decoded instruction tables for the `SegFinish` segment (`+0xe88..+0xf9c`) of
`session_message_encrypt_with_stores`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFinish

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalPublicApi

set_option maxRecDepth 200000 in
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFinish.libsignalSessionCode_fnOff_0x3cbd8 :
    libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = (ls_off% "libsignal_cli_ratchet::encrypt") := by
  exact (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt")

gen_decodes libsignalSessionCode_tree segFinishBinCli [(ls_off% "libsignal_cli_ratchet::encrypt" + 3720) → (ls_off% "libsignal_cli_ratchet::encrypt" + 3880), (ls_off% "libsignal_cli_ratchet::encrypt" + 3900) → (ls_off% "libsignal_cli_ratchet::encrypt" + 4008)]

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFinish
