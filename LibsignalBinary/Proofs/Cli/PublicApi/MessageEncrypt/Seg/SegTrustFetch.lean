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
# Instruction Decode Tables for `segTrust`

Generates instruction decode tables for the `is_trusted_identity` and `UntrustedIdentity` blocks
(`+0xa70..+0xd4c`) of `signal_session_ratchet::encrypt` in the CLI image.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalPublicApi

set_option maxRecDepth 200000 in
/-- `session_message_encrypt_with_stores` (`CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName`) starts at image offset `(ls_off% "signal_session_ratchet::encrypt")`. -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.libsignalSessionCode_fnOff_sym_3caf4 :
    libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = num% (ls_off% "libsignal_cli_ratchet::encrypt") := by
  exact (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt")

/-! ## E7, E7r, and E9 (`+0xa70..+0xd4c`) -/

gen_decodes libsignalSessionCode_tree segTrustBinCli [(ls_off% "libsignal_cli_ratchet::encrypt" + 2672) → (ls_off% "libsignal_cli_ratchet::encrypt" + 2728)]

gen_decodes libsignalSessionCode_tree segTrustBinCli [(ls_off% "libsignal_cli_ratchet::encrypt" + 2940) → (ls_off% "libsignal_cli_ratchet::encrypt" + 3024)]

gen_decodes libsignalSessionCode_tree segTrustBinCli [(ls_off% "libsignal_cli_ratchet::encrypt" + 3192) → (ls_off% "libsignal_cli_ratchet::encrypt" + 3204), (ls_off% "libsignal_cli_ratchet::encrypt" + 3340) → (ls_off% "libsignal_cli_ratchet::encrypt" + 3388)]

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust
