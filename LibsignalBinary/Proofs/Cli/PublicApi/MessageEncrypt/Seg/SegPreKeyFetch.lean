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
# Instruction Decode Tables for `segPreKey`

Generates instruction decode tables and fetch macros for the pre-key encryption blocks of
`signal_session_ratchet::encrypt` in the CLI image.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalPublicApi

set_option maxRecDepth 200000 in
/-- `session_message_encrypt_with_stores` (`CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName`) starts at image offset `(ls_off% "signal_session_ratchet::encrypt")`. -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.libsignalSessionCode_fnOff_0x3cbd8 :
    libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = (ls_off% "libsignal_cli_ratchet::encrypt") := by
  exact (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt")

/-- Fetch hypotheses for `session_message_encrypt_with_stores`
from fn-relative offset `k0`, `len` bytes. -/
macro "messageEncryptPreKey_fetches_cli " b:term:max H:term:max hfn:term:max k0:num len:num : tactic =>
  `(tactic| code_fetches_range CryptoVerification.libsignalSessionCode messageEncryptPreKeyBinCli $b $H
    $hfn (ls_off% "libsignal_cli_ratchet::encrypt") $k0 $len)

/-! ## E4b (+0x344..+0x390) -/

gen_decodes libsignalSessionCode_tree messageEncryptPreKeyBinCli [(ls_off% "libsignal_cli_ratchet::encrypt" + 836) → (ls_off% "libsignal_cli_ratchet::encrypt" + 908)]

gen_decodes libsignalSessionCode_tree messageEncryptPreKeyBinCli [(ls_off% "libsignal_cli_ratchet::encrypt" + 1664) → (ls_off% "libsignal_cli_ratchet::encrypt" + 1836)]

gen_decodes libsignalSessionCode_tree messageEncryptPreKeyBinCli [(ls_off% "libsignal_cli_ratchet::encrypt" + 1932) → (ls_off% "libsignal_cli_ratchet::encrypt" + 1996)]

gen_decodes libsignalSessionCode_tree messageEncryptPreKeyBinCli [(ls_off% "libsignal_cli_ratchet::encrypt" + 2000) → (ls_off% "libsignal_cli_ratchet::encrypt" + 2024)]

gen_decodes libsignalSessionCode_tree messageEncryptPreKeyBinCli [(ls_off% "libsignal_cli_ratchet::encrypt" + 2176) → (ls_off% "libsignal_cli_ratchet::encrypt" + 2284)]

gen_decodes libsignalSessionCode_tree messageEncryptPreKeyBinCli [(ls_off% "libsignal_cli_ratchet::encrypt" + 2288) → (ls_off% "libsignal_cli_ratchet::encrypt" + 2484)]

gen_decodes libsignalSessionCode_tree messageEncryptPreKeyBinCli [(ls_off% "libsignal_cli_ratchet::encrypt" + 2488) → (ls_off% "libsignal_cli_ratchet::encrypt" + 2668)]

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey
