/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.LibsignalSessionCode -- shake: keep
public import LibsignalBinary.Proofs.Cli.Specifications.LibsignalTripleRatchet

/-!
# CLI `SegRegionNone` Instruction Fetch Macro

Entry offset equation and range-fetch tactic for `SegRegionNone` in
`signal_session_ratchet::decrypt_signal`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegRegionNone

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoVerification.LibsignalTripleRatchet

set_option maxRecDepth 200000 in
/-- Entry offset of `signal_session_ratchet::decrypt_signal` (`238760`). -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegRegionNone.libsignalSessionCode_fnOff_sym_3a4a8 :
    libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName = num% (ls_off% "libsignal_cli_ratchet::decrypt_signal") := by
  exact (ls_lemma% fnOff "libsignal_cli_ratchet::decrypt_signal")

/-- Discharges instruction-fetch hypotheses for `signal_session_ratchet::decrypt_signal` on `[k0, k0 + len)`. -/
macro "messageDecryptRegionNone_fetches_cli " b:term:max H:term:max hfn:term:max k0:num len:num : tactic =>
  `(tactic| code_fetches_range CryptoVerification.libsignalSessionCode messageDecryptRegionNoneBinCli $b $H
    $hfn (num% (ls_off% "libsignal_cli_ratchet::decrypt_signal")) $k0 $len)

gen_decodes libsignalSessionCode_tree messageDecryptRegionNoneBinCli [(ls_off% "libsignal_cli_ratchet::decrypt_signal" + 424) → (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 504), (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2140) → (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2152), (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 5860) → (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 5872), (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 6836) → (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 6852), (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 6912) → (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 6920), (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 7408) → (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 7412), (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 7636) → (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 7720), (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 9792) → (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 9800), (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 7820) → (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 7828), (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 7988) → (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 7992)]

end CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegRegionNone
