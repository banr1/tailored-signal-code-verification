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
# Instruction Decode Fetches for CLI `spqr::send`

Provides `spqr_fetches_cli` and rebase decode lemmas for `spqr::send::<Coins>` in the CLI image.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.SpqrSendEmpty

open Arm64 ProofLib ProofLib.ProgramReflection

/-- Adds `libsignalSessionCode_fetch_fnAddr` hypotheses for `spqr::send` from relative offset `k0`
over `len` bytes. -/
macro "spqr_fetches_cli " b:term:max H:term:max hfn:term:max k0:num len:num : tactic =>
  `(tactic| code_fetches_range CryptoVerification.libsignalSessionCode libsignalSessionBinCli $b $H
    $hfn (num% (ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>")) $k0 $len)

gen_decodes libsignalSessionCode_tree libsignalSessionBinCli [(ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>" + 0) → (ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>" + 104), (ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>" + 136) → (ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>" + 220), (ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>" + 4608) → (ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>" + 4616), (ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>" + 4632) → (ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>" + 4664)]

end CryptoVerification.LibsignalTripleRatchet.SpqrSendEmpty
