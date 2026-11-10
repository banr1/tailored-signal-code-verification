/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.LibsignalSessionCode -- shake: keep
public meta import Mathlib.Tactic.Basic
public meta import Mathlib.Tactic.ToAdditive
public meta import Mathlib.Tactic.ToDual
import LibsignalBinary.Proofs.CodeLayout
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import VCVio.Prelude.Core

/-!
# Instruction Decode Fetches for CLI `SegTail` and `SegExit`

Provides `segTail_fetches_cli` and decode lemmas for the error-tail and exit segments of CLI
`signal_session_ratchet::decrypt_signal`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Record

open Arm64 ProofLib ProofLib.ProgramReflection

/-- Adds `libsignalSessionCode_fetch_fnAddr` hypotheses for `signal_session_ratchet::decrypt_signal`
from relative offset `k0` over `len` bytes. -/
macro "segTail_fetches_cli " b:term:max H:term:max hfn:term:max k0:num len:num : tactic =>
  `(tactic| code_fetches_range CryptoVerification.libsignalSessionCode segTailBinCli $b $H
    $hfn (num% (ls_off% "libsignal_cli_ratchet::decrypt_signal")) $k0 $len)

gen_decodes libsignalSessionCode_tree segTailBinCli [(ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2128), raw (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2132), (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2136) → (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2152), (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 5860) → (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 5872), (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 6836) → (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 6864), (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 7408) → (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 7412), (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 7636) → (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 7720), (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 7820) → (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 7868), raw (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 7872), (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 7876) → (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 7888), raw (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 7892), raw (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 7896), (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 7900) → (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 7908), raw (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 7912), raw (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 7916), (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 7920), raw (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 7924), (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 7988) → (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 8012), (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 9792) → (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 9800)]

end CryptoVerification.LibsignalTripleRatchet.Record
