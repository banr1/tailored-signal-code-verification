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
# Instruction Decode Tables for `MessageEncrypt` Shared Tails

Generates instruction decode tables and fetch macros for the shared exit/error tails of
`signal_session_ratchet::encrypt` in the CLI image.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon

open Arm64 ProofLib ProofLib.ProgramReflection

/-- Fetch hypotheses for `session_message_encrypt_with_stores`
from fn-relative offset `k0`, `len` bytes. -/
macro "messageEncryptTail_fetches_cli " b:term:max H:term:max hfn:term:max k0:num len:num : tactic =>
  `(tactic| code_fetches_range CryptoVerification.libsignalSessionCode messageEncryptTailBinCli $b $H
    $hfn (num% (ls_off% "libsignal_cli_ratchet::encrypt")) $k0 $len)

-- T1 (`+0x46c..+0x5b4`)

gen_decodes libsignalSessionCode_tree messageEncryptTailBinCli [(ls_off% "libsignal_cli_ratchet::encrypt" + 1132) → (ls_off% "libsignal_cli_ratchet::encrypt" + 1456)]

gen_decodes libsignalSessionCode_tree messageEncryptTailBinCli [(ls_off% "libsignal_cli_ratchet::encrypt" + 1460) → (ls_off% "libsignal_cli_ratchet::encrypt" + 1628)]

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon
