/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import VCVio.Prelude.Core

/-!
# Instruction Decodes for `signal_session::public::split_id`

Decode lemmas `sidDec_0` through `sidDec_284` covering all 72 instructions (288 bytes) of
`signal_session::public::split_id`.
-/

@[expose] public section

namespace CryptoVerification.SignalSession.Cli.SplitId.Helpers

open Arm64 ProofLib CryptoVerification.SignalSession.Cli

gen_decodes libsignalSessionCode_tree sidDec
  [(ls_off% "libsignal_cli::public::split_id") →
    (ls_off% "libsignal_cli::public::split_id" + 284)]

end CryptoVerification.SignalSession.Cli.SplitId.Helpers
