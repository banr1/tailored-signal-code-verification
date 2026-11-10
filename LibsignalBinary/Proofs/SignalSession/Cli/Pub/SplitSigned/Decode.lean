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
# Instruction Decodes for `signal_session::public::split_signed`

Decode lemmas `ssgDec_0` through `ssgDec_356` covering all 90 instructions (360 bytes) of
`signal_session::public::split_signed`.
-/

@[expose] public section

namespace CryptoVerification.SignalSession.Cli.SplitSigned.Helpers

open Arm64 ProofLib CryptoVerification.SignalSession.Cli

gen_decodes libsignalSessionCode_tree ssgDec
  [(ls_off% "libsignal_cli::public::split_signed") →
    (ls_off% "libsignal_cli::public::split_signed" + 356)]

end CryptoVerification.SignalSession.Cli.SplitSigned.Helpers
