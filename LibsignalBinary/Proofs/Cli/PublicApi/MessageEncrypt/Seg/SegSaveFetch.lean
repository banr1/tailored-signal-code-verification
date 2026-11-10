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
# Instruction Decode Tables for `segSave`

Generates instruction decode tables for the `save_identity` blocks (`+0xbd4..+0xc08` and
`+0xd50..+0xd98`) of `signal_session_ratchet::encrypt` in the CLI image.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegSave

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoVerification.LibsignalPublicApi

/-! ## E8 and E10a (`+0xbd4..+0xc08`, `+0xd50..+0xd98`) -/

gen_decodes libsignalSessionCode_tree segSaveBinCli [(ls_off% "libsignal_cli_ratchet::encrypt" + 3028) → (ls_off% "libsignal_cli_ratchet::encrypt" + 3080)]

gen_decodes libsignalSessionCode_tree segSaveBinCli [(ls_off% "libsignal_cli_ratchet::encrypt" + 3408) → (ls_off% "libsignal_cli_ratchet::encrypt" + 3480)]

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegSave
