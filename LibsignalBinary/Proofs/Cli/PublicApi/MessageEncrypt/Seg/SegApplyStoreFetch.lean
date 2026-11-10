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
# CLI `SegApplyStore` Instruction Decodes

Pre-decoded instruction tables for the `SegApplyStore` segment (`+0xd9c..+0xe88`) of
`session_message_encrypt_with_stores`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegApplyStore

open Arm64 ProofLib ProofLib.ProgramReflection


open CryptoVerification.LibsignalPublicApi

/-! ## Apply and Store Ranges (`+0xd9c..+0xe88`) -/

gen_decodes libsignalSessionCode_tree segApplyStoreBinCli [(ls_off% "libsignal_cli_ratchet::encrypt" + 3484) → (ls_off% "libsignal_cli_ratchet::encrypt" + 3556)]

gen_decodes libsignalSessionCode_tree segApplyStoreBinCli [(ls_off% "libsignal_cli_ratchet::encrypt" + 3560) → (ls_off% "libsignal_cli_ratchet::encrypt" + 3612), (ls_off% "libsignal_cli_ratchet::encrypt" + 3640) → (ls_off% "libsignal_cli_ratchet::encrypt" + 3716)]

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegApplyStore
