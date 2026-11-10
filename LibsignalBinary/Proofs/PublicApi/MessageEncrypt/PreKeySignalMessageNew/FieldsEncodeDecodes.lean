/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.LibsignalSessionCode -- shake: keep
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import ProofLib.GenDecodes
import VCVio.Prelude.Core

/-!
# Instruction Decode Lemmas for `PreKeySignalMessage::new` Field Encoding

Kernel-checked decode lemmas for the 154 instructions of the field-encoding segment
`+0x25c..+0x4c4` (`0x1538c..0x155f0`) of `PreKeySignalMessage::new`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncode

open Arm64 ProofLib ProofLib.ProgramReflection

gen_decodes libsignalSessionCode_tree preKeyMsgNewBin [0x1538c → 0x155f0]

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncode
