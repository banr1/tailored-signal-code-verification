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

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.InImage.UuidTryParse

open Arm64 ProofLib ProofLib.ProgramReflection
  CryptoVerification.LibsignalTripleRatchet

abbrev decodeHex32Name : String := "uuid::parser::decode_hex32"
abbrev parserTryParseName : String := "uuid::parser::try_parse"

gen_decodes libsignalSessionCode_tree uuidTryParseBin [(ls_off% "<uuid::Uuid>::try_parse") → (ls_off% "<uuid::Uuid>::try_parse" + 92)]
gen_decodes libsignalSessionCode_tree decodeHex32Bin [(ls_off% "uuid::parser::decode_hex32") → (ls_off% "uuid::parser::decode_hex32" + 376)]
gen_decodes libsignalSessionCode_tree parserTryParseBin [(ls_off% "uuid::parser::try_parse") → (ls_off% "uuid::parser::try_parse" + 532)]

end CryptoVerification.LibsignalTripleRatchet.InImage.UuidTryParse
