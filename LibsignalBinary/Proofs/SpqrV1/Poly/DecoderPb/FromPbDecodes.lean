/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.LibsignalSessionCode -- shake: keep
import ProofLib.GenDecodes

/-!
# Instruction Decode Trees for `<spqr::encoding::polynomial::PolyDecoder>::from_pb`

Pre-generated `gen_decodes` trees (`0x62b1c..0x63030`) isolated so downstream symbolic-execution
files avoid importing `libsignalSessionCode_tree`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Poly.DecoderPb

open Arm64 ProofLib ProofLib.ProgramReflection

gen_decodes libsignalSessionCode_tree spqrDecoderFromPbBin
  [0x5d724 → 0x5dc38]

@[simp, arm64_norm] theorem decoderFromPb_fnOff :
    libsignalSessionCode.fnOff "<spqr::encoding::polynomial::PolyDecoder>::from_pb" = 0x5d724 :=
  libsignalSessionCode_fnOff_0x5d724

end CryptoVerification.SpqrV1.Poly.DecoderPb
