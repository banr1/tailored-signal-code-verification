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
# Instruction Decode Tree for `spqr::decode_state` (`0x5349c..0x54040`, 745 insns)

**Checked by Lean.**
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.DecodeState

open Arm64 ProofLib ProofLib.ProgramReflection

/-- Symbol name for `spqr::decode_state` (`0x5349c`, 745 insns, 2980 bytes). -/
def decodeStateName : String :=
  "spqr::decode_state"

@[simp, arm64_norm]
theorem decodeState_fnOff :
    libsignalSessionCode.fnOff decodeStateName = 0x4e0a4 :=
  libsignalSessionCode_fnOff_0x4e0a4

gen_decodes libsignalSessionCode_tree decodeStateBin [ 0x4e0a4 → 0x4ec48 ]

end CryptoVerification.SpqrV1.Top.DecodeState
