/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.LibsignalSessionCode -- shake: keep
import ProofLib.GenDecodes

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000

namespace CryptoVerification.E2E.Pqxdh

open Arm64 CryptoVerification ProofLib.ProgramReflection

gen_decodes libsignalSessionCode_tree keyPairFromPubPriv [0x3e81c → 0x3e9c4]
gen_decodes libsignalSessionCode_tree identityKeyPairTryFrom [0x287e8 → 0x2890c]
gen_decodes libsignalSessionCode_tree identityKeyTryFromSlice [0x2c614 → 0x2c71c]

end CryptoVerification.E2E.Pqxdh
