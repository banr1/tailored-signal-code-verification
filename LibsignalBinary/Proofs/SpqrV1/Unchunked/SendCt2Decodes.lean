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
# Instruction Decodes and Offsets for `Ct1SentEkReceived::send_ct2`

Isolates `gen_decodes`, `ls_off%`, and `ls_stub%` invocations for `Ct1SentEkReceived::send_ct2`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Unchunked

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification

set_option maxHeartbeats 800000 in
gen_decodes libsignalSessionCode_tree unchunkedSendCt2Bin [0x59008 → 0x59468]

end CryptoVerification.SpqrV1.Unchunked
