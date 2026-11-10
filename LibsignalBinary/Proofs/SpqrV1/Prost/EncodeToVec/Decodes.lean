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
# `PqRatchetState::encode_to_vec`: Instruction Decode Table

Pre-compiled `gen_decodes` instruction decode table for
`<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec`
(`0x6d010..0x6ee60`, 1,940 instructions).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Prost.EncodeToVec

open Arm64 ProofLib.ProgramReflection

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

abbrev spqrEncodeToVecOff : Nat := 0x67c18

gen_decodes libsignalSessionCode_tree spqrEncodeToVecBin
  [0x67c18 → 0x69a68]

end CryptoVerification.SpqrV1.Prost.EncodeToVec
