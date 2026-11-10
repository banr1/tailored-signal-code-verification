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
# Instruction Decode Trees for `Epoch::encoded_len` and `Chain::encoded_len`

Function offsets and cached `gen_decodes` instruction decode trees for both `[local#1]` and
`[local#2]` copies of `Epoch::encoded_len` (`0x38abc`, `0x664fc`) and `Chain::encoded_len`
(`0x39698`, `0x68790`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.ProtoRepr

open Arm64 ProofLib.ProgramReflection

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

theorem epochEncodedLenLocal1_fnOff :
    libsignalSessionCode.fnOff
      "<spqr::proto::pq_ratchet::chain::Epoch as prost::message::Message>::encoded_len [local#1]" = 0x38ba0 :=
  libsignalSessionCode_fnOff_0x38ba0

theorem epochEncodedLenLocal2_fnOff :
    libsignalSessionCode.fnOff
      "<spqr::proto::pq_ratchet::chain::Epoch as prost::message::Message>::encoded_len [local#2]" = 0x61104 :=
  libsignalSessionCode_fnOff_0x61104

theorem chainEncodedLenLocal1_fnOff :
    libsignalSessionCode.fnOff
      "<spqr::proto::pq_ratchet::Chain as prost::message::Message>::encoded_len [local#1]" = 0x3977c :=
  libsignalSessionCode_fnOff_0x3977c

theorem chainEncodedLenLocal2_fnOff :
    libsignalSessionCode.fnOff
      "<spqr::proto::pq_ratchet::Chain as prost::message::Message>::encoded_len [local#2]" = 0x63398 :=
  libsignalSessionCode_fnOff_0x63398

-- Non-panic instruction decode trees for `Epoch::encoded_len` (`0x38abc`, `0x664fc`).
gen_decodes libsignalSessionCode_tree spqrEpochEncLenBin [
  0x38ba0 → 0x38d2c, 0x38d34 → 0x38d6c,
  0x61104 → 0x61290, 0x61298 → 0x612d0
]

-- Non-panic instruction decode trees for `Chain::encoded_len` (`0x39698`, `0x68790`).
gen_decodes libsignalSessionCode_tree spqrChainEncLenBin [
  0x3977c → 0x39910, 0x39920 → 0x3994c,
  0x63398 → 0x6352c, 0x6353c → 0x63568
]

end CryptoVerification.SpqrV1.ProtoRepr
