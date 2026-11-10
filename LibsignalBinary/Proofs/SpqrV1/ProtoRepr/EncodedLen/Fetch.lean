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
# Instruction Decode Trees for `V1State.Unchunked.*::encoded_len`

Generates cached `gen_decodes` instruction decode trees for both `[local#1]` and `[local#2]` copies
of the `59`-, `71`-, `82`-, and `93`-instruction `V1State.Unchunked.*::encoded_len` leaf
subroutines.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.ProtoRepr

open Arm64 ProofLib.ProgramReflection

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

theorem keysUnsampledEncodedLenLocal1_fnOff :
    libsignalSessionCode.fnOff
      "<spqr::proto::pq_ratchet::v1_state::unchunked::KeysUnsampled as prost::message::Message>::encoded_len [local#1]" = 0x38d84 :=
  libsignalSessionCode_fnOff_0x38d84

-- 59-insn group (`+0x000..+0x0c8`): `KeysUnsampled`, `NoHeaderReceived`, `Ct2Sent`.
gen_decodes libsignalSessionCode_tree spqrUnchunked59Bin [
  0x38d84 → 0x38e4c, 0x613cc → 0x61494,
  0x3a478 → 0x3a540, 0x6796c → 0x67a34,
  0x38a2c → 0x38af4, 0x5f2f0 → 0x5f3b8
]

-- 71-insn group (`+0x000..+0x0b8`, `+0x0bc..+0x0f8`): `EkSent`, `HeaderReceived`.
gen_decodes libsignalSessionCode_tree spqrUnchunked71Bin [
  0x3a1cc → 0x3a284, 0x3a288 → 0x3a2c4,
  0x64d94 → 0x64e4c, 0x64e50 → 0x64e8c,
  0x38fe0 → 0x39098, 0x3909c → 0x390d8,
  0x626c4 → 0x6277c, 0x62780 → 0x627bc
]

-- 82-insn group (`+0x000..+0x0b8`, `+0x0bc..+0x124`): `HeaderSent`, `EkSentCt1Received`.
gen_decodes libsignalSessionCode_tree spqrUnchunked82Bin [
  0x39e34 → 0x39eec, 0x39ef0 → 0x39f58,
  0x63eac → 0x63f64, 0x63f68 → 0x63fd0,
  0x3a330 → 0x3a3e8, 0x3a3ec → 0x3a454,
  0x67474 → 0x6752c, 0x67530 → 0x67598
]

-- 93-insn group (`+0x000..+0x0b8`, `+0x0bc..+0x150`): `Ct1Sent`, `Ct1SentEkReceived`.
gen_decodes libsignalSessionCode_tree spqrUnchunked93Bin [
  0x39a94 → 0x39b4c, 0x39b50 → 0x39be4,
  0x63948 → 0x63a00, 0x63a04 → 0x63a98,
  0x388b8 → 0x38970, 0x38974 → 0x38a08,
  0x5ed84 → 0x5ee3c, 0x5ee40 → 0x5eed4
]

end CryptoVerification.SpqrV1.ProtoRepr
