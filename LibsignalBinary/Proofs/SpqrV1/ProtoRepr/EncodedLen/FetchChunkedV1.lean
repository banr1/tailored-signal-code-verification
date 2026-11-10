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
# Instruction Decode Trees for Polynomial, Chunked, and `V1State` `encoded_len`

Generates cached `gen_decodes` instruction decode trees for `[local#1]` and `[local#2]` copies of
`PolynomialDecoder::encoded_len`, `PolynomialEncoder::encoded_len`,
`V1State.Chunked.{Ct1Sampled,HeaderSent}::encoded_len`, and `V1State::encoded_len`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.ProtoRepr

open Arm64 ProofLib.ProgramReflection

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

theorem polynomialDecoderEncodedLenLocal1_fnOff :
    libsignalSessionCode.fnOff
      "<spqr::proto::pq_ratchet::PolynomialDecoder as prost::message::Message>::encoded_len [local#1]" = 0x39f7c :=
  libsignalSessionCode_fnOff_0x39f7c

-- Decode lemmas for non-panic instructions of `PolynomialDecoder::encoded_len` (`+0x000..+0x0e4`):
gen_decodes libsignalSessionCode_tree spqrPolyDecBin [
  0x39f7c → 0x3a060,
  0x642fc → 0x643e0
]

-- Decode lemmas for non-panic instructions of `PolynomialEncoder::encoded_len` (`+0x000..+0x10c`):
gen_decodes libsignalSessionCode_tree spqrPolyEncBin [
  0x38e70 → 0x38f7c,
  0x615f4 → 0x61700
]

-- Decode lemmas for non-panic instructions of `chunked::Ct1Sampled::encoded_len` (`+0x000..+0x108`):
gen_decodes libsignalSessionCode_tree spqrChunkedCt1SampledBin [
  0x39974 → 0x39a7c,
  0x63768 → 0x63870
]

-- Decode lemmas for non-panic instructions of `chunked::HeaderSent::encoded_len` (`+0x000..+0x108`):
gen_decodes libsignalSessionCode_tree spqrChunkedHeaderSentBin [
  0x3a0ac → 0x3a1b4,
  0x64b78 → 0x64c80
]

-- Decode lemmas for `V1State::encoded_len` (`+0x000..+0x66c`):
gen_decodes libsignalSessionCode_tree spqrV1StateBin [
  0x39110 → 0x3977c,
  0x62a00 → 0x6306c
]

end CryptoVerification.SpqrV1.ProtoRepr
