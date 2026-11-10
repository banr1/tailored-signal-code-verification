/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout

/-!
# CLI Polynomial, Chunked, and `V1State` `encoded_len` Instruction Decode Tables

Generates instruction decode lemmas for CLI `PolynomialDecoder`, `PolynomialEncoder`,
`chunked::Ct1Sampled`, `chunked::HeaderSent`, and `V1State` `encoded_len` routines.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.ProtoRepr

open Arm64 ProofLib.ProgramReflection

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.polynomialDecoderEncodedLenLocal1_fnOff :
    libsignalSessionCode.fnOff
      "<spqr::proto::pq_ratchet::PolynomialDecoder as prost::message::Message>::encoded_len [local#3]" = (ls_off% "<spqr::proto::pq_ratchet::PolynomialDecoder as prost::message::Message>::encoded_len [local#3]") :=
  (ls_lemma% fnOff "<spqr::proto::pq_ratchet::PolynomialDecoder as prost::message::Message>::encoded_len [local#3]")

-- Decode lemmas for non-panic instructions of `PolynomialDecoder::encoded_len` (`+0x000..+0x0e4`):

gen_decodes libsignalSessionCode_tree spqrPolyDecBinCli [(ls_off% "<spqr::proto::pq_ratchet::PolynomialDecoder as prost::message::Message>::encoded_len [local#3]" + 0) → (ls_off% "<spqr::proto::pq_ratchet::PolynomialDecoder as prost::message::Message>::encoded_len [local#3]" + 228)]

gen_decodes libsignalSessionCode_tree spqrPolyEncBinCli [(ls_off% "<spqr::proto::pq_ratchet::PolynomialEncoder as prost::message::Message>::encoded_len [local#3]" + 0) → (ls_off% "<spqr::proto::pq_ratchet::PolynomialEncoder as prost::message::Message>::encoded_len [local#3]" + 268)]

gen_decodes libsignalSessionCode_tree spqrChunkedCt1SampledBinCli [(ls_off% "<spqr::proto::pq_ratchet::v1_state::chunked::Ct1Sampled as prost::message::Message>::encoded_len [local#3]" + 0) → (ls_off% "<spqr::proto::pq_ratchet::v1_state::chunked::Ct1Sampled as prost::message::Message>::encoded_len [local#3]" + 264)]

gen_decodes libsignalSessionCode_tree spqrChunkedHeaderSentBinCli [(ls_off% "<spqr::proto::pq_ratchet::v1_state::chunked::HeaderSent as prost::message::Message>::encoded_len [local#3]" + 0) → (ls_off% "<spqr::proto::pq_ratchet::v1_state::chunked::HeaderSent as prost::message::Message>::encoded_len [local#3]" + 264)]

gen_decodes libsignalSessionCode_tree spqrV1StateBinCli [(ls_off% "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]" + 0) → (ls_off% "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]" + 1644)]

end CryptoVerification.SpqrV1.ProtoRepr
