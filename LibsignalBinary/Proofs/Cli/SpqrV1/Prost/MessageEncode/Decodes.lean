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
# CLI SPQR V1 `MessageEncode` Instruction Decode Tables

Generates instruction decode lemmas for CLI `ChainParams`, `PolynomialDecoder`, `PolynomialEncoder`,
and `EpochDirection` message encoders and `PolynomialDecoder` / `PolynomialEncoder` length routines.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Prost.MessageEncode

open Arm64 ProofLib.ProgramReflection

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

gen_decodes libsignalSessionCode_tree libsignalSessionBinCli [(ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::ChainParams, alloc::vec::Vec<u8>> [local#3]" + 0) → (ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::ChainParams, alloc::vec::Vec<u8>> [local#3]" + 320), (ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialDecoder, alloc::vec::Vec<u8>> [local#3]" + 0) → (ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#3]" + 676)]

gen_decodes libsignalSessionCode_tree spqrPolyDecBinCli [(ls_off% "<spqr::proto::pq_ratchet::PolynomialDecoder as prost::message::Message>::encoded_len [local#3]" + 0) → (ls_off% "<spqr::proto::pq_ratchet::PolynomialDecoder as prost::message::Message>::encoded_len [local#3]" + 228)]

gen_decodes libsignalSessionCode_tree spqrPolyEncBinCli [(ls_off% "<spqr::proto::pq_ratchet::PolynomialEncoder as prost::message::Message>::encoded_len [local#3]" + 0) → (ls_off% "<spqr::proto::pq_ratchet::PolynomialEncoder as prost::message::Message>::encoded_len [local#3]" + 268)]

end CryptoVerification.SpqrV1.Prost.MessageEncode
