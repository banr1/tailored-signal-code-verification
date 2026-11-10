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
# CLI `Epoch::encoded_len` and `Chain::encoded_len` Instruction Decode Tables

Generates `fnOff` and instruction decode lemmas for CLI `Epoch::encoded_len [local#3]` and
`Chain::encoded_len [local#3]`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.ProtoRepr

open Arm64 ProofLib.ProgramReflection

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.epochEncodedLenLocal1_fnOff :
    libsignalSessionCode.fnOff
      "<spqr::proto::pq_ratchet::chain::Epoch as prost::message::Message>::encoded_len [local#3]" = (ls_off% "<spqr::proto::pq_ratchet::chain::Epoch as prost::message::Message>::encoded_len [local#3]") :=
  (ls_lemma% fnOff "<spqr::proto::pq_ratchet::chain::Epoch as prost::message::Message>::encoded_len [local#3]")

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.chainEncodedLenLocal1_fnOff :
    libsignalSessionCode.fnOff
      "<spqr::proto::pq_ratchet::Chain as prost::message::Message>::encoded_len [local#3]" = (ls_off% "<spqr::proto::pq_ratchet::Chain as prost::message::Message>::encoded_len [local#3]") :=
  (ls_lemma% fnOff "<spqr::proto::pq_ratchet::Chain as prost::message::Message>::encoded_len [local#3]")

gen_decodes libsignalSessionCode_tree spqrEpochEncLenBinCli [(ls_off% "<spqr::proto::pq_ratchet::chain::Epoch as prost::message::Message>::encoded_len [local#3]" + 0) → (ls_off% "<spqr::proto::pq_ratchet::chain::Epoch as prost::message::Message>::encoded_len [local#3]" + 396), (ls_off% "<spqr::proto::pq_ratchet::chain::Epoch as prost::message::Message>::encoded_len [local#3]" + 404) → (ls_off% "<spqr::proto::pq_ratchet::chain::Epoch as prost::message::Message>::encoded_len [local#3]" + 460)]

gen_decodes libsignalSessionCode_tree spqrChainEncLenBinCli [(ls_off% "<spqr::proto::pq_ratchet::Chain as prost::message::Message>::encoded_len [local#3]" + 0) → (ls_off% "<spqr::proto::pq_ratchet::Chain as prost::message::Message>::encoded_len [local#3]" + 404), (ls_off% "<spqr::proto::pq_ratchet::Chain as prost::message::Message>::encoded_len [local#3]" + 420) → (ls_off% "<spqr::proto::pq_ratchet::Chain as prost::message::Message>::encoded_len [local#3]" + 464)]

end CryptoVerification.SpqrV1.ProtoRepr
