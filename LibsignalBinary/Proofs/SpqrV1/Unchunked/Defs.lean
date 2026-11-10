/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout

@[expose] public section

namespace CryptoVerification.SpqrV1.Unchunked

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.CodeLayout

abbrev ct1SentFromPbName : String :=
  "<spqr::v1::unchunked::send_ct::Ct1Sent>::from_pb"

abbrev ekSentCt1ReceivedFromPbName : String :=
  "<spqr::v1::unchunked::send_ek::EkSentCt1Received>::from_pb"

abbrev ct1SentMergeName : String :=
  "prost::encoding::message::merge::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent, &mut &[u8]>"

abbrev ekSentCt1ReceivedMergeName : String :=
  "prost::encoding::message::merge::<spqr::proto::pq_ratchet::v1_state::unchunked::EkSentCt1Received, &mut &[u8]>"

@[simp, arm64_norm] theorem ct1SentFromPb_fnOff :
    libsignalSessionCode.fnOff ct1SentFromPbName = 0x58854 :=
  ls_lemma% fnOff "<spqr::v1::unchunked::send_ct::Ct1Sent>::from_pb"

@[simp, arm64_norm] theorem ekSentCt1ReceivedFromPb_fnOff :
    libsignalSessionCode.fnOff ekSentCt1ReceivedFromPbName = 0x5946c :=
  ls_lemma% fnOff "<spqr::v1::unchunked::send_ek::EkSentCt1Received>::from_pb"

@[simp, arm64_norm] theorem ct1SentMerge_fnOff :
    libsignalSessionCode.fnOff ct1SentMergeName = 0x4caa4 :=
  ls_lemma% fnOff "prost::encoding::message::merge::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent, &mut &[u8]>"

@[simp, arm64_norm] theorem ekSentCt1ReceivedMerge_fnOff :
    libsignalSessionCode.fnOff ekSentCt1ReceivedMergeName = 0x4c808 :=
  ls_lemma% fnOff "prost::encoding::message::merge::<spqr::proto::pq_ratchet::v1_state::unchunked::EkSentCt1Received, &mut &[u8]>"

gen_decodes libsignalSessionCode_tree ct1SentFromPbBin [0x58854 → 0x58a00]
gen_decodes libsignalSessionCode_tree ekSentCt1ReceivedFromPbBin [0x5946c → 0x595cc]
gen_decodes libsignalSessionCode_tree ct1SentMergeBin [0x4caa4 → 0x4cd74]
gen_decodes libsignalSessionCode_tree ekSentCt1ReceivedMergeBin [0x4c808 → 0x4caa0]

end CryptoVerification.SpqrV1.Unchunked
