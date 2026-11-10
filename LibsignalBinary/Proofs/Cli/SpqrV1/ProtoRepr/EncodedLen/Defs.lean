/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import VCVio.Prelude.Core

/-!
# CLI Unchunked `V1State` Sub-Message `encoded_len` Symbol Names

Defines CLI symbol-name abbreviations for the nine unchunked `v1_state::unchunked::*`
`Message::encoded_len [local#3]` routines.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.ProtoRepr





set_option maxRecDepth 200000

set_option maxHeartbeats 400000

namespace EncodedLen

end EncodedLen

open EncodedLen

abbrev _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.keysUnsampledEncodedLenLocal1Name : String :=
  "<spqr::proto::pq_ratchet::v1_state::unchunked::KeysUnsampled as prost::message::Message>::encoded_len [local#3]"

abbrev _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.noHeaderReceivedEncodedLenLocal1Name : String :=
  "<spqr::proto::pq_ratchet::v1_state::unchunked::NoHeaderReceived as prost::message::Message>::encoded_len [local#3]"

abbrev _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.ct2SentEncodedLenLocal1Name : String :=
  "<spqr::proto::pq_ratchet::v1_state::unchunked::Ct2Sent as prost::message::Message>::encoded_len [local#3]"

abbrev _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.ekSentEncodedLenLocal1Name : String :=
  "<spqr::proto::pq_ratchet::v1_state::unchunked::EkSent as prost::message::Message>::encoded_len [local#3]"

abbrev _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.headerReceivedEncodedLenLocal1Name : String :=
  "<spqr::proto::pq_ratchet::v1_state::unchunked::HeaderReceived as prost::message::Message>::encoded_len [local#3]"

abbrev _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.headerSentEncodedLenLocal1Name : String :=
  "<spqr::proto::pq_ratchet::v1_state::unchunked::HeaderSent as prost::message::Message>::encoded_len [local#3]"

abbrev _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.ekSentCt1ReceivedEncodedLenLocal1Name : String :=
  "<spqr::proto::pq_ratchet::v1_state::unchunked::EkSentCt1Received as prost::message::Message>::encoded_len [local#3]"

abbrev _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.ct1SentEncodedLenLocal1Name : String :=
  "<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent as prost::message::Message>::encoded_len [local#3]"

abbrev _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.ct1SentEkReceivedEncodedLenLocal1Name : String :=
  "<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1SentEkReceived as prost::message::Message>::encoded_len [local#3]"

end CryptoVerification.SpqrV1.ProtoRepr
