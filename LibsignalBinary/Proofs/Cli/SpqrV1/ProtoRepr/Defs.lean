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
# CLI `Epoch::encoded_len` and `Chain::encoded_len` Symbol Names

Defines CLI symbol-name abbreviations for `Epoch::encoded_len [local#3]` and
`Chain::encoded_len [local#3]`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.ProtoRepr






/-- CLI symbol name for `<spqr::proto::pq_ratchet::chain::Epoch as
prost::message::Message>::encoded_len [local#3]`. -/
abbrev _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.epochEncodedLenLocal1Name : String :=
  "<spqr::proto::pq_ratchet::chain::Epoch as prost::message::Message>::encoded_len [local#3]"

/-- CLI symbol name for `<spqr::proto::pq_ratchet::Chain as
prost::message::Message>::encoded_len [local#3]`. -/
abbrev _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.chainEncodedLenLocal1Name : String :=
  "<spqr::proto::pq_ratchet::Chain as prost::message::Message>::encoded_len [local#3]"

end CryptoVerification.SpqrV1.ProtoRepr
