/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

/-!
# Relocatable Block Indices for `Epoch::encoded_len` and `Chain::encoded_len`

Defines CLI block index constants `478` (`Epoch::encoded_len [local#3]`) and `485`
(`Chain::encoded_len [local#3]`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.SpqrV1.ProtoRepr

/-- Block index `478`: `<spqr::proto::pq_ratchet::chain::Epoch as prost::message::Message>::encoded_len [local#3]` (121 insns, 484B). -/
abbrev epochEncodedLenLocal1BlkIdx : Nat := 478

/-- Block index `485`: `<spqr::proto::pq_ratchet::Chain as prost::message::Message>::encoded_len [local#3]` (126 insns, 504B). -/
abbrev chainEncodedLenLocal1BlkIdx : Nat := 485

end CryptoVerification.Cli.SpqrV1.ProtoRepr
