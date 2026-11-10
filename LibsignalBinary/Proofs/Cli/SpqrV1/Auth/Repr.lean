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
# CLI SPQR V1 `Authenticator::encode [local#3]` Entry Symbol (`authEncodeLocal1Name`)
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Auth

open CryptoVerification

/-- `prost::encoding::message::encode::<spqr::proto::pq_ratchet::Authenticator, alloc::vec::Vec<u8>> [local#3]` (`147` instructions). -/
abbrev _root_.CryptoVerification.Cli.SpqrV1.Auth.authEncodeLocal1Name : String :=
  "prost::encoding::message::encode::<spqr::proto::pq_ratchet::Authenticator, alloc::vec::Vec<u8>> [local#3]"

end CryptoVerification.SpqrV1.Auth
