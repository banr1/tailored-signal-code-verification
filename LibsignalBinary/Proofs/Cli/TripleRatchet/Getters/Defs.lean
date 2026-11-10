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
# Symbol Definitions for CLI `drop_glue<Chain>`

Defines the CLI symbol name `dropChainName` for
`core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain>`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Getters



open CryptoVerification.LibsignalTripleRatchet

abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChainName : String :=
  "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#2]"

end CryptoVerification.LibsignalTripleRatchet.Getters
