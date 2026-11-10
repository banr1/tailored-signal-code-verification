/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import ProofLib.SepLogic.WPp
import VCVio.Prelude.Core

/-!
# CLI `StoreSession` Entry Symbol (`decWithStoresName`)
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.StoreSession

open Arm64 ProofLib

open CryptoVerification.LibsignalPublicApi

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- `session_message_decrypt_signal` (`(ls_off% "signal_session_ratchet::decrypt_signal")`). -/
abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.StoreSession.decWithStoresName : String := "libsignal_cli_ratchet::decrypt_signal"

end CryptoVerification.LibsignalPublicApi.StoreSession
