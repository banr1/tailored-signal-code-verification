/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import VCVio.Prelude.Core

/-!
# Decoded machine instructions for `<signal_session::stores::Dir>::get`
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Get.Helpers


gen_decodes CryptoVerification.libsignalSessionCode_tree dirGetBin
  [(ls_off% "<libsignal_cli::stores::Dir>::get") →
   (ls_off% "<libsignal_cli::stores::Dir>::get" + 520)]

end CryptoVerification.SignalSession.Cli.Get.Helpers
