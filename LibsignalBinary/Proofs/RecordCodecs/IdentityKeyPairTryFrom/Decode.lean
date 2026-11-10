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

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.RecordCodecsBinary.IdentityKeyPairTryFrom.Helpers

open Arm64 ProofLib ProofLib.ProgramReflection CryptoVerification

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

gen_decodes libsignalSessionCode_tree ikpTryFromBin
  [(ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from") →
   (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from" + 936)]

end CryptoVerification.RecordCodecsBinary.IdentityKeyPairTryFrom.Helpers
