/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSignalMessage
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import VCVio.Prelude.Core

/-!
# Shared `bv_decide` Enum Constants for `MessageType`

Generates `MessageType.enumToBitVec` and companion lemmas in a single shared module so independent
proof files using `bv_decide` on `MessageType` can be imported together without colliding.
-/

@[expose] public section

namespace CryptoVerification.LibsignalSession

open CryptoGames.LibsignalSession

theorem messageType_bv_trigger (a b : MessageType) (h : a = b) : b = a := by
  exact h.symm

end CryptoVerification.LibsignalSession
