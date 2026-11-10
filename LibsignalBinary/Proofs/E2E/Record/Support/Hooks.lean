/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.NonVacProofs.AllocWitness
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import VCVio.Prelude.Core

/-!
# Token-free `RustAlloc` instance `A0` for `E2E.Record`

Token-free `RustAlloc` alias `A0` (`NonVacuityWitness.A₀`) parameterizing the `Record` proofs via
`AllocHooks A0 abs`.
-/

@[expose] public section

namespace CryptoVerification.E2E.Record

open CryptoVerification.RustHeap

/-- Token-free `RustAlloc` instance (`NonVacuityWitness.A₀`) with no private state or ownership tokens. -/
abbrev A0 : RustAlloc := CryptoVerification.LibsignalSession.NonVacuityWitness.A₀

end CryptoVerification.E2E.Record
