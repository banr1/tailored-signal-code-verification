/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Composition.StatementModel
import Computational.Proofs.E2E.Dsl.M4AtomicWitness

/-!
# Lemma 3: multi-session composition with costed reductions

Proves `ModelSecure S ℓ` by instantiating `CompositionCostedReductionFamily` with the atomic
`ReductionDsl` reductions of `modelSecure_atomic`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.E2E

open Computational.Proofs.E2E.Dsl.M4AtomicWitness (modelSecure_atomic)

/-- Multi-session composition security (`ModelSecure S ℓ`) with costed reductions. -/
theorem model_secure_costed_proof {Pt : Type}
    (S : SignalPqxdh.Setup) (ℓ : ℕ) :
    ModelSecure (Pt := Pt) S ℓ :=
  modelSecure_atomic S ℓ

end CryptoVerification.E2E
