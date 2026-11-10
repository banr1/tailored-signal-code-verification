/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Assumptions.KemCorrect
import LibsignalBinary.Proofs.SpecLemmas.SignalPqxdh.ModelProofDefs

/-!
# PQXDH security proofs without perfect KEM correctness

**Checked by Lean.** Under DEV-PQ21, PQXDH security proofs assume `CryptoWellFormedPrimitivesδ P` or
`WellFormedPrimitivesδ P` wherever perfect KEM correctness (`kem_corr`) is not needed. This file
derives the arbitrary-length zero-output equivalence `WellFormedPrimitivesδ.x25519_zero_iff_any`.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh

/-- Arbitrary-length zero-output equivalence for `P.x25519` under `WellFormedPrimitivesδ`. -/
theorem WellFormedPrimitivesδ.x25519_zero_iff_any (P : Primitives) (hWF : WellFormedPrimitivesδ P)
    (a1 a2 pk : Bytes) (hpk : pk.length = 32) :
    P.x25519 a1 pk = List.replicate 32 0 ↔ P.x25519 a2 pk = List.replicate 32 0 := by
  rw [← hWF.x25519_clamp a1 pk, ← hWF.x25519_clamp a2 pk]
  exact hWF.x25519_zero_iff (clampScalar25519 a1) (clampScalar25519 a2) pk
    (clampScalar25519_length a1) (clampScalar25519_length a2) hpk

end SignalPqxdh
