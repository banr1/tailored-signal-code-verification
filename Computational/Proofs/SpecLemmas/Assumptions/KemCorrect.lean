/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Assumptions.KemCorrect
public import Computational.Proofs.SpecLemmas.SignalPqxdh.Assumptions

@[expose] public section

set_option autoImplicit false

/-!
# Companion lemmas for KEM correctness

**Checked by Lean.** Basic lemmas on honest KEM failure and encapsulation accompanying
`Computational/Specifications/Assumptions/KemCorrect.lean`.
-/

namespace SignalPqxdh

open OracleComp OracleSpec ENNReal

/-- Under perfect correctness the honest failure event never happens. -/
theorem kemHonestFail_eq_false_of_kem_corr {P : Primitives}
    (hCorr : ∀ seed r ss ct, P.kemEncaps (P.kemKeyGen seed).1 r = some (ss, ct) →
      P.kemDecaps (P.kemKeyGen seed).2 ct = some ss)
    (seed r : Bytes) : kemHonestExchangeFails P seed r = false := by
  unfold kemHonestExchangeFails
  cases hEnc : P.kemEncaps (P.kemKeyGen seed).1 r with
  | none => rfl
  | some p =>
    obtain ⟨ss, ct⟩ := p
    simp [hCorr seed r ss ct hEnc]

/-- Honest KEM public keys produced by `kemKeyGen` encapsulate on every 32-byte coin vector. -/
theorem WellFormedPrimitivesδ.kemKeyGen_encaps_isSome {P : Primitives}
    (hWF : WellFormedPrimitivesδ P) (seed r : Bytes) (hr : r.length = 32) :
    (P.kemEncaps (P.kemKeyGen seed).1 r).isSome = true :=
  hWF.kemEncaps_isSome (P.kemKeyGen seed).1 r (hWF.kemKeyGen_valid seed).1 hr

end SignalPqxdh
