/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthPrfHmacC
public import Computational.Proofs.SpecLemmas.Pqxdh.Security.BoundProofDefs

/-!
# PQXDH authentication: hybrid probabilities and assembly

Defines the generic hybrid acceptance probability `gProb` and assembles the multi-key INT-CTXT to
`PrfHmac` bound from the four hybrid steps.
-/

@[expose] public section

set_option autoImplicit false

open OracleSpec OracleComp MeasureTheory ENNReal BigOperators

namespace SignalPqxdh.Security

open SignalPqxdh
open RoKem

/-- Probability that the generic hybrid outputs `true` against `PrfHmac` oracle `b`. -/
noncomputable def gProb (P : Primitives) (b : Bool) (defer : ℕ → Prop) [DecidablePred defer]
    (tag : ℕ → Bytes → OracleComp PrfHmacSimSpec Bytes) (B : AeadMuIntCtxtAdv) : ℝ :=
  (𝒟[do
    let k ← sampleBytes32
    let (z, _) ← (simulateQ (prfFullImpl P b k) (gAfter defer tag B)).run []
    return z] {true}).toReal

theorem prfW_eq_gProb (P : Primitives) (b : Bool) (B : AeadMuIntCtxtAdv) (j : ℕ) :
    (𝒟[prfW P b B j] {true}).toReal = gProb P b (fun r => r ≤ j) (prfHmacTagQ j) B := by
  unfold prfW gProb
  rw [prfAfterRun_eq_gAfter]

/-- Assembles the multi-key INT-CTXT to `PrfHmac` bound from the four generic hybrid steps. -/
theorem aeadMuIntCtxt_le_of_gHybrids (P : Primitives) (B : AeadMuIntCtxtAdv) (q : ℝ)
    (hzero : B.q_enc + B.q_dec = 0 → AeadMuIntCtxt P B ≤ q)
    (hA : AeadMuIntCtxt P B ≤ gProb P false (fun _ => False) unifTag B)
    (hB : ∀ (m : ℕ) (D : ℕ → Prop) [DecidablePred D], (∀ r, D r ↔ r < m) →
      gProb P false D unifTag B ≤ gProb P true (fun r => r ≤ m) (prfHmacTagQ m) B)
    (hC : ∀ j, gProb P false (fun r => r ≤ j) (prfHmacTagQ j) B =
      gProb P false (fun r => r ≤ j) unifTag B)
    (hD : 0 < B.q_enc + B.q_dec →
      gProb P false (fun r => r ≤ B.q_enc + B.q_dec - 1) unifTag B ≤ q) :
    AeadMuIntCtxt P B ≤ ((B.q_enc + B.q_dec : ℕ) : ℝ) * PrfHmacReal P (prfHmacOfMu B) + q := by
  refine aeadMuIntCtxt_le_of_hybrids P B q hzero (fun _ => ?_) (fun j _ => ?_) (fun hN => ?_)
  · rw [prfW_eq_gProb]
    exact hA.trans (hB 0 (fun _ => False) (fun r => by simp))
  · rw [prfW_eq_gProb, prfW_eq_gProb, hC]
    exact hB (j + 1) (fun r => r ≤ j) (fun r => Nat.lt_succ_iff.symm)
  · rw [prfW_eq_gProb, hC]
    exact hD hN

end SignalPqxdh.Security
