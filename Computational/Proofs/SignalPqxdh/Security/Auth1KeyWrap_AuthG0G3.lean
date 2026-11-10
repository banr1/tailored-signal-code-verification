/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthGapDhHopB3

/-!
# One-Key `Auth` Hop `G0 → G3`

Bounds the advantage difference between the one-key `Auth` game and `G3` modulo an external bound
`hSig` on the signature hop `G0.1 → G1`, combining elliptic-curve and KEM key collisions with
`shcrReductionAuth1Key`.
-/

@[expose] public section

open scoped ENNReal
open MeasureTheory
open OracleSpec OracleComp
open SignalPqxdh SignalPqxdh.Security
namespace Proofs.SignalPqxdh.Security

theorem auth1Key_hop_G0_G2_1_exact_frozen_le (S : Setup) (P : Primitives)
    (hCWF : CryptoWellFormedPrimitivesδ P) (A : AuthAdversary S) (sigTerm : ℝ)
    (hSig : |(𝒟[authExpG0_1WithProvFrozen1Key (checkBundleProvenance P) S P A].boolBias).toReal -
      (𝒟[authExpG1WithProvFrozen1Key (checkBundleProvenanceExact P) S P A].boolBias).toReal| ≤
        sigTerm) :
    |Auth1KeyAdvantageReal S P A -
     (𝒟[authExpG2_1WithProvFrozen1Key (checkBundleProvenanceExact P) S P A].boolBias).toReal| ≤
      sigTerm +
      ((S.N_dh * (S.N_dh - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 251 +
      ((S.N_spk_tot * (S.N_spk_tot - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 256 := by
  have hG0 : Auth1KeyAdvantageReal S P A = (𝒟[authExpG0Frozen1Key S P A].boolBias).toReal := by
    unfold Auth1KeyAdvantageReal Auth1KeyAdvantage; rw [evalDist_pqxdhAuth1KeyExp_eq_G0Frozen1Key]
  rw [hG0]
  have h0 := auth_hop_G0_G0_1_frozen_le1Key S P hCWF A
  have h2 := auth_hop_kemColl_frozen_exact_le1Key S P hCWF A
  have ht1 := abs_sub_le ((𝒟[authExpG0Frozen1Key S P A].boolBias).toReal)
    ((𝒟[authExpG0_1WithProvFrozen1Key (checkBundleProvenance P) S P A].boolBias).toReal)
    ((𝒟[authExpG1WithProvFrozen1Key (checkBundleProvenanceExact P) S P A].boolBias).toReal)
  have ht2 := abs_sub_le ((𝒟[authExpG0Frozen1Key S P A].boolBias).toReal)
    ((𝒟[authExpG1WithProvFrozen1Key (checkBundleProvenanceExact P) S P A].boolBias).toReal)
    ((𝒟[authExpG2_1WithProvFrozen1Key (checkBundleProvenanceExact P) S P A].boolBias).toReal)
  set_option exponentiation.threshold 512 in
  linarith

/-- Bounds `|Auth1KeyAdvantageReal - authFixedAdvG3_1Key|` via `hSig`, collision bounds, and
`shcrReductionAuth1Key`. -/
theorem auth1Key_hop_G0_G3_le (S : Setup) (P : Primitives)
    (hCWF : CryptoWellFormedPrimitivesδ P) (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b)
    (sigTerm : ℝ)
    (hSig : |(𝒟[authExpG0_1WithProvFrozen1Key (checkBundleProvenance P) S P A.val].boolBias).toReal -
      (𝒟[authExpG1WithProvFrozen1Key (checkBundleProvenanceExact P) S P A.val].boolBias).toReal| ≤
        sigTerm) :
    |Auth1KeyAdvantageReal S P A.val - authFixedAdvG3_1Key S P A.val| ≤
      sigTerm +
      ((S.N_dh * (S.N_dh - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 251 +
      ((S.N_spk_tot * (S.N_spk_tot - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 256 +
      (S.N_spk_tot : ℝ) * (S.N_send_tot : ℝ) * KemShCrReal P (shcrReductionAuth1Key S b A) := by
  have h0_2_1 := auth1Key_hop_G0_G2_1_exact_frozen_le S P hCWF A.val sigTerm hSig
  have h2_1_3 := auth_hop_G2_1_exact_G3_le_prob1Key S P hCWF A.val
  have hShCrProb := badKemShCrProbAuth_g3_le1Key S P hCWF b A
  have hShCrRed := badKemShCrProbAuth_le_kemShCr1Key S P hCWF b A
  have htri := abs_sub_le (Auth1KeyAdvantageReal S P A.val)
    ((𝒟[authExpG2_1WithProvFrozen1Key (checkBundleProvenanceExact P) S P A.val].boolBias).toReal)
    (authFixedAdvG3_1Key S P A.val)
  set_option exponentiation.threshold 512 in
  linarith

end Proofs.SignalPqxdh.Security
