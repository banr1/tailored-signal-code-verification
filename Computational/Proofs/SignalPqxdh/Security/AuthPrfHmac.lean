/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthPrfHmacHA2
public import Computational.Proofs.SpecLemmas.Pqxdh.Security.BoundProofDefs
import Computational.Proofs.SignalPqxdh.Security.AuthPrfHmacHB
import Computational.Proofs.SignalPqxdh.Security.AuthPrfHmacHC
import Computational.Proofs.SignalPqxdh.Security.AuthPrfHmacHD
import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5M1

/-!
# PQXDH authentication: first-message MAC to `PrfHmac`

Bounds the multi-key INT-CTXT advantage of `aeadMuIntReductionAuth S b A` by the `PrfHmac`
advantage of `prfHmacReductionAuth S b A` plus `N_recv_tot / 2^64`.
-/

@[expose] public section

set_option autoImplicit false

open OracleSpec OracleComp MeasureTheory ENNReal BigOperators

namespace SignalPqxdh.Security

open SignalPqxdh

/-- Multi-key INT-CTXT to `PrfHmac` bound for any bounded, semantically MAC-input disciplined `B`. -/
theorem aeadMuIntCtxt_le_prfHmacOfMu_of_disciplined' (P : Primitives) (hP : WellFormedPrimitivesδ P)
    (B : AeadMuIntCtxtAdv) (hBd : B.Bounded) (Good : Bytes → Bool) (hGood : MacAdGood Good)
    (hGG : ∀ ad, Good ad = true → goodFirstMsgAD ad = true)
    (hDisc : MacInputDisciplined' P Good B) :
    AeadMuIntCtxt P B ≤
      ((B.q_enc + B.q_dec : ℕ) : ℝ) * PrfHmacReal P (prfHmacOfMu B) + (B.q_dec : ℝ) / (2 : ℝ) ^ 64 :=
  aeadMuIntCtxt_le_of_gHybrids P B _
    (fun h0 => (aeadMuIntCtxt_zero P B hBd h0).trans (by positivity))
    (aeadMuIntCtxt_le_gProb_allReal' P hP B Good hGood hGG hDisc)
    (fun m D _ hD => gProb_unif_le_hmac P hP B m D hD)
    (fun j => gProb_rf_eq_unif P B j)
    (fun hN => gProb_last_le P B hBd hN)

theorem aeadMuIntCtxt_le_prfHmac_of_pow8BaseLen (S : Setup) (P : Primitives)
    (hP : WellFormedPrimitivesδ P)
    (hLaw : ∀ p e, P.pow8 p = P.pow8 (P.x25519Base e) → p.length = 32)
    (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    AeadMuIntCtxt P (aeadMuIntReductionAuth S b A) ≤
      (S.N_sess_tot : ℝ) * PrfHmacReal P (prfHmacReductionAuth S b A) +
        (S.N_recv_tot : ℝ) / (2 : ℝ) ^ 64 :=
  aeadMuIntCtxt_le_prfHmacOfMu_of_disciplined' P hP _ (aeadMuIntReductionAuth_bounded S b A)
    goodFirstMsgAD macAdGood_goodFirstMsgAD (fun _ h => h)
    (aeadMuIntReductionAuth_disciplined S P hP hLaw b A)

/-- Bounds the multi-key INT-CTXT advantage of `aeadMuIntReductionAuth` by `PrfHmacReal` of
    `prfHmacReductionAuth`. -/
theorem aeadMuIntCtxt_le_prfHmac (S : Setup) (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    AeadMuIntCtxt P (aeadMuIntReductionAuth S b A) ≤
      2 * (S.N_sess_tot : ℝ) * PrfHmacReal P (prfHmacReductionAuth S b A) +
        (S.N_recv_tot : ℝ) / (2 : ℝ) ^ 64 := by
  have hLaw : ∀ p e, P.pow8 p = P.pow8 (P.x25519Base e) → p.length = 32 := hP.pow8_base_len
  have h := aeadMuIntCtxt_le_prfHmac_of_pow8BaseLen S P hP.toWellFormedPrimitivesδ hLaw b A
  have h0 : 0 ≤ PrfHmacReal P (prfHmacReductionAuth S b A) := ENNReal.toReal_nonneg
  have hN : (0 : ℝ) ≤ S.N_sess_tot := Nat.cast_nonneg _
  nlinarith [mul_nonneg hN h0]

end SignalPqxdh.Security
