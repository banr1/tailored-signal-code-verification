/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Auth1KeyStatements
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthG0G3
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthAssembly
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3G3
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3E
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3H
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthPrfHmac
public import Computational.Proofs.SignalPqxdh.Delta.Auth1KeyHop

/-!
# Conditional assembly of the one-key `Auth` bound

Assembles the one-key authentication hop chain `G0 → G3 → G3.5 → G3.6 → G3.7 → G3.8 → G5` into
`PqxdhAuth1KeyReductionBoundδ`, parameterized by the signature hop, the `G3 → G3.5` Gap-DH cutoff
hop, and shallow-to-costed simulator advantage transfers.
-/

@[expose] public section

open scoped ENNReal
open MeasureTheory
open OracleSpec OracleComp
open SignalPqxdh SignalPqxdh.Security Proofs.SignalPqxdh.Security
open SignalPqxdh.Security.AuthSubHops1to3

namespace Proofs.SignalPqxdh.Security.PqxdhDelta

/-- One-key `Auth` reduction bound from the signature hop `hSig`, abstract `G3 → G3.5` hop `hH3`,
and simulator advantage transfers. -/
theorem pqxdh_auth1Key_bound_of_hops (S : Setup) (R : Auth1KeyReductionFamily S)
    (hSig : ∀ (P : Primitives), CryptoWellFormedPrimitivesδ P →
      ∀ (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b),
        |(𝒟[authExpG0_1WithProvFrozen1Key (checkBundleProvenance P) S P A.1].boolBias).toReal -
         (𝒟[authExpG1WithProvFrozen1Key (checkBundleProvenanceExact P) S P A.1].boolBias).toReal|
          ≤ (S.N_id : ℝ) * GapSigEufCmaReal P P.isValidDhTriple (R.sig b A))
    (hH3 : ∀ (P : Primitives), CryptoWellFormedPrimitivesδ P →
      ∀ (δ : ℝ), KemDeltaCorrectReal P δ →
      ∀ (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b),
        |authFixedAdvG3_1Key S P A.1 - authFixedAdvG3_5_1Key S P A.1| ≤
          2 * ((S.N_spk_tot : ℝ) * ((S.N_id : ℝ) + (S.N_send_tot : ℝ)) +
            (S.N_id : ℝ) * (S.N_send_tot : ℝ) +
            (S.N_opk_tot : ℝ) * (S.N_send_opk_tot : ℝ)) *
            GapDhWithSignReal P P.isValidDhTriple P.pow8 (R.gdh b A) +
          2 * (S.N_send_tot : ℝ) * (S.N_recv_tot : ℝ) / (2 : ℝ) ^ 250 +
          kemDecapsFailureTermReal S δ)
    (hShCr : ∀ (P : Primitives) (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b),
      KemShCr P (shcrReductionAuth1Key S b A) ≤ KemShCr P (R.shcr b A))
    (hCk : ∀ (P : Primitives) (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b),
      PrfChainKey P (prfCkReductionAuthFixed1Key S b A) ≤ PrfChainKey P (R.ck b A))
    (hMk : ∀ (P : Primitives) (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b),
      PrfMsgKeys P (prfMsgKeysReductionAuthFixed1Key S b A) ≤ PrfMsgKeys P (R.mk b A))
    (hCpa : ∀ (P : Primitives) (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b),
      AeadIndCpa P (aeadCpaReductionAuthFixed1Key S b A) ≤ AeadIndCpa P (R.cpa b A))
    (hInt : ∀ (P : Primitives) (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b),
      PrfHmac P (prfHmacReductionAuth1Key S b A) ≤ PrfHmac P (R.int b A)) :
    PqxdhAuth1KeyReductionBoundδ S R := by
  intro P hP δ hδ b A
  have hd : min δ 1 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right δ 1)
  have h03 := auth1Key_hop_G0_G3_le S P hP b A _ (hSig P hP b A)
  have h335 := hH3 P hP (min δ 1).toReal hδ.min_one_real b A
  have h3536 := _root_.SignalPqxdh.Security.hop_G3_5_G3_6_1Key S P hP b A
  have h3637 := hop_G3_6_G3_7_1Key S P hP b A
  have h3738 := hop_G3_7_G3_8_1Key S P hP b A
  have h385 := (authSubHops4to5Bundle1Key S).hop_G3_8_G5 P hP b A
  have hIntR := aeadMuIntCtxt_le_prfHmac1Key S P hP b A
  have hG5 := authFixedAdvG5_eq_zero1Key S P A.1
  have hNonneg : 0 ≤ Auth1KeyAdvantageReal S P A.1 := ENNReal.toReal_nonneg
  have htri1 := abs_sub_le (Auth1KeyAdvantageReal S P A.1) (authFixedAdvG3_1Key S P A.1)
    (authFixedAdvG5_1Key S P A.1)
  have htri2 := abs_sub_le (authFixedAdvG3_1Key S P A.1) (authFixedAdvG3_5_1Key S P A.1)
    (authFixedAdvG5_1Key S P A.1)
  have htri3 := abs_sub_le (authFixedAdvG3_5_1Key S P A.1) (authFixedAdvG3_6_1Key S P A.1)
    (authFixedAdvG5_1Key S P A.1)
  have htri4 := abs_sub_le (authFixedAdvG3_6_1Key S P A.1) (authFixedAdvG3_7_1Key S P A.1)
    (authFixedAdvG5_1Key S P A.1)
  have htri5 := abs_sub_le (authFixedAdvG3_7_1Key S P A.1) (authFixedAdvG3_8_1Key S P A.1)
    (authFixedAdvG5_1Key S P A.1)
  have hAbs0 : |Auth1KeyAdvantageReal S P A.1 - authFixedAdvG5_1Key S P A.1| =
      Auth1KeyAdvantageReal S P A.1 := by
    rw [hG5, sub_zero, abs_of_nonneg hNonneg]
  have hN0 : (0 : ℝ) ≤ S.N_spk_tot := Nat.cast_nonneg _
  have hN1 : (0 : ℝ) ≤ S.N_send_tot := Nat.cast_nonneg _
  have tShCr : (S.N_spk_tot : ℝ) * (S.N_send_tot : ℝ) * KemShCrReal P (shcrReductionAuth1Key S b A) ≤
      (S.N_spk_tot : ℝ) * (S.N_send_tot : ℝ) * KemShCrReal P (R.shcr b A) :=
    mul_le_mul_of_nonneg_left (ENNReal.toReal_mono (KemShCr_ne_top _ _) (hShCr P b A))
      (mul_nonneg hN0 hN1)
  have tCk : 2 * (S.N_sess_tot : ℝ) * PrfChainKeyReal P (prfCkReductionAuthFixed1Key S b A) ≤
      2 * (S.N_sess_tot : ℝ) * PrfChainKeyReal P (R.ck b A) :=
    mul_le_mul_of_nonneg_left (ENNReal.toReal_mono (PrfChainKey_ne_top _ _) (hCk P b A))
      (by positivity)
  have tMk : 2 * (S.N_sess_tot : ℝ) * PrfMsgKeysReal P (prfMsgKeysReductionAuthFixed1Key S b A) ≤
      2 * (S.N_sess_tot : ℝ) * PrfMsgKeysReal P (R.mk b A) :=
    mul_le_mul_of_nonneg_left (ENNReal.toReal_mono (PrfMsgKeys_ne_top _ _) (hMk P b A))
      (by positivity)
  have tCpa : 2 * (S.N_send_tot : ℝ) * AeadIndCpaReal P (aeadCpaReductionAuthFixed1Key S b A) ≤
      2 * (S.N_send_tot : ℝ) * AeadIndCpaReal P (R.cpa b A) :=
    mul_le_mul_of_nonneg_left (ENNReal.toReal_mono (AeadIndCpa_ne_top _ _) (hCpa P b A))
      (by positivity)
  have tInt : 2 * (S.N_sess_tot : ℝ) * PrfHmacReal P (prfHmacReductionAuth1Key S b A) ≤
      2 * (S.N_sess_tot : ℝ) * PrfHmacReal P (R.int b A) :=
    mul_le_mul_of_nonneg_left (ENNReal.toReal_mono (PrfHmac_ne_top _ _) (hInt P b A))
      (by positivity)
  have hSendColl : (0 : ℝ) ≤ ((S.N_send_tot * (S.N_send_tot - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 251 := by
    positivity
  have hCollSplit : ((S.N_dh * (S.N_dh - 1) + S.N_send_tot * (S.N_send_tot - 1) : ℕ) : ℝ) /
      (2 : ℝ) ^ 251 = ((S.N_dh * (S.N_dh - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 251 +
        ((S.N_send_tot * (S.N_send_tot - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 251 := by
    push_cast; ring
  have hReal : (Auth1KeyAdvantage S P A.1).toReal ≤
      pqxdhAuthAdvantageBoundδReal S b.q_roRoot (min δ 1).toReal
        (GapSigEufCma P P.isValidDhTriple (R.sig b A)).toReal
        (KemShCr P (R.shcr b A)).toReal
        (GapDhWithSign P P.isValidDhTriple P.pow8 (R.gdh b A)).toReal
        (PrfChainKey P (R.ck b A)).toReal
        (PrfMsgKeys P (R.mk b A)).toReal
        (AeadIndCpa P (R.cpa b A)).toReal
        (PrfHmac P (R.int b A)).toReal := by
    clear hSig hH3 hShCr hCk hMk hCpa hInt
    simp only [authSubHops4to5Bundle1Key, authSubHops4to5Bundle_of_int1Key] at h385
    simp only [Auth1KeyAdvantageReal, GapSigEufCmaReal, KemShCrReal, GapDhWithSignReal,
      PrfChainKeyReal, PrfMsgKeysReal, AeadIndCpaReal, PrfHmacReal] at *
    unfold pqxdhAuthAdvantageBoundδReal pqxdhAuthBoundReal pqxdhKeyIndBoundReal
    rw [hCollSplit]
    set_option exponentiation.threshold 512 in
    linarith
  have hOfReal := ENNReal.ofReal_le_ofReal hReal
  rw [ENNReal.ofReal_toReal (Auth1KeyAdvantage_ne_top S P A.1),
    ofReal_pqxdhAuthAdvantageBoundδReal S b.q_roRoot hd
      (GapSigEufCma_ne_top P P.isValidDhTriple (R.sig b A))
      (KemShCr_ne_top P (R.shcr b A))
      (GapDhWithSign_ne_top P P.isValidDhTriple P.pow8 (R.gdh b A))
      (PrfChainKey_ne_top P (R.ck b A))
      (PrfMsgKeys_ne_top P (R.mk b A))
      (AeadIndCpa_ne_top P (R.cpa b A))
      (PrfHmac_ne_top P (R.int b A))] at hOfReal
  exact hOfReal.trans (pqxdhAuthAdvantageBoundδ_mono_δ (min_le_left δ 1))

/-- One-key `Auth` reduction bound conditional on the signature hop `hSig` and the Gap-DH
bad-event bound `hAny`. -/
theorem pqxdh_auth1Key_bound_of_sig_h3 (S : Setup) (R : Auth1KeyReductionFamily S)
    (hSig : ∀ (P : Primitives), CryptoWellFormedPrimitivesδ P →
      ∀ (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b),
        |(𝒟[authExpG0_1WithProvFrozen1Key (checkBundleProvenance P) S P A.1].boolBias).toReal -
         (𝒟[authExpG1WithProvFrozen1Key (checkBundleProvenanceExact P) S P A.1].boolBias).toReal|
          ≤ (S.N_id : ℝ) * GapSigEufCmaReal P P.isValidDhTriple (R.sig b A))
    (hAny : ∀ (P : Primitives), CryptoWellFormedPrimitivesδ P →
      ∀ (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b),
        (𝒟[runAuthFgLatchedSim1Key S P A.1 >>= fun x =>
          pure (badAuthFgAnyLatched P b.q_ro x.2.2)] {true}).toReal ≤
        ((S.N_spk_tot : ℝ) * ((S.N_id : ℝ) + (S.N_send_tot : ℝ)) +
          (S.N_id : ℝ) * (S.N_send_tot : ℝ) +
          (S.N_opk_tot : ℝ) * (S.N_send_opk_tot : ℝ)) *
          GapDhWithSignReal P P.isValidDhTriple P.pow8 (fgAuth1KeyGapDhAdv4 S b A))
    (hGdh : ∀ (P : Primitives) (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b),
      GapDhWithSign P P.isValidDhTriple P.pow8 (fgAuth1KeyGapDhAdv4 S b A) ≤
        GapDhWithSign P P.isValidDhTriple P.pow8 (R.gdh b A))
    (hShCr : ∀ (P : Primitives) (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b),
      KemShCr P (shcrReductionAuth1Key S b A) ≤ KemShCr P (R.shcr b A))
    (hCk : ∀ (P : Primitives) (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b),
      PrfChainKey P (prfCkReductionAuthFixed1Key S b A) ≤ PrfChainKey P (R.ck b A))
    (hMk : ∀ (P : Primitives) (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b),
      PrfMsgKeys P (prfMsgKeysReductionAuthFixed1Key S b A) ≤ PrfMsgKeys P (R.mk b A))
    (hCpa : ∀ (P : Primitives) (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b),
      AeadIndCpa P (aeadCpaReductionAuthFixed1Key S b A) ≤ AeadIndCpa P (R.cpa b A))
    (hInt : ∀ (P : Primitives) (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b),
      PrfHmac P (prfHmacReductionAuth1Key S b A) ≤ PrfHmac P (R.int b A)) :
    PqxdhAuth1KeyReductionBoundδ S R := by
  refine pqxdh_auth1Key_bound_of_hops S R hSig ?_ hShCr hCk hMk hCpa hInt
  intro P hP δ hδ b A
  have h := auth_hop_G3_G3_5_leδ1Key S P hP δ hδ b A (hAny P hP b A)
  have hc : (0 : ℝ) ≤ 2 * ((S.N_spk_tot : ℝ) * ((S.N_id : ℝ) + (S.N_send_tot : ℝ)) +
      (S.N_id : ℝ) * (S.N_send_tot : ℝ) + (S.N_opk_tot : ℝ) * (S.N_send_opk_tot : ℝ)) := by
    positivity
  have hG : GapDhWithSignReal P P.isValidDhTriple P.pow8 (fgAuth1KeyGapDhAdv4 S b A) ≤
      GapDhWithSignReal P P.isValidDhTriple P.pow8 (R.gdh b A) :=
    ENNReal.toReal_mono (GapDhWithSign_ne_top _ _ _ _) (hGdh P b A)
  have := mul_le_mul_of_nonneg_left hG hc
  linarith

/-- One-key `Auth` reduction bound for an evaluated costed family `R.eval`. -/
theorem pqxdh_auth1Key_bound_of_sig_h3_costed (S : Setup) (R : Auth1KeyCostedReductionFamily S)
    (hSig : ∀ (P : Primitives), CryptoWellFormedPrimitivesδ P →
      ∀ (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b),
        |(𝒟[authExpG0_1WithProvFrozen1Key (checkBundleProvenance P) S P A.1].boolBias).toReal -
         (𝒟[authExpG1WithProvFrozen1Key (checkBundleProvenanceExact P) S P A.1].boolBias).toReal|
          ≤ (S.N_id : ℝ) * GapSigEufCmaReal P P.isValidDhTriple (R.eval.sig b A))
    (hAny : ∀ (P : Primitives), CryptoWellFormedPrimitivesδ P →
      ∀ (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b),
        (𝒟[runAuthFgLatchedSim1Key S P A.1 >>= fun x =>
          pure (badAuthFgAnyLatched P b.q_ro x.2.2)] {true}).toReal ≤
        ((S.N_spk_tot : ℝ) * ((S.N_id : ℝ) + (S.N_send_tot : ℝ)) +
          (S.N_id : ℝ) * (S.N_send_tot : ℝ) +
          (S.N_opk_tot : ℝ) * (S.N_send_opk_tot : ℝ)) *
          GapDhWithSignReal P P.isValidDhTriple P.pow8 (fgAuth1KeyGapDhAdv4 S b A))
    (hGdh : ∀ (P : Primitives) (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b),
      GapDhWithSign P P.isValidDhTriple P.pow8 (fgAuth1KeyGapDhAdv4 S b A) ≤
        GapDhWithSign P P.isValidDhTriple P.pow8 (R.eval.gdh b A))
    (hShCr : ∀ (P : Primitives) (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b),
      KemShCr P (shcrReductionAuth1Key S b A) ≤ KemShCr P (R.eval.shcr b A))
    (hCk : ∀ (P : Primitives) (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b),
      PrfChainKey P (prfCkReductionAuthFixed1Key S b A) ≤ PrfChainKey P (R.eval.ck b A))
    (hMk : ∀ (P : Primitives) (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b),
      PrfMsgKeys P (prfMsgKeysReductionAuthFixed1Key S b A) ≤ PrfMsgKeys P (R.eval.mk b A))
    (hCpa : ∀ (P : Primitives) (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b),
      AeadIndCpa P (aeadCpaReductionAuthFixed1Key S b A) ≤ AeadIndCpa P (R.eval.cpa b A))
    (hInt : ∀ (P : Primitives) (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b),
      PrfHmac P (prfHmacReductionAuth1Key S b A) ≤ PrfHmac P (R.eval.int b A)) :
    PqxdhAuth1KeyReductionBoundδ S R.eval :=
  pqxdh_auth1Key_bound_of_sig_h3 S R.eval hSig hAny hGdh hShCr hCk hMk hCpa hInt

end Proofs.SignalPqxdh.Security.PqxdhDelta
