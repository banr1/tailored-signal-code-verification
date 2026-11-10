/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Pqxdh.Bound
public import Computational.Specifications.Pqxdh.Security.HeadlineDelta
public import Computational.Specifications.Pqxdh.Security.Auth.Headline
public import LibsignalBinary.Specifications.SignalPqxdh.Model
public import Computational.Specifications.Pqxdh.Game
public import Computational.Specifications.Assumptions.Assumptions
import VCVio.EvalDist.Monad.Basic
import VCVio.CryptoFoundations.SecExp.Measure

/-!
# Real-valued PQXDH bound projections and monotonicity lemmas

Real-valued (`ℝ`) projections of the `ℝ≥0∞` PQXDH advantage predicates and closed-form bounds,
together with `ENNReal.ofReal` bridge, comparison, and monotonicity lemmas for game-hop proofs.
-/

@[expose] public section

set_option autoImplicit false
namespace SignalPqxdh

open scoped ENNReal
open OracleComp OracleSpec MeasureTheory

/-- Reference deployment-scale replication parameters for numerical bound evaluation. -/
def deploymentSetup : Setup :=
  { N_id          := 2 ^ 20
    N_recv        := 32
    N_opk         := 32
    N_no_opk      := 32
    N_send_opk    := 512
    N_send_no_opk := 512 }

noncomputable def GapDhWithSignReal (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool) (pow8 : Bytes → Bytes)
    (A : GapDhWithSignAdv) : ℝ :=
  (GapDhWithSign P isValidDhTriple pow8 A).toReal

noncomputable def KemShCrReal (P : Primitives) (A : KemShCrAdv) : ℝ :=
  (KemShCr P A).toReal

noncomputable def GapSigEufCmaReal (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool) (A : GapSigEufCmaAdv) : ℝ :=
  (GapSigEufCma P isValidDhTriple A).toReal

noncomputable def KeyInd1KeyRoAdvantageReal (S : Setup) (P : Primitives)
    (A : KeyIndAdversary S) : ℝ :=
  (KeyInd1KeyRoAdvantage S P A).toReal

noncomputable def AeadIndCpaReal (P : Primitives) (A : AeadIndCpaAdv) : ℝ :=
  (AeadIndCpa P A).toReal

noncomputable def PrfHmacReal (P : Primitives) (A : PrfHmacAdv) : ℝ :=
  (PrfHmac P A).toReal

noncomputable def PrfChainKeyReal (P : Primitives) (A : PrfCkAdv) : ℝ :=
  (PrfChainKey P A).toReal

noncomputable def PrfMsgKeysReal (P : Primitives) (A : PrfMsgKeysAdv) : ℝ :=
  (PrfMsgKeys P A).toReal

noncomputable def AuthAdvantageReal (S : Setup) (P : Primitives) (A : AuthAdversary S) : ℝ :=
  (AuthAdvantage S P A).toReal

noncomputable def Auth1KeyAdvantageReal (S : Setup) (P : Primitives) (A : AuthAdversary S) : ℝ :=
  (Auth1KeyAdvantage S P A).toReal

/-- Real-valued KEM δ-correctness predicate. -/
def KemDeltaCorrectReal (P : Primitives) (δ : ℝ) : Prop :=
  (𝒟[do
    let seed ← sampleRandom64
    let r ← sampleCoins32
    pure (kemHonestExchangeFails P seed r)] {true}).toReal ≤ δ

theorem GapDhWithSign_ne_top (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool) (pow8 : Bytes → Bytes)
    (A : GapDhWithSignAdv) :
    GapDhWithSign P isValidDhTriple pow8 A ≠ ⊤ :=
  measure_ne_top _ {true}

theorem KemShCr_ne_top (P : Primitives) (A : KemShCrAdv) :
    KemShCr P A ≠ ⊤ :=
  measure_ne_top _ {true}

theorem GapSigEufCma_ne_top (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool) (A : GapSigEufCmaAdv) :
    GapSigEufCma P isValidDhTriple A ≠ ⊤ :=
  measure_ne_top _ {true}

theorem KeyInd1KeyRoAdvantage_ne_top (S : Setup) (P : Primitives) (A : KeyIndAdversary S) :
    KeyInd1KeyRoAdvantage S P A ≠ ⊤ :=
  Measure.boolBias_ne_top _

theorem AeadIndCpa_ne_top (P : Primitives) (A : AeadIndCpaAdv) :
    AeadIndCpa P A ≠ ⊤ :=
  Measure.boolBias_ne_top _

theorem PrfHmac_ne_top (P : Primitives) (A : PrfHmacAdv) :
    PrfHmac P A ≠ ⊤ :=
  Measure.boolBias_ne_top _

theorem PrfChainKey_ne_top (P : Primitives) (A : PrfCkAdv) :
    PrfChainKey P A ≠ ⊤ :=
  Measure.boolBias_ne_top _

theorem PrfMsgKeys_ne_top (P : Primitives) (A : PrfMsgKeysAdv) :
    PrfMsgKeys P A ≠ ⊤ :=
  Measure.boolBias_ne_top _

theorem AuthAdvantage_ne_top (S : Setup) (P : Primitives) (A : AuthAdversary S) :
    AuthAdvantage S P A ≠ ⊤ :=
  Measure.boolBias_ne_top _

theorem Auth1KeyAdvantage_ne_top (S : Setup) (P : Primitives) (A : AuthAdversary S) :
    Auth1KeyAdvantage S P A ≠ ⊤ :=
  Measure.boolBias_ne_top _

theorem prob_le_one_div_two_pow_of_toReal {p : ProbComp Bool} {k : ℕ}
    (h : (𝒟[p] {true}).toReal ≤ 1 / (2 : ℝ) ^ k) :
    𝒟[p] {true} ≤ 1 / (2 : ℝ≥0∞) ^ k := by
  rw [← ENNReal.ofReal_toReal (measure_ne_top 𝒟[p] {true})]
  refine (ENNReal.ofReal_le_ofReal h).trans_eq ?_
  rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_one,
    ENNReal.ofReal_pow (by norm_num) k, ENNReal.ofReal_ofNat]

theorem toReal_prob_le_one_div_two_pow {p : ProbComp Bool} {k : ℕ}
    (h : 𝒟[p] {true} ≤ 1 / (2 : ℝ≥0∞) ^ k) :
    (𝒟[p] {true}).toReal ≤ 1 / (2 : ℝ) ^ k := by
  have htop : (1 : ℝ≥0∞) / (2 : ℝ≥0∞) ^ k ≠ ⊤ :=
    ENNReal.div_ne_top ENNReal.one_ne_top (pow_ne_zero k (by norm_num))
  refine ((ENNReal.toReal_le_toReal (measure_ne_top 𝒟[p] {true}) htop).mpr h).trans_eq ?_
  rw [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_pow, ENNReal.toReal_ofNat]

theorem CryptoWellFormedPrimitivesδ.ec_coll_bound_real {P : Primitives}
    (hP : CryptoWellFormedPrimitivesδ P) (targetPk : Bytes) :
    (𝒟[do
      let sk ← sampleScalar32
      pure (P.pow8 (P.x25519Base sk) == P.pow8 targetPk)] {true}).toReal ≤
      1 / (2 : ℝ) ^ 250 :=
  toReal_prob_le_one_div_two_pow (hP.ec_coll_bound targetPk)

theorem CryptoWellFormedPrimitivesδ.kem_coll_bound_real {P : Primitives}
    (hP : CryptoWellFormedPrimitivesδ P) (targetPk : Bytes) :
    (𝒟[do let (pk, _) ← sampleKemKeyGen P; pure (pk == targetPk)] {true}).toReal ≤
      1 / (2 : ℝ) ^ 255 :=
  toReal_prob_le_one_div_two_pow (hP.kem_coll_bound targetPk)

theorem KemDeltaCorrect.min_one_real {P : Primitives} {δ : ℝ≥0∞} (hδ : KemDeltaCorrect P δ) :
    KemDeltaCorrectReal P (min δ 1).toReal := by
  have h1 : 𝒟[do
      let seed ← sampleRandom64
      let r ← sampleCoins32
      pure (kemHonestExchangeFails P seed r)] {true} ≤ 1 := prob_le_one
  have hmin : 𝒟[do
      let seed ← sampleRandom64
      let r ← sampleCoins32
      pure (kemHonestExchangeFails P seed r)] {true} ≤ min δ 1 := le_min hδ h1
  have htop : min δ 1 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right δ 1)
  exact (ENNReal.toReal_le_toReal (measure_ne_top _ {true}) htop).mpr hmin

/-- Real-valued closed-form PQXDH `KeyInd` bound matching `pqxdhKeyIndBound`. -/
noncomputable def pqxdhKeyIndBoundReal
    (S : Setup)
    (epsSig epsKemShCr epsGapDh : ℝ) : ℝ :=
  (S.N_id : ℝ) * epsSig +
  ((S.N_dh * (S.N_dh - 1) + S.N_send_tot * (S.N_send_tot - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 251 +
  (S.N_spk_tot : ℝ) * (S.N_send_tot : ℝ) * epsKemShCr +
  ((S.N_spk_tot * (S.N_spk_tot - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 256 +
  2 * ((S.N_spk_tot : ℝ) * ((S.N_id : ℝ) + (S.N_send_tot : ℝ)) +
    (S.N_id : ℝ) * (S.N_send_tot : ℝ) +
    (S.N_opk_tot : ℝ) * (S.N_send_opk_tot : ℝ)) * epsGapDh

theorem pqxdhKeyIndBound_ec_coll_le_old (S : Setup) :
    ((S.N_dh * (S.N_dh - 1) + S.N_send_tot * (S.N_send_tot - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 251 ≤
      ((S.N_dh : ℝ) ^ 2) / (2 : ℝ) ^ 250 := by
  have hSendDh : S.N_send_tot ≤ S.N_dh := by unfold Setup.N_dh; omega
  have hDh : S.N_dh * (S.N_dh - 1) ≤ S.N_dh ^ 2 := by
    rw [sq]; exact Nat.mul_le_mul_left _ (Nat.sub_le _ 1)
  have hSend : S.N_send_tot * (S.N_send_tot - 1) ≤ S.N_dh ^ 2 := by
    calc S.N_send_tot * (S.N_send_tot - 1)
        ≤ S.N_dh * (S.N_dh - 1) := Nat.mul_le_mul hSendDh (Nat.sub_le_sub_right hSendDh 1)
      _ ≤ S.N_dh ^ 2 := hDh
  have hEcNat : S.N_dh * (S.N_dh - 1) + S.N_send_tot * (S.N_send_tot - 1) ≤ 2 * S.N_dh ^ 2 := by
    omega
  have hEcReal :
      ((S.N_dh * (S.N_dh - 1) + S.N_send_tot * (S.N_send_tot - 1) : ℕ) : ℝ) ≤
        2 * (S.N_dh : ℝ) ^ 2 := by
    exact_mod_cast hEcNat
  rw [pow_succ' 2 250, div_mul_eq_div_div]
  exact div_le_div_of_nonneg_right (by linarith) (by positivity)

theorem pqxdhKeyIndBound_kem_coll_le_old (S : Setup) :
    ((S.N_spk_tot * (S.N_spk_tot - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 256 ≤
      ((S.N_spk_tot : ℝ) ^ 2) / (2 : ℝ) ^ 256 := by
  have hSpkNat : S.N_spk_tot * (S.N_spk_tot - 1) ≤ S.N_spk_tot ^ 2 := by
    rw [sq]; exact Nat.mul_le_mul_left _ (Nat.sub_le _ 1)
  have hSpkReal : ((S.N_spk_tot * (S.N_spk_tot - 1) : ℕ) : ℝ) ≤ (S.N_spk_tot : ℝ) ^ 2 := by
    exact_mod_cast hSpkNat
  exact div_le_div_of_nonneg_right hSpkReal (by positivity)

theorem pqxdhKeyIndBound_le_old_dh4 (S : Setup) (epsSig epsKemShCr epsGapDh : ℝ)
    (hGdh : 0 ≤ epsGapDh) :
    pqxdhKeyIndBoundReal S epsSig epsKemShCr epsGapDh ≤
      (S.N_id : ℝ) * epsSig +
      ((S.N_dh * (S.N_dh - 1) + S.N_send_tot * (S.N_send_tot - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 251 +
      (S.N_spk_tot : ℝ) * (S.N_send_tot : ℝ) * epsKemShCr +
      ((S.N_spk_tot * (S.N_spk_tot - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 256 +
      2 * ((S.N_spk_tot : ℝ) * ((S.N_id : ℝ) + (S.N_send_tot : ℝ)) +
        (S.N_id : ℝ) * (S.N_send_tot : ℝ) +
        (S.N_opk_tot : ℝ) * (S.N_send_tot : ℝ)) * epsGapDh := by
  unfold pqxdhKeyIndBoundReal
  have hSend : (S.N_send_opk_tot : ℝ) ≤ (S.N_send_tot : ℝ) := by
    exact_mod_cast (Nat.le_add_right S.N_send_opk_tot S.N_send_no_opk_tot :
      S.N_send_opk_tot ≤ S.N_send_tot)
  have hOpk : (0 : ℝ) ≤ (S.N_opk_tot : ℝ) := Nat.cast_nonneg _
  have hTerm5 :
      2 * ((S.N_spk_tot : ℝ) * ((S.N_id : ℝ) + (S.N_send_tot : ℝ)) +
        (S.N_id : ℝ) * (S.N_send_tot : ℝ) +
        (S.N_opk_tot : ℝ) * (S.N_send_opk_tot : ℝ)) * epsGapDh ≤
      2 * ((S.N_spk_tot : ℝ) * ((S.N_id : ℝ) + (S.N_send_tot : ℝ)) +
        (S.N_id : ℝ) * (S.N_send_tot : ℝ) +
        (S.N_opk_tot : ℝ) * (S.N_send_tot : ℝ)) * epsGapDh := by
    nlinarith [mul_nonneg (mul_nonneg hOpk (sub_nonneg.mpr hSend)) hGdh]
  exact add_le_add le_rfl hTerm5

theorem pqxdhKeyIndBound_le_old (S : Setup) (epsSig epsKemShCr epsGapDh : ℝ)
    (hGdh : 0 ≤ epsGapDh) :
    pqxdhKeyIndBoundReal S epsSig epsKemShCr epsGapDh ≤
      (S.N_id : ℝ) * epsSig +
      ((S.N_dh : ℝ) ^ 2) / (2 : ℝ) ^ 250 +
      (S.N_spk_tot : ℝ) * (S.N_send_tot : ℝ) * epsKemShCr +
      ((S.N_spk_tot : ℝ) ^ 2) / (2 : ℝ) ^ 256 +
      2 * ((S.N_spk_tot : ℝ) * ((S.N_id : ℝ) + (S.N_send_tot : ℝ)) +
        (S.N_id : ℝ) * (S.N_send_tot : ℝ) +
        (S.N_opk_tot : ℝ) * (S.N_send_tot : ℝ)) * epsGapDh := by
  refine (pqxdhKeyIndBound_le_old_dh4 S epsSig epsKemShCr epsGapDh hGdh).trans ?_
  exact add_le_add
    (add_le_add
      (add_le_add (add_le_add le_rfl (pqxdhKeyIndBound_ec_coll_le_old S)) le_rfl)
      (pqxdhKeyIndBound_kem_coll_le_old S))
    le_rfl

noncomputable def rootKdfRoTermReal (S : Setup) (q_roRoot : ℕ) : ℝ :=
  2 * (S.N_sess_tot : ℝ) * ((q_roRoot : ℝ) + (S.N_sess_tot : ℝ)) / (2 : ℝ) ^ 256

/-- Real-valued closed-form PQXDH `Auth` bound matching `pqxdhAuthBound`. -/
noncomputable def pqxdhAuthBoundReal
    (S : Setup) (q_roRoot : ℕ)
    (epsSig epsKemShCr epsGapDh
     epsPrfCk epsPrfMsgKeys epsAeadCpa epsPrfHmac : ℝ) : ℝ :=
  pqxdhKeyIndBoundReal S epsSig epsKemShCr epsGapDh +
  2 * (S.N_send_tot : ℝ) * (S.N_recv_tot : ℝ) / (2 : ℝ) ^ 250 +
  rootKdfRoTermReal S q_roRoot +
  2 * (S.N_sess_tot : ℝ) * epsPrfCk +
  2 * (S.N_sess_tot : ℝ) * epsPrfMsgKeys +
  2 * (S.N_send_tot : ℝ) * epsAeadCpa +
  2 * (2 * (S.N_sess_tot : ℝ) * epsPrfHmac + (S.N_recv_tot : ℝ) / (2 : ℝ) ^ 64)

theorem ofReal_natCast_div_two_pow (n k : ℕ) :
    ENNReal.ofReal ((n : ℝ) / (2 : ℝ) ^ k) = (n : ℝ≥0∞) / (2 : ℝ≥0∞) ^ k := by
  rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
    ENNReal.ofReal_pow (by norm_num) k, ENNReal.ofReal_ofNat]

theorem ofReal_natCast_mul_toReal (n : ℕ) {e : ℝ≥0∞} (he : e ≠ ⊤) :
    ENNReal.ofReal ((n : ℝ) * e.toReal) = (n : ℝ≥0∞) * e := by
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast, ENNReal.ofReal_toReal he]

theorem ofReal_pqxdhKeyIndBoundReal (S : Setup) {e1 e2 e3 : ℝ≥0∞}
    (he1 : e1 ≠ ⊤) (he2 : e2 ≠ ⊤) (he3 : e3 ≠ ⊤) :
    ENNReal.ofReal (pqxdhKeyIndBoundReal S e1.toReal e2.toReal e3.toReal) =
      pqxdhKeyIndBound S e1 e2 e3 := by
  unfold pqxdhKeyIndBoundReal pqxdhKeyIndBound
  have hc2R : (S.N_spk_tot : ℝ) * (S.N_send_tot : ℝ) = ((S.N_spk_tot * S.N_send_tot : ℕ) : ℝ) := by
    push_cast; rfl
  have hc2E : (S.N_spk_tot : ℝ≥0∞) * (S.N_send_tot : ℝ≥0∞) =
      ((S.N_spk_tot * S.N_send_tot : ℕ) : ℝ≥0∞) := by
    push_cast; rfl
  let c3 : ℕ := 2 * (S.N_spk_tot * (S.N_id + S.N_send_tot) +
    S.N_id * S.N_send_tot + S.N_opk_tot * S.N_send_opk_tot)
  have hc3R : 2 * ((S.N_spk_tot : ℝ) * ((S.N_id : ℝ) + (S.N_send_tot : ℝ)) +
      (S.N_id : ℝ) * (S.N_send_tot : ℝ) + (S.N_opk_tot : ℝ) * (S.N_send_opk_tot : ℝ)) =
      (c3 : ℝ) := by
    dsimp [c3]; push_cast; rfl
  have hc3E : 2 * ((S.N_spk_tot : ℝ≥0∞) * ((S.N_id : ℝ≥0∞) + (S.N_send_tot : ℝ≥0∞)) +
      (S.N_id : ℝ≥0∞) * (S.N_send_tot : ℝ≥0∞) +
      (S.N_opk_tot : ℝ≥0∞) * (S.N_send_opk_tot : ℝ≥0∞)) = (c3 : ℝ≥0∞) := by
    dsimp [c3]; push_cast; rfl
  rw [hc2R, hc2E, hc3R, hc3E]
  rw [ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity),
    ofReal_natCast_mul_toReal S.N_id he1,
    ofReal_natCast_div_two_pow (S.N_dh * (S.N_dh - 1) + S.N_send_tot * (S.N_send_tot - 1)) 251,
    ofReal_natCast_mul_toReal (S.N_spk_tot * S.N_send_tot) he2,
    ofReal_natCast_div_two_pow (S.N_spk_tot * (S.N_spk_tot - 1)) 256,
    ofReal_natCast_mul_toReal c3 he3]

theorem ofReal_rootKdfRoTermReal (S : Setup) (q_roRoot : ℕ) :
    ENNReal.ofReal (rootKdfRoTermReal S q_roRoot) = rootKdfRoTerm S q_roRoot := by
  unfold rootKdfRoTermReal rootKdfRoTerm
  have hcR : 2 * (S.N_sess_tot : ℝ) * ((q_roRoot : ℝ) + (S.N_sess_tot : ℝ)) =
      ((2 * S.N_sess_tot * (q_roRoot + S.N_sess_tot) : ℕ) : ℝ) := by
    push_cast; rfl
  have hcE : 2 * (S.N_sess_tot : ℝ≥0∞) * ((q_roRoot : ℝ≥0∞) + (S.N_sess_tot : ℝ≥0∞)) =
      ((2 * S.N_sess_tot * (q_roRoot + S.N_sess_tot) : ℕ) : ℝ≥0∞) := by
    push_cast; rfl
  rw [hcR, hcE, ofReal_natCast_div_two_pow (2 * S.N_sess_tot * (q_roRoot + S.N_sess_tot)) 256]

private theorem ofReal_add7 {a1 a2 a3 a4 a5 a6 a7 : ℝ}
    (h1 : 0 ≤ a1) (h2 : 0 ≤ a2) (h3 : 0 ≤ a3) (h4 : 0 ≤ a4)
    (h5 : 0 ≤ a5) (h6 : 0 ≤ a6) (h7 : 0 ≤ a7) :
    ENNReal.ofReal (a1 + a2 + a3 + a4 + a5 + a6 + a7) =
      ENNReal.ofReal a1 + ENNReal.ofReal a2 + ENNReal.ofReal a3 +
      ENNReal.ofReal a4 + ENNReal.ofReal a5 + ENNReal.ofReal a6 + ENNReal.ofReal a7 := by
  rw [ENNReal.ofReal_add (by linarith) h7,
    ENNReal.ofReal_add (by linarith) h6,
    ENNReal.ofReal_add (by linarith) h5,
    ENNReal.ofReal_add (by linarith) h4,
    ENNReal.ofReal_add (by linarith) h3,
    ENNReal.ofReal_add h1 h2]

theorem ofReal_pqxdhAuthBoundReal (S : Setup) (q_roRoot : ℕ)
    {e1 e2 e3 e4 e5 e6 e7 : ℝ≥0∞}
    (he1 : e1 ≠ ⊤) (he2 : e2 ≠ ⊤) (he3 : e3 ≠ ⊤) (he4 : e4 ≠ ⊤)
    (he5 : e5 ≠ ⊤) (he6 : e6 ≠ ⊤) (he7 : e7 ≠ ⊤) :
    ENNReal.ofReal
      (pqxdhAuthBoundReal S q_roRoot e1.toReal e2.toReal e3.toReal
        e4.toReal e5.toReal e6.toReal e7.toReal) =
      pqxdhAuthBound S q_roRoot e1 e2 e3 e4 e5 e6 e7 := by
  have h1 : 0 ≤ pqxdhKeyIndBoundReal S e1.toReal e2.toReal e3.toReal := by
    unfold pqxdhKeyIndBoundReal; positivity
  have h3 : 0 ≤ rootKdfRoTermReal S q_roRoot := by
    unfold rootKdfRoTermReal; positivity
  unfold pqxdhAuthBoundReal pqxdhAuthBound
  rw [ofReal_add7 h1 (by positivity) h3 (by positivity) (by positivity) (by positivity)
    (by positivity)]
  have hc2R : 2 * (S.N_send_tot : ℝ) * (S.N_recv_tot : ℝ) =
      ((2 * S.N_send_tot * S.N_recv_tot : ℕ) : ℝ) := by push_cast; rfl
  have hc2E : 2 * (S.N_send_tot : ℝ≥0∞) * (S.N_recv_tot : ℝ≥0∞) =
      ((2 * S.N_send_tot * S.N_recv_tot : ℕ) : ℝ≥0∞) := by push_cast; rfl
  have hc4R : 2 * (S.N_sess_tot : ℝ) = ((2 * S.N_sess_tot : ℕ) : ℝ) := by push_cast; rfl
  have hc4E : 2 * (S.N_sess_tot : ℝ≥0∞) = ((2 * S.N_sess_tot : ℕ) : ℝ≥0∞) := by push_cast; rfl
  have hc6R : 2 * (S.N_send_tot : ℝ) = ((2 * S.N_send_tot : ℕ) : ℝ) := by push_cast; rfl
  have hc6E : 2 * (S.N_send_tot : ℝ≥0∞) = ((2 * S.N_send_tot : ℕ) : ℝ≥0∞) := by push_cast; rfl
  have ht7 : ENNReal.ofReal (2 * (2 * (S.N_sess_tot : ℝ) * e7.toReal +
        (S.N_recv_tot : ℝ) / (2 : ℝ) ^ 64)) =
      2 * (2 * (S.N_sess_tot : ℝ≥0∞) * e7 + (S.N_recv_tot : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 64) := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat,
      ENNReal.ofReal_add (by positivity) (by positivity),
      hc4R, hc4E, ofReal_natCast_mul_toReal (2 * S.N_sess_tot) he7,
      ofReal_natCast_div_two_pow S.N_recv_tot 64]
  rw [ofReal_pqxdhKeyIndBoundReal S he1 he2 he3,
    hc2R, hc2E, ofReal_natCast_div_two_pow (2 * S.N_send_tot * S.N_recv_tot) 250,
    ofReal_rootKdfRoTermReal S q_roRoot,
    ht7,
    hc4R, hc4E, ofReal_natCast_mul_toReal (2 * S.N_sess_tot) he4,
    ofReal_natCast_mul_toReal (2 * S.N_sess_tot) he5,
    hc6R, hc6E, ofReal_natCast_mul_toReal (2 * S.N_send_tot) he6]

/-- Real-valued activity-bounded PQXDH `KeyInd` bound matching `pqxdhKeyIndBoundActive`. -/
noncomputable def pqxdhKeyIndBoundActiveReal
    (S : Setup) (q_on : Nat)
    (epsSig epsKemShCr epsGapDh : ℝ) : ℝ :=
  let n_id := activeIdCount S q_on
  let n_spk := activeSpkCount S q_on
  let n_opk := activeOpkCount S q_on
  let n_send := activeSendCount S q_on
  let n_send_opk := activeSendOpkCount S q_on
  let n_dh := activeDhCount S q_on
  (n_id : ℝ) * epsSig +
  ((n_dh * (n_dh - 1) + n_send * (n_send - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 251 +
  (n_spk : ℝ) * (n_send : ℝ) * epsKemShCr +
  ((n_spk * (n_spk - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 256 +
  2 * ((n_spk : ℝ) * ((n_id : ℝ) + (n_send : ℝ)) +
    (n_id : ℝ) * (n_send : ℝ) +
    (n_opk : ℝ) * (n_send_opk : ℝ)) * epsGapDh

theorem ofReal_pqxdhKeyIndBoundActiveReal (S : Setup) (q_on : Nat) {e1 e2 e3 : ℝ≥0∞}
    (he1 : e1 ≠ ⊤) (he2 : e2 ≠ ⊤) (he3 : e3 ≠ ⊤) :
    ENNReal.ofReal (pqxdhKeyIndBoundActiveReal S q_on e1.toReal e2.toReal e3.toReal) =
      pqxdhKeyIndBoundActive S q_on e1 e2 e3 := by
  unfold pqxdhKeyIndBoundActiveReal pqxdhKeyIndBoundActive
  dsimp only
  let n_id := activeIdCount S q_on
  let n_spk := activeSpkCount S q_on
  let n_opk := activeOpkCount S q_on
  let n_send := activeSendCount S q_on
  let n_send_opk := activeSendOpkCount S q_on
  let n_dh := activeDhCount S q_on
  have hc2R : (n_spk : ℝ) * (n_send : ℝ) = ((n_spk * n_send : ℕ) : ℝ) := by
    push_cast; rfl
  have hc2E : (n_spk : ℝ≥0∞) * (n_send : ℝ≥0∞) = ((n_spk * n_send : ℕ) : ℝ≥0∞) := by
    push_cast; rfl
  let c3 : ℕ := 2 * (n_spk * (n_id + n_send) + n_id * n_send + n_opk * n_send_opk)
  have hc3R : 2 * ((n_spk : ℝ) * ((n_id : ℝ) + (n_send : ℝ)) +
      (n_id : ℝ) * (n_send : ℝ) + (n_opk : ℝ) * (n_send_opk : ℝ)) = (c3 : ℝ) := by
    dsimp [c3]; push_cast; rfl
  have hc3E : 2 * ((n_spk : ℝ≥0∞) * ((n_id : ℝ≥0∞) + (n_send : ℝ≥0∞)) +
      (n_id : ℝ≥0∞) * (n_send : ℝ≥0∞) +
      (n_opk : ℝ≥0∞) * (n_send_opk : ℝ≥0∞)) = (c3 : ℝ≥0∞) := by
    dsimp [c3]; push_cast; rfl
  change ENNReal.ofReal
      ((n_id : ℝ) * e1.toReal +
        ((n_dh * (n_dh - 1) + n_send * (n_send - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 251 +
        (n_spk : ℝ) * (n_send : ℝ) * e2.toReal +
        ((n_spk * (n_spk - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 256 +
        2 * ((n_spk : ℝ) * ((n_id : ℝ) + (n_send : ℝ)) +
          (n_id : ℝ) * (n_send : ℝ) + (n_opk : ℝ) * (n_send_opk : ℝ)) * e3.toReal) =
    (n_id : ℝ≥0∞) * e1 +
      ((n_dh * (n_dh - 1) + n_send * (n_send - 1) : ℕ) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 251 +
      (n_spk : ℝ≥0∞) * (n_send : ℝ≥0∞) * e2 +
      ((n_spk * (n_spk - 1) : ℕ) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 256 +
      2 * ((n_spk : ℝ≥0∞) * ((n_id : ℝ≥0∞) + (n_send : ℝ≥0∞)) +
        (n_id : ℝ≥0∞) * (n_send : ℝ≥0∞) + (n_opk : ℝ≥0∞) * (n_send_opk : ℝ≥0∞)) * e3
  rw [hc2R, hc2E, hc3R, hc3E]
  rw [ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity),
    ofReal_natCast_mul_toReal n_id he1,
    ofReal_natCast_div_two_pow (n_dh * (n_dh - 1) + n_send * (n_send - 1)) 251,
    ofReal_natCast_mul_toReal (n_spk * n_send) he2,
    ofReal_natCast_div_two_pow (n_spk * (n_spk - 1)) 256,
    ofReal_natCast_mul_toReal c3 he3]

end SignalPqxdh

namespace SignalPqxdh.Security

open scoped ENNReal
open SignalPqxdh

noncomputable def kemDecapsFailureTermReal (S : Setup) (δ : ℝ) : ℝ :=
  2 * (S.N_send_tot : ℝ) * (S.N_spk_tot : ℝ) * δ

/-- Real-valued δ-correctness `KeyInd` bound matching `pqxdhKeyIndAdvantageBoundδ`. -/
noncomputable def pqxdhKeyIndAdvantageBoundδReal (S : Setup) (δ : ℝ)
    (epsSig epsKemShCr epsGapDh : ℝ) : ℝ :=
  pqxdhKeyIndBoundReal S epsSig epsKemShCr epsGapDh + kemDecapsFailureTermReal S δ

/-- Real-valued δ-correctness `Auth` bound matching `pqxdhAuthAdvantageBoundδ`. -/
noncomputable def pqxdhAuthAdvantageBoundδReal (S : Setup) (q_roRoot : ℕ) (δ : ℝ)
    (epsSig epsKemShCr epsGapDh epsPrfCk epsPrfMsgKeys epsAeadCpa epsPrfHmac : ℝ) : ℝ :=
  pqxdhAuthBoundReal S q_roRoot epsSig epsKemShCr epsGapDh epsPrfCk epsPrfMsgKeys epsAeadCpa
      epsPrfHmac +
    kemDecapsFailureTermReal S δ

theorem ofReal_kemDecapsFailureTermReal (S : Setup) {d : ℝ≥0∞} (hd : d ≠ ⊤) :
    ENNReal.ofReal (kemDecapsFailureTermReal S d.toReal) = kemDecapsFailureTerm S d := by
  unfold kemDecapsFailureTermReal kemDecapsFailureTerm
  have hcR : 2 * (S.N_send_tot : ℝ) * (S.N_spk_tot : ℝ) =
      ((2 * S.N_send_tot * S.N_spk_tot : ℕ) : ℝ) := by push_cast; rfl
  have hcE : 2 * (S.N_send_tot : ℝ≥0∞) * (S.N_spk_tot : ℝ≥0∞) =
      ((2 * S.N_send_tot * S.N_spk_tot : ℕ) : ℝ≥0∞) := by push_cast; rfl
  rw [hcR, hcE, ofReal_natCast_mul_toReal (2 * S.N_send_tot * S.N_spk_tot) hd]

theorem ofReal_pqxdhKeyIndAdvantageBoundδReal (S : Setup) {d e1 e2 e3 : ℝ≥0∞}
    (hd : d ≠ ⊤) (he1 : e1 ≠ ⊤) (he2 : e2 ≠ ⊤) (he3 : e3 ≠ ⊤) :
    ENNReal.ofReal (pqxdhKeyIndAdvantageBoundδReal S d.toReal e1.toReal e2.toReal e3.toReal) =
      pqxdhKeyIndAdvantageBoundδ S d e1 e2 e3 := by
  have h1 : 0 ≤ pqxdhKeyIndBoundReal S e1.toReal e2.toReal e3.toReal := by
    unfold pqxdhKeyIndBoundReal; positivity
  have h2 : 0 ≤ kemDecapsFailureTermReal S d.toReal := by
    unfold kemDecapsFailureTermReal; positivity
  unfold pqxdhKeyIndAdvantageBoundδReal pqxdhKeyIndAdvantageBoundδ
  rw [ENNReal.ofReal_add h1 h2, ofReal_pqxdhKeyIndBoundReal S he1 he2 he3,
    ofReal_kemDecapsFailureTermReal S hd]

theorem ofReal_pqxdhAuthAdvantageBoundδReal (S : Setup) (q_roRoot : ℕ)
    {d e1 e2 e3 e4 e5 e6 e7 : ℝ≥0∞}
    (hd : d ≠ ⊤) (he1 : e1 ≠ ⊤) (he2 : e2 ≠ ⊤) (he3 : e3 ≠ ⊤)
    (he4 : e4 ≠ ⊤) (he5 : e5 ≠ ⊤) (he6 : e6 ≠ ⊤) (he7 : e7 ≠ ⊤) :
    ENNReal.ofReal
      (pqxdhAuthAdvantageBoundδReal S q_roRoot d.toReal e1.toReal e2.toReal e3.toReal
        e4.toReal e5.toReal e6.toReal e7.toReal) =
      pqxdhAuthAdvantageBoundδ S q_roRoot d e1 e2 e3 e4 e5 e6 e7 := by
  have h1 : 0 ≤ pqxdhAuthBoundReal S q_roRoot e1.toReal e2.toReal e3.toReal
      e4.toReal e5.toReal e6.toReal e7.toReal := by
    unfold pqxdhAuthBoundReal pqxdhKeyIndBoundReal rootKdfRoTermReal; positivity
  have h2 : 0 ≤ kemDecapsFailureTermReal S d.toReal := by
    unfold kemDecapsFailureTermReal; positivity
  unfold pqxdhAuthAdvantageBoundδReal pqxdhAuthAdvantageBoundδ
  rw [ENNReal.ofReal_add h1 h2,
    ofReal_pqxdhAuthBoundReal S q_roRoot he1 he2 he3 he4 he5 he6 he7,
    ofReal_kemDecapsFailureTermReal S hd]

theorem kemDecapsFailureTerm_mono {S : Setup} {δ₁ δ₂ : ℝ≥0∞} (h : δ₁ ≤ δ₂) :
    kemDecapsFailureTerm S δ₁ ≤ kemDecapsFailureTerm S δ₂ := by
  unfold kemDecapsFailureTerm
  gcongr

theorem pqxdhKeyIndAdvantageBoundδ_mono_δ {S : Setup} {δ₁ δ₂ e1 e2 e3 : ℝ≥0∞} (h : δ₁ ≤ δ₂) :
    pqxdhKeyIndAdvantageBoundδ S δ₁ e1 e2 e3 ≤ pqxdhKeyIndAdvantageBoundδ S δ₂ e1 e2 e3 := by
  unfold pqxdhKeyIndAdvantageBoundδ
  gcongr
  exact kemDecapsFailureTerm_mono h

theorem pqxdhAuthAdvantageBoundδ_mono_δ {S : Setup} {q_roRoot : ℕ}
    {δ₁ δ₂ e1 e2 e3 e4 e5 e6 e7 : ℝ≥0∞} (h : δ₁ ≤ δ₂) :
    pqxdhAuthAdvantageBoundδ S q_roRoot δ₁ e1 e2 e3 e4 e5 e6 e7 ≤
      pqxdhAuthAdvantageBoundδ S q_roRoot δ₂ e1 e2 e3 e4 e5 e6 e7 := by
  unfold pqxdhAuthAdvantageBoundδ
  gcongr
  exact kemDecapsFailureTerm_mono h

/-- Real-valued activity-bounded δ-correctness `KeyInd` bound matching `pqxdhKeyIndAdvantageBoundActiveδ`. -/
noncomputable def pqxdhKeyIndAdvantageBoundActiveδReal (S : Setup) (q_on : Nat) (δ : ℝ)
    (epsSig epsKemShCr epsGapDh : ℝ) : ℝ :=
  pqxdhKeyIndBoundActiveReal S q_on epsSig epsKemShCr epsGapDh + kemDecapsFailureTermReal S δ

theorem ofReal_pqxdhKeyIndAdvantageBoundActiveδReal (S : Setup) (q_on : Nat) {d e1 e2 e3 : ℝ≥0∞}
    (hd : d ≠ ⊤) (he1 : e1 ≠ ⊤) (he2 : e2 ≠ ⊤) (he3 : e3 ≠ ⊤) :
    ENNReal.ofReal
      (pqxdhKeyIndAdvantageBoundActiveδReal S q_on d.toReal e1.toReal e2.toReal e3.toReal) =
      pqxdhKeyIndAdvantageBoundActiveδ S q_on d e1 e2 e3 := by
  have h1 : 0 ≤ pqxdhKeyIndBoundActiveReal S q_on e1.toReal e2.toReal e3.toReal := by
    unfold pqxdhKeyIndBoundActiveReal; dsimp only; positivity
  have h2 : 0 ≤ kemDecapsFailureTermReal S d.toReal := by
    unfold kemDecapsFailureTermReal; positivity
  unfold pqxdhKeyIndAdvantageBoundActiveδReal pqxdhKeyIndAdvantageBoundActiveδ
  rw [ENNReal.ofReal_add h1 h2, ofReal_pqxdhKeyIndBoundActiveReal S q_on he1 he2 he3,
    ofReal_kemDecapsFailureTermReal S hd]

theorem pqxdhKeyIndAdvantageBoundActiveδ_mono_δ {S : Setup} {q_on : Nat}
    {δ₁ δ₂ e1 e2 e3 : ℝ≥0∞} (h : δ₁ ≤ δ₂) :
    pqxdhKeyIndAdvantageBoundActiveδ S q_on δ₁ e1 e2 e3 ≤
      pqxdhKeyIndAdvantageBoundActiveδ S q_on δ₂ e1 e2 e3 := by
  unfold pqxdhKeyIndAdvantageBoundActiveδ
  gcongr
  exact kemDecapsFailureTerm_mono h

theorem pqxdhKeyIndAdvantageBoundActiveδ_le
    (S : Setup) (q_on : Nat) (δ epsSig epsKemShCr epsGapDh : ℝ≥0∞) :
    pqxdhKeyIndAdvantageBoundActiveδ S q_on δ epsSig epsKemShCr epsGapDh ≤
      pqxdhKeyIndAdvantageBoundδ S δ epsSig epsKemShCr epsGapDh :=
  add_le_add (pqxdhKeyIndBoundActive_le S q_on epsSig epsKemShCr epsGapDh) le_rfl

end SignalPqxdh.Security
