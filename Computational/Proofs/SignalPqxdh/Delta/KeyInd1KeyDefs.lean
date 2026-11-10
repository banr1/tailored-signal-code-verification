/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Pqxdh.Security.HeadlineDelta
public import Computational.Proofs.SignalPqxdh.Delta.KeyIndDefs
public import Computational.Proofs.SignalPqxdh.Security.RoKemHop1Key
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.EvalDist.Measure

/-!
# One-Key PQXDH Key Indistinguishability with Imperfect KEM Correctness: Hop Statements

**Checked by Lean.** States the static and activity-bounded hop obligations for the one-key
random-oracle handshake game `KeyInd1KeyRoAdvantage` (DEV-CLI16, DEV-PQ21) under δ-correct KEMs and
assembles them into `PqxdhKeyIndReductionBoundStaticδ` and `PqxdhKeyIndReductionBoundδ`.
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal
open MeasureTheory
open OracleSpec OracleComp
open SignalPqxdh SignalPqxdh.Security
open Proofs.SignalPqxdh.Security
open Proofs.SignalPqxdh.Security.FgGapDh

namespace Proofs.SignalPqxdh.Security.PqxdhDelta

/-- One-key `G0 -> G3` hop bound under `CryptoWellFormedPrimitivesδ`. -/
def KI1KeyHopG0G3Stmt (S : Setup) : Prop :=
  ∀ (P : Primitives), CryptoWellFormedPrimitivesδ P →
    ∀ (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b),
      |KeyInd1KeyRoAdvantageReal S P A.1 - keyInd1KeyAdvG3 S P A.1| ≤
        (S.N_id : ℝ) * GapSigEufCmaReal P P.isValidDhTriple (sigReductionKeyInd1Key S b A) +
        ((S.N_dh * (S.N_dh - 1) + S.N_send_tot * (S.N_send_tot - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 251 +
        (S.N_spk_tot : ℝ) * (S.N_send_tot : ℝ) * KemShCrReal P (shcrReductionKeyInd1Key S b A) +
        ((S.N_spk_tot * (S.N_spk_tot - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 256

/-- Per-index reduction of `hasBadKemCorrRecordsAt` in `runKeyInd1KeyShCrSim` to
    `kemCorrExpProb`. -/
def KI1KeyCorrAtStmt (S : Setup) : Prop :=
  ∀ (P : Primitives), CryptoWellFormedPrimitivesδ P →
    ∀ (A : KeyIndAdversary S) (idx : ℕ), idx < S.N_spk_tot * S.N_send_tot →
      ∃ choosePk : Bytes → Bytes → ProbComp Bytes,
        (𝒟[runKeyInd1KeyShCrSim S P A >>= fun x =>
            pure (hasBadKemCorrRecordsAt S P idx x.2.2.initKemRecs x.2.2.recvKemRecs)]
          {true}).toReal ≤
          (𝒟[kemCorrExpProb P choosePk] {true}).toReal

def KI1KeyStopStmt (S : Setup) : Prop :=
  KIStopStmt S

/-- Static `G3` bound on `keyInd1KeyAdvG3` via `gdh` and `kemDecapsFailureTermReal`. -/
def KI1KeyG3BoundStmt (S : Setup)
    (gdh : (b : QueryBudget) → BoundedAdv (KeyIndAdversary S) b → GapDhWithSignAdv) : Prop :=
  ∀ (P : Primitives), CryptoWellFormedPrimitivesδ P →
    ∀ (δ : ℝ), KemDeltaCorrectReal P δ →
    ∀ (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b),
      keyInd1KeyAdvG3 S P A.1 ≤
        2 * (((S.N_spk_tot : ℝ) * ((S.N_id : ℝ) + (S.N_send_tot : ℝ)) +
              (S.N_id : ℝ) * (S.N_send_tot : ℝ) +
              (S.N_opk_tot : ℝ) * (S.N_send_opk_tot : ℝ)) *
              GapDhWithSignReal P P.isValidDhTriple P.pow8 (gdh b A)) +
        kemDecapsFailureTermReal S δ

theorem prob_hasBadKemCorrRecords_runKeyInd1KeyShCrSim_le (S : Setup) (hAt : KI1KeyCorrAtStmt S)
    (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P) (δ : ℝ) (hδ : KemDeltaCorrectReal P δ)
    (A : KeyIndAdversary S) :
    (𝒟[runKeyInd1KeyShCrSim S P A >>= fun x =>
        pure (hasBadKemCorrRecords S P x.2.2.initKemRecs x.2.2.recvKemRecs)] {true}).toReal ≤
      (S.N_spk_tot : ℝ) * (S.N_send_tot : ℝ) * δ := by
  have hU := _root_.SignalPqxdh.Security.toReal_any_range_le_sum (runKeyInd1KeyShCrSim S P A)
    (S.N_spk_tot * S.N_send_tot)
    (fun idx x => hasBadKemCorrRecordsAt S P idx x.2.2.initKemRecs x.2.2.recvKemRecs)
  refine le_trans hU ?_
  calc (∑ k ∈ Finset.range (S.N_spk_tot * S.N_send_tot),
        (𝒟[runKeyInd1KeyShCrSim S P A >>= fun x =>
          pure (hasBadKemCorrRecordsAt S P k x.2.2.initKemRecs x.2.2.recvKemRecs)] {true}).toReal)
      ≤ ∑ _k ∈ Finset.range (S.N_spk_tot * S.N_send_tot), δ := by
        refine Finset.sum_le_sum (fun k hk => ?_)
        obtain ⟨choosePk, hC⟩ := hAt P hP A k (Finset.mem_range.mp hk)
        exact le_trans hC (kemCorrExpProb_le P δ hδ choosePk)
    _ = (S.N_spk_tot : ℝ) * (S.N_send_tot : ℝ) * δ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

/-- Static one-key δ key-indistinguishability reduction bound over `pqxdhKeyIndAdvantageBoundδ`. -/
def PqxdhKeyIndReductionBoundStaticδ (S : Setup) (R : KeyIndReductionFamily S) : Prop :=
  ∀ (P : Primitives), CryptoWellFormedPrimitivesδ P →
    ∀ (δ : ℝ≥0∞), KemDeltaCorrect P δ →
    ∀ (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b),
      KeyInd1KeyRoAdvantage S P A.1 ≤
        pqxdhKeyIndAdvantageBoundδ S δ
          (GapSigEufCma P P.isValidDhTriple (R.sig b A))
          (KemShCr P (R.shcr b A))
          (GapDhWithSign P P.isValidDhTriple P.pow8 (R.gdh b A))

/-- Assembles `KI1KeyHopG0G3Stmt` and `KI1KeyG3BoundStmt` into `PqxdhKeyIndReductionBoundStaticδ`. -/
theorem pqxdh_1key_key_ind_withδ_of_hops (S : Setup)
    (gdh : (b : QueryBudget) → BoundedAdv (KeyIndAdversary S) b → GapDhWithSignAdv)
    (hHop : KI1KeyHopG0G3Stmt S) (hG3 : KI1KeyG3BoundStmt S gdh) :
    PqxdhKeyIndReductionBoundStaticδ S
      { sig := sigReductionKeyInd1Key S
        shcr := shcrReductionKeyInd1Key S
        gdh := gdh } := by
  intro P hP δ hδ b A
  have h03 := hHop P hP b A
  have h3 := hG3 P hP (min δ 1).toReal hδ.min_one_real b A
  have hNonneg : 0 ≤ KeyInd1KeyRoAdvantageReal S P A.1 := by
    unfold KeyInd1KeyRoAdvantageReal
    exact ENNReal.toReal_nonneg
  have hG3_nonneg : 0 ≤ keyInd1KeyAdvG3 S P A.1 := by
    unfold keyInd1KeyAdvG3
    exact ENNReal.toReal_nonneg
  have htri := abs_sub_le (KeyInd1KeyRoAdvantageReal S P A.1) (keyInd1KeyAdvG3 S P A.1) 0
  rw [sub_zero, abs_of_nonneg hNonneg, sub_zero, abs_of_nonneg hG3_nonneg] at htri
  have hReal : (KeyInd1KeyRoAdvantage S P A.1).toReal ≤
      pqxdhKeyIndAdvantageBoundδReal S (min δ 1).toReal
        (GapSigEufCma P P.isValidDhTriple (sigReductionKeyInd1Key S b A)).toReal
        (KemShCr P (shcrReductionKeyInd1Key S b A)).toReal
        (GapDhWithSign P P.isValidDhTriple P.pow8 (gdh b A)).toReal := by
    simp only [KeyInd1KeyRoAdvantageReal, GapSigEufCmaReal, KemShCrReal, GapDhWithSignReal] at h03 h3 htri
    unfold pqxdhKeyIndAdvantageBoundδReal pqxdhKeyIndBoundReal
    set_option exponentiation.threshold 512 in
    linarith
  have hd : min δ 1 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right δ 1)
  have hOfReal := ENNReal.ofReal_le_ofReal hReal
  rw [ENNReal.ofReal_toReal (KeyInd1KeyRoAdvantage_ne_top S P A.1),
    ofReal_pqxdhKeyIndAdvantageBoundδReal S hd
      (GapSigEufCma_ne_top P P.isValidDhTriple (sigReductionKeyInd1Key S b A))
      (KemShCr_ne_top P (shcrReductionKeyInd1Key S b A))
      (GapDhWithSign_ne_top P P.isValidDhTriple P.pow8 (gdh b A))] at hOfReal
  exact hOfReal.trans (pqxdhKeyIndAdvantageBoundδ_mono_δ (min_le_left δ 1))

/-- Activity-bounded one-key `G0 -> G3` hop bound parameterized by creation-order `sig` and `shcr`
    reductions. -/
def KI1KeyActiveHopG0G3Stmt (S : Setup)
    (sig : (b : QueryBudget) → BoundedAdv (KeyIndAdversary S) b → GapSigEufCmaAdv)
    (shcr : (b : QueryBudget) → BoundedAdv (KeyIndAdversary S) b → KemShCrAdv) : Prop :=
  ∀ (P : Primitives), CryptoWellFormedPrimitivesδ P →
    ∀ (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b),
      let n_id := activeIdCount S b.q_on
      let n_spk := activeSpkCount S b.q_on
      let n_send := activeSendCount S b.q_on
      let n_dh := activeDhCount S b.q_on
      |KeyInd1KeyRoAdvantageReal S P A.1 - keyInd1KeyAdvG3 S P A.1| ≤
        (n_id : ℝ) * GapSigEufCmaReal P P.isValidDhTriple (sig b A) +
        ((n_dh * (n_dh - 1) + n_send * (n_send - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 251 +
        (n_spk : ℝ) * (n_send : ℝ) * KemShCrReal P (shcr b A) +
        ((n_spk * (n_spk - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 256

/-- Activity-bounded `G3` bound on `keyInd1KeyAdvG3` via `gdh` and `kemDecapsFailureTermReal`. -/
def KI1KeyActiveG3BoundStmt (S : Setup)
    (gdh : (b : QueryBudget) → BoundedAdv (KeyIndAdversary S) b → GapDhWithSignAdv) : Prop :=
  ∀ (P : Primitives), CryptoWellFormedPrimitivesδ P →
    ∀ (δ : ℝ), KemDeltaCorrectReal P δ →
    ∀ (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b),
      let n_id := activeIdCount S b.q_on
      let n_spk := activeSpkCount S b.q_on
      let n_opk := activeOpkCount S b.q_on
      let n_send := activeSendCount S b.q_on
      let n_send_opk := activeSendOpkCount S b.q_on
      keyInd1KeyAdvG3 S P A.1 ≤
        2 * (((n_spk : ℝ) * ((n_id : ℝ) + (n_send : ℝ)) +
              (n_id : ℝ) * (n_send : ℝ) +
              (n_opk : ℝ) * (n_send_opk : ℝ)) *
              GapDhWithSignReal P P.isValidDhTriple P.pow8 (gdh b A)) +
        kemDecapsFailureTermReal S δ

/-- Assembles `KI1KeyActiveHopG0G3Stmt` and `KI1KeyActiveG3BoundStmt` into
    `PqxdhKeyIndReductionBoundδ`. -/
theorem pqxdh_1key_key_ind_active_withδ_of_hops (S : Setup)
    (sig : (b : QueryBudget) → BoundedAdv (KeyIndAdversary S) b → GapSigEufCmaAdv)
    (shcr : (b : QueryBudget) → BoundedAdv (KeyIndAdversary S) b → KemShCrAdv)
    (gdh : (b : QueryBudget) → BoundedAdv (KeyIndAdversary S) b → GapDhWithSignAdv)
    (hHop : KI1KeyActiveHopG0G3Stmt S sig shcr)
    (hG3 : KI1KeyActiveG3BoundStmt S gdh) :
    PqxdhKeyIndReductionBoundδ S { sig := sig, shcr := shcr, gdh := gdh } := by
  intro P hP δ hδ b A
  have h03 := hHop P hP b A
  have h3 := hG3 P hP (min δ 1).toReal hδ.min_one_real b A
  dsimp only at h03 h3
  have hNonneg : 0 ≤ KeyInd1KeyRoAdvantageReal S P A.1 := by
    unfold KeyInd1KeyRoAdvantageReal
    exact ENNReal.toReal_nonneg
  have hG3_nonneg : 0 ≤ keyInd1KeyAdvG3 S P A.1 := by
    unfold keyInd1KeyAdvG3
    exact ENNReal.toReal_nonneg
  have htri := abs_sub_le (KeyInd1KeyRoAdvantageReal S P A.1) (keyInd1KeyAdvG3 S P A.1) 0
  rw [sub_zero, abs_of_nonneg hNonneg, sub_zero, abs_of_nonneg hG3_nonneg] at htri
  have hReal : (KeyInd1KeyRoAdvantage S P A.1).toReal ≤
      pqxdhKeyIndAdvantageBoundActiveδReal S b.q_on (min δ 1).toReal
        (GapSigEufCma P P.isValidDhTriple (sig b A)).toReal
        (KemShCr P (shcr b A)).toReal
        (GapDhWithSign P P.isValidDhTriple P.pow8 (gdh b A)).toReal := by
    simp only [KeyInd1KeyRoAdvantageReal, GapSigEufCmaReal, KemShCrReal, GapDhWithSignReal] at h03 h3 htri
    unfold pqxdhKeyIndAdvantageBoundActiveδReal pqxdhKeyIndBoundActiveReal
    dsimp only
    set_option exponentiation.threshold 512 in
    linarith
  have hd : min δ 1 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right δ 1)
  have hOfReal := ENNReal.ofReal_le_ofReal hReal
  rw [ENNReal.ofReal_toReal (KeyInd1KeyRoAdvantage_ne_top S P A.1),
    ofReal_pqxdhKeyIndAdvantageBoundActiveδReal S b.q_on hd
      (GapSigEufCma_ne_top P P.isValidDhTriple (sig b A))
      (KemShCr_ne_top P (shcr b A))
      (GapDhWithSign_ne_top P P.isValidDhTriple P.pow8 (gdh b A))] at hOfReal
  exact hOfReal.trans (pqxdhKeyIndAdvantageBoundActiveδ_mono_δ (min_le_left δ 1))

end Proofs.SignalPqxdh.Security.PqxdhDelta
