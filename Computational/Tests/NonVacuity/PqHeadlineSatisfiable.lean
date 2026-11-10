/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Tests.NonVacuity.ModelPrimsWitness255
public import Computational.Proofs.LibsignalCli.StatementPqSecure
import Computational.Proofs.E2E.ComposedBinaryLinkV1
import Computational.Proofs.SpecLemmas.Assumptions.KemCorrect
import Computational.Tests.NonVacuity.KeyInd1KeyRoNonVac
import LibsignalBinary.Proofs.SignalSession.PqModelRun

/-!
# Joint Hypothesis Satisfiability for `LibsignalCliPqSecure`

Exhibits simultaneous witnesses for all 15 universal hypotheses of `LibsignalCliPqSecure` for every
`S : SignalPqxdh.Setup` and `ℓ < 10 ^ 6`, and instantiates both conclusion clauses directly.
Combines the `BitVec 255` primitive witness from `ModelPrimsWitness255` with
`run := pqModelRun X255 W255`, query budgets `(b := ⟨1, 0, 1, 0⟩, qStart := 1, qs := fun _ => 1)`,
and the query-issuing adversary `cliRoCoinDrAdv` at `q_on = 0`.
-/

public section

set_option autoImplicit false
open OracleComp OracleSpec MeasureTheory ENNReal

namespace CryptoVerification.E2E

open CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession CKA
  CryptoVerification.LibsignalSession CryptoVerification.LibsignalSpqrV1
  CryptoVerification.SignalSession
open SignalPqxdh SpecTests.SignalPqxdh

private theorem k255_encaps1_isSome (pk : List (BitVec 8)) (r : List.Vector (BitVec 8) 32) :
    (K255.encaps1 pk r).isSome = true := rfl

private theorem bhEncaps1Total_W255 : MlKemEncaps1SucceedsOn64ByteHeaderAndSeeds W255.Q.K :=
  ⟨fun _ r _ => k255_encaps1_isSome _ r, fun _ r => k255_encaps1_isSome _ r⟩

private theorem w255_decaps_encaps (sk : List.Vector (BitVec 8) 3168)
    (pk : List.Vector (BitVec 8) 1568) (r : List.Vector (BitVec 8) 32) :
    W255.Q.decaps sk (W255.Q.encaps pk r).1 = (W255.Q.encaps pk r).2 := rfl

private theorem c255_D_E (k : BitVec 256) (x : BitVec 128) : c255.D k (c255.E k x) = x := rfl

private theorem kemCorrectWith_zero_of_kem_corr {P : SignalPqxdh.Primitives}
    (hCorr : ∀ seed r ss ct, P.kemEncaps (P.kemKeyGen seed).1 r = some (ss, ct) →
      P.kemDecaps (P.kemKeyGen seed).2 ct = some ss) :
    SignalPqxdh.KemDeltaCorrect P 0 := by
  unfold SignalPqxdh.KemDeltaCorrect
  simp [SignalPqxdh.kemHonestFail_eq_false_of_kem_corr hCorr]

private theorem modelPrims_X255_kemCorrectWith_zero :
    SignalPqxdh.KemDeltaCorrect (modelPrims X255 W255) 0 :=
  kemCorrectWith_zero_of_kem_corr
    (modelPrims_kem_corr_of_decaps X255 W255 fun _ _ => w255_decaps_encaps _ _ _)

private theorem modelPrims_X255_cwfδ :
    SignalPqxdh.CryptoWellFormedPrimitivesδ (modelPrims X255 W255) :=
  cryptoWellFormedPrimitivesδ_modelPrims X255 W255 modelPrims_X255_cryptoAssumptions
    dh255_commutes libX25519Rel_c255 c255_D_E

/-- Adversary on `cliGameSpec` that draws `unifSpec` coins, makes one `.roQuery`, and makes one DR
session query on instance `0`. -/
def cliRoCoinDrAdv (S : SignalPqxdh.Setup) (ℓ : ℕ) (PQC : Type) :
    CliGameAdversary S ℓ PQC where
  run :=
    liftM ((cliGameSpec S ℓ PQC).query (.inl (.inl (.inl 1)))) >>= fun _ =>
    liftM ((cliGameSpec S ℓ PQC).query (.inl (.inl (.inr (.roQuery []))))) >>= fun _ =>
    liftM ((cliGameSpec S ℓ PQC).query (.inr (0, .inr .A))) >>= fun _ =>
    pure false

/-- Coin draws, `.roQuery` calls, and DR session queries do not count against `b.q_on`. -/
theorem cliRoCoinDrAdv_bounded (S : SignalPqxdh.Setup) (ℓ : ℕ) (PQC : Type) :
    CliGameAdversaryPerInstanceBounded (cliRoCoinDrAdv S ℓ PQC)
      { q_ro := 1, q_roRoot := 0, q_total := 1, q_on := 0 } 1 (fun _ => 1) := by
  have hStep : ∀ (P : (cliGameSpec S ℓ PQC).Domain → Prop) [DecidablePred P] (n : ℕ),
      (¬ P (.inl (.inl (.inl 1))) ∨ 0 < n) →
      (let n1 := if P (.inl (.inl (.inl 1))) then n - 1 else n
       (¬ P (.inl (.inl (.inr (.roQuery [])))) ∨ 0 < n1) ∧
       (let n2 := if P (.inl (.inl (.inr (.roQuery [])))) then n1 - 1 else n1
        ¬ P (.inr (0, .inr .A)) ∨ 0 < n2)) →
      OracleComp.IsQueryBoundP (cliRoCoinDrAdv S ℓ PQC).run P n := by
    intro P _ n h1 h23
    simp only [cliRoCoinDrAdv]
    rw [OracleComp.isQueryBoundP_query_bind_iff]
    refine ⟨h1, fun _ => ?_⟩
    rw [OracleComp.isQueryBoundP_query_bind_iff]
    refine ⟨h23.1, fun _ => ?_⟩
    rw [OracleComp.isQueryBoundP_query_bind_iff]
    exact ⟨h23.2, fun _ => trivial⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact hStep _ _ (Or.inl (by simp)) ⟨Or.inr Nat.one_pos, Or.inl (by simp)⟩
  · exact hStep _ _ (Or.inl (by simp)) ⟨Or.inl (by simp), Or.inl (by simp)⟩
  · exact hStep _ _ (Or.inl (by simp)) ⟨Or.inl (by simp), Or.inl (by simp)⟩
  · exact hStep _ _ (Or.inl (by simp)) ⟨Or.inr Nat.one_pos, Or.inl (by simp)⟩
  · exact hStep _ _ (Or.inl (by simp)) ⟨Or.inl (by simp), Or.inl (by simp)⟩
  · exact hStep _ _ (Or.inl (by simp)) ⟨Or.inl (by simp), Or.inl (by simp)⟩
  · refine hStep _ _ (Or.inl (by simp)) ⟨Or.inl (by simp), Or.inr ?_⟩
    simp
  · exact hStep _ _ (Or.inl (by simp)) ⟨Or.inl (by simp), Or.inl (by simp)⟩
  · intro k hk
    have hk0 : k = 0 := Nat.lt_one_iff.mp hk
    subst hk0
    refine hStep _ _ (Or.inl (by simp [bhIsInstQueryWithSpqr]))
      ⟨Or.inl (by simp [bhIsInstQueryWithSpqr]), Or.inr ?_⟩
    simp [bhIsInstQueryWithSpqr]

/-- Adversary on `cliGameSpec` that issues a single online PQXDH `.initPrin u` query. -/
def cliInitPrinAdv (S : SignalPqxdh.Setup) (ℓ : ℕ) (PQC : Type) (u : Fin S.N_id) :
    CliGameAdversary S ℓ PQC where
  run :=
    liftM ((cliGameSpec S ℓ PQC).query (.inl (.inl (.inr (.initPrin u))))) >>= fun _ =>
    pure false

theorem cliInitPrinAdv_bounded (S : SignalPqxdh.Setup) (ℓ : ℕ) (PQC : Type) (u : Fin S.N_id) :
    CliGameAdversaryPerInstanceBounded (cliInitPrinAdv S ℓ PQC u)
      { q_ro := 0, q_roRoot := 0, q_total := 1, q_on := 1 } 0 (fun _ => 0) := by
  have hStep : ∀ (P : (cliGameSpec S ℓ PQC).Domain → Prop) [DecidablePred P] (n : ℕ),
      (¬ P (.inl (.inl (.inr (.initPrin u)))) ∨ 0 < n) →
      OracleComp.IsQueryBoundP (cliInitPrinAdv S ℓ PQC u).run P n := by
    intro P _ n h1
    simp only [cliInitPrinAdv]
    rw [OracleComp.isQueryBoundP_query_bind_iff]
    exact ⟨h1, fun _ => trivial⟩
  refine ⟨⟨hStep _ _ (Or.inl (by simp)), hStep _ _ (Or.inl (by simp)),
    hStep _ _ (Or.inl (by simp)), hStep _ _ (Or.inr Nat.one_pos),
    hStep _ _ (Or.inr Nat.one_pos), hStep _ _ (Or.inl (by simp)),
    hStep _ _ (Or.inl (by simp))⟩,
    hStep _ _ (Or.inl (by simp)), fun _ hk => absurd hk (Nat.not_lt_zero _)⟩

theorem cliInitPrinAdv_not_bounded_zero (S : SignalPqxdh.Setup) (ℓ : ℕ) (PQC : Type)
    (u : Fin S.N_id) :
    ¬ CliGameAdversaryPerInstanceBounded (cliInitPrinAdv S ℓ PQC u)
      { q_ro := 0, q_roRoot := 0, q_total := 1, q_on := 0 } 0 (fun _ => 0) := by
  intro ⟨⟨_, _, _, _, hOn, _, _⟩, _, _⟩
  simp only [cliInitPrinAdv] at hOn
  rw [OracleComp.isQueryBoundP_query_bind_iff] at hOn
  rcases hOn.1 with hFalse | hPos
  · exact hFalse (by simp)
  · exact Nat.not_lt_zero _ hPos

/-- Joint satisfiability of all 15 universal hypotheses of `LibsignalCliPqSecure` with
`0 < qStart` and `0 < qs 0`, parameterized by any `pqModelRun` satisfying `CliSpecPqxdh`. -/
theorem cli_pq_headline_hypotheses_jointly_satisfiable_of_cli
    {pqModelRun : UnreachedPqxdhPrimitives → PEParams → CliRun}
    (hCliModel : ∀ (X : UnreachedPqxdhPrimitives) (W : PEParams), CliSpecPqxdh (pqModelRun X W) X W)
    (S : SignalPqxdh.Setup) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6) :
    ∃ (Pt : Type) (_ : DecidableEq Pt) (zPt : Zero Pt) (sPt : SampleableType Pt)
      (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams)
      (δ_kem : ℝ≥0∞) (Dh : DHFun (BitVec 256) Pt)
      (encPt : Pt → CryptoVerification.E2E.Bytes) (encT : Pt → PublicKey)
      (decT : PublicKey → Option Pt)
      (_qep : ℕ) (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
      (δ : ℝ≥0∞) (A : CliGameAdversary S ℓ (BitVec 512)),
      letI : Zero Pt := zPt; letI : SampleableType Pt := sPt
      0 < qStart ∧
      0 < qs 0 ∧
      CliSpecPqxdh run X W ∧
      MlKemEncaps1SucceedsOn64ByteHeaderAndSeeds W.Q.K ∧
      SignalPqxdh.CryptoWellFormedPrimitivesδ (modelPrims X W) ∧
      SignalPqxdh.KemDeltaCorrect (modelPrims X W) δ_kem ∧
      ℓ < 10 ^ 6 ∧
      Dh.Commutes ∧
      X25519RealizesDh W.C Dh encPt encT ∧
      (∀ T, decT (encT T) = some T) ∧
      (∀ T, encT T ≠ dummyKey) ∧
      (∀ x, Dh.dh x 0 = 0) ∧
      (∀ k x, W.C.D k (W.C.E k x) = x) ∧
      DhKerUniform Dh ∧
      (∀ k < qStart, 2 * (qs k + 1) + 25002 < 2 ^ 32) ∧
      (∀ Q : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ) ∧
      CliGameAdversaryPerInstanceBounded A b qStart qs := by
  let b1 : SignalPqxdh.QueryBudget := ⟨1, 0, 1, 0⟩
  let A0 : CliGameAdversary S ℓ (BitVec 512) := cliRoCoinDrAdv S ℓ (BitVec 512)
  refine ⟨BitVec 255, inferInstance, inferInstance, inferInstance,
    pqModelRun X255 W255, X255, W255, 0, dh255, encPt255, encT255, decT255,
    1, b1, 1, fun _ => 1, 1, A0, ?_⟩
  exact ⟨by decide, by decide, hCliModel X255 W255, bhEncaps1Total_W255,
    modelPrims_X255_cwfδ, modelPrims_X255_kemCorrectWith_zero, hℓ,
    dh255_commutes, libX25519Rel_c255, decT255_encT255,
    encT255_ne_dummyKey, dh255_zero, c255_D_E, dh255_kerUniform,
    fun _ _ => show 2 * (1 + 1) + 25002 < 2 ^ 32 by decide,
    fun _ => MeasureTheory.prob_le_one,
    cliRoCoinDrAdv_bounded S ℓ (BitVec 512)⟩

/-- Closed concrete-setup (`N_id = 2`, `ℓ = 32`) specialization of
`cli_pq_headline_hypotheses_jointly_satisfiable_of_cli`. -/
theorem cli_pq_headline_hypotheses_jointly_satisfiable_concrete_of_cli
    {pqModelRun : UnreachedPqxdhPrimitives → PEParams → CliRun}
    (hCliModel : ∀ (X : UnreachedPqxdhPrimitives) (W : PEParams), CliSpecPqxdh (pqModelRun X W) X W) :
    ∃ (S : SignalPqxdh.Setup) (ℓ : ℕ)
      (Pt : Type) (_ : DecidableEq Pt) (zPt : Zero Pt) (sPt : SampleableType Pt)
      (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams)
      (δ_kem : ℝ≥0∞) (Dh : DHFun (BitVec 256) Pt)
      (encPt : Pt → CryptoVerification.E2E.Bytes) (encT : Pt → PublicKey)
      (decT : PublicKey → Option Pt)
      (_qep : ℕ) (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
      (δ : ℝ≥0∞) (A : CliGameAdversary S ℓ (BitVec 512)),
      letI : Zero Pt := zPt; letI : SampleableType Pt := sPt
      2 ≤ S.N_id ∧ 0 < S.N_send_tot ∧ 0 < S.N_recv_tot ∧ 0 < ℓ ∧
      0 < qStart ∧ 0 < qs 0 ∧
      CliSpecPqxdh run X W ∧
      MlKemEncaps1SucceedsOn64ByteHeaderAndSeeds W.Q.K ∧
      SignalPqxdh.CryptoWellFormedPrimitivesδ (modelPrims X W) ∧
      SignalPqxdh.KemDeltaCorrect (modelPrims X W) δ_kem ∧
      ℓ < 10 ^ 6 ∧
      Dh.Commutes ∧
      X25519RealizesDh W.C Dh encPt encT ∧
      (∀ T, decT (encT T) = some T) ∧
      (∀ T, encT T ≠ dummyKey) ∧
      (∀ x, Dh.dh x 0 = 0) ∧
      (∀ k x, W.C.D k (W.C.E k x) = x) ∧
      DhKerUniform Dh ∧
      (∀ k < qStart, 2 * (qs k + 1) + 25002 < 2 ^ 32) ∧
      (∀ Q : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ) ∧
      CliGameAdversaryPerInstanceBounded A b qStart qs := by
  let S0 : SignalPqxdh.Setup := ⟨2, 1, 1, 1, 1, 1⟩
  obtain ⟨Pt, dPt, zPt, sPt, run, X, W, δ_kem, Dh, encPt, encT, decT, qep,
      b, qStart, qs, δ, A, hRest⟩ :=
    cli_pq_headline_hypotheses_jointly_satisfiable_of_cli hCliModel S0 32 (by decide)
  exact ⟨S0, 32, Pt, dPt, zPt, sPt, run, X, W, δ_kem, Dh, encPt, encT, decT, qep,
    b, qStart, qs, δ, A, by decide, by decide, by decide, by decide, hRest⟩

/-- Instantiates both conclusion clauses of `LibsignalCliPqSecure` at the `X255`/`W255` witness for
any `pqModelRun` satisfying `CliSpecPqxdh`. -/
theorem libsignalCliPqSecure_instantiable_of_cli
    {pqModelRun : UnreachedPqxdhPrimitives → PEParams → CliRun}
    (hCliModel : ∀ (X : UnreachedPqxdhPrimitives) (W : PEParams), CliSpecPqxdh (pqModelRun X W) X W)
    (S : SignalPqxdh.Setup) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (hSec : LibsignalCliPqSecure (Pt := BitVec 255) S ℓ) :
    ∃ (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams) (qep : ℕ)
      (RK : SignalPqxdh.Security.KeyIndCostedReductionFamily S)
      (b_ki : SignalPqxdh.QueryBudget)
      (A : CliGameAdversary S ℓ (BitVec 512))
      (advK : SignalPqxdh.KeyIndAdversary S)
      (hK : SignalPqxdh.QueryBounded advK b_ki)
      (prefixSum : ℝ≥0∞),
      CliPqxdhAdvantage S run X W ℓ qep decT255 encT255 A ≤
        2 * SignalPqxdh.KeyInd1KeyRealAdvantage S (modelPrims X W) advK +
          prefixSum + SignalPqxdh.Security.kemDecapsFailureTerm S 0 +
          2 * CliKemFailProb S run X W ℓ qep decT255 encT255 A ∧
      CliPqxdhAdvantage S run X W ℓ qep decT255 encT255 A ≤
        2 * (let R := RK.eval
             let Ab : SignalPqxdh.BoundedAdv (SignalPqxdh.KeyIndAdversary S) b_ki := ⟨advK, hK⟩
             SignalPqxdh.Security.pqxdhKeyIndAdvantageBoundActiveδ S b_ki.q_on 0
               (SignalPqxdh.GapSigEufCma (modelPrims X W) (modelPrims X W).isValidDhTriple (R.sig _ Ab))
               (SignalPqxdh.KemShCr (modelPrims X W) (R.shcr _ Ab))
               (SignalPqxdh.GapDhWithSign (modelPrims X W) (modelPrims X W).isValidDhTriple
                 (modelPrims X W).pow8 (R.gdh _ Ab)) + 1)
          + prefixSum + SignalPqxdh.Security.kemDecapsFailureTerm S 0
          + 2 * CliKemFailProb S run X W ℓ qep decT255 encT255 A := by
  rcases hSec with ⟨L_cli, RK, D, R_e2e, _, _, _, _, hMain⟩
  let b1 : SignalPqxdh.QueryBudget := ⟨1, 1, 1, 1⟩
  let A0 : CliGameAdversary S ℓ (BitVec 512) := ⟨pure false⟩
  have hA0 : CliGameAdversaryPerInstanceBounded A0 b1 1 (fun _ => 1) :=
    ⟨⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩, trivial, fun _ _ => trivial⟩
  rcases hMain (pqModelRun X255 W255) X255 W255 (hCliModel X255 W255)
      bhEncaps1Total_W255 modelPrims_X255_cwfδ 0 modelPrims_X255_kemCorrectWith_zero
      dh255 encPt255 encT255 decT255 1 hℓ
      dh255_commutes libX25519Rel_c255 decT255_encT255 encT255_ne_dummyKey
      dh255_zero c255_D_E dh255_kerUniform
      b1 1 (fun _ => 1) (fun _ _ => show 2 * (1 + 1) + 25002 < 2 ^ 32 by decide)
      1 (fun _ => MeasureTheory.prob_le_one) A0 hA0
    with ⟨hK, _, hBound1, hBound2⟩
  exact ⟨pqModelRun X255 W255, X255, W255, 1, RK, keyIndReductionBudget S 1 b1, A0, _, hK, _,
    hBound1, hBound2 1 (SignalPqxdh.keyIndRoGap_one S (modelPrims X255 W255) _)⟩

/-- Unconditional joint satisfiability of all 15 universal hypotheses of `LibsignalCliPqSecure`,
witnessed by `run := pqModelRun X255 W255`. -/
theorem cli_pq_headline_hypotheses_jointly_satisfiable
    (S : SignalPqxdh.Setup) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6) :
    ∃ (Pt : Type) (_ : DecidableEq Pt) (zPt : Zero Pt) (sPt : SampleableType Pt)
      (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams)
      (δ_kem : ℝ≥0∞) (Dh : DHFun (BitVec 256) Pt)
      (encPt : Pt → CryptoVerification.E2E.Bytes) (encT : Pt → PublicKey)
      (decT : PublicKey → Option Pt)
      (_qep : ℕ) (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
      (δ : ℝ≥0∞) (A : CliGameAdversary S ℓ (BitVec 512)),
      letI : Zero Pt := zPt; letI : SampleableType Pt := sPt
      0 < qStart ∧
      0 < qs 0 ∧
      CliSpecPqxdh run X W ∧
      MlKemEncaps1SucceedsOn64ByteHeaderAndSeeds W.Q.K ∧
      SignalPqxdh.CryptoWellFormedPrimitivesδ (modelPrims X W) ∧
      SignalPqxdh.KemDeltaCorrect (modelPrims X W) δ_kem ∧
      ℓ < 10 ^ 6 ∧
      Dh.Commutes ∧
      X25519RealizesDh W.C Dh encPt encT ∧
      (∀ T, decT (encT T) = some T) ∧
      (∀ T, encT T ≠ dummyKey) ∧
      (∀ x, Dh.dh x 0 = 0) ∧
      (∀ k x, W.C.D k (W.C.E k x) = x) ∧
      DhKerUniform Dh ∧
      (∀ k < qStart, 2 * (qs k + 1) + 25002 < 2 ^ 32) ∧
      (∀ Q : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ) ∧
      CliGameAdversaryPerInstanceBounded A b qStart qs :=
  cli_pq_headline_hypotheses_jointly_satisfiable_of_cli cliSpecPq_pqModelRun S ℓ hℓ

/-- Closed concrete-setup (`N_id = 2`, `ℓ = 32`) specialization of
`cli_pq_headline_hypotheses_jointly_satisfiable`. -/
theorem cli_pq_headline_hypotheses_jointly_satisfiable_concrete :
    ∃ (S : SignalPqxdh.Setup) (ℓ : ℕ)
      (Pt : Type) (_ : DecidableEq Pt) (zPt : Zero Pt) (sPt : SampleableType Pt)
      (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams)
      (δ_kem : ℝ≥0∞) (Dh : DHFun (BitVec 256) Pt)
      (encPt : Pt → CryptoVerification.E2E.Bytes) (encT : Pt → PublicKey)
      (decT : PublicKey → Option Pt)
      (_qep : ℕ) (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
      (δ : ℝ≥0∞) (A : CliGameAdversary S ℓ (BitVec 512)),
      letI : Zero Pt := zPt; letI : SampleableType Pt := sPt
      2 ≤ S.N_id ∧ 0 < S.N_send_tot ∧ 0 < S.N_recv_tot ∧ 0 < ℓ ∧
      0 < qStart ∧ 0 < qs 0 ∧
      CliSpecPqxdh run X W ∧
      MlKemEncaps1SucceedsOn64ByteHeaderAndSeeds W.Q.K ∧
      SignalPqxdh.CryptoWellFormedPrimitivesδ (modelPrims X W) ∧
      SignalPqxdh.KemDeltaCorrect (modelPrims X W) δ_kem ∧
      ℓ < 10 ^ 6 ∧
      Dh.Commutes ∧
      X25519RealizesDh W.C Dh encPt encT ∧
      (∀ T, decT (encT T) = some T) ∧
      (∀ T, encT T ≠ dummyKey) ∧
      (∀ x, Dh.dh x 0 = 0) ∧
      (∀ k x, W.C.D k (W.C.E k x) = x) ∧
      DhKerUniform Dh ∧
      (∀ k < qStart, 2 * (qs k + 1) + 25002 < 2 ^ 32) ∧
      (∀ Q : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ) ∧
      CliGameAdversaryPerInstanceBounded A b qStart qs :=
  cli_pq_headline_hypotheses_jointly_satisfiable_concrete_of_cli cliSpecPq_pqModelRun

/-- Instantiates both conclusion clauses of `LibsignalCliPqSecure` unconditionally via
`pqModelRun X255 W255`. -/
theorem libsignalCliPqSecure_instantiable
    (S : SignalPqxdh.Setup) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (hSec : LibsignalCliPqSecure (Pt := BitVec 255) S ℓ) :
    ∃ (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams) (qep : ℕ)
      (RK : SignalPqxdh.Security.KeyIndCostedReductionFamily S)
      (b_ki : SignalPqxdh.QueryBudget)
      (A : CliGameAdversary S ℓ (BitVec 512))
      (advK : SignalPqxdh.KeyIndAdversary S)
      (hK : SignalPqxdh.QueryBounded advK b_ki)
      (prefixSum : ℝ≥0∞),
      CliPqxdhAdvantage S run X W ℓ qep decT255 encT255 A ≤
        2 * SignalPqxdh.KeyInd1KeyRealAdvantage S (modelPrims X W) advK +
          prefixSum + SignalPqxdh.Security.kemDecapsFailureTerm S 0 +
          2 * CliKemFailProb S run X W ℓ qep decT255 encT255 A ∧
      CliPqxdhAdvantage S run X W ℓ qep decT255 encT255 A ≤
        2 * (let R := RK.eval
             let Ab : SignalPqxdh.BoundedAdv (SignalPqxdh.KeyIndAdversary S) b_ki := ⟨advK, hK⟩
             SignalPqxdh.Security.pqxdhKeyIndAdvantageBoundActiveδ S b_ki.q_on 0
               (SignalPqxdh.GapSigEufCma (modelPrims X W) (modelPrims X W).isValidDhTriple (R.sig _ Ab))
               (SignalPqxdh.KemShCr (modelPrims X W) (R.shcr _ Ab))
               (SignalPqxdh.GapDhWithSign (modelPrims X W) (modelPrims X W).isValidDhTriple
                 (modelPrims X W).pow8 (R.gdh _ Ab)) + 1)
          + prefixSum + SignalPqxdh.Security.kemDecapsFailureTerm S 0
          + 2 * CliKemFailProb S run X W ℓ qep decT255 encT255 A :=
  libsignalCliPqSecure_instantiable_of_cli cliSpecPq_pqModelRun S ℓ hℓ hSec

/-- Boundary check on `2 * (qs k + 1) + 25002 < 2 ^ 32`: holds up to `qs k = 2147471145` and fails
at `2147471146`. -/
theorem pq_budget_2000_2001_26816_satisfiable :
    2 * (2000 + 1) + 25002 < 2 ^ 32 ∧
    2 * (2001 + 1) + 25002 < 2 ^ 32 ∧
    2 * (26816 + 1) + 25002 < 2 ^ 32 ∧
    2 * (2147471145 + 1) + 25002 < 2 ^ 32 ∧
    ¬ (2 * (2147471146 + 1) + 25002 < 2 ^ 32) := by decide

end CryptoVerification.E2E
