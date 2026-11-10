/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.LibsignalCli.StatementPqElf
import Computational.Tests.NonVacuity.PqHeadlineSatisfiable

@[expose] public section

set_option autoImplicit false

/-!
# Joint Hypothesis Satisfiability for `CliPqxdhRunSecureUpToExcusedAbortTest`

Proves joint satisfiability of all universal hypotheses of `CliPqxdhRunSecureUpToExcusedAbortTest`
(the excused-abort specialization of `CliPqxdhSecurityFor`) and instantiates its conclusion. Lifts
the witness tuple of `cli_pq_headline_hypotheses_jointly_satisfiable` to
`CliSpecPqxdhOrExcusedAbort exc run X W` at the empty excuse predicate `exc := ⊥`.
-/

namespace Computational.Proofs.LibsignalCli.PqOomSatisfiable

open OracleComp OracleSpec
open scoped ENNReal
open CryptoGames.CKA (DHFun)
open CryptoGames.LibsignalSession (PublicKey)
open CryptoGames.Ratchet.LibsignalInst (dummyKey X25519RealizesDh)
open CryptoVerification.SignalSession
  (CliRun Inputs Outcome CliSpecPqxdh OutcomeOrExcusedAbort CliSpecPqxdhOrExcusedAbort)
open CryptoVerification.E2E
  (Bytes UnreachedPqxdhPrimitives PEParams MlKemEncaps1SucceedsOn64ByteHeaderAndSeeds modelPrims DhKerUniform
   CliGameAdversary CliGameAdversaryPerInstanceBounded
   CliPqxdhExcusedAbort CliPqxdhAdvantage CliPqxdhFlagProb CliKemFailProb CliPqxdhSecurityFor
   cli_pq_headline_hypotheses_jointly_satisfiable)

/-- Excused-abort (`some exc`) specialization of `CliPqxdhSecurityFor`. -/
abbrev CliPqxdhRunSecureUpToExcusedAbortTest {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (S : SignalPqxdh.Setup) (ℓ : ℕ) : Prop :=
  CliPqxdhSecurityFor (Pt := Pt) S ℓ fun Bound =>
    ∀ (exc : Inputs → Prop) (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams)
      (_hCli : CliSpecPqxdhOrExcusedAbort exc run X W),
      Bound run X W (some exc)

private theorem outcomeUpTo_of_eq {exc : Inputs → Prop} {run : CliRun} {i : Inputs} {e : Outcome}
    (h : run i = some e) : OutcomeOrExcusedAbort exc run i (· = e) :=
  Or.inl ⟨e, h, rfl⟩

private theorem some_ite_eq {α : Type} (p : Prop) [Decidable p] (a b : α) :
    (if p then some a else some b) = some (if p then a else b) := by
  by_cases hp : p <;> simp [hp]

private theorem some_ite2_eq {α : Type} (p q : Prop) [Decidable p] [Decidable q] (a b c : α) :
    (if p then some a else if q then some b else some c) =
      some (if p then a else if q then b else c) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

private theorem cliSpecPqUpTo_of_cliSpecPq (exc : Inputs → Prop) {run : CliRun}
    {X : UnreachedPqxdhPrimitives} {W : PEParams} (h : CliSpecPqxdh run X W) :
    CliSpecPqxdhOrExcusedAbort exc run X W := by
  intro st hst
  obtain ⟨hInit, hSend, hWhisper, hPrekey, hBad⟩ := h st hst
  exact ⟨fun b t hnone => outcomeUpTo_of_eq (hInit b t hnone),
    fun m r hm => outcomeUpTo_of_eq ((hSend m r hm).trans (some_ite2_eq _ _ _ _ _)),
    fun c rc hc => outcomeUpTo_of_eq ((hWhisper c rc hc).trans (some_ite_eq _ _ _)),
    fun m rc h1 h2 => outcomeUpTo_of_eq ((hPrekey m rc h1 h2).trans (some_ite_eq _ _ _)),
    fun c rc h1 h2 h3 => outcomeUpTo_of_eq ((hBad c rc h1 h2 h3).trans (some_ite_eq _ _ _))⟩

/-- Joint satisfiability of all universal hypotheses of `CliPqxdhRunSecureUpToExcusedAbortTest` with
`0 < qStart` and `0 < qs 0`, for every `S` and `ℓ < 10 ^ 6`. -/
theorem pqOom_hypotheses_satisfiable_for
    (S : SignalPqxdh.Setup) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6) :
    ∃ (Pt : Type) (_ : DecidableEq Pt) (zPt : Zero Pt) (sPt : SampleableType Pt)
      (exc : Inputs → Prop) (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams)
      (δ_kem : ℝ≥0∞) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
      (decT : PublicKey → Option Pt) (_qep : ℕ)
      (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ) (δ : ℝ≥0∞)
      (A : CliGameAdversary S ℓ (BitVec 512)),
      letI : Zero Pt := zPt; letI : SampleableType Pt := sPt
      0 < qStart ∧
      0 < qs 0 ∧
      CliSpecPqxdhOrExcusedAbort exc run X W ∧
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
  obtain ⟨Pt, dPt, zPt, sPt, run, X, W, δ_kem, Dh, encPt, encT, decT, qep,
      b, qStart, qs, δ, A, hqStart, hqs0, hCli, hRest⟩ :=
    cli_pq_headline_hypotheses_jointly_satisfiable S ℓ hℓ
  exact ⟨Pt, dPt, zPt, sPt, ⊥, run, X, W, δ_kem, Dh, encPt, encT, decT, qep,
    b, qStart, qs, δ, A, hqStart, hqs0, cliSpecPqUpTo_of_cliSpecPq ⊥ hCli, hRest⟩

/-- Closed concrete-setup (`N_id = 2`, `ℓ = 32`) specialization of `pqOom_hypotheses_satisfiable_for`. -/
theorem pqOom_hypotheses_satisfiable :
    ∃ (S : SignalPqxdh.Setup) (ℓ : ℕ)
      (Pt : Type) (_ : DecidableEq Pt) (zPt : Zero Pt) (sPt : SampleableType Pt)
      (exc : Inputs → Prop) (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams)
      (δ_kem : ℝ≥0∞) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
      (decT : PublicKey → Option Pt) (_qep : ℕ)
      (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ) (δ : ℝ≥0∞)
      (A : CliGameAdversary S ℓ (BitVec 512)),
      letI : Zero Pt := zPt; letI : SampleableType Pt := sPt
      CliSpecPqxdhOrExcusedAbort exc run X W ∧
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
  obtain ⟨Pt, dPt, zPt, sPt, exc, run, X, W, δ_kem, Dh, encPt, encT, decT, qep,
      b, qStart, qs, δ, A, _, _, hAll⟩ :=
    pqOom_hypotheses_satisfiable_for S0 32 (by decide)
  exact ⟨S0, 32, Pt, dPt, zPt, sPt, exc, run, X, W, δ_kem, Dh, encPt, encT, decT, qep,
    b, qStart, qs, δ, A, hAll⟩

/-- Instantiates the conclusion of `CliPqxdhRunSecureUpToExcusedAbortTest` at the witness from
`pqOom_hypotheses_satisfiable_for`. -/
theorem libsignalCliPqSecureOom_instantiable
    (S : SignalPqxdh.Setup) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (hSec : ∀ (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt],
      CliPqxdhRunSecureUpToExcusedAbortTest (Pt := Pt) S ℓ) :
    ∃ (Pt : Type) (_ : DecidableEq Pt) (_ : Zero Pt) (_ : SampleableType Pt)
      (exc : Inputs → Prop) (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams)
      (δ_kem : ℝ≥0∞) (qep : ℕ) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
      (A : CliGameAdversary S ℓ (BitVec 512))
      (advK : SignalPqxdh.KeyIndAdversary S) (prefixSum : ℝ≥0∞),
      CliPqxdhAdvantage S run X W ℓ qep decT encT A ≤
        2 * SignalPqxdh.KeyInd1KeyRealAdvantage S (modelPrims X W) advK +
          prefixSum + SignalPqxdh.Security.kemDecapsFailureTerm S δ_kem +
          2 * CliKemFailProb S run X W ℓ qep decT encT A +
          2 * CliPqxdhFlagProb S run X W ℓ qep decT encT A (CliPqxdhExcusedAbort exc run W) := by
  obtain ⟨Pt, dPt, zPt, sPt, exc, run, X, W, δ_kem, Dh, encPt, encT, decT, qep,
      b, qStart, qs, δ, A, _, _,
      hCli, hK_tot, hP, hKemBin, hℓ', hDh, hX, hdec, hdum, hz, hD, hkerAll,
      hq32, hδ, hA⟩ :=
    pqOom_hypotheses_satisfiable_for S ℓ hℓ
  let _ : DecidableEq Pt := dPt
  let _ : Zero Pt := zPt
  let _ : SampleableType Pt := sPt
  rcases hSec Pt with ⟨L_cli, RK, D, R_e2e, _, _, _, _, hMain⟩
  rcases hMain exc run X W hCli hK_tot hP δ_kem hKemBin Dh encPt encT decT qep hℓ'
      hDh hX hdec hdum hz hD hkerAll b qStart qs hq32 δ hδ A hA
    with ⟨_, _, hBound1, _⟩
  exact ⟨Pt, dPt, zPt, sPt, exc, run, X, W, δ_kem, qep, decT, encT, A, _, _, hBound1⟩

end Computational.Proofs.LibsignalCli.PqOomSatisfiable
