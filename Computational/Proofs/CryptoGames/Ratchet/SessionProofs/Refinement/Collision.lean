/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.CKA.LibsignalCKA
import ProofLib.Lemmas

/-!
# Ratchet public-key collision bounds

**Checked by Lean.** No theorem of `Computational/Theorems/` unfolds a definition of this file, and
Lean's kernel checks every proof in it: you do not need to read it to trust those theorems.

Union bound (`dh_mem_list_prob_le`) on the probability that an honest ratchet public key
`Dh.dh x Dh.base` collides with a list of points (DEV-LS18).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames.LibsignalSM.Proofs.Refinement

open CryptoGames.CKA

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {Pt : Type} [Zero Pt] [DecidableEq Pt]

theorem dh_mem_list_prob_le (Dh : DHFun (BitVec 256) Pt) (δ : ℝ≥0∞)
    (hδ : ∀ Q : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ)
    (L : List Pt) :
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x => pure (decide (Dh.dh x Dh.base ∈ L))] {true} ≤
      (L.length : ℝ≥0∞) * δ := by
  induction L with
  | nil =>
    simp
  | cons a L ih =>
    have hsub : {x : BitVec 256 | Dh.dh x Dh.base ∈ a :: L} ⊆
        {x : BitVec 256 | Dh.dh x Dh.base = a} ∪ {x : BitVec 256 | Dh.dh x Dh.base ∈ L} := by
      intro x hx
      simpa using hx
    have hmeas : ∀ (P : BitVec 256 → Prop) [DecidablePred P],
        𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x => pure (decide (P x))] {true} =
          𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | P x} := by
      intro P _
      rw [evalDist_bind_of_discrete,
        Measure.bind_apply (MeasurableSet.singleton true) Measurable.of_discrete.aemeasurable]
      calc ∫⁻ x, 𝒟[pure (decide (P x))] {true} ∂𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))]
          = ∫⁻ x, Set.indicator {x | P x} 1 x ∂𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] := by
            refine lintegral_congr fun x => ?_
            by_cases h : P x <;> simp [h]
        _ = 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | P x} :=
            lintegral_indicator_one MeasurableSet.of_discrete
    rw [hmeas (fun x => Dh.dh x Dh.base ∈ a :: L)]
    rw [hmeas (fun x => Dh.dh x Dh.base ∈ L)] at ih
    calc 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base ∈ a :: L}
        ≤ 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))]
            ({x | Dh.dh x Dh.base = a} ∪ {x | Dh.dh x Dh.base ∈ L}) :=
          measure_mono hsub
      _ ≤ 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = a} +
          𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base ∈ L} :=
          measure_union_le _ _
      _ ≤ δ + (L.length : ℝ≥0∞) * δ := add_le_add (hδ a) ih
      _ = ((a :: L).length : ℝ≥0∞) * δ := by
          simp [List.length_cons, add_mul, one_mul, add_comm]

end CryptoGames.LibsignalSM.Proofs.Refinement
