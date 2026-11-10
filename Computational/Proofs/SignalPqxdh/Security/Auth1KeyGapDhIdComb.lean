/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyGapDhIdA
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyGapDhRestCaseC
public import Computational.Proofs.SignalPqxdh.Security.FgGapDh1KeyPre
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.EvalDist.Measure

/-!
# One-key `Auth` `G3 → G3.5` Case A + Case C combiner

**Checked by Lean.** Combines the per-index Case A (`DH1`) and Case C (`DH3`) `GapDhWithSign`
bounds into the union bound for `badAuthFgAnyLatched` on `runAuthFgLatchedSim1Key` against the
mixture reduction `fgAuth1KeyGapDhAdv4`.
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal BigOperators
open MeasureTheory
open SignalPqxdh SignalPqxdh.Security
open OracleSpec OracleComp
open Proofs.SignalPqxdh.Security.FgGapDh
open Proofs.SignalPqxdh.Security.FgGapDh1Key

namespace Proofs.SignalPqxdh.Security

theorem evalDist_gapDhWithSignExp_fgAuth1KeyGapDhAdv4_eq (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (pow8 : Bytes → Bytes)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    𝒟[gapDhWithSignExp P ddh pow8 (fgAuth1KeyGapDhAdv4 S b A)] =
    𝒟[sampleIndexRange2 (S.N_id + S.N_send_tot) S.N_spk_tot >>= fun p =>
        if p.1 < S.N_id then
          gapDhWithSignExp P ddh pow8 (fgAuth1KeyGapDhAdvAt true p.1 p.2 S b A)
        else
          gapDhWithSignExp P ddh pow8
            (fgAuth1KeyGapDhAdvAt false (p.1 - S.N_id) p.2 S b A)] := by
  have hStep1 :
      gapDhWithSignExp P ddh pow8 (fgAuth1KeyGapDhAdv4 S b A) =
      (do
        let u ← sampleScalar32
        let v ← sampleScalar32
        let p ← sampleIndexRange2 (S.N_id + S.N_send_tot) S.N_spk_tot
        let Z ← simulateQ (gapDhWithSignFullImpl P u ddh)
          (if p.1 < S.N_id then
            fgAuth1KeyGapDhRunAt true p.1 p.2 S b A (P.x25519Base u) (P.x25519Base v)
          else
            fgAuth1KeyGapDhRunAt false (p.1 - S.N_id) p.2 S b A (P.x25519Base u)
              (P.x25519Base v))
        return (pow8 Z == pow8 (P.x25519 u (P.x25519Base v)))) := by
    unfold gapDhWithSignExp fgAuth1KeyGapDhAdv4
    congr 1; ext u; congr 1; ext v
    change (simulateQ (gapDhWithSignFullImpl P u ddh)
        (unifGdhSign (sampleIndexRange2 (S.N_id + S.N_send_tot) S.N_spk_tot) >>= fun p =>
          if p.1 < S.N_id then
            fgAuth1KeyGapDhRunAt true p.1 p.2 S b A (P.x25519Base u) (P.x25519Base v)
          else
            fgAuth1KeyGapDhRunAt false (p.1 - S.N_id) p.2 S b A (P.x25519Base u)
              (P.x25519Base v)) >>=
      fun Z => pure (pow8 Z == pow8 (P.x25519 u (P.x25519Base v)))) = _
    rw [simulateQ_bind, simulateQ_gapDhWithSignFullImpl_unifGdhSign, bind_assoc]
  rw [hStep1]
  have hSwap1 :
      𝒟[do
        let u ← sampleScalar32
        let v ← sampleScalar32
        let p ← sampleIndexRange2 (S.N_id + S.N_send_tot) S.N_spk_tot
        let Z ← simulateQ (gapDhWithSignFullImpl P u ddh)
          (if p.1 < S.N_id then
            fgAuth1KeyGapDhRunAt true p.1 p.2 S b A (P.x25519Base u) (P.x25519Base v)
          else
            fgAuth1KeyGapDhRunAt false (p.1 - S.N_id) p.2 S b A (P.x25519Base u)
              (P.x25519Base v))
        return (pow8 Z == pow8 (P.x25519 u (P.x25519Base v)))] =
      𝒟[do
        let u ← sampleScalar32
        let p ← sampleIndexRange2 (S.N_id + S.N_send_tot) S.N_spk_tot
        let v ← sampleScalar32
        let Z ← simulateQ (gapDhWithSignFullImpl P u ddh)
          (if p.1 < S.N_id then
            fgAuth1KeyGapDhRunAt true p.1 p.2 S b A (P.x25519Base u) (P.x25519Base v)
          else
            fgAuth1KeyGapDhRunAt false (p.1 - S.N_id) p.2 S b A (P.x25519Base u)
              (P.x25519Base v))
        return (pow8 Z == pow8 (P.x25519 u (P.x25519Base v)))] := by
    refine OracleComp.evalDist_bind_congr_of_support sampleScalar32 _ _ (fun u _ => ?_)
    exact OracleComp.evalDist_bind_bind_swap sampleScalar32
      (sampleIndexRange2 (S.N_id + S.N_send_tot) S.N_spk_tot) _
  rw [hSwap1, OracleComp.evalDist_bind_bind_swap sampleScalar32
    (sampleIndexRange2 (S.N_id + S.N_send_tot) S.N_spk_tot)]
  refine OracleComp.evalDist_bind_congr_of_support
    (sampleIndexRange2 (S.N_id + S.N_send_tot) S.N_spk_tot) _ _ (fun p _ => ?_)
  by_cases hp : p.1 < S.N_id
  · simp only [hp, ↓reduceIte]; rfl
  · simp only [hp, ↓reduceIte]; rfl

theorem sum_gapDhWithSign_fgAuth1KeyGapDhAdvAt_eq (S : Setup) (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (pow8 : Bytes → Bytes)
    (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    (∑ u ∈ Finset.range S.N_id, ∑ bIdx ∈ Finset.range S.N_spk_tot,
      GapDhWithSignReal P ddh pow8 (fgAuth1KeyGapDhAdvAt true u bIdx S b A)) +
    (∑ idx ∈ Finset.range S.N_send_tot, ∑ bIdx ∈ Finset.range S.N_spk_tot,
      GapDhWithSignReal P ddh pow8 (fgAuth1KeyGapDhAdvAt false idx bIdx S b A)) =
    (S.N_spk_tot : ℝ) * ((S.N_id : ℝ) + (S.N_send_tot : ℝ)) *
      GapDhWithSignReal P ddh pow8 (fgAuth1KeyGapDhAdv4 S b A) := by
  have hExp := evalDist_gapDhWithSignExp_fgAuth1KeyGapDhAdv4_eq P ddh pow8 S b A
  have hDouble := mul_toReal_sampleIndexRange2_bind_eq_double_sum_fg
    (S.N_id + S.N_send_tot) S.N_spk_tot
    (fun flatIdx bIdx =>
      if flatIdx < S.N_id then
        gapDhWithSignExp P ddh pow8 (fgAuth1KeyGapDhAdvAt true flatIdx bIdx S b A)
      else
        gapDhWithSignExp P ddh pow8 (fgAuth1KeyGapDhAdvAt false (flatIdx - S.N_id) bIdx S b A))
  have hRhs :
      (S.N_spk_tot : ℝ) * ((S.N_id : ℝ) + (S.N_send_tot : ℝ)) *
        GapDhWithSignReal P ddh pow8 (fgAuth1KeyGapDhAdv4 S b A) =
      ∑ flatIdx ∈ Finset.range (S.N_id + S.N_send_tot), ∑ bIdx ∈ Finset.range S.N_spk_tot,
        (𝒟[if flatIdx < S.N_id then
            gapDhWithSignExp P ddh pow8 (fgAuth1KeyGapDhAdvAt true flatIdx bIdx S b A)
          else
            gapDhWithSignExp P ddh pow8
              (fgAuth1KeyGapDhAdvAt false (flatIdx - S.N_id) bIdx S b A)] {true}).toReal := by
    unfold GapDhWithSignReal GapDhWithSign; rw [hExp, ← hDouble]; push_cast; ring
  rw [hRhs, Finset.sum_range_add]
  congr 1
  · refine Finset.sum_congr rfl (fun u hu => Finset.sum_congr rfl (fun bIdx _ => ?_))
    rw [Finset.mem_range] at hu; simp [hu, GapDhWithSignReal, GapDhWithSign]
  · refine Finset.sum_congr rfl (fun idx _ => Finset.sum_congr rfl (fun bIdx _ => ?_))
    have hnot : ¬ (S.N_id + idx < S.N_id) := by omega
    simp [hnot, GapDhWithSignReal, GapDhWithSign]

theorem prob_badAuthFgAnyLatched_1Key_le_gapDhWithSign_of_dh1_dh3 {S : Setup} (b : QueryBudget)
    (P : Primitives) (A : BoundedAdv (AuthAdversary S) b)
    {α : Type} (mx : ProbComp α) (proj : α → AuthFgCutoffState S)
    (hDh1 : ∀ uIdx ∈ Finset.range S.N_id, ∀ bIdx ∈ Finset.range S.N_spk_tot,
      (𝒟[mx >>= fun x =>
          pure (badAuthFgDh1LatchedAt P b.q_ro uIdx bIdx (proj x))] {true}).toReal ≤
        GapDhWithSignReal P P.isValidDhTriple P.pow8 (fgAuth1KeyGapDhAdvAt true uIdx bIdx S b A))
    (hDh3 : ∀ sIdx ∈ Finset.range S.N_send_tot, ∀ bIdx ∈ Finset.range S.N_spk_tot,
      (𝒟[mx >>= fun x =>
          pure (badAuthFgDh3At P b.q_ro sIdx bIdx
            (proj x).base (proj x).advRoLog (proj x).respRecs)] {true}).toReal ≤
        GapDhWithSignReal P P.isValidDhTriple P.pow8 (fgAuth1KeyGapDhAdvAt false sIdx bIdx S b A)) :
    (𝒟[mx >>= fun x => pure (badAuthFgAnyLatched P b.q_ro (proj x))] {true}).toReal ≤
      ((S.N_spk_tot : ℝ) * ((S.N_id : ℝ) + (S.N_send_tot : ℝ)) +
        (S.N_id : ℝ) * (S.N_send_tot : ℝ) +
        (S.N_opk_tot : ℝ) * (S.N_send_opk_tot : ℝ)) *
        GapDhWithSignReal P P.isValidDhTriple P.pow8 (fgAuth1KeyGapDhAdv4 S b A) := by
  have hUnion := prob_badAuthFgAnyLatched_le_sum P b.q_ro mx proj
  have hSumDh1 :
      (∑ uIdx ∈ Finset.range S.N_id, ∑ bIdx ∈ Finset.range S.N_spk_tot,
        (𝒟[mx >>= fun x =>
          pure (badAuthFgDh1LatchedAt P b.q_ro uIdx bIdx (proj x))] {true}).toReal) ≤
      (∑ uIdx ∈ Finset.range S.N_id, ∑ bIdx ∈ Finset.range S.N_spk_tot,
        GapDhWithSignReal P P.isValidDhTriple P.pow8 (fgAuth1KeyGapDhAdvAt true uIdx bIdx S b A)) :=
    Finset.sum_le_sum (fun uIdx huIdx =>
      Finset.sum_le_sum (fun bIdx hbIdx => hDh1 uIdx huIdx bIdx hbIdx))
  have hSumDh3 :
      (∑ sIdx ∈ Finset.range S.N_send_tot, ∑ bIdx ∈ Finset.range S.N_spk_tot,
        (𝒟[mx >>= fun x =>
          pure (badAuthFgDh3At P b.q_ro sIdx bIdx
            (proj x).base (proj x).advRoLog (proj x).respRecs)] {true}).toReal) ≤
      (∑ sIdx ∈ Finset.range S.N_send_tot, ∑ bIdx ∈ Finset.range S.N_spk_tot,
        GapDhWithSignReal P P.isValidDhTriple P.pow8 (fgAuth1KeyGapDhAdvAt false sIdx bIdx S b A)) :=
    Finset.sum_le_sum (fun sIdx hsIdx =>
      Finset.sum_le_sum (fun bIdx hbIdx => hDh3 sIdx hsIdx bIdx hbIdx))
  have hEq := sum_gapDhWithSign_fgAuth1KeyGapDhAdvAt_eq S P P.isValidDhTriple P.pow8 b A
  have hNonnegGdh : 0 ≤ GapDhWithSignReal P P.isValidDhTriple P.pow8 (fgAuth1KeyGapDhAdv4 S b A) :=
    ENNReal.toReal_nonneg
  have hExtraNonneg : 0 ≤ ((S.N_id : ℝ) * (S.N_send_tot : ℝ) +
      (S.N_opk_tot : ℝ) * (S.N_send_opk_tot : ℝ)) *
      GapDhWithSignReal P P.isValidDhTriple P.pow8 (fgAuth1KeyGapDhAdv4 S b A) := by
    positivity
  linarith

theorem prob_badAuthFgAnyLatched_1Key_le_gapDhWithSign_of_dh3 (S : Setup)
    (b : QueryBudget) (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (A : BoundedAdv (AuthAdversary S) b)
    (hDh3 : ∀ sIdx ∈ Finset.range S.N_send_tot, ∀ bIdx ∈ Finset.range S.N_spk_tot,
      (𝒟[runAuthFgLatchedSim1Key S P A.1 >>= fun x =>
          pure (badAuthFgDh3At P b.q_ro sIdx bIdx
            x.2.2.base x.2.2.advRoLog x.2.2.respRecs)] {true}).toReal ≤
        GapDhWithSignReal P P.isValidDhTriple P.pow8 (fgAuth1KeyGapDhAdvAt false sIdx bIdx S b A)) :
    (𝒟[runAuthFgLatchedSim1Key S P A.1 >>= fun x =>
        pure (badAuthFgAnyLatched P b.q_ro x.2.2)] {true}).toReal ≤
      ((S.N_spk_tot : ℝ) * ((S.N_id : ℝ) + (S.N_send_tot : ℝ)) +
        (S.N_id : ℝ) * (S.N_send_tot : ℝ) +
        (S.N_opk_tot : ℝ) * (S.N_send_opk_tot : ℝ)) *
        GapDhWithSignReal P P.isValidDhTriple P.pow8 (fgAuth1KeyGapDhAdv4 S b A) :=
  prob_badAuthFgAnyLatched_1Key_le_gapDhWithSign_of_dh1_dh3 b P A
    (runAuthFgLatchedSim1Key S P A.1) (fun x => x.2.2)
    (fun uIdx huIdx bIdx hbIdx =>
      prob_badAuthFgDh1LatchedAt_1Key_le_gapDhWithSign S b P hP A uIdx huIdx bIdx hbIdx)
    hDh3

/-- Bounds `badAuthFgAnyLatched` in `runAuthFgLatchedSim1Key` by the `GapDhWithSign` advantage of
`fgAuth1KeyGapDhAdv4`. -/
theorem prob_badAuthFgAnyLatched_runAuthFgLatchedSim1Key_le_gapDhWithSign (S : Setup)
    (b : QueryBudget) (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (A : BoundedAdv (AuthAdversary S) b) :
    (𝒟[runAuthFgLatchedSim1Key S P A.1 >>= fun x =>
        pure (badAuthFgAnyLatched P b.q_ro x.2.2)] {true}).toReal ≤
      ((S.N_spk_tot : ℝ) * ((S.N_id : ℝ) + (S.N_send_tot : ℝ)) +
        (S.N_id : ℝ) * (S.N_send_tot : ℝ) +
        (S.N_opk_tot : ℝ) * (S.N_send_opk_tot : ℝ)) *
        GapDhWithSignReal P P.isValidDhTriple P.pow8 (fgAuth1KeyGapDhAdv4 S b A) :=
  prob_badAuthFgAnyLatched_1Key_le_gapDhWithSign_of_dh3 S b P hP A
    (fun sIdx hsIdx bIdx hbIdx =>
      prob_badAuthFgDh3At_1Key_le_gapDhWithSign S b P hP A sIdx hsIdx bIdx hbIdx)

end Proofs.SignalPqxdh.Security
