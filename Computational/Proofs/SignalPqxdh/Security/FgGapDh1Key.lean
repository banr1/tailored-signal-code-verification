/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.FgGapDh1KeyCD
public import Computational.Proofs.SignalPqxdh.Security.FgGapDh1KeyA
public import Computational.Proofs.SignalPqxdh.Security.FgGapDh1KeyB
public import Computational.Proofs.SignalPqxdh.Security.FgGapDhCoupling
public import Computational.Specifications.Assumptions.KeyInd1KeyRo
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.EvalDist.Measure
import VCVio.CryptoFoundations.SecExp.Measure

/-!
# One-Key Hop 4: Lazy-Cache Coupling and `GapDhWithSign` Union Bound

**Checked by Lean.** Combines the four per-slot one-key `GapDhWithSign` leg bounds (Cases A, B, C,
and D) with the one-key `G3 -> G3.5` lazy-cache coupling to bound `keyIndAdvG3_1Key`.
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal BigOperators
open MeasureTheory
open OracleSpec OracleComp
open SignalPqxdh SignalPqxdh.Security SignalPqxdh.Security.FgGapDh SignalPqxdh.Security.FgGapDh1Key
open Proofs.SignalPqxdh.Security
open Proofs.SignalPqxdh.Security.FgGapDh
open Proofs.SignalPqxdh.Security.FgGapDh.Ik
open Proofs.SignalPqxdh.Security.FgGapDh.Opk
open Proofs.SignalPqxdh.Security.FgGapDh1Key

namespace Proofs.SignalPqxdh.Security

/-! ## Index-Averaging and Four-Leg Union Bound -/

theorem evalDist_gapDhWithSignExp_fgKeyInd1KeyGapDhAdv4_eq (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (pow8 : Bytes → Bytes)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    𝒟[gapDhWithSignExp P ddh pow8 (fgKeyInd1KeyGapDhAdv4 S b A)] =
    𝒟[FgGapDh.sampleIndexRange (fgTotalIndexCount S) >>= fun idx =>
        gapDhWithSignExp P ddh pow8 (fgKeyInd1KeyGapDhAdvAtFlat idx S b A)] := by
  have hStep1 :
      gapDhWithSignExp P ddh pow8 (fgKeyInd1KeyGapDhAdv4 S b A) =
      (do
        let u ← sampleScalar32
        let v ← sampleScalar32
        let idx ← FgGapDh.sampleIndexRange (fgTotalIndexCount S)
        let Z ← simulateQ (gapDhWithSignFullImpl P u ddh)
          (fgKeyInd1KeyGapDhRunAtFlat idx S b A (P.x25519Base u) (P.x25519Base v))
        return (pow8 Z == pow8 (P.x25519 u (P.x25519Base v)))) := by
    unfold gapDhWithSignExp fgKeyInd1KeyGapDhAdv4
    congr 1; ext u; congr 1; ext v
    change (simulateQ (gapDhWithSignFullImpl P u ddh)
        (unifGdhSign (FgGapDh.sampleIndexRange (fgTotalIndexCount S)) >>= fun idx =>
          fgKeyInd1KeyGapDhRunAtFlat idx S b A (P.x25519Base u) (P.x25519Base v)) >>=
      fun Z => pure (pow8 Z == pow8 (P.x25519 u (P.x25519Base v)))) = _
    rw [simulateQ_bind, simulateQ_gapDhWithSignFullImpl_unifGdhSign, bind_assoc]
  rw [hStep1]
  have hSwap1 :
      𝒟[do
        let u ← sampleScalar32
        let v ← sampleScalar32
        let idx ← FgGapDh.sampleIndexRange (fgTotalIndexCount S)
        let Z ← simulateQ (gapDhWithSignFullImpl P u ddh)
          (fgKeyInd1KeyGapDhRunAtFlat idx S b A (P.x25519Base u) (P.x25519Base v))
        return (pow8 Z == pow8 (P.x25519 u (P.x25519Base v)))] =
      𝒟[do
        let u ← sampleScalar32
        let idx ← FgGapDh.sampleIndexRange (fgTotalIndexCount S)
        let v ← sampleScalar32
        let Z ← simulateQ (gapDhWithSignFullImpl P u ddh)
          (fgKeyInd1KeyGapDhRunAtFlat idx S b A (P.x25519Base u) (P.x25519Base v))
        return (pow8 Z == pow8 (P.x25519 u (P.x25519Base v)))] := by
    refine OracleComp.evalDist_bind_congr_of_support sampleScalar32 _ _ (fun u _ => ?_)
    exact OracleComp.evalDist_bind_bind_swap sampleScalar32
      (FgGapDh.sampleIndexRange (fgTotalIndexCount S)) _
  rw [hSwap1, OracleComp.evalDist_bind_bind_swap sampleScalar32
    (FgGapDh.sampleIndexRange (fgTotalIndexCount S))]
  rfl

theorem gapDhWithSign_congr_run (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (pow8 : Bytes → Bytes)
    {adv1 adv2 : GapDhWithSignAdv} (h : adv1.run = adv2.run) :
    GapDhWithSignReal P ddh pow8 adv1 = GapDhWithSignReal P ddh pow8 adv2 := by
  unfold GapDhWithSignReal GapDhWithSign gapDhWithSignExp
  rw [h]

theorem sum_gapDhWithSign_fgKeyInd1KeyGapDhAdv4_eq (S : Setup) (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (pow8 : Bytes → Bytes)
    (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    (∑ u ∈ Finset.range S.N_id, ∑ bIdx ∈ Finset.range S.N_spk_tot,
      GapDhWithSignReal P ddh pow8 (fgKeyInd1KeyGapDhAdvAt true u bIdx S b A)) +
    (∑ idx ∈ Finset.range S.N_send_tot, ∑ bIdx ∈ Finset.range S.N_spk_tot,
      GapDhWithSignReal P ddh pow8 (fgKeyInd1KeyGapDhAdvAt false idx bIdx S b A)) +
    (∑ sIdx ∈ Finset.range S.N_send_tot, ∑ kIdx ∈ Finset.range S.N_id,
      GapDhWithSignReal P ddh pow8 (fgKeyInd1KeyGapDhAdvAtIk sIdx kIdx S b A)) +
    (∑ sIdx ∈ Finset.range S.N_send_opk_tot, ∑ oIdx ∈ Finset.range S.N_opk_tot,
      GapDhWithSignReal P ddh pow8 (fgKeyInd1KeyGapDhAdvAtOpk sIdx oIdx S b A)) =
    ((S.N_spk_tot : ℝ) * ((S.N_id : ℝ) + (S.N_send_tot : ℝ)) +
      (S.N_id : ℝ) * (S.N_send_tot : ℝ) +
      (S.N_opk_tot : ℝ) * (S.N_send_opk_tot : ℝ)) *
      GapDhWithSignReal P ddh pow8 (fgKeyInd1KeyGapDhAdv4 S b A) := by
  have hExp := evalDist_gapDhWithSignExp_fgKeyInd1KeyGapDhAdv4_eq P ddh pow8 S b A
  have hSum := FgGapDh.mul_toReal_sampleIndexRange_bind_eq_sum_fg (fgTotalIndexCount S)
    (fun idx => gapDhWithSignExp P ddh pow8 (fgKeyInd1KeyGapDhAdvAtFlat idx S b A))
  have hRhs :
      ((S.N_spk_tot : ℝ) * ((S.N_id : ℝ) + (S.N_send_tot : ℝ)) +
        (S.N_id : ℝ) * (S.N_send_tot : ℝ) +
        (S.N_opk_tot : ℝ) * (S.N_send_opk_tot : ℝ)) *
        GapDhWithSignReal P ddh pow8 (fgKeyInd1KeyGapDhAdv4 S b A) =
      ∑ idx ∈ Finset.range (fgTotalIndexCount S),
        GapDhWithSignReal P ddh pow8 (fgKeyInd1KeyGapDhAdvAtFlat idx S b A) := by
    unfold GapDhWithSignReal GapDhWithSign
    rw [hExp, ← hSum]
    unfold fgTotalIndexCount
    push_cast
    ring
  rw [hRhs]
  unfold fgTotalIndexCount
  rw [Finset.sum_range_add, Finset.sum_range_add, Finset.sum_range_add]
  have h1 : ∑ x ∈ Finset.range (S.N_id * S.N_spk_tot),
      GapDhWithSignReal P ddh pow8 (fgKeyInd1KeyGapDhAdvAtFlat x S b A) =
      ∑ u ∈ Finset.range S.N_id, ∑ bIdx ∈ Finset.range S.N_spk_tot,
        GapDhWithSignReal P ddh pow8 (fgKeyInd1KeyGapDhAdvAt true u bIdx S b A) := by
    rw [← sum_range_mul_div_mod]
    refine Finset.sum_congr rfl (fun x hx => gapDhWithSign_congr_run P ddh pow8 ?_)
    rw [Finset.mem_range] at hx
    funext U V
    dsimp only [fgKeyInd1KeyGapDhAdvAtFlat, fgKeyInd1KeyGapDhAdvAt, fgKeyInd1KeyGapDhRunAtFlat]
    simp only [hx, ↓reduceIte]
  have h2 : ∑ x ∈ Finset.range (S.N_send_tot * S.N_spk_tot),
      GapDhWithSignReal P ddh pow8 (fgKeyInd1KeyGapDhAdvAtFlat (S.N_id * S.N_spk_tot + x) S b A) =
      ∑ idx ∈ Finset.range S.N_send_tot, ∑ bIdx ∈ Finset.range S.N_spk_tot,
        GapDhWithSignReal P ddh pow8 (fgKeyInd1KeyGapDhAdvAt false idx bIdx S b A) := by
    rw [← sum_range_mul_div_mod]
    refine Finset.sum_congr rfl (fun x hx => gapDhWithSign_congr_run P ddh pow8 ?_)
    rw [Finset.mem_range] at hx
    funext U V
    dsimp only [fgKeyInd1KeyGapDhAdvAtFlat, fgKeyInd1KeyGapDhAdvAt, fgKeyInd1KeyGapDhRunAtFlat]
    have hNot1 : ¬ (S.N_id * S.N_spk_tot + x < S.N_id * S.N_spk_tot) := by omega
    have hlt2 : S.N_id * S.N_spk_tot + x < S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot := by
      omega
    simp only [hNot1, hlt2, ↓reduceIte, Nat.add_sub_cancel_left]
  have h3 : ∑ x ∈ Finset.range (S.N_send_tot * S.N_id),
      GapDhWithSignReal P ddh pow8
        (fgKeyInd1KeyGapDhAdvAtFlat (S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot + x) S b A) =
      ∑ sIdx ∈ Finset.range S.N_send_tot, ∑ kIdx ∈ Finset.range S.N_id,
        GapDhWithSignReal P ddh pow8 (fgKeyInd1KeyGapDhAdvAtIk sIdx kIdx S b A) := by
    rw [← sum_range_mul_div_mod]
    refine Finset.sum_congr rfl (fun x hx => gapDhWithSign_congr_run P ddh pow8 ?_)
    rw [Finset.mem_range] at hx
    funext U V
    dsimp only [fgKeyInd1KeyGapDhAdvAtFlat, fgKeyInd1KeyGapDhAdvAtIk, fgKeyInd1KeyGapDhRunAtFlat]
    have hNot1 : ¬ (S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot + x < S.N_id * S.N_spk_tot) :=
      by omega
    have hNot2 : ¬ (S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot + x <
        S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot) := by omega
    have hlt3 : S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot + x <
        S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot + S.N_send_tot * S.N_id := by omega
    simp only [hNot1, hNot2, hlt3, ↓reduceIte, Nat.add_sub_cancel_left]
  have h4 : ∑ x ∈ Finset.range (S.N_send_opk_tot * S.N_opk_tot),
      GapDhWithSignReal P ddh pow8
        (fgKeyInd1KeyGapDhAdvAtFlat
          (S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot + S.N_send_tot * S.N_id + x) S b A) =
      ∑ sIdx ∈ Finset.range S.N_send_opk_tot, ∑ oIdx ∈ Finset.range S.N_opk_tot,
        GapDhWithSignReal P ddh pow8 (fgKeyInd1KeyGapDhAdvAtOpk sIdx oIdx S b A) := by
    rw [← sum_range_mul_div_mod]
    refine Finset.sum_congr rfl (fun x hx => gapDhWithSign_congr_run P ddh pow8 ?_)
    rw [Finset.mem_range] at hx
    funext U V
    dsimp only [fgKeyInd1KeyGapDhAdvAtFlat, fgKeyInd1KeyGapDhAdvAtOpk, fgKeyInd1KeyGapDhRunAtFlat]
    have hNot1 : ¬ (S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot + S.N_send_tot * S.N_id + x <
        S.N_id * S.N_spk_tot) := by omega
    have hNot2 : ¬ (S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot + S.N_send_tot * S.N_id + x <
        S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot) := by omega
    have hNot3 : ¬ (S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot + S.N_send_tot * S.N_id + x <
        S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot + S.N_send_tot * S.N_id) := by omega
    simp only [hNot1, hNot2, hNot3, ↓reduceIte, Nat.add_sub_cancel_left]
  rw [h1, h2, h3, h4]

/-- Four-leg union bound on `runKeyIndFgSim1Key`: bounds `Pr[badKeyIndFgAny4]` in the one-key
    simulation by `fgTotalIndexCount S * GapDhWithSignReal(fgKeyInd1KeyGapDhAdv4 S b A)`. -/
theorem prob_badKeyIndFgAny4_1Key_le_gapDhWithSign (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    (𝒟[runKeyIndFgSim1Key S P A.1 >>= fun x =>
        pure (badKeyIndFgAny4 P b.q_ro x.2.2.base x.2.2.advRoLog)] {true}).toReal ≤
      ((S.N_spk_tot : ℝ) * ((S.N_id : ℝ) + (S.N_send_tot : ℝ)) +
        (S.N_id : ℝ) * (S.N_send_tot : ℝ) +
        (S.N_opk_tot : ℝ) * (S.N_send_opk_tot : ℝ)) *
        GapDhWithSignReal P P.isValidDhTriple P.pow8 (fgKeyInd1KeyGapDhAdv4 S b A) := by
  have hUnion := prob_badKeyIndFgAny4_le_sum P b.q_ro (runKeyIndFgSim1Key S P A.1)
    (fun x => x.2.2.base) (fun x => x.2.2.advRoLog)
  have hSumDh1 :
      (∑ uIdx ∈ Finset.range S.N_id, ∑ bIdx ∈ Finset.range S.N_spk_tot,
        (𝒟[runKeyIndFgSim1Key S P A.1 >>= fun x =>
          pure (badKeyIndFgDh1At P b.q_ro uIdx bIdx x.2.2.base x.2.2.advRoLog)] {true}).toReal) ≤
      (∑ uIdx ∈ Finset.range S.N_id, ∑ bIdx ∈ Finset.range S.N_spk_tot,
        GapDhWithSignReal P P.isValidDhTriple P.pow8 (fgKeyInd1KeyGapDhAdvAt true uIdx bIdx S b A)) :=
    Finset.sum_le_sum (fun uIdx huIdx =>
      Finset.sum_le_sum (fun bIdx hbIdx =>
        prob_badKeyIndFgDh1At_1Key_le_gapDhWithSign S b P hP A uIdx huIdx bIdx hbIdx))
  have hSumDh3 :
      (∑ sIdx ∈ Finset.range S.N_send_tot, ∑ bIdx ∈ Finset.range S.N_spk_tot,
        (𝒟[runKeyIndFgSim1Key S P A.1 >>= fun x =>
          pure (badKeyIndFgDh3At P b.q_ro sIdx bIdx x.2.2.base x.2.2.advRoLog)] {true}).toReal) ≤
      (∑ sIdx ∈ Finset.range S.N_send_tot, ∑ bIdx ∈ Finset.range S.N_spk_tot,
        GapDhWithSignReal P P.isValidDhTriple P.pow8 (fgKeyInd1KeyGapDhAdvAt false sIdx bIdx S b A)) :=
    Finset.sum_le_sum (fun sIdx hsIdx =>
      Finset.sum_le_sum (fun bIdx hbIdx =>
        prob_badKeyIndFgDh3At_1Key_le_gapDhWithSign S b P hP A sIdx hsIdx bIdx hbIdx))
  have hSumDh2 :
      (∑ sIdx ∈ Finset.range S.N_send_tot, ∑ kIdx ∈ Finset.range S.N_id,
        (𝒟[runKeyIndFgSim1Key S P A.1 >>= fun x =>
          pure (badKeyIndFgDh2At P b.q_ro sIdx kIdx x.2.2.base x.2.2.advRoLog)] {true}).toReal) ≤
      (∑ sIdx ∈ Finset.range S.N_send_tot, ∑ kIdx ∈ Finset.range S.N_id,
        GapDhWithSignReal P P.isValidDhTriple P.pow8 (fgKeyInd1KeyGapDhAdvAtIk sIdx kIdx S b A)) :=
    Finset.sum_le_sum (fun sIdx hsIdx =>
      Finset.sum_le_sum (fun kIdx hkIdx =>
        prob_badKeyIndFgDh2At_1Key_le_gapDhWithSign S b P hP A sIdx hsIdx kIdx hkIdx))
  have hSumDh4 :
      (∑ sIdx ∈ Finset.range S.N_send_opk_tot, ∑ oIdx ∈ Finset.range S.N_opk_tot,
        (𝒟[runKeyIndFgSim1Key S P A.1 >>= fun x =>
          pure (badKeyIndFgDh4At P b.q_ro sIdx oIdx x.2.2.base x.2.2.advRoLog)] {true}).toReal) ≤
      (∑ sIdx ∈ Finset.range S.N_send_opk_tot, ∑ oIdx ∈ Finset.range S.N_opk_tot,
        GapDhWithSignReal P P.isValidDhTriple P.pow8 (fgKeyInd1KeyGapDhAdvAtOpk sIdx oIdx S b A)) :=
    Finset.sum_le_sum (fun sIdx hsIdx =>
      Finset.sum_le_sum (fun oIdx hoIdx =>
        prob_badKeyIndFgDh4At_1Key_le_gapDhWithSign S b P hP A sIdx
          (Finset.mem_range.mpr (Nat.lt_of_lt_of_le (Finset.mem_range.mp hsIdx)
            (Nat.le_add_right _ _))) oIdx hoIdx))
  have hEq := sum_gapDhWithSign_fgKeyInd1KeyGapDhAdv4_eq S P P.isValidDhTriple P.pow8 b A
  linarith

/-! ## One-Key `ShCr` Simulation and `G3` Game -/

def pqxdhKeyIndShCrImpl1Key (checkG2 : Bool) (S : Setup) (P : Primitives) :
    QueryImpl (keyIndSpec S) (StateT (KeyIndShCrState S) ProbComp)
  | .initPrin u => liftKeyIndShCrBase (pqxdhKeyIndImpl1KeyReal S P (.initPrin u))
  | q => pqxdhKeyIndShCrImpl checkG2 S P q

theorem pqxdhKeyIndShCrImpl1Key_eq_of_ne_initPrin (checkG2 : Bool) (S : Setup) (P : Primitives)
    (q : KeyIndQuery S) (hNe : ∀ u, q ≠ .initPrin u) :
    pqxdhKeyIndShCrImpl1Key checkG2 S P q = pqxdhKeyIndShCrImpl checkG2 S P q := by
  cases q with
  | initPrin u => exact False.elim (hNe u rfl)
  | _ => rfl

theorem map_base_pqxdhKeyIndShCrImpl1Key_false (S : Setup) (P : Primitives)
    (q : KeyIndQuery S) (hst : KeyIndShCrState S) :
    Prod.map id ShCrState.base <$> ((pqxdhKeyIndShCrImpl1Key false S P q).run hst) =
      (pqxdhKeyIndImpl1KeyRo S P q).run hst.base := by
  have hInitOrNe : (∃ u, q = .initPrin u) ∨ (∀ u, q ≠ .initPrin u) := by
    cases q with
    | initPrin u => exact Or.inl ⟨u, rfl⟩
    | _ => exact Or.inr (fun _ h => by cases h)
  rcases hInitOrNe with ⟨u, rfl⟩ | hNe
  · simp [pqxdhKeyIndShCrImpl1Key, pqxdhKeyIndImpl1KeyRo, liftKeyIndShCrBase, liftShCrBase_run,
      Prod.map]
  · have hRo : pqxdhKeyIndImpl1KeyRo S P q = pqxdhKeyIndImpl true S P q := by
      cases q with
      | initPrin u => exact False.elim (hNe u rfl)
      | _ => rfl
    rw [pqxdhKeyIndShCrImpl1Key_eq_of_ne_initPrin false S P q hNe, hRo]
    exact map_base_pqxdhKeyIndShCrImpl_false S P q hst

theorem map_base_fullKeyIndShCrImpl1Key_false (S : Setup) (P : Primitives)
    (q : (unifSpec + keyIndSpec S).Domain) (hst : KeyIndShCrState S) :
    (Prod.map id ShCrState.base <$>
      (((QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndShCrState S) ProbComp) + pqxdhKeyIndShCrImpl1Key false S P) q).run hst) =
      (((QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndState S) ProbComp) + pqxdhKeyIndImpl1KeyRo S P) q).run hst.base := by
  cases q with
  | inl _ => simp [QueryImpl.liftTarget, StateT.run_monadLift]
  | inr kq => exact map_base_pqxdhKeyIndShCrImpl1Key_false S P kq hst

noncomputable def runKeyIndShCrSim1Key (S : Setup) (P : Primitives)
    (A : KeyIndAdversary S) : ProbComp (Bool × Bool × KeyIndShCrState S) := do
  let secb ← $ᵗ Bool
  let initSt : KeyIndShCrState S := { base := KeyIndState.empty S secb }
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (KeyIndShCrState S) ProbComp) + pqxdhKeyIndShCrImpl1Key false S P
  let (b', finalHst) ← (simulateQ impl A.run).run initSt
  return (secb, b', finalHst)

noncomputable def badKemShCrProbKeyInd_1Key (S : Setup) (P : Primitives)
    (A : KeyIndAdversary S) : ℝ :=
  (𝒟[runKeyIndShCrSim1Key S P A >>= fun (_, _, finalHst) =>
    pure (hasBadKemShCrRecords S P finalHst.initKemRecs finalHst.recvKemRecs)] {true}).toReal

noncomputable def keyIndExpG2_5ShCr_1Key (S : Setup) (P : Primitives) (A : KeyIndAdversary S) :
    ProbComp Bool := do
  let (secb, b', finalHst) ← runKeyIndShCrSim1Key S P A
  let finalSt := finalHst.base
  let allTestedClean :=
    finalSt.sessions.all (fun s =>
      !s.tested || isKeyIndInitStillFresh P true finalSt.principals finalSt.spkBundles
        finalSt.respSessions s) &&
    finalSt.respSessions.all (fun r =>
      !r.tested || isKeyIndRespStillFresh P true finalSt.principals finalSt.spkBundles
        finalSt.sessions r)
  if ((!allTestedClean || hasEcPkCollisionKeyInd P finalSt) || hasBadSigKeyInd finalSt) ||
     hasKemPkCollisionKeyInd finalSt then
    $ᵗ Bool
  else
    pure (b' == secb)

noncomputable def keyIndAdvG2_5ShCr_1Key (S : Setup) (P : Primitives) (A : KeyIndAdversary S) : ℝ :=
  (𝒟[keyIndExpG2_5ShCr_1Key S P A].boolBias).toReal

/-- One-key `G3` experiment: runs `runKeyIndShCrSim1Key` and applies `finalizeKeyIndG3`. -/
noncomputable def keyIndExpG3_1Key (S : Setup) (P : Primitives) (A : KeyIndAdversary S) :
    ProbComp Bool := do
  let (secb, b', finalHst) ← runKeyIndShCrSim1Key S P A
  finalizeKeyIndG3 S P secb b' finalHst

noncomputable def keyIndAdvG3_1Key (S : Setup) (P : Primitives) (A : KeyIndAdversary S) : ℝ :=
  (𝒟[keyIndExpG3_1Key S P A].boolBias).toReal

theorem keyInd_hop_badKemShCr_1Key_le_prob (S : Setup) (P : Primitives) (A : KeyIndAdversary S) :
    |keyIndAdvG2_5ShCr_1Key S P A - keyIndAdvG3_1Key S P A| ≤ badKemShCrProbKeyInd_1Key S P A := by
  unfold keyIndAdvG2_5ShCr_1Key keyIndAdvG3_1Key keyIndExpG2_5ShCr_1Key keyIndExpG3_1Key
    finalizeKeyIndG3 badKemShCrProbKeyInd_1Key
  exact abs_sub_boolBias_abort_or_le (runKeyIndShCrSim1Key S P A)
    (fun (_, _, finalHst) =>
      ((!(finalHst.base.sessions.all (fun s =>
            !s.tested || isKeyIndInitStillFresh P true finalHst.base.principals
              finalHst.base.spkBundles finalHst.base.respSessions s) &&
          finalHst.base.respSessions.all (fun r =>
            !r.tested || isKeyIndRespStillFresh P true finalHst.base.principals
              finalHst.base.spkBundles finalHst.base.sessions r)) ||
       hasEcPkCollisionKeyInd P finalHst.base) ||
       hasBadSigKeyInd finalHst.base) ||
       hasKemPkCollisionKeyInd finalHst.base)
    (fun (_, _, finalHst) => hasBadKemShCrRecords S P finalHst.initKemRecs finalHst.recvKemRecs)
    (fun (secb, b', _) => pure (b' == secb))

/-! ## `advRoLog` Extension and `secb`-Branch Decomposition -/

def pqxdhKeyIndAdvG3Impl1Key (S : Setup) (P : Primitives) :
    QueryImpl (keyIndSpec S) (StateT (KeyIndAdvCutoffState S) ProbComp)
  | .roQuery sec =>
    StateT.mk fun hst => do
      let (r, shCr') ← (pqxdhKeyIndShCrImpl1Key false S P (.roQuery sec)).run hst.shCr
      return (r, { shCr := shCr', advRoLog := sec :: hst.advRoLog })
  | q => liftKeyIndAdvShCr (pqxdhKeyIndShCrImpl1Key false S P q)

theorem pqxdhKeyIndAdvG3Impl1Key_eq_of_ne_initPrin (S : Setup) (P : Primitives)
    (q : KeyIndQuery S) (hNe : ∀ u, q ≠ .initPrin u) :
    pqxdhKeyIndAdvG3Impl1Key S P q = pqxdhKeyIndAdvG3Impl S P q := by
  cases q with
  | initPrin u => exact False.elim (hNe u rfl)
  | _ => rfl

theorem pqxdhKeyIndAdvG3Impl1Key_shCr {S : Setup} (P : Primitives)
    (q : KeyIndQuery S) (hst : KeyIndAdvCutoffState S) :
    Prod.map id KeyIndAdvCutoffState.shCr <$> ((pqxdhKeyIndAdvG3Impl1Key S P q).run hst) =
      (pqxdhKeyIndShCrImpl1Key false S P q).run hst.shCr := by
  cases q with
  | roQuery sec =>
    simp [pqxdhKeyIndAdvG3Impl1Key, StateT.run_mk, Prod.map]
  | _ => exact liftKeyIndAdvShCr_shCr _ hst

theorem simulateQ_pqxdhKeyIndAdvG3Impl1Key_shCr {S : Setup} {α : Type} (P : Primitives)
    (oa : OracleComp (unifSpec + keyIndSpec S) α) (hst : KeyIndAdvCutoffState S) :
    let fullAdv := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndAdvCutoffState S) ProbComp) + pqxdhKeyIndAdvG3Impl1Key S P
    let fullShCr := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndShCrState S) ProbComp) + pqxdhKeyIndShCrImpl1Key false S P
    Prod.map id KeyIndAdvCutoffState.shCr <$> ((simulateQ fullAdv oa).run hst) =
      (simulateQ fullShCr oa).run hst.shCr := by
  intro fullAdv fullShCr
  induction oa using OracleComp.inductionOn generalizing hst with
  | pure a =>
    simp [simulateQ_pure, StateT.run_pure, Prod.map]
  | query_bind q oa ih =>
    cases q with
    | inl uq =>
      dsimp only [fullAdv, fullShCr]
      rw [simulateQ_run_query_inl, simulateQ_run_query_inl, map_bind]
      congr 1; funext u
      exact ih u hst
    | inr gq =>
      dsimp only [fullAdv, fullShCr]
      rw [simulateQ_run_query_inr, simulateQ_run_query_inr, map_bind]
      rw [← pqxdhKeyIndAdvG3Impl1Key_shCr P gq hst, bind_map_left]
      congr 1; funext y
      exact ih y.1 y.2

noncomputable def runKeyIndAdvG3Sim1Key (S : Setup) (P : Primitives)
    (A : KeyIndAdversary S) : ProbComp (Bool × Bool × KeyIndAdvCutoffState S) := do
  let secb ← $ᵗ Bool
  let initSt : KeyIndAdvCutoffState S :=
    { shCr := { base := KeyIndState.empty S secb }, advRoLog := [] }
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (KeyIndAdvCutoffState S) ProbComp) + pqxdhKeyIndAdvG3Impl1Key S P
  let (b', finalHst) ← (simulateQ impl A.run).run initSt
  return (secb, b', finalHst)

theorem runKeyIndAdvG3Sim1Key_shCr (S : Setup) (P : Primitives) (A : KeyIndAdversary S) :
    Prod.map id (Prod.map id KeyIndAdvCutoffState.shCr) <$> runKeyIndAdvG3Sim1Key S P A =
      runKeyIndShCrSim1Key S P A := by
  unfold runKeyIndAdvG3Sim1Key runKeyIndShCrSim1Key
  rw [map_bind]
  congr 1; funext secb
  dsimp only
  have hSim := simulateQ_pqxdhKeyIndAdvG3Impl1Key_shCr P A.run
    { shCr := { base := KeyIndState.empty S secb }, advRoLog := [] }
  dsimp only at hSim
  rw [← hSim, bind_map_left]
  simp [Prod.map, map_eq_bind_pure_comp, bind_assoc]

theorem keyIndExpG3_1Key_eq_advG3Sim (S : Setup) (P : Primitives) (A : KeyIndAdversary S) :
    keyIndExpG3_1Key S P A = (do
      let (secb, b', finalHst) ← runKeyIndAdvG3Sim1Key S P A
      finalizeKeyIndG3 S P secb b' finalHst.shCr) := by
  unfold keyIndExpG3_1Key
  rw [← runKeyIndAdvG3Sim1Key_shCr S P A, bind_map_left]
  rfl

theorem pqxdhKeyIndAdvG3Impl1Key_toFg {S : Setup} (P : Primitives)
    (q : KeyIndQuery S) (hst : KeyIndAdvCutoffState S) :
    Prod.map id KeyIndAdvCutoffState.toFg <$> ((pqxdhKeyIndAdvG3Impl1Key S P q).run hst) =
      (pqxdhKeyIndFgImpl1Key S P q).run hst.toFg := by
  have hInitOrNe : (∃ u, q = .initPrin u) ∨ (∀ u, q ≠ .initPrin u) := by
    cases q with
    | initPrin u => exact Or.inl ⟨u, rfl⟩
    | _ => exact Or.inr (fun _ h => by cases h)
  rcases hInitOrNe with ⟨u, rfl⟩ | hNe
  · simp [pqxdhKeyIndAdvG3Impl1Key, pqxdhKeyIndFgImpl1Key, liftKeyIndAdvShCr,
      pqxdhKeyIndShCrImpl1Key, liftKeyIndShCrBase, liftFgBase, StateT.run_mk,
      KeyIndAdvCutoffState.toFg, Prod.map, map_eq_bind_pure_comp, bind_assoc]
  · have hFg : pqxdhKeyIndFgImpl1Key S P q = pqxdhKeyIndFgImpl S P q := by
      cases q with
      | initPrin u => exact False.elim (hNe u rfl)
      | _ => rfl
    rw [pqxdhKeyIndAdvG3Impl1Key_eq_of_ne_initPrin S P q hNe, hFg]
    exact pqxdhKeyIndAdvG3Impl_toFg P q hst

theorem simulateQ_pqxdhKeyIndAdvG3Impl1Key_toFg {S : Setup} {α : Type} (P : Primitives)
    (oa : OracleComp (unifSpec + keyIndSpec S) α) (hst : KeyIndAdvCutoffState S) :
    let fullAdv := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndAdvCutoffState S) ProbComp) + pqxdhKeyIndAdvG3Impl1Key S P
    let fullFg := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndFgCutoffState S) ProbComp) + pqxdhKeyIndFgImpl1Key S P
    Prod.map id KeyIndAdvCutoffState.toFg <$> ((simulateQ fullAdv oa).run hst) =
      (simulateQ fullFg oa).run hst.toFg := by
  intro fullAdv fullFg
  induction oa using OracleComp.inductionOn generalizing hst with
  | pure a =>
    simp [simulateQ_pure, StateT.run_pure, Prod.map]
  | query_bind q oa ih =>
    cases q with
    | inl uq =>
      dsimp only [fullAdv, fullFg]
      rw [simulateQ_run_query_inl, simulateQ_run_query_inl, map_bind]
      congr 1; funext u
      exact ih u hst
    | inr gq =>
      dsimp only [fullAdv, fullFg]
      rw [simulateQ_run_query_inr, simulateQ_run_query_inr, map_bind]
      rw [← pqxdhKeyIndAdvG3Impl1Key_toFg P gq hst, bind_map_left]
      congr 1; funext y
      exact ih y.1 y.2

theorem runKeyIndAdvG3Sim1Key_toFg (S : Setup) (P : Primitives) (A : KeyIndAdversary S) :
    Prod.map id (Prod.map id KeyIndAdvCutoffState.toFg) <$> runKeyIndAdvG3Sim1Key S P A =
      runKeyIndFgSim1Key S P A := by
  unfold runKeyIndAdvG3Sim1Key runKeyIndFgSim1Key KeyIndFgCutoffState.empty
  rw [map_bind]
  congr 1; funext secb
  dsimp only
  have hSim := simulateQ_pqxdhKeyIndAdvG3Impl1Key_toFg P A.run
    { shCr := { base := KeyIndState.empty S secb }, advRoLog := [] }
  dsimp only [KeyIndAdvCutoffState.toFg] at hSim
  rw [← hSim, bind_map_left]
  simp [Prod.map, KeyIndAdvCutoffState.toFg, map_eq_bind_pure_comp, bind_assoc]

theorem badKeyIndFgAny_runKeyIndAdvG3Sim1Key_eq_runKeyIndFgSim1Key
    (S : Setup) (P : Primitives) (maxLen : ℕ) (A : KeyIndAdversary S) :
    (runKeyIndAdvG3Sim1Key S P A >>= fun x =>
      pure (badKeyIndFgAny4 P maxLen x.2.2.shCr.base x.2.2.advRoLog)) =
    (runKeyIndFgSim1Key S P A >>= fun x =>
      pure (badKeyIndFgAny4 P maxLen x.2.2.base x.2.2.advRoLog)) := by
  rw [← runKeyIndAdvG3Sim1Key_toFg S P A, bind_map_left]
  rfl

noncomputable def keyIndAdvG3Branch1Key (secb : Bool) (S : Setup) (P : Primitives)
    (A : KeyIndAdversary S) : ProbComp Bool := do
  let initSt : KeyIndAdvCutoffState S :=
    { shCr := { base := KeyIndState.empty S secb }, advRoLog := [] }
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (KeyIndAdvCutoffState S) ProbComp) + pqxdhKeyIndAdvG3Impl1Key S P
  let (b', finalHst) ← (simulateQ impl A.run).run initSt
  finalizeKeyIndG3Post S P b' finalHst.shCr

def pqxdhKeyIndAdvTestImpl1Key (testReal : Bool) (S : Setup) (P : Primitives) :
    QueryImpl (keyIndSpec S) (StateT (KeyIndAdvCutoffState S) ProbComp)
  | .testSession sid =>
    liftKeyIndAdvShCr (liftKeyIndShCrBase (runKeyIndTestSession testReal S sid))
  | q => pqxdhKeyIndAdvG3Impl1Key S P q

theorem pqxdhKeyIndAdvTestImpl1Key_eq_of_ne_initPrin (testReal : Bool) (S : Setup) (P : Primitives)
    (q : KeyIndQuery S) (hNe : ∀ u, q ≠ .initPrin u) :
    pqxdhKeyIndAdvTestImpl1Key testReal S P q = pqxdhKeyIndAdvTestImpl testReal S P q := by
  cases q with
  | initPrin u => exact False.elim (hNe u rfl)
  | _ => rfl

theorem pqxdhKeyIndImpl1KeyReal_initPrin_withSecbBase (b : Bool) (S : Setup) (P : Primitives)
    (u : Fin S.N_id) (st : KeyIndState S) :
    (pqxdhKeyIndImpl1KeyReal S P (.initPrin u)).run (withSecbBase b st) =
      Prod.map id (withSecbBase b) <$> (pqxdhKeyIndImpl1KeyReal S P (.initPrin u)).run st := by
  unfold pqxdhKeyIndImpl1KeyReal withSecbBase
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split_ifs <;> simp [StateT.run_pure, StateT.run_set, StateT.run_monadLift,
    Prod.map, map_eq_bind_pure_comp, bind_assoc]

theorem pqxdhKeyIndAdvG3Impl1Key_withSecbAdv_eq_testImpl (b : Bool) (S : Setup) (P : Primitives)
    (q : KeyIndQuery S) (hst : KeyIndAdvCutoffState S) :
    (pqxdhKeyIndAdvG3Impl1Key S P q).run (withSecbAdv b hst) =
      Prod.map id (withSecbAdv b) <$> (pqxdhKeyIndAdvTestImpl1Key b S P q).run hst := by
  have hInitOrNe : (∃ u, q = .initPrin u) ∨ (∀ u, q ≠ .initPrin u) := by
    cases q with
    | initPrin u => exact Or.inl ⟨u, rfl⟩
    | _ => exact Or.inr (fun _ h => by cases h)
  rcases hInitOrNe with ⟨u, rfl⟩ | hNe
  · exact liftKeyIndAdvShCr_withSecbAdv b (pqxdhKeyIndShCrImpl1Key false S P (.initPrin u)) hst
      (liftShCrBase_withSecbShCr b (pqxdhKeyIndImpl1KeyReal S P (.initPrin u)) hst.shCr
        (pqxdhKeyIndImpl1KeyReal_initPrin_withSecbBase b S P u hst.shCr.base))
  · rw [pqxdhKeyIndAdvG3Impl1Key_eq_of_ne_initPrin S P q hNe,
      pqxdhKeyIndAdvTestImpl1Key_eq_of_ne_initPrin b S P q hNe]
    exact pqxdhKeyIndAdvG3Impl_withSecbAdv_eq_testImpl b S P q hst

theorem simulateQ_pqxdhKeyIndAdvG3Impl1Key_withSecbAdv {S : Setup} {α : Type}
    (b : Bool) (P : Primitives)
    (oa : OracleComp (unifSpec + keyIndSpec S) α) (hst : KeyIndAdvCutoffState S) :
    let fullAdv := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndAdvCutoffState S) ProbComp) + pqxdhKeyIndAdvG3Impl1Key S P
    let fullTest := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndAdvCutoffState S) ProbComp) + pqxdhKeyIndAdvTestImpl1Key b S P
    ((simulateQ fullAdv oa).run (withSecbAdv b hst)) =
      Prod.map id (withSecbAdv b) <$> ((simulateQ fullTest oa).run hst) := by
  intro fullAdv fullTest
  induction oa using OracleComp.inductionOn generalizing hst with
  | pure a =>
    simp [simulateQ_pure, StateT.run_pure, Prod.map]
  | query_bind q oa ih =>
    cases q with
    | inl uq =>
      dsimp only [fullAdv, fullTest]
      rw [simulateQ_run_query_inl, simulateQ_run_query_inl, map_bind]
      congr 1; funext u
      exact ih u hst
    | inr gq =>
      dsimp only [fullAdv, fullTest]
      rw [simulateQ_run_query_inr, simulateQ_run_query_inr,
        pqxdhKeyIndAdvG3Impl1Key_withSecbAdv_eq_testImpl b S P gq hst,
        bind_map_left, map_bind]
      congr 1; funext y
      exact ih y.1 y.2

theorem evalDist_keyIndExpG3_1Key_eq_branch (S : Setup) (P : Primitives) (A : KeyIndAdversary S) :
    𝒟[keyIndExpG3_1Key S P A] =
    𝒟[do
      let secb ← ($ᵗ Bool : ProbComp Bool)
      let z ←
        if secb then
          keyIndAdvG3Branch1Key true S P A
        else
          keyIndAdvG3Branch1Key false S P A
      return (secb == z)] := by
  rw [keyIndExpG3_1Key_eq_advG3Sim]
  unfold runKeyIndAdvG3Sim1Key keyIndAdvG3Branch1Key
  simp only [bind_assoc, pure_bind]
  refine OracleComp.evalDist_bind_congr_of_support _ _ _ fun secb _ => ?_
  cases secb <;>
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine OracleComp.evalDist_bind_congr_of_support _ _ _ fun ⟨b', finalHst⟩ _ => ?_
    exact evalDist_finalizeKeyIndG3_eq_post_beq S P _ b' finalHst.shCr

theorem keyIndAdvG3_1Key_eq_abs_sub_branch (S : Setup) (P : Primitives) (A : KeyIndAdversary S) :
    keyIndAdvG3_1Key S P A =
      |(𝒟[keyIndAdvG3Branch1Key true S P A] {true}).toReal -
       (𝒟[keyIndAdvG3Branch1Key false S P A] {true}).toReal| := by
  unfold keyIndAdvG3_1Key
  rw [evalDist_keyIndExpG3_1Key_eq_branch, evalDist_boolBias_bind_uniformBool,
    Measure.toReal_boolDist]

/-! ## Lazy-Cache Implementation and Coupling -/

def tagStepView1Key (testReal : Bool) (S : Setup) (P : Primitives) (q : KeyIndQuery S)
    (adv : KeyIndAdvCutoffState S) : ProbComp (LazyPost × KeyIndAdvCutoffState S) :=
  match q with
  | .initPrin u => do
    let (r, adv') ← (pqxdhKeyIndAdvG3Impl1Key S P (.initPrin u)).run adv
    return (.done r, adv')
  | q => tagStepView testReal S P q adv

theorem tagStepView1Key_eq_of_ne_initPrin (testReal : Bool) (S : Setup) (P : Primitives)
    (q : KeyIndQuery S) (hNe : ∀ u, q ≠ .initPrin u) :
    tagStepView1Key testReal S P q = tagStepView testReal S P q := by
  cases q with
  | initPrin u => exact False.elim (hNe u rfl)
  | _ => rfl

/-- One-key lazy/pre-warmed tagged `KeyInd` oracle implementation on `KeyIndLazyState S`. -/
def pqxdhKeyIndAdvTagImpl1Key (eagerRoHonest eagerRand testReal : Bool)
    (S : Setup) (P : Primitives) :
    QueryImpl (keyIndSpec S) (StateT (KeyIndLazyState S) ProbComp) :=
  mkLazyKeyIndImpl eagerRoHonest eagerRand S (tagStepView1Key testReal S P)

theorem pqxdhKeyIndAdvTagImpl1Key_eq_of_ne_initPrin
    (eagerRoHonest eagerRand testReal : Bool) (S : Setup) (P : Primitives)
    (q : KeyIndQuery S) (hNe : ∀ u, q ≠ .initPrin u) :
    pqxdhKeyIndAdvTagImpl1Key eagerRoHonest eagerRand testReal S P q =
      pqxdhKeyIndAdvTagImpl eagerRoHonest eagerRand testReal S P q := by
  unfold pqxdhKeyIndAdvTagImpl1Key pqxdhKeyIndAdvTagImpl mkLazyKeyIndImpl
  rw [tagStepView1Key_eq_of_ne_initPrin testReal S P q hNe]

theorem evalDist_simulateQ_pqxdhKeyIndAdvTagImpl1Key_true_true_eq_false_false
    {S : Setup} {α : Type}
    (testReal : Bool) (P : Primitives)
    (oa : OracleComp (unifSpec + keyIndSpec S) α)
    {obs : α × KeyIndLazyState S → ProbComp Bool}
    (hObsRand : (randLens S).IsInvariant obs)
    (hObsRo : (roLens S).IsInvariant obs)
    (lst : KeyIndLazyState S) :
    let full11 := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndLazyState S) ProbComp) + pqxdhKeyIndAdvTagImpl1Key true true testReal S P
    let full00 := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndLazyState S) ProbComp) + pqxdhKeyIndAdvTagImpl1Key false false testReal S P
    𝒟[(_root_.simulateQ full11 oa).run lst >>= obs] =
      𝒟[(_root_.simulateQ full00 oa).run lst >>= obs] :=
  evalDist_simulateQ_mkLazyKeyIndImpl_true_true_eq_false_false (tagStepView1Key testReal S P)
    oa hObsRand hObsRo lst

theorem pqxdhKeyIndImpl1KeyReal_initPrin_withBaseRoCache
    (c : List (Bytes × DRKey)) (S : Setup) (P : Primitives) (u : Fin S.N_id)
    (st : KeyIndState S) :
    (pqxdhKeyIndImpl1KeyReal S P (.initPrin u)).run (withBaseRoCache c st) =
      Prod.map id (withBaseRoCache c) <$> (pqxdhKeyIndImpl1KeyReal S P (.initPrin u)).run st := by
  unfold pqxdhKeyIndImpl1KeyReal withBaseRoCache
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split_ifs <;> simp [StateT.run_pure, StateT.run_set, StateT.run_monadLift,
    Prod.map, map_eq_bind_pure_comp, bind_assoc]

theorem pqxdhKeyIndAdvG3Impl1Key_initPrin_withAdvRoCache
    (S : Setup) (P : Primitives) (u : Fin S.N_id)
    (adv : KeyIndAdvCutoffState S) (c : List (Bytes × DRKey)) :
    (pqxdhKeyIndAdvG3Impl1Key S P (.initPrin u)).run (withAdvRoCache c adv) =
      Prod.map id (withAdvRoCache c) <$> (pqxdhKeyIndAdvG3Impl1Key S P (.initPrin u)).run adv :=
  liftKeyIndAdvShCr_withAdvRoCache c _ adv
    (liftShCrBase_withShCrRoCache c _ adv.shCr
      (pqxdhKeyIndImpl1KeyReal_initPrin_withBaseRoCache c S P u adv.shCr.base))

theorem pqxdhKeyIndAdvTagImpl1Key_run_initPrin {S : Setup}
    (eagerRoHonest eagerRand testReal : Bool) (P : Primitives) (u : Fin S.N_id)
    (lst : KeyIndLazyState S) :
    (pqxdhKeyIndAdvTagImpl1Key eagerRoHonest eagerRand testReal S P (.initPrin u)).run lst =
      (do
        let (r, adv') ← (pqxdhKeyIndAdvG3Impl1Key S P (.initPrin u)).run lst.adv
        pure (r, { lst with adv := adv' })) := by
  have hCache := pqxdhKeyIndAdvG3Impl1Key_initPrin_withAdvRoCache S P u
    (withAdvRoCache [] lst.adv) lst.adv.shCr.base.roCache
  have hId : withAdvRoCache lst.adv.shCr.base.roCache (withAdvRoCache [] lst.adv) = lst.adv := rfl
  rw [hId] at hCache
  dsimp only [pqxdhKeyIndAdvTagImpl1Key, mkLazyKeyIndImpl, tagStepView1Key, liftTagView,
    getLazyView, setLazyView]
  rw [StateT.run_mk, hCache]
  simp [runLazyPost, Prod.map, map_eq_bind_pure_comp, bind_assoc]

theorem pqxdhKeyIndImpl1KeyReal_initPrin_resolveLazyBase {S : Setup} (P : Primitives)
    (randCache : List (Bytes × DRKey)) (u : Fin S.N_id) (st : KeyIndState S) :
    (pqxdhKeyIndImpl1KeyReal S P (.initPrin u)).run (resolveLazyBase randCache st) =
      Prod.map id (resolveLazyBase randCache) <$>
        (pqxdhKeyIndImpl1KeyReal S P (.initPrin u)).run st ∧
    (∀ y ∈ support ((pqxdhKeyIndImpl1KeyReal S P (.initPrin u)).run st),
      (y.2.sessions, y.2.respSessions, y.2.roCache) =
        (st.sessions, st.respSessions, st.roCache)) := by
  refine ⟨?_, ?_⟩
  · unfold pqxdhKeyIndImpl1KeyReal resolveLazyBase
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs <;> simp [StateT.run_pure, StateT.run_set, StateT.run_monadLift,
      Prod.map, map_eq_bind_pure_comp, bind_assoc]
  · intro y hy
    unfold pqxdhKeyIndImpl1KeyReal at hy; dsimp only at hy
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hy
    split_ifs at hy
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
      subst hy; rfl
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
        StateT.run_pure, bind_assoc, pure_bind, MonadAttach.mem_support_bind, support_pure,
        Set.mem_singleton_iff] at hy
      rcases hy with ⟨_, _, rfl⟩
      rfl

theorem evalDist_step_relEagerTag1Key_initPrin {S : Setup} (testReal : Bool) (P : Primitives)
    (u : Fin S.N_id) (lst : KeyIndLazyState S) (hWF : WellFormedLazy lst)
    (k1 : KeyIndResponse × KeyIndAdvCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × KeyIndLazyState S → ProbComp Bool)
    (hk : ∀ r s1' s2', RelEagerTag s1' s2' → 𝒟[k1 (r, s1')] = 𝒟[k2 (r, s2')]) :
    𝒟[(pqxdhKeyIndAdvTestImpl1Key testReal S P (.initPrin u)).run (resolveLazyAdv lst) >>= k1] =
      𝒟[(pqxdhKeyIndAdvTagImpl1Key true true testReal S P (.initPrin u)).run lst >>= k2] := by
  rw [pqxdhKeyIndAdvTagImpl1Key_run_initPrin true true testReal P u lst]
  have hBase := pqxdhKeyIndImpl1KeyReal_initPrin_resolveLazyBase P lst.randCache u
    lst.adv.shCr.base
  have hAdv :
      (pqxdhKeyIndAdvTestImpl1Key testReal S P (.initPrin u)).run (resolveLazyAdv lst) =
      Prod.map id (fun a => { a with shCr := resolveLazyShCr lst.randCache a.shCr }) <$>
        (pqxdhKeyIndAdvG3Impl1Key S P (.initPrin u)).run lst.adv :=
    liftKeyIndAdvShCr_resolveLazyAdv lst.randCache
      (liftShCrBase (pqxdhKeyIndImpl1KeyReal S P (.initPrin u))) lst.adv
      (liftShCrBase_resolveLazyShCr lst.randCache _ lst.adv.shCr hBase.1)
  rw [hAdv, bind_map_left, bind_assoc]
  refine OracleComp.evalDist_bind_congr_of_support _ _ _ fun z hz => ?_
  have hzBase : (z.1, z.2.shCr.base) ∈
      support ((pqxdhKeyIndImpl1KeyReal S P (.initPrin u)).run lst.adv.shCr.base) := by
    have h1 : Prod.map id ShCrState.base <$>
        (Prod.map id KeyIndAdvCutoffState.shCr <$>
          ((pqxdhKeyIndAdvG3Impl1Key S P (.initPrin u)).run lst.adv)) =
        (pqxdhKeyIndImpl1KeyReal S P (.initPrin u)).run lst.adv.shCr.base := by
      rw [pqxdhKeyIndAdvG3Impl1Key_shCr, map_base_pqxdhKeyIndShCrImpl1Key_false]
      rfl
    rw [← h1]
    simp only [Functor.map_map, support_map, Set.mem_image]
    exact ⟨z, hz, rfl⟩
  have hEq := hBase.2 (z.1, z.2.shCr.base) hzBase
  injection hEq with hSess hRest
  injection hRest with hResp hRo
  refine hk z.1 _ { lst with adv := z.2 } ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only; rw [hSess, hRo]; exact hWF.sess_ro
  · dsimp only; rw [hSess]; exact hWF.sess_rand
  · dsimp only; rw [hResp, hRo]; exact hWF.resp_ro
  · dsimp only; rw [hResp]; exact hWF.resp_rand
  · dsimp only; rw [hSess, hResp]; exact hWF.rand_len

theorem evalDist_step_relEagerTag1Key {S : Setup} (testReal : Bool) (P : Primitives)
    (q : KeyIndQuery S) (adv : KeyIndAdvCutoffState S) (lst : KeyIndLazyState S)
    (hRel : RelEagerTag adv lst)
    (k1 : (keyIndSpec S).Range q × KeyIndAdvCutoffState S → ProbComp Bool)
    (k2 : (keyIndSpec S).Range q × KeyIndLazyState S → ProbComp Bool)
    (hk : ∀ r s1' s2', RelEagerTag s1' s2' → 𝒟[k1 (r, s1')] = 𝒟[k2 (r, s2')]) :
    𝒟[(pqxdhKeyIndAdvTestImpl1Key testReal S P q).run adv >>= k1] =
      𝒟[(pqxdhKeyIndAdvTagImpl1Key true true testReal S P q).run lst >>= k2] := by
  have hInitOrNe : (∃ u, q = .initPrin u) ∨ (∀ u, q ≠ .initPrin u) := by
    cases q with
    | initPrin u => exact Or.inl ⟨u, rfl⟩
    | _ => exact Or.inr (fun _ h => by cases h)
  rcases hInitOrNe with ⟨u, rfl⟩ | hNe
  · rcases hRel with ⟨rfl, hWF⟩
    exact evalDist_step_relEagerTag1Key_initPrin testReal P u lst hWF k1 k2 hk
  · rw [pqxdhKeyIndAdvTestImpl1Key_eq_of_ne_initPrin testReal S P q hNe,
        pqxdhKeyIndAdvTagImpl1Key_eq_of_ne_initPrin true true testReal S P q hNe]
    exact evalDist_step_relEagerTag testReal P q adv lst hRel k1 k2 hk

theorem evalDist_simulateQ_testImpl1Key_eq_tagImpl1Key_true_true {S : Setup} {α : Type}
    (testReal : Bool) (P : Primitives)
    (obs1 : α × KeyIndAdvCutoffState S → ProbComp Bool)
    (obs2 : α × KeyIndLazyState S → ProbComp Bool)
    (hObs : ∀ a s1 s2, RelEagerTag s1 s2 → 𝒟[obs1 (a, s1)] = 𝒟[obs2 (a, s2)])
    (oa : OracleComp (unifSpec + keyIndSpec S) α)
    (adv : KeyIndAdvCutoffState S) (lst : KeyIndLazyState S)
    (hRel : RelEagerTag adv lst) :
    let full1 := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndAdvCutoffState S) ProbComp) + pqxdhKeyIndAdvTestImpl1Key testReal S P
    let full2 := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndLazyState S) ProbComp) + pqxdhKeyIndAdvTagImpl1Key true true testReal S P
    𝒟[(_root_.simulateQ full1 oa).run adv >>= obs1] =
      𝒟[(_root_.simulateQ full2 oa).run lst >>= obs2] :=
  CacheLens.evalDist_simulateQ_eq_of_rel RelEagerTag
    (pqxdhKeyIndAdvTestImpl1Key testReal S P)
    (pqxdhKeyIndAdvTagImpl1Key true true testReal S P)
    (fun q s1 s2 hR k1 k2 hk => evalDist_step_relEagerTag1Key testReal P q s1 s2 hR k1 k2 hk)
    obs1 obs2 hObs oa adv lst hRel

theorem evalDist_simulateQ_testImpl1Key_finalizeKeyIndG3_eq_tagImpl1Key_false_false {S : Setup}
    (testReal : Bool) (P : Primitives) (secb : Bool)
    (oa : OracleComp (unifSpec + keyIndSpec S) Bool) :
    let initTrue : KeyIndAdvCutoffState S :=
      { shCr := { base := KeyIndState.empty S true }, advRoLog := [] }
    let fullTest := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndAdvCutoffState S) ProbComp) + pqxdhKeyIndAdvTestImpl1Key testReal S P
    let full00 := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndLazyState S) ProbComp) + pqxdhKeyIndAdvTagImpl1Key false false testReal S P
    𝒟[(_root_.simulateQ fullTest oa).run initTrue >>= fun p =>
        finalizeKeyIndG3 S P secb p.1 p.2.shCr] =
      𝒟[(_root_.simulateQ full00 oa).run (KeyIndLazyState.empty S) >>=
        fun p => finalizeKeyIndG3 S P secb p.1 p.2.adv.shCr] := by
  intro initTrue fullTest full00
  rw [evalDist_simulateQ_testImpl1Key_eq_tagImpl1Key_true_true testReal P
    (fun p => finalizeKeyIndG3 S P secb p.1 p.2.shCr)
    (fun p => finalizeKeyIndG3 S P secb p.1 p.2.adv.shCr)
    (fun a s1 s2 ⟨hEq, _⟩ => by
      subst hEq
      dsimp only [resolveLazyAdv]
      rw [finalizeKeyIndG3_resolveLazyShCr])
    oa initTrue (KeyIndLazyState.empty S) (relEagerTag_empty S)]
  exact evalDist_simulateQ_pqxdhKeyIndAdvTagImpl1Key_true_true_eq_false_false testReal P oa
    (isInvariant_randLens_finalizeKeyIndG3 S P secb)
    (isInvariant_roLens_finalizeKeyIndG3 S P secb)
    (KeyIndLazyState.empty S)

theorem evalDist_simulateQ_testImpl1Key_badKeyIndFgAny_eq_tagImpl1Key_false_false {S : Setup}
    (testReal : Bool) (P : Primitives) (maxLen : ℕ)
    (oa : OracleComp (unifSpec + keyIndSpec S) Bool) :
    let initTrue : KeyIndAdvCutoffState S :=
      { shCr := { base := KeyIndState.empty S true }, advRoLog := [] }
    let fullTest := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndAdvCutoffState S) ProbComp) + pqxdhKeyIndAdvTestImpl1Key testReal S P
    let full00 := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndLazyState S) ProbComp) + pqxdhKeyIndAdvTagImpl1Key false false testReal S P
    𝒟[(_root_.simulateQ fullTest oa).run initTrue >>=
        fun p => pure (badKeyIndFgAny4 P maxLen p.2.shCr.base p.2.advRoLog)] =
      𝒟[(_root_.simulateQ full00 oa).run (KeyIndLazyState.empty S) >>=
        fun p => pure (badKeyIndFgAny4 P maxLen p.2.adv.shCr.base p.2.adv.advRoLog)] := by
  intro initTrue fullTest full00
  rw [evalDist_simulateQ_testImpl1Key_eq_tagImpl1Key_true_true testReal P
    (fun p => pure (badKeyIndFgAny4 P maxLen p.2.shCr.base p.2.advRoLog))
    (fun p => pure (badKeyIndFgAny4 P maxLen p.2.adv.shCr.base p.2.adv.advRoLog))
    (fun a s1 s2 ⟨hEq, _⟩ => by
      subst hEq
      dsimp only [resolveLazyAdv, resolveLazyShCr]
      rw [badKeyIndFgAny_resolveLazyBase])
    oa initTrue (KeyIndLazyState.empty S) (relEagerTag_empty S)]
  exact evalDist_simulateQ_pqxdhKeyIndAdvTagImpl1Key_true_true_eq_false_false testReal P oa
    (isInvariant_randLens_badKeyIndFgAny S P maxLen)
    (isInvariant_roLens_badKeyIndFgAny S P maxLen)
    (KeyIndLazyState.empty S)

theorem keyIndAdvG3_1Key_le_prob_badKeyIndFgAny_of_tagImpl_false_false_relCoupled
    (S : Setup) (P : Primitives) (maxLen : ℕ) (A : KeyIndAdversary S)
    (R : Bool × KeyIndLazyState S → Bool × KeyIndLazyState S → Prop)
    (hRel :
      let fullF := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (KeyIndLazyState S) ProbComp) + pqxdhKeyIndAdvTagImpl1Key false false false S P
      let fullT := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (KeyIndLazyState S) ProbComp) + pqxdhKeyIndAdvTagImpl1Key false false true S P
      RelCoupled R
        ((simulateQ fullF A.run).run (KeyIndLazyState.empty S))
        ((simulateQ fullT A.run).run (KeyIndLazyState.empty S)))
    (hFin : ∀ p5 p6, R p5 p6 →
      𝒟[finalizeKeyIndG3 S P true p5.1 p5.2.adv.shCr] {true} =
        𝒟[finalizeKeyIndG3 S P true p6.1 p6.2.adv.shCr] {true} ∨
      badKeyIndFgAny4 P maxLen p5.2.adv.shCr.base p5.2.adv.advRoLog = true ∨
      badKeyIndFgAny4 P maxLen p6.2.adv.shCr.base p6.2.adv.advRoLog = true) :
    keyIndAdvG3_1Key S P A ≤
      2 * (𝒟[runKeyIndFgSim1Key S P A >>= fun x =>
        pure (badKeyIndFgAny4 P maxLen x.2.2.base x.2.2.advRoLog)] {true}).toReal := by
  let initFalse : KeyIndAdvCutoffState S :=
    { shCr := { base := KeyIndState.empty S false }, advRoLog := [] }
  let initTrue : KeyIndAdvCutoffState S :=
    { shCr := { base := KeyIndState.empty S true }, advRoLog := [] }
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (KeyIndAdvCutoffState S) ProbComp) + pqxdhKeyIndAdvG3Impl1Key S P
  let implF := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (KeyIndAdvCutoffState S) ProbComp) + pqxdhKeyIndAdvTestImpl1Key false S P
  let implT := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (KeyIndAdvCutoffState S) ProbComp) + pqxdhKeyIndAdvTestImpl1Key true S P
  have hSym := hRel.evalDist_bind_le_sym
    (fun p5 => badKeyIndFgAny4 P maxLen p5.2.adv.shCr.base p5.2.adv.advRoLog)
    (fun p6 => badKeyIndFgAny4 P maxLen p6.2.adv.shCr.base p6.2.adv.advRoLog)
    (fun p5 => finalizeKeyIndG3 S P true p5.1 p5.2.adv.shCr)
    (fun p6 => finalizeKeyIndG3 S P true p6.1 p6.2.adv.shCr)
    hFin
  rw [← evalDist_simulateQ_testImpl1Key_finalizeKeyIndG3_eq_tagImpl1Key_false_false false P true
        A.run,
      ← evalDist_simulateQ_testImpl1Key_finalizeKeyIndG3_eq_tagImpl1Key_false_false true P true
        A.run,
      ← evalDist_simulateQ_testImpl1Key_badKeyIndFgAny_eq_tagImpl1Key_false_false false P maxLen
        A.run,
      ← evalDist_simulateQ_testImpl1Key_badKeyIndFgAny_eq_tagImpl1Key_false_false true P maxLen
        A.run] at hSym
  have hBrF : keyIndAdvG3Branch1Key false S P A =
      ((simulateQ implF A.run).run initTrue >>= fun p => finalizeKeyIndG3 S P true p.1 p.2.shCr) :=
    by
    unfold keyIndAdvG3Branch1Key
    simp only [finalizeKeyIndG3Post_eq_finalizeKeyIndG3_true]
    have hInit : ({ shCr :=
      { base := KeyIndState.empty S false }, advRoLog := [] } : KeyIndAdvCutoffState S) =
        withSecbAdv false initTrue := rfl
    rw [hInit, simulateQ_pqxdhKeyIndAdvG3Impl1Key_withSecbAdv false P A.run initTrue,
      bind_map_left]
    rfl
  have hBrT : keyIndAdvG3Branch1Key true S P A =
      ((simulateQ implT A.run).run initTrue >>= fun p => finalizeKeyIndG3 S P true p.1 p.2.shCr) :=
    by
    unfold keyIndAdvG3Branch1Key
    simp only [finalizeKeyIndG3Post_eq_finalizeKeyIndG3_true]
    have hInit : ({ shCr :=
      { base := KeyIndState.empty S true }, advRoLog := [] } : KeyIndAdvCutoffState S) =
        withSecbAdv true initTrue := rfl
    conv_lhs => rw [hInit]
    rw [simulateQ_pqxdhKeyIndAdvG3Impl1Key_withSecbAdv true P A.run initTrue, bind_map_left]
    rfl
  have hBadF : ((simulateQ implF A.run).run initTrue >>= fun p =>
      pure (badKeyIndFgAny4 P maxLen p.2.shCr.base p.2.advRoLog)) =
      ((simulateQ impl A.run).run initFalse >>= fun p =>
      pure (badKeyIndFgAny4 P maxLen p.2.shCr.base p.2.advRoLog)) := by
    have hInit : initFalse = withSecbAdv false initTrue := rfl
    rw [hInit, simulateQ_pqxdhKeyIndAdvG3Impl1Key_withSecbAdv false P A.run initTrue,
      bind_map_left]
    rfl
  have hBadT : ((simulateQ implT A.run).run initTrue >>= fun p =>
      pure (badKeyIndFgAny4 P maxLen p.2.shCr.base p.2.advRoLog)) =
      ((simulateQ impl A.run).run initTrue >>= fun p =>
      pure (badKeyIndFgAny4 P maxLen p.2.shCr.base p.2.advRoLog)) := by
    have hInit : initTrue = withSecbAdv true initTrue := rfl
    conv_rhs => rw [hInit]
    rw [simulateQ_pqxdhKeyIndAdvG3Impl1Key_withSecbAdv true P A.run initTrue, bind_map_left]
    rfl
  rw [← hBrF, ← hBrT, hBadF, hBadT] at hSym
  have hBadSum :
      2 * (𝒟[runKeyIndFgSim1Key S P A >>= fun x =>
        pure (badKeyIndFgAny4 P maxLen x.2.2.base x.2.2.advRoLog)] {true}).toReal =
      (𝒟[(simulateQ impl A.run).run initFalse >>= fun p =>
        pure (badKeyIndFgAny4 P maxLen p.2.shCr.base p.2.advRoLog)] {true}).toReal +
      (𝒟[(simulateQ impl A.run).run initTrue >>= fun p =>
        pure (badKeyIndFgAny4 P maxLen p.2.shCr.base p.2.advRoLog)] {true}).toReal := by
    rw [← badKeyIndFgAny_runKeyIndAdvG3Sim1Key_eq_runKeyIndFgSim1Key]
    unfold runKeyIndAdvG3Sim1Key
    simp only [bind_assoc, pure_bind]
    exact two_mul_toReal_uniformBool_bind_eq_add_fg (fun secb =>
      (simulateQ impl A.run).run
        { shCr := { base := KeyIndState.empty S secb }, advRoLog := [] } >>=
        fun p => pure (badKeyIndFgAny4 P maxLen p.2.shCr.base p.2.advRoLog))
  have hfin5 : 𝒟[keyIndAdvG3Branch1Key false S P A] {true} ≠ ⊤ :=
    MeasureTheory.measure_ne_top _ {true}
  have hfin6 : 𝒟[keyIndAdvG3Branch1Key true S P A] {true} ≠ ⊤ :=
    MeasureTheory.measure_ne_top _ {true}
  have hfinB5 : 𝒟[(simulateQ impl A.run).run initFalse >>= fun p =>
      pure (badKeyIndFgAny4 P maxLen p.2.shCr.base p.2.advRoLog)] {true} ≠ ⊤ :=
    MeasureTheory.measure_ne_top _ {true}
  have hfinB6 : 𝒟[(simulateQ impl A.run).run initTrue >>= fun p =>
      pure (badKeyIndFgAny4 P maxLen p.2.shCr.base p.2.advRoLog)] {true} ≠ ⊤ :=
    MeasureTheory.measure_ne_top _ {true}
  have hfinBad : 𝒟[(simulateQ impl A.run).run initFalse >>= fun p =>
      pure (badKeyIndFgAny4 P maxLen p.2.shCr.base p.2.advRoLog)] {true} +
     𝒟[(simulateQ impl A.run).run initTrue >>= fun p =>
      pure (badKeyIndFgAny4 P maxLen p.2.shCr.base p.2.advRoLog)] {true} ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hfinB5, hfinB6⟩
  have h1 : 𝒟[keyIndAdvG3Branch1Key false S P A] {true} ≤
      𝒟[keyIndAdvG3Branch1Key true S P A] {true} +
      (𝒟[(simulateQ impl A.run).run initFalse >>= fun p =>
        pure (badKeyIndFgAny4 P maxLen p.2.shCr.base p.2.advRoLog)] {true} +
       𝒟[(simulateQ impl A.run).run initTrue >>= fun p =>
        pure (badKeyIndFgAny4 P maxLen p.2.shCr.base p.2.advRoLog)] {true}) := by
    rw [← add_assoc]; exact hSym.1
  have h2 : 𝒟[keyIndAdvG3Branch1Key true S P A] {true} ≤
      𝒟[keyIndAdvG3Branch1Key false S P A] {true} +
      (𝒟[(simulateQ impl A.run).run initFalse >>= fun p =>
        pure (badKeyIndFgAny4 P maxLen p.2.shCr.base p.2.advRoLog)] {true} +
       𝒟[(simulateQ impl A.run).run initTrue >>= fun p =>
        pure (badKeyIndFgAny4 P maxLen p.2.shCr.base p.2.advRoLog)] {true}) := by
    rw [← add_assoc]; exact hSym.2
  have h1r := (ENNReal.toReal_le_toReal hfin5 (ENNReal.add_ne_top.mpr ⟨hfin6, hfinBad⟩)).mpr h1
  have h2r := (ENNReal.toReal_le_toReal hfin6 (ENNReal.add_ne_top.mpr ⟨hfin5, hfinBad⟩)).mpr h2
  rw [ENNReal.toReal_add hfin6 hfinBad, ENNReal.toReal_add hfinB5 hfinB6] at h1r
  rw [ENNReal.toReal_add hfin5 hfinBad, ENNReal.toReal_add hfinB5 hfinB6] at h2r
  rw [keyIndAdvG3_1Key_eq_abs_sub_branch, hBadSum]
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

theorem validNonTestTagStep_of_tagStepView1Key {S : Setup} (testReal : Bool) (P : Primitives)
    (q : KeyIndQuery S) (hNeTest : ∀ sid, q ≠ .testSession sid)
    (adv : KeyIndAdvCutoffState S)
    {y : LazyPost × KeyIndAdvCutoffState S}
    (hy : y ∈ support (tagStepView1Key testReal S P q adv)) :
    ValidNonTestTagStep adv y.1 y.2 := by
  have hInitOrNe : (∃ u, q = .initPrin u) ∨ (∀ u, q ≠ .initPrin u) := by
    cases q with
    | initPrin u => exact Or.inl ⟨u, rfl⟩
    | _ => exact Or.inr (fun _ h => by cases h)
  rcases hInitOrNe with ⟨u, rfl⟩ | hNe
  · dsimp only [tagStepView1Key] at hy
    have hRun : (pqxdhKeyIndAdvG3Impl1Key S P (.initPrin u)).run adv =
        (do
          let (r, base') ← (pqxdhKeyIndImpl1KeyReal S P (.initPrin u)).run adv.shCr.base
          return (r, { adv with shCr := { adv.shCr with base := base' } })) := by
      simp [pqxdhKeyIndAdvG3Impl1Key, liftKeyIndAdvShCr, pqxdhKeyIndShCrImpl1Key,
        liftKeyIndShCrBase, liftShCrBase, StateT.run]; rfl
    rw [hRun] at hy
    simp only [bind_assoc, pure_bind, MonadAttach.mem_support_bind,
      support_pure, Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨r, base'⟩, hBase, rfl⟩
    have hEq := (pqxdhKeyIndImpl1KeyReal_initPrin_resolveLazyBase P [] u adv.shCr.base).2
      (r, base') hBase
    injection hEq with hSess hRest
    injection hRest with hResp _
    exact ValidNonTestTagStep.of_eq_lists adv _ r rfl hSess hResp
  · rw [tagStepView1Key_eq_of_ne_initPrin testReal S P q hNe] at hy
    exact validNonTestTagStep_of_tagStepView testReal P q hNeTest adv hy

theorem viewExtends_of_tagStepView1Key {S : Setup} (testReal : Bool) (P : Primitives)
    (q : KeyIndQuery S) (adv : KeyIndAdvCutoffState S)
    {y : LazyPost × KeyIndAdvCutoffState S}
    (hy : y ∈ support (tagStepView1Key testReal S P q adv)) :
    ViewExtends adv y.2 := by
  by_cases hTest : ∃ sid, q = .testSession sid
  · rcases hTest with ⟨sid, rfl⟩
    exact viewExtends_of_tagStepTestSession testReal sid adv hy
  · exact (validNonTestTagStep_of_tagStepView1Key testReal P q
      (fun sid hEq => hTest ⟨sid, hEq⟩) adv hy).1

theorem lazyStop_mono_pqxdhKeyIndAdvTagImpl1Key_false_false {S : Setup}
    (testReal : Bool) (P : Primitives) (q : KeyIndQuery S) (lst : KeyIndLazyState S)
    (hStop : lazyStop lst.adv = true)
    {y : KeyIndResponse × KeyIndLazyState S}
    (hy : y ∈ support ((pqxdhKeyIndAdvTagImpl1Key false false testReal S P q).run lst)) :
    lazyStop y.2.adv = true := by
  dsimp only [pqxdhKeyIndAdvTagImpl1Key, mkLazyKeyIndImpl, liftTagView, StateT.run_mk] at hy
  simp only [bind_assoc, pure_bind, MonadAttach.mem_support_bind] at hy
  rcases hy with ⟨⟨post, adv'⟩, hStep, hRun⟩
  rw [lazyStop_runLazyPost_false_false post (setLazyView adv' lst) hRun]
  have hExt := viewExtends_of_tagStepView1Key testReal P q (getLazyView lst) hStep
  have hStopView : lazyStop (getLazyView lst) = true := by
    simpa [getLazyView] using hStop
  simpa [setLazyView] using lazyStop_mono_of_viewExtends hExt hStopView

theorem tagStepView1Key_eq_of_ne_testSession {S : Setup} (P : Primitives)
    (q : KeyIndQuery S) (hNeTest : ∀ sid, q ≠ .testSession sid)
    (adv : KeyIndAdvCutoffState S) :
    tagStepView1Key false S P q adv = tagStepView1Key true S P q adv := by
  cases q with
  | testSession sid => exact False.elim (hNeTest sid rfl)
  | _ => rfl

theorem relCoupled_pqxdhKeyIndAdvTagImpl1Key_false_false_step {S : Setup} (P : Primitives)
    (q : KeyIndQuery S) (lst5 lst6 : KeyIndLazyState S)
    (hAg : LazyTagCacheAgree lst5 lst6) :
    RelCoupled
      (fun y5 y6 =>
        (y5.1 = y6.1 ∧ LazyTagCacheAgree y5.2 y6.2) ∨
        (lazyStop y5.2.adv = true ∧ lazyStop y6.2.adv = true))
      ((pqxdhKeyIndAdvTagImpl1Key false false false S P q).run lst5)
      ((pqxdhKeyIndAdvTagImpl1Key false false true S P q).run lst6) := by
  by_cases hTest : ∃ sid, q = .testSession sid
  · rcases hTest with ⟨sid, rfl⟩
    exact relCoupled_tagStepTestSession P sid lst5 lst6 hAg
  · have hNeTest : ∀ sid, q ≠ .testSession sid := fun sid hEq => hTest ⟨sid, hEq⟩
    dsimp only [pqxdhKeyIndAdvTagImpl1Key, mkLazyKeyIndImpl, liftTagView, StateT.run_mk]
    simp only [bind_assoc, pure_bind]
    rw [← hAg.1, ← tagStepView1Key_eq_of_ne_testSession P q hNeTest (getLazyView lst5)]
    refine RelCoupled.bind_same (tagStepView1Key false S P q (getLazyView lst5)) ?_
    rintro ⟨post, adv'⟩ hy
    have hStepView := validNonTestTagStep_of_tagStepView1Key false P q hNeTest (getLazyView lst5) hy
    exact relCoupled_runLazyPost_of_validNonTestTagStep lst5 lst6 post adv' hAg hStepView

theorem keyIndAdvG3_1Key_le_prob_badKeyIndFgAny_of_lazyStop
    (S : Setup) (P : Primitives) (maxLen : ℕ) (A : KeyIndAdversary S)
    (hStop :
      ∀ (testReal : Bool),
      let full := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (KeyIndLazyState S) ProbComp) + pqxdhKeyIndAdvTagImpl1Key false false testReal S P
      ∀ p ∈ support ((simulateQ full A.run).run (KeyIndLazyState.empty S)),
      lazyStop p.2.adv = true →
      badKeyIndFgAny4 P maxLen p.2.adv.shCr.base p.2.adv.advRoLog = true ∨
      isKeyIndG3Abort P p.2.adv.shCr = true) :
    keyIndAdvG3_1Key S P A ≤
      2 * (𝒟[runKeyIndFgSim1Key S P A >>= fun x =>
        pure (badKeyIndFgAny4 P maxLen x.2.2.base x.2.2.advRoLog)] {true}).toReal := by
  let fullF := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (KeyIndLazyState S) ProbComp) + pqxdhKeyIndAdvTagImpl1Key false false false S P
  let fullT := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (KeyIndLazyState S) ProbComp) + pqxdhKeyIndAdvTagImpl1Key false false true S P
  apply keyIndAdvG3_1Key_le_prob_badKeyIndFgAny_of_tagImpl_false_false_relCoupled S P maxLen A
    (fun p5 p6 =>
      ((p5.1 = p6.1 ∧ LazyTagCacheAgree p5.2 p6.2) ∨
        (lazyStop p5.2.adv = true ∧ lazyStop p6.2.adv = true)) ∧
      p5 ∈ support ((simulateQ fullF A.run).run (KeyIndLazyState.empty S)) ∧
      p6 ∈ support ((simulateQ fullT A.run).run (KeyIndLazyState.empty S)))
  · exact (simulateQ_relCoupled_or_stop
      (pqxdhKeyIndAdvTagImpl1Key false false false S P)
      (pqxdhKeyIndAdvTagImpl1Key false false true S P)
      LazyTagCacheAgree (fun s => lazyStop s.adv) (fun s => lazyStop s.adv)
      (fun q s5 hS _ hy => lazyStop_mono_pqxdhKeyIndAdvTagImpl1Key_false_false false P q s5 hS hy)
      (fun q s6 hS _ hy => lazyStop_mono_pqxdhKeyIndAdvTagImpl1Key_false_false true P q s6 hS hy)
      (relCoupled_pqxdhKeyIndAdvTagImpl1Key_false_false_step P) A.run
      (KeyIndLazyState.empty S) (KeyIndLazyState.empty S) (lazyTagCacheAgree_empty S)).and_support
  · rintro p5 p6 ⟨⟨hEq, hAg⟩ | ⟨hs5, hs6⟩, hp5, hp6⟩
    · left
      rw [hEq, finalizeKeyIndG3_eq_of_lazyTagCacheAgree P p6.1 p5.2 p6.2 hAg]
    · rcases hStop false p5 hp5 hs5 with hb5 | ha5
      · exact Or.inr (Or.inl hb5)
      · rcases hStop true p6 hp6 hs6 with hb6 | ha6
        · exact Or.inr (Or.inr hb6)
        · left
          rw [finalizeKeyIndG3_of_isKeyIndG3Abort S P true p5.1 p5.2.adv.shCr ha5,
              finalizeKeyIndG3_of_isKeyIndG3Abort S P true p6.1 p6.2.adv.shCr ha6]

/-! ## `ValidTagState` Preservation and `G3 -> G3.5` Bound -/

theorem validTagStateCore_of_tagStepView1Key {S : Setup} (P : Primitives)
    (testReal : Bool) (q : KeyIndQuery S) (adv : KeyIndAdvCutoffState S)
    (hCore : ValidTagStateCore P adv)
    {y : LazyPost × KeyIndAdvCutoffState S}
    (hMem : y ∈ support (tagStepView1Key testReal S P q adv)) :
    ValidTagStateCore P y.2 ∧
    y.2.advRoLog.length ≤ adv.advRoLog.length + (if isKeyIndRoQuery (.inr q) then 1 else 0) ∧
    y.2.shCr.sendCount ≤ adv.shCr.sendCount + (if isKeyIndSendQuery (.inr q) then 1 else 0) := by
  have hInitOrNe : (∃ u, q = .initPrin u) ∨ (∀ u, q ≠ .initPrin u) := by
    cases q with
    | initPrin u => exact Or.inl ⟨u, rfl⟩
    | _ => exact Or.inr (fun _ h => by cases h)
  rcases hInitOrNe with ⟨u, rfl⟩ | hNe
  · dsimp only [tagStepView1Key] at hMem
    have hRun : (pqxdhKeyIndAdvG3Impl1Key S P (.initPrin u)).run adv =
        (do
          let (r, base') ← (pqxdhKeyIndImpl1KeyReal S P (.initPrin u)).run adv.shCr.base
          return (r, { adv with shCr := { adv.shCr with base := base' } })) := by
      simp [pqxdhKeyIndAdvG3Impl1Key, liftKeyIndAdvShCr, pqxdhKeyIndShCrImpl1Key,
        liftKeyIndShCrBase, liftShCrBase, StateT.run]; rfl
    rw [hRun] at hMem
    simp only [bind_assoc, pure_bind, MonadAttach.mem_support_bind,
      support_pure, Set.mem_singleton_iff] at hMem
    rcases hMem with ⟨⟨r1, st1⟩, hSt1, _, rfl⟩
    simp only [isKeyIndRoQuery, isKeyIndSendQuery, ↓reduceIte, Nat.add_zero]
    unfold pqxdhKeyIndImpl1KeyReal at hSt1; dsimp only at hSt1
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hSt1
    cases hFresh : adv.shCr.base.principals.any (fun (idx, _) => idx == u.val) with
    | true =>
      rw [hFresh] at hSt1
      simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq]
        at hSt1
      rcases hSt1 with ⟨_, rfl⟩
      exact ⟨hCore, Nat.le_refl _, Nat.le_refl _⟩
    | false =>
      rw [hFresh] at hSt1
      simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hSt1
      rcases hSt1 with ⟨sec0, hSec0, _, rfl⟩
      rcases hCore.1 with ⟨hVP, hVS, hVO, hPrinV, hSpkV, hOpkV, hAdvV⟩
      refine ⟨validTagStateCore_of_shCrExtends_eq_sessions P hCore ?_ ?_ rfl rfl
        (fun _ h => h) (fun _ h => h), Nat.le_refl _, Nat.le_refl _⟩
      · refine ⟨(validPrincipals_cons S u _ adv.shCr.base.principals hVP hFresh).1,
          hVS, hVO, ?_, ?_, hOpkV, hAdvV⟩
        · intro kv hkv
          rcases List.mem_cons.mp hkv with rfl | hOld
          · exact ⟨length_of_mem_support_sampleScalar32_coll hSec0, rfl⟩
          · exact hPrinV kv hOld
        · intro kv hkv
          rcases hSpkV kv hkv with ⟨h1, h2, ⟨uE, huE⟩, h4⟩
          exact ⟨h1, h2, ⟨uE, List.mem_cons_of_mem _ huE⟩, h4⟩
      · exact ⟨⟨fun _ e h => ⟨e, List.mem_cons_of_mem _ h, rfl, rfl⟩,
          fun _ b h => ⟨b, h, rfl, rfl, rfl, rfl⟩,
          fun _ o h => ⟨o, h, rfl, rfl⟩,
          fun _ h => h⟩, Nat.le_refl _, fun _ h => h, fun _ h => h, fun _ h => h⟩
  · rw [tagStepView1Key_eq_of_ne_initPrin testReal S P q hNe] at hMem
    exact validTagStateCore_of_tagStepView P testReal q adv hCore hMem

theorem validTagStateCore_of_pqxdhKeyIndAdvTagImpl1Key {S : Setup} (P : Primitives)
    (eagerRoHonest eagerRand testReal : Bool) (q : KeyIndQuery S)
    (lst : KeyIndLazyState S) (hCore : ValidTagStateCore P lst.adv)
    {y : KeyIndResponse × KeyIndLazyState S}
    (hy : y ∈ support ((pqxdhKeyIndAdvTagImpl1Key eagerRoHonest eagerRand testReal S P q).run lst)) :
    ValidTagStateCore P y.2.adv ∧
    y.2.adv.advRoLog.length ≤ lst.adv.advRoLog.length + (if isKeyIndRoQuery (.inr q) then 1 else 0)
      ∧
    y.2.adv.shCr.sendCount ≤ lst.adv.shCr.sendCount + (if isKeyIndSendQuery (.inr q) then 1 else 0)
      := by
  dsimp only [pqxdhKeyIndAdvTagImpl1Key, mkLazyKeyIndImpl, liftTagView, StateT.run_mk] at hy
  simp only [bind_assoc, pure_bind, MonadAttach.mem_support_bind] at hy
  rcases hy with ⟨⟨post, adv'⟩, hView, hyPost⟩
  rcases validTagStateCore_of_tagStepView1Key P testReal q (getLazyView lst)
    (validTagStateCore_of_withAdvRoCache P [] hCore) hView with
    ⟨hCore', hLog', hSend'⟩
  rcases validTagStateCore_of_runLazyPost P eagerRoHonest eagerRand post (setLazyView adv' lst)
    (validTagStateCore_of_withAdvRoCache P _ hCore') hyPost with ⟨hCoreY, hLogY, hSendY⟩
  exact ⟨hCoreY,
    by simpa [hLogY, getLazyView, setLazyView, withAdvRoCache] using hLog',
    by simpa [hSendY, getLazyView, setLazyView, withAdvRoCache, withShCrRoCache] using hSend'⟩

theorem simulateQ_pqxdhKeyIndAdvTagImpl1Key_validTagStateCore {S : Setup} {α : Type}
    (P : Primitives) (eagerRoHonest eagerRand testReal : Bool)
    (oa : OracleComp (unifSpec + keyIndSpec S) α)
    (lst : KeyIndLazyState S) (nRo nSend : Nat)
    (hCore : ValidTagStateCore P lst.adv)
    (hRo : OracleComp.IsQueryBoundP oa isKeyIndRoQuery nRo)
    (hSend : OracleComp.IsQueryBoundP oa isKeyIndSendQuery nSend) :
    let full := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndLazyState S) ProbComp) + pqxdhKeyIndAdvTagImpl1Key eagerRoHonest eagerRand
          testReal S P
    ∀ y ∈ support ((simulateQ full oa).run lst),
      ValidTagStateCore P y.2.adv ∧
      y.2.adv.advRoLog.length ≤ lst.adv.advRoLog.length + nRo ∧
      y.2.adv.shCr.sendCount ≤ lst.adv.shCr.sendCount + nSend := by
  intro full
  induction oa using OracleComp.inductionOn generalizing lst nRo nSend with
  | pure a =>
    intro y hy
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
    subst hy; dsimp only; exact ⟨hCore, by omega, by omega⟩
  | query_bind t mx ih =>
    rw [isQueryBoundP_query_bind_iff] at hRo hSend
    rcases t with uq | gq
    · intro y hy
      dsimp only [full] at hy
      rw [simulateQ_run_query_inl] at hy
      simp only [MonadAttach.mem_support_bind] at hy
      rcases hy with ⟨u, _, hy'⟩
      have hRo' := hRo.2 u
      have hSend' := hSend.2 u
      simp only [isKeyIndRoQuery, isKeyIndSendQuery, ↓reduceIte] at hRo' hSend'
      exact ih u lst nRo nSend hCore hRo' hSend' y hy'
    · intro y hy
      dsimp only [full] at hy
      rw [simulateQ_run_query_inr] at hy
      simp only [MonadAttach.mem_support_bind] at hy
      rcases hy with ⟨x, hstep, hy'⟩
      rcases validTagStateCore_of_pqxdhKeyIndAdvTagImpl1Key P eagerRoHonest eagerRand testReal gq
        lst hCore hstep with
        ⟨hCoreX, hLogX, hSendX⟩
      rcases ih x.1 x.2
        (if isKeyIndRoQuery (.inr gq) then nRo - 1 else nRo)
        (if isKeyIndSendQuery (.inr gq) then nSend - 1 else nSend)
        hCoreX (hRo.2 x.1) (hSend.2 x.1) y hy' with ⟨hCoreY, hLogY, hSendY⟩
      have h1 := hRo.1
      have h2 := hSend.1
      refine ⟨hCoreY, ?_, ?_⟩
      · by_cases hro : isKeyIndRoQuery (.inr gq) <;>
          simp only [hro, not_true_eq_false, false_or, ↓reduceIte] at h1 hLogX hLogY <;> omega
      · by_cases hs : isKeyIndSendQuery (.inr gq) <;>
          simp only [hs, not_true_eq_false, false_or, ↓reduceIte] at h2 hSendX hSendY <;> omega

theorem validTagState_of_mem_support_simulateQ1Key {S : Setup}
    (P : Primitives) (eagerRoHonest eagerRand testReal : Bool)
    (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    let full := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndLazyState S) ProbComp) + pqxdhKeyIndAdvTagImpl1Key eagerRoHonest eagerRand
          testReal S P
    ∀ p ∈ support ((simulateQ full A.1.run).run (KeyIndLazyState.empty S)),
      ValidTagState P b.q_ro p.2.adv := by
  intro full p hp
  rcases simulateQ_pqxdhKeyIndAdvTagImpl1Key_validTagStateCore P eagerRoHonest eagerRand testReal
    A.1.run (KeyIndLazyState.empty S) b.q_ro S.N_send_tot
    (validTagStateCore_empty S P true) A.2.1 A.2.2.1 p hp with
    ⟨hCore, hLog, hSend⟩
  exact ⟨by simpa [KeyIndLazyState.empty] using hLog,
    by simpa [KeyIndLazyState.empty, KeyIndState.empty] using hSend,
    hCore.1, hCore.2.1, hCore.2.2.1, hCore.2.2.2⟩

end Proofs.SignalPqxdh.Security
