/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthSigHop1KeyA
public import Computational.Proofs.SignalPqxdh.Security.ReductionsAuth1KeySig
public import Computational.Proofs.SignalPqxdh.Security.SigHop1Key
import VCVio.OracleComp.EvalDist.Measure

/-!
# One-key `Auth` bad-signature hop: union bound and index sampling

**Checked by Lean.** Reduces the one-key `Auth` bad-signature hop (`G0.1 → G1`) to the per-principal
bound `authSig1KeyPerKBound` via a union bound over `k < N_id` and index sampling for
`sigReductionAuth1Key`.
-/

@[expose] public section

set_option autoImplicit false

open SignalPqxdh SignalPqxdh.Security
open OracleSpec OracleComp

namespace Proofs.SignalPqxdh.Security

/-- Per-principal bad-signature bound for one-key `Auth`, in the frozen `NoOpk` game. -/
def authSig1KeyPerKBound (S : Setup) (P : Primitives) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) (k : Nat) : Prop :=
  𝒟[runAuthWithProvFrozen1Key (checkBundleProvenanceNoOpk P) S P A.val >>= fun (_, _, finalSt) =>
      pure (hasBadSigAuthAt S P k finalSt)] {true} ≤
    𝒟[gapSigEufCmaExp P P.isValidDhTriple (sigReductionAuth1KeyAt k S b A)] {true}

theorem liftGdhToSign_fgEmbedPrim_eq {α : Type} (mx : OracleComp PrimBaseSpec α) :
    FgGapDh1Key.liftGdhToSign (FgGapDh.embedPrim (spec := gapDhOracleSpec) mx) =
      SignalPqxdh.Security.embedPrim (spec := sigAndDdhSpec) mx := by
  induction mx using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind q k ih =>
    change (liftM (OracleSpec.query (spec := GdhSignSimSpec) (Sum.inl q)) >>= fun u =>
        FgGapDh1Key.liftGdhToSign (FgGapDh.embedPrim (spec := gapDhOracleSpec) (k u))) =
      (liftM (OracleSpec.query (spec := PrimBaseSpec + sigAndDdhSpec) (Sum.inl q)) >>= fun u =>
        SignalPqxdh.Security.embedPrim (spec := sigAndDdhSpec) (k u))
    simp only [ih]

theorem unifGdhSign_eq_unifSigDdh {α : Type} (mx : ProbComp α) :
    FgGapDh1Key.unifGdhSign mx = unifSigDdh mx := by
  unfold FgGapDh1Key.unifGdhSign FgGapDh.unifGdh unifSigDdh
  rw [liftGdhToSign_fgEmbedPrim_eq]; rfl

theorem mul_gapSigEufCma_sigReductionAuth1Key_eq_sum (S : Setup) (b : QueryBudget)
    (P : Primitives) (A : BoundedAdv (AuthAdversary S) b) :
    (S.N_id : ℝ) * GapSigEufCmaReal P P.isValidDhTriple (sigReductionAuth1Key S b A) =
      ∑ k ∈ Finset.range S.N_id,
        GapSigEufCmaReal P P.isValidDhTriple (sigReductionAuth1KeyAt k S b A) := by
  have hSwap :
      𝒟[gapSigEufCmaExp P P.isValidDhTriple (sigReductionAuth1Key S b A)] =
      𝒟[RoKem.sampleIndexRange S.N_id >>= fun k =>
        gapSigEufCmaExp P P.isValidDhTriple (sigReductionAuth1KeyAt k S b A)] := by
    simp only [gapSigEufCmaExp_eq_fullImpl]
    unfold sigReductionAuth1Key sigReductionAuth1KeyAt
    dsimp only
    simp only [unifGdhSign_eq_unifSigDdh, simulateQ_bind, StateT.run_bind, simulateQ_unifSigDdh_run,
      bind_map_left, bind_assoc]
    rw [OracleComp.evalDist_bind_bind_swap]
  unfold GapSigEufCmaReal GapSigEufCma
  rw [hSwap]
  exact _root_.Proofs.SignalPqxdh.Security.mul_toReal_sampleIndexRange_bind_eq_sum S.N_id
    (fun k => gapSigEufCmaExp P P.isValidDhTriple (sigReductionAuth1KeyAt k S b A))

/-- One-key `Auth` bad-signature hop, given the per-principal bound. -/
theorem auth1Key_hop_sigEufCma_frozen_le_of_perK (S : Setup) (P : Primitives)
    (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b)
    (hPerK : ∀ k < S.N_id, authSig1KeyPerKBound S P b A k) :
    |(𝒟[authExpG0_1WithProvFrozen1Key (checkBundleProvenance P) S P A.val].boolBias).toReal -
     (𝒟[authExpG1WithProvFrozen1Key (checkBundleProvenanceExact P) S P A.val].boolBias).toReal| ≤
      (S.N_id : ℝ) * GapSigEufCmaReal P P.isValidDhTriple (sigReductionAuth1Key S b A) := by
  rw [authExpG0_1WithProvFrozen1Key_orig_eq_dual, ← authExpG1WithProvFrozen1Key_dual_eq_exact]
  have h2 : authExpG1WithProvFrozen1Key (checkBundleProvenanceDual P) S P A.val =
      (runAuthWithProvFrozen1Key (checkBundleProvenanceDual P) S P A.val >>= fun a =>
        if hasEcPkCollisionAuth P a.2.2 ||
           (hasBadSigAuth a.2.2 && noPrinPkColl P a.2.2.principals) then $ᵗ Bool
        else contAuth S P a) := by
    unfold authExpG1WithProvFrozen1Key; congr 1; ext ⟨secb, b', finalSt⟩; dsimp only
    have h_or : (hasEcPkCollisionAuth P finalSt || hasBadSigAuth finalSt) =
        (hasEcPkCollisionAuth P finalSt ||
          (hasBadSigAuth finalSt && noPrinPkColl P finalSt.principals)) := by
      cases hnp : noPrinPkColl P finalSt.principals; swap; · simp
      have hcoll : hasDuplicateBytes (allHonestEcPksAuth P finalSt) = true := by
        unfold allHonestEcPksAuth; simp only [HasAuthState.toAuthState, List.append_assoc]
        exact hasDuplicateBytes_append_of_left _ _ (by unfold noPrinPkColl at hnp; simpa using hnp)
      simp [hasEcPkCollisionAuth, hcoll]
    rw [h_or]
  have hAbort :
      |(𝒟[authExpG0_1WithProvFrozen1Key (checkBundleProvenanceDual P) S P A.val].boolBias).toReal -
       (𝒟[authExpG1WithProvFrozen1Key (checkBundleProvenanceDual P) S P A.val].boolBias).toReal| ≤
      (𝒟[runAuthWithProvFrozen1Key (checkBundleProvenanceDual P) S P A.val >>= fun (_, _, finalSt) =>
        pure (hasBadSigAuth finalSt && noPrinPkColl P finalSt.principals)] {true}).toReal := by
    rw [h2]; exact abs_sub_boolBias_abort_or_le
      (runAuthWithProvFrozen1Key (checkBundleProvenanceDual P) S P A.val)
      (fun (_, _, s) => hasEcPkCollisionAuth P s)
      (fun (_, _, s) => hasBadSigAuth s && noPrinPkColl P s.principals) (contAuth S P)
  have hMapDual :
      (runAuthWithProvFrozen1Key (checkBundleProvenanceDual P) S P A.val >>= fun (_, _, finalSt) =>
        pure (hasBadSigAuth finalSt && noPrinPkColl P finalSt.principals)) =
      (runAuthWithProvFrozen1Key (checkBundleProvenanceNoOpk P) S P A.val >>= fun (_, _, finalSt) =>
        pure ((List.range S.N_id).any (fun k => hasBadSigAuthAt S P k finalSt))) := by
    rw [runAuthWithProvFrozen1Key_eq_map S P eraseOpkTriples
          (checkBundleProvenanceNoOpk P) (checkBundleProvenanceDual P)
          (checkBundleProvenanceNoOpk_eq_eraseOpk_dual P) A.val,
        bind_map_left]
    refine bind_congr (fun ⟨secb, b', st⟩ => ?_)
    dsimp only; rw [← hasBadSigAuth_eq_any_range S P, hasBadSigAuth_mapAuthSessions_eraseOpk]; rfl
  have hSum :
      (𝒟[runAuthWithProvFrozen1Key (checkBundleProvenanceDual P) S P A.val >>= fun (_, _, finalSt) =>
        pure (hasBadSigAuth finalSt && noPrinPkColl P finalSt.principals)] {true}).toReal ≤
      ∑ k ∈ Finset.range S.N_id,
        GapSigEufCmaReal P P.isValidDhTriple (sigReductionAuth1KeyAt k S b A) := by
    rw [hMapDual]
    refine (toReal_any_range_le_sum
      (runAuthWithProvFrozen1Key (checkBundleProvenanceNoOpk P) S P A.val)
      S.N_id (fun k (_, _, finalSt) => hasBadSigAuthAt S P k finalSt)).trans ?_
    refine Finset.sum_le_sum (fun k hk => ?_)
    exact (ENNReal.toReal_le_toReal
      (MeasureTheory.measure_ne_top _ _) (MeasureTheory.measure_ne_top _ _)).mpr
      (hPerK k (Finset.mem_range.mp hk))
  rw [mul_gapSigEufCma_sigReductionAuth1Key_eq_sum]
  exact hAbort.trans hSum

end Proofs.SignalPqxdh.Security
