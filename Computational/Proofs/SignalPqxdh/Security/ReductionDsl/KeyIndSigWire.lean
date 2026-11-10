/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndSigKemBounds
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndSigEval
public import Computational.Proofs.ReductionDsl.Soundness
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndSigKemProofs

/-!
# Cost Bounds for the DSL `KeyInd` `SigEufCma` Adversary

Packages syntactic step-cost and semantic query bounds (`SigEufCmaAdv.Bounded`) for
`sigKeyIndDslAdv`.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.KeyInd

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security
open OracleSpec OracleComp

abbrev sigKeyIndDslProg (useRo : Bool) (S : Setup) (b : QueryBudget) :=
  sigKeyIndProg useRo S b.q_total

theorem sigKeyIndDslAdv_q_prim (useRo : Bool) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    (sigKeyIndDslAdv useRo S b A).q_prim = b.q_total * (S.N_dh * 20 + S.N_sess_tot * 8 + 17) := rfl

theorem sigKeyIndDslAdv_q_prim_le (useRo : Bool) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    (sigKeyIndDslAdv useRo S b A).q_prim ≤ primQueryBudget S b := by
  rw [sigKeyIndDslAdv_q_prim]
  unfold primQueryBudget
  nlinarith

theorem sigKeyIndDslProg_totalCost_le (useRo : Bool) (S : Setup) (b : QueryBudget) :
    (sigKeyIndDslProg useRo S b).totalCost b.q_total ≤ stepCostBudget S b :=
  sigKeyIndProg_totalCost_le_of_le useRo S b b.q_total
    (show b.q_total ≤ 2 * b.q_total + 1 by omega)

theorem sigKeyIndDslProg_totalPrimQueries_le (useRo : Bool) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    (sigKeyIndDslProg useRo S b).totalQueries sigPrimW sigWS b.q_total ≤
      (sigKeyIndDslAdv useRo S b A).q_prim :=
  sigKeyIndProg_totalPrimQueries_le useRo S b b.q_total

theorem sigKeyIndProg_primBounded (useRo : Bool) (S : Setup) (K q : Nat)
    (A : Unit → OracleComp (unifSpec + keyIndSpec S) Bool)
    (hA : ∀ u, (A u).IsQueryBoundP (_root_.ReductionDsl.isGameQuery (G := keyIndSpec S)) q)
    (pk : Bytes) :
    ((sigKeyIndProg useRo S K).eval A pk).IsQueryBoundP
      (fun q => SignalPqxdh.isPrimQuery q = true)
      ((sigKeyIndProg useRo S K).totalQueries sigPrimW sigWS q) :=
  CostedReduction.queryBound_eval (sigKeyIndProg useRo S K)
    (fun q => SignalPqxdh.isPrimQuery q = true) sigPrimW sigWS
    (fun g _ hg => by cases g with | inl _ => exact le_rfl | inr _ => cases hg)
    (fun n => (isQueryBoundP_query_iff (spec := PrimBaseSpec + eufCmaSignOracle.spec)
      (fun q => SignalPqxdh.isPrimQuery q = true) (Sum.inl (Sum.inl n)) 0).2
      (fun h => by cases h))
    A q hA pk

/-- `sigKeyIndDslAdv` respects its declared signing and primitive query budgets. -/
theorem sigKeyIndDslAdv_bounded (useRo : Bool) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    (sigKeyIndDslAdv useRo S b A).Bounded := by
  have hA : ∀ u : Unit,
      A.1.run.IsQueryBoundP (_root_.ReductionDsl.isGameQuery (G := keyIndSpec S)) b.q_total := by
    intro _
    have h := A.2.2.2.2.1
    convert h using 1; funext q
    cases q <;> simp [_root_.ReductionDsl.isGameQuery, isGameQuery]
  refine ⟨fun pk => ?_, fun pk => ?_⟩
  · exact sigKeyIndProg_chalBounded useRo S b.q_total (fun _ => A.1.run) pk
  · exact (sigKeyIndProg_primBounded useRo S b.q_total b.q_total (fun _ => A.1.run) hA pk).mono
      (sigKeyIndDslProg_totalPrimQueries_le useRo S b A)

end SignalPqxdh.Security.ReductionDsl.KeyInd
