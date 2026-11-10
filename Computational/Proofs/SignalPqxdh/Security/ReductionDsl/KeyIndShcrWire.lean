/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndSigKemBounds
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndShcrLoop

/-!
# Cost Bounds for the DSL `KemShCr` Adversary

Packages syntactic step-cost and semantic primitive-query bounds for `shcrKeyIndDslAdv`.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.KeyInd

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security
open OracleSpec OracleComp

abbrev shcrKeyIndDslProg (S : Setup) (b : QueryBudget) :=
  shcrKeyIndProg S b.q_total (keyIndLoopBound b)

theorem shcrKeyIndDslProg_totalCost_le (S : Setup) (b : QueryBudget) :
    (shcrKeyIndDslProg S b).totalCost b.q_total ≤ stepCostBudget S b :=
  shcrKeyIndProg_totalCost_le S b

theorem shcrKeyIndDslProg_totalPrimQueries_le (S : Setup) (b : QueryBudget) :
    (shcrKeyIndDslProg S b).totalQueries primW primWS b.q_total ≤ primQueryBudget S b :=
  shcrKeyIndProg_totalQueries_le S b (keyIndLoopBound b)

theorem shcrKeyIndProg_eval1_primBounded (S : Setup) (Q K fuel : Nat)
    (A : Unit → OracleComp (unifSpec + keyIndSpec S) Bool) (pk sk : Bytes) :
    ((shcrKeyIndProg S Q K).eval1 A (pk, sk) fuel false).IsQueryBoundP
      (fun q => SignalPqxdh.isPrimQuery₀ q = true)
      ((shcrKeyIndProg S Q K).totalQueries primW primWS fuel) :=
  TwoStageCostedReduction.eval1_queryBound (shcrKeyIndProg S Q K)
    (fun q => SignalPqxdh.isPrimQuery₀ q = true) primW primWS
    (fun _ _ _ => le_rfl)
    (fun n => (isQueryBoundP_query_iff (spec := PrimBaseSpec)
      (fun q => SignalPqxdh.isPrimQuery₀ q = true) (Sum.inl n) 0).2 (fun h => by cases h))
    A (pk, sk) fuel false

theorem shcrKeyIndProg_eval2_primBounded (S : Setup) (Q K fuel : Nat)
    (m : Mid (keyIndSpec S) Bool pauseTy.denote shcrStTy.denote Bytes) (ss ct : Bytes) :
    ((shcrKeyIndProg S Q K).eval2 m (ss, ct) fuel false).IsQueryBoundP
      (fun q => SignalPqxdh.isPrimQuery₀ q = true)
      ((shcrKeyIndProg S Q K).totalQueries primW primWS fuel) :=
  TwoStageCostedReduction.eval2_queryBound (shcrKeyIndProg S Q K)
    (fun q => SignalPqxdh.isPrimQuery₀ q = true) primW primWS
    (fun _ _ _ => le_rfl)
    (fun n => (isQueryBoundP_query_iff (spec := PrimBaseSpec)
      (fun q => SignalPqxdh.isPrimQuery₀ q = true) (Sum.inl n) 0).2 (fun h => by cases h))
    m (ss, ct) fuel false

/-- `shcrKeyIndDslAdv` respects its declared primitive-query budget in both stages. -/
theorem shcrKeyIndDslAdv_bounded (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    (shcrKeyIndDslAdv S b A).Bounded := by
  refine ⟨fun pk sk => ?_, fun st ss ct => ?_⟩
  · exact (shcrKeyIndProg_eval1_primBounded S b.q_total (keyIndLoopBound b) b.q_total
      (fun _ => A.1.run) pk sk).mono (shcrKeyIndDslProg_totalPrimQueries_le S b)
  · exact (shcrKeyIndProg_eval2_primBounded S b.q_total (keyIndLoopBound b) b.q_total
      st ss ct).mono (shcrKeyIndDslProg_totalPrimQueries_le S b)

end SignalPqxdh.Security.ReductionDsl.KeyInd
