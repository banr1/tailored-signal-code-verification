/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndGapDhProofs
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndGapDhEvalEq

/-!
# Cost and Query Bounds for the `ReductionDsl` `KeyInd` `GapDH` Adversary

Packages `fgKeyIndGapDhProg` as a bounded `GapDhAdv` (`fgKeyIndGapDhAdv4GenAdv`) and proves its
`GapDH` advantage equals that of the shallow reduction `fgKeyIndGapDhAdv4`.
-/

@[expose] public section

set_option autoImplicit false

open SignalPqxdh SignalPqxdh.Security SignalPqxdh.Security.FgGapDh
open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh.LegacyCosted
open OracleSpec OracleComp

namespace SignalPqxdh.Security.ReductionDsl.KeyIndGapDh
open SignalPqxdh.Security.ReductionDsl.KeyInd

/-- The `ReductionDsl` `KeyInd` `GapDH` adversary with semantic DDH and primitive query budgets. -/
def fgKeyIndGapDhAdv4GenAdv (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) : GapDhAdv where
  run U V := (fgKeyIndGapDhProg S b.q_total).eval (fun _ => A.1.run) (U, V)
  q_ddh := gdhQueryBudget S b
  q_prim := primQueryBudget S b

theorem fgKeyIndGapDhAdv4GenAdv_q_ddh_le (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    (fgKeyIndGapDhAdv4GenAdv S b A).q_ddh ≤ gdhQueryBudget S b :=
  le_rfl

theorem fgKeyIndGapDhProg_totalPrimQueries_le_q_prim (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    (fgKeyIndGapDhProg S b.q_total).totalQueries wPrimGdh wsZero b.q_total ≤
      (fgKeyIndGapDhAdv4GenAdv S b A).q_prim :=
  fgKeyIndGapDhProg_totalPrimQueries_le S b

theorem fgKeyIndGapDhAdv4GenAdv_bounded (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    (fgKeyIndGapDhAdv4GenAdv S b A).Bounded := by
  have hA : ∀ a : Unit, (A.1.run).IsQueryBoundP
      (ReductionDsl.isGameQuery (G := keyIndSpec S)) b.q_total := by
    intro _
    obtain ⟨_, _, _, h, _⟩ := A.2
    convert h using 1
    funext q
    cases q
    · exact propext ⟨False.elim, Bool.noConfusion⟩
    · exact propext ⟨fun _ => rfl, fun _ => trivial⟩
  refine ⟨fun U V => ?_, fun U V => ?_⟩
  · exact fgKeyIndGapDhProg_chalBounded_gdhQueryBudget S b A U V
  · have hP := fgKeyIndGapDhProg_primBounded S b.q_total b.q_total (fun _ => A.1.run) hA U V
    exact hP.mono (fgKeyIndGapDhProg_totalPrimQueries_le_q_prim S b A)

theorem fgKeyIndGapDhProg_evalDist_eq (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool) (pow8 : Bytes → Bytes)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    𝒟[gapDhExp P isValidDhTriple pow8 (fgKeyIndGapDhAdv4GenAdv S b A)] =
      𝒟[gapDhExp P isValidDhTriple pow8 (fgKeyIndGapDhAdv4 S b A)] := by
  have h : fgKeyIndGapDhAdv4GenAdv S b A =
      { fgKeyIndGapDhAdv4 S b A with
        q_ddh := gdhQueryBudget S b
        q_prim := primQueryBudget S b } := by
    unfold fgKeyIndGapDhAdv4GenAdv
    congr 1
    funext U V
    exact fgKeyIndGapDhProg_eval_eq S b A U V
  rw [h]
  rfl

/-- Advantage equality between `fgKeyIndGapDhAdv4GenAdv` and `fgKeyIndGapDhAdv4`. -/
theorem fgKeyIndGapDhProg_gapDh_eq (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool) (pow8 : Bytes → Bytes)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    GapDH P isValidDhTriple pow8 (fgKeyIndGapDhAdv4GenAdv S b A) =
      GapDH P isValidDhTriple pow8 (fgKeyIndGapDhAdv4 S b A) := by
  simp only [GapDH, fgKeyIndGapDhProg_evalDist_eq]

end SignalPqxdh.Security.ReductionDsl.KeyIndGapDh
