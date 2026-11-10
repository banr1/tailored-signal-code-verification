/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthHopInterface
public import Computational.Proofs.SignalPqxdh.Security.ReductionsAuthAead
public import Computational.Proofs.SignalPqxdh.Security.SigHopA
public import Computational.Proofs.SignalPqxdh.Security.FgGapDhA
public import Computational.Proofs.SignalPqxdh.Security.FgGapDhC
public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyHybrid
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_CollisionsB
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_TwoKeyAndAuthStatements
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrapBase
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyShallowSims

/-!
# One-Key Primitive Query Bound on Non-Session `Auth` Queries

Proves that `stepAuthOtherPrim1Key` makes at most four primitive oracle queries per `AuthQuery`.
-/

@[expose] public section

set_option autoImplicit false

open OracleSpec OracleComp MeasureTheory ENNReal BigOperators

namespace SignalPqxdh.Security

open SignalPqxdh
open _root_.Proofs.SignalPqxdh.Security
open _root_.Proofs.SignalPqxdh.Security.FgGapDh
  (initSessionSlotIdx initSessionSlotIdx_sendOPK_lt initSessionSlotIdx_sendNoOPK_lt
   initSessionSlotIdx_inj_of_lt RelProbUpToBad simulateQ_relProbUpToBad
   evalDist_simulateQ_eq_of_step_or_bad)

theorem primBounded_stepAuthOtherPrim1Key (useRo : Bool) (S : Setup) (q : AuthQuery S)
    (hst : AuthHybridStateFixed S) :
    PrimBounded (stepAuthOtherPrim1Key useRo S q hst) 4 := by
  unfold stepAuthOtherPrim1Key
  cases q with
  | initPrin u =>
    dsimp only
    split
    · exact primBounded_pure'
    · refine primBounded_bind_le 1 (primBounded_embedUnif sampleScalar32 0) (fun _ => ?_)
      exact primBounded_bind_le 0 (primBounded_primQ _) (fun _ => primBounded_pure')
  | corruptIK u =>
    dsimp only
    cases hst.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == u.val) <;>
      exact primBounded_pure'
  | genSPK u j =>
    dsimp only
    split
    · exact primBounded_pure'
    · cases hst.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none => exact primBounded_pure'
      | some p =>
        rcases p with ⟨_, uEntry⟩
        dsimp only
        refine primBounded_bind_le 4 (primBounded_embedUnif sampleScalar32 0) (fun _ => ?_)
        refine primBounded_bind_le 3 (primBounded_primQ _) (fun _ => ?_)
        refine primBounded_bind_le 3 (primBounded_embedUnif sampleRandom64 0) (fun _ => ?_)
        refine primBounded_bind_le 2 (primBounded_primQ _) (fun _ => ?_)
        refine primBounded_bind_le 1 primBounded_sampleKemKeyGenPrim (fun _ => ?_)
        refine primBounded_bind_le 1 (primBounded_embedUnif sampleRandom64 0) (fun _ => ?_)
        exact primBounded_bind_le 0 (primBounded_primQ _) (fun _ => primBounded_pure')
  | genOPK u j o =>
    dsimp only
    split
    · exact primBounded_pure'
    · refine primBounded_bind_le 1 (primBounded_embedUnif sampleScalar32 0) (fun _ => ?_)
      exact primBounded_bind_le 0 (primBounded_primQ _) (fun _ => primBounded_pure')
  | registerKey sk =>
    dsimp only
    split
    · exact primBounded_pure'
    · refine primBounded_bind_le 1 (primBounded_primQ _) (fun _ => ?_)
      exact primBounded_bind_le 0 (primBounded_primQ _) (fun _ => primBounded_pure')
  | roQuery secrets =>
    dsimp only
    split
    · exact primBounded_pure'
    · exact primBounded_bind_le 0
        (primBounded_evalHkdfOrRoPrim true _ secrets) (fun _ => primBounded_pure')
  | roRootQuery rk dh =>
    dsimp only
    split
    · exact primBounded_pure'
    · exact primBounded_bind_le 0
        (primBounded_embedUnif (evalRootKdfRoPure _ rk dh) 0) (fun _ => primBounded_pure')
  | revealDhSecrets =>
    dsimp only
    split <;> exact primBounded_pure'
  | sendOPK _ _ _ _ _ | sendNoOPK _ _ _ _ _ | recvOPK _ _ _ _ | recvNoOPK _ _ _ _ =>
    exact primBounded_pure'

end SignalPqxdh.Security
