/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5B
public import Computational.Proofs.SignalPqxdh.Security.ReductionsAuthAead
public import Computational.Proofs.SignalPqxdh.Security.SigHopA
public import Computational.Proofs.GameHop.Swap
public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5B2
public import Computational.Proofs.SignalPqxdh.Security.FgGapDhC
public import VCVio.EvalDist.Monad.Basic
public import VCVio.OracleComp.EvalDist.Measure
public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5C1
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyHybrid
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5B
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5B2
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_CollisionsB
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_TwoKeyAndAuthStatements
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrapBase
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyShallowSims

/-!
# One-Key Ideal-Session AEAD Validity Invariant

Proves that `IdealSessionsAeadValid` is preserved by `pqxdhAuthHybridSplitFixedImpl1Key` whenever
`recvStage.idealMsgKeys = true`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000

open scoped ENNReal BigOperators
open OracleComp OracleSpec MeasureTheory

namespace SignalPqxdh.Security

open SignalPqxdh
open _root_.Proofs.SignalPqxdh.Security
open _root_.Proofs.SignalPqxdh.Security.FgGapDh (initSessionSlotIdx initSessionSlotIdx_sendOPK_lt initSessionSlotIdx_sendNoOPK_lt initSessionSlotIdx_inj_of_lt RelProbUpToBad simulateQ_relProbUpToBad evalDist_simulateQ_eq_of_step_or_bad)

namespace SlotM

end SlotM

theorem idealSessionsAeadValid_nonRecvSplitFixed1Key {S : Setup}
    (sendStage recvStage : AuthHybridStage) (hIdeal : recvStage.idealMsgKeys = true)
    (useRo checkAuth : Bool) (P : Primitives)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (hInv : IdealSessionsAeadValid P hst)
    {p : (authSpec S).Range q × AuthHybridStateFixed S}
    (hp : p ∈ support ((pqxdhAuthHybridSplitFixedImpl1Key sendStage recvStage useRo checkAuth S P q).run
      hst)) :
    IdealSessionsAeadValid P p.2 := by
  unfold pqxdhAuthHybridSplitFixedImpl1Key at hp
  simp only [hIdeal, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    StateT.run_bind, StateT.run_get, pure_bind] at hp
  unfold IdealSessionsAeadValid at hInv ⊢
  cases q with
  | recvOPK k j o msg =>
    rw [pqxdhAuthHybridFixedImpl_recvOPK_eq1Key recvStage hIdeal] at hp
    cases hprep : prepareAuthHybridRecvOPK checkAuth P k j o msg hst.toAuthHybridState with
    | none =>
      simp only [hprep, support_pure, Set.mem_singleton_iff] at hp
      rcases hp with ⟨_, rfl⟩; exact hInv
    | some prep =>
      simp only [hprep, support_map, Set.mem_image] at hp
      rcases hp with ⟨⟨res?, mkSaltCache'⟩, _, hEq⟩
      have hSt : p.2.toAuthHybridState = (prep.finish res?).2 := by
        simpa using congrArg (fun x => x.2.toAuthHybridState) hEq.symm
      rw [hSt, (prepareAuthHybridRecvOPK_idealSessions checkAuth P k j o msg hst.toAuthHybridState
        hprep).2 res?]
      exact hInv
  | recvNoOPK k j l msg =>
    rw [pqxdhAuthHybridFixedImpl_recvNoOPK_eq1Key recvStage hIdeal] at hp
    cases hprep : prepareAuthHybridRecvNoOPK checkAuth P k j l msg hst.toAuthHybridState with
    | none =>
      simp only [hprep, support_pure, Set.mem_singleton_iff] at hp
      rcases hp with ⟨_, rfl⟩; exact hInv
    | some prep =>
      simp only [hprep, support_map, Set.mem_image] at hp
      rcases hp with ⟨⟨res?, mkSaltCache'⟩, _, hEq⟩
      have hSt : p.2.toAuthHybridState = (prep.finish res?).2 := by
        simpa using congrArg (fun x => x.2.toAuthHybridState) hEq.symm
      rw [hSt, (prepareAuthHybridRecvNoOPK_idealSessions checkAuth P k j l msg hst.toAuthHybridState
        hprep).2 res?]
      exact hInv
  | sendOPK u i bundle m0 m1 =>
    simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
      StateT.run_pure,
      bind_assoc, pure_bind, MonadAttach.mem_support_bind, support_pure,
        Set.mem_singleton_iff] at hp
    rcases hp with ⟨⟨resp, hst'⟩, hp, rfl⟩
    dsimp only [pqxdhAuthHybridKoskImpl1Key] at hp
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hp
    split_ifs at hp
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
      rcases hp with ⟨_, rfl⟩; exact hInv
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
      rcases hp with ⟨_, rfl⟩; exact hInv
    · rw [runAuthHybridSendKosk_eq] at hp
      exact idealSessionsAeadValid_evalAuthHybridSendKosk sendStage useRo P (.sendOPK u i)
        (Nat.lt_of_lt_of_le (initSessionSlotIdx_sendOPK_lt u i) (Nat.le_add_right _ _)) u bundle m0
          m1 hst.toAuthHybridState hInv hp
  | sendNoOPK u i bundle m0 m1 =>
    simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
      StateT.run_pure,
      bind_assoc, pure_bind, MonadAttach.mem_support_bind, support_pure,
        Set.mem_singleton_iff] at hp
    rcases hp with ⟨⟨resp, hst'⟩, hp, rfl⟩
    dsimp only [pqxdhAuthHybridKoskImpl1Key] at hp
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hp
    split_ifs at hp
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
      rcases hp with ⟨_, rfl⟩; exact hInv
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
      rcases hp with ⟨_, rfl⟩; exact hInv
    · rw [runAuthHybridSendKosk_eq] at hp
      exact idealSessionsAeadValid_evalAuthHybridSendKosk sendStage useRo P (.sendNoOPK u i)
        (initSessionSlotIdx_sendNoOPK_lt u i) u bundle m0 m1 hst.toAuthHybridState hInv hp
  | _ =>
    simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
      StateT.run_pure,
      bind_assoc, pure_bind, MonadAttach.mem_support_bind, support_pure,
        Set.mem_singleton_iff] at hp
    rcases hp with ⟨⟨resp, hst'⟩, hp, rfl⟩
    dsimp only [pqxdhAuthHybridKoskImpl1Key] at hp
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hp
    split_ifs at hp
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
      rcases hp with ⟨_, rfl⟩; exact hInv
    · simp only [run_liftAuthBase, support_map, Set.mem_image] at hp
      rcases hp with ⟨⟨_, _⟩, _, hEq⟩
      cases hEq
      exact hInv

end SignalPqxdh.Security
