/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopC6c
public import Computational.Proofs.SignalPqxdh.Security.FgGapDhE
public import VCVio.EvalDist.Monad.Basic
public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopC6c1
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthGapDhHopC2
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthGapDhHopC2b
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthGapDhHopC3b
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthGapDhHopC6b
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthGapDhHopC6c
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthHopInterface
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrapBase
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyShallowSims
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyHybrid
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyGapDhIdSim

/-!
# One-Key `Auth` `G3 -> G3.5` Coupled Invariant and Send Couplings

Support projections and `.roQuery`, `.sendOPK`, and `.sendNoOPK` step couplings for
`pqxdhAuthAdvLatchedStageImpl1Key`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Classical
open SignalPqxdh SignalPqxdh.Security
open OracleSpec OracleComp
open scoped ENNReal BigOperators
open Proofs.SignalPqxdh.Security.FgGapDh
namespace Proofs.SignalPqxdh.Security

theorem mem_support_hyb_of_mem_support_pqxdhAuthAdvLatchedStageImpl1Key
    {S : Setup} (stage : AuthHybridStage) (P : Primitives)
    (q : AuthQuery S) (s : AuthAdvLatchedState S) {y : AuthResponse × AuthAdvLatchedState S}
    (hy : y ∈ support ((pqxdhAuthAdvLatchedStageImpl1Key stage S P q).run s)) :
    (y.1, y.2.hyb) ∈ support ((pqxdhAuthHybridKoskImpl1Key stage true true S P q).run s.hyb) := by
  have hyAdv := mem_support_adv_of_mem_support_pqxdhAuthAdvLatchedStageImpl1Key stage P q s y hy
  unfold AuthAdvLatchedState.hyb
  rw [← map_hyb_pqxdhAuthAdvStageImpl1Key stage S P q s.adv, support_map]
  exact ⟨(y.1, y.2.adv), hyAdv, rfl⟩
theorem authHybridTraceSub_pqxdhAuthAdvLatchedStageImpl1Key
    {S : Setup} (stage : AuthHybridStage) (P : Primitives)
    (q : AuthQuery S) (s : AuthAdvLatchedState S) {y : AuthResponse × AuthAdvLatchedState S}
    (hy : y ∈ support ((pqxdhAuthAdvLatchedStageImpl1Key stage S P q).run s)) :
    AuthHybridTraceSub s.hyb y.2.hyb :=
  authHybridTraceSub_pqxdhAuthHybridKoskImpl1Key stage true true P q s.hyb
    (mem_support_hyb_of_mem_support_pqxdhAuthAdvLatchedStageImpl1Key stage P q s hy)
private theorem prop_of_liftAuthBase_c6c1 {S : Setup} (Q : AuthHybridState S → Prop)
    (m : StateT (AuthState S) ProbComp AuthResponse) (hst : AuthHybridState S)
    (h : ∀ p ∈ support (m.run hst.base), Q { hst with base := p.2 })
    {y : AuthResponse × AuthHybridState S} (hy : y ∈ support ((liftAuthBase m).run hst)) :
    Q y.2 := by
  unfold liftAuthBase at hy
  simp only [StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
    StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
    support_bind, Set.mem_iUnion, mem_support_pure_iff] at hy
  rcases hy with ⟨⟨resp, base'⟩, hp, _, rfl⟩; exact h (resp, base') hp
theorem nonRo_query_hyb_fields_eq_of_mem_support1Key {S : Setup} (stage : AuthHybridStage)
    (P : Primitives) (q : AuthQuery S) (hst : AuthHybridState S) (hq : isAuthNonRoQuery q = true)
    {y : AuthResponse × AuthHybridState S}
    (hy : y ∈ support ((pqxdhAuthHybridKoskImpl1Key stage true true S P q).run hst)) :
    y.2.base.roCache = hst.base.roCache ∧ y.2.idealSessions = hst.idealSessions ∧
    y.2.base.usedSendSessions = hst.base.usedSendSessions := by
  let Q : AuthHybridState S → Prop := fun s =>
    s.base.roCache = hst.base.roCache ∧
    s.idealSessions = hst.idealSessions ∧
    s.base.usedSendSessions = hst.base.usedSendSessions
  unfold pqxdhAuthHybridKoskImpl1Key at hy; rw [StateT.run_bind, StateT.run_get, pure_bind] at hy
  by_cases hWon : (true && hst.base.hasWonAuth) = true
  · simp only [hWon, ↓reduceIte, StateT.run_pure, mem_support_pure_iff] at hy
    rcases hy with ⟨_, rfl⟩; exact ⟨rfl, rfl, rfl⟩
  simp only [hWon, Bool.false_eq_true, ↓reduceIte] at hy
  cases q with
  | roQuery _ => nomatch hq
  | sendOPK _ _ _ _ _ => nomatch hq
  | sendNoOPK _ _ _ _ _ => nomatch hq
  | recvOPK _ _ _ _ => nomatch hq
  | recvNoOPK _ _ _ _ => nomatch hq
  | initPrin u =>
    refine prop_of_liftAuthBase_c6c1 Q _ hst (fun p hp => ?_) hy
    unfold pqxdhAuthImpl1KeyG at hp
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hp; dsimp only at hp
    split_ifs at hp
    · rw [StateT.run_pure, mem_support_pure_iff] at hp
      rcases hp with ⟨_, rfl⟩; exact ⟨rfl, rfl, rfl⟩
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
        StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        support_bind, Set.mem_iUnion, mem_support_pure_iff] at hp
      rcases hp with ⟨_, _, _, _, _, rfl⟩; exact ⟨rfl, rfl, rfl⟩
  | corruptIK u =>
    refine prop_of_liftAuthBase_c6c1 Q _ hst (fun p hp => ?_) hy
    unfold pqxdhAuthImpl1KeyG at hp
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hp; dsimp only at hp
    cases hF : hst.base.principals.find? (fun (idx, _) => idx == u.val) with
    | none =>
      rw [hF] at hp; dsimp only at hp; rw [StateT.run_pure, mem_support_pure_iff] at hp
      rcases hp with ⟨_, rfl⟩; exact ⟨rfl, rfl, rfl⟩
    | some ue =>
      rcases ue with ⟨_, entry⟩; rw [hF] at hp; dsimp only at hp
      rw [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure, mem_support_pure_iff] at hp
      rcases hp with ⟨_, rfl⟩; exact ⟨rfl, rfl, rfl⟩
  | genSPK u j =>
    refine prop_of_liftAuthBase_c6c1 Q _ hst (fun p hp => ?_) hy
    unfold pqxdhAuthImpl1KeyG at hp
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hp; dsimp only at hp
    split_ifs at hp
    · rw [StateT.run_pure, mem_support_pure_iff] at hp
      rcases hp with ⟨_, rfl⟩; exact ⟨rfl, rfl, rfl⟩
    · cases hF : hst.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none =>
        rw [hF] at hp; dsimp only at hp; rw [StateT.run_pure, mem_support_pure_iff] at hp
        rcases hp with ⟨_, rfl⟩; exact ⟨rfl, rfl, rfl⟩
      | some ue =>
        rcases ue with ⟨_, uEntry⟩; rw [hF] at hp; dsimp only at hp
        simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
          StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
          support_bind, Set.mem_iUnion, mem_support_pure_iff] at hp
        rcases hp with ⟨_, _, _, _, ⟨_, _⟩, _, _, _, _, rfl⟩; exact ⟨rfl, rfl, rfl⟩
  | genOPK u j o =>
    refine prop_of_liftAuthBase_c6c1 Q _ hst (fun p hp => ?_) hy
    unfold pqxdhAuthImpl1KeyG at hp
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hp; dsimp only at hp
    split_ifs at hp
    · rw [StateT.run_pure, mem_support_pure_iff] at hp
      rcases hp with ⟨_, rfl⟩; exact ⟨rfl, rfl, rfl⟩
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
        StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        support_bind, Set.mem_iUnion, mem_support_pure_iff] at hp
      rcases hp with ⟨_, _, _, rfl⟩; exact ⟨rfl, rfl, rfl⟩
  | registerKey sk =>
    refine prop_of_liftAuthBase_c6c1 Q _ hst (fun p hp => ?_) hy
    unfold pqxdhAuthImpl1KeyG at hp
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hp; dsimp only at hp
    cases hReg : registerAdvKey P hst.base.advKeys sk with
    | none =>
      rw [hReg] at hp; dsimp only at hp; rw [StateT.run_pure, mem_support_pure_iff] at hp
      rcases hp with ⟨_, rfl⟩; exact ⟨rfl, rfl, rfl⟩
    | some pa =>
      rcases pa with ⟨pk, advKeys'⟩; rw [hReg] at hp; dsimp only at hp
      rw [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure, mem_support_pure_iff] at hp
      rcases hp with ⟨_, rfl⟩; exact ⟨rfl, rfl, rfl⟩
  | roRootQuery rk dh =>
    refine prop_of_liftAuthBase_c6c1 Q _ hst (fun p hp => ?_) hy
    unfold pqxdhAuthImpl1KeyG at hp
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hp; dsimp only at hp
    split_ifs at hp
    · rw [StateT.run_pure, mem_support_pure_iff] at hp
      rcases hp with ⟨_, rfl⟩; exact ⟨rfl, rfl, rfl⟩
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
        StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        support_bind, Set.mem_iUnion, mem_support_pure_iff] at hp
      rcases hp with ⟨⟨_, _⟩, _, _, rfl⟩; exact ⟨rfl, rfl, rfl⟩
  | revealDhSecrets =>
    refine prop_of_liftAuthBase_c6c1 Q _ hst (fun p hp => ?_) hy
    unfold pqxdhAuthImpl1KeyG at hp
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hp; dsimp only at hp
    split_ifs at hp <;>
      (rw [StateT.run_pure, mem_support_pure_iff] at hp;
       rcases hp with ⟨_, rfl⟩; exact ⟨rfl, rfl, rfl⟩)
theorem nonRo_query_fields_eq_of_mem_support1Key {S : Setup} (stage : AuthHybridStage)
    (P : Primitives) (q : AuthQuery S) (s : AuthAdvLatchedState S) (hq : isAuthNonRoQuery q = true)
    {y : AuthResponse × AuthAdvLatchedState S}
    (hy : y ∈ support ((pqxdhAuthAdvLatchedStageImpl1Key stage S P q).run s)) :
    y.2.adv.hyb.base.roCache = s.adv.hyb.base.roCache ∧
    y.2.hyb.idealSessions = s.hyb.idealSessions ∧ y.2.adv.advRoLog = s.adv.advRoLog ∧
    y.2.adv.respRecs = s.adv.respRecs ∧
    y.2.hyb.base.usedSendSessions = s.hyb.base.usedSendSessions := by
  have hyHyb := mem_support_hyb_of_mem_support_pqxdhAuthAdvLatchedStageImpl1Key stage P q s hy
  rcases nonRo_query_hyb_fields_eq_of_mem_support1Key stage P q s.hyb hq hyHyb with
    ⟨hRo, hId, hUsed⟩
  have hyAdv := mem_support_adv_of_mem_support_pqxdhAuthAdvLatchedStageImpl1Key stage P q s y hy
  have hLogResp : y.2.adv.advRoLog = s.adv.advRoLog ∧ y.2.adv.respRecs = s.adv.respRecs := by
    cases q with
    | roQuery _ => nomatch hq
    | sendOPK _ _ _ _ _ => nomatch hq
    | sendNoOPK _ _ _ _ _ => nomatch hq
    | recvOPK _ _ _ _ => nomatch hq
    | recvNoOPK _ _ _ _ => nomatch hq
    | _ =>
      unfold pqxdhAuthAdvStageImpl1Key at hyAdv
      simp only [StateT.run_mk, support_bind, Set.mem_iUnion, mem_support_pure_iff] at hyAdv
      rcases hyAdv with ⟨⟨_, _⟩, _, hEq⟩
      injection hEq with _ hAdvEq; rw [hAdvEq]; exact ⟨rfl, rfl⟩
  exact ⟨hRo, hId, hLogResp.1, hLogResp.2, hUsed⟩
theorem authG3G3_5CoupledInv_of_nonRo_query1Key {S : Setup} (P : Primitives)
    (q : AuthQuery S) (s35 s3 : AuthAdvLatchedState S) (hq : isAuthNonRoQuery q = true)
    (hInv : AuthG3G3_5CoupledInv P s35 s3) {y3 : AuthResponse × AuthAdvLatchedState S}
    (hy3 : y3 ∈ support ((pqxdhAuthAdvLatchedStageImpl1Key .g3 S P q).run s3)) :
    AuthG3G3_5CoupledInv P (withAuthAdvLatchedRoCache s35.adv.hyb.base.roCache y3.2) y3.2 := by
  have hSub := authHybridTraceSub_pqxdhAuthAdvLatchedStageImpl1Key .g3 P q s3 hy3
  have hRun' := validAuthHybridRunInv_pqxdhAuthAdvLatchedStageImpl1Key .g3 P q s3 hInv.2.1 hy3
  rcases nonRo_query_fields_eq_of_mem_support1Key .g3 P q s3 hq hy3 with
    ⟨hRo, hId, hLog, hResp, hUsed⟩
  exact ⟨AuthAdvLatchedAgreeOffRo.of_withAuthAdvLatchedRoCache _ _, hRun',
    authRoCacheCoupled_of_traceSub_eq_roCache P hInv.2.2 hSub hRo hId
      (fun x hx => hLog ▸ hx) (fun x hx => hUsed ▸ hx) (fun x hx => hResp ▸ hx)⟩
theorem fgAuthStepCoupling_cutoff_latched_initPrin1Key
    (S : Setup) (P : Primitives) (maxRo : ℕ) (u : Fin S.N_id)
    (s35 s3 : AuthAdvLatchedState S) (hInv : AuthG3G3_5CoupledInv P s35 s3) : RelProbUpToBad
      (fun y35 y3 => (y35.1 = y3.1 ∧ AuthG3G3_5CoupledInv P y35.2 y3.2) ∨
        (isAuthG3Abort P y35.2.hyb = true ∧ isAuthG3Abort P y3.2.hyb = true))
      (fun y3 => badAuthFgAnyLatchedMono P maxRo y3.2.toFg)
      ((pqxdhAuthAdvLatchedStageImpl1Key .g3_5 S P (.initPrin u)).run s35)
      ((pqxdhAuthAdvLatchedStageImpl1Key .g3 S P (.initPrin u)).run s3) :=
  relProbUpToBad_of_withAuthAdvLatchedRoCache_comm1Key P (.initPrin u)
    (AuthG3G3_5CoupledInv P) (badAuthFgAnyLatchedMono P maxRo) s35 s3 hInv.1
    (pqxdhAuthAdvLatchedStageImpl_initPrin_withAuthAdvLatchedRoCache1Key S P u _ s3)
    (fun _ hy3 _ => Or.inl
      (authG3G3_5CoupledInv_of_nonRo_query1Key P (.initPrin u) s35 s3 rfl hInv hy3))
theorem fgAuthStepCoupling_cutoff_latched_corruptIK1Key
    (S : Setup) (P : Primitives) (maxRo : ℕ) (u : Fin S.N_id)
    (s35 s3 : AuthAdvLatchedState S) (hInv : AuthG3G3_5CoupledInv P s35 s3) : RelProbUpToBad
      (fun y35 y3 => (y35.1 = y3.1 ∧ AuthG3G3_5CoupledInv P y35.2 y3.2) ∨
        (isAuthG3Abort P y35.2.hyb = true ∧ isAuthG3Abort P y3.2.hyb = true))
      (fun y3 => badAuthFgAnyLatchedMono P maxRo y3.2.toFg)
      ((pqxdhAuthAdvLatchedStageImpl1Key .g3_5 S P (.corruptIK u)).run s35)
      ((pqxdhAuthAdvLatchedStageImpl1Key .g3 S P (.corruptIK u)).run s3) :=
  relProbUpToBad_of_withAuthAdvLatchedRoCache_comm1Key P (.corruptIK u)
    (AuthG3G3_5CoupledInv P) (badAuthFgAnyLatchedMono P maxRo) s35 s3 hInv.1
    (pqxdhAuthAdvLatchedStageImpl_corruptIK_withAuthAdvLatchedRoCache1Key S P u _ s3)
    (fun _ hy3 _ => Or.inl
      (authG3G3_5CoupledInv_of_nonRo_query1Key P (.corruptIK u) s35 s3 rfl hInv hy3))
theorem fgAuthStepCoupling_cutoff_latched_genSPK1Key
    (S : Setup) (P : Primitives) (maxRo : ℕ) (u : Fin S.N_id) (j : Fin S.N_recv)
    (s35 s3 : AuthAdvLatchedState S) (hInv : AuthG3G3_5CoupledInv P s35 s3) : RelProbUpToBad
      (fun y35 y3 => (y35.1 = y3.1 ∧ AuthG3G3_5CoupledInv P y35.2 y3.2) ∨
        (isAuthG3Abort P y35.2.hyb = true ∧ isAuthG3Abort P y3.2.hyb = true))
      (fun y3 => badAuthFgAnyLatchedMono P maxRo y3.2.toFg)
      ((pqxdhAuthAdvLatchedStageImpl1Key .g3_5 S P (.genSPK u j)).run s35)
      ((pqxdhAuthAdvLatchedStageImpl1Key .g3 S P (.genSPK u j)).run s3) :=
  relProbUpToBad_of_withAuthAdvLatchedRoCache_comm1Key P (.genSPK u j)
    (AuthG3G3_5CoupledInv P) (badAuthFgAnyLatchedMono P maxRo) s35 s3 hInv.1
    (pqxdhAuthAdvLatchedStageImpl_genSPK_withAuthAdvLatchedRoCache1Key S P u j _ s3)
    (fun _ hy3 _ => Or.inl
      (authG3G3_5CoupledInv_of_nonRo_query1Key P (.genSPK u j) s35 s3 rfl hInv hy3))
theorem fgAuthStepCoupling_cutoff_latched_genOPK1Key
    (S : Setup) (P : Primitives) (maxRo : ℕ) (u : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (s35 s3 : AuthAdvLatchedState S) (hInv : AuthG3G3_5CoupledInv P s35 s3) : RelProbUpToBad
      (fun y35 y3 => (y35.1 = y3.1 ∧ AuthG3G3_5CoupledInv P y35.2 y3.2) ∨
        (isAuthG3Abort P y35.2.hyb = true ∧ isAuthG3Abort P y3.2.hyb = true))
      (fun y3 => badAuthFgAnyLatchedMono P maxRo y3.2.toFg)
      ((pqxdhAuthAdvLatchedStageImpl1Key .g3_5 S P (.genOPK u j o)).run s35)
      ((pqxdhAuthAdvLatchedStageImpl1Key .g3 S P (.genOPK u j o)).run s3) :=
  relProbUpToBad_of_withAuthAdvLatchedRoCache_comm1Key P (.genOPK u j o)
    (AuthG3G3_5CoupledInv P) (badAuthFgAnyLatchedMono P maxRo) s35 s3 hInv.1
    (pqxdhAuthAdvLatchedStageImpl_genOPK_withAuthAdvLatchedRoCache1Key S P u j o _ s3)
    (fun _ hy3 _ => Or.inl
      (authG3G3_5CoupledInv_of_nonRo_query1Key P (.genOPK u j o) s35 s3 rfl hInv hy3))
theorem fgAuthStepCoupling_cutoff_latched_registerKey1Key
    (S : Setup) (P : Primitives) (maxRo : ℕ) (sk : Bytes)
    (s35 s3 : AuthAdvLatchedState S) (hInv : AuthG3G3_5CoupledInv P s35 s3) : RelProbUpToBad
      (fun y35 y3 => (y35.1 = y3.1 ∧ AuthG3G3_5CoupledInv P y35.2 y3.2) ∨
        (isAuthG3Abort P y35.2.hyb = true ∧ isAuthG3Abort P y3.2.hyb = true))
      (fun y3 => badAuthFgAnyLatchedMono P maxRo y3.2.toFg)
      ((pqxdhAuthAdvLatchedStageImpl1Key .g3_5 S P (.registerKey sk)).run s35)
      ((pqxdhAuthAdvLatchedStageImpl1Key .g3 S P (.registerKey sk)).run s3) :=
  relProbUpToBad_of_withAuthAdvLatchedRoCache_comm1Key P (.registerKey sk)
    (AuthG3G3_5CoupledInv P) (badAuthFgAnyLatchedMono P maxRo) s35 s3 hInv.1
    (pqxdhAuthAdvLatchedStageImpl_registerKey_withAuthAdvLatchedRoCache1Key S P sk _ s3)
    (fun _ hy3 _ => Or.inl
      (authG3G3_5CoupledInv_of_nonRo_query1Key P (.registerKey sk) s35 s3 rfl hInv hy3))
theorem fgAuthStepCoupling_cutoff_latched_roRootQuery1Key
    (S : Setup) (P : Primitives) (maxRo : ℕ) (rk dh : Bytes)
    (s35 s3 : AuthAdvLatchedState S) (hInv : AuthG3G3_5CoupledInv P s35 s3) : RelProbUpToBad
      (fun y35 y3 => (y35.1 = y3.1 ∧ AuthG3G3_5CoupledInv P y35.2 y3.2) ∨
        (isAuthG3Abort P y35.2.hyb = true ∧ isAuthG3Abort P y3.2.hyb = true))
      (fun y3 => badAuthFgAnyLatchedMono P maxRo y3.2.toFg)
      ((pqxdhAuthAdvLatchedStageImpl1Key .g3_5 S P (.roRootQuery rk dh)).run s35)
      ((pqxdhAuthAdvLatchedStageImpl1Key .g3 S P (.roRootQuery rk dh)).run s3) :=
  relProbUpToBad_of_withAuthAdvLatchedRoCache_comm1Key P (.roRootQuery rk dh)
    (AuthG3G3_5CoupledInv P) (badAuthFgAnyLatchedMono P maxRo) s35 s3 hInv.1
    (pqxdhAuthAdvLatchedStageImpl_roRootQuery_withAuthAdvLatchedRoCache1Key S P rk dh _ s3)
    (fun _ hy3 _ => Or.inl
      (authG3G3_5CoupledInv_of_nonRo_query1Key P (.roRootQuery rk dh) s35 s3 rfl hInv hy3))
theorem fgAuthStepCoupling_cutoff_latched_revealDhSecrets1Key (S : Setup) (P : Primitives) (maxRo : ℕ)
    (s35 s3 : AuthAdvLatchedState S) (hInv : AuthG3G3_5CoupledInv P s35 s3) : RelProbUpToBad
      (fun y35 y3 => (y35.1 = y3.1 ∧ AuthG3G3_5CoupledInv P y35.2 y3.2) ∨
        (isAuthG3Abort P y35.2.hyb = true ∧ isAuthG3Abort P y3.2.hyb = true))
      (fun y3 => badAuthFgAnyLatchedMono P maxRo y3.2.toFg)
      ((pqxdhAuthAdvLatchedStageImpl1Key .g3_5 S P .revealDhSecrets).run s35)
      ((pqxdhAuthAdvLatchedStageImpl1Key .g3 S P .revealDhSecrets).run s3) :=
  relProbUpToBad_of_withAuthAdvLatchedRoCache_comm1Key P .revealDhSecrets
    (AuthG3G3_5CoupledInv P) (badAuthFgAnyLatchedMono P maxRo) s35 s3 hInv.1
    (pqxdhAuthAdvLatchedStageImpl_revealDhSecrets_withAuthAdvLatchedRoCache1Key S P _ s3)
    (fun _ hy3 _ => Or.inl
      (authG3G3_5CoupledInv_of_nonRo_query1Key P .revealDhSecrets s35 s3 rfl hInv hy3))

private theorem validAuthHybridRunInv_withAuthHybRoCache {S : Setup} (P : Primitives)
    (rc : List (Bytes × DRKey)) (hst : AuthHybridState S) (hRun : ValidAuthHybridRunInv S P hst) :
    ValidAuthHybridRunInv S P (withAuthHybRoCache rc hst) := by
  have hSub : AuthHybridTraceSub hst (withAuthHybRoCache rc hst) :=
    ⟨⟨List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _,
      List.Sublist.refl _, List.Sublist.refl _⟩,
     List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _⟩
  exact ⟨validAuthKeyStoresFull_of_fields_eq hRun.1,
    validAllIdealAuthSessions_of_traceSub P hSub rfl hRun.2.1,
    validSentEvents_of_traceSub_and_eq P hSub rfl rfl hRun.2.2⟩
theorem fgAuthStepCoupling_cutoff_latched_roQuery1Key
    (S : Setup) (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (maxRo : ℕ) (secrets : Bytes) (s35 s3 : AuthAdvLatchedState S)
    (hInv : AuthG3G3_5CoupledInv P s35 s3) (hAbF : isAuthG3Abort P s3.hyb = false)
    (hRoStep : s3.adv.advRoLog.length + 1 ≤ maxRo) : RelProbUpToBad (fun y35 y3 =>
        (y35.1 = y3.1 ∧ AuthG3G3_5CoupledInv P y35.2 y3.2) ∨
        (isAuthG3Abort P y35.2.hyb = true ∧ isAuthG3Abort P y3.2.hyb = true))
      (fun y3 => badAuthFgAnyLatchedMono P maxRo y3.2.toFg)
      ((pqxdhAuthAdvLatchedStageImpl1Key .g3_5 S P (.roQuery secrets)).run s35)
      ((pqxdhAuthAdvLatchedStageImpl1Key .g3 S P (.roQuery secrets)).run s3) := by
  have hw := hP.toWellFormedPrimitivesδ
  rcases hInv with ⟨hAg, hRun, hSub35, hIdealIn3, hOrigin3, hDiffIdeal⟩
  refine relProbUpToBad_roQuery_of_cache_agree_or_bad1Key P secrets
    (AuthG3G3_5CoupledInv P) (badAuthFgAnyLatchedMono P maxRo) s35 s3 hAg
    (fun c' => badAuthFgAnyLatchedMono_updateRoQueryLatched P maxRo secrets c' s3)
    (hSub35 secrets) ?_ ?_ ?_
  · intro _
    refine ⟨?_, hRun, hSub35, hIdealIn3, ?_, hDiffIdeal⟩
    · unfold AuthAdvLatchedAgreeOffRo; rw [← withAuthAdvLatchedRoCache_updateRoQueryLatched]; rfl
    · intro sec' p' hF'
      rcases hOrigin3 sec' p' hF' with ⟨hp1, hInLog | hSess | hResp⟩
      · exact ⟨hp1, Or.inl (List.mem_cons_of_mem _ hInLog)⟩
      · exact ⟨hp1, Or.inr (Or.inl hSess)⟩
      · exact ⟨hp1, Or.inr (Or.inr hResp)⟩
  · intro dk hF35 hF3 _
    refine ⟨?_, validAuthHybridRunInv_withAuthHybRoCache P _ s3.hyb hRun, ?_, ?_, ?_, ?_⟩
    · unfold AuthAdvLatchedAgreeOffRo; rw [← withAuthAdvLatchedRoCache_updateRoQueryLatched]; rfl
    · intro sec' p' hF35'
      dsimp only [updateRoQueryLatched, withAuthHybRoCache, withAuthBaseRoCache,
        List.find?_cons] at hF35' ⊢
      cases hBeq : (secrets == sec')
      · rw [hBeq] at hF35'; exact hSub35 sec' p' hF35'
      · rw [hBeq] at hF35'; exact hF35'
    · intro s hs
      rcases hIdealIn3 s hs with ⟨sessEntry, u, uEntry, kemCoins, ss_s, initRec, hVi, hVh, hFindS⟩
      refine ⟨sessEntry, u, uEntry, kemCoins, ss_s, initRec, hVi, hVh, ?_⟩
      dsimp only [updateRoQueryLatched, withAuthHybRoCache, withAuthBaseRoCache, List.find?_cons]
      have hNe : (secrets == idealSessionSecrets P uEntry sessEntry.ekASk ss_s s) = false := by
        cases hBeq : (secrets == idealSessionSecrets P uEntry sessEntry.ekASk ss_s s)
        · rfl
        · dsimp only at hFindS
          rw [← beq_iff_eq.mp hBeq] at hFindS; rw [hF3] at hFindS; nomatch hFindS
      rw [hNe]; exact hFindS
    · intro sec' p' hF3'
      dsimp only [updateRoQueryLatched, withAuthHybRoCache, withAuthBaseRoCache,
        List.find?_cons] at hF3' ⊢
      cases hBeq : (secrets == sec')
      · rw [hBeq] at hF3'; rcases hOrigin3 sec' p' hF3' with ⟨hp1, hInLog | hSess | hResp⟩
        · exact ⟨hp1, Or.inl (List.mem_cons_of_mem _ hInLog)⟩
        · exact ⟨hp1, Or.inr (Or.inl hSess)⟩
        · exact ⟨hp1, Or.inr (Or.inr hResp)⟩
      · rw [hBeq] at hF3'
        injection hF3' with hp'; subst hp'; have hEq : secrets = sec' := beq_iff_eq.mp hBeq
        subst hEq; exact ⟨rfl, Or.inl List.mem_cons_self⟩
    · intro sec' p' hF35' hF3'
      dsimp only [updateRoQueryLatched, withAuthHybRoCache, withAuthBaseRoCache,
        List.find?_cons] at hF35' hF3'
      cases hBeq : (secrets == sec')
      · rw [hBeq] at hF35' hF3'; exact hDiffIdeal sec' p' hF35' hF3'
      · rw [hBeq] at hF35'; nomatch hF35'
  · intro p hF35 hF3
    left
    rcases hDiffIdeal secrets p hF35 hF3 with
      ⟨s, _, sessEntry, u, uEntry, kemCoins, ss_s, initRec, hVi, hVh, hSec, _⟩
    have hNoBadSig : hasBadSigAuth s3.hyb = false := by
      unfold isAuthG3Abort at hAbF; simp only [Bool.or_eq_false_iff] at hAbF; exact hAbF.1.1.2
    rcases validIdealSessionHonesty_imp_spk_and_pqspk_of_hasBadSigAuth_false
        P s3.hyb hNoBadSig hVi.1 hVh with ⟨⟨k_s, j_s, b_s, hbMem, hPowSpk⟩, _⟩
    have hPowSess : P.pow8 sessEntry.peerSpkPk = P.pow8 b_s.spkPk := by
      rw [hVi.2.2.2.2.2.1, hPowSpk]
    have hDh3 : extractDh3 secrets = P.x25519 sessEntry.ekASk sessEntry.peerSpkPk := by
      rw [hSec, hVi.2.2.2.2.2.1, extractDh3_idealSessionSecrets P hw]
    have hTake : secrets ∈ (secrets :: s3.adv.advRoLog).take maxRo := by
      cases hMax : maxRo with
      | zero => omega
      | succ m => simp
    exact badAuthFgAnyLatched_true_of_advRoLog_dh3 P hP maxRo
      { s3.toFg with advRoLog := secrets :: s3.adv.advRoLog }
      hRun.1 hVi.1 hbMem hPowSess hTake hDh3

def pqxdhAuthSendLatchedStageImpl1Key (stage : AuthHybridStage) (S : Setup) (P : Primitives) :
    QueryImpl (authSpec S) (StateT (AuthSendLatchedState S) ProbComp)
  | .sendOPK u i bundle m0 m1 => StateT.mk (fun s =>
    ((pqxdhAuthAdvLatchedStageImpl1Key stage S P (.sendOPK u i bundle m0 m1)).run
      s.toAuthAdvLatchedState) >>= fun p => pure (wrapSendLatched P s p))
  | .sendNoOPK u i bundle m0 m1 => StateT.mk (fun s =>
    ((pqxdhAuthAdvLatchedStageImpl1Key stage S P (.sendNoOPK u i bundle m0 m1)).run
      s.toAuthAdvLatchedState) >>= fun p => pure (wrapSendLatched P s p))
  | q => StateT.mk (fun s =>
    ((pqxdhAuthAdvLatchedStageImpl1Key stage S P q).run s.toAuthAdvLatchedState) >>=
      fun p => pure (p.1, { s with toAuthAdvLatchedState := p.2 }))

theorem fgAuthStepCoupling_cutoff_latched_sendOPK_or_respEkColl1Key
    (S : Setup) (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (maxRo : ℕ) (u : Fin S.N_id) (i : Fin S.N_send_opk) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (s35 s3 : AuthAdvLatchedState S) (hInv : AuthG3G3_5CoupledInv P s35 s3)
    (hAbF : isAuthG3Abort P s3.hyb = false) (hLogLen : s3.adv.advRoLog.length ≤ maxRo)
    (hRespLen : s3.adv.respRecs.length ≤ S.N_sess_tot) : RelProbUpToBad (fun y35 y3 =>
        (y35.1 = y3.1 ∧ AuthG3G3_5CoupledInv P y35.2 y3.2) ∨
        (isAuthG3Abort P y35.2.hyb = true ∧ isAuthG3Abort P y3.2.hyb = true))
      (fun y3 => badAuthFgAnyLatchedMono P maxRo y3.2.toFg ||
                 latchRespEkCollSendStep P s3 y3.2 false)
      ((pqxdhAuthAdvLatchedStageImpl1Key .g3_5 S P (.sendOPK u i bundle m0 m1)).run s35)
      ((pqxdhAuthAdvLatchedStageImpl1Key .g3 S P (.sendOPK u i bundle m0 m1)).run s3) := by
  refine relProbUpToBad_of_imp_support_right ?_
  have hStep : RelProbUpToBad
        (fun y35 y3 =>
          (y35.1 = y3.1 ∧ AuthAdvLatchedAgreeOffRo y35.2 y3.2 ∧ AuthRoCacheCoupled P y35.2 y3.2) ∨
          (isAuthG3Abort P y35.2.hyb = true ∧ isAuthG3Abort P y3.2.hyb = true))
        (fun y3 => badAuthFgAnyLatchedMono P maxRo y3.2.toFg ||
                   latchRespEkCollSendStep P s3 y3.2 false)
        ((pqxdhAuthAdvLatchedStageImpl1Key .g3_5 S P (.sendOPK u i bundle m0 m1)).run s35)
        ((pqxdhAuthAdvLatchedStageImpl1Key .g3 S P (.sendOPK u i bundle m0 m1)).run s3) := by
    unfold pqxdhAuthAdvLatchedStageImpl1Key pqxdhAuthAdvStageImpl1Key pqxdhAuthHybridKoskImpl1Key
    simp only [StateT.run_mk, StateT.run_bind, StateT.run_get, bind_assoc, pure_bind]
    have hWonEq : s35.adv.hyb.base.hasWonAuth = s3.adv.hyb.base.hasWonAuth := by rw [hInv.1]; rfl
    rw [hWonEq]
    by_cases hWon : (true && s3.adv.hyb.base.hasWonAuth) = true
    · simp only [hWon, ↓reduceIte, StateT.run_pure, pure_bind]
      exact RelProbUpToBad.of_pure (Or.inl ⟨rfl, hInv.1, hInv.2.2⟩)
    simp only [hWon, Bool.false_eq_true, ↓reduceIte]
    by_cases hNone : bundle.opkB?.isNone = true
    · simp only [hNone, ↓reduceIte, StateT.run_pure, pure_bind]
      exact RelProbUpToBad.of_pure (Or.inl ⟨rfl, hInv.1, hInv.2.2⟩)
    · simp only [hNone, Bool.false_eq_true, ↓reduceIte]
      exact relProbUpToBad_runAuthHybridSendKosk_latched P hP maxRo (.sendOPK u i) u rfl trivial
        bundle m0 m1 s35 s3 hInv hAbF hLogLen hRespLen
  refine RelProbUpToBad.mono hStep (fun y35 y3 hRel _ hy3 => ?_) (fun _ h => h)
  rcases hRel with ⟨hEq, hAg, hRc⟩ | hAb
  · exact Or.inl ⟨hEq, hAg,
      validAuthHybridRunInv_pqxdhAuthAdvLatchedStageImpl1Key .g3 P _ s3 hInv.2.1 hy3, hRc⟩
  · exact Or.inr hAb
theorem fgAuthStepCoupling_cutoff_latched_sendNoOPK_or_respEkColl1Key
    (S : Setup) (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (maxRo : ℕ) (u : Fin S.N_id) (i : Fin S.N_send_no_opk)
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes) (s35 s3 : AuthAdvLatchedState S)
    (hInv : AuthG3G3_5CoupledInv P s35 s3) (hAbF : isAuthG3Abort P s3.hyb = false)
    (hLogLen : s3.adv.advRoLog.length ≤ maxRo) (hRespLen : s3.adv.respRecs.length ≤ S.N_sess_tot) :
    RelProbUpToBad (fun y35 y3 => (y35.1 = y3.1 ∧ AuthG3G3_5CoupledInv P y35.2 y3.2) ∨
        (isAuthG3Abort P y35.2.hyb = true ∧ isAuthG3Abort P y3.2.hyb = true))
      (fun y3 => badAuthFgAnyLatchedMono P maxRo y3.2.toFg ||
                 latchRespEkCollSendStep P s3 y3.2 false)
      ((pqxdhAuthAdvLatchedStageImpl1Key .g3_5 S P (.sendNoOPK u i bundle m0 m1)).run s35)
      ((pqxdhAuthAdvLatchedStageImpl1Key .g3 S P (.sendNoOPK u i bundle m0 m1)).run s3) := by
  refine relProbUpToBad_of_imp_support_right ?_
  have hStep : RelProbUpToBad
        (fun y35 y3 =>
          (y35.1 = y3.1 ∧ AuthAdvLatchedAgreeOffRo y35.2 y3.2 ∧ AuthRoCacheCoupled P y35.2 y3.2) ∨
          (isAuthG3Abort P y35.2.hyb = true ∧ isAuthG3Abort P y3.2.hyb = true))
        (fun y3 => badAuthFgAnyLatchedMono P maxRo y3.2.toFg ||
                   latchRespEkCollSendStep P s3 y3.2 false)
        ((pqxdhAuthAdvLatchedStageImpl1Key .g3_5 S P (.sendNoOPK u i bundle m0 m1)).run s35)
        ((pqxdhAuthAdvLatchedStageImpl1Key .g3 S P (.sendNoOPK u i bundle m0 m1)).run s3) := by
    unfold pqxdhAuthAdvLatchedStageImpl1Key pqxdhAuthAdvStageImpl1Key pqxdhAuthHybridKoskImpl1Key
    simp only [StateT.run_mk, StateT.run_bind, StateT.run_get, bind_assoc, pure_bind]
    have hWonEq : s35.adv.hyb.base.hasWonAuth = s3.adv.hyb.base.hasWonAuth := by rw [hInv.1]; rfl
    rw [hWonEq]
    by_cases hWon : (true && s3.adv.hyb.base.hasWonAuth) = true
    · simp only [hWon, ↓reduceIte, StateT.run_pure, pure_bind]
      exact RelProbUpToBad.of_pure (Or.inl ⟨rfl, hInv.1, hInv.2.2⟩)
    simp only [hWon, Bool.false_eq_true, ↓reduceIte]
    by_cases hSome : bundle.opkB?.isSome = true
    · simp only [hSome, ↓reduceIte, StateT.run_pure, pure_bind]
      exact RelProbUpToBad.of_pure (Or.inl ⟨rfl, hInv.1, hInv.2.2⟩)
    · simp only [hSome, Bool.false_eq_true, ↓reduceIte]
      exact relProbUpToBad_runAuthHybridSendKosk_latched P hP maxRo (.sendNoOPK u i) u rfl trivial
        bundle m0 m1 s35 s3 hInv hAbF hLogLen hRespLen
  refine RelProbUpToBad.mono hStep (fun y35 y3 hRel _ hy3 => ?_) (fun _ h => h)
  rcases hRel with ⟨hEq, hAg, hRc⟩ | hAb
  · exact Or.inl ⟨hEq, hAg,
      validAuthHybridRunInv_pqxdhAuthAdvLatchedStageImpl1Key .g3 P _ s3 hInv.2.1 hy3, hRc⟩
  · exact Or.inr hAb
end Proofs.SignalPqxdh.Security
