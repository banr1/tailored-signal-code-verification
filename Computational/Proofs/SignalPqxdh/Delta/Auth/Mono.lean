/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Delta.AuthDefs
import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopC6c5
import VCVio.EvalDist.Monad.Basic

/-!
# PQXDH δ Authentication: Monotonicity of the KEM Correctness Bad Event

**Checked by Lean.** Proves `authCorrMono` (`AuthCorrMonoStmt`, DEV-PQ21): `hasBadAuthKemCorr` is
preserved along `.g3` send-latched steps because unfrozen steps only prepend to the KEM record lists
and frozen steps leave the state unchanged.
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal
open MeasureTheory
open OracleSpec OracleComp
open SignalPqxdh SignalPqxdh.Security
open Proofs.SignalPqxdh.Security

namespace Proofs.SignalPqxdh.Security.PqxdhDelta

private theorem am_unfrozen_sub (S : Setup) (P : Primitives)
    (q : AuthQuery S) (h : AuthHybridState S) (x : (authSpec S).Range q × AuthHybridState S)
    (hx : x ∈ support ((pqxdhAuthHybridKoskUnfrozenImpl S P q).run h)) :
    HybridRecsSub h x.2 := by
  cases q with
  | sendOPK u i bundle m0 m1 =>
    exact (SatisfiesAt.ite_return (HybridRecsSub h) h _ _ ⟨fun _ hi => hi, fun _ hr => hr⟩
      (fun _ => runAuthHybridSendKosk_g3_sub S P (.sendOPK u i) u bundle m0 m1 h)) x hx
  | sendNoOPK u i bundle m0 m1 =>
    exact (SatisfiesAt.ite_return (HybridRecsSub h) h _ _ ⟨fun _ hi => hi, fun _ hr => hr⟩
      (fun _ => runAuthHybridSendKosk_g3_sub S P (.sendNoOPK u i) u bundle m0 m1 h)) x hx
  | recvOPK k j o msg =>
    rcases pqxdhAuthHybridKoskImpl_recvOPK_step S P k j o msg h x hx with
      ⟨hInit, _, hRecv | ⟨_, _, _, _, _, hRecv⟩⟩
    · exact ⟨fun _ hi => hInit ▸ hi, fun _ hr => hRecv ▸ hr⟩
    · exact ⟨fun _ hi => hInit ▸ hi, fun _ hr => hRecv ▸ List.mem_cons_of_mem _ hr⟩
  | recvNoOPK k j l msg =>
    rcases pqxdhAuthHybridKoskImpl_recvNoOPK_step S P k j l msg h x hx with
      ⟨hInit, _, hRecv | ⟨_, _, _, _, _, hRecv⟩⟩
    · exact ⟨fun _ hi => hInit ▸ hi, fun _ hr => hRecv ▸ hr⟩
    · exact ⟨fun _ hi => hInit ▸ hi, fun _ hr => hRecv ▸ List.mem_cons_of_mem _ hr⟩
  | initPrin _ | corruptIK _ | genSPK _ _ | genOPK _ _ _ | roQuery _ | roRootQuery _ _
  | revealDhSecrets | registerKey _ =>
    change x ∈ support ((do
      let hst ← get; let st := hst.base
      if true && st.hasWonAuth then return AuthResponse.noneResp
      liftAuthBase (pqxdhAuthImpl true true S P _) :
        StateT (AuthHybridState S) ProbComp AuthResponse).run (clearHybridWon h)) at hx
    simp only [clearHybridWon, StateT.run_bind, StateT.run_get, Bool.and_false,
      Bool.false_eq_true, ↓reduceIte, pure_bind] at hx
    unfold liftAuthBase at hx
    simp only [StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      StateT.run_set, StateT.run_pure, pure_bind, bind_assoc,
      MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
    rcases hx with ⟨_, _, rfl⟩
    exact ⟨fun _ hi => hi, fun _ hr => hr⟩

theorem authCorrMono (S : Setup) : AuthCorrMonoStmt S := by
  intro P q s hBad y hy
  by_cases hWon : s.hyb.base.hasWonAuth = true
  · rw [hyb_eq_of_mem_support_pqxdhAuthSendLatchedStageImpl_of_hasWonAuth .g3 P q s hWon y hy]
    exact hBad
  · have hWonF : s.hyb.base.hasWonAuth = false := Bool.eq_false_iff.mpr hWon
    have hyAdv := mem_support_toAuthAdvLatchedState_of_mem_support_pqxdhAuthSendLatchedStageImpl
      .g3 P q s y hy
    have hyCut : (y.1, y.2.toAuthAdvLatchedState.adv) ∈
        support ((pqxdhAuthAdvStageImpl .g3 S P q).run s.adv) := by
      rw [← map_adv_pqxdhAuthAdvLatchedStageImpl .g3 S P q s.toAuthAdvLatchedState, support_map]
      exact ⟨(y.1, y.2.toAuthAdvLatchedState), hyAdv, rfl⟩
    have hyHyb : (y.1, y.2.hyb) ∈
        support ((pqxdhAuthHybridKoskImpl .g3 true true S P q).run s.hyb) := by
      have hMap := map_hyb_pqxdhAuthAdvStageImpl .g3 S P q s.adv
      change Prod.map id AuthAdvCutoffState.hyb <$> (pqxdhAuthAdvStageImpl .g3 S P q).run s.adv =
        (pqxdhAuthHybridKoskImpl .g3 true true S P q).run s.hyb at hMap
      rw [← hMap, support_map]
      exact ⟨(y.1, y.2.toAuthAdvLatchedState.adv), hyCut, rfl⟩
    rw [pqxdhAuthHybridKoskImpl_g3_eq_freeze S P q s.hyb] at hyHyb
    simp only [freezeImpl, StateT.run_bind, StateT.run_get, hWonF, Bool.false_eq_true,
      ↓reduceIte, pure_bind] at hyHyb
    have hSub := am_unfrozen_sub S P q s.hyb (y.1, y.2.hyb) hyHyb
    unfold hasBadAuthKemCorr at hBad ⊢
    rw [List.any_eq_true] at hBad ⊢
    rcases hBad with ⟨i, hi, hBadR⟩
    rw [List.any_eq_true] at hBadR
    rcases hBadR with ⟨r, hr, hPred⟩
    exact ⟨i, hSub.1 i hi, List.any_eq_true.mpr ⟨r, hSub.2 r hr, hPred⟩⟩

end Proofs.SignalPqxdh.Security.PqxdhDelta
