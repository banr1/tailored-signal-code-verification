/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Delta.AuthDefs
import VCVio.EvalDist.Monad.Basic

/-!
# PQXDH δ authentication: transfer of the KEM correctness bad event

**Checked by Lean.** Proves `authCorrTransfer` (`AuthCorrTransferStmt`, DEV-PQ21), bounding
`hasBadAuthKemCorr` in `runAuthSendLatchedSim .g3` by `hasBadKemCorrRecords` in `runAuthShCrSim`.
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal
open MeasureTheory
open OracleSpec OracleComp
open SignalPqxdh SignalPqxdh.Security
open Proofs.SignalPqxdh.Security

namespace Proofs.SignalPqxdh.Security.PqxdhDelta

private theorem at_runAuthSendLatchedSim_g3_hasBadAuthKemCorr_eq (S : Setup)
    (P : Primitives) (A : AuthAdversary S) :
    (runAuthSendLatchedSim .g3 S P A >>= fun x =>
        pure (hasBadAuthKemCorr P x.2.2.hyb)) =
      (runAuthKoskG3 S P A >>= fun (_, _, finalSt) =>
        pure (hasBadAuthKemCorr P finalSt)) := by
  unfold runAuthSendLatchedSim runAuthKoskG3
  simp only [bind_assoc, pure_bind]
  congr 1; funext secb
  have h1 := simulateQ_map_toAuthAdvLatchedState_fullAuthSendLatchedStageImpl
    .g3 S P A.run (AuthSendLatchedState.empty S secb)
  have h2 := simulateQ_map_adv_fullAuthAdvLatchedStageImpl
    .g3 S P A.run (AuthAdvLatchedState.empty S secb)
  dsimp only [AuthSendLatchedState.toAuthAdvLatchedState,
    AuthSendLatchedState.empty, AuthAdvLatchedState.empty,
    AuthAdvLatchedState.adv] at h1 h2
  have h3 := simulateQ_map_hyb_fullAuthAdvStageImpl
    .g3 S P A.run (AuthAdvCutoffState.empty S secb)
  dsimp only [AuthAdvCutoffState.hyb_empty] at h3
  rw [← h3, ← h2, ← h1]
  simp only [bind_map_left, Prod.map]
  rfl

private theorem at_unfrozen_hasBadAuthKemCorr_mono (S : Setup) (P : Primitives)
    (q : AuthQuery S) (h : AuthHybridState S) (x : (authSpec S).Range q × AuthHybridState S)
    (hx : x ∈ support ((pqxdhAuthHybridKoskUnfrozenImpl S P q).run h))
    (hBad : hasBadAuthKemCorr P h = true) :
    hasBadAuthKemCorr P x.2 = true := by
  have hSub : HybridRecsSub h x.2 := by
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
  unfold hasBadAuthKemCorr at hBad ⊢
  rw [List.any_eq_true] at hBad ⊢; rcases hBad with ⟨i, hi, hBadR⟩
  rw [List.any_eq_true] at hBadR; rcases hBadR with ⟨r, hr, hPred⟩
  exact ⟨i, hSub.1 i hi, List.any_eq_true.mpr ⟨r, hSub.2 r hr, hPred⟩⟩

private theorem at_hasBadAuthKemCorr_imp_hasBadKemCorrRecords {S : Setup} (P : Primitives)
    (hst : AuthHybridShCrState S) (hV : ValidHybridShCr S hst)
    (hSend : hst.sendCount ≤ S.N_send_tot)
    (hBad : hasBadAuthKemCorr P hst.base = true) :
    hasBadKemCorrRecords S P hst.initKemRecs hst.recvKemRecs = true := by
  unfold hasBadAuthKemCorr at hBad
  rw [List.any_eq_true] at hBad; rcases hBad with ⟨i, hi, hBadR⟩; rw [List.any_eq_true] at hBadR
  rcases hBadR with ⟨r, hr, hPred⟩; rcases hV.1 i hi with ⟨i', hi', rfl, hiLt⟩
  rcases hV.2 r hr with ⟨r', hr', rfl, hrLt⟩
  have hPred' : isKemCorrPair P i' r' = true := hPred
  have hiTot : i'.sendIdx < S.N_send_tot := Nat.lt_of_lt_of_le hiLt hSend
  have hPos : 0 < S.N_send_tot := Nat.pos_of_ne_zero (by omega)
  let idx := r'.bIdx * S.N_send_tot + i'.sendIdx
  have hIdxLt : idx < S.N_spk_tot * S.N_send_tot := by
    dsimp [idx]
    calc r'.bIdx * S.N_send_tot + i'.sendIdx
        < r'.bIdx * S.N_send_tot + S.N_send_tot := Nat.add_lt_add_left hiTot _
      _ = (r'.bIdx + 1) * S.N_send_tot := by ring
      _ ≤ S.N_spk_tot * S.N_send_tot := Nat.mul_le_mul_right _ hrLt
  have hDiv : idx / S.N_send_tot = r'.bIdx := by
    dsimp [idx]; rw [Nat.mul_comm, Nat.mul_add_div hPos, Nat.div_eq_of_lt hiTot, Nat.add_zero]
  have hMod : idx % S.N_send_tot = i'.sendIdx := by
    dsimp [idx]; rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hiTot]
  unfold hasBadKemCorrRecords; rw [List.any_eq_true]
  refine ⟨idx, List.mem_range.mpr hIdxLt, ?_⟩
  unfold hasBadKemCorrRecordsAt
  rw [hDiv, hMod, List.any_eq_true]; refine ⟨i', hi', ?_⟩
  simp only [beq_self_eq_true, Bool.true_and, List.any_eq_true]; exact ⟨r', hr', by simp [hPred']⟩

private theorem at_badKemCorrProbAuth_g3_unfrozen_le (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    (𝒟[runAuthKoskG3Unfrozen S P A.1 >>= fun (_, _, finalSt) =>
        pure (hasBadAuthKemCorr P finalSt)] {true}).toReal ≤
      (𝒟[runAuthShCrSim S P A.1 >>= fun x =>
        pure (hasBadKemCorrRecords S P x.2.2.initKemRecs x.2.2.recvKemRecs)] {true}).toReal := by
  have hLHS : (runAuthKoskG3Unfrozen S P A.1 >>= fun (_, _, finalSt) =>
        pure (hasBadAuthKemCorr P finalSt)) =
      (runAuthHybridShCr S P A.1 >>= fun (_, _, finalHst) =>
        pure (hasBadAuthKemCorr P finalHst.base)) := by
    rw [← runAuthHybridShCr_map_base S P A.1, bind_map_left]
  have hRHS : (runAuthShCrSim S P A.1 >>= fun x =>
        pure (hasBadKemCorrRecords S P x.2.2.initKemRecs x.2.2.recvKemRecs)) =
      (runAuthHybridShCr S P A.1 >>= fun (_, _, finalHst) =>
        pure (hasBadKemCorrRecords S P finalHst.initKemRecs finalHst.recvKemRecs)) := by
    rw [← runAuthHybridShCr_map_shcr S P hP A.1, bind_map_left]; rfl
  rw [hLHS, hRHS]
  refine toReal_bind_bool_mono_of_support (runAuthHybridShCr S P A.1)
    (fun (_, _, finalHst) => hasBadAuthKemCorr P finalHst.base)
    (fun (_, _, finalHst) => hasBadKemCorrRecords S P finalHst.initKemRecs finalHst.recvKemRecs)
    (fun ⟨secb, b', finalHst⟩ hmem => ?_)
  unfold runAuthHybridShCr at hmem
  simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hmem
  rcases hmem with ⟨secb0, _, ⟨b0, hst0⟩, hsim, hEq⟩
  injection hEq with _ hEq2; injection hEq2 with _ hEq3
  subst hEq3
  have hV0 : ValidHybridShCr S { base := AuthHybridState.empty S secb0 } :=
    ⟨(fun _ h => by cases h), (fun _ h => by cases h)⟩
  rcases simulateQ_pqxdhAuthHybridShCrImpl_invariant P A.1.run S.N_send_tot A.property.2.1
    { base := AuthHybridState.empty S secb0 } hV0 (b0, finalHst) hsim with ⟨hV, hSend⟩
  exact at_hasBadAuthKemCorr_imp_hasBadKemCorrRecords P finalHst hV (by simpa using hSend)

private theorem at_badKemCorrProbAuth_g3_le (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    (𝒟[runAuthKoskG3 S P A.1 >>= fun (_, _, finalSt) =>
        pure (hasBadAuthKemCorr P finalSt)] {true}).toReal ≤
      (𝒟[runAuthShCrSim S P A.1 >>= fun x =>
        pure (hasBadKemCorrRecords S P x.2.2.initKemRecs x.2.2.recvKemRecs)] {true}).toReal := by
  refine le_trans ?_ (at_badKemCorrProbAuth_g3_unfrozen_le S P hP b A)
  refine (ENNReal.toReal_le_toReal
    (MeasureTheory.measure_ne_top _ _) (MeasureTheory.measure_ne_top _ _)).mpr ?_
  unfold runAuthKoskG3 runAuthKoskG3Unfrozen
  rw [evalDist_bind_true_eq_probExpect_ite, evalDist_bind_true_eq_probExpect_ite]
  simp only [probExpect_bind, probExpect_pure]
  have hImplEq : pqxdhAuthHybridKoskImpl .g3 true true S P =
      freezeImpl (fun h : AuthHybridState S => h.base.hasWonAuth)
        (fun _ => .noneResp) (pqxdhAuthHybridKoskUnfrozenImpl S P) := by
    funext q; apply StateT.ext; intro h; exact pqxdhAuthHybridKoskImpl_g3_eq_freeze S P q h
  rw [hImplEq]
  refine probExpect_mono_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  have h := evalDist_simulateQ_bad_freeze_le_unfrozen
    (fun h : AuthHybridState S => h.base.hasWonAuth) (fun _ => .noneResp)
    (pqxdhAuthHybridKoskUnfrozenImpl S P) (hasBadAuthKemCorr P)
    (at_unfrozen_hasBadAuthKemCorr_mono S P)
    A.1.run (AuthHybridState.empty S secb)
  rwa [evalDist_bind_true_eq_probExpect_ite, evalDist_bind_true_eq_probExpect_ite] at h

/-- Transfers the KEM correctness bad event from `runAuthSendLatchedSim .g3` to `runAuthShCrSim`. -/
theorem authCorrTransfer (S : Setup) : AuthCorrTransferStmt S := by
  intro P hP b A
  rw [at_runAuthSendLatchedSim_g3_hasBadAuthKemCorr_eq S P A.1]
  exact at_badKemCorrProbAuth_g3_le S P hP b A

end Proofs.SignalPqxdh.Security.PqxdhDelta
