/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndGapDhProofsBase -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndGapDhProofsInit -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndGapDhProofsAccept -- proof-setup: allow-public-import
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndCoreSim
import Computational.Proofs.ReductionDsl.Size

/-!
# Cost and Query Bounds for `fgKeyIndGapDhProg`

Proves potential-function and bilinear DDH query bounds for the fine-grained `KeyInd` gap-DH
reduction `fgKeyIndGapDhProg`, discharging `gdhQueryBudget` compliance for bounded adversaries.
-/

public section

set_option autoImplicit false

open SignalPqxdh SignalPqxdh.Security SignalPqxdh.Security.FgGapDh
open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh.LegacyCosted
open OracleSpec OracleComp

namespace SignalPqxdh.Security.ReductionDsl.KeyIndGapDh
open SignalPqxdh.Security.ReductionDsl.KeyInd


/-- Potential induction across `simulateQ (handlerImpl h)` for any handler satisfying the 3-way
    RO / session / other `DdhStep` contract with state projection `fgLOf : σ.denote → List fgPatchEntryTy.denote`. -/
theorem simulateQ_handlerImpl_ddhPhi {S : Setup} {σ : PT} {α : Type}
    (fgLOf : σ.denote → List fgPatchEntryTy.denote)
    (h : Comp pqxdhOps pqGapDhIface [σ, (keyIndCodec S).Q] (.prod (keyIndCodec S).R σ))
    (hStepRo : ∀ st gq, isRoQ gq = true →
      DdhStep (4 * fgSDone (fgLOf st))
        (fun p => fgRDone (fgLOf p.2) ≤ fgRDone (fgLOf st) + 1 ∧ fgSDone (fgLOf p.2) = fgSDone (fgLOf st))
        (h.eval (.cons st (.cons ((keyIndCodec S).qenc gq) .nil))))
    (hStepSess : ∀ st gq, isSessQ gq = true →
      DdhStep (4 * (fgRDone (fgLOf st) + fgSDone (fgLOf st)))
        (fun p =>
          let r := fgRDone (fgLOf st)
          let s := fgSDone (fgLOf st)
          (fgRDone (fgLOf p.2) = r ∧ fgSDone (fgLOf p.2) = s) ∨
          (fgRDone (fgLOf p.2) = r + 1 ∧ fgSDone (fgLOf p.2) = s) ∨
          (fgRDone (fgLOf p.2) = r ∧ fgSDone (fgLOf p.2) = s + 1))
        (h.eval (.cons st (.cons ((keyIndCodec S).qenc gq) .nil))))
    (hStepOther : ∀ st gq, isRoQ gq = false → isSessQ gq = false →
      DdhStep 0 (fun p => fgLOf p.2 = fgLOf st)
        (h.eval (.cons st (.cons ((keyIndCodec S).qenc gq) .nil))))
    (oa : OracleComp (unifSpec + keyIndSpec S) α) :
    ∀ (r_rem s_rem : ℕ) (st : σ.denote),
      oa.IsQueryBoundP (onGame (G := keyIndSpec S) (fun t => isRoQ t = true)) r_rem →
      oa.IsQueryBoundP (onGame (G := keyIndSpec S) (fun t => isSessQ t = true)) s_rem →
      ((simulateQ (handlerImpl (C := keyIndCodec S) h) oa).run st).IsQueryBoundP
        (fun q => q.isRight = true)
        (fgDdhPhi (fgRDone (fgLOf st)) (fgSDone (fgLOf st)) r_rem s_rem) := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro r_rem s_rem st _ _
    simp [simulateQ_pure]
  | query_bind t mx ih =>
    intro r_rem s_rem st hRo hSess
    rw [isQueryBoundP_query_bind_iff] at hRo hSess
    rw [simulateQ_query_bind, StateT.run_bind]
    rcases t with uq | gq
    · have hStep0 : (((handlerImpl (C := keyIndCodec S) h) (.inl uq)).run st).IsQueryBoundP
          (fun q => q.isRight = true) 0 := by
        have hb := isQueryBoundP_bind (n := 0) (m := 0) (hUDdh uq)
          (fun u _ => isQueryBoundP_pure (fun q : (PrimBaseSpec + gapDhDdhOracle.spec).Domain => q.isRight = true) (u, st) 0)
        simpa [handlerImpl] using hb
      refine (isQueryBoundP_bind (n := 0)
        (m := fgDdhPhi (fgRDone (fgLOf st)) (fgSDone (fgLOf st)) r_rem s_rem)
        hStep0 fun x hx => ?_).mono (by omega)
      have hst : x.2 = st := by
        simp only [handlerImpl, StateT.run_lift, mem_support_bind_iff, support_pure,
          Set.mem_singleton_iff] at hx
        obtain ⟨_, _, rfl⟩ := hx; rfl
      rw [← hst]
      exact ih x.1 r_rem s_rem x.2
        (by simpa [onGame] using hRo.2 x.1)
        (by simpa [onGame] using hSess.2 x.1)
    · cases hR : isRoQ gq
      · cases hS : isSessQ gq
        · have hs := hStepOther st gq hR hS
          have hRun : (((handlerImpl (C := keyIndCodec S) h) (.inr gq)).run st).IsQueryBoundP
              (fun q => q.isRight = true) 0 := by
            have hb := isQueryBoundP_bind (n := 0) (m := 0) hs.1
              (fun p _ => isQueryBoundP_pure _ ((keyIndCodec S).rdec gq p.1, p.2) 0)
            simpa [handlerImpl] using hb
          refine (isQueryBoundP_bind (n := 0)
            (m := fgDdhPhi (fgRDone (fgLOf st)) (fgSDone (fgLOf st)) r_rem s_rem)
            hRun fun x hx => ?_).mono (by omega)
          simp only [handlerImpl, StateT.run_mk, mem_support_bind_iff, support_pure,
            Set.mem_singleton_iff] at hx
          obtain ⟨p, hp, rfl⟩ := hx
          have hEq := hs.2 p hp
          have hCont := ih ((keyIndCodec S).rdec gq p.1) r_rem s_rem p.2
            (by simpa [onGame, hR] using hRo.2 ((keyIndCodec S).rdec gq p.1))
            (by simpa [onGame, hS] using hSess.2 ((keyIndCodec S).rdec gq p.1))
          rwa [hEq] at hCont
        · have hPos : 0 < s_rem := hSess.1.resolve_left (by simp [onGame, hS])
          obtain ⟨s', rfl⟩ : ∃ s', s_rem = s' + 1 := ⟨s_rem - 1, by omega⟩
          have hs := hStepSess st gq hS
          have hRun : (((handlerImpl (C := keyIndCodec S) h) (.inr gq)).run st).IsQueryBoundP
              (fun q => q.isRight = true) (4 * (fgRDone (fgLOf st) + fgSDone (fgLOf st))) := by
            have hb := isQueryBoundP_bind (n := 4 * (fgRDone (fgLOf st) + fgSDone (fgLOf st))) (m := 0) hs.1
              (fun p _ => isQueryBoundP_pure _ ((keyIndCodec S).rdec gq p.1, p.2) 0)
            simpa [handlerImpl] using hb
          refine (isQueryBoundP_bind
            (n := 4 * (fgRDone (fgLOf st) + fgSDone (fgLOf st)))
            (m := fgDdhPhi (fgRDone (fgLOf st)) (fgSDone (fgLOf st) + 1) r_rem s')
            hRun fun x hx => ?_).mono (by rw [fgDdhPhi_sess_step])
          simp only [handlerImpl, StateT.run_mk, mem_support_bind_iff, support_pure,
            Set.mem_singleton_iff] at hx
          obtain ⟨p, hp, rfl⟩ := hx
          exact (ih ((keyIndCodec S).rdec gq p.1) r_rem s' p.2
            (by simpa [onGame, hR] using hRo.2 ((keyIndCodec S).rdec gq p.1))
            (by simpa [onGame, hS] using hSess.2 ((keyIndCodec S).rdec gq p.1))).mono
            (fgDdhPhi_le_sess_inc (hs.2 p hp) r_rem s')
      · have hS : isSessQ gq = false := by cases gq <;> simp_all [isRoQ, isSessQ]
        have hPos : 0 < r_rem := hRo.1.resolve_left (by simp [onGame, hR])
        obtain ⟨r', rfl⟩ : ∃ r', r_rem = r' + 1 := ⟨r_rem - 1, by omega⟩
        have hs := hStepRo st gq hR
        have hRun : (((handlerImpl (C := keyIndCodec S) h) (.inr gq)).run st).IsQueryBoundP
            (fun q => q.isRight = true) (4 * fgSDone (fgLOf st)) := by
          have hb := isQueryBoundP_bind (n := 4 * fgSDone (fgLOf st)) (m := 0) hs.1
            (fun p _ => isQueryBoundP_pure _ ((keyIndCodec S).rdec gq p.1, p.2) 0)
          simpa [handlerImpl] using hb
        refine (isQueryBoundP_bind
          (n := 4 * fgSDone (fgLOf st))
          (m := fgDdhPhi (fgRDone (fgLOf st) + 1) (fgSDone (fgLOf st)) r' s_rem)
          hRun fun x hx => ?_).mono (by rw [fgDdhPhi_ro_step])
        simp only [handlerImpl, StateT.run_mk, mem_support_bind_iff, support_pure,
          Set.mem_singleton_iff] at hx
        obtain ⟨p, hp, rfl⟩ := hx
        obtain ⟨hr_le, hs_eq⟩ := hs.2 p hp
        have hCont := ih ((keyIndCodec S).rdec gq p.1) r' s_rem p.2
          (by simpa [onGame, hR] using hRo.2 ((keyIndCodec S).rdec gq p.1))
          (by simpa [onGame, hS] using hSess.2 ((keyIndCodec S).rdec gq p.1))
        rw [hs_eq] at hCont
        exact hCont.mono (fgDdhPhi_mono hr_le le_rfl le_rfl)

/-- Semantic bilinear DDH query bound for `(fgKeyIndGapDhProg S K).eval A (U, V)` when `A` makes at
    most `r_max` random-oracle queries and at most `s_max` session queries. -/
theorem fgKeyIndGapDhProg_chalBounded_bilinear (S : Setup) (K r_max s_max : Nat)
    (A : Unit → OracleComp (unifSpec + keyIndSpec S) Bool)
    (hRo : ∀ a, (A a).IsQueryBoundP (onGame (G := keyIndSpec S) (fun t => isRoQ t = true)) r_max)
    (hSess : ∀ a, (A a).IsQueryBoundP (onGame (G := keyIndSpec S) (fun t => isSessQ t = true)) s_max)
    (U V : Bytes) :
    ((fgKeyIndGapDhProg S K).eval A (U, V)).IsQueryBoundP
      (fun q => q.isRight = true)
      (4 * r_max * s_max + 2 * s_max * (s_max - 1) + K + min K S.N_dh + min K S.N_sess_tot) := by
  have hInit : DdhStep 0 (fun as : Unit × gdhStateTy.denote => as.2.2.2.1 = [])
      (((fgKeyIndGapDhProg S K).init).eval (.cons (U, V) .nil)) := by
    change DdhStep 0 _ ((bindV (initAdv4 S (.fst (.var .zero)) (.snd (.var .zero))) fun s =>
      .ret (.pair .unit (v s))).eval (.cons (U, V) .nil))
    unfold initAdv4
    refine ddhStep_mono (m₁ := 0 + 0) (by omega) (fun x hx => hx)
      (ddhStep_bindV (Q₁ := fun s : gdhStateTy.denote => s.2.2.1 = []) _ _ _ ?_ fun s hs => ?_)
    · ddh_step_auto
      simp [emptySimE, smMk, Expr.eval]
    · exact ddhStep_ret _ _ (by simpa [v, Expr.eval] using hs)
  unfold CostedReduction.eval CostedReduction.impl
  refine (isQueryBoundP_bind (n := 0)
    (m := 4 * r_max * s_max + 2 * s_max * (s_max - 1) + (K + min K S.N_dh + min K S.N_sess_tot))
    hInit.1 fun as has => ?_).mono (by omega)
  have hEmpty := hInit.2 as has
  have hSim := simulateQ_handlerImpl_ddhPhi (fun s : gdhStateTy.denote => s.2.2.1)
    (gdhHandle S K) (gdhHandle_ddhStep_ro S K) (gdhHandle_ddhStep_sess S K)
    (gdhHandle_ddhStep_other S K) (A as.1) r_max s_max as.2 (hRo as.1) (hSess as.1)
  rw [hEmpty, show fgRDone [] = 0 from rfl, show fgSDone [] = 0 from rfl,
    fgDdhPhi_zero_done] at hSim
  refine isQueryBoundP_bind
    (n := 4 * r_max * s_max + 2 * s_max * (s_max - 1))
    (m := K + min K S.N_dh + min K S.N_sess_tot)
    hSim fun bs _ => ?_
  have hFin := Comp.queryBound_eval (fun q => q.isRight = true) wDdhGdh wsZero hwDdh hUDdh
    (gdhFinish S K) (.cons bs.2 (.cons bs.1 .nil))
  rwa [gdhFinish_chalQueries] at hFin

/-- Semantic `gdhQueryBudget S b` DDH query bound for `fgKeyIndGapDhProg` against any `b`-bounded
    `KeyInd` adversary `A`. -/
theorem fgKeyIndGapDhProg_chalBounded_gdhQueryBudget (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) (U V : Bytes) :
    ((fgKeyIndGapDhProg S b.q_total).eval (fun _ => A.1.run) (U, V)).IsQueryBoundP
      (fun q => q.isRight = true) (gdhQueryBudget S b) := by
  obtain ⟨hRoRaw, hSend, hRecv, hTotRaw, hOnRaw⟩ := A.2
  have hTot : A.1.run.IsQueryBoundP (ReductionDsl.isGameQuery (G := keyIndSpec S)) b.q_total := by
    convert hTotRaw using 1
    funext q; cases q
    · exact propext ⟨False.elim, Bool.noConfusion⟩
    · exact propext ⟨fun _ => rfl, fun _ => trivial⟩
  let M_ro := min b.q_ro b.q_total
  let M_sess := min (min b.q_on b.q_total) S.N_sess_tot
  by_cases hLe : 4 * b.q_total ^ 2 ≤ 4 * M_ro * M_sess + 2 * M_sess * (M_sess - 1)
  · refine (fgKeyIndGapDhProg_chalBounded S b.q_total b.q_total (fun _ => A.1.run)
      (fun _ => hTot) U V).mono ?_
    unfold gdhQueryBudget
    dsimp only
    change 4 * b.q_total * b.q_total + b.q_total + min b.q_total S.N_dh + min b.q_total S.N_sess_tot ≤
      min (4 * b.q_total ^ 2) (4 * M_ro * M_sess + 2 * M_sess * (M_sess - 1)) +
        b.q_total + S.N_dh + S.N_sess_tot
    rw [Nat.min_eq_left hLe]
    have md : min b.q_total S.N_dh ≤ S.N_dh := Nat.min_le_right _ _
    have ms : min b.q_total S.N_sess_tot ≤ S.N_sess_tot := Nat.min_le_right _ _
    nlinarith
  · have hMin : min (4 * b.q_total ^ 2) (4 * M_ro * M_sess + 2 * M_sess * (M_sess - 1)) =
        4 * M_ro * M_sess + 2 * M_sess * (M_sess - 1) :=
      Nat.min_eq_right (Nat.le_of_not_le hLe)
    have hRoOn : A.1.run.IsQueryBoundP (onGame (G := keyIndSpec S) (fun t => isRoQ t = true)) b.q_ro := by
      refine isQueryBoundP_of_imp (fun t ht => ?_) hRoRaw
      rcases t with _ | gq
      · exact ht.elim
      · cases gq <;> simp_all [onGame, isRoQ, isKeyIndRoQuery]
    have hSessOn : A.1.run.IsQueryBoundP
        (onGame (G := keyIndSpec S) (fun t => isSessQ t = true)) S.N_sess_tot := by
      refine isQueryBoundP_or_add (p₁ := isKeyIndSendQuery) (p₂ := isKeyIndRecvQuery) ?_ hSend hRecv
      intro t ht
      rcases t with _ | gq
      · exact ht.elim
      · cases gq <;> simp_all [onGame, isSessQ, isKeyIndSendQuery, isKeyIndRecvQuery]
    have hSessQOn : A.1.run.IsQueryBoundP
        (onGame (G := keyIndSpec S) (fun t => isSessQ t = true)) b.q_on := by
      refine isQueryBoundP_of_imp (fun t ht => ?_) hOnRaw
      rcases t with _ | gq
      · exact ht.elim
      · cases gq <;> simp_all [onGame, isSessQ, isKeyIndOnlineQuery]
    have hSessOnTot : A.1.run.IsQueryBoundP
        (onGame (G := keyIndSpec S) (fun t => isSessQ t = true)) (min b.q_on b.q_total) := by
      by_cases hOnLe : b.q_on ≤ b.q_total
      · simpa [Nat.min_eq_left hOnLe] using hSessQOn
      · simpa [Nat.min_eq_right (Nat.le_of_not_le hOnLe)] using isQueryBoundP_of_imp
          (fun t (ht : onGame (G := keyIndSpec S) (fun t => isSessQ t = true) t) => by
            cases t with | inl _ => exact ht.elim | inr _ => trivial) hTot
    have hRoM : A.1.run.IsQueryBoundP (onGame (G := keyIndSpec S) (fun t => isRoQ t = true)) M_ro := by
      by_cases h1 : b.q_ro ≤ b.q_total
      · simpa [M_ro, Nat.min_eq_left h1] using hRoOn
      · simpa [M_ro, Nat.min_eq_right (Nat.le_of_not_le h1)] using isQueryBoundP_of_imp
          (fun t (ht : onGame (G := keyIndSpec S) (fun t => isRoQ t = true) t) => by
            cases t with | inl _ => exact ht.elim | inr _ => trivial) hTot
    have hSessM : A.1.run.IsQueryBoundP (onGame (G := keyIndSpec S) (fun t => isSessQ t = true)) M_sess := by
      by_cases h2 : min b.q_on b.q_total ≤ S.N_sess_tot
      · simpa [M_sess, Nat.min_eq_left h2] using hSessOnTot
      · simpa [M_sess, Nat.min_eq_right (Nat.le_of_not_le h2)] using hSessOn
    refine (fgKeyIndGapDhProg_chalBounded_bilinear S b.q_total M_ro M_sess
      (fun _ => A.1.run) (fun _ => hRoM) (fun _ => hSessM) U V).mono ?_
    unfold gdhQueryBudget
    dsimp only
    change 4 * M_ro * M_sess + 2 * M_sess * (M_sess - 1) + b.q_total +
        min b.q_total S.N_dh + min b.q_total S.N_sess_tot ≤
      min (4 * b.q_total ^ 2) (4 * M_ro * M_sess + 2 * M_sess * (M_sess - 1)) +
        b.q_total + S.N_dh + S.N_sess_tot
    rw [hMin]
    have md : min b.q_total S.N_dh ≤ S.N_dh := Nat.min_le_right _ _
    have ms : min b.q_total S.N_sess_tot ≤ S.N_sess_tot := Nat.min_le_right _ _
    omega

end SignalPqxdh.Security.ReductionDsl.KeyIndGapDh
