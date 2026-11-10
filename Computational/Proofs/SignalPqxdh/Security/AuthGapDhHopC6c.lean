/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopC6b
public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopC2b
import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopC5
import VCVio.EvalDist.Monad.Basic

/-!
# `Auth` hybrid hop `G3 → G3.5`: step couplings and monotone bad events

Establishes the latched `GapDH` bound on `badAuthFgAnyLatched`, the `.roQuery` step coupling,
the `.g3`/`.g3_5` receiver schedule factorization, and the guarded monotone bad-event variants.
-/

@[expose] public section

set_option autoImplicit false
open Classical
open SignalPqxdh SignalPqxdh.Security
open OracleSpec OracleComp
open scoped ENNReal BigOperators
open Proofs.SignalPqxdh.Security.FgGapDh

namespace Proofs.SignalPqxdh.Security

/-! ## Latched `GapDH` bound -/

theorem authFgDh1LatchedCoupling (S : Setup) : AuthFgDh1LatchedCouplingStmt S :=
  fun b P hP A u hu bI hb =>
    prob_badAuthFgDh1LatchedAt_le_gapDh S b P hP A u hu bI hb

/-- Combined `GapDH` bound on `badAuthFgAnyLatched` under `runAuthFgLatchedSim`. -/
theorem prob_badAuthFgAnyLatched_runAuthFgLatchedSim_le_gapDh (S : Setup)
    (b : QueryBudget) (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (A : BoundedAdv (AuthAdversary S) b) :
    (𝒟[runAuthFgLatchedSim S P A.1 >>= fun x =>
        pure (badAuthFgAnyLatched P b.q_ro x.2.2)] {true}).toReal ≤
      ((S.N_spk_tot : ℝ) * ((S.N_id : ℝ) + (S.N_send_tot : ℝ)) +
        (S.N_id : ℝ) * (S.N_send_tot : ℝ) +
        (S.N_opk_tot : ℝ) * (S.N_send_opk_tot : ℝ)) *
        GapDH P P.isValidDhTriple P.pow8 (fgAuthGapDhAdv4 S b A) :=
  prob_badAuthFgAnyLatched_runAuthFgLatchedSim_le_gapDh_of_dh1 S b P hP A
    (fun uIdx huIdx bIdx hbIdx =>
      authFgDh1LatchedCoupling S b P hP A uIdx huIdx bIdx hbIdx)

/-! ## Invariant and query-budget preservation -/

theorem validAuthHybridRunInv_pqxdhAuthAdvLatchedStageImpl
    {S : Setup} (stage : AuthHybridStage) (P : Primitives)
    (q : AuthQuery S)
    (s : AuthAdvLatchedState S) (hInv : ValidAuthHybridRunInv S P s.hyb)
    {y : AuthResponse × AuthAdvLatchedState S}
    (hy : y ∈ support ((pqxdhAuthAdvLatchedStageImpl stage S P q).run s)) :
    ValidAuthHybridRunInv S P y.2.hyb :=
  validAuthHybridRunInv_pqxdhAuthAdvStageImpl stage P q s.adv hInv
    (mem_support_adv_of_mem_support_pqxdhAuthAdvLatchedStageImpl stage P q s y hy)

theorem isAuthG3Abort_eq_of_latchedAgreeOffRo {S : Setup} (P : Primitives)
    {s35 s3 : AuthAdvLatchedState S} (hAg : AuthAdvLatchedAgreeOffRo s35 s3) :
    isAuthG3Abort P s35.hyb = isAuthG3Abort P s3.hyb := by
  rw [hAg]
  exact isAuthG3Abort_withAuthAdvRoCache P _ s3.adv

theorem finalizeAuthKosk_eq_of_latchedAgreeOffRo {S : Setup} (P : Primitives)
    (secb b' : Bool) {s35 s3 : AuthAdvLatchedState S}
    (hAg : AuthAdvLatchedAgreeOffRo s35 s3) :
    finalizeAuthKosk S P secb b' s35.hyb = finalizeAuthKosk S P secb b' s3.hyb := by
  rw [hAg]; rfl

theorem authRoStepInc_le_of_queryGuard {S : Setup} (gq : AuthQuery S)
    {curLen fuelRo maxRo : ℕ}
    (hGuard : ¬isAuthRoQuery (Sum.inr gq) ∨ 0 < fuelRo)
    (hBudget : curLen + fuelRo ≤ maxRo) :
    curLen + authRoStepInc gq ≤ maxRo ∧
    curLen + authRoStepInc gq +
      (if isAuthRoQuery (Sum.inr gq) then fuelRo - 1 else fuelRo) ≤ maxRo := by
  rw [authRoStepInc_eq_ite]
  by_cases hPRo : isAuthRoQuery (Sum.inr gq)
  · rcases hGuard with hF | hPos
    · exact False.elim (hF hPRo)
    · simp only [hPRo, ↓reduceIte]; omega
  · simp only [hPRo, ↓reduceIte]; omega

theorem authRecvStepInc_le_of_queryGuard {S : Setup} (gq : AuthQuery S)
    {curLen fuelRecv maxRecv : ℕ}
    (hGuard : ¬isAuthRecvQuery (Sum.inr gq) ∨ 0 < fuelRecv)
    (hBudget : curLen + fuelRecv ≤ maxRecv) :
    curLen + authRecvStepInc gq ≤ maxRecv ∧
    curLen + authRecvStepInc gq +
      (if isAuthRecvQuery (Sum.inr gq) then fuelRecv - 1 else fuelRecv) ≤ maxRecv := by
  rw [authRecvStepInc_eq_ite]
  by_cases hPRecv : isAuthRecvQuery (Sum.inr gq)
  · rcases hGuard with hF | hPos
    · exact False.elim (hF hPRecv)
    · simp only [hPRecv, ↓reduceIte]; omega
  · simp only [hPRecv, ↓reduceIte]; omega

/-! ## Random-oracle query coupling -/

@[simp]
theorem badAuthFgAnyLatched_withAuthAdvLatchedRoCache {S : Setup} (P : Primitives)
    (maxLen : ℕ) (c : List (Bytes × DRKey)) (s : AuthAdvLatchedState S) :
    badAuthFgAnyLatched P maxLen (withAuthAdvLatchedRoCache c s).toFg =
      badAuthFgAnyLatched P maxLen s.toFg := rfl

theorem pqxdhAuthAdvLatchedStageImpl_initPrin_withAuthAdvLatchedRoCache
    (S : Setup) (P : Primitives) (u : Fin S.N_id)
    (c : List (Bytes × DRKey)) (s : AuthAdvLatchedState S) :
    (pqxdhAuthAdvLatchedStageImpl .g3_5 S P (.initPrin u)).run
        (withAuthAdvLatchedRoCache c s) =
      Prod.map id (withAuthAdvLatchedRoCache c) <$>
        ((pqxdhAuthAdvLatchedStageImpl .g3 S P (.initPrin u)).run s) :=
  pqxdhAuthAdvLatchedStageImpl_withAuthAdvLatchedRoCache_of_nonCorrupt P (.initPrin u)
    (fun _ h => nomatch h) c s
    (pqxdhAuthAdvStageImpl_initPrin_withAuthAdvRoCache S P u c s.adv)

theorem pqxdhAuthAdvLatchedStageImpl_genSPK_withAuthAdvLatchedRoCache
    (S : Setup) (P : Primitives) (u : Fin S.N_id) (j : Fin S.N_recv)
    (c : List (Bytes × DRKey)) (s : AuthAdvLatchedState S) :
    (pqxdhAuthAdvLatchedStageImpl .g3_5 S P (.genSPK u j)).run
        (withAuthAdvLatchedRoCache c s) =
      Prod.map id (withAuthAdvLatchedRoCache c) <$>
        ((pqxdhAuthAdvLatchedStageImpl .g3 S P (.genSPK u j)).run s) :=
  pqxdhAuthAdvLatchedStageImpl_withAuthAdvLatchedRoCache_of_nonCorrupt P (.genSPK u j)
    (fun _ h => nomatch h) c s
    (pqxdhAuthAdvStageImpl_genSPK_withAuthAdvRoCache S P u j c s.adv)

theorem pqxdhAuthAdvLatchedStageImpl_genOPK_withAuthAdvLatchedRoCache
    (S : Setup) (P : Primitives) (u : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (c : List (Bytes × DRKey)) (s : AuthAdvLatchedState S) :
    (pqxdhAuthAdvLatchedStageImpl .g3_5 S P (.genOPK u j o)).run
        (withAuthAdvLatchedRoCache c s) =
      Prod.map id (withAuthAdvLatchedRoCache c) <$>
        ((pqxdhAuthAdvLatchedStageImpl .g3 S P (.genOPK u j o)).run s) :=
  pqxdhAuthAdvLatchedStageImpl_withAuthAdvLatchedRoCache_of_nonCorrupt P (.genOPK u j o)
    (fun _ h => nomatch h) c s
    (pqxdhAuthAdvStageImpl_genOPK_withAuthAdvRoCache S P u j o c s.adv)

theorem pqxdhAuthAdvLatchedStageImpl_registerKey_withAuthAdvLatchedRoCache
    (S : Setup) (P : Primitives) (sk : Bytes)
    (c : List (Bytes × DRKey)) (s : AuthAdvLatchedState S) :
    (pqxdhAuthAdvLatchedStageImpl .g3_5 S P (.registerKey sk)).run
        (withAuthAdvLatchedRoCache c s) =
      Prod.map id (withAuthAdvLatchedRoCache c) <$>
        ((pqxdhAuthAdvLatchedStageImpl .g3 S P (.registerKey sk)).run s) :=
  pqxdhAuthAdvLatchedStageImpl_withAuthAdvLatchedRoCache_of_nonCorrupt P (.registerKey sk)
    (fun _ h => nomatch h) c s
    (pqxdhAuthAdvStageImpl_registerKey_withAuthAdvRoCache S P sk c s.adv)

theorem pqxdhAuthAdvLatchedStageImpl_roRootQuery_withAuthAdvLatchedRoCache
    (S : Setup) (P : Primitives) (rk dh : Bytes)
    (c : List (Bytes × DRKey)) (s : AuthAdvLatchedState S) :
    (pqxdhAuthAdvLatchedStageImpl .g3_5 S P (.roRootQuery rk dh)).run
        (withAuthAdvLatchedRoCache c s) =
      Prod.map id (withAuthAdvLatchedRoCache c) <$>
        ((pqxdhAuthAdvLatchedStageImpl .g3 S P (.roRootQuery rk dh)).run s) :=
  pqxdhAuthAdvLatchedStageImpl_withAuthAdvLatchedRoCache_of_nonCorrupt P (.roRootQuery rk dh)
    (fun _ h => nomatch h) c s
    (pqxdhAuthAdvStageImpl_roRootQuery_withAuthAdvRoCache S P rk dh c s.adv)

theorem pqxdhAuthAdvLatchedStageImpl_revealDhSecrets_withAuthAdvLatchedRoCache
    (S : Setup) (P : Primitives)
    (c : List (Bytes × DRKey)) (s : AuthAdvLatchedState S) :
    (pqxdhAuthAdvLatchedStageImpl .g3_5 S P .revealDhSecrets).run
        (withAuthAdvLatchedRoCache c s) =
      Prod.map id (withAuthAdvLatchedRoCache c) <$>
        ((pqxdhAuthAdvLatchedStageImpl .g3 S P .revealDhSecrets).run s) :=
  pqxdhAuthAdvLatchedStageImpl_withAuthAdvLatchedRoCache_of_nonCorrupt P .revealDhSecrets
    (fun _ h => nomatch h) c s
    (pqxdhAuthAdvStageImpl_revealDhSecrets_withAuthAdvRoCache S P c s.adv)

/-- Post-`.roQuery` state update on `AuthAdvLatchedState S`. -/
def updateRoQueryLatched {S : Setup} (secrets : Bytes) (c' : List (Bytes × DRKey))
    (s : AuthAdvLatchedState S) : AuthAdvLatchedState S :=
  { s with adv := { s.adv with
      hyb := withAuthHybRoCache c' s.adv.hyb
      advRoLog := secrets :: s.adv.advRoLog } }

@[simp]
theorem updateRoQueryLatched_withAuthAdvLatchedRoCache {S : Setup}
    (secrets : Bytes) (c' c : List (Bytes × DRKey)) (s : AuthAdvLatchedState S) :
    updateRoQueryLatched secrets c' (withAuthAdvLatchedRoCache c s) =
      updateRoQueryLatched secrets c' s := rfl

@[simp]
theorem withAuthAdvLatchedRoCache_updateRoQueryLatched {S : Setup}
    (secrets : Bytes) (c1 c2 : List (Bytes × DRKey)) (s : AuthAdvLatchedState S) :
    withAuthAdvLatchedRoCache c1 (updateRoQueryLatched secrets c2 s) =
      updateRoQueryLatched secrets c1 s := rfl

@[simp]
theorem isAuthG3Abort_updateRoQueryLatched {S : Setup} (P : Primitives)
    (secrets : Bytes) (c' : List (Bytes × DRKey)) (s : AuthAdvLatchedState S) :
    isAuthG3Abort P (updateRoQueryLatched secrets c' s).hyb =
      isAuthG3Abort P s.hyb := rfl

@[simp]
theorem badAuthFgAnyLatched_updateRoQueryLatched {S : Setup} (P : Primitives)
    (maxLen : ℕ) (secrets : Bytes) (c' : List (Bytes × DRKey))
    (s : AuthAdvLatchedState S) :
    badAuthFgAnyLatched P maxLen (updateRoQueryLatched secrets c' s).toFg =
      badAuthFgAnyLatched P maxLen
        { s.toFg with advRoLog := secrets :: s.adv.advRoLog } := rfl

theorem evalHkdfOrRo_true_bind_eq {α : Type} (P : Primitives)
    (roCache : List (Bytes × DRKey)) (secrets : Bytes)
    (k : DRKey × List (Bytes × DRKey) → ProbComp α) :
    (evalHkdfOrRo true P roCache secrets >>= k) =
      (match roCache.find? (fun (s, _) => s == secrets) with
      | some (_, dk) => k (dk, roCache)
      | none => (sampleDRKey96 >>= fun dk => k (dk, (secrets, dk) :: roCache))) := by
  unfold evalHkdfOrRo
  cases roCache.find? (fun (s, _) => s == secrets) with
  | some p =>
    rcases p with ⟨_, dk⟩
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure_bind]
  | none =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]

@[simp]
theorem withAuthAdvLatchedRoCache_roCache {S : Setup} (c : List (Bytes × DRKey))
    (s : AuthAdvLatchedState S) :
    (withAuthAdvLatchedRoCache c s).adv.hyb.base.roCache = c := rfl

theorem pqxdhAuthAdvLatchedStageImpl_roQuery_run_of_hasWonAuth {S : Setup}
    (stage : AuthHybridStage) (P : Primitives) (secrets : Bytes)
    (s : AuthAdvLatchedState S) (hWon : s.adv.hyb.base.hasWonAuth = true) :
    (pqxdhAuthAdvLatchedStageImpl stage S P (.roQuery secrets)).run s =
      pure (.noneResp, updateRoQueryLatched secrets s.adv.hyb.base.roCache s) := by
  unfold pqxdhAuthAdvLatchedStageImpl pqxdhAuthAdvStageImpl pqxdhAuthHybridKoskImpl
    updateRoQueryLatched
  simp [StateT.run_mk, StateT.run_bind, StateT.run_get, pure_bind, hWon]
  rfl

theorem pqxdhAuthAdvLatchedStageImpl_roQuery_run_eq {S : Setup}
    (stage : AuthHybridStage) (P : Primitives) (secrets : Bytes)
    (s : AuthAdvLatchedState S) (hWonF : s.adv.hyb.base.hasWonAuth = false) :
    (pqxdhAuthAdvLatchedStageImpl stage S P (.roQuery secrets)).run s =
      (evalHkdfOrRo true P s.adv.hyb.base.roCache secrets >>= fun p =>
        pure (.drKeyResp p.1, updateRoQueryLatched secrets p.2 s)) := by
  have hIf : (true && s.adv.hyb.base.hasWonAuth) = false := by simp [hWonF]
  unfold pqxdhAuthAdvLatchedStageImpl pqxdhAuthAdvStageImpl pqxdhAuthHybridKoskImpl
  dsimp only [StateT.run_mk]
  rw [StateT.run_bind, StateT.run_get, pure_bind, hIf]
  simp only [liftAuthBase, pqxdhAuthImpl, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    StateT.run_bind, StateT.run_get,
    StateT.run_monadLift, monadLift_self, StateT.run_set, StateT.run_pure,
    bind_assoc, pure_bind]
  rfl

theorem RelProbUpToBad.of_pure_or_bad {α : Type} {R : α → α → Prop} {bad : α → Bool}
    {x5 x6 : α} (h : R x5 x6 ∨ bad x6 = true) :
    RelProbUpToBad R bad (pure x5) (pure x6) := by
  rcases h with hR | hBad
  · exact RelProbUpToBad.of_pure hR
  · exact RelProbUpToBad.bad6 (pure x5) (pure x6) (fun y6 hy6 => by
      rw [support_pure, Set.mem_singleton_iff] at hy6
      subst hy6
      exact hBad)

theorem RelProbUpToBad.of_bind_left_pure_right {α β : Type}
    {R : α → α → Prop} {bad : α → Bool}
    (mx : ProbComp β) (f5 : β → α) (x6 : α)
    (h : (∀ b, R (f5 b) x6) ∨ bad x6 = true) :
    RelProbUpToBad R bad (mx >>= fun b => pure (f5 b)) (pure x6) := by
  rcases h with hR | hBad
  · refine ⟨fun w5 w6 _ _ hle => ?_, fun w6 w5 _ hle => ?_⟩
    · rw [probExpect_bind, probExpect_pure]
      refine probExpect_const_le_of_support mx _ (w6 x6) (fun b _ => ?_)
      rw [probExpect_pure]
      exact hle (f5 b) x6 (hR b)
    · rw [probExpect_bind, probExpect_pure]
      refine FgGapDh.le_probExpect_const_of_support mx _ (w6 x6) (fun b _ => ?_)
      rw [probExpect_pure]
      exact hle (f5 b) x6 (hR b)
  · exact RelProbUpToBad.bad6 _ (pure x6) (fun y6 hy6 => by
      rw [support_pure, Set.mem_singleton_iff] at hy6
      subst hy6
      exact hBad)

/-- Step coupling for `.roQuery secrets` on `AuthAdvLatchedState S`. -/
theorem relProbUpToBad_roQuery_of_cache_agree_or_bad
    {S : Setup} (P : Primitives) (secrets : Bytes)
    (Inv : AuthAdvLatchedState S → AuthAdvLatchedState S → Prop)
    (badFg : AuthFgCutoffState S → Bool)
    (s35 s3 : AuthAdvLatchedState S)
    (hAg : AuthAdvLatchedAgreeOffRo s35 s3)
    (hBadIndep : ∀ c', badFg (updateRoQueryLatched secrets c' s3).toFg =
      badFg { s3.toFg with advRoLog := secrets :: s3.adv.advRoLog })
    (hSub35 : ∀ p,
      s35.adv.hyb.base.roCache.find? (fun (s, _) => s == secrets) = some p →
      s3.adv.hyb.base.roCache.find? (fun (s, _) => s == secrets) = some p)
    (hHitPres :
      badFg { s3.toFg with advRoLog := secrets :: s3.adv.advRoLog } = false →
      Inv (updateRoQueryLatched secrets s35.adv.hyb.base.roCache s3)
          (updateRoQueryLatched secrets s3.adv.hyb.base.roCache s3))
    (hMissPres : ∀ dk,
      s35.adv.hyb.base.roCache.find? (fun (s, _) => s == secrets) = none →
      s3.adv.hyb.base.roCache.find? (fun (s, _) => s == secrets) = none →
      badFg { s3.toFg with advRoLog := secrets :: s3.adv.advRoLog } = false →
      Inv (updateRoQueryLatched secrets ((secrets, dk) :: s35.adv.hyb.base.roCache) s3)
          (updateRoQueryLatched secrets ((secrets, dk) :: s3.adv.hyb.base.roCache) s3))
    (hDiffBad : ∀ p,
      s35.adv.hyb.base.roCache.find? (fun (s, _) => s == secrets) = none →
      s3.adv.hyb.base.roCache.find? (fun (s, _) => s == secrets) = some p →
      badFg { s3.toFg with advRoLog := secrets :: s3.adv.advRoLog } = true ∨
      isAuthG3Abort P s3.hyb = true) :
    RelProbUpToBad
      (fun y35 y3 =>
        (y35.1 = y3.1 ∧ Inv y35.2 y3.2) ∨
        (isAuthG3Abort P y35.2.hyb = true ∧ isAuthG3Abort P y3.2.hyb = true))
      (fun y3 => badFg y3.2.toFg)
      ((pqxdhAuthAdvLatchedStageImpl .g3_5 S P (.roQuery secrets)).run s35)
      ((pqxdhAuthAdvLatchedStageImpl .g3 S P (.roQuery secrets)).run s3) := by
  have hWonEq : s35.adv.hyb.base.hasWonAuth = s3.adv.hyb.base.hasWonAuth := by
    rw [hAg]; rfl
  by_cases hWon : s3.adv.hyb.base.hasWonAuth = true
  · rw [pqxdhAuthAdvLatchedStageImpl_roQuery_run_of_hasWonAuth _ _ _ _ (hWonEq.trans hWon),
        pqxdhAuthAdvLatchedStageImpl_roQuery_run_of_hasWonAuth _ _ _ _ hWon]
    conv_lhs => rw [hAg]
    simp only [withAuthAdvLatchedRoCache_roCache, updateRoQueryLatched_withAuthAdvLatchedRoCache]
    refine RelProbUpToBad.of_pure_or_bad ?_
    by_cases hb : badFg { s3.toFg with advRoLog := secrets :: s3.adv.advRoLog } = true
    · right; dsimp only; rw [hBadIndep]; exact hb
    · left; exact Or.inl ⟨rfl, hHitPres (Bool.eq_false_iff.mpr hb)⟩
  · have hWonF : s3.adv.hyb.base.hasWonAuth = false := Bool.eq_false_iff.mpr hWon
    rw [pqxdhAuthAdvLatchedStageImpl_roQuery_run_eq _ _ _ _ (hWonEq.trans hWonF),
        pqxdhAuthAdvLatchedStageImpl_roQuery_run_eq _ _ _ _ hWonF]
    conv_lhs => rw [hAg]
    simp only [withAuthAdvLatchedRoCache_roCache,
      updateRoQueryLatched_withAuthAdvLatchedRoCache]
    rw [evalHkdfOrRo_true_bind_eq, evalHkdfOrRo_true_bind_eq]
    cases hF35 : s35.adv.hyb.base.roCache.find? (fun (s, _) => s == secrets) with
    | some p =>
      have hF3 := hSub35 p hF35
      rw [hF3]
      rcases p with ⟨sKey, dk⟩
      dsimp only
      refine RelProbUpToBad.of_pure_or_bad ?_
      by_cases hb : badFg { s3.toFg with advRoLog := secrets :: s3.adv.advRoLog } = true
      · right; dsimp only; rw [hBadIndep]; exact hb
      · left; exact Or.inl ⟨rfl, hHitPres (Bool.eq_false_iff.mpr hb)⟩
    | none =>
      cases hF3 : s3.adv.hyb.base.roCache.find? (fun (s, _) => s == secrets) with
      | none =>
        dsimp only
        refine RelProbUpToBad.bind_same sampleDRKey96 (fun dk => ?_)
        refine RelProbUpToBad.of_pure_or_bad ?_
        by_cases hb : badFg { s3.toFg with advRoLog := secrets :: s3.adv.advRoLog } = true
        · right; dsimp only; rw [hBadIndep]; exact hb
        · left; exact Or.inl ⟨rfl, hMissPres dk hF35 hF3 (Bool.eq_false_iff.mpr hb)⟩
      | some p =>
        rcases p with ⟨sKey, dk⟩
        dsimp only
        refine @RelProbUpToBad.of_bind_left_pure_right (AuthResponse × AuthAdvLatchedState S) DRKey
          (fun y35 y3 =>
            (y35.1 = y3.1 ∧ Inv y35.2 y3.2) ∨
            (isAuthG3Abort P y35.2.hyb = true ∧ isAuthG3Abort P y3.2.hyb = true))
          (fun y3 => badFg y3.2.toFg) sampleDRKey96
          (fun dk' => (.drKeyResp dk',
            updateRoQueryLatched secrets ((secrets, dk') :: s35.adv.hyb.base.roCache) s3))
          (.drKeyResp dk, updateRoQueryLatched secrets s3.adv.hyb.base.roCache s3) ?_
        rcases hDiffBad (sKey, dk) hF35 hF3 with hb | hAb3
        · right; dsimp only; rw [hBadIndep]; exact hb
        · left
          intro dk'
          refine Or.inr ⟨?_, ?_⟩
          · rw [isAuthG3Abort_updateRoQueryLatched]; exact hAb3
          · rw [isAuthG3Abort_updateRoQueryLatched]; exact hAb3

/-- Predicate selecting the 7 queries that do not read or write `roCache`. -/
def isAuthNonRoQuery {S : Setup} : AuthQuery S → Bool
  | .roQuery _           => false
  | .sendOPK _ _ _ _ _   => false
  | .sendNoOPK _ _ _ _ _ => false
  | .recvOPK _ _ _ _     => false
  | .recvNoOPK _ _ _ _   => false
  | _                    => true

/-! ## Receiver schedule factorization -/

theorem RelProbUpToBad.bind_same_support {β α : Type} {R : α → α → Prop} {bad : α → Bool}
    (mx : ProbComp β) {f5 f6 : β → ProbComp α}
    (h : ∀ b ∈ support mx, RelProbUpToBad R bad (f5 b) (f6 b)) :
    RelProbUpToBad R bad (mx >>= f5) (mx >>= f6) := by
  refine ⟨fun w5 w6 hw5 hw6 hle => ?_, fun w6 w5 hw6 hle => ?_⟩
  · rw [probExpect_bind, probExpect_bind]
    exact probExpect_mono_of_support mx _ _ (fun b hb => (h b hb).1 w5 w6 hw5 hw6 hle)
  · rw [probExpect_bind, probExpect_bind]
    exact probExpect_mono_of_support mx _ _ (fun b hb => (h b hb).2 w6 w5 hw6 hle)

/-- Stage-dependent `drKey` and `roCache'` step of `evalAuthHybridRecvSchedule`. -/
def evalAuthHybridRecvDrKey {S : Setup} (stage : AuthHybridStage) (useRo : Bool) (P : Primitives)
    (roCache : List (Bytes × DRKey)) (matchedSess? : Option (IdealAuthSession S))
    (isUncorruptedHonestSender : Bool) (secrets : Bytes) :
    ProbComp (DRKey × List (Bytes × DRKey)) :=
  let useIdealBranch : Bool := matchedSess?.isSome || isUncorruptedHonestSender
  if useIdealBranch && stage.idealDrKey then
    match matchedSess? with
    | some s => pure (s.drKey, roCache)
    | none   => do
      let dk ← sampleDRKey96
      pure (dk, roCache)
  else
    evalHkdfOrRo useRo P roCache secrets

/-- Stage-independent core of `evalAuthHybridRecvSchedule` at `.g3` and `.g3_5`. -/
def evalAuthHybridRecvCore (useRo : Bool) (P : Primitives)
    (rootRoCache : List ((Bytes × Bytes) × (Bytes × Bytes)))
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry) (msg : PreKeyMsg)
    (drKey : DRKey) :
    ProbComp (Option (Bytes × Bytes × Bytes × List ((Bytes × Bytes) × (Bytes × Bytes)))) := do
  let dhRatchet := P.x25519 bEntry.spkSk msg.ephAPk
  let ((rk1, ck1_0), rootRoCache') ←
    evalRootKdfOrRo useRo P rootRoCache drKey.rootKey dhRatchet
  let (mkSeed, ck1_1) := (P.chainKdfSeed ck1_0, P.chainKdfNext ck1_0)
  match P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
  | none => return none
  | some (_pqrStB, spqrSalt?) =>
    let deriveMessageKeys := P.deriveMsgKeys mkSeed spqrSalt?
    let ad := firstMsgAD msg.hdr.ikAPk kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg
    match P.aeadDec deriveMessageKeys ad msg.aeadCt with
    | none    => return none
    | some pt => return some (rk1, ck1_1, pt, rootRoCache')

/-- Post-`drKey` continuation of `evalAuthHybridRecvSchedule` at `.g3` and `.g3_5`. -/
def evalAuthHybridRecvPost (useRo : Bool) (P : Primitives)
    (rootRoCache : List ((Bytes × Bytes) × (Bytes × Bytes)))
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry) (msg : PreKeyMsg)
    (drKey : DRKey) (roCache' : List (Bytes × DRKey)) :
    ProbComp (Option (DRKey × Bytes × Bytes × Bytes ×
      List (Bytes × DRKey) × List ((Bytes × Bytes) × (Bytes × Bytes)))) := do
  let core? ← evalAuthHybridRecvCore useRo P rootRoCache kEntry bEntry msg drKey
  match core? with
  | none => return none
  | some (rk1, ck1_1, pt, rootRoCache') =>
    return some (drKey, rk1, ck1_1, pt, roCache', rootRoCache')

theorem evalAuthHybridRecvSchedule_g3_eq {S : Setup} (useRo : Bool) (P : Primitives)
    (hst : AuthHybridState S) (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry)
    (opkPk? : Option Bytes) (secrets : Bytes) (msg : PreKeyMsg) :
    evalAuthHybridRecvSchedule .g3 useRo P hst kEntry bEntry opkPk? secrets msg = (do
      let st := hst.base
      let senderPrincipal? := findHonestPrincipal P st.principals msg.hdr.ikAPk
      let isUncorruptedHonestSender : Bool :=
        match senderPrincipal? with
        | some (_, sEntry) => !sEntry.corrupted
        | none             => false
      let matchedSess? : Option (IdealAuthSession S) :=
        hst.idealSessions.find?
          (matchIdealAuthHandshake P kEntry.ikAPk bEntry.spkPk opkPk? bEntry.pqspkPk msg.hdr)
      let (drKey, roCache') ←
        evalAuthHybridRecvDrKey .g3 useRo P st.roCache matchedSess?
          isUncorruptedHonestSender secrets
      evalAuthHybridRecvPost useRo P st.rootRoCache kEntry bEntry msg drKey roCache') := by
  unfold evalAuthHybridRecvSchedule evalAuthHybridRecvDrKey evalAuthHybridRecvPost
    evalAuthHybridRecvCore AuthHybridStage.idealDrKey AuthHybridStage.idealRk
    AuthHybridStage.idealCk AuthHybridStage.idealMsgKeys AuthHybridStage.idealFreshAead
    AuthHybridStage.idealUnmatchedRecvAead
  dsimp only
  simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte, ite_self, bind_assoc, pure_bind]
  congr 1
  funext ⟨drKey, roCache'⟩
  congr 1
  funext ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
  dsimp only
  cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
  | none => simp only [pure_bind]
  | some p =>
    rcases p with ⟨_pqrStB, spqrSalt?⟩
    dsimp only
    cases P.aeadDec (P.deriveMsgKeys (P.chainKdfSeed ck1_0) spqrSalt?)
        (firstMsgAD msg.hdr.ikAPk kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg) msg.aeadCt <;>
      simp only [pure_bind]

theorem evalAuthHybridRecvSchedule_g3_5_eq {S : Setup} (useRo : Bool) (P : Primitives)
    (hst : AuthHybridState S) (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry)
    (opkPk? : Option Bytes) (secrets : Bytes) (msg : PreKeyMsg) :
    evalAuthHybridRecvSchedule .g3_5 useRo P hst kEntry bEntry opkPk? secrets msg = (do
      let st := hst.base
      let senderPrincipal? := findHonestPrincipal P st.principals msg.hdr.ikAPk
      let isUncorruptedHonestSender : Bool :=
        match senderPrincipal? with
        | some (_, sEntry) => !sEntry.corrupted
        | none             => false
      let matchedSess? : Option (IdealAuthSession S) :=
        hst.idealSessions.find?
          (matchIdealAuthHandshake P kEntry.ikAPk bEntry.spkPk opkPk? bEntry.pqspkPk msg.hdr)
      let (drKey, roCache') ←
        evalAuthHybridRecvDrKey .g3_5 useRo P st.roCache matchedSess?
          isUncorruptedHonestSender secrets
      evalAuthHybridRecvPost useRo P st.rootRoCache kEntry bEntry msg drKey roCache') := by
  unfold evalAuthHybridRecvSchedule evalAuthHybridRecvDrKey evalAuthHybridRecvPost
    evalAuthHybridRecvCore AuthHybridStage.idealDrKey AuthHybridStage.idealRk
    AuthHybridStage.idealCk AuthHybridStage.idealMsgKeys AuthHybridStage.idealFreshAead
    AuthHybridStage.idealUnmatchedRecvAead
  dsimp (config := { zetaHave := true }) only
  cases hst.idealSessions.find?
      (matchIdealAuthHandshake P kEntry.ikAPk bEntry.spkPk opkPk? bEntry.pqspkPk msg.hdr) with
  | some s =>
    simp only [Option.isSome_some, Bool.true_or, Bool.and_true, Bool.and_false,
      Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
    congr 1
    funext ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
    dsimp only
    cases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
    | none => simp only [pure_bind]
    | some p =>
      rcases p with ⟨_pqrStB, spqrSalt?⟩
      dsimp only
      cases P.aeadDec (P.deriveMsgKeys (P.chainKdfSeed ck1_0) spqrSalt?)
          (firstMsgAD msg.hdr.ikAPk kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg) msg.aeadCt <;>
        simp only [pure_bind]
  | none =>
    cases findHonestPrincipal P hst.base.principals msg.hdr.ikAPk with
    | none =>
      simp only [Option.isSome_none, Bool.false_or, Bool.and_true, Bool.and_false,
        Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
      congr 1
      funext ⟨drKey, roCache'⟩
      congr 1
      funext ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
      dsimp only
      cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
      | none => simp only [pure_bind]
      | some p =>
        rcases p with ⟨_pqrStB, spqrSalt?⟩
        dsimp only
        cases P.aeadDec (P.deriveMsgKeys (P.chainKdfSeed ck1_0) spqrSalt?)
            (firstMsgAD msg.hdr.ikAPk kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg) msg.aeadCt <;>
          simp only [pure_bind]
    | some kp =>
      rcases kp with ⟨_, sEntry⟩
      cases hCorr : sEntry.corrupted with
      | true =>
        simp only [hCorr, Option.isSome_none, Bool.false_or, Bool.not_true, Bool.and_true,
          Bool.and_false, Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
        congr 1
        funext ⟨drKey, roCache'⟩
        congr 1
        funext ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
        dsimp only
        cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
        | none => simp only [pure_bind]
        | some p =>
          rcases p with ⟨_pqrStB, spqrSalt?⟩
          dsimp only
          cases P.aeadDec (P.deriveMsgKeys (P.chainKdfSeed ck1_0) spqrSalt?)
              (firstMsgAD msg.hdr.ikAPk kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg) msg.aeadCt <;>
            simp only [pure_bind]
      | false =>
        simp only [hCorr, Option.isSome_none, Bool.false_or, Bool.not_false, Bool.and_true,
          Bool.and_false, Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
        congr 1
        funext dk
        congr 1
        funext ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
        dsimp only
        cases P.spqrInitRecv dk.pqrKey msg.pqRatchetMsg with
        | none => simp only [pure_bind]
        | some p =>
          rcases p with ⟨_pqrStB, spqrSalt?⟩
          dsimp only
          cases P.aeadDec (P.deriveMsgKeys (P.chainKdfSeed ck1_0) spqrSalt?)
              (firstMsgAD msg.hdr.ikAPk kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg) msg.aeadCt <;>
            simp only [pure_bind]

theorem relProbUpToBad_evalAuthHybridRecvPost_bind {α : Type}
    (R : α → α → Prop) (bad : α → Bool)
    (useRo : Bool) (P : Primitives)
    (rootRoCache : List ((Bytes × Bytes) × (Bytes × Bytes)))
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry) (msg : PreKeyMsg)
    (drKey : DRKey) (roCache35' roCache3' : List (Bytes × DRKey))
    (k35 k3 : Option (DRKey × Bytes × Bytes × Bytes ×
      List (Bytes × DRKey) × List ((Bytes × Bytes) × (Bytes × Bytes))) → ProbComp α)
    (hNone : RelProbUpToBad R bad (k35 none) (k3 none))
    (hSome : ∀ rk1 ck1_1 pt rootRoCache',
      some (rk1, ck1_1, pt, rootRoCache') ∈
        support (evalAuthHybridRecvCore useRo P rootRoCache kEntry bEntry msg drKey) →
      RelProbUpToBad R bad
        (k35 (some (drKey, rk1, ck1_1, pt, roCache35', rootRoCache')))
        (k3 (some (drKey, rk1, ck1_1, pt, roCache3', rootRoCache')))) :
    RelProbUpToBad R bad
      (evalAuthHybridRecvPost useRo P rootRoCache kEntry bEntry msg drKey roCache35' >>= k35)
      (evalAuthHybridRecvPost useRo P rootRoCache kEntry bEntry msg drKey roCache3' >>= k3) := by
  unfold evalAuthHybridRecvPost
  rw [bind_assoc, bind_assoc]
  refine RelProbUpToBad.bind_same_support
    (evalAuthHybridRecvCore useRo P rootRoCache kEntry bEntry msg drKey) (fun core? hCore => ?_)
  cases core? with
  | none =>
    simp only [pure_bind]
    exact hNone
  | some tup =>
    rcases tup with ⟨rk1, ck1_1, pt, rootRoCache'⟩
    simp only [pure_bind]
    exact hSome rk1 ck1_1 pt rootRoCache' hCore

/-! ## Guarded monotone bad events -/

/-- Guard ensuring `initAuthDh1Cand` never evaluates `P.x25519` on the empty fallback key. -/
def initAuthDh1CandGuard (S : Setup) (P : Primitives)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (advKeyPows : List (Bytes × Bytes))
    (s : AuthInitiatorEntry S) : Bool :=
  !(lookupAuthSpkSkTake S P spkBundles advKeyPows s.peerSpkPk).isEmpty &&
  (principals.find? (fun (idx, _) => idx == sessionSenderIdx s.sid)).isSome

/-- Guard ensuring `respAuthCand` never evaluates `P.x25519` on the empty fallback scalar. -/
def respAuthCandGuard (S : Setup)
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (bKey : Nat × Nat) : Bool :=
  let spkSk : Bytes := match (spkBundles.take S.N_dh).find? (fun (idx, _) => idx == bKey) with
    | some (_, b) => b.spkSk
    | none => []
  !spkSk.isEmpty

/-- Monotone Case A (`DH1`) bad event at `(uIdx, bIdx)`. -/
def badAuthFgDh1AtMono {S : Setup} (P : Primitives) (maxLen uIdx bIdx : ℕ)
    (st : AuthState S) (advRoLog : List Bytes) (respRecs : List AuthRespRecord) : Bool :=
  match st.principals.find? (fun (u, _) => u == uIdx),
        st.spkBundles.find? (fun (k, _) => spkBundleFlatIdxVal S k == bIdx) with
  | some (_, uEntry), some (_, bEntry) =>
    let zTarget := P.x25519 uEntry.secIKA0 bEntry.spkPk
    let spkErased := eraseSpkBundlesFg S bIdx st.spkBundles
    let advKeyPows := st.advKeys.map (fun (sk, pk) => (sk, P.pow8 pk))
    !uEntry.corrupted &&
    ((advRoLog.take maxLen).any (fun sec => extractDh1 sec == zTarget) ||
     (st.sessions.take S.N_dh).any (fun s =>
       initAuthDh1CandGuard S P st.principals spkErased advKeyPows s &&
       (initAuthDh1Cand S P st.principals spkErased advKeyPows s == zTarget)) ||
     (respRecs.take S.N_sess_tot).any (fun r =>
       respAuthCandGuard S spkErased r.bKey &&
       (respAuthDh1Cand S P spkErased r == zTarget)))
  | _, _ => false

/-- Monotone Case C (`DH3`) bad event at `(sIdx, bIdx)`. -/
def badAuthFgDh3AtMono {S : Setup} (P : Primitives) (maxLen sIdx bIdx : ℕ)
    (st : AuthState S) (advRoLog : List Bytes) (respRecs : List AuthRespRecord) : Bool :=
  match st.sessions.find? (fun s => initSessionSlotIdx s.sid == sIdx),
        st.spkBundles.find? (fun (k, _) => spkBundleFlatIdxVal S k == bIdx) with
  | some s, some (_, bEntry) =>
    let zTarget := P.x25519 s.ekASk bEntry.spkPk
    let spkErased := eraseSpkBundlesFg S bIdx st.spkBundles
    (P.pow8 s.peerSpkPk == P.pow8 bEntry.spkPk) &&
    ((advRoLog.take maxLen).any (fun sec => extractDh3 sec == zTarget) ||
     (st.sessions.take S.N_dh).any (fun s' =>
       initSessionSlotIdx s'.sid != sIdx && P.x25519 s'.ekASk s'.peerSpkPk == zTarget) ||
     (respRecs.take S.N_sess_tot).any (fun r =>
       respAuthCandGuard S spkErased r.bKey &&
       (respAuthDh3Cand S P spkErased r == zTarget)))
  | _, _ => false

def badAuthFgDh1LatchedAtMono {S : Setup} (P : Primitives) (maxLen uIdx bIdx : ℕ)
    (hst : AuthFgCutoffState S) : Bool :=
  hst.latchedDh1.contains (uIdx, bIdx) ||
  badAuthFgDh1AtMono P maxLen uIdx bIdx hst.base hst.advRoLog hst.respRecs

/-- Combined sticky-latch monotone bad event (`DH1` and `DH3`). -/
def badAuthFgAnyLatchedMono {S : Setup} (P : Primitives) (maxLen : ℕ)
    (hst : AuthFgCutoffState S) : Bool :=
  (List.range S.N_id).any (fun uIdx =>
    (List.range S.N_spk_tot).any (fun bIdx =>
      badAuthFgDh1LatchedAtMono P maxLen uIdx bIdx hst)) ||
  (List.range S.N_send_tot).any (fun sIdx =>
    (List.range S.N_spk_tot).any (fun bIdx =>
      badAuthFgDh3AtMono P maxLen sIdx bIdx hst.base hst.advRoLog hst.respRecs))

@[simp]
theorem badAuthFgAnyLatchedMono_updateRoQueryLatched {S : Setup} (P : Primitives)
    (maxLen : ℕ) (secrets : Bytes) (c' : List (Bytes × DRKey))
    (s : AuthAdvLatchedState S) :
    badAuthFgAnyLatchedMono P maxLen (updateRoQueryLatched secrets c' s).toFg =
      badAuthFgAnyLatchedMono P maxLen
        { s.toFg with advRoLog := secrets :: s.adv.advRoLog } := rfl

theorem badAuthFgDh1AtMono_imp_badAuthFgDh1At {S : Setup} (P : Primitives)
    (maxLen uIdx bIdx : ℕ) (st : AuthState S)
    (advRoLog : List Bytes) (respRecs : List AuthRespRecord)
    (h : badAuthFgDh1AtMono P maxLen uIdx bIdx st advRoLog respRecs = true) :
    badAuthFgDh1At P maxLen uIdx bIdx st advRoLog respRecs = true := by
  unfold badAuthFgDh1AtMono at h
  unfold badAuthFgDh1At
  cases hU : st.principals.find? (fun (u, _) => u == uIdx) with
  | none => rw [hU] at h; simp at h
  | some up =>
    rcases up with ⟨_, uEntry⟩
    cases hB : st.spkBundles.find? (fun (k, _) => spkBundleFlatIdxVal S k == bIdx) with
    | none => rw [hU, hB] at h; simp at h
    | some bp =>
      rcases bp with ⟨_, bEntry⟩
      rw [hU, hB] at h
      dsimp only at h ⊢
      simp only [Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true] at h ⊢
      rcases h with ⟨hNotCorr, (hRo | ⟨s, hsMem, _, hsEq⟩) | ⟨r, hrMem, _, hrEq⟩⟩
      · exact ⟨hNotCorr, Or.inl (Or.inl hRo)⟩
      · exact ⟨hNotCorr, Or.inl (Or.inr ⟨s, hsMem, hsEq⟩)⟩
      · exact ⟨hNotCorr, Or.inr ⟨r, hrMem, hrEq⟩⟩

theorem badAuthFgDh3AtMono_imp_badAuthFgDh3At {S : Setup} (P : Primitives)
    (maxLen sIdx bIdx : ℕ) (st : AuthState S)
    (advRoLog : List Bytes) (respRecs : List AuthRespRecord)
    (h : badAuthFgDh3AtMono P maxLen sIdx bIdx st advRoLog respRecs = true) :
    badAuthFgDh3At P maxLen sIdx bIdx st advRoLog respRecs = true := by
  unfold badAuthFgDh3AtMono at h
  unfold badAuthFgDh3At
  cases hS : st.sessions.find? (fun s => initSessionSlotIdx s.sid == sIdx) with
  | none => rw [hS] at h; simp at h
  | some s =>
    cases hB : st.spkBundles.find? (fun (k, _) => spkBundleFlatIdxVal S k == bIdx) with
    | none => rw [hS, hB] at h; simp at h
    | some bp =>
      rcases bp with ⟨_, bEntry⟩
      rw [hS, hB] at h
      dsimp only at h ⊢
      simp only [Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true] at h ⊢
      rcases h with ⟨hPow, (hRo | hSess) | ⟨r, hrMem, _, hrEq⟩⟩
      · exact ⟨hPow, Or.inl (Or.inl hRo)⟩
      · exact ⟨hPow, Or.inl (Or.inr hSess)⟩
      · exact ⟨hPow, Or.inr ⟨r, hrMem, hrEq⟩⟩

theorem badAuthFgDh1LatchedAtMono_imp_badAuthFgDh1LatchedAt {S : Setup} (P : Primitives)
    (maxLen uIdx bIdx : ℕ) (hst : AuthFgCutoffState S)
    (h : badAuthFgDh1LatchedAtMono P maxLen uIdx bIdx hst = true) :
    badAuthFgDh1LatchedAt P maxLen uIdx bIdx hst = true := by
  unfold badAuthFgDh1LatchedAtMono at h
  unfold badAuthFgDh1LatchedAt
  rcases Bool.or_eq_true_iff.mp h with hL | hD
  · exact Bool.or_eq_true_iff.mpr (Or.inl hL)
  · exact Bool.or_eq_true_iff.mpr (Or.inr
      (badAuthFgDh1AtMono_imp_badAuthFgDh1At P maxLen uIdx bIdx
        hst.base hst.advRoLog hst.respRecs hD))

theorem badAuthFgAnyLatchedMono_imp_badAuthFgAnyLatched {S : Setup} (P : Primitives)
    (maxLen : ℕ) (hst : AuthFgCutoffState S)
    (h : badAuthFgAnyLatchedMono P maxLen hst = true) :
    badAuthFgAnyLatched P maxLen hst = true := by
  unfold badAuthFgAnyLatchedMono at h
  unfold badAuthFgAnyLatched
  simp only [Bool.or_eq_true, List.any_eq_true] at h ⊢
  rcases h with ⟨uIdx, hu, bIdx, hb, hDh1⟩ | ⟨sIdx, hs, bIdx, hb, hDh3⟩
  · exact Or.inl ⟨uIdx, hu, bIdx, hb,
      badAuthFgDh1LatchedAtMono_imp_badAuthFgDh1LatchedAt P maxLen uIdx bIdx hst hDh1⟩
  · exact Or.inr ⟨sIdx, hs, bIdx, hb,
      badAuthFgDh3AtMono_imp_badAuthFgDh3At P maxLen sIdx bIdx
        hst.base hst.advRoLog hst.respRecs hDh3⟩

theorem badAuthFgAnyLatchedMono_of_exists_badAuthFgDh1AtMono {S : Setup} (P : Primitives)
    (maxLen : ℕ) (s : AuthFgCutoffState S)
    (h : ∃ u : Fin S.N_id, ∃ bIdx ∈ List.range S.N_spk_tot,
      badAuthFgDh1AtMono P maxLen u.val bIdx s.base s.advRoLog s.respRecs = true) :
    badAuthFgAnyLatchedMono P maxLen s = true := by
  rcases h with ⟨u, bIdx, hbIdx, hBad⟩
  unfold badAuthFgAnyLatchedMono
  apply Bool.or_eq_true_iff.mpr
  left
  rw [List.any_eq_true]
  refine ⟨u.val, List.mem_range.mpr u.isLt, ?_⟩
  rw [List.any_eq_true]
  refine ⟨bIdx, hbIdx, ?_⟩
  unfold badAuthFgDh1LatchedAtMono
  simp [hBad]

theorem badAuthFgAnyLatchedMono_of_exists_badAuthFgDh3AtMono {S : Setup} (P : Primitives)
    (maxLen : ℕ) (s : AuthFgCutoffState S)
    (h : ∃ sIdx ∈ List.range S.N_send_tot, ∃ bIdx ∈ List.range S.N_spk_tot,
      badAuthFgDh3AtMono P maxLen sIdx bIdx s.base s.advRoLog s.respRecs = true) :
    badAuthFgAnyLatchedMono P maxLen s = true := by
  rcases h with ⟨sIdx, hsIdx, bIdx, hbIdx, hBad⟩
  unfold badAuthFgAnyLatchedMono
  apply Bool.or_eq_true_iff.mpr
  right
  rw [List.any_eq_true]
  refine ⟨sIdx, hsIdx, ?_⟩
  rw [List.any_eq_true]
  exact ⟨bIdx, hbIdx, hBad⟩

theorem subcase4B_advKey_imp_badAuthFgDh1AtMono {S : Setup} (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (maxLen uIdx bIdx : ℕ)
    (hst : AuthHybridState S) (advRoLog : List Bytes) (respRecs : List AuthRespRecord)
    (hNoEc : hasEcPkCollisionAuth P hst = false)
    {uEntry : PrincipalEntry} {k j : Nat} {bEntry : SpkBundleEntry}
    {s : AuthInitiatorEntry S}
    (hFindU : hst.base.principals.find? (fun (u, _) => u == uIdx) = some (uIdx, uEntry))
    (hFindB : hst.base.spkBundles.find?
      (fun (k', _) => spkBundleFlatIdxVal S k' == bIdx) = some ((k, j), bEntry))
    (huNotCorr : (!uEntry.corrupted) = true)
    (huIk : uEntry.secIKA0.length = 32 ∧ uEntry.ikAPk = P.x25519Base uEntry.secIKA0)
    (hAdvSkLen : ∀ kv ∈ hst.base.advKeys, kv.1.length = 32 ∧ kv.2 = P.x25519Base kv.1)
    (hsMemTake : s ∈ hst.base.sessions.take S.N_dh)
    (hsSender : sessionSenderIdx s.sid = uIdx)
    (hAdvReg : isAdvRegistered P hst.base.advKeys s.peerSpkPk = true)
    (hPowEq : P.pow8 bEntry.spkPk = P.pow8 s.peerSpkPk) :
    badAuthFgDh1AtMono P maxLen uIdx bIdx hst.base advRoLog respRecs = true := by
  have hCandEq := (subcase4B_advKey_imp_badAuthFgDh1AtNonEmpty P hP maxLen uIdx bIdx
    hst advRoLog respRecs hNoEc hFindU hFindB huNotCorr huIk hAdvSkLen
    hsMemTake hsSender hAdvReg hPowEq).1
  have hbMem : ((k, j), bEntry) ∈ hst.base.spkBundles := List.mem_of_find?_eq_some hFindB
  have hbIdx : spkBundleFlatIdxVal S (k, j) = bIdx :=
    beq_iff_eq.mp (List.find?_some
      (p := fun (x : (Nat × Nat) × SpkBundleEntry) => spkBundleFlatIdxVal S x.1 == bIdx) hFindB)
  have hFindNone := find_nonEmpty_eraseSpkBundlesFg_eq_none_of_noEc P hst hNoEc hbMem hbIdx hPowEq
  have hAdvPowsReg :
      isAdvRegisteredPows (hst.base.advKeys.map (fun (sk, pk) => (sk, P.pow8 pk)))
        (P.pow8 s.peerSpkPk) = true := by
    rw [isAdvRegisteredPows_map_eq]; exact hAdvReg
  unfold isAdvRegisteredPows at hAdvPowsReg
  have hGuard :
      initAuthDh1CandGuard S P hst.base.principals
        (eraseSpkBundlesFg S bIdx hst.base.spkBundles)
        (hst.base.advKeys.map (fun (sk, pk) => (sk, P.pow8 pk))) s = true := by
    unfold initAuthDh1CandGuard lookupAuthSpkSkTake
    dsimp only
    rw [hFindNone, hsSender, hFindU]
    dsimp only
    cases hFA : (hst.base.advKeys.map (fun (sk, pk) => (sk, P.pow8 pk))).find?
        (fun (_, wPk) => wPk == P.pow8 s.peerSpkPk) with
    | none =>
      rcases List.any_eq_true.mp hAdvPowsReg with ⟨x, hxMem, hxPred⟩
      exact False.elim (List.find?_eq_none.mp hFA x hxMem hxPred)
    | some sp =>
      rcases sp with ⟨sk, wPk⟩
      dsimp only
      have hspMem := List.mem_of_find?_eq_some hFA
      rw [List.mem_map] at hspMem
      rcases hspMem with ⟨⟨sk0, pk0⟩, hkvMem, hPairEq⟩
      injection hPairEq with hskEq _
      subst hskEq
      have hLen := (hAdvSkLen (sk0, pk0) hkvMem).1
      cases sk0 <;> simp_all
  unfold badAuthFgDh1AtMono
  rw [hFindU, hFindB]
  dsimp only
  rw [huNotCorr, Bool.true_and, Bool.or_eq_true, Bool.or_eq_true]
  left; right
  exact List.any_eq_true.mpr ⟨s, hsMemTake,
    Bool.and_eq_true_iff.mpr ⟨hGuard, beq_iff_eq.mpr hCandEq⟩⟩

theorem subcase4B_kosk_imp_ecColl_or_badDh1Mono {S : Setup} (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (maxLen uIdx bIdx : ℕ)
    (st0 : AuthState S) (hst : AuthHybridState S)
    (advRoLog : List Bytes) (respRecs : List AuthRespRecord)
    {uEntry : PrincipalEntry} {k j : Nat} {bEntry : SpkBundleEntry}
    {s : AuthInitiatorEntry S}
    (hNotIn0 : ∀ b0, ((k, j), b0) ∉ st0.spkBundles)
    (hSubSpk : ∀ x ∈ st0.spkBundles,
      (x.1, P.pow8 x.2.spkPk) ∈ hst.base.spkBundles.map (fun (idx, b) => (idx, P.pow8 b.spkPk)))
    (hSubAdv : ∀ x ∈ st0.advKeys, x ∈ hst.base.advKeys)
    (hFindU : hst.base.principals.find? (fun (u, _) => u == uIdx) = some (uIdx, uEntry))
    (hFindB : hst.base.spkBundles.find?
      (fun (k', _) => spkBundleFlatIdxVal S k' == bIdx) = some ((k, j), bEntry))
    (huNotCorr : (!uEntry.corrupted) = true)
    (huIk : uEntry.secIKA0.length = 32 ∧ uEntry.ikAPk = P.x25519Base uEntry.secIKA0)
    (hAdvSkLen : ∀ kv ∈ hst.base.advKeys, kv.1.length = 32 ∧ kv.2 = P.x25519Base kv.1)
    (hsMemTake : s ∈ hst.base.sessions.take S.N_dh)
    (hsSender : sessionSenderIdx s.sid = uIdx)
    (hKoskSpk0 :
      (isGameSpk P st0.spkBundles s.peerSpkPk ||
        isAdvRegistered P st0.advKeys s.peerSpkPk) = true)
    (hPowEq : P.pow8 bEntry.spkPk = P.pow8 s.peerSpkPk) :
    (hasEcPkCollisionAuth P hst = true ∧ isAuthG3Abort P hst = true) ∨
    badAuthFgDh1AtMono P maxLen uIdx bIdx hst.base advRoLog respRecs = true := by
  have hbMem1 : ((k, j), bEntry) ∈ hst.base.spkBundles := List.mem_of_find?_eq_some hFindB
  rcases Bool.or_eq_true_iff.mp hKoskSpk0 with hGame0 | hAdv0
  · left
    exact subcase4B_honest_spk_imp_hasEcPkCollisionAuth P st0 hst hNotIn0 hSubSpk hbMem1
      hGame0 hPowEq
  · cases hEc : hasEcPkCollisionAuth P hst
    · right
      have hAdv1 : isAdvRegistered P hst.base.advKeys s.peerSpkPk = true := by
        unfold isAdvRegistered at hAdv0 ⊢
        rcases List.any_eq_true.mp hAdv0 with ⟨x, hx0, hxPred⟩
        exact List.any_eq_true.mpr ⟨x, hSubAdv x hx0, hxPred⟩
      exact subcase4B_advKey_imp_badAuthFgDh1AtMono P hP maxLen uIdx bIdx hst advRoLog respRecs
        hEc hFindU hFindB huNotCorr huIk hAdvSkLen hsMemTake hsSender hAdv1 hPowEq
    · left
      refine ⟨rfl, ?_⟩
      unfold isAuthG3Abort
      simp [hEc]

private theorem subcase4B_from_runInv_mono {S : Setup} (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (maxLen : ℕ)
    (st0 : AuthState S) (hst : AuthHybridState S) (hInv : ValidAuthHybridRunInv S P hst)
    (advRoLog : List Bytes) (respRecs : List AuthRespRecord)
    (hNoEc : hasEcPkCollisionAuth P hst = false)
    {u : Fin S.N_id} {uEntry0 senderEntry : PrincipalEntry} {u_r k j : Nat}
    {bEntry : SpkBundleEntry} {bundle : PreKeyBundleInput} {sessEntry : AuthInitiatorEntry S}
    {hdr : HandshakeHdr}
    (hSub0 : AuthBaseTraceSub st0 hst.base)
    (hNotIn0 : ∀ b0, ((k, j), b0) ∉ st0.spkBundles)
    (hFU0 : st0.principals.find? (fun (idx, _) => idx == u.val) = some (u.val, uEntry0))
    (hbMem : ((k, j), bEntry) ∈ hst.base.spkBundles)
    (hFindSender : findHonestPrincipal P hst.base.principals hdr.ikAPk = some (u_r, senderEntry))
    (hSenderNotCorr : (!senderEntry.corrupted) = true)
    (hPowA0 : P.pow8 hdr.ikAPk = P.pow8 uEntry0.ikAPk)
    (hPowSb : P.pow8 bEntry.spkPk = P.pow8 bundle.spkB)
    (hKosk0 :
      (isGameSpk P st0.spkBundles bundle.spkB ||
        isAdvRegistered P st0.advKeys bundle.spkB) = true)
    (hSessMem : sessEntry ∈ hst.base.sessions)
    (hSendIdx : sessionSenderIdx sessEntry.sid = u.val)
    (hSessSpk : sessEntry.peerSpkPk = bundle.spkB) :
    (hasEcPkCollisionAuth P hst = true ∧ isAuthG3Abort P hst = true) ∨
    ∃ u' : Fin S.N_id, ∃ bIdx ∈ List.range S.N_spk_tot,
      badAuthFgDh1AtMono P maxLen u'.val bIdx hst.base advRoLog respRecs = true := by
  have hu0Mem : (u.val, uEntry0) ∈ st0.principals := List.mem_of_find?_eq_some hFU0
  rcases hSub0.exists_prin hu0Mem with ⟨uEntry1, hu1Mem, _, huIkEq⟩
  have hFS' : hst.base.principals.find? (fun (_, e) => P.pow8 hdr.ikAPk == P.pow8 e.ikAPk) =
      some (u_r, senderEntry) := hFindSender
  have hSenderMem : (u_r, senderEntry) ∈ hst.base.principals := List.mem_of_find?_eq_some hFS'
  have hSenderPow : P.pow8 hdr.ikAPk = P.pow8 senderEntry.ikAPk :=
    beq_iff_eq.mp (List.find?_some
      (p := fun (x : Nat × PrincipalEntry) => P.pow8 hdr.ikAPk == P.pow8 x.2.ikAPk) hFS')
  have hNodupPrin := nodup_principals_of_hasEcPkCollisionAuth_false P hst hNoEc
  have hPrinEq : (u_r, senderEntry) = (u.val, uEntry1) :=
    eq_of_nodup_map_auth (fun (_, e) => P.pow8 e.ikAPk) hNodupPrin hSenderMem hu1Mem
      (by dsimp only; rw [← hSenderPow, hPowA0, huIkEq])
  have huEntryEq : senderEntry = uEntry1 := congrArg Prod.snd hPrinEq
  rw [huEntryEq] at hSenderNotCorr
  have hFindU := find_principals_eq_some_of_mem hInv.1.1.1 hu1Mem
  have hFindB := find_spkBundles_flatIdx_eq_some_of_mem hInv.1.1.2.1 hbMem
  have hbRange := spkBundleFlatIdxVal_mem_range hInv.1.1.2.1 hbMem
  have hLenLe := (validAuthKeyStoresFull_lengths_le S P hst.base hInv.1).2.2.2
  have hsMemTake : sessEntry ∈ hst.base.sessions.take S.N_dh := by
    rw [List.take_of_length_le hLenLe]; exact hSessMem
  have hKoskSpk0 :
      (isGameSpk P st0.spkBundles sessEntry.peerSpkPk ||
        isAdvRegistered P st0.advKeys sessEntry.peerSpkPk) = true := by
    rw [hSessSpk]; exact hKosk0
  have hPowSpk : P.pow8 bEntry.spkPk = P.pow8 sessEntry.peerSpkPk := by
    rw [hSessSpk]; exact hPowSb
  rcases subcase4B_kosk_imp_ecColl_or_badDh1Mono P hP maxLen u.val (spkBundleFlatIdxVal S (k, j))
      st0 hst advRoLog respRecs hNotIn0 (hSub0.subSpk P) hSub0.subAdv hFindU hFindB
      hSenderNotCorr (hInv.1.1.2.2.2.1 (u.val, uEntry1) hu1Mem) hInv.1.1.2.2.2.2.2.2
      hsMemTake hSendIdx hKoskSpk0 hPowSpk with hAbort | hBad
  · exact Or.inl hAbort
  · exact Or.inr ⟨u, spkBundleFlatIdxVal S (k, j), hbRange, hBad⟩

theorem consumeMatchingSentOPK_true_imp_abort_or_badLatchedMono_of_matched_none
    {S : Setup} (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P) (maxLen : ℕ)
    (s3 : AuthAdvLatchedState S) (hInv : ValidAuthHybridRunInv S P s3.hyb)
    {kEntry senderEntry : PrincipalEntry} {u_r k j : Nat}
    {bEntry : SpkBundleEntry} {oEntry : OpkEntry}
    {hdr : HandshakeHdr} {pt : Bytes} {recvEv : RecvdOPKEvent}
    (hMatchedNone :
      s3.hyb.idealSessions.find?
        (matchIdealAuthHandshake P kEntry.ikAPk bEntry.spkPk (some oEntry.opkPk)
          bEntry.pqspkPk hdr) = none)
    (hkMem : (k, kEntry) ∈ s3.hyb.base.principals)
    (hbMem : ((k, j), bEntry) ∈ s3.hyb.base.spkBundles)
    (hrEv : recvEv.bCorr = kEntry.corrupted ∧ recvEv.a0 = hdr.ikAPk ∧ recvEv.b0 = kEntry.ikAPk ∧
      recvEv.sb = bEntry.spkPk ∧ recvEv.ob = oEntry.opkPk ∧ recvEv.a1 = hdr.ekAPk ∧
      recvEv.pk1 = bEntry.pqspkPk ∧ recvEv.ct = hdr.kemCt ∧ recvEv.m = pt)
    (hFindSender : findHonestPrincipal P s3.hyb.base.principals hdr.ikAPk = some (u_r, senderEntry))
    (hSenderNotCorr : (!senderEntry.corrupted) = true)
    (hConsume : (consumeMatchingSentOPK P recvEv s3.hyb.base.sentOPKEvents).1 = true) :
    isAuthG3Abort P s3.hyb = true ∨ badAuthFgAnyLatchedMono P maxLen s3.toFg = true := by
  by_cases hEcB : hasEcPkCollisionAuth P s3.hyb = true
  · exact Or.inl (by unfold isAuthG3Abort; simp [hEcB])
  · have hEc : hasEcPkCollisionAuth P s3.hyb = false := Bool.eq_false_iff.mpr hEcB
    rcases consumeMatchingSentOPK_true_imp_exists_match P recvEv
      s3.hyb.base.sentOPKEvents hConsume with ⟨s_ev, hsEvMem, hMatchSent⟩
    rcases hInv.2.2.1 s_ev hsEvMem with ⟨st0, u, uEntry0, pEntry0, k_s, bundle, opkId, opkPk,
      ekAPk, kemCt, msgPlain, sessEntry, idealEntry, hSub0, hFU0, hFP0, hOpk0, hKosk0,
      hSessMem, hSendIdx, hSessSpk, hsEv0, hIdeal0, hIdealMem0⟩
    by_cases hIn0 : ∃ b0, ((k, j), b0) ∈ st0.spkBundles
    · rcases hIn0 with ⟨b0, hb0Mem0⟩
      have hb0Mem1 : ((k, j), b0) ∈ s3.hyb.base.spkBundles := hSub0.spkBundles_sub.subset hb0Mem0
      have hFB0 := find_spkBundles_flatIdx_eq_some_of_mem hInv.1.1.2.1 hb0Mem1
      have hFB1 := find_spkBundles_flatIdx_eq_some_of_mem hInv.1.1.2.1 hbMem
      rw [hFB1] at hFB0; injection hFB0 with hPair; injection hPair with _ hbEq; subst hbEq
      rcases subcase4A_matchSentOPK_imp_idealSend_and_matchIdealAuthHandshake P st0 s3.hyb hEc
          hSub0.subPrin hFP0 hkMem hb0Mem0 hOpk0 hsEv0 hrEv hIdeal0 hMatchSent with
          ⟨hCond, hMatchIdeal⟩
      exact False.elim
        (List.find?_eq_none.mp hMatchedNone idealEntry (hIdealMem0 hCond) hMatchIdeal)
    · have hNotIn0 : ∀ b0, ((k, j), b0) ∉ st0.spkBundles := fun b0 hb0 => hIn0 ⟨b0, hb0⟩
      have hMatchSent' := hMatchSent
      unfold matchSentOPK at hMatchSent'
      simp only [Bool.and_eq_true, beq_iff_eq] at hMatchSent'
      rcases hMatchSent' with ⟨⟨⟨⟨⟨⟨⟨⟨⟨_, hPowA0⟩, _⟩, _⟩, _⟩, hPowSb⟩, _⟩, _⟩, _⟩, _⟩
      have hPowA0' : P.pow8 hdr.ikAPk = P.pow8 uEntry0.ikAPk := by
        rw [← hrEv.2.1, hPowA0, hsEv0.1]
      have hPowSb' : P.pow8 bEntry.spkPk = P.pow8 bundle.spkB := by
        rw [← hrEv.2.2.2.1, hPowSb, hsEv0.2.2.1]
      rcases subcase4B_from_runInv_mono P hP maxLen st0 s3.hyb hInv s3.adv.advRoLog s3.adv.respRecs
          hEc hSub0 hNotIn0 hFU0 hbMem hFindSender hSenderNotCorr hPowA0' hPowSb' hKosk0
          hSessMem hSendIdx hSessSpk with ⟨_, hAb⟩ | hDh1
      · exact Or.inl hAb
      · exact Or.inr (badAuthFgAnyLatchedMono_of_exists_badAuthFgDh1AtMono P maxLen s3.toFg hDh1)

theorem consumeMatchingSentNoOPK_true_imp_abort_or_badLatchedMono_of_matched_none
    {S : Setup} (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P) (maxLen : ℕ)
    (s3 : AuthAdvLatchedState S) (hInv : ValidAuthHybridRunInv S P s3.hyb)
    {kEntry senderEntry : PrincipalEntry} {u_r k j : Nat}
    {bEntry : SpkBundleEntry} {hdr : HandshakeHdr} {pt : Bytes} {recvEv : RecvdNoOPKEvent}
    (hMatchedNone :
      s3.hyb.idealSessions.find?
        (matchIdealAuthHandshake P kEntry.ikAPk bEntry.spkPk none bEntry.pqspkPk hdr) = none)
    (hkMem : (k, kEntry) ∈ s3.hyb.base.principals)
    (hbMem : ((k, j), bEntry) ∈ s3.hyb.base.spkBundles)
    (hrEv : recvEv.bCorr = kEntry.corrupted ∧ recvEv.a0 = hdr.ikAPk ∧ recvEv.b0 = kEntry.ikAPk ∧
      recvEv.sb = bEntry.spkPk ∧ recvEv.a1 = hdr.ekAPk ∧
      recvEv.pk1 = bEntry.pqspkPk ∧ recvEv.ct = hdr.kemCt ∧ recvEv.m = pt)
    (hFindSender : findHonestPrincipal P s3.hyb.base.principals hdr.ikAPk = some (u_r, senderEntry))
    (hSenderNotCorr : (!senderEntry.corrupted) = true)
    (hConsume : (consumeMatchingSentNoOPK P recvEv s3.hyb.base.sentNoOPKEvents).1 = true) :
    isAuthG3Abort P s3.hyb = true ∨ badAuthFgAnyLatchedMono P maxLen s3.toFg = true := by
  by_cases hEcB : hasEcPkCollisionAuth P s3.hyb = true
  · exact Or.inl (by unfold isAuthG3Abort; simp [hEcB])
  · have hEc : hasEcPkCollisionAuth P s3.hyb = false := Bool.eq_false_iff.mpr hEcB
    rcases consumeMatchingSentNoOPK_true_imp_exists_match P recvEv
      s3.hyb.base.sentNoOPKEvents hConsume with ⟨s_ev, hsEvMem, hMatchSent⟩
    rcases hInv.2.2.2 s_ev hsEvMem with ⟨st0, u, uEntry0, pEntry0, k_s, bundle,
      ekAPk, kemCt, msgPlain, sessEntry, idealEntry, hSub0, hFU0, hFP0, hOpk0, hKosk0,
      hSessMem, hSendIdx, hSessSpk, hsEv0, hIdeal0, hIdealMem0⟩
    by_cases hIn0 : ∃ b0, ((k, j), b0) ∈ st0.spkBundles
    · rcases hIn0 with ⟨b0, hb0Mem0⟩
      have hb0Mem1 : ((k, j), b0) ∈ s3.hyb.base.spkBundles := hSub0.spkBundles_sub.subset hb0Mem0
      have hFB0 := find_spkBundles_flatIdx_eq_some_of_mem hInv.1.1.2.1 hb0Mem1
      have hFB1 := find_spkBundles_flatIdx_eq_some_of_mem hInv.1.1.2.1 hbMem
      rw [hFB1] at hFB0; injection hFB0 with hPair; injection hPair with _ hbEq; subst hbEq
      rcases subcase4A_matchSentNoOPK_imp_idealSend_and_matchIdealAuthHandshake P st0 s3.hyb hEc
          hSub0.subPrin hFP0 hkMem hb0Mem0 hOpk0 hsEv0 hrEv hIdeal0 hMatchSent with
          ⟨hCond, hMatchIdeal⟩
      exact False.elim
        (List.find?_eq_none.mp hMatchedNone idealEntry (hIdealMem0 hCond) hMatchIdeal)
    · have hNotIn0 : ∀ b0, ((k, j), b0) ∉ st0.spkBundles := fun b0 hb0 => hIn0 ⟨b0, hb0⟩
      have hMatchSent' := hMatchSent
      unfold matchSentNoOPK at hMatchSent'
      simp only [Bool.and_eq_true, beq_iff_eq] at hMatchSent'
      rcases hMatchSent' with ⟨⟨⟨⟨⟨⟨⟨⟨_, hPowA0⟩, _⟩, _⟩, hPowSb⟩, _⟩, _⟩, _⟩, _⟩
      have hPowA0' : P.pow8 hdr.ikAPk = P.pow8 uEntry0.ikAPk := by
        rw [← hrEv.2.1, hPowA0, hsEv0.1]
      have hPowSb' : P.pow8 bEntry.spkPk = P.pow8 bundle.spkB := by
        rw [← hrEv.2.2.2.1, hPowSb, hsEv0.2.2.1]
      rcases subcase4B_from_runInv_mono P hP maxLen st0 s3.hyb hInv s3.adv.advRoLog s3.adv.respRecs
          hEc hSub0 hNotIn0 hFU0 hbMem hFindSender hSenderNotCorr hPowA0' hPowSb' hKosk0
          hSessMem hSendIdx hSessSpk with ⟨_, hAb⟩ | hDh1
      · exact Or.inl hAb
      · exact Or.inr (badAuthFgAnyLatchedMono_of_exists_badAuthFgDh1AtMono P maxLen s3.toFg hDh1)

end Proofs.SignalPqxdh.Security
