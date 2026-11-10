/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopC6b
public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopC2b
public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopC5
public import VCVio.EvalDist.Monad.Basic
public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopC6c
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthGapDhHopC2
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthGapDhHopC2b
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthGapDhHopC3b
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthGapDhHopC6b
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthHopInterface
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrapBase
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyShallowSims
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyHybrid
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyGapDhIdSim

/-!
# One-Key `Auth` `G3 -> G3.5` Non-Send Step Couplings

Cache-override equalities and `.roQuery` step couplings for `pqxdhAuthAdvLatchedStageImpl1Key`
between `.g3` and `.g3_5`.
-/

@[expose] public section

set_option autoImplicit false
open Classical
open SignalPqxdh SignalPqxdh.Security
open OracleSpec OracleComp
open scoped ENNReal BigOperators
open Proofs.SignalPqxdh.Security.FgGapDh

namespace Proofs.SignalPqxdh.Security

theorem validAuthHybridRunInv_pqxdhAuthAdvLatchedStageImpl1Key
    {S : Setup} (stage : AuthHybridStage) (P : Primitives)
    (q : AuthQuery S)
    (s : AuthAdvLatchedState S) (hInv : ValidAuthHybridRunInv S P s.hyb)
    {y : AuthResponse × AuthAdvLatchedState S}
    (hy : y ∈ support ((pqxdhAuthAdvLatchedStageImpl1Key stage S P q).run s)) :
    ValidAuthHybridRunInv S P y.2.hyb :=
  validAuthHybridRunInv_pqxdhAuthAdvStageImpl1Key stage P q s.adv hInv
    (mem_support_adv_of_mem_support_pqxdhAuthAdvLatchedStageImpl1Key stage P q s y hy)

theorem pqxdhAuthAdvLatchedStageImpl_initPrin_withAuthAdvLatchedRoCache1Key
    (S : Setup) (P : Primitives) (u : Fin S.N_id)
    (c : List (Bytes × DRKey)) (s : AuthAdvLatchedState S) :
    (pqxdhAuthAdvLatchedStageImpl1Key .g3_5 S P (.initPrin u)).run
        (withAuthAdvLatchedRoCache c s) =
      Prod.map id (withAuthAdvLatchedRoCache c) <$>
        ((pqxdhAuthAdvLatchedStageImpl1Key .g3 S P (.initPrin u)).run s) :=
  pqxdhAuthAdvLatchedStageImpl_withAuthAdvLatchedRoCache_of_nonCorrupt1Key P (.initPrin u)
    (fun _ h => nomatch h) c s
    (pqxdhAuthAdvStageImpl_initPrin_withAuthAdvRoCache1Key S P u c s.adv)

theorem pqxdhAuthAdvLatchedStageImpl_genSPK_withAuthAdvLatchedRoCache1Key
    (S : Setup) (P : Primitives) (u : Fin S.N_id) (j : Fin S.N_recv)
    (c : List (Bytes × DRKey)) (s : AuthAdvLatchedState S) :
    (pqxdhAuthAdvLatchedStageImpl1Key .g3_5 S P (.genSPK u j)).run
        (withAuthAdvLatchedRoCache c s) =
      Prod.map id (withAuthAdvLatchedRoCache c) <$>
        ((pqxdhAuthAdvLatchedStageImpl1Key .g3 S P (.genSPK u j)).run s) :=
  pqxdhAuthAdvLatchedStageImpl_withAuthAdvLatchedRoCache_of_nonCorrupt1Key P (.genSPK u j)
    (fun _ h => nomatch h) c s
    (pqxdhAuthAdvStageImpl_genSPK_withAuthAdvRoCache1Key S P u j c s.adv)

theorem pqxdhAuthAdvLatchedStageImpl_genOPK_withAuthAdvLatchedRoCache1Key
    (S : Setup) (P : Primitives) (u : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (c : List (Bytes × DRKey)) (s : AuthAdvLatchedState S) :
    (pqxdhAuthAdvLatchedStageImpl1Key .g3_5 S P (.genOPK u j o)).run
        (withAuthAdvLatchedRoCache c s) =
      Prod.map id (withAuthAdvLatchedRoCache c) <$>
        ((pqxdhAuthAdvLatchedStageImpl1Key .g3 S P (.genOPK u j o)).run s) :=
  pqxdhAuthAdvLatchedStageImpl_withAuthAdvLatchedRoCache_of_nonCorrupt1Key P (.genOPK u j o)
    (fun _ h => nomatch h) c s
    (pqxdhAuthAdvStageImpl_genOPK_withAuthAdvRoCache1Key S P u j o c s.adv)

theorem pqxdhAuthAdvLatchedStageImpl_registerKey_withAuthAdvLatchedRoCache1Key
    (S : Setup) (P : Primitives) (sk : Bytes)
    (c : List (Bytes × DRKey)) (s : AuthAdvLatchedState S) :
    (pqxdhAuthAdvLatchedStageImpl1Key .g3_5 S P (.registerKey sk)).run
        (withAuthAdvLatchedRoCache c s) =
      Prod.map id (withAuthAdvLatchedRoCache c) <$>
        ((pqxdhAuthAdvLatchedStageImpl1Key .g3 S P (.registerKey sk)).run s) :=
  pqxdhAuthAdvLatchedStageImpl_withAuthAdvLatchedRoCache_of_nonCorrupt1Key P (.registerKey sk)
    (fun _ h => nomatch h) c s
    (pqxdhAuthAdvStageImpl_registerKey_withAuthAdvRoCache1Key S P sk c s.adv)

theorem pqxdhAuthAdvLatchedStageImpl_roRootQuery_withAuthAdvLatchedRoCache1Key
    (S : Setup) (P : Primitives) (rk dh : Bytes)
    (c : List (Bytes × DRKey)) (s : AuthAdvLatchedState S) :
    (pqxdhAuthAdvLatchedStageImpl1Key .g3_5 S P (.roRootQuery rk dh)).run
        (withAuthAdvLatchedRoCache c s) =
      Prod.map id (withAuthAdvLatchedRoCache c) <$>
        ((pqxdhAuthAdvLatchedStageImpl1Key .g3 S P (.roRootQuery rk dh)).run s) :=
  pqxdhAuthAdvLatchedStageImpl_withAuthAdvLatchedRoCache_of_nonCorrupt1Key P (.roRootQuery rk dh)
    (fun _ h => nomatch h) c s
    (pqxdhAuthAdvStageImpl_roRootQuery_withAuthAdvRoCache1Key S P rk dh c s.adv)

theorem pqxdhAuthAdvLatchedStageImpl_revealDhSecrets_withAuthAdvLatchedRoCache1Key
    (S : Setup) (P : Primitives)
    (c : List (Bytes × DRKey)) (s : AuthAdvLatchedState S) :
    (pqxdhAuthAdvLatchedStageImpl1Key .g3_5 S P .revealDhSecrets).run
        (withAuthAdvLatchedRoCache c s) =
      Prod.map id (withAuthAdvLatchedRoCache c) <$>
        ((pqxdhAuthAdvLatchedStageImpl1Key .g3 S P .revealDhSecrets).run s) :=
  pqxdhAuthAdvLatchedStageImpl_withAuthAdvLatchedRoCache_of_nonCorrupt1Key P .revealDhSecrets
    (fun _ h => nomatch h) c s
    (pqxdhAuthAdvStageImpl_revealDhSecrets_withAuthAdvRoCache1Key S P c s.adv)

theorem pqxdhAuthAdvLatchedStageImpl_roQuery_run_of_hasWonAuth1Key {S : Setup}
    (stage : AuthHybridStage) (P : Primitives) (secrets : Bytes)
    (s : AuthAdvLatchedState S) (hWon : s.adv.hyb.base.hasWonAuth = true) :
    (pqxdhAuthAdvLatchedStageImpl1Key stage S P (.roQuery secrets)).run s =
      pure (.noneResp, updateRoQueryLatched secrets s.adv.hyb.base.roCache s) := by
  unfold pqxdhAuthAdvLatchedStageImpl1Key pqxdhAuthAdvStageImpl1Key pqxdhAuthHybridKoskImpl1Key
    updateRoQueryLatched
  simp [StateT.run_mk, StateT.run_bind, StateT.run_get, pure_bind, hWon]
  rfl

theorem pqxdhAuthAdvLatchedStageImpl_roQuery_run_eq1Key {S : Setup}
    (stage : AuthHybridStage) (P : Primitives) (secrets : Bytes)
    (s : AuthAdvLatchedState S) (hWonF : s.adv.hyb.base.hasWonAuth = false) :
    (pqxdhAuthAdvLatchedStageImpl1Key stage S P (.roQuery secrets)).run s =
      (evalHkdfOrRo true P s.adv.hyb.base.roCache secrets >>= fun p =>
        pure (.drKeyResp p.1, updateRoQueryLatched secrets p.2 s)) := by
  have hIf : (true && s.adv.hyb.base.hasWonAuth) = false := by simp [hWonF]
  unfold pqxdhAuthAdvLatchedStageImpl1Key pqxdhAuthAdvStageImpl1Key pqxdhAuthHybridKoskImpl1Key
  dsimp only [StateT.run_mk]
  rw [StateT.run_bind, StateT.run_get, pure_bind, hIf]
  simp only [liftAuthBase, pqxdhAuthImpl1KeyG, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    StateT.run_bind, StateT.run_get,
    StateT.run_monadLift, monadLift_self, StateT.run_set, StateT.run_pure,
    bind_assoc, pure_bind]
  rfl

theorem relProbUpToBad_roQuery_of_cache_agree_or_bad1Key
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
      ((pqxdhAuthAdvLatchedStageImpl1Key .g3_5 S P (.roQuery secrets)).run s35)
      ((pqxdhAuthAdvLatchedStageImpl1Key .g3 S P (.roQuery secrets)).run s3) := by
  have hWonEq : s35.adv.hyb.base.hasWonAuth = s3.adv.hyb.base.hasWonAuth := by
    rw [hAg]; rfl
  by_cases hWon : s3.adv.hyb.base.hasWonAuth = true
  · rw [pqxdhAuthAdvLatchedStageImpl_roQuery_run_of_hasWonAuth1Key _ _ _ _ (hWonEq.trans hWon),
        pqxdhAuthAdvLatchedStageImpl_roQuery_run_of_hasWonAuth1Key _ _ _ _ hWon]
    conv_lhs => rw [hAg]
    simp only [withAuthAdvLatchedRoCache_roCache, updateRoQueryLatched_withAuthAdvLatchedRoCache]
    refine RelProbUpToBad.of_pure_or_bad ?_
    by_cases hb : badFg { s3.toFg with advRoLog := secrets :: s3.adv.advRoLog } = true
    · right; dsimp only; rw [hBadIndep]; exact hb
    · left; exact Or.inl ⟨rfl, hHitPres (Bool.eq_false_iff.mpr hb)⟩
  · have hWonF : s3.adv.hyb.base.hasWonAuth = false := Bool.eq_false_iff.mpr hWon
    rw [pqxdhAuthAdvLatchedStageImpl_roQuery_run_eq1Key _ _ _ _ (hWonEq.trans hWonF),
        pqxdhAuthAdvLatchedStageImpl_roQuery_run_eq1Key _ _ _ _ hWonF]
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

end Proofs.SignalPqxdh.Security
