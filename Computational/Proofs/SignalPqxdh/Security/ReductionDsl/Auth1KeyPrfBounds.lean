/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyPrfMk
import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3H2
import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3D

/-!
# Query Bounds for the One-Key `PrfMsgKeys` Reduction

Establishes `PrfMsgKeysAdv.Bounded` and `primQueryBudget` compliance for the one-key shallow
simulator `prfMsgKeysReductionAuthFixed1Key` and `ReductionDsl` adversary `prfMsgKeys1KeyDslAdv`.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.AuthPrf

open SignalPqxdh
open SignalPqxdh.Security
open SignalPqxdh.Security.AuthSubHops1to3
open OracleSpec OracleComp

private theorem isQueryBoundP_bind_le_mk {ι : Type} {spec : OracleSpec.{0, 0} ι} {α β : Type}
    {p : ι → Prop} [DecidablePred p]
    {oa : OracleComp spec α} {ob : α → OracleComp spec β} {n1 n : ℕ}
    (n2 : ℕ) (h1 : IsQueryBoundP oa p n1) (h2 : ∀ x, IsQueryBoundP (ob x) p n2)
    (hle : n1 + n2 ≤ n) :
    IsQueryBoundP (oa >>= ob) p n :=
  (isQueryBoundP_bind h1 (fun x _ => h2 x)).mono hle

theorem primBounded_stepAuthOtherPrim1Key (S : Setup) (q : AuthQuery S)
    (hst : AuthHybridStateFixed S) :
    PrimBounded (AuthSubHops1to3.stepAuthOtherPrim1Key S q hst) 4 := by
  by_cases hI : AuthQuery.NotInitPrin q
  · rw [stepAuthOtherPrim1Key_eq_of_ne q hI hst]
    exact primBounded_stepAuthOtherPrim S q hst
  · obtain ⟨u, rfl⟩ : ∃ u, q = .initPrin u := by
      by_contra hne; push Not at hne; exact hI hne
    unfold AuthSubHops1to3.stepAuthOtherPrim1Key; dsimp only
    by_cases hWon : hst.base.hasWonAuth = true
    · simp only [hWon, ↓reduceIte]; exact primBounded_pure'
    simp only [hWon, Bool.false_eq_true, ↓reduceIte]
    split
    · exact primBounded_pure'
    · refine primBounded_bind_le 4 (primBounded_embedUnif sampleScalar32 0) (fun _ => ?_) (by omega)
      exact primBounded_bind_le 0 (primBounded_primQ _) (fun _ => primBounded_pure') (by omega)

theorem isQueryBoundP_authMkStepReduction1Key_prim (S : Setup) (idx : Nat)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) (sentChal : Bool) :
    IsQueryBoundP (authMkStepReduction1Key S idx q hst sentChal)
      (fun q => isPrimQuery q = true) (S.N_dh * 30 + 26) := by
  by_cases hI : AuthQuery.NotInitPrin q
  · rw [authMkStepReduction1Key_eq_of_ne idx q hI hst sentChal]
    exact isQueryBoundP_authMkStepReduction_prim S idx q hst sentChal
  · obtain ⟨u, rfl⟩ : ∃ u, q = .initPrin u := by
      by_contra hne; push Not at hne; exact hI hne
    unfold authMkStepReduction1Key; dsimp only
    exact isQueryBoundP_bind_le_mk 0 (isQueryBoundP_embedPrim_isPrimQuery _ _
      (primBounded_stepAuthOtherPrim1Key S _ hst))
      (fun _ => isQueryBoundP_pure _ _ _) (by omega)

theorem isQueryBoundP_runWithPrfMkStep1Key_prim {S : Setup} {α : Type} (idx : Nat)
    (mx : OracleComp (unifSpec + authSpec S) α) (N : Nat)
    (hN : IsQueryBoundP mx (fun q => isGameQuery q = true) N)
    (hst : AuthHybridStateFixed S) (sentChal : Bool) :
    IsQueryBoundP (runWithPrfMkStep (authMkStepReduction1Key S idx) mx hst sentChal)
      (fun q => isPrimQuery q = true) (N * (S.N_dh * 30 + 26)) := by
  induction mx using OracleComp.inductionOn generalizing N hst sentChal with
  | pure a => rw [runWithPrfMkStep_pure]; exact isQueryBoundP_pure _ _ _
  | query_bind q k ih =>
    rw [isQueryBoundP_query_bind_iff] at hN
    rcases q with uq | gq
    · rw [runWithPrfMkStep_query_bind_inl]
      have hk : ∀ u, IsQueryBoundP (k u) (fun q => isGameQuery q = true) N :=
        hN.2
      exact isQueryBoundP_bind_le_mk (N * (S.N_dh * 30 + 26))
        (isQueryBoundP_embedPrim_isPrimQuery _ 0 (primBounded_embedUnif _ 0))
        (fun u => ih u N (hk u) hst sentChal) (by omega)
    · rw [runWithPrfMkStep_query_bind_inr]
      have hPos : 0 < N := hN.1.resolve_left (not_not.mpr rfl)
      have hk : ∀ resp, IsQueryBoundP (k resp) (fun q => isGameQuery q = true) (N - 1) :=
        hN.2
      have hMul : (S.N_dh * 30 + 26) + (N - 1) * (S.N_dh * 30 + 26) ≤ N * (S.N_dh * 30 + 26) := by
        have h1 : 1 + (N - 1) = N := Nat.add_sub_of_le hPos
        calc (S.N_dh * 30 + 26) + (N - 1) * (S.N_dh * 30 + 26)
          _ = (1 + (N - 1)) * (S.N_dh * 30 + 26) := by ring
          _ = N * (S.N_dh * 30 + 26) := by rw [h1]
          _ ≤ N * (S.N_dh * 30 + 26) := Nat.le_refl _
      exact isQueryBoundP_bind_le_mk ((N - 1) * (S.N_dh * 30 + 26))
        (isQueryBoundP_authMkStepReduction1Key_prim S idx gq hst sentChal)
        (fun ⟨⟨resp, s'⟩, c'⟩ => ih resp (N - 1) (hk resp) s' c') hMul

theorem isQueryBoundP_runWithPrfMkStep1Key_prf {S : Setup} {α : Type} (idx : Nat)
    (mx : OracleComp (unifSpec + authSpec S) α) (R : Nat) (hR : IsQueryBoundP mx isAuthRecvQuery R)
    (hst : AuthHybridStateFixed S) (sentChal : Bool) :
    IsQueryBoundP (runWithPrfMkStep (authMkStepReduction1Key S idx) mx hst sentChal)
      (fun q => q.isRight = true) (R + if sentChal then 0 else 1) := by
  induction mx using OracleComp.inductionOn generalizing R hst sentChal with
  | pure a => rw [runWithPrfMkStep_pure]; exact isQueryBoundP_pure _ _ _
  | query_bind q k ih =>
    rw [isQueryBoundP_query_bind_iff] at hR
    rcases q with uq | gq
    · rw [runWithPrfMkStep_query_bind_inl]
      have hk : ∀ u, IsQueryBoundP (k u) isAuthRecvQuery R := fun u =>
        by simpa [isAuthRecvQuery] using hR.2 u
      exact isQueryBoundP_bind_le_mk (R + if sentChal then 0 else 1)
        (isQueryBoundP_embedPrim_isRight _ 0) (fun u => ih u R (hk u) hst sentChal) (by omega)
    · rw [runWithPrfMkStep_query_bind_inr]
      cases gq with
      | sendOPK u i bundle m0 m1 =>
        have hk : ∀ resp, IsQueryBoundP (k resp) isAuthRecvQuery R := fun resp =>
          by simpa [isAuthRecvQuery] using hR.2 resp
        unfold authMkStepReduction1Key; dsimp only; split
        · rw [pure_bind]; exact ih _ R (hk _) hst sentChal
        · exact isQueryBoundP_authMkSendReduction_prf_cont idx (.sendOPK u i) u bundle m0 m1 hst
            sentChal R
            (fun ((resp, s'), c') => runWithPrfMkStep (authMkStepReduction1Key S idx) (k resp) s' c')
            (fun ⟨⟨resp, s'⟩, c'⟩ => ih resp R (hk resp) s' c')
      | sendNoOPK u i bundle m0 m1 =>
        have hk : ∀ resp, IsQueryBoundP (k resp) isAuthRecvQuery R := fun resp =>
          by simpa [isAuthRecvQuery] using hR.2 resp
        unfold authMkStepReduction1Key; dsimp only; split
        · rw [pure_bind]; exact ih _ R (hk _) hst sentChal
        · exact isQueryBoundP_authMkSendReduction_prf_cont idx (.sendNoOPK u i) u bundle m0 m1 hst
            sentChal R
            (fun ((resp, s'), c') => runWithPrfMkStep (authMkStepReduction1Key S idx) (k resp) s' c')
            (fun ⟨⟨resp, s'⟩, c'⟩ => ih resp R (hk resp) s' c')
      | recvOPK k' j o msg =>
        have hPos : 0 < R := hR.1.resolve_left (not_not.mpr trivial)
        have hk : ∀ resp, IsQueryBoundP (k resp) isAuthRecvQuery (R - 1) := fun resp =>
          by simpa [isAuthRecvQuery] using hR.2 resp
        unfold authMkStepReduction1Key; dsimp only; simp only [bind_assoc, pure_bind]
        refine isQueryBoundP_bind_le_mk (1 + ((R - 1) + if sentChal then 0 else 1))
          (isQueryBoundP_embedPrim_isRight _ 0) (fun prep? => ?_) (by omega)
        exact isQueryBoundP_bind_le_mk ((R - 1) + if sentChal then 0 else 1)
          (isQueryBoundP_authMkRecvReduction_prf S idx msg prep? hst sentChal)
          (fun ⟨resp, s'⟩ => ih resp (R - 1) (hk resp) s' sentChal) (by omega)
      | recvNoOPK k' j l msg =>
        have hPos : 0 < R := hR.1.resolve_left (not_not.mpr trivial)
        have hk : ∀ resp, IsQueryBoundP (k resp) isAuthRecvQuery (R - 1) := fun resp =>
          by simpa [isAuthRecvQuery] using hR.2 resp
        unfold authMkStepReduction1Key; dsimp only; simp only [bind_assoc, pure_bind]
        refine isQueryBoundP_bind_le_mk (1 + ((R - 1) + if sentChal then 0 else 1))
          (isQueryBoundP_embedPrim_isRight _ 0) (fun prep? => ?_) (by omega)
        exact isQueryBoundP_bind_le_mk ((R - 1) + if sentChal then 0 else 1)
          (isQueryBoundP_authMkRecvReduction_prf S idx msg prep? hst sentChal)
          (fun ⟨resp, s'⟩ => ih resp (R - 1) (hk resp) s' sentChal) (by omega)
      | _ =>
        have hk : ∀ resp, IsQueryBoundP (k resp) isAuthRecvQuery R := fun resp =>
          by simpa [isAuthRecvQuery] using hR.2 resp
        unfold authMkStepReduction1Key; dsimp only; simp only [bind_assoc, pure_bind]
        exact isQueryBoundP_bind_le_mk (R + if sentChal then 0 else 1)
          (isQueryBoundP_embedPrim_isRight _ 0) (fun ⟨resp, s'⟩ => ih resp R (hk resp) s' sentChal)
            (by omega)

theorem isQueryBoundP_authMkReductionRun1Key_prf (S : Setup) (idx : Nat)
    (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    IsQueryBoundP (authMkReductionRun1Key S idx A.1) (fun q => q.isRight = true)
      (S.N_recv_tot + 1) := by
  unfold authMkReductionRun1Key
  refine isQueryBoundP_bind_le_mk (S.N_recv_tot + 1)
    (isQueryBoundP_embedPrim_isRight _ 0) (fun secb => ?_) (by omega)
  exact isQueryBoundP_bind_le_mk 0
    (isQueryBoundP_runWithPrfMkStep1Key_prf idx A.1.run S.N_recv_tot A.2.2.2.1
      (AuthHybridStateFixed.empty S secb) false)
    (fun _ => isQueryBoundP_embedPrim_isRight _ 0) (by simp)

theorem isQueryBoundP_authMkReductionRun1Key_prim (S : Setup) (idx : Nat)
    (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    IsQueryBoundP (authMkReductionRun1Key S idx A.1)
      (fun q => isPrimQuery q = true) (b.q_total * (S.N_dh * 30 + 26) + S.N_dh * 5) := by
  unfold authMkReductionRun1Key
  refine isQueryBoundP_bind_le_mk (b.q_total * (S.N_dh * 30 + 26) + S.N_dh * 5)
    (isQueryBoundP_embedPrim_isPrimQuery _ 0 (primBounded_embedUnif _ 0)) (fun secb => ?_) (
      by omega)
  exact isQueryBoundP_bind_le_mk (S.N_dh * 5)
    (isQueryBoundP_runWithPrfMkStep1Key_prim idx A.1.run b.q_total
      (SignalPqxdh.QueryBounded.auth_total A.2)
      (AuthHybridStateFixed.empty S secb) false)
    (fun ⟨⟨b', finalSt⟩, _⟩ => isQueryBoundP_embedPrim_isPrimQuery _ _
      (primBounded_finalizeAuthFixedPrim S secb b' finalSt.toAuthHybridState))
    (by omega)

/-- The shallow one-key `PrfMsgKeys` simulator respects its declared query bounds. -/
theorem prfMsgKeysReductionAuthFixed1Key_bounded (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    (prfMsgKeysReductionAuthFixed1Key S b A).Bounded :=
  ⟨isQueryBoundP_bind_le_mk (S.N_recv_tot + 1)
     (isQueryBoundP_embedPrim_isRight _ 0)
     (fun idx => isQueryBoundP_authMkReductionRun1Key_prf S idx b A)
     (by dsimp [prfMsgKeysReductionAuthFixed1Key]; omega),
   isQueryBoundP_bind_le_mk (b.q_total * (S.N_dh * 30 + 26) + S.N_dh * 5)
     (isQueryBoundP_embedPrim_isPrimQuery _ 0 (primBounded_embedUnif _ 0))
     (fun idx => isQueryBoundP_authMkReductionRun1Key_prim S idx b A)
     (by dsimp [prfMsgKeysReductionAuthFixed1Key]; omega)⟩

theorem prfMsgKeysReductionAuthFixed1Key_prim_queries (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    (prfMsgKeysReductionAuthFixed1Key S b A).q_prim ≤ primQueryBudget S b := by
  dsimp [prfMsgKeysReductionAuthFixed1Key, primQueryBudget]
  nlinarith

/-- The one-key `ReductionDsl` `PrfMsgKeys` adversary respects its declared query bounds. -/
theorem prfMsgKeys1KeyDslAdv_bounded (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    (prfMsgKeys1KeyDslAdv S b A).Bounded := by
  rw [prfMsgKeys1KeyDslAdv_eq]
  exact prfMsgKeysReductionAuthFixed1Key_bounded S b A

theorem prfMsgKeys1KeyDslAdv_prim_queries (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    (prfMsgKeys1KeyDslAdv S b A).q_prim ≤ primQueryBudget S b :=
  prfMsgKeysReductionAuthFixed1Key_prim_queries S b A

end SignalPqxdh.Security.ReductionDsl.AuthPrf
