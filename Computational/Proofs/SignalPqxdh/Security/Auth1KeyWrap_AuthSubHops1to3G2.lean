/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3G
public import Computational.Proofs.SignalPqxdh.Security.CollisionsC
public import Computational.Proofs.SignalPqxdh.Security.FgGapDhC
public import VCVio.EvalDist.Monad.Basic
public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3G2
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyHybrid
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3B
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3F
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3G
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_Collisions
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_CollisionsB
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_TwoKeyAndAuthStatements
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrapBase
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyShallowSims

/-!
# One-Key `RootKdfRO` Up-to-Bad Coupling on Non-Session Queries

Proves `AgreeOffRkAuth` preservation and `RelProbUpToBad` coupling for `authCkOtherStep1Key` over
`pqxdhAuthImpl1KeyG`.
-/

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 400000
open scoped ENNReal BigOperators
open OracleComp OracleSpec MeasureTheory
open SignalPqxdh SignalPqxdh.Security
open _root_.Proofs.SignalPqxdh.Security
open _root_.Proofs.SignalPqxdh.Security.FgGapDh
namespace SignalPqxdh.Security.AuthSubHops1to3

theorem pqxdhAuthImpl_withRootRoCache1Key {S : Setup} (P : Primitives)
    (q : AuthQuery S) (hOther : IsAuthOtherNonRoRoot q)
    (c : List ((Bytes × Bytes) × (Bytes × Bytes))) (b0 : AuthState S) :
    (pqxdhAuthImpl1KeyG true true S P q).run { b0 with rootRoCache := c } =
      ((pqxdhAuthImpl1KeyG true true S P q).run b0 >>= fun x =>
        pure (x.1, { x.2 with rootRoCache := c })) := by
  cases q with
  | sendOPK u i bundle m0 m1 => exact False.elim (hOther.1 u i bundle m0 m1 rfl)
  | sendNoOPK u i bundle m0 m1 => exact False.elim (hOther.2.1 u i bundle m0 m1 rfl)
  | recvOPK k j o msg => exact False.elim (hOther.2.2.1 k j o msg rfl)
  | recvNoOPK k j l msg => exact False.elim (hOther.2.2.2.1 k j l msg rfl)
  | roRootQuery rk dh => exact False.elim (hOther.2.2.2.2 rk dh rfl)
  | _ =>
    unfold pqxdhAuthImpl1KeyG; dsimp only
    simp only [StateT.run_bind, StateT.run_get,
      pure_bind]
    repeat (first
      | rfl
      | (split; all_goals (try simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
          StateT.run_set, StateT.run_pure, bind_assoc, pure_bind]))
      | (refine congrArg (Bind.bind _) (funext fun _ => ?_)))
theorem authCkOtherStep_withRkAuth1Key {S : Setup} (P : Primitives) (idx : Nat) (rkStar : Bytes)
    (q : AuthQuery S) (hOther : IsAuthOtherNonRoRoot q)
    (c : List ((Bytes × Bytes) × (Bytes × Bytes))) (s6 : AuthHybridStateFixed S) :
    authCkOtherStep1Key S P q (withRkAuth idx rkStar c s6) = (authCkOtherStep1Key S P q s6 >>= fun x =>
        pure (x.1, withRkAuth idx rkStar c x.2)) := by
  unfold authCkOtherStep1Key withRkAuth; dsimp only
  split; · simp
  rw [pqxdhAuthImpl_withRootRoCache1Key P q hOther c s6.toAuthHybridState.base, bind_assoc, bind_assoc]
  refine congrArg (Bind.bind ((pqxdhAuthImpl1KeyG true true S P q).run s6.toAuthHybridState.base))
    (funext fun ⟨resp, base'⟩ => ?_)
  simp only [pure_bind]
theorem pqxdhAuthImpl_other_preserves1Key {S : Setup} (P : Primitives)
    (q : AuthQuery S) (hOther : IsAuthOtherNonRoRoot q) (st : AuthState S) :
    ∀ y ∈ support ((pqxdhAuthImpl1KeyG true true S P q).run st), y.2.usedSendSessions =
        st.usedSendSessions ∧
      y.2.seenKyberBaseKeys = st.seenKyberBaseKeys ∧
      (∀ p ∈ st.spkBundles, p ∈ y.2.spkBundles) ∧
      (∀ ik ∈ st.principals.map (fun (_, e) => e.ikAPk),
        ik ∈ y.2.principals.map (fun (_, e) => e.ikAPk)) ∧
      ((∀ p ∈ st.spkBundles, p.2.spkSk.length = 32 ∧ p.2.spkPk = P.x25519Base p.2.spkSk) →
        ∀ p ∈ y.2.spkBundles, p.2.spkSk.length = 32 ∧ p.2.spkPk = P.x25519Base p.2.spkSk) := by
  cases q with
  | sendOPK u i bundle m0 m1 => exact False.elim (hOther.1 u i bundle m0 m1 rfl)
  | sendNoOPK u i bundle m0 m1 => exact False.elim (hOther.2.1 u i bundle m0 m1 rfl)
  | recvOPK k j o msg => exact False.elim (hOther.2.2.1 k j o msg rfl)
  | recvNoOPK k j l msg => exact False.elim (hOther.2.2.2.1 k j l msg rfl)
  | roRootQuery rk dh => exact False.elim (hOther.2.2.2.2 rk dh rfl)
  | initPrin u =>
    intro y hy; unfold pqxdhAuthImpl1KeyG at hy; dsimp only at hy
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hy
    split at hy
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
      subst hy; exact ⟨rfl, rfl, fun _ h => h, fun _ h => h, fun h => h⟩
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
        StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
      rcases hy with ⟨sec0, _, rfl⟩
      exact ⟨rfl, rfl, fun _ h => h, fun _ h => List.mem_cons_of_mem _ h, fun h => h⟩
  | corruptIK u =>
    intro y hy; unfold pqxdhAuthImpl1KeyG at hy; dsimp only at hy
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hy
    split at hy
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
      subst hy; exact ⟨rfl, rfl, fun _ h => h, fun _ h => h, fun h => h⟩
    · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff] at hy
      subst hy
      refine ⟨rfl, rfl, fun _ h => h, fun ik hik => ?_, fun h => h⟩
      dsimp only; rcases List.mem_map.mp hik with ⟨⟨pIdx, pEntry⟩, hpMem, rfl⟩; rw [List.mem_map]
      refine ⟨if pIdx == u.val then (pIdx, { pEntry with corrupted := true }) else (pIdx, pEntry),
          ?_, by split <;> rfl⟩
      rw [List.mem_map]
      exact ⟨(pIdx, pEntry), hpMem, rfl⟩
  | genSPK u j =>
    intro y hy; unfold pqxdhAuthImpl1KeyG at hy; dsimp only at hy
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hy
    split at hy
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
      subst hy; exact ⟨rfl, rfl, fun _ h => h, fun _ h => h, fun h => h⟩
    · split at hy
      · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
          StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
          MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
        rcases hy with ⟨spkSk, hSpkSk, rSpk, _, ⟨pqspkPk, pqspkSk⟩, _, rPq, _, rfl⟩
        refine ⟨rfl, rfl, fun _ h => List.mem_cons_of_mem _ h, fun _ h => h, fun hWf p hp => ?_⟩
        rcases List.mem_cons.mp hp with rfl | hp'
        · exact ⟨length_of_mem_support_sampleScalar32_coll hSpkSk, rfl⟩
        · exact hWf p hp'
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
        subst hy; exact ⟨rfl, rfl, fun _ h => h, fun _ h => h, fun h => h⟩
  | genOPK u j o =>
    intro y hy; unfold pqxdhAuthImpl1KeyG at hy; dsimp only at hy
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hy
    split at hy
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
      subst hy; exact ⟨rfl, rfl, fun _ h => h, fun _ h => h, fun h => h⟩
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
        StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
      rcases hy with ⟨opkSk, _, rfl⟩; exact ⟨rfl, rfl, fun _ h => h, fun _ h => h, fun h => h⟩
  | registerKey sk =>
    intro y hy; unfold pqxdhAuthImpl1KeyG at hy; dsimp only at hy
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hy
    split at hy
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
      subst hy; exact ⟨rfl, rfl, fun _ h => h, fun _ h => h, fun h => h⟩
    · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff] at hy
      subst hy; exact ⟨rfl, rfl, fun _ h => h, fun _ h => h, fun h => h⟩
  | roQuery secrets =>
    intro y hy; unfold pqxdhAuthImpl1KeyG at hy; dsimp only at hy
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
      StateT.run_get, StateT.run_monadLift, monadLift_self, StateT.run_set,
      StateT.run_pure, bind_assoc, pure_bind, MonadAttach.mem_support_bind,
      support_pure, Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨dk, roCache'⟩, _, rfl⟩; exact ⟨rfl, rfl, fun _ h => h, fun _ h => h, fun h =>
        h⟩
  | revealDhSecrets =>
    intro y hy; unfold pqxdhAuthImpl1KeyG at hy; dsimp only at hy
    simp only [↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_pure,
      ] at hy
    subst hy; exact ⟨rfl, rfl, fun _ h => h, fun _ h => h, fun h => h⟩
theorem authCkOtherStep_preserves_agree1Key {S : Setup} (P : Primitives)
    (rkStar : Bytes) (idx : Nat) (q : AuthQuery S) (hOther : IsAuthOtherNonRoRoot q)
    (c5 : List ((Bytes × Bytes) × (Bytes × Bytes)))
    (s6 : AuthHybridStateFixed S)
    (hNoRk6 : cacheHasRk rkStar s6.toAuthHybridState.base.rootRoCache = false)
    (hSlot : authSlotFired S idx s6 = false → c5 = s6.toAuthHybridState.base.rootRoCache)
    (hFilter : filterOutRk rkStar c5 = s6.toAuthHybridState.base.rootRoCache)
    (hWf : AuthRkStateWf P s6)
    (hCacheInv : ∀ s ∈ s6.toAuthHybridState.idealSessions,
      sessionSlotIndex s.sid = idx → SlotSessionCacheInv P rkStar c5 s6 s)
    (hUniq : ∀ s1 ∈ s6.toAuthHybridState.idealSessions, ∀ s2 ∈ s6.toAuthHybridState.idealSessions,
      sessionSlotIndex s1.sid = idx → sessionSlotIndex s2.sid = idx → s1 = s2) :
    ∀ y ∈ support (authCkOtherStep1Key S P q s6),
      AgreeOffRkAuth P rkStar idx (withRkAuth idx rkStar c5 y.2) y.2 := by
  intro y hy
  have hCacheEq := authCkOtherStep_preserves_rootRoCache1Key P q hOther s6 y hy
  unfold authCkOtherStep1Key at hy
  split at hy
  · simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy
    exact ⟨c5, rfl, hNoRk6, hSlot, hFilter, hWf, hCacheInv, hUniq⟩
  simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
  rcases hy with ⟨⟨resp, base'⟩, hbase, rfl⟩; dsimp only at hCacheEq
  obtain ⟨hUsedSend, hUsedKyber, hSpkSub, hPrinSub, hSpkWf⟩ :=
    pqxdhAuthImpl_other_preserves1Key P q hOther s6.toAuthHybridState.base (resp, base') hbase
  refine ⟨c5, rfl, ?_, ?_, ?_, ?_, ?_, hUniq⟩
  · rw [hCacheEq]; exact hNoRk6
  · intro hNotFired
    have hFiredEq : authSlotFired S idx
        { s6 with toAuthHybridState := { s6.toAuthHybridState with base := base' } } =
        authSlotFired S idx s6 := by
      unfold authSlotFired; dsimp only; rw [hUsedSend]
    rw [hFiredEq] at hNotFired
    rw [hCacheEq]
    exact hSlot hNotFired
  · rw [hCacheEq]; exact hFilter
  · refine ⟨hSpkWf hWf.spk_wf, fun s hs => ?_⟩
    have hs0 := hWf.ideal_wf s hs
    dsimp only; rw [hUsedSend]; exact ⟨hs0.1, hs0.2.1, hPrinSub _ hs0.2.2.1, hs0.2.2.2⟩
  · intro s hs hSlotIdx
    exact (hCacheInv s hs hSlotIdx).preserved_of_find?_eq
      (fun _ => rfl) hSpkSub (by rw [hUsedKyber]; exact fun _ h => h)
theorem relProbUpToBad_authCkOtherStep1Key {S : Setup} (P : Primitives)
    (rkStar : Bytes) (idx : Nat) (q : AuthQuery S)
    (s5 s6 : AuthHybridStateFixed S) (hAg : AgreeOffRkAuth P rkStar idx s5 s6)
    (hNotSendOPK : ∀ u i bundle m0 m1, q ≠ .sendOPK u i bundle m0 m1)
    (hNotSendNoOPK : ∀ u i bundle m0 m1, q ≠ .sendNoOPK u i bundle m0 m1)
    (hNotRecvOPK : ∀ k j o msg, q ≠ .recvOPK k j o msg)
    (hNotRecvNoOPK : ∀ k j l msg, q ≠ .recvNoOPK k j l msg) :
    RelProbUpToBad (fun y5 y6 => y5.1 = y6.1 ∧ AgreeOffRkAuth P rkStar idx y5.2 y6.2)
      (fun y6 => cacheHasRk rkStar y6.2.toAuthHybridState.base.rootRoCache)
      (authCkOtherStep1Key S P q s5)
      (authCkOtherStep1Key S P q s6) := by
  rcases hAg with ⟨c5, rfl, hNoRk6, hSlot, hFilter, hWf, hCacheInv, hUniq⟩
  by_cases hRo : ∃ rk dh, q = .roRootQuery rk dh
  · rcases hRo with ⟨rk, dh, rfl⟩
    rw [authCkOtherStep_roRootQuery_eq1Key, authCkOtherStep_roRootQuery_eq1Key]
    by_cases hWon : s6.toAuthHybridState.base.hasWonAuth = true
    · rw [withRkAuth_hasWonAuth, ite_eq_left hWon, ite_eq_left hWon]
      exact RelProbUpToBad.of_pure ⟨rfl, c5, rfl, hNoRk6, hSlot, hFilter, hWf, hCacheInv, hUniq⟩
    rw [withRkAuth_hasWonAuth, ite_eq_right hWon, ite_eq_right hWon]
    dsimp only [withRkAuth]
    refine RelProbUpToBad.bind_rel (R1 := fun y5 y6 => y5.1 = y6.1 ∧ filterOutRk rkStar y5.2 = y6.2
        ∧
        cacheHasRk rkStar y6.2 = false ∧
        (c5 = s6.toAuthHybridState.base.rootRoCache → y5.2 = y6.2) ∧
        (∀ dh0, y5.2.find? (fun (inp, _) => inp == (rkStar, dh0)) =
          c5.find? (fun (inp, _) => inp == (rkStar, dh0))))
      (bad1 := fun y6 => cacheHasRk rkStar y6.2)
      (relProbUpToBad_evalRootKdfOrRo_ext P rkStar rk dh c5
        s6.toAuthHybridState.base.rootRoCache hFilter hNoRk6)
      (fun x6 hBad y6 hy6 => by
        simp only [support_pure, Set.mem_singleton_iff] at hy6
        subst hy6; exact hBad)
      (fun y5 y6 ⟨hOut, hFilter', hNoRk6', hEqImp, hFindEq⟩ => ?_)
    apply RelProbUpToBad.of_pure
    refine ⟨by rw [hOut], y5.2, rfl, hNoRk6', fun hNotFired => hEqImp (hSlot hNotFired),
      hFilter', ⟨hWf.spk_wf, hWf.ideal_wf⟩, fun s hs hSlotIdx => ?_, hUniq⟩
    exact (hCacheInv s hs hSlotIdx).preserved_of_find?_eq hFindEq (fun _ h => h) (fun _ h => h)
  · have hOther : IsAuthOtherNonRoRoot q :=
      ⟨hNotSendOPK, hNotSendNoOPK, hNotRecvOPK, hNotRecvNoOPK, fun rk dh h => hRo ⟨rk, dh, h⟩⟩
    rw [authCkOtherStep_withRkAuth1Key P idx rkStar q hOther c5 s6]
    exact RelProbUpToBad.map_left_of_support (authCkOtherStep1Key S P q s6)
      (fun y => (y.1, withRkAuth idx rkStar c5 y.2))
      (fun y hy => ⟨rfl, authCkOtherStep_preserves_agree1Key P rkStar idx q hOther c5 s6
        hNoRk6 hSlot hFilter hWf hCacheInv hUniq y hy⟩)

end SignalPqxdh.Security.AuthSubHops1to3
