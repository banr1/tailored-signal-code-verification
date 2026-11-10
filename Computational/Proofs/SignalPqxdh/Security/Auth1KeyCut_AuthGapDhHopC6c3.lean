/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopC6c2
public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopC6c1
public import Computational.Proofs.SignalPqxdh.Security.FgGapDh
public import Computational.Proofs.SpecLemmas.Assumptions.KemCorrect
public import VCVio.EvalDist.Monad.Basic
public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopC6c3
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthGapDhHopC2
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthGapDhHopC2b
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthGapDhHopC3b
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthGapDhHopC6b
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthGapDhHopC6c
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthGapDhHopC6c1
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthGapDhHopC6c2
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthHopInterface
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrapBase
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyShallowSims
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyHybrid
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyGapDhIdSim

/-!
# One-Key `Auth` Receive-Origin Invariant and Full Step Couplings

Preservation of `AuthRecvOriginInv` across one-key queries and full `AuthFullG3G3_5CoupledInv`
step couplings for `.roQuery`, `.sendOPK`, and `.sendNoOPK`.
-/

@[expose] public section
set_option autoImplicit false
open SignalPqxdh SignalPqxdh.Security
open OracleSpec OracleComp
open scoped ENNReal
open Proofs.SignalPqxdh.Security.FgGapDh
namespace Proofs.SignalPqxdh.Security

private theorem prop_of_liftAuthBase_c6c3 {S : Setup} (Q : AuthHybridState S → Prop)
    (m : StateT (AuthState S) ProbComp AuthResponse) (hst : AuthHybridState S)
    (h : ∀ p ∈ support (m.run hst.base), Q { hst with base := p.2 })
    {y : AuthResponse × AuthHybridState S}
    (hy : y ∈ support ((liftAuthBase m).run hst)) :
    Q y.2 := by
  unfold liftAuthBase at hy
  simp only [StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
    StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
    support_bind, Set.mem_iUnion, mem_support_pure_iff] at hy
  rcases hy with ⟨⟨resp, base'⟩, hp, _, rfl⟩
  exact h (resp, base') hp
theorem nonRo_query_usedKyberTriples_eq_of_mem_support1Key {S : Setup} (stage : AuthHybridStage)
    (P : Primitives) (q : AuthQuery S) (s : AuthAdvLatchedState S) (hq : isAuthNonRoQuery q = true)
    {y : AuthResponse × AuthAdvLatchedState S}
    (hy : y ∈ support ((pqxdhAuthAdvLatchedStageImpl1Key stage S P q).run s)) :
    y.2.hyb.base.seenKyberBaseKeys = s.hyb.base.seenKyberBaseKeys ∧
    y.2.hyb.base.hasWonAuth = s.hyb.base.hasWonAuth := by
  have hyHyb := mem_support_hyb_of_mem_support_pqxdhAuthAdvLatchedStageImpl1Key stage P q s hy
  let Q : AuthHybridState S → Prop :=
    fun h' => h'.base.seenKyberBaseKeys = s.hyb.base.seenKyberBaseKeys ∧
      h'.base.hasWonAuth = s.hyb.base.hasWonAuth
  unfold pqxdhAuthHybridKoskImpl1Key at hyHyb
  rw [StateT.run_bind, StateT.run_get, pure_bind] at hyHyb
  by_cases hWon : (true && s.hyb.base.hasWonAuth) = true
  · simp only [hWon, ↓reduceIte, StateT.run_pure, mem_support_pure_iff] at hyHyb
    injection hyHyb with _ hEq; rw [hEq]; exact ⟨rfl, rfl⟩
  simp only [hWon, Bool.false_eq_true, ↓reduceIte] at hyHyb
  cases q with
  | roQuery _ => nomatch hq
  | sendOPK _ _ _ _ _ => nomatch hq
  | sendNoOPK _ _ _ _ _ => nomatch hq
  | recvOPK _ _ _ _ => nomatch hq
  | recvNoOPK _ _ _ _ => nomatch hq
  | initPrin u =>
    refine prop_of_liftAuthBase_c6c3 Q _ s.hyb (fun p hp => ?_) hyHyb
    unfold pqxdhAuthImpl1KeyG at hp
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hp; dsimp only at hp
    split_ifs at hp
    · rw [StateT.run_pure, mem_support_pure_iff] at hp; rcases hp with ⟨_, rfl⟩; exact ⟨rfl, rfl⟩
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
        StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        support_bind, Set.mem_iUnion, mem_support_pure_iff] at hp
      rcases hp with ⟨_, _, _, _, _, rfl⟩; exact ⟨rfl, rfl⟩
  | corruptIK u =>
    refine prop_of_liftAuthBase_c6c3 Q _ s.hyb (fun p hp => ?_) hyHyb
    unfold pqxdhAuthImpl1KeyG at hp
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hp; dsimp only at hp
    cases hF : s.hyb.base.principals.find? (fun (idx, _) => idx == u.val) with
    | none =>
      rw [hF] at hp; dsimp only at hp; rw [StateT.run_pure, mem_support_pure_iff] at hp
      rcases hp with ⟨_, rfl⟩; exact ⟨rfl, rfl⟩
    | some ue =>
      rcases ue with ⟨_, entry⟩; rw [hF] at hp; dsimp only at hp
      rw [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure, mem_support_pure_iff] at hp
      rcases hp with ⟨_, rfl⟩; exact ⟨rfl, rfl⟩
  | genSPK u j =>
    refine prop_of_liftAuthBase_c6c3 Q _ s.hyb (fun p hp => ?_) hyHyb
    unfold pqxdhAuthImpl1KeyG at hp
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hp; dsimp only at hp
    split_ifs at hp
    · rw [StateT.run_pure, mem_support_pure_iff] at hp; rcases hp with ⟨_, rfl⟩; exact ⟨rfl, rfl⟩
    · cases hF : s.hyb.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none =>
        rw [hF] at hp; dsimp only at hp; rw [StateT.run_pure, mem_support_pure_iff] at hp
        rcases hp with ⟨_, rfl⟩; exact ⟨rfl, rfl⟩
      | some ue =>
        rcases ue with ⟨_, uEntry⟩; rw [hF] at hp; dsimp only at hp
        simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
          StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
          support_bind, Set.mem_iUnion, mem_support_pure_iff] at hp
        rcases hp with ⟨_, _, _, _, ⟨_, _⟩, _, _, _, _, rfl⟩; exact ⟨rfl, rfl⟩
  | genOPK u j o =>
    refine prop_of_liftAuthBase_c6c3 Q _ s.hyb (fun p hp => ?_) hyHyb
    unfold pqxdhAuthImpl1KeyG at hp
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hp; dsimp only at hp
    split_ifs at hp
    · rw [StateT.run_pure, mem_support_pure_iff] at hp; rcases hp with ⟨_, rfl⟩; exact ⟨rfl, rfl⟩
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
        StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        support_bind, Set.mem_iUnion, mem_support_pure_iff] at hp
      rcases hp with ⟨_, _, _, rfl⟩; exact ⟨rfl, rfl⟩
  | registerKey sk =>
    refine prop_of_liftAuthBase_c6c3 Q _ s.hyb (fun p hp => ?_) hyHyb
    unfold pqxdhAuthImpl1KeyG at hp
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hp; dsimp only at hp
    cases hReg : registerAdvKey P s.hyb.base.advKeys sk with
    | none =>
      rw [hReg] at hp; dsimp only at hp; rw [StateT.run_pure, mem_support_pure_iff] at hp
      rcases hp with ⟨_, rfl⟩; exact ⟨rfl, rfl⟩
    | some pa =>
      rcases pa with ⟨pk, advKeys'⟩; rw [hReg] at hp; dsimp only at hp
      rw [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure, mem_support_pure_iff] at hp
      rcases hp with ⟨_, rfl⟩; exact ⟨rfl, rfl⟩
  | roRootQuery rk dh =>
    refine prop_of_liftAuthBase_c6c3 Q _ s.hyb (fun p hp => ?_) hyHyb
    unfold pqxdhAuthImpl1KeyG at hp
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hp; dsimp only at hp
    split_ifs at hp
    · rw [StateT.run_pure, mem_support_pure_iff] at hp; rcases hp with ⟨_, rfl⟩; exact ⟨rfl, rfl⟩
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
        StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        support_bind, Set.mem_iUnion, mem_support_pure_iff] at hp
      rcases hp with ⟨⟨_, _⟩, _, _, rfl⟩; exact ⟨rfl, rfl⟩
  | revealDhSecrets =>
    refine prop_of_liftAuthBase_c6c3 Q _ s.hyb (fun p hp => ?_) hyHyb
    unfold pqxdhAuthImpl1KeyG at hp
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hp; dsimp only at hp
    split_ifs at hp <;>
      (rw [StateT.run_pure, mem_support_pure_iff] at hp;
       rcases hp with ⟨_, rfl⟩; exact ⟨rfl, rfl⟩)
theorem authRecvOriginInv_of_nonRo_query1Key {S : Setup} (P : Primitives)
    (q : AuthQuery S) (s3 : AuthAdvLatchedState S) (hq : isAuthNonRoQuery q = true)
    (hOrig : AuthRecvOriginInv S P s3)
    {y3 : AuthResponse × AuthAdvLatchedState S}
    (hy3 : y3 ∈ support ((pqxdhAuthAdvLatchedStageImpl1Key .g3 S P q).run s3)) :
    AuthRecvOriginInv S P y3.2 := by
  have hSub := authHybridTraceSub_pqxdhAuthAdvLatchedStageImpl1Key .g3 P q s3 hy3
  rcases nonRo_query_fields_eq_of_mem_support1Key .g3 P q s3 hq hy3 with
    ⟨hRo, _, hLog, hResp, _⟩
  have hKyb := (nonRo_query_usedKyberTriples_eq_of_mem_support1Key .g3 P q s3 hq hy3).1
  exact authRecvOriginInv_of_traceSub_eq_roCache P hOrig hSub hRo
    (fun x hx => hLog ▸ hx) (hResp ▸ List.Sublist.refl _) (hKyb ▸ List.Sublist.refl _)
theorem authRecvOriginInv_of_roQuery1Key {S : Setup} (P : Primitives)
    (secrets : Bytes) (s3 : AuthAdvLatchedState S)
    (hOrig : AuthRecvOriginInv S P s3)
    {y3 : AuthResponse × AuthAdvLatchedState S}
    (hy3 : y3 ∈ support ((pqxdhAuthAdvLatchedStageImpl1Key .g3 S P (.roQuery secrets)).run s3)) :
    AuthRecvOriginInv S P y3.2 := by
  have hSub : ∀ c', AuthHybridTraceSub s3.hyb (updateRoQueryLatched secrets c' s3).hyb :=
    fun _ => ⟨⟨List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _,
      List.Sublist.refl _, List.Sublist.refl _⟩,
      List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _⟩
  cases hWon : s3.adv.hyb.base.hasWonAuth
  · rw [pqxdhAuthAdvLatchedStageImpl_roQuery_run_eq1Key _ _ _ _ hWon,
        evalHkdfOrRo_true_bind_eq] at hy3
    cases hF : s3.adv.hyb.base.roCache.find? (fun (s, _) => s == secrets) with
    | some p =>
      rw [hF] at hy3; rcases p with ⟨_, dk⟩; dsimp only at hy3
      rw [mem_support_pure_iff] at hy3; subst hy3
      exact authRecvOriginInv_of_traceSub_eq_roCache P hOrig (hSub _) rfl
        (fun _ hx => List.mem_cons_of_mem _ hx) (List.Sublist.refl _) (List.Sublist.refl _)
    | none =>
      rw [hF] at hy3; dsimp only at hy3
      simp only [support_bind, Set.mem_iUnion, mem_support_pure_iff] at hy3
      rcases hy3 with ⟨dk, _, rfl⟩
      exact authRecvOriginInv_of_traceSub_cons_roCache P hOrig (hSub _) rfl
        (fun _ hx => List.mem_cons_of_mem _ hx) (List.Sublist.refl _) (List.Sublist.refl _)
        (Or.inl List.mem_cons_self)
  · rw [pqxdhAuthAdvLatchedStageImpl_roQuery_run_of_hasWonAuth1Key _ _ _ _ hWon,
        mem_support_pure_iff] at hy3
    subst hy3
    exact authRecvOriginInv_of_traceSub_eq_roCache P hOrig (hSub _) rfl
      (fun _ hx => List.mem_cons_of_mem _ hx) (List.Sublist.refl _) (List.Sublist.refl _)
private theorem authRecvOriginInv_of_runAuthHybridSendLatched {S : Setup} (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (hSender : sessionSenderIdx sid = u.val)
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes) (s3 : AuthAdvLatchedState S)
    (hKS : ValidAuthKeyStores S P s3.hyb.base)
    (hOrig : AuthRecvOriginInv S P s3)
    {y3 : AuthResponse × AuthAdvLatchedState S}
    (hy3 : y3 ∈ support (runAuthHybridSendLatched .g3 S P sid u bundle m0 m1 s3)) :
    AuthRecvOriginInv S P y3.2 := by
  revert hy3
  rw [runAuthHybridSendLatched_eq .g3 P sid u bundle m0 m1 s3]
  dsimp only
  by_cases h1 : (m0.length != m1.length) = true
  · simp only [h1, ↓reduceIte, mem_support_pure_iff]; rintro rfl; exact hOrig
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : s3.hyb.base.usedSendSessions.contains sid = true
    · simp only [h2, ↓reduceIte, mem_support_pure_iff]; rintro rfl; exact hOrig
    · rw [Bool.not_eq_true] at h2
      simp only [h2, Bool.false_eq_true, ↓reduceIte]
      cases hFU : s3.hyb.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none =>
        dsimp only; rw [mem_support_pure_iff]; rintro rfl; exact hOrig
      | some ue =>
        rcases ue with ⟨uIdx, uEntry⟩; dsimp only
        have huEq : uIdx = u.val :=
          beq_iff_eq.mp (List.find?_some (p := fun (x : Nat × PrincipalEntry) => x.1 == u.val) hFU)
        subst huEq
        split_ifs with h3 h4 h5
        · rw [mem_support_pure_iff]; rintro rfl; exact hOrig
        · rw [mem_support_pure_iff]; rintro rfl; exact hOrig
        · intro hy3
          simp only [support_bind, Set.mem_iUnion, mem_support_pure_iff] at hy3
          rcases hy3 with ⟨_, _, _, _, _, _, _, _, rfl⟩; exact hOrig
        · have hKosk : koskBundleOk P s3.hyb.base.principals s3.hyb.base.spkBundles
              s3.hyb.base.opkEntries s3.hyb.base.advKeys bundle = true := by
            revert h4; simp
          intro hy3
          simp only [support_bind, Set.mem_iUnion] at hy3
          rcases hy3 with ⟨ekASk, hek, kemCoins, _, ephASk, _, spqrCoins, _, hy3⟩
          have hEkLen : ekASk.length = 32 := length_of_mem_support_sampleScalar32 hek
          cases hKem : P.kemEncaps bundle.pqspkB kemCoins with
            | none =>
              rw [hKem] at hy3; dsimp only at hy3
              rw [mem_support_pure_iff] at hy3; subst hy3; exact hOrig
            | some sc =>
              rcases sc with ⟨ss, kemCt⟩
              rw [hKem] at hy3; dsimp only at hy3
              simp only [support_bind, Set.mem_iUnion] at hy3
              rcases hy3 with ⟨⟨drKey, roCache'⟩, hDr, hyPost⟩
              unfold finishAuthHybridSendPost at hyPost
              simp only [support_bind, Set.mem_iUnion, mem_support_pure_iff] at hyPost
              rcases hyPost with ⟨⟨⟨rk1, ck1_0⟩, rootRoCache'⟩, _, rfl⟩
              cases hSpqr : P.spqrInitSend drKey.pqrKey spqrCoins with
              | none =>
                dsimp only [finishAuthHybridSendPure]; rw [hSpqr]; exact hOrig
              | some pqr =>
                rcases pqr with ⟨pqrStA, spqrSalt?, pqRatchetMsg⟩
                have hSub : AuthHybridTraceSub s3.hyb
                    (withLatchedHyb s3 (finishAuthHybridSendPure P sid bundle m0 m1 uEntry
                      ekASk ephASk spqrCoins ss kemCt s3.hyb drKey roCache'
                      rk1 ck1_0 rootRoCache').2).hyb := by
                  unfold finishAuthHybridSendPure; rw [hSpqr]
                  dsimp only [withLatchedHyb, AuthAdvLatchedState.hyb]
                  refine ⟨⟨List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _,
                    List.Sublist.refl _, List.sublist_cons_self _ _⟩,
                    List.sublist_cons_self _ _, List.Sublist.refl _, ?_⟩
                  dsimp only
                  split_ifs <;> first | exact List.sublist_cons_self _ _ | exact List.Sublist.refl _
                have hSendOrig := authSendRoOrigin_finishSend_of_spqr_some P sid u hSender
                  bundle m0 m1 uEntry ekASk kemCoins ephASk spqrCoins ss kemCt hEkLen s3
                  hKS hFU hKosk hKem drKey roCache' rk1 ck1_0 rootRoCache' hSpqr
                have hRoEq : (withLatchedHyb s3 (finishAuthHybridSendPure P sid bundle m0 m1
                    uEntry ekASk ephASk spqrCoins ss kemCt s3.hyb drKey roCache'
                    rk1 ck1_0 rootRoCache').2).adv.hyb.base.roCache = roCache' := by
                  unfold finishAuthHybridSendPure; rw [hSpqr]; rfl
                have hKybSub : s3.hyb.base.seenKyberBaseKeys.Sublist
                    (withLatchedHyb s3 (finishAuthHybridSendPure P sid bundle m0 m1 uEntry
                      ekASk ephASk spqrCoins ss kemCt s3.hyb drKey roCache'
                      rk1 ck1_0 rootRoCache').2).hyb.base.seenKyberBaseKeys := by
                  unfold finishAuthHybridSendPure; rw [hSpqr]; exact List.Sublist.refl _
                unfold evalAuthHybridSendDrKey AuthHybridStage.idealDrKey evalHkdfOrRo at hDr
                simp only [Bool.and_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hDr
                let secrets := buildSecrets (P.x25519 uEntry.secIKA0 bundle.spkB)
                  (P.x25519 ekASk bundle.ikB) (P.x25519 ekASk bundle.spkB)
                  (bundle.opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk)) ss
                cases hF : s3.hyb.base.roCache.find? (fun (s, _) => s == secrets) with
                | some p =>
                  rw [hF] at hDr; rcases p with ⟨_, dk⟩; dsimp only at hDr
                  rw [mem_support_pure_iff] at hDr
                  injection hDr with _ hRcEq; subst hRcEq
                  exact authRecvOriginInv_of_traceSub_eq_roCache P hOrig hSub hRoEq
                    (fun _ hx => hx) (List.Sublist.refl _) hKybSub
                | none =>
                  rw [hF] at hDr; dsimp only at hDr
                  simp only [support_bind, Set.mem_iUnion, mem_support_pure_iff] at hDr
                  rcases hDr with ⟨dk, _, hEq⟩
                  injection hEq with hDkEq hRcEq; subst hDkEq hRcEq
                  exact authRecvOriginInv_of_traceSub_cons_roCache P hOrig hSub hRoEq
                    (fun _ hx => hx) (List.Sublist.refl _) hKybSub (Or.inr (Or.inl hSendOrig))
theorem authRecvOriginInv_of_sendOPK1Key {S : Setup} (P : Primitives)
    (u : Fin S.N_id) (i : Fin S.N_send_opk) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (s3 : AuthAdvLatchedState S) (hKS : ValidAuthKeyStores S P s3.hyb.base)
    (hOrig : AuthRecvOriginInv S P s3)
    {y3 : AuthResponse × AuthAdvLatchedState S}
    (hy3 : y3 ∈ support
      ((pqxdhAuthAdvLatchedStageImpl1Key .g3 S P (.sendOPK u i bundle m0 m1)).run s3)) :
    AuthRecvOriginInv S P y3.2 := by
  unfold pqxdhAuthAdvLatchedStageImpl1Key pqxdhAuthAdvStageImpl1Key pqxdhAuthHybridKoskImpl1Key at hy3
  simp only [StateT.run_mk, StateT.run_bind, StateT.run_get, bind_assoc, pure_bind] at hy3
  split_ifs at hy3
  · rw [StateT.run_pure, pure_bind, mem_support_pure_iff] at hy3; subst hy3; exact hOrig
  · rw [StateT.run_pure, pure_bind, mem_support_pure_iff] at hy3; subst hy3; exact hOrig
  · exact authRecvOriginInv_of_runAuthHybridSendLatched P (.sendOPK u i) u rfl bundle m0 m1
      s3 hKS hOrig hy3
theorem authRecvOriginInv_of_sendNoOPK1Key {S : Setup} (P : Primitives)
    (u : Fin S.N_id) (i : Fin S.N_send_no_opk) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (s3 : AuthAdvLatchedState S) (hKS : ValidAuthKeyStores S P s3.hyb.base)
    (hOrig : AuthRecvOriginInv S P s3)
    {y3 : AuthResponse × AuthAdvLatchedState S}
    (hy3 : y3 ∈ support
      ((pqxdhAuthAdvLatchedStageImpl1Key .g3 S P (.sendNoOPK u i bundle m0 m1)).run s3)) :
    AuthRecvOriginInv S P y3.2 := by
  unfold pqxdhAuthAdvLatchedStageImpl1Key pqxdhAuthAdvStageImpl1Key pqxdhAuthHybridKoskImpl1Key at hy3
  simp only [StateT.run_mk, StateT.run_bind, StateT.run_get, bind_assoc, pure_bind] at hy3
  split_ifs at hy3
  · rw [StateT.run_pure, pure_bind, mem_support_pure_iff] at hy3; subst hy3; exact hOrig
  · rw [StateT.run_pure, pure_bind, mem_support_pure_iff] at hy3; subst hy3; exact hOrig
  · exact authRecvOriginInv_of_runAuthHybridSendLatched P (.sendNoOPK u i) u rfl bundle m0 m1
      s3 hKS hOrig hy3

theorem authRecvOriginInv_of_recvOPK1Key {S : Setup} (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (msg : PreKeyMsg)
    (s3 : AuthAdvLatchedState S) (hOrig : AuthRecvOriginInv S P s3)
    {y3 : AuthResponse × AuthAdvLatchedState S}
    (hy3 : y3 ∈ support ((pqxdhAuthAdvLatchedStageImpl1Key .g3 S P (.recvOPK k j o msg)).run s3)) :
    AuthRecvOriginInv S P y3.2 := by
  rw [pqxdhAuthAdvLatchedStageImpl_recvOPK_run_eq1Key] at hy3
  cases hPre : parseAuthRecvOPKPre P k j o msg s3.hyb.base with
  | none =>
    rw [hPre, mem_support_pure_iff] at hy3; subst hy3
    have hSub : AuthHybridTraceSub s3.hyb
        (wrapAuthAdvLatchedRecv k j msg s3 (.noneResp, s3.hyb)).2.hyb :=
      ⟨⟨List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _,
        List.Sublist.refl _, List.Sublist.refl _⟩,
        List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _⟩
    exact authRecvOriginInv_of_traceSub_eq_roCache P hOrig hSub rfl
      (fun _ hx => hx) (List.sublist_cons_self _ _) (List.Sublist.refl _)
  | some pre =>
    rcases pre with ⟨kEntry, bEntry, oEntry, usedTriples', ss⟩
    rw [hPre] at hy3; dsimp only at hy3
    simp only [support_bind, Set.mem_iUnion, mem_support_pure_iff] at hy3
    rcases hy3 with ⟨res?, hRes, rfl⟩
    let rRec : _root_.SignalPqxdh.Security.RecvKemRecord := {
      k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk,
      pqspkSk := bEntry.pqspkSk, kemCt := msg.hdr.kemCt, kemSs := ss }
    let hstDec : AuthHybridState S := { s3.hyb with recvKemRecs := rRec :: s3.hyb.recvKemRecs }
    cases res? with
    | none =>
      have hSub : AuthHybridTraceSub s3.hyb
          (finishLatchedRecvOPK P k j o kEntry bEntry oEntry usedTriples' msg
            s3 hstDec none).2.hyb :=
        ⟨⟨List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _,
          List.Sublist.refl _, List.Sublist.refl _⟩,
          List.Sublist.refl _, List.sublist_cons_self _ _, List.Sublist.refl _⟩
      exact authRecvOriginInv_of_traceSub_eq_roCache P hOrig hSub rfl
        (fun _ hx => hx) (List.sublist_cons_self _ _) (List.Sublist.refl _)
    | some r =>
      rcases r with ⟨dk, rk1, ck1_1, pt, roCache', rootRoCache'⟩
      have hUtSub :=
        (parseAuthRecvOPKPre_some_props P k j o msg s3.hyb hPre).2.2.2.2.2.2.2.2.2.2.2.1
      rcases finishLatchedRecvOPK_some_ext P k j o kEntry bEntry oEntry usedTriples' msg
          s3 rRec dk rk1 ck1_1 pt roCache' rootRoCache' with
        ⟨hSub, hRoEq, _, hAdvEq, _, hRespSub, hKybEq⟩
      have hKybSub : s3.hyb.base.seenKyberBaseKeys.Sublist
          (finishLatchedRecvOPK P k j o kEntry bEntry oEntry usedTriples' msg s3 hstDec
            (some (dk, rk1, ck1_1, pt, roCache', rootRoCache'))).2.hyb.base.seenKyberBaseKeys := by
        rw [hKybEq]; exact hUtSub
      have hLogSub : ∀ x ∈ s3.adv.advRoLog, x ∈
          (finishLatchedRecvOPK P k j o kEntry bEntry oEntry usedTriples' msg s3 hstDec
            (some (dk, rk1, ck1_1, pt, roCache', rootRoCache'))).2.adv.advRoLog := by
        intro x hx; rw [hAdvEq]; exact hx
      have hNewResp := (authRespRoOrigin_finishLatchedRecvOPK P hP k j o msg s3 hPre dk
          rk1 ck1_1 pt roCache' rootRoCache').1
      rcases roCache_of_mem_support_evalAuthHybridRecvSchedule_g3 P hstDec kEntry bEntry
          (some oEntry.opkPk)
          (recvHandshakeSecrets P kEntry bEntry (some (P.x25519 oEntry.opkSk msg.hdr.ekAPk))
            ss msg.hdr)
          msg hRes with hEq | hCons
      · exact authRecvOriginInv_of_traceSub_eq_roCache P hOrig hSub (hRoEq.trans hEq)
          hLogSub hRespSub hKybSub
      · exact authRecvOriginInv_of_traceSub_cons_roCache P hOrig hSub (hRoEq.trans hCons)
          hLogSub hRespSub hKybSub (Or.inr (Or.inr hNewResp))
theorem authRecvOriginInv_of_recvNoOPK1Key {S : Setup} (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg : PreKeyMsg)
    (s3 : AuthAdvLatchedState S) (hOrig : AuthRecvOriginInv S P s3)
    {y3 : AuthResponse × AuthAdvLatchedState S}
    (hy3 : y3 ∈ support ((pqxdhAuthAdvLatchedStageImpl1Key .g3 S P (.recvNoOPK k j l msg)).run s3)) :
    AuthRecvOriginInv S P y3.2 := by
  rw [pqxdhAuthAdvLatchedStageImpl_recvNoOPK_run_eq1Key] at hy3
  cases hPre : parseAuthRecvNoOPKPre P k j l msg s3.hyb.base with
  | none =>
    rw [hPre, mem_support_pure_iff] at hy3; subst hy3
    have hSub : AuthHybridTraceSub s3.hyb
        (wrapAuthAdvLatchedRecv k j msg s3 (.noneResp, s3.hyb)).2.hyb :=
      ⟨⟨List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _,
        List.Sublist.refl _, List.Sublist.refl _⟩,
        List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _⟩
    exact authRecvOriginInv_of_traceSub_eq_roCache P hOrig hSub rfl
      (fun _ hx => hx) (List.sublist_cons_self _ _) (List.Sublist.refl _)
  | some pre =>
    rcases pre with ⟨kEntry, bEntry, usedTriples', ss⟩
    rw [hPre] at hy3; dsimp only at hy3
    simp only [support_bind, Set.mem_iUnion, mem_support_pure_iff] at hy3
    rcases hy3 with ⟨res?, hRes, rfl⟩
    let rRec : _root_.SignalPqxdh.Security.RecvKemRecord := {
      k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk,
      pqspkSk := bEntry.pqspkSk, kemCt := msg.hdr.kemCt, kemSs := ss }
    let hstDec : AuthHybridState S := { s3.hyb with recvKemRecs := rRec :: s3.hyb.recvKemRecs }
    cases res? with
    | none =>
      have hSub : AuthHybridTraceSub s3.hyb
          (finishLatchedRecvNoOPK P k j l kEntry bEntry usedTriples' msg
            s3 hstDec none).2.hyb :=
        ⟨⟨List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _,
          List.Sublist.refl _, List.Sublist.refl _⟩,
          List.Sublist.refl _, List.sublist_cons_self _ _, List.Sublist.refl _⟩
      exact authRecvOriginInv_of_traceSub_eq_roCache P hOrig hSub rfl
        (fun _ hx => hx) (List.sublist_cons_self _ _) (List.Sublist.refl _)
    | some r =>
      rcases r with ⟨dk, rk1, ck1_1, pt, roCache', rootRoCache'⟩
      have hUtSub :=
        (parseAuthRecvNoOPKPre_some_props P k j l msg s3.hyb hPre).2.2.2.2.2.2.2.2.2.2.1
      rcases finishLatchedRecvNoOPK_some_ext P k j l kEntry bEntry usedTriples' msg
          s3 rRec dk rk1 ck1_1 pt roCache' rootRoCache' with
        ⟨hSub, hRoEq, _, hAdvEq, _, hRespSub, hKybEq⟩
      have hKybSub : s3.hyb.base.seenKyberBaseKeys.Sublist
          (finishLatchedRecvNoOPK P k j l kEntry bEntry usedTriples' msg s3 hstDec
            (some (dk, rk1, ck1_1, pt, roCache', rootRoCache'))).2.hyb.base.seenKyberBaseKeys := by
        rw [hKybEq]; exact hUtSub
      have hLogSub : ∀ x ∈ s3.adv.advRoLog, x ∈
          (finishLatchedRecvNoOPK P k j l kEntry bEntry usedTriples' msg s3 hstDec
            (some (dk, rk1, ck1_1, pt, roCache', rootRoCache'))).2.adv.advRoLog := by
        intro x hx; rw [hAdvEq]; exact hx
      have hNewResp := (authRespRoOrigin_finishLatchedRecvNoOPK P hP k j l msg s3 hPre dk
          rk1 ck1_1 pt roCache' rootRoCache').1
      rcases roCache_of_mem_support_evalAuthHybridRecvSchedule_g3 P hstDec kEntry bEntry none
          (recvHandshakeSecrets P kEntry bEntry none ss msg.hdr) msg hRes with hEq | hCons
      · exact authRecvOriginInv_of_traceSub_eq_roCache P hOrig hSub (hRoEq.trans hEq)
          hLogSub hRespSub hKybSub
      · exact authRecvOriginInv_of_traceSub_cons_roCache P hOrig hSub (hRoEq.trans hCons)
          hLogSub hRespSub hKybSub (Or.inr (Or.inr hNewResp))

theorem fgAuthStepCoupling_cutoff_latched_roQuery_full1Key
    (S : Setup) (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (maxRo : ℕ) (secrets : Bytes) (s35 s3 : AuthAdvLatchedState S)
    (hFull : AuthFullG3G3_5CoupledInv P s35 s3) (hAbF : isAuthG3Abort P s3.hyb = false)
    (hRoStep : s3.adv.advRoLog.length + 1 ≤ maxRo) :
    RelProbUpToBad (fun y35 y3 =>
        (y35.1 = y3.1 ∧ AuthFullG3G3_5CoupledInv P y35.2 y3.2) ∨
        (isAuthG3Abort P y35.2.hyb = true ∧ isAuthG3Abort P y3.2.hyb = true))
      (fun y3 => badAuthFgAnyLatchedMono P maxRo y3.2.toFg)
      ((pqxdhAuthAdvLatchedStageImpl1Key .g3_5 S P (.roQuery secrets)).run s35)
      ((pqxdhAuthAdvLatchedStageImpl1Key .g3 S P (.roQuery secrets)).run s3) := by
  refine relProbUpToBad_of_imp_support_right ?_
  have hStep := fgAuthStepCoupling_cutoff_latched_roQuery1Key S P hP maxRo secrets s35 s3
    hFull.1 hAbF hRoStep
  refine RelProbUpToBad.mono hStep (fun y35 y3 hRel _ hy3 => ?_) (fun _ h => h)
  rcases hRel with ⟨hEq, hInv'⟩ | hAb
  · exact Or.inl ⟨hEq, hInv', authRecvOriginInv_of_roQuery1Key P secrets s3 hFull.2 hy3⟩
  · exact Or.inr hAb

theorem fgAuthStepCoupling_cutoff_latched_sendOPK_or_respEkColl_full1Key
    (S : Setup) (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (maxRo : ℕ) (u : Fin S.N_id) (i : Fin S.N_send_opk)
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes) (s35 s3 : AuthAdvLatchedState S)
    (hFull : AuthFullG3G3_5CoupledInv P s35 s3)
    (hAbF : isAuthG3Abort P s3.hyb = false) (hLogLen : s3.adv.advRoLog.length ≤ maxRo)
    (hRespLen : s3.adv.respRecs.length ≤ S.N_sess_tot) :
    RelProbUpToBad (fun y35 y3 =>
        (y35.1 = y3.1 ∧ AuthFullG3G3_5CoupledInv P y35.2 y3.2) ∨
        (isAuthG3Abort P y35.2.hyb = true ∧ isAuthG3Abort P y3.2.hyb = true))
      (fun y3 => badAuthFgAnyLatchedMono P maxRo y3.2.toFg ||
                 latchRespEkCollSendStep P s3 y3.2 false)
      ((pqxdhAuthAdvLatchedStageImpl1Key .g3_5 S P (.sendOPK u i bundle m0 m1)).run s35)
      ((pqxdhAuthAdvLatchedStageImpl1Key .g3 S P (.sendOPK u i bundle m0 m1)).run s3) := by
  refine relProbUpToBad_of_imp_support_right ?_
  have hStep := fgAuthStepCoupling_cutoff_latched_sendOPK_or_respEkColl1Key S P hP maxRo u i
    bundle m0 m1 s35 s3 hFull.1 hAbF hLogLen hRespLen
  refine RelProbUpToBad.mono hStep (fun y35 y3 hRel _ hy3 => ?_) (fun _ h => h)
  rcases hRel with ⟨hEq, hInv'⟩ | hAb
  · exact Or.inl ⟨hEq, hInv',
      authRecvOriginInv_of_sendOPK1Key P u i bundle m0 m1 s3 hFull.1.2.1.1.1 hFull.2 hy3⟩
  · exact Or.inr hAb

theorem fgAuthStepCoupling_cutoff_latched_sendNoOPK_or_respEkColl_full1Key
    (S : Setup) (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (maxRo : ℕ) (u : Fin S.N_id) (i : Fin S.N_send_no_opk)
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes) (s35 s3 : AuthAdvLatchedState S)
    (hFull : AuthFullG3G3_5CoupledInv P s35 s3)
    (hAbF : isAuthG3Abort P s3.hyb = false) (hLogLen : s3.adv.advRoLog.length ≤ maxRo)
    (hRespLen : s3.adv.respRecs.length ≤ S.N_sess_tot) :
    RelProbUpToBad (fun y35 y3 =>
        (y35.1 = y3.1 ∧ AuthFullG3G3_5CoupledInv P y35.2 y3.2) ∨
        (isAuthG3Abort P y35.2.hyb = true ∧ isAuthG3Abort P y3.2.hyb = true))
      (fun y3 => badAuthFgAnyLatchedMono P maxRo y3.2.toFg ||
                 latchRespEkCollSendStep P s3 y3.2 false)
      ((pqxdhAuthAdvLatchedStageImpl1Key .g3_5 S P (.sendNoOPK u i bundle m0 m1)).run s35)
      ((pqxdhAuthAdvLatchedStageImpl1Key .g3 S P (.sendNoOPK u i bundle m0 m1)).run s3) := by
  refine relProbUpToBad_of_imp_support_right ?_
  have hStep := fgAuthStepCoupling_cutoff_latched_sendNoOPK_or_respEkColl1Key S P hP maxRo u i
    bundle m0 m1 s35 s3 hFull.1 hAbF hLogLen hRespLen
  refine RelProbUpToBad.mono hStep (fun y35 y3 hRel _ hy3 => ?_) (fun _ h => h)
  rcases hRel with ⟨hEq, hInv'⟩ | hAb
  · exact Or.inl ⟨hEq, hInv',
      authRecvOriginInv_of_sendNoOPK1Key P u i bundle m0 m1 s3 hFull.1.2.1.1.1 hFull.2 hy3⟩
  · exact Or.inr hAb

end Proofs.SignalPqxdh.Security
