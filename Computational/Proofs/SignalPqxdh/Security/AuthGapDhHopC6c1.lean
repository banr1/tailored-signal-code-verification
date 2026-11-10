/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopC6c
import Computational.Proofs.SignalPqxdh.Security.FgGapDhE
import VCVio.EvalDist.Monad.Basic

/-!
# `Auth` hybrid hop `G3 → G3.5`: non-receiver step couplings

Defines the coupled random-oracle cache invariant `AuthG3G3_5CoupledInv` and proves step
couplings for the seven non-`roCache` queries, `.roQuery`, `.sendOPK`, and `.sendNoOPK`.
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
/-! ## Coupled random-oracle cache invariant -/
def ValidIdealSessionHonesty (S : Setup) (P : Primitives) (hst : AuthHybridState S)
    (s : IdealAuthSession S) (sessEntry : AuthInitiatorEntry S) : Prop :=
  (sessEntry.fresh = true ∨ ((∃ k_s j_s b_s, ((k_s, j_s), b_s) ∈ hst.base.spkBundles ∧
      P.pow8 s.peerSpkPk = P.pow8 b_s.spkPk) ∧ sessEntry.pqspkHonest = true)) ∧
  (sessEntry.spkHonest = true → ∃ k_s j_s b_s,
     ((k_s, j_s), b_s) ∈ hst.base.spkBundles ∧ P.pow8 s.peerSpkPk = P.pow8 b_s.spkPk) ∧
  (sessEntry.pqspkHonest = true → ∃ k_s j_s k_s_Entry b_s,
     (k_s, k_s_Entry) ∈ hst.base.principals ∧ ((k_s, j_s), b_s) ∈ hst.base.spkBundles ∧
     P.pow8 s.peerIkPk = P.pow8 k_s_Entry.ikAPk ∧ s.peerPqspkPk = b_s.pqspkPk)
theorem validIdealSessionHonesty_of_traceSub {S : Setup} (P : Primitives)
    {hst1 hst2 : AuthHybridState S} (hSub : AuthHybridTraceSub hst1 hst2)
    {s : IdealAuthSession S} {sessEntry : AuthInitiatorEntry S}
    (hH : ValidIdealSessionHonesty S P hst1 s sessEntry) :
    ValidIdealSessionHonesty S P hst2 s sessEntry := by
  rcases hH with ⟨h1, h2, h3⟩; refine ⟨?_, ?_, ?_⟩
  · rcases h1 with hFresh | ⟨⟨k_s, j_s, b_s, hbMem, hPow⟩, hPq⟩
    · exact Or.inl hFresh
    · exact Or.inr ⟨⟨k_s, j_s, b_s, hSub.base_sub.spkBundles_sub.subset hbMem, hPow⟩, hPq⟩
  · intro hSpk
    rcases h2 hSpk with ⟨k_s, j_s, b_s, hbMem, hPow⟩
    exact ⟨k_s, j_s, b_s, hSub.base_sub.spkBundles_sub.subset hbMem, hPow⟩
  · intro hPq
    rcases h3 hPq with ⟨k_s, j_s, k_s_Entry1, b_s, hkMem1, hbMem1, hPowIk, hPqEq⟩
    rcases hSub.base_sub.exists_prin hkMem1 with ⟨k_s_Entry2, hkMem2, _, hIkEq⟩
    exact ⟨k_s, j_s, k_s_Entry2, b_s, hkMem2,
      hSub.base_sub.spkBundles_sub.subset hbMem1, by rw [hIkEq, hPowIk], hPqEq⟩
theorem validIdealSessionHonesty_imp_spk_and_pqspk_of_hasBadSigAuth_false
    {S : Setup} (P : Primitives) (hst : AuthHybridState S) (hNoBadSig : hasBadSigAuth hst = false)
    {s : IdealAuthSession S} {sessEntry : AuthInitiatorEntry S}
    (hsMem : sessEntry ∈ hst.base.sessions) (hH : ValidIdealSessionHonesty S P hst s sessEntry) :
    (∃ k_s j_s b_s, ((k_s, j_s), b_s) ∈ hst.base.spkBundles ∧
      P.pow8 s.peerSpkPk = P.pow8 b_s.spkPk) ∧ (∃ k_s j_s k_s_Entry b_s,
      (k_s, k_s_Entry) ∈ hst.base.principals ∧ ((k_s, j_s), b_s) ∈ hst.base.spkBundles ∧
      P.pow8 s.peerIkPk = P.pow8 k_s_Entry.ikAPk ∧ s.peerPqspkPk = b_s.pqspkPk) := by
  rcases hH with ⟨h1, h2, h3⟩; rcases h1 with hFresh | ⟨hSpkW, hPq⟩
  · rcases fresh_imp_spkHonest_and_pqspkHonest_of_hasBadSigAuth_false
      hNoBadSig hsMem hFresh with ⟨hSpk, hPq⟩
    exact ⟨h2 hSpk, h3 hPq⟩
  · exact ⟨hSpkW, h3 hPq⟩
def AuthRoCacheCoupled {S : Setup} (P : Primitives) (s35 s3 : AuthAdvLatchedState S) : Prop :=
  (∀ secrets p,
    s35.adv.hyb.base.roCache.find? (fun (s, _) => s == secrets) = some p →
    s3.adv.hyb.base.roCache.find? (fun (s, _) => s == secrets) = some p) ∧
  (∀ s ∈ s3.hyb.idealSessions,
    ∃ sessEntry u uEntry kemCoins ss_s initRec,
      ValidIdealAuthSession S P s3.hyb s sessEntry u uEntry kemCoins ss_s initRec ∧
      ValidIdealSessionHonesty S P s3.hyb s sessEntry ∧
      let sec := idealSessionSecrets P uEntry sessEntry.ekASk ss_s s
      s3.adv.hyb.base.roCache.find? (fun (x, _) => x == sec) = some (sec, s.drKey)) ∧
  (∀ secrets p,
    s3.adv.hyb.base.roCache.find? (fun (s, _) => s == secrets) = some p →
    p.1 = secrets ∧
    (secrets ∈ s3.adv.advRoLog ∨
     (∃ s_old ∈ s3.hyb.base.sessions,
       s_old.sid ∈ s3.hyb.base.usedSendSessions ∧
       IsSendSessionId S s_old.sid ∧
       extractDh3 secrets = P.x25519 s_old.ekASk s_old.peerSpkPk) ∨
     (∃ k_r j_r bEntry_r r_rec,
       ((k_r, j_r), bEntry_r) ∈ s3.hyb.base.spkBundles ∧
       r_rec ∈ s3.adv.respRecs ∧
       r_rec.bKey = (k_r, j_r) ∧
       r_rec.ekAPk.length = 32 ∧
       extractDh3 secrets = P.x25519 bEntry_r.spkSk r_rec.ekAPk))) ∧
  (∀ secrets p,
    s35.adv.hyb.base.roCache.find? (fun (s, _) => s == secrets) = none →
    s3.adv.hyb.base.roCache.find? (fun (s, _) => s == secrets) = some p →
    ∃ s ∈ s3.hyb.idealSessions, ∃ sessEntry u uEntry kemCoins ss_s initRec,
      ValidIdealAuthSession S P s3.hyb s sessEntry u uEntry kemCoins ss_s initRec ∧
      ValidIdealSessionHonesty S P s3.hyb s sessEntry ∧
      secrets = idealSessionSecrets P uEntry sessEntry.ekASk ss_s s ∧
      p = (secrets, s.drKey))
def AuthG3G3_5CoupledInv {S : Setup} (P : Primitives) (s35 s3 : AuthAdvLatchedState S) : Prop :=
  AuthAdvLatchedAgreeOffRo s35 s3 ∧
  ValidAuthHybridRunInv S P s3.hyb ∧
  AuthRoCacheCoupled P s35 s3
theorem authRoCacheCoupled_empty (S : Setup) (P : Primitives) (secb : Bool) :
    AuthRoCacheCoupled P (AuthAdvLatchedState.empty S secb) (AuthAdvLatchedState.empty S secb) := by
  unfold AuthRoCacheCoupled AuthAdvLatchedState.empty AuthAdvCutoffState.empty
    AuthAdvLatchedState.hyb AuthHybridState.empty AuthState.empty
  dsimp only; refine ⟨fun _ _ h => h, fun _ h => ?_, fun _ _ h => ?_, fun _ _ _ h => ?_⟩
  · cases h
  · cases h
  · cases h
theorem authRoCacheCoupled_of_traceSub_eq_roCache {S : Setup} (P : Primitives)
    {s35 s3 y3 : AuthAdvLatchedState S} (hRc : AuthRoCacheCoupled P s35 s3)
    (hSub : AuthHybridTraceSub s3.hyb y3.hyb)
    (hRoEq : y3.adv.hyb.base.roCache = s3.adv.hyb.base.roCache)
    (hIdEq : y3.hyb.idealSessions = s3.hyb.idealSessions)
    (hLogSub : ∀ x ∈ s3.adv.advRoLog, x ∈ y3.adv.advRoLog)
    (hUsedSub : ∀ x ∈ s3.hyb.base.usedSendSessions, x ∈ y3.hyb.base.usedSendSessions)
    (hRespSub : ∀ x ∈ s3.adv.respRecs, x ∈ y3.adv.respRecs) : AuthRoCacheCoupled P
      (withAuthAdvLatchedRoCache s35.adv.hyb.base.roCache y3) y3 := by
  rcases hRc with ⟨h1, h2, h3, h4⟩
  have h35Ro :
      (withAuthAdvLatchedRoCache s35.adv.hyb.base.roCache y3).adv.hyb.base.roCache =
        s35.adv.hyb.base.roCache := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro secrets p hF35; rw [h35Ro] at hF35; rw [hRoEq]; exact h1 secrets p hF35
  · intro s hs
    rw [hIdEq] at hs
    rcases h2 s hs with ⟨sessEntry, u, uEntry1, kemCoins, ss_s, initRec, hVi1, hVh1, hFind1⟩
    rcases validIdealAuthSession_of_traceSub P hSub hVi1 with ⟨uEntry2, hSecEq, _, hVi2⟩
    have hVh2 := validIdealSessionHonesty_of_traceSub P hSub hVh1
    have hIdealSecEq : idealSessionSecrets P uEntry2 sessEntry.ekASk ss_s s =
          idealSessionSecrets P uEntry1 sessEntry.ekASk ss_s s := by
      unfold idealSessionSecrets; rw [hSecEq]
    refine ⟨sessEntry, u, uEntry2, kemCoins, ss_s, initRec, hVi2, hVh2, ?_⟩
    dsimp only; rw [hRoEq, hIdealSecEq]; exact hFind1
  · intro secrets p hF3
    rw [hRoEq] at hF3; rcases h3 secrets p hF3 with ⟨hp1, hDisj⟩; refine ⟨hp1, ?_⟩
    rcases hDisj with hInLog | ⟨s_old, hsMem, hsUsed, hsInit, hDh3⟩ |
      ⟨k_r, j_r, bEntry_r, r_rec, hbMem, hrMem, hrKey, hEkLen, hDh3⟩
    · exact Or.inl (hLogSub secrets hInLog)
    · exact Or.inr (Or.inl ⟨s_old, hSub.base_sub.sessions_sub.subset hsMem,
        hUsedSub s_old.sid hsUsed, hsInit, hDh3⟩)
    · exact Or.inr (Or.inr ⟨k_r, j_r, bEntry_r, r_rec,
        hSub.base_sub.spkBundles_sub.subset hbMem, hRespSub r_rec hrMem, hrKey, hEkLen, hDh3⟩)
  · intro secrets p hF35 hF3
    rw [h35Ro] at hF35; rw [hRoEq] at hF3
    rcases h4 secrets p hF35 hF3 with
      ⟨s, hs, sessEntry, u, uEntry1, kemCoins, ss_s, initRec, hVi1, hVh1, hSec, hpEq⟩
    rcases validIdealAuthSession_of_traceSub P hSub hVi1 with ⟨uEntry2, hSecEq, _, hVi2⟩
    have hVh2 := validIdealSessionHonesty_of_traceSub P hSub hVh1
    have hIdealSecEq : idealSessionSecrets P uEntry2 sessEntry.ekASk ss_s s =
          idealSessionSecrets P uEntry1 sessEntry.ekASk ss_s s := by
      unfold idealSessionSecrets; rw [hSecEq]
    rw [← hIdealSecEq] at hSec; rw [← hIdEq] at hs
    exact ⟨s, hs, sessEntry, u, uEntry2, kemCoins, ss_s, initRec, hVi2, hVh2, hSec, hpEq⟩
/-! ## Non-`roCache` step couplings -/
theorem mem_support_hyb_of_mem_support_pqxdhAuthAdvLatchedStageImpl
    {S : Setup} (stage : AuthHybridStage) (P : Primitives)
    (q : AuthQuery S) (s : AuthAdvLatchedState S) {y : AuthResponse × AuthAdvLatchedState S}
    (hy : y ∈ support ((pqxdhAuthAdvLatchedStageImpl stage S P q).run s)) :
    (y.1, y.2.hyb) ∈ support ((pqxdhAuthHybridKoskImpl stage true true S P q).run s.hyb) := by
  have hyAdv := mem_support_adv_of_mem_support_pqxdhAuthAdvLatchedStageImpl stage P q s y hy
  unfold AuthAdvLatchedState.hyb
  rw [← map_hyb_pqxdhAuthAdvStageImpl stage S P q s.adv, support_map]
  exact ⟨(y.1, y.2.adv), hyAdv, rfl⟩
theorem authHybridTraceSub_pqxdhAuthAdvLatchedStageImpl
    {S : Setup} (stage : AuthHybridStage) (P : Primitives)
    (q : AuthQuery S) (s : AuthAdvLatchedState S) {y : AuthResponse × AuthAdvLatchedState S}
    (hy : y ∈ support ((pqxdhAuthAdvLatchedStageImpl stage S P q).run s)) :
    AuthHybridTraceSub s.hyb y.2.hyb :=
  authHybridTraceSub_pqxdhAuthHybridKoskImpl stage true true P q s.hyb
    (mem_support_hyb_of_mem_support_pqxdhAuthAdvLatchedStageImpl stage P q s hy)
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
theorem nonRo_query_hyb_fields_eq_of_mem_support {S : Setup} (stage : AuthHybridStage)
    (P : Primitives) (q : AuthQuery S) (hst : AuthHybridState S) (hq : isAuthNonRoQuery q = true)
    {y : AuthResponse × AuthHybridState S}
    (hy : y ∈ support ((pqxdhAuthHybridKoskImpl stage true true S P q).run hst)) :
    y.2.base.roCache = hst.base.roCache ∧ y.2.idealSessions = hst.idealSessions ∧
    y.2.base.usedSendSessions = hst.base.usedSendSessions := by
  let Q : AuthHybridState S → Prop := fun s =>
    s.base.roCache = hst.base.roCache ∧
    s.idealSessions = hst.idealSessions ∧
    s.base.usedSendSessions = hst.base.usedSendSessions
  unfold pqxdhAuthHybridKoskImpl at hy; rw [StateT.run_bind, StateT.run_get, pure_bind] at hy
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
    unfold pqxdhAuthImpl at hp
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
    unfold pqxdhAuthImpl at hp
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
    unfold pqxdhAuthImpl at hp
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
    unfold pqxdhAuthImpl at hp
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
    unfold pqxdhAuthImpl at hp
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
    unfold pqxdhAuthImpl at hp
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
    unfold pqxdhAuthImpl at hp
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hp; dsimp only at hp
    split_ifs at hp <;>
      (rw [StateT.run_pure, mem_support_pure_iff] at hp;
       rcases hp with ⟨_, rfl⟩; exact ⟨rfl, rfl, rfl⟩)
theorem nonRo_query_fields_eq_of_mem_support {S : Setup} (stage : AuthHybridStage)
    (P : Primitives) (q : AuthQuery S) (s : AuthAdvLatchedState S) (hq : isAuthNonRoQuery q = true)
    {y : AuthResponse × AuthAdvLatchedState S}
    (hy : y ∈ support ((pqxdhAuthAdvLatchedStageImpl stage S P q).run s)) :
    y.2.adv.hyb.base.roCache = s.adv.hyb.base.roCache ∧
    y.2.hyb.idealSessions = s.hyb.idealSessions ∧ y.2.adv.advRoLog = s.adv.advRoLog ∧
    y.2.adv.respRecs = s.adv.respRecs ∧
    y.2.hyb.base.usedSendSessions = s.hyb.base.usedSendSessions := by
  have hyHyb := mem_support_hyb_of_mem_support_pqxdhAuthAdvLatchedStageImpl stage P q s hy
  rcases nonRo_query_hyb_fields_eq_of_mem_support stage P q s.hyb hq hyHyb with
    ⟨hRo, hId, hUsed⟩
  have hyAdv := mem_support_adv_of_mem_support_pqxdhAuthAdvLatchedStageImpl stage P q s y hy
  have hLogResp : y.2.adv.advRoLog = s.adv.advRoLog ∧ y.2.adv.respRecs = s.adv.respRecs := by
    cases q with
    | roQuery _ => nomatch hq
    | sendOPK _ _ _ _ _ => nomatch hq
    | sendNoOPK _ _ _ _ _ => nomatch hq
    | recvOPK _ _ _ _ => nomatch hq
    | recvNoOPK _ _ _ _ => nomatch hq
    | _ =>
      unfold pqxdhAuthAdvStageImpl at hyAdv
      simp only [StateT.run_mk, support_bind, Set.mem_iUnion, mem_support_pure_iff] at hyAdv
      rcases hyAdv with ⟨⟨_, _⟩, _, hEq⟩
      injection hEq with _ hAdvEq; rw [hAdvEq]; exact ⟨rfl, rfl⟩
  exact ⟨hRo, hId, hLogResp.1, hLogResp.2, hUsed⟩
theorem authG3G3_5CoupledInv_of_nonRo_query {S : Setup} (P : Primitives)
    (q : AuthQuery S) (s35 s3 : AuthAdvLatchedState S) (hq : isAuthNonRoQuery q = true)
    (hInv : AuthG3G3_5CoupledInv P s35 s3) {y3 : AuthResponse × AuthAdvLatchedState S}
    (hy3 : y3 ∈ support ((pqxdhAuthAdvLatchedStageImpl .g3 S P q).run s3)) :
    AuthG3G3_5CoupledInv P (withAuthAdvLatchedRoCache s35.adv.hyb.base.roCache y3.2) y3.2 := by
  have hSub := authHybridTraceSub_pqxdhAuthAdvLatchedStageImpl .g3 P q s3 hy3
  have hRun' := validAuthHybridRunInv_pqxdhAuthAdvLatchedStageImpl .g3 P q s3 hInv.2.1 hy3
  rcases nonRo_query_fields_eq_of_mem_support .g3 P q s3 hq hy3 with
    ⟨hRo, hId, hLog, hResp, hUsed⟩
  exact ⟨AuthAdvLatchedAgreeOffRo.of_withAuthAdvLatchedRoCache _ _, hRun',
    authRoCacheCoupled_of_traceSub_eq_roCache P hInv.2.2 hSub hRo hId
      (fun x hx => hLog ▸ hx) (fun x hx => hUsed ▸ hx) (fun x hx => hResp ▸ hx)⟩
theorem fgAuthStepCoupling_cutoff_latched_initPrin
    (S : Setup) (P : Primitives) (maxRo : ℕ) (u : Fin S.N_id)
    (s35 s3 : AuthAdvLatchedState S) (hInv : AuthG3G3_5CoupledInv P s35 s3) : RelProbUpToBad
      (fun y35 y3 => (y35.1 = y3.1 ∧ AuthG3G3_5CoupledInv P y35.2 y3.2) ∨
        (isAuthG3Abort P y35.2.hyb = true ∧ isAuthG3Abort P y3.2.hyb = true))
      (fun y3 => badAuthFgAnyLatchedMono P maxRo y3.2.toFg)
      ((pqxdhAuthAdvLatchedStageImpl .g3_5 S P (.initPrin u)).run s35)
      ((pqxdhAuthAdvLatchedStageImpl .g3 S P (.initPrin u)).run s3) :=
  relProbUpToBad_of_withAuthAdvLatchedRoCache_comm P (.initPrin u)
    (AuthG3G3_5CoupledInv P) (badAuthFgAnyLatchedMono P maxRo) s35 s3 hInv.1
    (pqxdhAuthAdvLatchedStageImpl_initPrin_withAuthAdvLatchedRoCache S P u _ s3)
    (fun _ hy3 _ => Or.inl
      (authG3G3_5CoupledInv_of_nonRo_query P (.initPrin u) s35 s3 rfl hInv hy3))
theorem fgAuthStepCoupling_cutoff_latched_corruptIK
    (S : Setup) (P : Primitives) (maxRo : ℕ) (u : Fin S.N_id)
    (s35 s3 : AuthAdvLatchedState S) (hInv : AuthG3G3_5CoupledInv P s35 s3) : RelProbUpToBad
      (fun y35 y3 => (y35.1 = y3.1 ∧ AuthG3G3_5CoupledInv P y35.2 y3.2) ∨
        (isAuthG3Abort P y35.2.hyb = true ∧ isAuthG3Abort P y3.2.hyb = true))
      (fun y3 => badAuthFgAnyLatchedMono P maxRo y3.2.toFg)
      ((pqxdhAuthAdvLatchedStageImpl .g3_5 S P (.corruptIK u)).run s35)
      ((pqxdhAuthAdvLatchedStageImpl .g3 S P (.corruptIK u)).run s3) :=
  relProbUpToBad_of_withAuthAdvLatchedRoCache_comm P (.corruptIK u)
    (AuthG3G3_5CoupledInv P) (badAuthFgAnyLatchedMono P maxRo) s35 s3 hInv.1
    (pqxdhAuthAdvLatchedStageImpl_corruptIK_withAuthAdvLatchedRoCache S P u _ s3)
    (fun _ hy3 _ => Or.inl
      (authG3G3_5CoupledInv_of_nonRo_query P (.corruptIK u) s35 s3 rfl hInv hy3))
theorem fgAuthStepCoupling_cutoff_latched_genSPK
    (S : Setup) (P : Primitives) (maxRo : ℕ) (u : Fin S.N_id) (j : Fin S.N_recv)
    (s35 s3 : AuthAdvLatchedState S) (hInv : AuthG3G3_5CoupledInv P s35 s3) : RelProbUpToBad
      (fun y35 y3 => (y35.1 = y3.1 ∧ AuthG3G3_5CoupledInv P y35.2 y3.2) ∨
        (isAuthG3Abort P y35.2.hyb = true ∧ isAuthG3Abort P y3.2.hyb = true))
      (fun y3 => badAuthFgAnyLatchedMono P maxRo y3.2.toFg)
      ((pqxdhAuthAdvLatchedStageImpl .g3_5 S P (.genSPK u j)).run s35)
      ((pqxdhAuthAdvLatchedStageImpl .g3 S P (.genSPK u j)).run s3) :=
  relProbUpToBad_of_withAuthAdvLatchedRoCache_comm P (.genSPK u j)
    (AuthG3G3_5CoupledInv P) (badAuthFgAnyLatchedMono P maxRo) s35 s3 hInv.1
    (pqxdhAuthAdvLatchedStageImpl_genSPK_withAuthAdvLatchedRoCache S P u j _ s3)
    (fun _ hy3 _ => Or.inl
      (authG3G3_5CoupledInv_of_nonRo_query P (.genSPK u j) s35 s3 rfl hInv hy3))
theorem fgAuthStepCoupling_cutoff_latched_genOPK
    (S : Setup) (P : Primitives) (maxRo : ℕ) (u : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (s35 s3 : AuthAdvLatchedState S) (hInv : AuthG3G3_5CoupledInv P s35 s3) : RelProbUpToBad
      (fun y35 y3 => (y35.1 = y3.1 ∧ AuthG3G3_5CoupledInv P y35.2 y3.2) ∨
        (isAuthG3Abort P y35.2.hyb = true ∧ isAuthG3Abort P y3.2.hyb = true))
      (fun y3 => badAuthFgAnyLatchedMono P maxRo y3.2.toFg)
      ((pqxdhAuthAdvLatchedStageImpl .g3_5 S P (.genOPK u j o)).run s35)
      ((pqxdhAuthAdvLatchedStageImpl .g3 S P (.genOPK u j o)).run s3) :=
  relProbUpToBad_of_withAuthAdvLatchedRoCache_comm P (.genOPK u j o)
    (AuthG3G3_5CoupledInv P) (badAuthFgAnyLatchedMono P maxRo) s35 s3 hInv.1
    (pqxdhAuthAdvLatchedStageImpl_genOPK_withAuthAdvLatchedRoCache S P u j o _ s3)
    (fun _ hy3 _ => Or.inl
      (authG3G3_5CoupledInv_of_nonRo_query P (.genOPK u j o) s35 s3 rfl hInv hy3))
theorem fgAuthStepCoupling_cutoff_latched_registerKey
    (S : Setup) (P : Primitives) (maxRo : ℕ) (sk : Bytes)
    (s35 s3 : AuthAdvLatchedState S) (hInv : AuthG3G3_5CoupledInv P s35 s3) : RelProbUpToBad
      (fun y35 y3 => (y35.1 = y3.1 ∧ AuthG3G3_5CoupledInv P y35.2 y3.2) ∨
        (isAuthG3Abort P y35.2.hyb = true ∧ isAuthG3Abort P y3.2.hyb = true))
      (fun y3 => badAuthFgAnyLatchedMono P maxRo y3.2.toFg)
      ((pqxdhAuthAdvLatchedStageImpl .g3_5 S P (.registerKey sk)).run s35)
      ((pqxdhAuthAdvLatchedStageImpl .g3 S P (.registerKey sk)).run s3) :=
  relProbUpToBad_of_withAuthAdvLatchedRoCache_comm P (.registerKey sk)
    (AuthG3G3_5CoupledInv P) (badAuthFgAnyLatchedMono P maxRo) s35 s3 hInv.1
    (pqxdhAuthAdvLatchedStageImpl_registerKey_withAuthAdvLatchedRoCache S P sk _ s3)
    (fun _ hy3 _ => Or.inl
      (authG3G3_5CoupledInv_of_nonRo_query P (.registerKey sk) s35 s3 rfl hInv hy3))
theorem fgAuthStepCoupling_cutoff_latched_roRootQuery
    (S : Setup) (P : Primitives) (maxRo : ℕ) (rk dh : Bytes)
    (s35 s3 : AuthAdvLatchedState S) (hInv : AuthG3G3_5CoupledInv P s35 s3) : RelProbUpToBad
      (fun y35 y3 => (y35.1 = y3.1 ∧ AuthG3G3_5CoupledInv P y35.2 y3.2) ∨
        (isAuthG3Abort P y35.2.hyb = true ∧ isAuthG3Abort P y3.2.hyb = true))
      (fun y3 => badAuthFgAnyLatchedMono P maxRo y3.2.toFg)
      ((pqxdhAuthAdvLatchedStageImpl .g3_5 S P (.roRootQuery rk dh)).run s35)
      ((pqxdhAuthAdvLatchedStageImpl .g3 S P (.roRootQuery rk dh)).run s3) :=
  relProbUpToBad_of_withAuthAdvLatchedRoCache_comm P (.roRootQuery rk dh)
    (AuthG3G3_5CoupledInv P) (badAuthFgAnyLatchedMono P maxRo) s35 s3 hInv.1
    (pqxdhAuthAdvLatchedStageImpl_roRootQuery_withAuthAdvLatchedRoCache S P rk dh _ s3)
    (fun _ hy3 _ => Or.inl
      (authG3G3_5CoupledInv_of_nonRo_query P (.roRootQuery rk dh) s35 s3 rfl hInv hy3))
theorem fgAuthStepCoupling_cutoff_latched_revealDhSecrets (S : Setup) (P : Primitives) (maxRo : ℕ)
    (s35 s3 : AuthAdvLatchedState S) (hInv : AuthG3G3_5CoupledInv P s35 s3) : RelProbUpToBad
      (fun y35 y3 => (y35.1 = y3.1 ∧ AuthG3G3_5CoupledInv P y35.2 y3.2) ∨
        (isAuthG3Abort P y35.2.hyb = true ∧ isAuthG3Abort P y3.2.hyb = true))
      (fun y3 => badAuthFgAnyLatchedMono P maxRo y3.2.toFg)
      ((pqxdhAuthAdvLatchedStageImpl .g3_5 S P .revealDhSecrets).run s35)
      ((pqxdhAuthAdvLatchedStageImpl .g3 S P .revealDhSecrets).run s3) :=
  relProbUpToBad_of_withAuthAdvLatchedRoCache_comm P .revealDhSecrets
    (AuthG3G3_5CoupledInv P) (badAuthFgAnyLatchedMono P maxRo) s35 s3 hInv.1
    (pqxdhAuthAdvLatchedStageImpl_revealDhSecrets_withAuthAdvLatchedRoCache S P _ s3)
    (fun _ hy3 _ => Or.inl
      (authG3G3_5CoupledInv_of_nonRo_query P .revealDhSecrets s35 s3 rfl hInv hy3))
/-! ## `.roQuery` step coupling -/
private theorem find?_eq_some_of_nodup_map_c6c1 {α β : Type} [BEq β] [LawfulBEq β]
    (f : α → β) {l : List α} (hNodup : (l.map f).Nodup) {x : α} (hx : x ∈ l) :
    l.find? (fun y => f y == f x) = some x := by
  induction l with
  | nil => nomatch hx
  | cons hd tl ih =>
    rw [List.map_cons, List.nodup_cons] at hNodup; rcases List.mem_cons.mp hx with rfl | hTl
    · simp [List.find?]
    · have hNe : (f hd == f x) = false := by
        cases hBeq : (f hd == f x)
        · rfl
        · exact False.elim (hNodup.1 (beq_iff_eq.mp hBeq ▸ List.mem_map_of_mem hTl))
      simp only [List.find?_cons, hNe]; exact ih hNodup.2 hTl
theorem initSessionSlotIdx_eq_sessSlotFlatIdx_of_isSend {S : Setup} {sid : SessionId S}
    (h : IsSendSessionId S sid) : initSessionSlotIdx sid = sessSlotFlatIdx S sid := by
  cases sid with
  | sendOPK _ _ => rfl
  | sendNoOPK _ _ => rfl
  | recvOPK _ _ _ => exact False.elim h
  | recvNoOPK _ _ _ => exact False.elim h
theorem isSendSessionId_of_mem_sessions {S : Setup} {P : Primitives} {st : AuthState S}
    (hV : ValidAuthKeyStoresFull S P st) {s : AuthInitiatorEntry S} (hs : s ∈ st.sessions) :
    IsSendSessionId S s.sid := by
  apply hV.2.1.1; unfold sessPksAuth; rw [List.map_map]; exact List.mem_map.mpr ⟨s, hs, rfl⟩
theorem initSessionSlotIdx_mem_range_of_mem_sessions {S : Setup} {P : Primitives}
    {st : AuthState S} (hV : ValidAuthKeyStoresFull S P st) {s : AuthInitiatorEntry S}
    (hs : s ∈ st.sessions) : initSessionSlotIdx s.sid ∈ List.range S.N_send_tot := by
  have hSend := isSendSessionId_of_mem_sessions hV hs
  rw [List.mem_range, initSessionSlotIdx_eq_sessSlotFlatIdx_of_isSend hSend]
  exact sessSlotFlatIdx_lt S s.sid hSend
theorem nodup_sessions_initSessionSlotIdx {S : Setup} {P : Primitives}
    {st : AuthState S} (hV : ValidAuthKeyStoresFull S P st) :
    (st.sessions.map (fun s => initSessionSlotIdx s.sid)).Nodup := by
  have hNodupEc : (st.sessions.map (fun s => ecSessSlotIdx S s.sid)).Nodup := by
    have h1 := hV.2.1.2; unfold sessPksAuth at h1
    rwa [List.map_map, List.map_map] at h1
  have hMapEq :
      st.sessions.map (fun s => ecSessSlotIdx S s.sid) =
        (st.sessions.map (fun s => initSessionSlotIdx s.sid)).map
          (fun x => S.N_id + S.N_spk_tot + S.N_opk_tot + x) := by
    rw [List.map_map]; refine List.map_congr_left (fun s hs => ?_)
    dsimp only [Function.comp_def, ecSessSlotIdx]
    rw [initSessionSlotIdx_eq_sessSlotFlatIdx_of_isSend (isSendSessionId_of_mem_sessions hV hs)]
  rw [hMapEq] at hNodupEc; exact List.Nodup.of_map _ hNodupEc
theorem find_sessions_slotIdx_eq_some_of_mem {S : Setup} {P : Primitives}
    {st : AuthState S} (hV : ValidAuthKeyStoresFull S P st) {sessEntry : AuthInitiatorEntry S}
    (hs : sessEntry ∈ st.sessions) :
    st.sessions.find? (fun s => initSessionSlotIdx s.sid == initSessionSlotIdx sessEntry.sid) =
      some sessEntry :=
  find?_eq_some_of_nodup_map_c6c1 (fun s => initSessionSlotIdx s.sid)
    (nodup_sessions_initSessionSlotIdx hV) hs
theorem extractDh3_idealSessionSecrets {S : Setup} (P : Primitives) (hw : WellFormedPrimitivesδ P)
    (uEntry : PrincipalEntry) (ekASk ss_s : Bytes) (s : IdealAuthSession S) :
    extractDh3 (idealSessionSecrets P uEntry ekASk ss_s s) = P.x25519 ekASk s.peerSpkPk :=
  extractDh3_buildSecrets
    (hw.x25519_len uEntry.secIKA0 s.peerSpkPk) (hw.x25519_len ekASk s.peerIkPk)
    (hw.x25519_len ekASk s.peerSpkPk)
theorem badAuthFgAnyLatched_true_of_advRoLog_dh3 {S : Setup} (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (maxRo : ℕ)
    (s : AuthFgCutoffState S) (hV : ValidAuthKeyStoresFull S P s.base)
    {sessEntry : AuthInitiatorEntry S} (hsMem : sessEntry ∈ s.base.sessions)
    {k_s j_s : Nat} {b_s : SpkBundleEntry} (hbMem : ((k_s, j_s), b_s) ∈ s.base.spkBundles)
    (hPowSpk : P.pow8 sessEntry.peerSpkPk = P.pow8 b_s.spkPk)
    {sec : Bytes} (hSecTake : sec ∈ s.advRoLog.take maxRo)
    (hDh3 : extractDh3 sec = P.x25519 sessEntry.ekASk sessEntry.peerSpkPk) :
    badAuthFgAnyLatchedMono P maxRo s = true := by
  refine badAuthFgAnyLatchedMono_of_exists_badAuthFgDh3AtMono P maxRo s
    ⟨initSessionSlotIdx sessEntry.sid, initSessionSlotIdx_mem_range_of_mem_sessions hV hsMem,
     spkBundleFlatIdxVal S (k_s, j_s), spkBundleFlatIdxVal_mem_range hV.1.2.1 hbMem, ?_⟩
  unfold badAuthFgDh3AtMono
  rw [find_sessions_slotIdx_eq_some_of_mem hV hsMem,
      find_spkBundles_flatIdx_eq_some_of_mem hV.1.2.1 hbMem]
  dsimp only; rw [Bool.and_eq_true, beq_iff_eq]; refine ⟨hPowSpk, ?_⟩
  apply Bool.or_eq_true_iff.mpr; left; apply Bool.or_eq_true_iff.mpr; left
  have hbSpkPk : b_s.spkPk = P.x25519Base b_s.spkSk :=
    (hV.1.2.2.2.2.1 ((k_s, j_s), b_s) hbMem).2.1
  have hPowSpkBase : P.pow8 sessEntry.peerSpkPk = P.pow8 (P.x25519Base b_s.spkSk) := by
    rw [hPowSpk, hbSpkPk]
  rw [List.any_eq_true]; refine ⟨sec, hSecTake, ?_⟩; rw [beq_iff_eq, hDh3, hbSpkPk]
  exact hP.x25519_pow8_congr sessEntry.ekASk sessEntry.peerSpkPk (P.x25519Base b_s.spkSk)
    (hP.pow8_base_len sessEntry.peerSpkPk b_s.spkSk hPowSpkBase)
    (hP.x25519Base_len b_s.spkSk) hPowSpkBase
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
theorem fgAuthStepCoupling_cutoff_latched_roQuery
    (S : Setup) (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (maxRo : ℕ) (secrets : Bytes) (s35 s3 : AuthAdvLatchedState S)
    (hInv : AuthG3G3_5CoupledInv P s35 s3) (hAbF : isAuthG3Abort P s3.hyb = false)
    (hRoStep : s3.adv.advRoLog.length + 1 ≤ maxRo) : RelProbUpToBad (fun y35 y3 =>
        (y35.1 = y3.1 ∧ AuthG3G3_5CoupledInv P y35.2 y3.2) ∨
        (isAuthG3Abort P y35.2.hyb = true ∧ isAuthG3Abort P y3.2.hyb = true))
      (fun y3 => badAuthFgAnyLatchedMono P maxRo y3.2.toFg)
      ((pqxdhAuthAdvLatchedStageImpl .g3_5 S P (.roQuery secrets)).run s35)
      ((pqxdhAuthAdvLatchedStageImpl .g3 S P (.roQuery secrets)).run s3) := by
  have hw := hP.toWellFormedPrimitivesδ
  rcases hInv with ⟨hAg, hRun, hSub35, hIdealIn3, hOrigin3, hDiffIdeal⟩
  refine relProbUpToBad_roQuery_of_cache_agree_or_bad P secrets
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
/-! ## `.sendOPK` and `.sendNoOPK` step couplings -/
def latchRespEkCollAtSend (P : Primitives)
    (respRecs : List AuthRespRecord) (ekASk : Bytes) : Bool :=
  respRecs.any (fun r => P.pow8 (P.x25519Base ekASk) == P.pow8 r.ekAPk)
def latchRespEkCollSendStep {S : Setup} (P : Primitives)
    (sPre sPost : AuthAdvLatchedState S) (prevLatched : Bool) : Bool :=
  prevLatched ||
  match sPost.hyb.base.sessions with
  | sessEntry :: rest =>
    if rest.length == sPre.hyb.base.sessions.length then
      latchRespEkCollAtSend P sPre.adv.respRecs sessEntry.ekASk
    else false
  | [] => false
structure AuthSendLatchedState (S : Setup) extends AuthAdvLatchedState S where
  respEkCollLatched : Bool := false
def AuthSendLatchedState.empty (S : Setup) (secb : Bool) : AuthSendLatchedState S :=
  { toAuthAdvLatchedState := AuthAdvLatchedState.empty S secb, respEkCollLatched := false }
def wrapSendLatched {S : Setup} (P : Primitives) (s : AuthSendLatchedState S)
    (p : AuthResponse × AuthAdvLatchedState S) : AuthResponse × AuthSendLatchedState S :=
  (p.1, { toAuthAdvLatchedState := p.2
          respEkCollLatched :=
            latchRespEkCollSendStep P s.toAuthAdvLatchedState p.2 s.respEkCollLatched })
def pqxdhAuthSendLatchedStageImpl (stage : AuthHybridStage) (S : Setup) (P : Primitives) :
    QueryImpl (authSpec S) (StateT (AuthSendLatchedState S) ProbComp)
  | .sendOPK u i bundle m0 m1 => StateT.mk (fun s =>
    ((pqxdhAuthAdvLatchedStageImpl stage S P (.sendOPK u i bundle m0 m1)).run
      s.toAuthAdvLatchedState) >>= fun p => pure (wrapSendLatched P s p))
  | .sendNoOPK u i bundle m0 m1 => StateT.mk (fun s =>
    ((pqxdhAuthAdvLatchedStageImpl stage S P (.sendNoOPK u i bundle m0 m1)).run
      s.toAuthAdvLatchedState) >>= fun p => pure (wrapSendLatched P s p))
  | q => StateT.mk (fun s =>
    ((pqxdhAuthAdvLatchedStageImpl stage S P q).run s.toAuthAdvLatchedState) >>=
      fun p => pure (p.1, { s with toAuthAdvLatchedState := p.2 }))
theorem badAuthFgAnyLatched_true_of_session_dh3 {S : Setup} (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (maxRo : ℕ)
    (s : AuthFgCutoffState S) (hV : ValidAuthKeyStoresFull S P s.base)
    {sessEntry : AuthInitiatorEntry S} (hsMem : sessEntry ∈ s.base.sessions)
    {k_s j_s : Nat} {b_s : SpkBundleEntry} (hbMem : ((k_s, j_s), b_s) ∈ s.base.spkBundles)
    (hPowSpk : P.pow8 sessEntry.peerSpkPk = P.pow8 b_s.spkPk)
    {s_old : AuthInitiatorEntry S} (hsOldMem : s_old ∈ s.base.sessions)
    (hSlotNe : initSessionSlotIdx s_old.sid ≠ initSessionSlotIdx sessEntry.sid)
    (hDh3 : P.x25519 s_old.ekASk s_old.peerSpkPk = P.x25519 sessEntry.ekASk sessEntry.peerSpkPk) :
    badAuthFgAnyLatchedMono P maxRo s = true := by
  have hLen := validAuthEc_lengths_le_fg S P s.base ⟨hV.1.1, hV.1.2.1, hV.1.2.2.1, hV.2.1, hV.2.2⟩
  refine badAuthFgAnyLatchedMono_of_exists_badAuthFgDh3AtMono P maxRo s
    ⟨initSessionSlotIdx sessEntry.sid, initSessionSlotIdx_mem_range_of_mem_sessions hV hsMem,
     spkBundleFlatIdxVal S (k_s, j_s), spkBundleFlatIdxVal_mem_range hV.1.2.1 hbMem, ?_⟩
  unfold badAuthFgDh3AtMono
  rw [find_sessions_slotIdx_eq_some_of_mem hV hsMem,
      find_spkBundles_flatIdx_eq_some_of_mem hV.1.2.1 hbMem]
  dsimp only; rw [Bool.and_eq_true, beq_iff_eq]; refine ⟨hPowSpk, ?_⟩
  apply Bool.or_eq_true_iff.mpr; left; apply Bool.or_eq_true_iff.mpr; right
  have hbSpkPk : b_s.spkPk = P.x25519Base b_s.spkSk :=
    (hV.1.2.2.2.2.1 ((k_s, j_s), b_s) hbMem).2.1
  have hPowSpkBase : P.pow8 sessEntry.peerSpkPk = P.pow8 (P.x25519Base b_s.spkSk) := by
    rw [hPowSpk, hbSpkPk]
  rw [List.take_of_length_le hLen.2.2.2, List.any_eq_true]; refine ⟨s_old, hsOldMem, ?_⟩
  rw [Bool.and_eq_true, bne_iff_ne, beq_iff_eq, hDh3, hbSpkPk]
  exact ⟨hSlotNe, hP.x25519_pow8_congr sessEntry.ekASk sessEntry.peerSpkPk (P.x25519Base b_s.spkSk)
    (hP.pow8_base_len sessEntry.peerSpkPk b_s.spkSk hPowSpkBase)
    (hP.x25519Base_len b_s.spkSk) hPowSpkBase⟩
private theorem nodup_spkBundles_fst_c6c1 {S : Setup} {st : AuthState S}
    (hVS : ValidSpkBundles S st.spkBundles) : (st.spkBundles.map Prod.fst).Nodup := by
  have hNodup := hVS.2; have hMapEq :
      st.spkBundles.map (fun e => ecSpkSlotIdx S e.1) =
        (st.spkBundles.map Prod.fst).map (ecSpkSlotIdx S) := by
    rw [List.map_map]; rfl
  rw [hMapEq] at hNodup; exact List.Nodup.of_map _ hNodup
theorem badAuthFgAnyLatched_true_of_respRec_dh3 {S : Setup} (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (maxRo : ℕ)
    (s : AuthFgCutoffState S) (hV : ValidAuthKeyStoresFull S P s.base)
    {sessEntry : AuthInitiatorEntry S} (hsMem : sessEntry ∈ s.base.sessions)
    {k_s j_s : Nat} {b_s : SpkBundleEntry} (hbMem : ((k_s, j_s), b_s) ∈ s.base.spkBundles)
    (hPowSpk : P.pow8 sessEntry.peerSpkPk = P.pow8 b_s.spkPk)
    {k_r j_r : Nat} {bEntry_r : SpkBundleEntry} {r_rec : AuthRespRecord}
    (hbMemR : ((k_r, j_r), bEntry_r) ∈ s.base.spkBundles)
    (hrTake : r_rec ∈ s.respRecs.take S.N_sess_tot) (hrKey : r_rec.bKey = (k_r, j_r))
    (hFlatNe : spkBundleFlatIdxVal S (k_r, j_r) ≠ spkBundleFlatIdxVal S (k_s, j_s))
    (hDh3 : P.x25519 bEntry_r.spkSk r_rec.ekAPk = P.x25519 sessEntry.ekASk sessEntry.peerSpkPk) :
    badAuthFgAnyLatchedMono P maxRo s = true := by
  have hLen := validAuthEc_lengths_le_fg S P s.base ⟨hV.1.1, hV.1.2.1, hV.1.2.2.1, hV.2.1, hV.2.2⟩
  refine badAuthFgAnyLatchedMono_of_exists_badAuthFgDh3AtMono P maxRo s
    ⟨initSessionSlotIdx sessEntry.sid, initSessionSlotIdx_mem_range_of_mem_sessions hV hsMem,
     spkBundleFlatIdxVal S (k_s, j_s), spkBundleFlatIdxVal_mem_range hV.1.2.1 hbMem, ?_⟩
  unfold badAuthFgDh3AtMono
  rw [find_sessions_slotIdx_eq_some_of_mem hV hsMem,
      find_spkBundles_flatIdx_eq_some_of_mem hV.1.2.1 hbMem]
  dsimp only; rw [Bool.and_eq_true, beq_iff_eq]; refine ⟨hPowSpk, ?_⟩
  apply Bool.or_eq_true_iff.mpr; right; rw [List.any_eq_true]; refine ⟨r_rec, hrTake, ?_⟩
  rw [Bool.and_eq_true, beq_iff_eq]
  unfold respAuthCandGuard respAuthDh3Cand respAuthCand
  have hErasedLen :
      (eraseSpkBundlesFg S (spkBundleFlatIdxVal S (k_s, j_s)) s.base.spkBundles).length ≤
        S.N_dh := by
    unfold eraseSpkBundlesFg; rw [List.length_map]; exact hLen.2.1
  rw [List.take_of_length_le hErasedLen, hrKey,
      find?_idx_eraseSpkBundlesFg S (spkBundleFlatIdxVal S (k_s, j_s)) (k_r, j_r) s.base.spkBundles,
      find?_eq_some_of_nodup_map_c6c1 Prod.fst (nodup_spkBundles_fst_c6c1 hV.1.2.1) hbMemR]
  dsimp only [Option.map]
  have hEraseR : eraseSpkBundleEntryFg S (spkBundleFlatIdxVal S (k_s, j_s)) (k_r, j_r) bEntry_r =
        bEntry_r := by
    simp only [eraseSpkBundleEntryFg, beq_iff_eq, ite_eq_right_iff]; intro hEq
    exact False.elim (hFlatNe hEq)
  have hSkLen := (hV.1.2.2.2.2.1 ((k_r, j_r), bEntry_r) hbMemR).1
  have hbSpkPk : b_s.spkPk = P.x25519Base b_s.spkSk :=
    (hV.1.2.2.2.2.1 ((k_s, j_s), b_s) hbMem).2.1
  have hPowSpkBase : P.pow8 sessEntry.peerSpkPk = P.pow8 (P.x25519Base b_s.spkSk) := by
    rw [hPowSpk, hbSpkPk]
  rw [hEraseR, hDh3, hbSpkPk]
  refine ⟨by cases h : bEntry_r.spkSk <;> simp_all, ?_⟩
  exact hP.x25519_pow8_congr sessEntry.ekASk sessEntry.peerSpkPk (P.x25519Base b_s.spkSk)
    (hP.pow8_base_len sessEntry.peerSpkPk b_s.spkSk hPowSpkBase)
    (hP.x25519Base_len b_s.spkSk) hPowSpkBase
theorem idealSend_respOrigin_imp_badDh3_or_respEkColl {S : Setup} (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (maxRo : ℕ)
    (s : AuthFgCutoffState S) (hV : ValidAuthKeyStoresFull S P s.base)
    {sessEntry : AuthInitiatorEntry S} (hsMem : sessEntry ∈ s.base.sessions)
    (_hEkLen : sessEntry.ekASk.length = 32) {k_s j_s : Nat} {b_s : SpkBundleEntry}
    (hbMem : ((k_s, j_s), b_s) ∈ s.base.spkBundles)
    (hPowSpk : P.pow8 sessEntry.peerSpkPk = P.pow8 b_s.spkPk)
    {k_r j_r : Nat} {bEntry_r : SpkBundleEntry} {r_rec : AuthRespRecord}
    (hbMemR : ((k_r, j_r), bEntry_r) ∈ s.base.spkBundles)
    (hrTake : r_rec ∈ s.respRecs.take S.N_sess_tot) (hrKey : r_rec.bKey = (k_r, j_r))
    (hrEkLen : r_rec.ekAPk.length = 32) (hDh3 : P.x25519 bEntry_r.spkSk r_rec.ekAPk =
      P.x25519 sessEntry.ekASk sessEntry.peerSpkPk) : badAuthFgAnyLatchedMono P maxRo s = true ∨
      latchRespEkCollAtSend P s.respRecs sessEntry.ekASk = true := by
  by_cases hFlatEq : spkBundleFlatIdxVal S (k_r, j_r) = spkBundleFlatIdxVal S (k_s, j_s)
  · right
    have hw := hP.toWellFormedPrimitivesδ
    have hFR := find_spkBundles_flatIdx_eq_some_of_mem hV.1.2.1 hbMemR
    have hFS := find_spkBundles_flatIdx_eq_some_of_mem hV.1.2.1 hbMem; rw [hFlatEq, hFS] at hFR
    injection hFR with hPairEq
    have hbEq : bEntry_r = b_s := congrArg Prod.snd hPairEq.symm; rw [hbEq] at hDh3
    have hbValid := hV.1.2.2.2.2.1 ((k_s, j_s), b_s) hbMem
    have hSpkSkLen : b_s.spkSk.length = 32 := hbValid.1
    have hSpkPkEq : b_s.spkPk = P.x25519Base b_s.spkSk := hbValid.2.1
    have hPowSpkBase : P.pow8 sessEntry.peerSpkPk = P.pow8 (P.x25519Base b_s.spkSk) := by
      rw [hPowSpk, hSpkPkEq]
    have hDhEq : P.x25519 b_s.spkSk r_rec.ekAPk =
          P.x25519 b_s.spkSk (P.x25519Base sessEntry.ekASk) := by
      rw [hDh3,
          hP.x25519_pow8_congr sessEntry.ekASk sessEntry.peerSpkPk (P.x25519Base b_s.spkSk)
            (hP.pow8_base_len sessEntry.peerSpkPk b_s.spkSk hPowSpkBase)
            (hw.x25519Base_len b_s.spkSk) hPowSpkBase,
          hw.x25519_comm sessEntry.ekASk b_s.spkSk]
    have hPowEk : P.pow8 r_rec.ekAPk = P.pow8 (P.x25519Base sessEntry.ekASk) :=
      hP.x25519_inj_pow8 b_s.spkSk r_rec.ekAPk (P.x25519Base sessEntry.ekASk)
        hSpkSkLen hrEkLen (hw.x25519Base_len sessEntry.ekASk) hDhEq
    unfold latchRespEkCollAtSend; rw [List.any_eq_true]
    exact ⟨r_rec, List.mem_of_mem_take hrTake, beq_iff_eq.mpr hPowEk.symm⟩
  · left
    exact badAuthFgAnyLatched_true_of_respRec_dh3 P hP maxRo s hV hsMem hbMem hPowSpk
      hbMemR hrTake hrKey hFlatEq hDh3
theorem relProbUpToBad_of_imp_support_right {α : Type}
    {R : α → α → Prop} {bad : α → Bool} {m1 m2 : ProbComp α}
    (h : RelProbUpToBad (fun x y => y ∈ support m2 → R x y) bad m1 m2) :
    RelProbUpToBad R bad m1 m2 := by
  classical
  refine ⟨fun w1 w2 hw1 hw2 hle => ?_, fun w2 w1 hw2 hle => ?_⟩
  · refine le_trans (h.1 w1 (fun y => if y ∈ support m2 then w2 y else 1) hw1
      (fun y hb => by split_ifs; exact hw2 y hb; rfl)
      (fun x y hImp => by
        split_ifs with hSup
        · exact hle x y (hImp hSup)
        · exact hw1 x)) ?_
    exact probExpect_mono_of_support m2 _ _ (fun y hSup => by simp [hSup])
  · refine le_trans
      (probExpect_mono_of_support m2 _ _ (fun y hSup => by simp [hSup]))
      (h.2 (fun y => if y ∈ support m2 then w2 y else 0) w1
        (fun y hb => by split_ifs; exact hw2 y hb; rfl)
        (fun x y hImp => by
          split_ifs with hSup
          · exact hle x y (hImp hSup)
          · exact zero_le))
def withLatchedHyb {S : Setup} (s : AuthAdvLatchedState S) (h' : AuthHybridState S) :
    AuthAdvLatchedState S :=
  { s with adv := { s.adv with hyb := h' } }
def mkSendSessEntry {S : Setup} (P : Primitives) (st : AuthState S)
    (sid : SessionId S) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (isFreshPeer : Bool) (ekASk ephASk : Bytes) : AuthInitiatorEntry S :=
  let (spkHon, opkHon, pqspkHon) :=
    checkBundleProvenanceExact P st.principals st.spkBundles st.opkEntries bundle
  { sid := sid, peerIkPk := bundle.ikB, peerSpkPk := bundle.spkB,
    peerOpkPk? := bundle.opkB?.map Prod.snd, peerPqspkPk := bundle.pqspkB,
    spkHonest := spkHon, opkHonest := opkHon, pqspkHonest := pqspkHon,
    ekASk := ekASk, ephASk := ephASk, fresh := isFreshPeer,
    challenged := isFreshPeer && (m0 != m1) }
def sendPostFgState {S : Setup} (s : AuthAdvLatchedState S)
    (sid : SessionId S) (sessEntry : AuthInitiatorEntry S) : AuthFgCutoffState S :=
  { s.toFg with
    base := { s.hyb.base with
      sessions         := sessEntry :: s.hyb.base.sessions
      usedSendSessions := sid :: s.hyb.base.usedSendSessions } }
theorem validAuthKeyStoresFull_sendPostFgState {S : Setup} {P : Primitives}
    (s : AuthAdvLatchedState S) (hV : ValidAuthKeyStoresFull S P s.hyb.base)
    {sid : SessionId S} (hSend : IsSendSessionId S sid)
    (hNotUsed : s.hyb.base.usedSendSessions.contains sid = false)
    (sessEntry : AuthInitiatorEntry S) (hSid : sessEntry.sid = sid) :
    ValidAuthKeyStoresFull S P (sendPostFgState s sid sessEntry).base := by
  have hFresh' : ((sessPksAuth S P s.hyb.base).map Prod.fst).any (fun x => x == sid) = false := by
    rw [← hV.2.2]
    revert hNotUsed; simp; rintro h x hx rfl; exact h hx
  have hCons := validSessionIds_cons S sid ((sessPksAuth S P s.hyb.base).map Prod.fst)
    hSend hV.2.1 hFresh'
  refine ⟨validAuthKeyStores_of_fields_eq hV.1, ?_, ?_⟩
  · unfold sessPksAuth sendPostFgState; dsimp only [List.map]; rw [hSid]; exact hCons.1
  · unfold sessPksAuth sendPostFgState; dsimp only [List.map]; rw [hSid, hV.2.2]; rfl
theorem badAuthFgAnyLatched_eq_of_fields {S : Setup} (P : Primitives) (maxRo : ℕ)
    {s1 s2 : AuthFgCutoffState S} (hPrin : s1.base.principals = s2.base.principals)
    (hSpk : s1.base.spkBundles = s2.base.spkBundles) (hAdv : s1.base.advKeys = s2.base.advKeys)
    (hSess : s1.base.sessions = s2.base.sessions) (hLog : s1.advRoLog = s2.advRoLog)
    (hResp : s1.respRecs = s2.respRecs) (hLatch : s1.latchedDh1 = s2.latchedDh1) :
    badAuthFgAnyLatchedMono P maxRo s1 = badAuthFgAnyLatchedMono P maxRo s2 := by
  unfold badAuthFgAnyLatchedMono badAuthFgDh1LatchedAtMono badAuthFgDh1AtMono badAuthFgDh3AtMono
    initAuthDh1CandGuard initAuthDh1Cand lookupAuthSpkSkTake respAuthCandGuard
    respAuthDh1Cand respAuthDh3Cand respAuthCand
  simp only [hPrin, hSpk, hAdv, hSess, hLog, hResp, hLatch]
theorem latchRespEkCollSendStep_eq_of_agree {S : Setup} (P : Primitives)
    {s35 s3 y35 y3 : AuthAdvLatchedState S} {prev35 prev3 : Bool}
    (hAg0 : AuthAdvLatchedAgreeOffRo s35 s3) (hAg1 : AuthAdvLatchedAgreeOffRo y35 y3)
    (hPrev : prev35 = prev3) :
    latchRespEkCollSendStep P s35 y35 prev35 = latchRespEkCollSendStep P s3 y3 prev3 := by
  have hSess0 : s35.hyb.base.sessions = s3.hyb.base.sessions := by rw [hAg0]; rfl
  have hResp0 : s35.adv.respRecs = s3.adv.respRecs := by rw [hAg0]; rfl
  have hSess1 : y35.hyb.base.sessions = y3.hyb.base.sessions := by rw [hAg1]; rfl
  unfold latchRespEkCollSendStep; rw [hPrev, hSess0, hResp0, hSess1]
theorem RelProbUpToBad.of_support_prod {α : Type} {R : α → α → Prop} {bad : α → Bool}
    (m5 m6 : ProbComp α) (h : ∀ x5 ∈ support m5, ∀ x6 ∈ support m6, R x5 x6) :
    RelProbUpToBad R bad m5 m6 := by
  refine ⟨fun w5 w6 _ _ hle => ?_, fun w6 w5 _ hle => ?_⟩
  · refine _root_.SignalPqxdh.Security.le_probExpect_const_of_support m6 w6
      (probExpect m5 w5) (fun x6 hx6 => ?_)
    exact _root_.SignalPqxdh.Security.probExpect_const_le_of_support m5 w5 (w6 x6)
      (fun x5 hx5 => hle x5 x6 (h x5 hx5 x6 hx6))
  · refine _root_.SignalPqxdh.Security.le_probExpect_const_of_support m5 w5
      (probExpect m6 w6) (fun x5 hx5 => ?_)
    exact _root_.SignalPqxdh.Security.probExpect_const_le_of_support m6 w6 (w5 x5)
      (fun x6 hx6 => hle x5 x6 (h x5 hx5 x6 hx6))
private theorem exists_spkBundle_of_checkBundleSpkHonIdeal (P : Primitives)
    (principals : List (Nat × PrincipalEntry)) (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (bundle : PreKeyBundleInput)
    (h : checkBundleSpkHonIdeal P principals spkBundles bundle = true) : ∃ k_s j_s b_s,
      ((k_s, j_s), b_s) ∈ spkBundles ∧ P.pow8 bundle.spkB = P.pow8 b_s.spkPk := by
  unfold checkBundleSpkHonIdeal at h
  cases hF : findHonestPrincipal P principals bundle.ikB with
  | none => rw [hF] at h; nomatch h
  | some kp =>
    rcases kp with ⟨k, pEntry⟩; rw [hF] at h; dsimp only at h
    rcases List.any_eq_true.mp h with ⟨⟨⟨u, j⟩, b⟩, hMem, hPred⟩
    rcases Bool.and_eq_true_iff.mp hPred with ⟨_, hOr⟩; refine ⟨u, j, b, hMem, ?_⟩
    rcases Bool.or_eq_true_iff.mp hOr with hCorr | hEq
    · exact (beq_iff_eq.mp (Bool.and_eq_true_iff.mp hCorr).2).symm
    · rw [beq_iff_eq.mp hEq]
private theorem exists_pqspkBundle_of_checkBundleProvenanceExact_thd (P : Primitives)
    (principals : List (Nat × PrincipalEntry)) (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry)) (bundle : PreKeyBundleInput)
    (h : (checkBundleProvenanceExact P principals spkBundles opkEntries bundle).2.2 = true) :
    ∃ k_s j_s k_s_Entry b_s, (k_s, k_s_Entry) ∈ principals ∧ ((k_s, j_s), b_s) ∈ spkBundles ∧
      P.pow8 bundle.ikB = P.pow8 k_s_Entry.ikAPk ∧ bundle.pqspkB = b_s.pqspkPk := by
  unfold checkBundleProvenanceExact findHonestPrincipal at h
  cases hF : principals.find? (fun (_, e) => P.pow8 bundle.ikB == P.pow8 e.ikAPk) with
  | none => rw [hF] at h; nomatch h
  | some kp =>
    rcases kp with ⟨k, pEntry⟩; rw [hF] at h; dsimp only at h
    have hkMem : (k, pEntry) ∈ principals := List.mem_of_find?_eq_some hF
    have hPowIk : P.pow8 bundle.ikB = P.pow8 pEntry.ikAPk := beq_iff_eq.mp (List.find?_some
        (p := fun (x : Nat × PrincipalEntry) => P.pow8 bundle.ikB == P.pow8 x.2.ikAPk) hF)
    rcases List.any_eq_true.mp h with ⟨⟨⟨u, j⟩, b⟩, hbMem, hPred⟩
    rcases Bool.and_eq_true_iff.mp hPred with ⟨huk, hPq⟩; have huEq : u = k := beq_iff_eq.mp huk
    subst huEq; exact ⟨u, j, pEntry, b, hkMem, hbMem, hPowIk, (beq_iff_eq.mp hPq).symm⟩
def evalAuthHybridSendDrKey (stage : AuthHybridStage) (useRo : Bool) (P : Primitives)
    (roCache : List (Bytes × DRKey)) (isIdealSend : Bool) (secrets : Bytes) :
    ProbComp (DRKey × List (Bytes × DRKey)) :=
  if isIdealSend && stage.idealDrKey then do
    let dk ← sampleDRKey96
    pure (dk, roCache)
  else
    evalHkdfOrRo useRo P roCache secrets
def buildSendIdealSession {S : Setup} (P : Primitives)
    (sid : SessionId S) (bundle : PreKeyBundleInput) (uEntry : PrincipalEntry)
    (ekASk ephASk kemCt msgPlain : Bytes) (drKey : DRKey) (rk1 ck1_0 ck1_1 : Bytes)
    (spqrSalt? : Option Bytes) (pqRatchetMsg : Bytes) : IdealAuthSession S :=
  let ekAPk := P.x25519Base ekASk; let ephAPk := P.x25519Base ephASk
  let mkSeed := P.chainKdfSeed ck1_0; let deriveMessageKeys := P.deriveMsgKeys mkSeed spqrSalt?
  let ad := firstMsgAD uEntry.ikAPk bundle.ikB ephAPk pqRatchetMsg
  let aeadCt := P.aeadEnc deriveMessageKeys ad msgPlain
  { sid := sid, ikAPk := uEntry.ikAPk, peerIkPk := bundle.ikB, peerSpkPk := bundle.spkB,
    peerOpkPk? := bundle.opkB?.map Prod.snd, ekAPk := ekAPk, peerPqspkPk := bundle.pqspkB,
    kemCt := kemCt, ephAPk := ephAPk, spqrSalt? := spqrSalt?, pqRatchetMsg := pqRatchetMsg,
    ad := ad, aeadCt := aeadCt, msgPlain := msgPlain, drKey := drKey, rk1 := rk1,
    ck1_0 := ck1_0, mkSeed := mkSeed, ck1_1 := ck1_1, deriveMessageKeys := deriveMessageKeys }
def finishAuthHybridSendPure {S : Setup} (P : Primitives)
    (sid : SessionId S) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (uEntry : PrincipalEntry) (ekASk ephASk spqrCoins ss kemCt : Bytes)
    (hst : AuthHybridState S) (drKey : DRKey) (roCache' : List (Bytes × DRKey)) (rk1 ck1_0 : Bytes)
    (rootRoCache' : List ((Bytes × Bytes) × (Bytes × Bytes))) : AuthResponse × AuthHybridState S :=
  let st := hst.base; let peerPrincipal? := findHonestPrincipal P st.principals bundle.ikB
  let isFreshPeer : Bool := match peerPrincipal? with | some (_, p) => !p.corrupted | none => false
  let msgPlain := if isFreshPeer then (if st.secb then m1 else m0) else m0
  let ekAPk := P.x25519Base ekASk; let ephAPk := P.x25519Base ephASk
  let (_, _, pqspkHon) :=
    checkBundleProvenanceExact P st.principals st.spkBundles st.opkEntries bundle
  let spkHonIdeal := checkBundleSpkHonIdeal P st.principals st.spkBundles bundle
  let isIdealSend : Bool := isFreshPeer || (peerPrincipal?.isSome && spkHonIdeal && pqspkHon)
  let (mkSeed, ck1_1) := (P.chainKdfSeed ck1_0, P.chainKdfNext ck1_0)
  match P.spqrInitSend drKey.pqrKey spqrCoins with
  | none => (.noneResp, hst)
  | some (_pqrStA, spqrSalt?, pqRatchetMsg) =>
    let deriveMessageKeys := P.deriveMsgKeys mkSeed spqrSalt?
    let ad := firstMsgAD uEntry.ikAPk bundle.ikB ephAPk pqRatchetMsg
    let aeadCt := P.aeadEnc deriveMessageKeys ad msgPlain
    let hdr : HandshakeHdr :=
      { ikAPk := uEntry.ikAPk, ekAPk := ekAPk, spkId := bundle.spkId,
        opkId? := bundle.opkB?.map Prod.fst, pqspkId := bundle.pqspkId, kemCt := kemCt }
    let wireMsg : PreKeyMsg :=
      { hdr := hdr, ephAPk := ephAPk, pqRatchetMsg := pqRatchetMsg, aeadCt := aeadCt }
    let sessEntry := mkSendSessEntry P st sid bundle m0 m1 isFreshPeer ekASk ephASk
    let (sentOPK', sentNoOPK') :=
      match peerPrincipal?, bundle.opkB? with
      | some (_, pEntry), some (_, opkPk) =>
        ({ a0 := uEntry.ikAPk, b0 := pEntry.ikAPk, sb := bundle.spkB, ob := opkPk, a1 := ekAPk,
           pk1 := bundle.pqspkB, ct := kemCt, m := msgPlain, matched := false } :: st.sentOPKEvents,
         st.sentNoOPKEvents)
      | some (_, pEntry), none =>
        (st.sentOPKEvents,
         { a0 := uEntry.ikAPk, b0 := pEntry.ikAPk, sb := bundle.spkB, a1 := ekAPk,
           pk1 := bundle.pqspkB, ct := kemCt, m := msgPlain, matched := false } ::
           st.sentNoOPKEvents)
      | none, _ => (st.sentOPKEvents, st.sentNoOPKEvents)
    let initRec : _root_.SignalPqxdh.Security.InitKemRecord S :=
      { sid := sid, pqspkPk := bundle.pqspkB, kemCt := kemCt, kemSs := ss }
    let idealSessions' := if isIdealSend then buildSendIdealSession P sid bundle uEntry ekASk
      ephASk kemCt msgPlain drKey rk1 ck1_0 ck1_1 spqrSalt? pqRatchetMsg :: hst.idealSessions
      else hst.idealSessions
    let hst' : AuthHybridState S :=
      { hst with
        base := { st with
          sessions := sessEntry :: st.sessions, usedSendSessions := sid :: st.usedSendSessions,
          sentOPKEvents := sentOPK', sentNoOPKEvents := sentNoOPK',
          roCache := roCache', rootRoCache := rootRoCache' },
        initKemRecs := initRec :: hst.initKemRecs, idealSessions := idealSessions' }
    (if peerPrincipal?.isSome then .sendFreshResp wireMsg
     else .sendUnfreshResp drKey rk1 ck1_1 wireMsg, hst')
def finishAuthHybridSendPost {S : Setup} (useRo : Bool) (P : Primitives) (sid : SessionId S)
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes) (uEntry : PrincipalEntry)
    (ekASk ephASk spqrCoins ss kemCt : Bytes) (s : AuthAdvLatchedState S) (drKey : DRKey)
    (roCache' : List (Bytes × DRKey)) : ProbComp (AuthResponse × AuthAdvLatchedState S) := do
  let ((rk1, ck1_0), rootRoCache') ←
    evalRootKdfOrRo useRo P s.hyb.base.rootRoCache drKey.rootKey (P.x25519 ephASk bundle.spkB)
  let (resp, h') := finishAuthHybridSendPure P sid bundle m0 m1 uEntry
    ekASk ephASk spqrCoins ss kemCt s.hyb drKey roCache' rk1 ck1_0 rootRoCache'
  return (resp, withLatchedHyb s h')
def runAuthHybridSendLatched (stage : AuthHybridStage) (S : Setup) (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (s : AuthAdvLatchedState S) : ProbComp (AuthResponse × AuthAdvLatchedState S) :=
  ((runAuthHybridSendKosk stage true S P sid u bundle m0 m1).run s.hyb) >>=
    fun p => pure (p.1, withLatchedHyb s p.2)
@[simp] theorem withLatchedHyb_self {S : Setup} (s : AuthAdvLatchedState S) :
    withLatchedHyb s s.hyb = s := rfl
theorem runAuthHybridSendLatched_eq {S : Setup} (stage : AuthHybridStage)
    (P : Primitives) (sid : SessionId S) (u : Fin S.N_id)
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes) (s : AuthAdvLatchedState S)
    (hAead : stage.idealFreshAead = false := by rfl) (hRk : stage.idealRk = false := by rfl)
    (hCk : stage.idealCk = false := by rfl) (hMk : stage.idealMsgKeys = false := by rfl) :
    runAuthHybridSendLatched stage S P sid u bundle m0 m1 s = (do
      let st := s.hyb.base
      if m0.length != m1.length then return (.noneResp, s)
      if st.usedSendSessions.contains sid then return (.noneResp, s)
      let some (_, uEntry) := st.principals.find? (fun (idx, _) => idx == u.val)
        | return (.noneResp, s)
      let peerPrincipal? := findHonestPrincipal P st.principals bundle.ikB
      let isFreshPeer : Bool :=
        match peerPrincipal? with | some (_, pEntry) => !pEntry.corrupted | none => false
      if !isFreshPeer && m0 != m1 then return (.noneResp, s)
      if !koskBundleOk P st.principals st.spkBundles st.opkEntries st.advKeys bundle then
        return (.noneResp, s)
      let ekASk ← sampleScalar32; let kemCoins ← sampleCoins32
      let ephASk ← sampleScalar32; let spqrCoins ← sampleCoins32
      let sigPkB := resolveSigPk P st.principals bundle.ikB
      if !(P.sigVerify sigPkB (encodeEC bundle.spkB) bundle.spkSig &&
           P.sigVerify sigPkB (encodeKEM bundle.pqspkB) bundle.pqspkSig) then
        return (.noneResp, s)
      let some (ss, kemCt) := P.kemEncaps bundle.pqspkB kemCoins | return (.noneResp, s)
      let (_, _, pqspkHon) :=
        checkBundleProvenanceExact P st.principals st.spkBundles st.opkEntries bundle
      let spkHonIdeal := checkBundleSpkHonIdeal P st.principals st.spkBundles bundle
      let isIdealSend : Bool := isFreshPeer || (peerPrincipal?.isSome && spkHonIdeal && pqspkHon)
      let dh1 := P.x25519 uEntry.secIKA0 bundle.spkB; let dh2 := P.x25519 ekASk bundle.ikB
      let dh3 := P.x25519 ekASk bundle.spkB
      let dh4? := bundle.opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk)
      let secrets := buildSecrets dh1 dh2 dh3 dh4? ss
      let (drKey, roCache') ←
        evalAuthHybridSendDrKey stage true P st.roCache isIdealSend secrets
      finishAuthHybridSendPost true P sid bundle m0 m1 uEntry
        ekASk ephASk spqrCoins ss kemCt s drKey roCache') := by
  unfold runAuthHybridSendLatched runAuthHybridSendKosk evalAuthHybridSendDrKey
    finishAuthHybridSendPost finishAuthHybridSendPure buildSendIdealSession mkSendSessEntry
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases h1 : (m0.length != m1.length) = true
  · simp only [h1, ↓reduceIte, StateT.run_pure, pure_bind, withLatchedHyb_self]
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : (s.hyb.base.usedSendSessions.contains sid) = true
    · simp only [h2, ↓reduceIte, StateT.run_pure, pure_bind, withLatchedHyb_self]
    · simp only [h2, Bool.false_eq_true, ↓reduceIte]
      cases s.hyb.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none => dsimp only; simp only [StateT.run_pure, pure_bind, withLatchedHyb_self]
      | some up =>
        rcases up with ⟨_, uEntry⟩; dsimp only; rw [hAead, hRk, hCk, hMk]
        cases hFp : findHonestPrincipal P s.hyb.base.principals bundle.ikB with
        | none =>
          dsimp only; simp only [Bool.not_false, Bool.true_and, Bool.false_or, Option.isSome,
            Bool.false_and, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
          by_cases h3 : (m0 != m1) = true
          · simp only [h3, ↓reduceIte, StateT.run_pure, pure_bind, withLatchedHyb_self]
          · simp only [h3, Bool.false_eq_true, ↓reduceIte]
            by_cases h4 : (!koskBundleOk P s.hyb.base.principals s.hyb.base.spkBundles
                             s.hyb.base.opkEntries s.hyb.base.advKeys bundle) = true
            · simp only [h4, ↓reduceIte, StateT.run_pure, pure_bind, withLatchedHyb_self]
            · simp only [h4, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
                StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind]
              congr 1; funext ekASk; congr 1; funext kemCoins
              congr 1; funext ephASk; congr 1; funext spqrCoins
              by_cases h5 : (!(P.sigVerify (resolveSigPk P s.hyb.base.principals bundle.ikB)
                                (encodeEC bundle.spkB) bundle.spkSig &&
                               P.sigVerify (resolveSigPk P s.hyb.base.principals bundle.ikB)
                                (encodeKEM bundle.pqspkB) bundle.pqspkSig)) = true
              · simp only [h5, ↓reduceIte, StateT.run_pure, pure_bind, withLatchedHyb_self]
              · simp only [h5, Bool.false_eq_true, ↓reduceIte]
                cases P.kemEncaps bundle.pqspkB kemCoins with
                | none => dsimp only; simp only [StateT.run_pure, pure_bind, withLatchedHyb_self]
                | some sc =>
                  rcases sc with ⟨ss, kemCt⟩; dsimp only
                  simp only [
                    StateT.run_bind, StateT.run_monadLift,
                    monadLift_self, bind_assoc, pure_bind]
                  congr 1; funext ⟨drKey, roCache'⟩; congr 1; funext ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
                  cases P.spqrInitSend drKey.pqrKey spqrCoins with
                  | none => dsimp only; simp only [StateT.run_pure, pure_bind, withLatchedHyb_self]
                  | some pqr =>
                    rcases pqr with ⟨_pqrStA, spqrSalt?, pqRatchetMsg⟩; dsimp only
                    simp only [
                      StateT.run_bind, StateT.run_set,
                      StateT.run_pure, pure_bind]
        | some pp =>
          rcases pp with ⟨_, pEntry⟩; dsimp only
          by_cases hcorr : pEntry.corrupted = true
          · simp only [hcorr, Option.isSome, Bool.not_true, Bool.not_false, Bool.true_and,
              Bool.false_or, Bool.false_eq_true, ↓reduceIte]
            by_cases h3 : (m0 != m1) = true
            · simp only [h3, ↓reduceIte, StateT.run_pure, pure_bind, withLatchedHyb_self]
            · simp only [h3, Bool.false_eq_true, ↓reduceIte]
              by_cases h4 : (!koskBundleOk P s.hyb.base.principals s.hyb.base.spkBundles
                               s.hyb.base.opkEntries s.hyb.base.advKeys bundle) = true
              · simp only [h4, ↓reduceIte, StateT.run_pure, pure_bind, withLatchedHyb_self]
              · simp only [h4, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
                  StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind]
                congr 1; funext ekASk; congr 1; funext kemCoins
                congr 1; funext ephASk; congr 1; funext spqrCoins
                by_cases h5 : (!(P.sigVerify (resolveSigPk P s.hyb.base.principals bundle.ikB)
                                  (encodeEC bundle.spkB) bundle.spkSig &&
                                 P.sigVerify (resolveSigPk P s.hyb.base.principals bundle.ikB)
                                  (encodeKEM bundle.pqspkB) bundle.pqspkSig)) = true
                · simp only [h5, ↓reduceIte, StateT.run_pure, pure_bind, withLatchedHyb_self]
                · simp only [h5, Bool.false_eq_true, ↓reduceIte]
                  cases P.kemEncaps bundle.pqspkB kemCoins with
                  | none => dsimp only; simp only [StateT.run_pure, pure_bind, withLatchedHyb_self]
                  | some sc =>
                    rcases sc with ⟨ss, kemCt⟩; dsimp only
                    by_cases hId :
                        ((checkBundleSpkHonIdeal P s.hyb.base.principals s.hyb.base.spkBundles
                            bundle &&
                          (checkBundleProvenanceExact P s.hyb.base.principals s.hyb.base.spkBundles
                            s.hyb.base.opkEntries bundle).2.2) &&
                         stage.idealDrKey) = true
                    · simp only [hId, 
                        Bool.and_false, Bool.false_eq_true, ↓reduceIte,
                        StateT.run_bind, StateT.run_monadLift, monadLift_self, 
                        bind_assoc, pure_bind]
                      congr 1; funext dk; congr 1; funext ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
                      cases P.spqrInitSend dk.pqrKey spqrCoins with
                      | none =>
                        dsimp only; simp only [StateT.run_pure, pure_bind, withLatchedHyb_self]
                      | some pqr =>
                        rcases pqr with ⟨_pqrStA, spqrSalt?, pqRatchetMsg⟩; dsimp only
                        simp only [
                          
                          StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]; rfl
                    · simp only [hId, 
                        Bool.and_false, Bool.false_eq_true, ↓reduceIte,
                        StateT.run_bind, StateT.run_monadLift, monadLift_self, 
                        bind_assoc, pure_bind]
                      congr 1; funext ⟨drKey, roCache'⟩
                      congr 1; funext ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
                      cases P.spqrInitSend drKey.pqrKey spqrCoins with
                      | none =>
                        dsimp only; simp only [StateT.run_pure, pure_bind, withLatchedHyb_self]
                      | some pqr =>
                        rcases pqr with ⟨_pqrStA, spqrSalt?, pqRatchetMsg⟩; dsimp only
                        simp only [
                          
                          StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]; rfl
          · rw [Bool.not_eq_true] at hcorr
            simp only [hcorr, Option.isSome, Bool.not_false, Bool.not_true, Bool.false_and,
              Bool.true_or, Bool.true_and, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
            by_cases h4 : (!koskBundleOk P s.hyb.base.principals s.hyb.base.spkBundles
                             s.hyb.base.opkEntries s.hyb.base.advKeys bundle) = true
            · simp only [h4, ↓reduceIte, StateT.run_pure, pure_bind, withLatchedHyb_self]
            · simp only [h4, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
                StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind]
              congr 1; funext ekASk; congr 1; funext kemCoins
              congr 1; funext ephASk; congr 1; funext spqrCoins
              by_cases h5 : (!(P.sigVerify (resolveSigPk P s.hyb.base.principals bundle.ikB)
                                (encodeEC bundle.spkB) bundle.spkSig &&
                               P.sigVerify (resolveSigPk P s.hyb.base.principals bundle.ikB)
                                (encodeKEM bundle.pqspkB) bundle.pqspkSig)) = true
              · simp only [h5, ↓reduceIte, StateT.run_pure, pure_bind, withLatchedHyb_self]
              · simp only [h5, Bool.false_eq_true, ↓reduceIte]
                cases P.kemEncaps bundle.pqspkB kemCoins with
                | none => dsimp only; simp only [StateT.run_pure, pure_bind, withLatchedHyb_self]
                | some sc =>
                  rcases sc with ⟨ss, kemCt⟩; dsimp only
                  by_cases hId : stage.idealDrKey = true
                  · simp only [hId, 
                      ↓reduceIte,
                      StateT.run_bind, StateT.run_monadLift, monadLift_self, 
                      bind_assoc, pure_bind]
                    congr 1; funext dk; congr 1; funext ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
                    cases P.spqrInitSend dk.pqrKey spqrCoins with
                    | none =>
                      dsimp only; simp only [StateT.run_pure, pure_bind, withLatchedHyb_self]
                    | some pqr =>
                      rcases pqr with ⟨_pqrStA, spqrSalt?, pqRatchetMsg⟩; dsimp only
                      simp only [
                        
                        StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]; rfl
                  · simp only [hId, 
                      Bool.false_eq_true, ↓reduceIte,
                      StateT.run_bind, StateT.run_monadLift, monadLift_self, 
                      bind_assoc, pure_bind]
                    congr 1; funext ⟨drKey, roCache'⟩; congr 1; funext ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
                    cases P.spqrInitSend drKey.pqrKey spqrCoins with
                    | none =>
                      dsimp only; simp only [StateT.run_pure, pure_bind, withLatchedHyb_self]
                    | some pqr =>
                      rcases pqr with ⟨_pqrStA, spqrSalt?, pqRatchetMsg⟩; dsimp only
                      simp only [
                        
                        StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]; rfl
private theorem exists_spkBundle_of_checkBundleProvenanceExact_fst (P : Primitives)
    (principals : List (Nat × PrincipalEntry)) (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry)) (bundle : PreKeyBundleInput)
    (h : (checkBundleProvenanceExact P principals spkBundles opkEntries bundle).1 = true) :
    ∃ k_s j_s b_s, ((k_s, j_s), b_s) ∈ spkBundles ∧ P.pow8 bundle.spkB = P.pow8 b_s.spkPk := by
  unfold checkBundleProvenanceExact findHonestPrincipal at h
  cases hF : principals.find? (fun (_, e) => P.pow8 bundle.ikB == P.pow8 e.ikAPk) with
  | none => rw [hF] at h; nomatch h
  | some kp =>
    rcases kp with ⟨k, pEntry⟩; rw [hF] at h; dsimp only at h
    rcases List.any_eq_true.mp h with ⟨⟨⟨u, j⟩, b⟩, hbMem, hPred⟩
    rcases Bool.and_eq_true_iff.mp hPred with ⟨_, hSpk⟩
    exact ⟨u, j, b, hbMem, by rw [beq_iff_eq.mp hSpk]⟩
private theorem authRoCacheCoupled_cons_both {S : Setup} (P : Primitives)
    {a35 a3 : AuthAdvLatchedState S} (hRc : AuthRoCacheCoupled P a35 a3)
    (secrets : Bytes) (dk : DRKey)
    (hF3 : a3.adv.hyb.base.roCache.find? (fun (s, _) => s == secrets) = none)
    (hSess : ∃ s_old ∈ a3.hyb.base.sessions, s_old.sid ∈ a3.hyb.base.usedSendSessions ∧
      IsSendSessionId S s_old.sid ∧ extractDh3 secrets = P.x25519 s_old.ekASk s_old.peerSpkPk) :
    AuthRoCacheCoupled P (withAuthAdvLatchedRoCache ((secrets, dk) :: a35.adv.hyb.base.roCache) a3)
      (withAuthAdvLatchedRoCache ((secrets, dk) :: a3.adv.hyb.base.roCache) a3) := by
  rcases hRc with ⟨hSub35, hIdealIn3, hOrigin3, hDiffIdeal⟩; refine ⟨?_, ?_, ?_, ?_⟩
  · intro sec' p' hF35'
    dsimp only [withAuthAdvLatchedRoCache, withAuthAdvRoCache,
      withAuthHybRoCache, withAuthBaseRoCache, List.find?_cons] at hF35' ⊢
    cases hBeq : (secrets == sec')
    · rw [hBeq] at hF35'; exact hSub35 sec' p' hF35'
    · rw [hBeq] at hF35'; exact hF35'
  · intro s hs
    rcases hIdealIn3 s hs with ⟨sessEntry, u, uEntry, kemCoins, ss_s, initRec, hVi, hVh, hFindS⟩
    refine ⟨sessEntry, u, uEntry, kemCoins, ss_s, initRec, hVi, hVh, ?_⟩
    dsimp only [withAuthAdvLatchedRoCache, withAuthAdvRoCache,
      withAuthHybRoCache, withAuthBaseRoCache, List.find?_cons]
    have hNe : (secrets == idealSessionSecrets P uEntry sessEntry.ekASk ss_s s) = false := by
      cases hBeq : (secrets == idealSessionSecrets P uEntry sessEntry.ekASk ss_s s)
      · rfl
      · dsimp only at hFindS
        rw [← beq_iff_eq.mp hBeq] at hFindS; rw [hF3] at hFindS; nomatch hFindS
    rw [hNe]; exact hFindS
  · intro sec' p' hF3'
    dsimp only [withAuthAdvLatchedRoCache, withAuthAdvRoCache,
      withAuthHybRoCache, withAuthBaseRoCache, List.find?_cons] at hF3' ⊢
    cases hBeq : (secrets == sec')
    · rw [hBeq] at hF3'; exact hOrigin3 sec' p' hF3'
    · rw [hBeq] at hF3'
      injection hF3' with hp'; subst hp'
      have hEq : secrets = sec' := beq_iff_eq.mp hBeq; subst hEq; exact ⟨rfl, Or.inr (Or.inl hSess)⟩
  · intro sec' p' hF35' hF3'
    dsimp only [withAuthAdvLatchedRoCache, withAuthAdvRoCache,
      withAuthHybRoCache, withAuthBaseRoCache, List.find?_cons] at hF35' hF3'
    cases hBeq : (secrets == sec')
    · rw [hBeq] at hF35' hF3'; exact hDiffIdeal sec' p' hF35' hF3'
    · rw [hBeq] at hF35'; nomatch hF35'
private theorem authRoCacheCoupled_finishSend_ideal {S : Setup} (P : Primitives)
    {s35 s3 y3 : AuthAdvLatchedState S} (hRc : AuthRoCacheCoupled P s35 s3)
    {secrets : Bytes} {s_new : IdealAuthSession S}
    {sessEntry : AuthInitiatorEntry S} {u : Nat} {uEntry : PrincipalEntry}
    {kemCoins ss : Bytes} {initRec : _root_.SignalPqxdh.Security.InitKemRecord S}
    (hF35 : s35.adv.hyb.base.roCache.find? (fun (s, _) => s == secrets) = none)
    (hF3 : s3.adv.hyb.base.roCache.find? (fun (s, _) => s == secrets) = none)
    (hSub : AuthHybridTraceSub s3.hyb y3.hyb)
    (hRo3 : y3.adv.hyb.base.roCache = (secrets, s_new.drKey) :: s3.adv.hyb.base.roCache)
    (hId3 : y3.hyb.idealSessions = s_new :: s3.hyb.idealSessions)
    (hLogEq : y3.adv.advRoLog = s3.adv.advRoLog) (hRespEq : y3.adv.respRecs = s3.adv.respRecs)
    (hUsedSub : ∀ x ∈ s3.hyb.base.usedSendSessions, x ∈ y3.hyb.base.usedSendSessions)
    (hViNew : ValidIdealAuthSession S P y3.hyb s_new sessEntry u uEntry kemCoins ss initRec)
    (hVhNew : ValidIdealSessionHonesty S P y3.hyb s_new sessEntry)
    (hSecNew : secrets = idealSessionSecrets P uEntry sessEntry.ekASk ss s_new)
    (hSessNew : sessEntry ∈ y3.hyb.base.sessions ∧ sessEntry.sid ∈ y3.hyb.base.usedSendSessions ∧
      IsSendSessionId S sessEntry.sid ∧
      extractDh3 secrets = P.x25519 sessEntry.ekASk sessEntry.peerSpkPk) :
    AuthRoCacheCoupled P (withAuthAdvLatchedRoCache s35.adv.hyb.base.roCache y3) y3 := by
  rcases hRc with ⟨hSub35, hIdealIn3, hOrigin3, hDiffIdeal⟩
  have h35Ro :
      (withAuthAdvLatchedRoCache s35.adv.hyb.base.roCache y3).adv.hyb.base.roCache =
        s35.adv.hyb.base.roCache := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro sec' p' hF35'
    rw [h35Ro] at hF35'; rw [hRo3, List.find?_cons]; dsimp only
    have hNe : (secrets == sec') = false := by
      cases hBeq : (secrets == sec')
      · rfl
      · rw [← beq_iff_eq.mp hBeq, hF35] at hF35'; nomatch hF35'
    rw [hNe]; exact hSub35 sec' p' hF35'
  · intro s hs
    rw [hId3] at hs; rcases List.mem_cons.mp hs with rfl | hsOld
    · refine ⟨sessEntry, u, uEntry, kemCoins, ss, initRec, hViNew, hVhNew, ?_⟩
      dsimp only; rw [hRo3, ← hSecNew, List.find?_cons]; dsimp only; rw [beq_self_eq_true]
    · rcases hIdealIn3 s hsOld with ⟨se1, u1, ue1, kc1, ss1, ir1, hVi1, hVh1, hFind1⟩
      rcases validIdealAuthSession_of_traceSub P hSub hVi1 with ⟨ue2, hSecEq, _, hVi2⟩
      have hVh2 := validIdealSessionHonesty_of_traceSub P hSub hVh1
      have hIdealSecEq : idealSessionSecrets P ue2 se1.ekASk ss1 s =
            idealSessionSecrets P ue1 se1.ekASk ss1 s := by
        unfold idealSessionSecrets; rw [hSecEq]
      refine ⟨se1, u1, ue2, kc1, ss1, ir1, hVi2, hVh2, ?_⟩
      dsimp only at hFind1 ⊢; rw [hIdealSecEq, hRo3, List.find?_cons]; dsimp only
      have hNe : (secrets == idealSessionSecrets P ue1 se1.ekASk ss1 s) = false := by
        cases hBeq : (secrets == idealSessionSecrets P ue1 se1.ekASk ss1 s)
        · rfl
        · rw [← beq_iff_eq.mp hBeq, hF3] at hFind1; nomatch hFind1
      rw [hNe]; exact hFind1
  · intro sec' p' hF3'
    rw [hRo3, List.find?_cons] at hF3'; dsimp only at hF3'
    cases hBeq : (secrets == sec')
    · rw [hBeq] at hF3'; rcases hOrigin3 sec' p' hF3' with ⟨hp1, hInLog | hSess | hResp⟩
      · exact ⟨hp1, Or.inl (hLogEq ▸ hInLog)⟩
      · rcases hSess with ⟨s_old, hsOld, hUsed, hSendOld, hDh3⟩
        exact ⟨hp1, Or.inr (Or.inl ⟨s_old, hSub.base_sub.sessions_sub.subset hsOld,
           hUsedSub _ hUsed, hSendOld, hDh3⟩)⟩
      · rcases hResp with ⟨k_r, j_r, bEntry_r, r_rec, hbMem, hrMem, hrKey, hrLen, hDh3⟩
        exact ⟨hp1, Or.inr (Or.inr ⟨k_r, j_r, bEntry_r, r_rec,
           hSub.base_sub.spkBundles_sub.subset hbMem, hRespEq ▸ hrMem, hrKey, hrLen, hDh3⟩)⟩
    · rw [hBeq] at hF3'
      injection hF3' with hp'; subst hp'
      have hEq : secrets = sec' := beq_iff_eq.mp hBeq; subst hEq; exact ⟨rfl, Or.inr (Or.inl
        ⟨sessEntry, hSessNew.1, hSessNew.2.1, hSessNew.2.2.1, hSessNew.2.2.2⟩)⟩
  · intro sec' p' hF35' hF3'
    rw [h35Ro] at hF35'; rw [hRo3, List.find?_cons] at hF3'; dsimp only at hF3'
    cases hBeq : (secrets == sec')
    · rw [hBeq] at hF3'
      rcases hDiffIdeal sec' p' hF35' hF3' with
        ⟨s, hs, se1, u1, ue1, kc1, ss1, ir1, hVi1, hVh1, hSec, hpEq⟩
      rcases validIdealAuthSession_of_traceSub P hSub hVi1 with ⟨ue2, hSecEq, _, hVi2⟩
      have hVh2 := validIdealSessionHonesty_of_traceSub P hSub hVh1
      have hIdealSecEq : idealSessionSecrets P ue2 se1.ekASk ss1 s =
            idealSessionSecrets P ue1 se1.ekASk ss1 s := by
        unfold idealSessionSecrets; rw [hSecEq]
      rw [← hIdealSecEq] at hSec
      exact ⟨s, hId3 ▸ List.mem_cons_of_mem _ hs, se1, u1, ue2, kc1, ss1, ir1,
        hVi2, hVh2, hSec, hpEq⟩
    · rw [hBeq] at hF3'
      injection hF3' with hp'; subst hp'
      have hEq : secrets = sec' := beq_iff_eq.mp hBeq; subst hEq
      exact ⟨s_new, hId3 ▸ List.mem_cons_self, sessEntry, u, uEntry, kemCoins, ss, initRec,
        hViNew, hVhNew, hSecNew, rfl⟩
theorem finishAuthHybridSendPure_agree {S : Setup} (P : Primitives)
    (sid : SessionId S) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (uEntry : PrincipalEntry) (ekASk ephASk spqrCoins ss kemCt : Bytes)
    {s35 s3 : AuthAdvLatchedState S} (hAg : AuthAdvLatchedAgreeOffRo s35 s3)
    (drKey : DRKey) (roCache35' roCache3' : List (Bytes × DRKey)) (rk1 ck1_0 : Bytes)
    (rootRoCache' : List ((Bytes × Bytes) × (Bytes × Bytes)))
    {pqrStA : Bytes} {spqrSalt? : Option Bytes} {pqRatchetMsg : Bytes}
    (hSpqr : P.spqrInitSend drKey.pqrKey spqrCoins = some (pqrStA, spqrSalt?, pqRatchetMsg)) :
    let r35 := finishAuthHybridSendPure P sid bundle m0 m1 uEntry
      ekASk ephASk spqrCoins ss kemCt s35.hyb drKey roCache35' rk1 ck1_0 rootRoCache'
    let r3 := finishAuthHybridSendPure P sid bundle m0 m1 uEntry
      ekASk ephASk spqrCoins ss kemCt s3.hyb drKey roCache3' rk1 ck1_0 rootRoCache'
    r35.1 = r3.1 ∧
    withLatchedHyb s35 r35.2 = withAuthAdvLatchedRoCache roCache35' (withLatchedHyb s3 r3.2) := by
  rw [hAg]; dsimp only [withAuthAdvLatchedRoCache, withAuthAdvRoCache,
    withAuthHybRoCache, withAuthBaseRoCache, AuthAdvLatchedState.hyb]
  unfold finishAuthHybridSendPure; rw [hSpqr]; dsimp only [withLatchedHyb]; exact ⟨rfl, rfl⟩
theorem mem_support_bind_finishAuthHybridSendPost {S : Setup} (P : Primitives)
    (hw : WellFormedPrimitivesδ P) (maxRo : ℕ)
    (sid : SessionId S) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (uEntry : PrincipalEntry) (ekASk ephASk spqrCoins ss kemCt : Bytes) (s : AuthAdvLatchedState S)
    (mDr : ProbComp (DRKey × List (Bytes × DRKey))) {y : AuthResponse × AuthAdvLatchedState S}
    (hy : y ∈ support (do
      let (drKey, roCache') ← mDr
      finishAuthHybridSendPost true P sid bundle m0 m1 uEntry
        ekASk ephASk spqrCoins ss kemCt s drKey roCache')) :
    let isFreshPeer : Bool :=
      match findHonestPrincipal P s.hyb.base.principals bundle.ikB with
      | some (_, pEntry) => !pEntry.corrupted
      | none             => false
    let sessEntry := mkSendSessEntry P s.hyb.base sid bundle m0 m1 isFreshPeer ekASk ephASk
    badAuthFgAnyLatchedMono P maxRo y.2.toFg =
      badAuthFgAnyLatchedMono P maxRo (sendPostFgState s sid sessEntry) ∧
    latchRespEkCollSendStep P s y.2 false =
      latchRespEkCollAtSend P s.adv.respRecs sessEntry.ekASk ∧
    sessEntry ∈ y.2.hyb.base.sessions := by
  unfold finishAuthHybridSendPost at hy
  simp only [support_bind, Set.mem_iUnion, mem_support_pure_iff] at hy
  rcases hy with ⟨⟨drKey, roCache'⟩, _, ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩, _, hyEq⟩
  rcases Option.isSome_iff_exists.mp (hw.spqrInitSend_some drKey.pqrKey spqrCoins) with
    ⟨⟨pqrStA, spqrSalt?, pqRatchetMsg⟩, hSpqr⟩
  unfold finishAuthHybridSendPure at hyEq; rw [hSpqr] at hyEq; dsimp only at hyEq; subst hyEq
  refine ⟨badAuthFgAnyLatched_eq_of_fields P maxRo rfl rfl rfl rfl rfl rfl rfl, ?_,
    List.mem_cons_self⟩
  simp [latchRespEkCollSendStep, withLatchedHyb, AuthAdvLatchedState.hyb]
private theorem relProbUpToBad_finishAuthHybridSendPost_of_roCoupled {S : Setup} (P : Primitives)
    (hw : WellFormedPrimitivesδ P) (maxRo : ℕ)
    (sid : SessionId S) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (uEntry : PrincipalEntry) (ekASk ephASk spqrCoins ss kemCt : Bytes)
    (s35 s3 : AuthAdvLatchedState S) (hAg : AuthAdvLatchedAgreeOffRo s35 s3)
    (drKey : DRKey) (roCache35' roCache3' : List (Bytes × DRKey))
    (hRc : ∀ rk1 ck1_0 rootRoCache' pqrStA spqrSalt? pqRatchetMsg,
      P.spqrInitSend drKey.pqrKey spqrCoins = some (pqrStA, spqrSalt?, pqRatchetMsg) →
      let y3 := withLatchedHyb s3 (finishAuthHybridSendPure P sid bundle m0 m1 uEntry
        ekASk ephASk spqrCoins ss kemCt s3.hyb drKey roCache3' rk1 ck1_0 rootRoCache').2
      AuthRoCacheCoupled P (withAuthAdvLatchedRoCache roCache35' y3) y3) :
    RelProbUpToBad
      (fun y35 y3 =>
        (y35.1 = y3.1 ∧ AuthAdvLatchedAgreeOffRo y35.2 y3.2 ∧ AuthRoCacheCoupled P y35.2 y3.2) ∨
        (isAuthG3Abort P y35.2.hyb = true ∧ isAuthG3Abort P y3.2.hyb = true))
      (fun y3 => badAuthFgAnyLatchedMono P maxRo y3.2.toFg ||
                 latchRespEkCollSendStep P s3 y3.2 false)
      (finishAuthHybridSendPost true P sid bundle m0 m1 uEntry
        ekASk ephASk spqrCoins ss kemCt s35 drKey roCache35')
      (finishAuthHybridSendPost true P sid bundle m0 m1 uEntry
        ekASk ephASk spqrCoins ss kemCt s3 drKey roCache3') := by
  have hRootEq : s35.hyb.base.rootRoCache = s3.hyb.base.rootRoCache := by rw [hAg]; rfl
  unfold finishAuthHybridSendPost; rw [hRootEq]
  refine RelProbUpToBad.bind_same _ (fun ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩ => ?_)
  dsimp only; refine RelProbUpToBad.of_pure ?_
  rcases Option.isSome_iff_exists.mp (hw.spqrInitSend_some drKey.pqrKey spqrCoins) with
    ⟨⟨pqrStA, spqrSalt?, pqRatchetMsg⟩, hSpqr⟩
  rcases finishAuthHybridSendPure_agree P sid bundle m0 m1 uEntry
    ekASk ephASk spqrCoins ss kemCt hAg drKey roCache35' roCache3' rk1 ck1_0 rootRoCache' hSpqr with
    ⟨hRespEq, hStEq⟩
  left; refine ⟨hRespEq, ?_, ?_⟩
  · rw [hStEq]; exact AuthAdvLatchedAgreeOffRo.of_withAuthAdvLatchedRoCache _ _
  · rw [hStEq]; exact hRc rk1 ck1_0 rootRoCache' pqrStA spqrSalt? pqRatchetMsg hSpqr
theorem RelProbUpToBad.bind_refl_support {α β : Type} {R : β → β → Prop} {bad : β → Bool}
    (m : ProbComp α) (f1 f2 : α → ProbComp β)
    (h : ∀ x ∈ support m, RelProbUpToBad R bad (f1 x) (f2 x)) :
    RelProbUpToBad R bad (m >>= f1) (m >>= f2) := by
  refine ⟨fun w5 w6 hw5 hw6 hle => ?_, fun w6 w5 hw6 hle => ?_⟩
  · rw [probExpect_bind, probExpect_bind]
    exact probExpect_mono_of_support m _ _ (fun x hx => (h x hx).1 w5 w6 hw5 hw6 hle)
  · rw [probExpect_bind, probExpect_bind]
    exact probExpect_mono_of_support m _ _ (fun x hx => (h x hx).2 w6 w5 hw6 hle)
private theorem slotIdx_ne_of_mem_sessions_cons {S : Setup} {P : Primitives}
    (s : AuthAdvLatchedState S) (hV : ValidAuthKeyStoresFull S P s.hyb.base)
    {sid : SessionId S} (hSend : IsSendSessionId S sid)
    (hNotUsed : s.hyb.base.usedSendSessions.contains sid = false)
    (sessEntry : AuthInitiatorEntry S) (hSid : sessEntry.sid = sid)
    {s_old : AuthInitiatorEntry S} (hsOld : s_old ∈ s.hyb.base.sessions) :
    initSessionSlotIdx s_old.sid ≠ initSessionSlotIdx sessEntry.sid := by
  have hPostV := validAuthKeyStoresFull_sendPostFgState s hV hSend hNotUsed sessEntry hSid
  have hNodup := nodup_sessions_initSessionSlotIdx hPostV; unfold sendPostFgState at hNodup
  dsimp only [List.map] at hNodup; intro hEq
  exact (List.nodup_cons.mp hNodup).1 (hEq ▸ List.mem_map_of_mem hsOld)
private theorem authHybridTraceSub_finishSend_of_spqr_some {S : Setup} (P : Primitives)
    (sid : SessionId S) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (uEntry : PrincipalEntry) (ekASk ephASk spqrCoins ss kemCt : Bytes)
    (s3 : AuthAdvLatchedState S) (drKey : DRKey) (roCache3' : List (Bytes × DRKey))
    (rk1 ck1_0 : Bytes) (rootRoCache' : List ((Bytes × Bytes) × (Bytes × Bytes)))
    {pqrStA : Bytes} {spqrSalt? : Option Bytes} {pqRatchetMsg : Bytes}
    (hSpqr : P.spqrInitSend drKey.pqrKey spqrCoins = some (pqrStA, spqrSalt?, pqRatchetMsg)) :
    AuthHybridTraceSub s3.hyb (withLatchedHyb s3 (finishAuthHybridSendPure P sid bundle m0 m1 uEntry
        ekASk ephASk spqrCoins ss kemCt s3.hyb drKey roCache3' rk1 ck1_0 rootRoCache').2).hyb := by
  unfold finishAuthHybridSendPure; rw [hSpqr]; dsimp only [withLatchedHyb, AuthAdvLatchedState.hyb]
  refine ⟨⟨List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _,
    List.Sublist.refl _, List.sublist_cons_self _ _⟩,
    List.sublist_cons_self _ _, List.Sublist.refl _, ?_⟩
  exact match (match findHonestPrincipal P s3.adv.hyb.base.principals bundle.ikB with
    | some (_, pEntry) => !pEntry.corrupted
    | none => false) ||
    ((findHonestPrincipal P s3.adv.hyb.base.principals bundle.ikB).isSome &&
      checkBundleSpkHonIdeal P s3.adv.hyb.base.principals s3.adv.hyb.base.spkBundles bundle &&
      (checkBundleProvenanceExact P s3.adv.hyb.base.principals s3.adv.hyb.base.spkBundles
        s3.adv.hyb.base.opkEntries bundle).2.2) with
  | true => List.sublist_cons_self _ _
  | false => List.Sublist.refl _
theorem relProbUpToBad_evalSendDrKey_and_finish {S : Setup} (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (maxRo : ℕ)
    (sid : SessionId S) (u : Fin S.N_id) (hSender : sessionSenderIdx sid = u.val)
    (hSend : IsSendSessionId S sid) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (uEntry : PrincipalEntry) (ekASk kemCoins ephASk spqrCoins ss kemCt : Bytes)
    (hEkLen : ekASk.length = 32) (s35 s3 : AuthAdvLatchedState S)
    (hInv : AuthG3G3_5CoupledInv P s35 s3) (huMem : (u.val, uEntry) ∈ s3.hyb.base.principals)
    (hNotUsed : s3.hyb.base.usedSendSessions.contains sid = false)
    (hKosk : koskBundleOk P s3.hyb.base.principals s3.hyb.base.spkBundles
      s3.hyb.base.opkEntries s3.hyb.base.advKeys bundle = true)
    (hKem : P.kemEncaps bundle.pqspkB kemCoins = some (ss, kemCt))
    (hAbF : isAuthG3Abort P s3.hyb = false) (hLogLen : s3.adv.advRoLog.length ≤ maxRo)
    (hRespLen : s3.adv.respRecs.length ≤ S.N_sess_tot) :
    let peerPrincipal? := findHonestPrincipal P s3.hyb.base.principals bundle.ikB
    let isFreshPeer : Bool :=
      match peerPrincipal? with
      | some (_, pEntry) => !pEntry.corrupted
      | none             => false
    let pqspkHon :=
      (checkBundleProvenanceExact P s3.hyb.base.principals s3.hyb.base.spkBundles
        s3.hyb.base.opkEntries bundle).2.2
    let spkHonIdeal := checkBundleSpkHonIdeal P s3.hyb.base.principals s3.hyb.base.spkBundles bundle
    let isIdealSend : Bool := isFreshPeer || (peerPrincipal?.isSome && spkHonIdeal && pqspkHon)
    let dh1 := P.x25519 uEntry.secIKA0 bundle.spkB
    let dh2 := P.x25519 ekASk bundle.ikB
    let dh3 := P.x25519 ekASk bundle.spkB
    let dh4? := bundle.opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk)
    let secrets := buildSecrets dh1 dh2 dh3 dh4? ss
    RelProbUpToBad
      (fun y35 y3 =>
        (y35.1 = y3.1 ∧ AuthAdvLatchedAgreeOffRo y35.2 y3.2 ∧ AuthRoCacheCoupled P y35.2 y3.2) ∨
        (isAuthG3Abort P y35.2.hyb = true ∧ isAuthG3Abort P y3.2.hyb = true))
      (fun y3 => badAuthFgAnyLatchedMono P maxRo y3.2.toFg ||
                 latchRespEkCollSendStep P s3 y3.2 false)
      (do
        let (drKey, roCache') ←
          evalAuthHybridSendDrKey .g3_5 true P s35.hyb.base.roCache isIdealSend secrets
        finishAuthHybridSendPost true P sid bundle m0 m1 uEntry
          ekASk ephASk spqrCoins ss kemCt s35 drKey roCache')
      (do
        let (drKey, roCache') ←
          evalAuthHybridSendDrKey .g3 true P s3.hyb.base.roCache isIdealSend secrets
        finishAuthHybridSendPost true P sid bundle m0 m1 uEntry
          ekASk ephASk spqrCoins ss kemCt s3 drKey roCache') := by
  have hw := hP.toWellFormedPrimitivesδ; rcases hInv with ⟨hAg, hRun, hRc⟩
  intro peerPrincipal? isFreshPeer pqspkHon spkHonIdeal isIdealSend dh1 dh2 dh3 dh4? secrets
  let sessEntry := mkSendSessEntry P s3.hyb.base sid bundle m0 m1 isFreshPeer ekASk ephASk
  have hPostV := validAuthKeyStoresFull_sendPostFgState s3 hRun.1 hSend hNotUsed sessEntry rfl
  have hDh3Sec : extractDh3 secrets = P.x25519 sessEntry.ekASk sessEntry.peerSpkPk :=
    extractDh3_buildSecrets
      (hw.x25519_len uEntry.secIKA0 bundle.spkB)
      (hw.x25519_len ekASk bundle.ikB)
      (hw.x25519_len ekASk bundle.spkB)
  by_cases hId : isIdealSend = true
  · cases hF3 : s3.adv.hyb.base.roCache.find? (fun (s, _) => s == secrets) with
    | none =>
      have hF35 : s35.adv.hyb.base.roCache.find? (fun (s, _) => s == secrets) = none := by
        cases hF : s35.adv.hyb.base.roCache.find? (fun (s, _) => s == secrets) with
        | none => rfl
        | some p => have hSome := hRc.1 secrets p hF; rw [hF3] at hSome; nomatch hSome
      have hEval35 : evalAuthHybridSendDrKey .g3_5 true P s35.hyb.base.roCache isIdealSend secrets =
            (do let dk ← sampleDRKey96; pure (dk, s35.hyb.base.roCache)) := by
        unfold evalAuthHybridSendDrKey AuthHybridStage.idealDrKey; simp [hId]
      have hEval3 : evalAuthHybridSendDrKey .g3 true P s3.hyb.base.roCache isIdealSend secrets =
            (do let dk ← sampleDRKey96; pure (dk, (secrets, dk) :: s3.hyb.base.roCache)) := by
        unfold evalAuthHybridSendDrKey AuthHybridStage.idealDrKey evalHkdfOrRo
        change (if isIdealSend && false then _ else _) = _
        simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        change (match s3.adv.hyb.base.roCache.find? (fun (s, _) => s == secrets) with
          | some (_, drKey) => pure (drKey, s3.hyb.base.roCache)
          | none => do
            let drKey ← sampleDRKey96
            pure (drKey, (secrets, drKey) :: s3.hyb.base.roCache)) = _
        rw [hF3]
      rw [hEval35, hEval3, bind_assoc, bind_assoc]
      refine RelProbUpToBad.bind_refl_support sampleDRKey96 _ _ (fun dk _ => ?_)
      simp only [pure_bind]; refine relProbUpToBad_finishAuthHybridSendPost_of_roCoupled P hw maxRo
        sid bundle m0 m1 uEntry ekASk ephASk spqrCoins ss kemCt s35 s3 hAg
        dk s35.hyb.base.roCache ((secrets, dk) :: s3.hyb.base.roCache)
        (fun rk1 ck1_0 rootRoCache' pqrStA spqrSalt? pqRatchetMsg hSpqr => ?_)
      intro y3
      have hSub := authHybridTraceSub_finishSend_of_spqr_some P sid bundle m0 m1 uEntry
        ekASk ephASk spqrCoins ss kemCt s3 dk ((secrets, dk) :: s3.hyb.base.roCache)
        rk1 ck1_0 rootRoCache' hSpqr
      have hPeerKeys := koskBundleOk_imp_validPeerKeys P s3.hyb.base hRun.1.1 bundle hKosk
      let msgPlain := if isFreshPeer then (if s3.hyb.base.secb then m1 else m0) else m0
      let s_new := buildSendIdealSession P sid bundle uEntry ekASk ephASk kemCt msgPlain
        dk rk1 ck1_0 (P.chainKdfNext ck1_0) spqrSalt? pqRatchetMsg
      let initRec : _root_.SignalPqxdh.Security.InitKemRecord S :=
        { sid := sid, pqspkPk := bundle.pqspkB, kemCt := kemCt, kemSs := ss }
      have hy3Eq :
          y3 = withLatchedHyb s3 (finishAuthHybridSendPure P sid bundle m0 m1 uEntry
            ekASk ephASk spqrCoins ss kemCt s3.hyb dk ((secrets, dk) :: s3.hyb.base.roCache)
            rk1 ck1_0 rootRoCache').2 := rfl
      have hRo3 : y3.adv.hyb.base.roCache = (secrets, s_new.drKey) :: s3.adv.hyb.base.roCache := by
        rw [hy3Eq]; unfold finishAuthHybridSendPure; rw [hSpqr]; rfl
      have hId3 : y3.hyb.idealSessions = s_new :: s3.hyb.idealSessions := by
        rw [hy3Eq]; unfold finishAuthHybridSendPure; rw [hSpqr]
        dsimp only [withLatchedHyb, AuthAdvLatchedState.hyb]
        change (if isIdealSend then s_new :: s3.hyb.idealSessions else s3.hyb.idealSessions) = _
        simp only [hId, ↓reduceIte]; rfl
      have hSessMem : sessEntry ∈ y3.hyb.base.sessions := by
        rw [hy3Eq]; unfold finishAuthHybridSendPure; rw [hSpqr]; exact List.mem_cons_self
      have hUsedMem : sessEntry.sid ∈ y3.hyb.base.usedSendSessions := by
        rw [hy3Eq]; unfold finishAuthHybridSendPure; rw [hSpqr]; exact List.mem_cons_self
      have hInitMem : initRec ∈ y3.hyb.initKemRecs := by
        rw [hy3Eq]; unfold finishAuthHybridSendPure; rw [hSpqr]; exact List.mem_cons_self
      have hPrinEq : y3.hyb.base.principals = s3.hyb.base.principals := by
        rw [hy3Eq]; unfold finishAuthHybridSendPure; rw [hSpqr]; rfl
      have hSpkEq : y3.hyb.base.spkBundles = s3.hyb.base.spkBundles := by
        rw [hy3Eq]; unfold finishAuthHybridSendPure; rw [hSpqr]; rfl
      have hViNew : ValidIdealAuthSession S P y3.hyb s_new sessEntry u.val uEntry
          kemCoins ss initRec :=
        ⟨hSessMem, rfl, hEkLen, rfl, rfl, rfl, rfl, rfl,
         hPrinEq ▸ huMem, hSender, rfl, hKem, hInitMem, rfl, rfl, rfl,
         hPeerKeys.1, hPeerKeys.2.1, hPeerKeys.2.2⟩
      have hVhNew : ValidIdealSessionHonesty S P y3.hyb s_new sessEntry := by
        refine ⟨?_, ?_, ?_⟩
        · rcases Bool.or_eq_true_iff.mp hId with hFr | hSpkPq
          · exact Or.inl hFr
          · rcases Bool.and_eq_true_iff.mp hSpkPq with ⟨hSpk0, hPq⟩
            rcases Bool.and_eq_true_iff.mp hSpk0 with ⟨_, hSpkId⟩; rw [hSpkEq]
            exact Or.inr ⟨exists_spkBundle_of_checkBundleSpkHonIdeal P s3.hyb.base.principals
              s3.hyb.base.spkBundles bundle hSpkId, hPq⟩
        · intro hSpk; rw [hSpkEq]
          exact exists_spkBundle_of_checkBundleProvenanceExact_fst P s3.hyb.base.principals
            s3.hyb.base.spkBundles s3.hyb.base.opkEntries bundle hSpk
        · intro hPq; rw [hPrinEq, hSpkEq]
          exact exists_pqspkBundle_of_checkBundleProvenanceExact_thd P s3.hyb.base.principals
            s3.hyb.base.spkBundles s3.hyb.base.opkEntries bundle hPq
      have hSecNew : secrets = idealSessionSecrets P uEntry sessEntry.ekASk ss s_new := by
        unfold secrets idealSessionSecrets dh1 dh2 dh3 dh4? s_new buildSendIdealSession sessEntry
          mkSendSessEntry
        cases bundle.opkB? <;> rfl
      refine authRoCacheCoupled_finishSend_ideal P hRc hF35 hF3 hSub hRo3 hId3 ?_ ?_ ?_
        hViNew hVhNew hSecNew ⟨hSessMem, hUsedMem, hSend, hDh3Sec⟩
      · rw [hy3Eq]; unfold finishAuthHybridSendPure; rw [hSpqr]; rfl
      · rw [hy3Eq]; unfold finishAuthHybridSendPure; rw [hSpqr]; rfl
      · intro x hx; rw [hy3Eq]; unfold finishAuthHybridSendPure; rw [hSpqr]
        exact List.mem_cons_of_mem _ hx
    | some p =>
      by_cases hSpkAny : (spkHonIdeal || sessEntry.spkHonest) = true
      · have hSpkWitness : ∃ k_s j_s b_s,
            ((k_s, j_s), b_s) ∈ s3.hyb.base.spkBundles ∧
            P.pow8 sessEntry.peerSpkPk = P.pow8 b_s.spkPk := by
          rcases Bool.or_eq_true_iff.mp hSpkAny with hSpkId | hSpkEx
          · exact exists_spkBundle_of_checkBundleSpkHonIdeal P s3.hyb.base.principals
              s3.hyb.base.spkBundles bundle hSpkId
          · exact exists_spkBundle_of_checkBundleProvenanceExact_fst P s3.hyb.base.principals
              s3.hyb.base.spkBundles s3.hyb.base.opkEntries bundle hSpkEx
        rcases hSpkWitness with ⟨k_s, j_s, b_s, hbMem, hPowSpk⟩
        have hBadPost : badAuthFgAnyLatchedMono P maxRo (sendPostFgState s3 sid sessEntry) = true ∨
            latchRespEkCollAtSend P s3.adv.respRecs sessEntry.ekASk = true := by
          rcases hRc.2.2.1 secrets p hF3 with ⟨_, hInLog | hSess | hResp⟩
          · left
            have hTake : secrets ∈ (sendPostFgState s3 sid sessEntry).advRoLog.take maxRo := by
              change secrets ∈ s3.adv.advRoLog.take maxRo
              rwa [List.take_of_length_le hLogLen]
            exact badAuthFgAnyLatched_true_of_advRoLog_dh3 P hP maxRo
              (sendPostFgState s3 sid sessEntry) hPostV List.mem_cons_self
              hbMem hPowSpk hTake hDh3Sec
          · left
            rcases hSess with ⟨s_old, hsOld, _, _, hDh3Old⟩
            have hSlotNe := slotIdx_ne_of_mem_sessions_cons s3 hRun.1 hSend hNotUsed
              sessEntry rfl hsOld
            exact badAuthFgAnyLatched_true_of_session_dh3 P hP maxRo
              (sendPostFgState s3 sid sessEntry) hPostV List.mem_cons_self
              hbMem hPowSpk (List.mem_cons_of_mem _ hsOld) hSlotNe
              (hDh3Old.symm.trans hDh3Sec)
          · rcases hResp with ⟨k_r, j_r, bEntry_r, r_rec, hbMemR, hrMem, hrKey, hrLen, hDh3R⟩
            have hrTake :
                r_rec ∈ (sendPostFgState s3 sid sessEntry).respRecs.take S.N_sess_tot := by
              change r_rec ∈ s3.adv.respRecs.take S.N_sess_tot
              rwa [List.take_of_length_le hRespLen]
            exact idealSend_respOrigin_imp_badDh3_or_respEkColl P hP maxRo
              (sendPostFgState s3 sid sessEntry) hPostV List.mem_cons_self hEkLen
              hbMem hPowSpk hbMemR hrTake hrKey hrLen (hDh3R.symm.trans hDh3Sec)
        refine RelProbUpToBad.bad6 _ _ (fun y3 hy3 => ?_)
        rcases mem_support_bind_finishAuthHybridSendPost P hw maxRo sid bundle m0 m1
          uEntry ekASk ephASk spqrCoins ss kemCt s3 _ hy3 with ⟨hBadEq, hCollEq, _⟩
        rw [Bool.or_eq_true_iff, hBadEq, hCollEq]; exact hBadPost
      · rw [Bool.not_eq_true, Bool.or_eq_false_iff] at hSpkAny
        rcases hSpkAny with ⟨hSpkIdF, hSpkExF⟩
        have hFreshTrue : sessEntry.fresh = true := by
          change isFreshPeer = true; rcases Bool.or_eq_true_iff.mp hId with hFr | hSpkPq
          · exact hFr
          · rw [hSpkIdF, Bool.and_false, Bool.false_and] at hSpkPq; nomatch hSpkPq
        refine RelProbUpToBad.of_support_prod _ _ (fun y35 hy35 y3 hy3 => Or.inr ⟨?_, ?_⟩)
        · rcases mem_support_bind_finishAuthHybridSendPost P hw maxRo sid bundle m0 m1
            uEntry ekASk ephASk spqrCoins ss kemCt s35 _ hy35 with ⟨_, _, hMem35⟩
          have hSessEq : mkSendSessEntry P s35.hyb.base sid bundle m0 m1
                (match findHonestPrincipal P s35.hyb.base.principals bundle.ikB with
                 | some (_, pEntry) => !pEntry.corrupted
                 | none => false) ekASk ephASk = sessEntry := by
            rw [hAg]; rfl
          rw [hSessEq] at hMem35; unfold isAuthG3Abort
          apply Bool.or_eq_true_iff.mpr; left; apply Bool.or_eq_true_iff.mpr; left
          apply Bool.or_eq_true_iff.mpr; right; unfold hasBadSigAuth; rw [List.any_eq_true]
          exact ⟨sessEntry, hMem35, by simp [hFreshTrue, hSpkExF]⟩
        · rcases mem_support_bind_finishAuthHybridSendPost P hw maxRo sid bundle m0 m1
            uEntry ekASk ephASk spqrCoins ss kemCt s3 _ hy3 with ⟨_, _, hMem3⟩
          unfold isAuthG3Abort
          apply Bool.or_eq_true_iff.mpr; left; apply Bool.or_eq_true_iff.mpr; left
          apply Bool.or_eq_true_iff.mpr; right; unfold hasBadSigAuth; rw [List.any_eq_true]
          exact ⟨sessEntry, hMem3, by simp [hFreshTrue, hSpkExF]⟩
  · rw [Bool.not_eq_true] at hId
    have hEval35 : evalAuthHybridSendDrKey .g3_5 true P s35.hyb.base.roCache isIdealSend secrets =
          evalHkdfOrRo true P s35.hyb.base.roCache secrets := by
      unfold evalAuthHybridSendDrKey; simp [hId]
    have hEval3 : evalAuthHybridSendDrKey .g3 true P s3.hyb.base.roCache isIdealSend secrets =
          evalHkdfOrRo true P s3.hyb.base.roCache secrets := by
      unfold evalAuthHybridSendDrKey; simp [hId]
    rw [hEval35, hEval3]
    cases hF35 : s35.adv.hyb.base.roCache.find? (fun (s, _) => s == secrets) with
    | some p =>
      have hF3 := hRc.1 secrets p hF35; rcases p with ⟨sec0, dk0⟩; have hHkdf35 :
          evalHkdfOrRo true P s35.hyb.base.roCache secrets = pure (dk0, s35.hyb.base.roCache) := by
        unfold evalHkdfOrRo
        change (match s35.adv.hyb.base.roCache.find? (fun (s, _) => s == secrets) with
          | some (_, drKey) => pure (drKey, s35.hyb.base.roCache)
          | none => _) = _
        rw [hF35]
      have hHkdf3 :
          evalHkdfOrRo true P s3.hyb.base.roCache secrets = pure (dk0, s3.hyb.base.roCache) := by
        unfold evalHkdfOrRo
        change (match s3.adv.hyb.base.roCache.find? (fun (s, _) => s == secrets) with
          | some (_, drKey) => pure (drKey, s3.hyb.base.roCache)
          | none => _) = _
        rw [hF3]
      rw [hHkdf35, hHkdf3, pure_bind, pure_bind]
      refine relProbUpToBad_finishAuthHybridSendPost_of_roCoupled P hw maxRo
        sid bundle m0 m1 uEntry ekASk ephASk spqrCoins ss kemCt s35 s3 hAg
        dk0 s35.hyb.base.roCache s3.hyb.base.roCache
        (fun rk1 ck1_0 rootRoCache' pqrStA spqrSalt? pqRatchetMsg hSpqr => ?_)
      intro y3
      have hSub := authHybridTraceSub_finishSend_of_spqr_some P sid bundle m0 m1 uEntry
        ekASk ephASk spqrCoins ss kemCt s3 dk0 s3.hyb.base.roCache rk1 ck1_0 rootRoCache' hSpqr
      have hy3Eq :
          y3 = withLatchedHyb s3 (finishAuthHybridSendPure P sid bundle m0 m1 uEntry
            ekASk ephASk spqrCoins ss kemCt s3.hyb dk0 s3.hyb.base.roCache
            rk1 ck1_0 rootRoCache').2 := rfl
      refine authRoCacheCoupled_of_traceSub_eq_roCache P hRc hSub ?_ ?_ ?_ ?_ ?_
      · rw [hy3Eq]; unfold finishAuthHybridSendPure; rw [hSpqr]; rfl
      · rw [hy3Eq]; unfold finishAuthHybridSendPure; rw [hSpqr]
        dsimp only [withLatchedHyb, AuthAdvLatchedState.hyb]
        change (if isIdealSend then _ else s3.hyb.idealSessions) = s3.hyb.idealSessions
        simp only [hId, Bool.false_eq_true, ↓reduceIte]
      · intro x hx; rw [hy3Eq]; unfold finishAuthHybridSendPure; rw [hSpqr]; exact hx
      · intro x hx; rw [hy3Eq]; unfold finishAuthHybridSendPure; rw [hSpqr]
        exact List.mem_cons_of_mem _ hx
      · intro x hx; rw [hy3Eq]; unfold finishAuthHybridSendPure; rw [hSpqr]; exact hx
    | none =>
      cases hF3 : s3.adv.hyb.base.roCache.find? (fun (s, _) => s == secrets) with
      | none =>
        have hHkdf35 : evalHkdfOrRo true P s35.hyb.base.roCache secrets =
              (do let dk ← sampleDRKey96; pure (dk, (secrets, dk) :: s35.hyb.base.roCache)) := by
          unfold evalHkdfOrRo
          change (match s35.adv.hyb.base.roCache.find? (fun (s, _) => s == secrets) with
            | some (_, drKey) => pure (drKey, s35.hyb.base.roCache)
            | none => _) = _
          rw [hF35]
        have hHkdf3 : evalHkdfOrRo true P s3.hyb.base.roCache secrets =
              (do let dk ← sampleDRKey96; pure (dk, (secrets, dk) :: s3.hyb.base.roCache)) := by
          unfold evalHkdfOrRo
          change (match s3.adv.hyb.base.roCache.find? (fun (s, _) => s == secrets) with
            | some (_, drKey) => pure (drKey, s3.hyb.base.roCache)
            | none => _) = _
          rw [hF3]
        rw [hHkdf35, hHkdf3, bind_assoc, bind_assoc]
        refine RelProbUpToBad.bind_refl_support sampleDRKey96 _ _ (fun dk _ => ?_)
        simp only [pure_bind]
        refine relProbUpToBad_finishAuthHybridSendPost_of_roCoupled P hw maxRo
          sid bundle m0 m1 uEntry ekASk ephASk spqrCoins ss kemCt s35 s3 hAg
          dk ((secrets, dk) :: s35.hyb.base.roCache) ((secrets, dk) :: s3.hyb.base.roCache)
          (fun rk1 ck1_0 rootRoCache' pqrStA spqrSalt? pqRatchetMsg hSpqr => ?_)
        intro y3
        let y3_base := withAuthAdvLatchedRoCache s3.adv.hyb.base.roCache y3
        have hy3Eq :
            y3 = withLatchedHyb s3 (finishAuthHybridSendPure P sid bundle m0 m1 uEntry
              ekASk ephASk spqrCoins ss kemCt s3.hyb dk ((secrets, dk) :: s3.hyb.base.roCache)
              rk1 ck1_0 rootRoCache').2 := rfl
        have hSubBase : AuthHybridTraceSub s3.hyb y3_base.hyb := by
          dsimp only [y3_base]; rw [hy3Eq]; unfold finishAuthHybridSendPure; rw [hSpqr]
          dsimp only [withAuthAdvLatchedRoCache, withAuthAdvRoCache, withAuthHybRoCache,
            withAuthBaseRoCache, withLatchedHyb, AuthAdvLatchedState.hyb]
          refine ⟨⟨List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _,
            List.Sublist.refl _, List.sublist_cons_self _ _⟩,
            List.sublist_cons_self _ _, List.Sublist.refl _, ?_⟩
          exact match (match findHonestPrincipal P s3.adv.hyb.base.principals bundle.ikB with
            | some (_, pEntry) => !pEntry.corrupted
            | none => false) ||
            ((findHonestPrincipal P s3.adv.hyb.base.principals bundle.ikB).isSome &&
              checkBundleSpkHonIdeal P s3.adv.hyb.base.principals
                s3.adv.hyb.base.spkBundles bundle &&
              (checkBundleProvenanceExact P s3.adv.hyb.base.principals s3.adv.hyb.base.spkBundles
                s3.adv.hyb.base.opkEntries bundle).2.2) with
          | true => List.sublist_cons_self _ _
          | false => List.Sublist.refl _
        have hRcBase : AuthRoCacheCoupled P
              (withAuthAdvLatchedRoCache s35.adv.hyb.base.roCache y3_base) y3_base := by
          refine authRoCacheCoupled_of_traceSub_eq_roCache P hRc hSubBase rfl ?_ ?_ ?_ ?_
          · change y3.hyb.idealSessions = s3.hyb.idealSessions
            rw [hy3Eq]; unfold finishAuthHybridSendPure; rw [hSpqr]
            dsimp only [withLatchedHyb, AuthAdvLatchedState.hyb]
            change (if isIdealSend then _ else s3.hyb.idealSessions) = s3.hyb.idealSessions
            simp only [hId, Bool.false_eq_true, ↓reduceIte]
          · intro x hx; change x ∈ y3.adv.advRoLog
            rw [hy3Eq]; unfold finishAuthHybridSendPure; rw [hSpqr]; exact hx
          · intro x hx; change x ∈ y3.hyb.base.usedSendSessions
            rw [hy3Eq]; unfold finishAuthHybridSendPure; rw [hSpqr]; exact List.mem_cons_of_mem _ hx
          · intro x hx; change x ∈ y3.adv.respRecs
            rw [hy3Eq]; unfold finishAuthHybridSendPure; rw [hSpqr]; exact hx
        have hCons := authRoCacheCoupled_cons_both P hRcBase secrets dk hF3
          ⟨sessEntry, by
            change sessEntry ∈ y3.hyb.base.sessions
            rw [hy3Eq]; unfold finishAuthHybridSendPure; rw [hSpqr]; exact List.mem_cons_self,
           by
            change sessEntry.sid ∈ y3.hyb.base.usedSendSessions
            rw [hy3Eq]; unfold finishAuthHybridSendPure; rw [hSpqr]; exact List.mem_cons_self,
           hSend, hDh3Sec⟩
        have h3Eq :
            withAuthAdvLatchedRoCache ((secrets, dk) :: y3_base.adv.hyb.base.roCache) y3_base =
              y3 := by
          dsimp only [y3_base]; rw [hy3Eq]; unfold finishAuthHybridSendPure; rw [hSpqr]; rfl
        rw [← h3Eq]; exact hCons
      | some p =>
        rcases hRc.2.2.2 secrets p hF35 hF3 with
          ⟨s_id, _, sessEntry_id, u_id, uEntry_id, kc_id, ss_id, ir_id, hViId, hVhId, hSecId, _⟩
        have hNoBadSig : hasBadSigAuth s3.hyb = false := by
          unfold isAuthG3Abort at hAbF; simp only [Bool.or_eq_false_iff] at hAbF; exact hAbF.1.1.2
        rcases validIdealSessionHonesty_imp_spk_and_pqspk_of_hasBadSigAuth_false
            P s3.hyb hNoBadSig hViId.1 hVhId with ⟨⟨k_s, j_s, b_s, hbMemId, hPowSpkId⟩, _⟩
        have hPowSessId : P.pow8 sessEntry_id.peerSpkPk = P.pow8 b_s.spkPk := by
          rw [hViId.2.2.2.2.2.1, hPowSpkId]
        have hDh3Id : P.x25519 sessEntry.ekASk sessEntry.peerSpkPk =
              P.x25519 sessEntry_id.ekASk sessEntry_id.peerSpkPk := by
          rw [← hDh3Sec, hSecId, hViId.2.2.2.2.2.1, extractDh3_idealSessionSecrets P hw]
        have hSlotNe := slotIdx_ne_of_mem_sessions_cons s3 hRun.1 hSend hNotUsed
          sessEntry rfl hViId.1
        have hBadPost : badAuthFgAnyLatchedMono P maxRo (sendPostFgState s3 sid sessEntry) = true :=
          badAuthFgAnyLatched_true_of_session_dh3 P hP maxRo
            (sendPostFgState s3 sid sessEntry) hPostV
            (List.mem_cons_of_mem _ hViId.1) hbMemId hPowSessId
            List.mem_cons_self hSlotNe.symm hDh3Id
        refine RelProbUpToBad.bad6 _ _ (fun y3 hy3 => ?_)
        rcases mem_support_bind_finishAuthHybridSendPost P hw maxRo sid bundle m0 m1
          uEntry ekASk ephASk spqrCoins ss kemCt s3 _ hy3 with ⟨hBadEq, _, _⟩
        rw [Bool.or_eq_true_iff, hBadEq]; exact Or.inl hBadPost
theorem relProbUpToBad_runAuthHybridSendKosk_latched {S : Setup} (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (maxRo : ℕ)
    (sid : SessionId S) (u : Fin S.N_id) (hSender : sessionSenderIdx sid = u.val)
    (hSend : IsSendSessionId S sid) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (s35 s3 : AuthAdvLatchedState S) (hInv : AuthG3G3_5CoupledInv P s35 s3)
    (hAbF : isAuthG3Abort P s3.hyb = false) (hLogLen : s3.adv.advRoLog.length ≤ maxRo)
    (hRespLen : s3.adv.respRecs.length ≤ S.N_sess_tot) : RelProbUpToBad (fun y35 y3 =>
        (y35.1 = y3.1 ∧ AuthAdvLatchedAgreeOffRo y35.2 y3.2 ∧ AuthRoCacheCoupled P y35.2 y3.2) ∨
        (isAuthG3Abort P y35.2.hyb = true ∧ isAuthG3Abort P y3.2.hyb = true))
      (fun y3 => badAuthFgAnyLatchedMono P maxRo y3.2.toFg ||
                 latchRespEkCollSendStep P s3 y3.2 false)
      (runAuthHybridSendLatched .g3_5 S P sid u bundle m0 m1 s35)
      (runAuthHybridSendLatched .g3 S P sid u bundle m0 m1 s3) := by
  have hAg := hInv.1; have hRc := hInv.2.2
  have hUsedEq : s35.hyb.base.usedSendSessions = s3.hyb.base.usedSendSessions := by rw [hAg]; rfl
  have hPrinEq : s35.hyb.base.principals = s3.hyb.base.principals := by rw [hAg]; rfl
  have hSpkEq : s35.hyb.base.spkBundles = s3.hyb.base.spkBundles := by rw [hAg]; rfl
  have hOpkEq : s35.hyb.base.opkEntries = s3.hyb.base.opkEntries := by rw [hAg]; rfl
  have hAdvEq : s35.hyb.base.advKeys = s3.hyb.base.advKeys := by rw [hAg]; rfl
  rw [runAuthHybridSendLatched_eq .g3_5 P sid u bundle m0 m1 s35,
      runAuthHybridSendLatched_eq .g3 P sid u bundle m0 m1 s3]
  dsimp only; rw [hUsedEq, hPrinEq, hSpkEq, hOpkEq, hAdvEq]
  by_cases h1 : (m0.length != m1.length) = true
  · simp only [h1, ↓reduceIte]; exact RelProbUpToBad.of_pure (Or.inl ⟨rfl, hAg, hRc⟩)
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : s3.hyb.base.usedSendSessions.contains sid = true
    · simp only [h2, ↓reduceIte]; exact RelProbUpToBad.of_pure (Or.inl ⟨rfl, hAg, hRc⟩)
    · rw [Bool.not_eq_true] at h2; simp only [h2, Bool.false_eq_true, ↓reduceIte]
      cases hF : s3.hyb.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none => dsimp only; exact RelProbUpToBad.of_pure (Or.inl ⟨rfl, hAg, hRc⟩)
      | some ue =>
        rcases ue with ⟨uIdx, uEntry⟩; dsimp only
        have huMem0 : (uIdx, uEntry) ∈ s3.hyb.base.principals := List.mem_of_find?_eq_some hF
        have huEq : uIdx = u.val :=
          beq_iff_eq.mp (List.find?_some (p := fun (x : Nat × PrincipalEntry) => x.1 == u.val) hF)
        subst huEq
        by_cases h3 : (!(match findHonestPrincipal P s3.hyb.base.principals bundle.ikB with
            | some (_, pEntry) => !pEntry.corrupted
            | none => false) && m0 != m1) = true
        · simp only [h3, ↓reduceIte]; exact RelProbUpToBad.of_pure (Or.inl ⟨rfl, hAg, hRc⟩)
        · simp only [h3, Bool.false_eq_true, ↓reduceIte]
          by_cases h4 : (!koskBundleOk P s3.hyb.base.principals s3.hyb.base.spkBundles
                           s3.hyb.base.opkEntries s3.hyb.base.advKeys bundle) = true
          · simp only [h4, ↓reduceIte]; exact RelProbUpToBad.of_pure (Or.inl ⟨rfl, hAg, hRc⟩)
          · simp only [h4, Bool.false_eq_true, ↓reduceIte]
            have hKosk : koskBundleOk P s3.hyb.base.principals s3.hyb.base.spkBundles
                s3.hyb.base.opkEntries s3.hyb.base.advKeys bundle = true := by revert h4; simp
            refine RelProbUpToBad.bind_refl_support sampleScalar32 _ _ (fun ekASk hek => ?_)
            have hEkLen : ekASk.length = 32 := length_of_mem_support_sampleScalar32 hek
            refine RelProbUpToBad.bind_same sampleCoins32 (fun kemCoins => ?_)
            refine RelProbUpToBad.bind_same sampleScalar32 (fun ephASk => ?_)
            refine RelProbUpToBad.bind_same sampleCoins32 (fun spqrCoins => ?_)
            by_cases h5 : (!(P.sigVerify (resolveSigPk P s3.hyb.base.principals bundle.ikB)
                              (encodeEC bundle.spkB) bundle.spkSig &&
                             P.sigVerify (resolveSigPk P s3.hyb.base.principals bundle.ikB)
                              (encodeKEM bundle.pqspkB) bundle.pqspkSig)) = true
            · simp only [h5, ↓reduceIte]; exact RelProbUpToBad.of_pure (Or.inl ⟨rfl, hAg, hRc⟩)
            · simp only [h5, Bool.false_eq_true, ↓reduceIte]
              cases hKem : P.kemEncaps bundle.pqspkB kemCoins with
              | none => dsimp only; exact RelProbUpToBad.of_pure (Or.inl ⟨rfl, hAg, hRc⟩)
              | some sc =>
                rcases sc with ⟨ss, kemCt⟩; dsimp only
                exact relProbUpToBad_evalSendDrKey_and_finish P hP maxRo sid u hSender hSend
                  bundle m0 m1 uEntry ekASk kemCoins ephASk spqrCoins ss kemCt hEkLen
                  s35 s3 hInv huMem0 h2 hKosk hKem hAbF hLogLen hRespLen
theorem fgAuthStepCoupling_cutoff_latched_sendOPK_or_respEkColl
    (S : Setup) (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (maxRo : ℕ) (u : Fin S.N_id) (i : Fin S.N_send_opk) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (s35 s3 : AuthAdvLatchedState S) (hInv : AuthG3G3_5CoupledInv P s35 s3)
    (hAbF : isAuthG3Abort P s3.hyb = false) (hLogLen : s3.adv.advRoLog.length ≤ maxRo)
    (hRespLen : s3.adv.respRecs.length ≤ S.N_sess_tot) : RelProbUpToBad (fun y35 y3 =>
        (y35.1 = y3.1 ∧ AuthG3G3_5CoupledInv P y35.2 y3.2) ∨
        (isAuthG3Abort P y35.2.hyb = true ∧ isAuthG3Abort P y3.2.hyb = true))
      (fun y3 => badAuthFgAnyLatchedMono P maxRo y3.2.toFg ||
                 latchRespEkCollSendStep P s3 y3.2 false)
      ((pqxdhAuthAdvLatchedStageImpl .g3_5 S P (.sendOPK u i bundle m0 m1)).run s35)
      ((pqxdhAuthAdvLatchedStageImpl .g3 S P (.sendOPK u i bundle m0 m1)).run s3) := by
  refine relProbUpToBad_of_imp_support_right ?_
  have hStep : RelProbUpToBad
        (fun y35 y3 =>
          (y35.1 = y3.1 ∧ AuthAdvLatchedAgreeOffRo y35.2 y3.2 ∧ AuthRoCacheCoupled P y35.2 y3.2) ∨
          (isAuthG3Abort P y35.2.hyb = true ∧ isAuthG3Abort P y3.2.hyb = true))
        (fun y3 => badAuthFgAnyLatchedMono P maxRo y3.2.toFg ||
                   latchRespEkCollSendStep P s3 y3.2 false)
        ((pqxdhAuthAdvLatchedStageImpl .g3_5 S P (.sendOPK u i bundle m0 m1)).run s35)
        ((pqxdhAuthAdvLatchedStageImpl .g3 S P (.sendOPK u i bundle m0 m1)).run s3) := by
    unfold pqxdhAuthAdvLatchedStageImpl pqxdhAuthAdvStageImpl pqxdhAuthHybridKoskImpl
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
      validAuthHybridRunInv_pqxdhAuthAdvLatchedStageImpl .g3 P _ s3 hInv.2.1 hy3, hRc⟩
  · exact Or.inr hAb
theorem fgAuthStepCoupling_cutoff_latched_sendNoOPK_or_respEkColl
    (S : Setup) (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (maxRo : ℕ) (u : Fin S.N_id) (i : Fin S.N_send_no_opk)
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes) (s35 s3 : AuthAdvLatchedState S)
    (hInv : AuthG3G3_5CoupledInv P s35 s3) (hAbF : isAuthG3Abort P s3.hyb = false)
    (hLogLen : s3.adv.advRoLog.length ≤ maxRo) (hRespLen : s3.adv.respRecs.length ≤ S.N_sess_tot) :
    RelProbUpToBad (fun y35 y3 => (y35.1 = y3.1 ∧ AuthG3G3_5CoupledInv P y35.2 y3.2) ∨
        (isAuthG3Abort P y35.2.hyb = true ∧ isAuthG3Abort P y3.2.hyb = true))
      (fun y3 => badAuthFgAnyLatchedMono P maxRo y3.2.toFg ||
                 latchRespEkCollSendStep P s3 y3.2 false)
      ((pqxdhAuthAdvLatchedStageImpl .g3_5 S P (.sendNoOPK u i bundle m0 m1)).run s35)
      ((pqxdhAuthAdvLatchedStageImpl .g3 S P (.sendNoOPK u i bundle m0 m1)).run s3) := by
  refine relProbUpToBad_of_imp_support_right ?_
  have hStep : RelProbUpToBad
        (fun y35 y3 =>
          (y35.1 = y3.1 ∧ AuthAdvLatchedAgreeOffRo y35.2 y3.2 ∧ AuthRoCacheCoupled P y35.2 y3.2) ∨
          (isAuthG3Abort P y35.2.hyb = true ∧ isAuthG3Abort P y3.2.hyb = true))
        (fun y3 => badAuthFgAnyLatchedMono P maxRo y3.2.toFg ||
                   latchRespEkCollSendStep P s3 y3.2 false)
        ((pqxdhAuthAdvLatchedStageImpl .g3_5 S P (.sendNoOPK u i bundle m0 m1)).run s35)
        ((pqxdhAuthAdvLatchedStageImpl .g3 S P (.sendNoOPK u i bundle m0 m1)).run s3) := by
    unfold pqxdhAuthAdvLatchedStageImpl pqxdhAuthAdvStageImpl pqxdhAuthHybridKoskImpl
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
      validAuthHybridRunInv_pqxdhAuthAdvLatchedStageImpl .g3 P _ s3 hInv.2.1 hy3, hRc⟩
  · exact Or.inr hAb
end Proofs.SignalPqxdh.Security
