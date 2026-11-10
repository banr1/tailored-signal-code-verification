/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3C
import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3B
import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3D
import Computational.Proofs.SignalPqxdh.Security.RoKemHopA
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.EvalDist.Measure

/-!
# PQXDH Authentication Sub-Hop `G3.6 → G3.7` (`PrfChainKey`)

Proves `ValidAuthHybrid` preservation under `authCkStepWith` and establishes the creation-order
`PrfChainKey` hybrid bound `hop_G3_6_G3_7 : AuthHopG3_6G3_7Stmt S (prfCkReductionAuthFixed S)`.
-/

@[expose] public section

set_option autoImplicit false

open OracleSpec OracleComp MeasureTheory ENNReal BigOperators

namespace SignalPqxdh.Security

open SignalPqxdh
open _root_.Proofs.SignalPqxdh.Security

namespace AuthSubHops1to3

theorem validAuthHybrid_finishAuthHybridSend {S : Setup} (P : Primitives)
    (sid : SessionId S) (hSend : IsSendSessionId S sid)
    (uEntry : PrincipalEntry)
    (peerPrincipal? : Option (Nat × PrincipalEntry)) (isFreshPeer : Bool)
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (ekASk ekAPk ss kemCt ephASk ephAPk : Bytes)
    (drKey : DRKey) (rk1 ck1_0 mkSeed ck1_1 : Bytes)
    (spqrSalt? : Option Bytes) (pqRatchetMsg : Bytes)
    (deriveMessageKeys : MessageKeys) (ad aeadCt msgPlain : Bytes)
    (roCache' : List (Bytes × DRKey))
    (rootRoCache' : List ((Bytes × Bytes) × (Bytes × Bytes)))
    (hst : AuthHybridStateFixed S)
    (hV : ValidAuthHybrid S P hst)
    (hFresh : hst.toAuthHybridState.base.usedSendSessions.contains sid = false) :
    ValidAuthHybrid S P
      { toAuthHybridState := (finishAuthHybridSend P sid uEntry peerPrincipal?
          isFreshPeer bundle m0 m1 ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 ck1_0 mkSeed ck1_1
          spqrSalt? pqRatchetMsg deriveMessageKeys ad aeadCt msgPlain
          roCache' rootRoCache' hst.toAuthHybridState).2
        recvCount := hst.recvCount } := by
  rcases hV with ⟨⟨hVP, hVS, hVO, hVSess⟩, hSessLe, hIdealLe, hSentOPKLe, hSentNoOPKLe, hVKem⟩
  have hFresh' : hst.toAuthHybridState.base.usedSendSessions.any (fun s => s == sid) = false := by
    revert hFresh; simp; rintro h x hx rfl; exact h hx
  have hCons := (validSessionIds_cons S sid
    hst.toAuthHybridState.base.usedSendSessions hSend hVSess hFresh').1
  refine ⟨⟨hVP, hVS, hVO, hCons⟩, ?_, ?_, ?_, ?_, hVKem⟩
  · unfold finishAuthHybridSend; dsimp only; simp only [List.length_cons]; omega
  · unfold finishAuthHybridSend; dsimp only
    split <;> simp only [List.length_cons] <;> omega
  · unfold finishAuthHybridSend; dsimp only
    cases peerPrincipal? with
    | none => simp only [List.length_cons]; omega
    | some p =>
      cases bundle.opkB? <;> simp only [List.length_cons] <;> omega
  · unfold finishAuthHybridSend; dsimp only
    cases peerPrincipal? with
    | none => simp only [List.length_cons]; omega
    | some p =>
      cases bundle.opkB? <;> simp only [List.length_cons] <;> omega

private theorem forall_mem_support_ite {α : Type} (c : Bool) (t e : ProbComp α) (Q : α → Prop)
    (ht : ∀ x ∈ support t, Q x) (he : ∀ x ∈ support e, Q x) :
    ∀ x ∈ support (if c then t else e), Q x := by
  cases c <;> [exact he; exact ht]

theorem authCkSendWith_validAuthHybrid (S : Setup) (P : Primitives)
    (sampAt : Nat → ProbComp (Bytes × Bytes))
    (sid : SessionId S) (hSend : IsSendSessionId S sid)
    (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) (hV : ValidAuthHybrid S P hst) :
    ∀ x ∈ support (authCkSendWith S P sampAt sid u bundle m0 m1 hst), ValidAuthHybrid S P x.2 := by
  unfold authCkSendWith
  dsimp only
  refine forall_mem_support_ite _ _ _ _ (fun x hx => by simp at hx; subst hx; exact hV) ?_
  refine forall_mem_support_ite _ _ _ _ (fun x hx => by simp at hx; subst hx; exact hV) ?_
  cases hFresh : hst.toAuthHybridState.base.usedSendSessions.contains sid
  · simp only [Bool.false_eq_true, ↓reduceIte]
    split
    · intro x hx; simp at hx; subst hx; exact hV
    · refine forall_mem_support_ite _ _ _ _ (fun x hx => by simp at hx; subst hx; exact hV) ?_
      refine forall_mem_support_ite _ _ _ _ (fun x hx => by simp at hx; subst hx; exact hV) ?_
      intro x hx
      simp only [MonadAttach.mem_support_bind] at hx
      rcases hx with ⟨ekASk, _, kemCoins, _, ephASk, _, spqrCoins, _, hx⟩
      revert x hx
      refine forall_mem_support_ite _ _ _ _ (fun x hx => by simp at hx; subst hx; exact hV) ?_
      cases P.kemEncaps bundle.pqspkB kemCoins with
      | none => intro x hx; simp at hx; subst hx; exact hV
      | some pair =>
        rcases pair with ⟨ss, kemCt⟩
        dsimp only
        refine forall_mem_support_ite _ _ _ _ ?_ ?_
        · intro x hx
          simp only [MonadAttach.mem_support_bind] at hx
          rcases hx with ⟨drKey, _, rk1, _, hx⟩
          revert x hx
          cases P.spqrInitSend drKey.pqrKey spqrCoins with
          | none => intro x hx; simp at hx; subst hx; exact hV
          | some spqrVal =>
            rcases spqrVal with ⟨_, spqrSalt?, pqRatchetMsg⟩
            intro x hx
            simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
            rcases hx with ⟨p, _, rfl⟩
            exact validAuthHybrid_finishAuthHybridSend P sid hSend _ _ _ bundle m0 m1
              ekASk _ _ _ ephASk _ drKey rk1 [] p.1 p.2 _ _ _ _ _ _ _ _ hst hV hFresh
        · intro x hx
          simp only [MonadAttach.mem_support_bind] at hx
          rcases hx with ⟨⟨drKey, roCache'⟩, _, ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩, _, hx⟩
          revert x hx
          cases P.spqrInitSend drKey.pqrKey spqrCoins with
          | none => intro x hx; simp at hx; subst hx; exact hV
          | some spqrVal =>
            rcases spqrVal with ⟨_, spqrSalt?, pqRatchetMsg⟩
            intro x hx
            simp only [support_pure, Set.mem_singleton_iff] at hx
            subst hx
            exact validAuthHybrid_finishAuthHybridSend P sid hSend _ _ _ bundle m0 m1
              ekASk _ _ _ ephASk _ drKey rk1 ck1_0 _ _ _ _ _ _ _ _
              roCache' rootRoCache' hst hV hFresh
  · simp only [↓reduceIte]
    intro x hx; simp at hx; subst hx; exact hV

theorem validOpkEntries_map_consumed (S : Setup)
    (target : Nat × Nat × Nat) (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (hVO : ValidOpkEntries S opkEntries) :
    ValidOpkEntries S (opkEntries.map (fun (idx, e) =>
      if idx == target then (idx, { e with consumed := true }) else (idx, e))) := by
  have hFst : (opkEntries.map (fun (idx, e) =>
      if idx == target then (idx, { e with consumed := true }) else (idx, e))).map Prod.fst =
      opkEntries.map Prod.fst := by
    rw [List.map_map]
    refine List.map_congr_left (fun ⟨idx, e⟩ _ => ?_)
    simp only [Function.comp_def]; split_ifs <;> rfl
  refine ⟨?_, ?_⟩
  · intro e he
    have he_fst : e.1 ∈ opkEntries.map Prod.fst := by
      rw [← hFst]; exact List.mem_map_of_mem he
    rw [List.mem_map] at he_fst
    rcases he_fst with ⟨e', he', heq⟩
    rw [← heq]; exact hVO.1 e' he'
  · have h_slot : (opkEntries.map (fun (idx, e) =>
        if idx == target then (idx, { e with consumed := true }) else (idx, e))).map
          (fun e => ecOpkSlotIdx S e.1) =
        opkEntries.map (fun e => ecOpkSlotIdx S e.1) := by
      simpa [List.map_map, Function.comp_def] using congrArg (List.map (ecOpkSlotIdx S)) hFst
    rw [h_slot]; exact hVO.2

theorem prepareAuthHybridRecvOPK_validAuthHybrid {S : Setup} (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (msg : PreKeyMsg)
    (hst : AuthHybridStateFixed S) (hV : ValidAuthHybrid S P hst)
    (prep : PreparedAuthRecv S)
    (hPrep : prepareAuthHybridRecvOPK true P k j o msg hst.toAuthHybridState = some prep)
    (res? : Option (DRKey × Bytes × Bytes × Bytes × List (Bytes × DRKey) ×
      List ((Bytes × Bytes) × (Bytes × Bytes))))
    (recvCount' : Nat) :
    ValidAuthHybrid S P { toAuthHybridState := (prep.finish res?).2, recvCount := recvCount' } := by
  rcases hV with ⟨⟨hVP, hVS, hVO, hVSess⟩, hSessLe, hIdealLe, hSentOPKLe, hSentNoOPKLe, hVKem⟩
  unfold prepareAuthHybridRecvOPK at hPrep
  dsimp only at hPrep
  split at hPrep; · contradiction
  split at hPrep; · contradiction
  split at hPrep; · contradiction
  split at hPrep; · contradiction
  rcases h1 : hst.toAuthHybridState.base.principals.find?
    (fun (idx, _) => idx == k.val) with _ | ⟨_, kEntry⟩ <;>
  rcases h2 : hst.toAuthHybridState.base.spkBundles.find?
    (fun (idx, _) => idx == (k.val, j.val)) with _ | ⟨_, bEntry⟩ <;>
  rcases h3 : hst.toAuthHybridState.base.opkEntries.find?
    (fun (idx, _) => idx == (k.val, j.val, o.val)) with _ | ⟨_, oEntry⟩ <;>
  simp only [h1, h2, h3] at hPrep
  all_goals try contradiction
  split at hPrep; · contradiction
  split at hPrep; · contradiction
  cases hDec : P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
  | none => rw [hDec] at hPrep; contradiction
  | some ss =>
    rw [hDec] at hPrep
    injection hPrep with hEq; subst hEq
    dsimp only
    have hVKem' : ValidRecvKemRecords P
        ({ k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk, pqspkSk := bEntry.pqspkSk,
           kemCt := msg.hdr.kemCt, kemSs := ss } ::
          hst.toAuthHybridState.recvKemRecs) := by
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr'
      · exact hDec
      · exact hVKem r hr'
    unfold finishAuthHybridRecvOPK
    cases res? with
    | none =>
      exact ⟨⟨hVP, hVS, hVO, hVSess⟩, hSessLe, hIdealLe, hSentOPKLe, hSentNoOPKLe, hVKem'⟩
    | some r =>
      rcases r with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩
      dsimp only
      have hVO' := validOpkEntries_map_consumed S (k.val, j.val, o.val)
        hst.toAuthHybridState.base.opkEntries hVO
      cases findHonestPrincipal P hst.toAuthHybridState.base.principals msg.hdr.ikAPk with
      | none =>
        exact ⟨⟨hVP, hVS, hVO', hVSess⟩, hSessLe, hIdealLe, hSentOPKLe, hSentNoOPKLe, hVKem'⟩
      | some p =>
        rcases p with ⟨_, senderEntry⟩
        dsimp only
        cases senderEntry.corrupted
        · simp only [Bool.not_false, ↓reduceIte]
          refine ⟨⟨hVP, hVS, hVO', hVSess⟩, hSessLe, hIdealLe, ?_, hSentNoOPKLe, hVKem'⟩
          rw [consumeMatchingSentOPK_length]
          exact hSentOPKLe
        · exact ⟨⟨hVP, hVS, hVO', hVSess⟩, hSessLe, hIdealLe, hSentOPKLe, hSentNoOPKLe, hVKem'⟩

theorem prepareAuthHybridRecvNoOPK_validAuthHybrid {S : Setup} (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg : PreKeyMsg)
    (hst : AuthHybridStateFixed S) (hV : ValidAuthHybrid S P hst)
    (prep : PreparedAuthRecv S)
    (hPrep : prepareAuthHybridRecvNoOPK true P k j l msg hst.toAuthHybridState = some prep)
    (res? : Option (DRKey × Bytes × Bytes × Bytes × List (Bytes × DRKey) ×
      List ((Bytes × Bytes) × (Bytes × Bytes))))
    (recvCount' : Nat) :
    ValidAuthHybrid S P { toAuthHybridState := (prep.finish res?).2, recvCount := recvCount' } := by
  rcases hV with ⟨⟨hVP, hVS, hVO, hVSess⟩, hSessLe, hIdealLe, hSentOPKLe, hSentNoOPKLe, hVKem⟩
  unfold prepareAuthHybridRecvNoOPK at hPrep
  dsimp only at hPrep
  split at hPrep; · contradiction
  split at hPrep; · contradiction
  split at hPrep; · contradiction
  split at hPrep; · contradiction
  rcases h1 : hst.toAuthHybridState.base.principals.find?
    (fun (idx, _) => idx == k.val) with _ | ⟨_, kEntry⟩ <;>
  rcases h2 : hst.toAuthHybridState.base.spkBundles.find?
    (fun (idx, _) => idx == (k.val, j.val)) with _ | ⟨_, bEntry⟩ <;>
  simp only [h1, h2] at hPrep
  all_goals try contradiction
  split at hPrep; · contradiction
  cases hDec : P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
  | none => rw [hDec] at hPrep; contradiction
  | some ss =>
    rw [hDec] at hPrep
    injection hPrep with hEq; subst hEq
    dsimp only
    have hVKem' : ValidRecvKemRecords P
        ({ k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk, pqspkSk := bEntry.pqspkSk,
           kemCt := msg.hdr.kemCt, kemSs := ss } ::
          hst.toAuthHybridState.recvKemRecs) := by
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr'
      · exact hDec
      · exact hVKem r hr'
    unfold finishAuthHybridRecvNoOPK
    cases res? with
    | none =>
      exact ⟨⟨hVP, hVS, hVO, hVSess⟩, hSessLe, hIdealLe, hSentOPKLe, hSentNoOPKLe, hVKem'⟩
    | some r =>
      rcases r with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩
      dsimp only
      cases findHonestPrincipal P hst.toAuthHybridState.base.principals msg.hdr.ikAPk with
      | none =>
        exact ⟨⟨hVP, hVS, hVO, hVSess⟩, hSessLe, hIdealLe, hSentOPKLe, hSentNoOPKLe, hVKem'⟩
      | some p =>
        rcases p with ⟨_, senderEntry⟩
        dsimp only
        cases senderEntry.corrupted
        · simp only [Bool.not_false, ↓reduceIte]
          refine ⟨⟨hVP, hVS, hVO, hVSess⟩, hSessLe, hIdealLe, hSentOPKLe, ?_, hVKem'⟩
          rw [consumeMatchingSentNoOPK_length]
          exact hSentNoOPKLe
        · exact ⟨⟨hVP, hVS, hVO, hVSess⟩, hSessLe, hIdealLe, hSentOPKLe, hSentNoOPKLe, hVKem'⟩

theorem authCkRecvWith_validAuthHybrid (S : Setup) (P : Primitives)
    (sampAt : Nat → ProbComp (Bytes × Bytes))
    (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecv S))
    (hst : AuthHybridStateFixed S) (hV : ValidAuthHybrid S P hst)
    (hFinish : ∀ prep, prep? = some prep → ∀ res? recvCount',
      ValidAuthHybrid S P { toAuthHybridState := (prep.finish res?).2, recvCount := recvCount' }) :
    ∀ x ∈ support (authCkRecvWith S P sampAt msg prep? hst), ValidAuthHybrid S P x.2 := by
  unfold authCkRecvWith
  cases prep? with
  | none =>
    intro x hx; simp at hx; subst hx
    exact ⟨hV.validEc, hV.sess_le, hV.ideal_le, hV.sentOPK_le, hV.sentNoOPK_le, hV.validKem⟩
  | some prep =>
    have hF := hFinish prep rfl
    dsimp only
    split
    · cases prep.matchedSess? with
      | some s =>
        dsimp only
        split
        · cases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
          | none =>
            intro x hx; simp at hx; subst hx; exact hF none _
          | some pqr =>
            intro x hx; simp [finishAuthRecvCk] at hx; subst hx; exact hF _ _
        · intro x hx
          simp only [MonadAttach.mem_support_bind] at hx
          rcases hx with ⟨rk1, _, hx⟩
          cases hSpqr : P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg <;> rw [hSpqr] at hx
          · simp at hx; subst hx; exact hF none _
          · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
            rcases hx with ⟨p, _, rfl⟩
            exact hF _ _
      | none =>
        dsimp only
        intro x hx
        simp only [MonadAttach.mem_support_bind] at hx
        rcases hx with ⟨drKey, _, rk1, _, hx⟩
        cases hSpqr : P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg <;> rw [hSpqr] at hx
        · simp at hx; subst hx; exact hF none _
        · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
          rcases hx with ⟨p, _, rfl⟩
          exact hF _ _
    · intro x hx
      simp only [MonadAttach.mem_support_bind] at hx
      rcases hx with ⟨⟨drKey, roCache'⟩, _, ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩, _, hx⟩
      cases hSpqr : P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg <;> rw [hSpqr] at hx
      · simp at hx; subst hx; exact hF none _
      · simp only [support_pure, Set.mem_singleton_iff] at hx
        subst hx
        exact hF _ _

theorem authCkStepWith_validAuthHybrid (S : Setup) (P : Primitives)
    (sampAt : Nat → ProbComp (Bytes × Bytes))
    (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (hV : ValidAuthHybrid S P hst) :
    ∀ x ∈ support (authCkStepWith S P sampAt q hst), ValidAuthHybrid S P x.2 := by
  cases q with
  | sendOPK u i bundle m0 m1 =>
    unfold authCkStepWith; dsimp only
    split
    · intro x hx; simp at hx; subst hx; exact hV
    · exact authCkSendWith_validAuthHybrid S P sampAt (.sendOPK u i) trivial u bundle m0 m1 hst hV
  | sendNoOPK u i bundle m0 m1 =>
    unfold authCkStepWith; dsimp only
    split
    · intro x hx; simp at hx; subst hx; exact hV
    · exact authCkSendWith_validAuthHybrid S P sampAt (.sendNoOPK u i) trivial u bundle m0 m1 hst hV
  | recvOPK k j o msg =>
    unfold authCkStepWith; dsimp only
    exact authCkRecvWith_validAuthHybrid S P sampAt msg _ hst hV
      (fun prep hPrep res? recvCount' =>
        prepareAuthHybridRecvOPK_validAuthHybrid P k j o msg hst hV prep hPrep res? recvCount')
  | recvNoOPK k j l msg =>
    unfold authCkStepWith; dsimp only
    exact authCkRecvWith_validAuthHybrid S P sampAt msg _ hst hV
      (fun prep hPrep res? recvCount' =>
        prepareAuthHybridRecvNoOPK_validAuthHybrid P k j l msg hst hV prep hPrep res? recvCount')
  | initPrin u =>
    unfold authCkStepWith authCkOtherStep pqxdhAuthImpl; dsimp only
    split; · intro x hx; simp at hx; subst hx; exact hV
    rcases hV with ⟨⟨hVP, hVS, hVO, hVSess⟩, hSessLe, hIdealLe, hSentOPKLe, hSentNoOPKLe, hVKem⟩
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases hFresh : hst.toAuthHybridState.base.principals.any (fun (idx, _) => idx == u.val)
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind]
      intro x hx
      simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
      rcases hx with ⟨secIKA0, _, secIKAsign, _, rfl⟩
      exact ⟨⟨(validPrincipals_cons S u _ hst.toAuthHybridState.base.principals hVP hFresh).1,
        hVS, hVO, hVSess⟩, hSessLe, hIdealLe, hSentOPKLe, hSentNoOPKLe, hVKem⟩
    · simp only [↓reduceIte, StateT.run_pure, pure_bind]
      intro x hx; simp at hx; subst hx
      exact ⟨⟨hVP, hVS, hVO, hVSess⟩, hSessLe, hIdealLe, hSentOPKLe, hSentNoOPKLe, hVKem⟩
  | corruptIK u =>
    unfold authCkStepWith authCkOtherStep pqxdhAuthImpl; dsimp only
    split; · intro x hx; simp at hx; subst hx; exact hV
    rcases hV with ⟨⟨hVP, hVS, hVO, hVSess⟩, hSessLe, hIdealLe, hSentOPKLe, hSentNoOPKLe, hVKem⟩
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases hst.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == u.val) with
    | none =>
      intro x hx; simp at hx; subst hx
      exact ⟨⟨hVP, hVS, hVO, hVSess⟩, hSessLe, hIdealLe, hSentOPKLe, hSentNoOPKLe, hVKem⟩
    | some p =>
      rcases p with ⟨_, entry⟩
      dsimp only
      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
      have h_corr := validPrincipals_map_corrupted S P u.val
        hst.toAuthHybridState.base.principals hVP
      intro x hx
      simp only [support_pure, Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨⟨h_corr.1, hVS, hVO, hVSess⟩, hSessLe, hIdealLe, hSentOPKLe, hSentNoOPKLe, hVKem⟩
  | genSPK u j =>
    unfold authCkStepWith authCkOtherStep pqxdhAuthImpl; dsimp only
    split; · intro x hx; simp at hx; subst hx; exact hV
    rcases hV with ⟨⟨hVP, hVS, hVO, hVSess⟩, hSessLe, hIdealLe, hSentOPKLe, hSentNoOPKLe, hVKem⟩
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases hFresh : hst.toAuthHybridState.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases hst.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none =>
        intro x hx; simp at hx; subst hx
        exact ⟨⟨hVP, hVS, hVO, hVSess⟩, hSessLe, hIdealLe, hSentOPKLe, hSentNoOPKLe, hVKem⟩
      | some p =>
        rcases p with ⟨_, uEntry⟩
        dsimp only
        simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
          StateT.run_pure, bind_assoc, pure_bind]
        intro x hx
        simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
        rcases hx with ⟨spkSk, _, rSpk, _, ⟨pqspkPk, pqspkSk⟩, _, rPq, _, rfl⟩
        exact ⟨⟨hVP,
          (validSpkBundles_cons S u j _ hst.toAuthHybridState.base.spkBundles hVS hFresh).1,
          hVO, hVSess⟩, hSessLe, hIdealLe, hSentOPKLe, hSentNoOPKLe, hVKem⟩
    · simp only [↓reduceIte, StateT.run_pure, pure_bind]
      intro x hx; simp at hx; subst hx
      exact ⟨⟨hVP, hVS, hVO, hVSess⟩, hSessLe, hIdealLe, hSentOPKLe, hSentNoOPKLe, hVKem⟩
  | genOPK u j o =>
    unfold authCkStepWith authCkOtherStep pqxdhAuthImpl; dsimp only
    split; · intro x hx; simp at hx; subst hx; exact hV
    rcases hV with ⟨⟨hVP, hVS, hVO, hVSess⟩, hSessLe, hIdealLe, hSentOPKLe, hSentNoOPKLe, hVKem⟩
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases hFresh : hst.toAuthHybridState.base.opkEntries.any
      (fun (k, _) => k == (u.val, j.val, o.val))
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind]
      intro x hx
      simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
      rcases hx with ⟨opkSk, _, rfl⟩
      exact ⟨⟨hVP, hVS,
        (validOpkEntries_cons S u j o _ hst.toAuthHybridState.base.opkEntries hVO hFresh).1,
        hVSess⟩, hSessLe, hIdealLe, hSentOPKLe, hSentNoOPKLe, hVKem⟩
    · simp only [↓reduceIte, StateT.run_pure, pure_bind]
      intro x hx; simp at hx; subst hx
      exact ⟨⟨hVP, hVS, hVO, hVSess⟩, hSessLe, hIdealLe, hSentOPKLe, hSentNoOPKLe, hVKem⟩
  | registerKey sk =>
    unfold authCkStepWith authCkOtherStep pqxdhAuthImpl registerAdvKey; dsimp only
    split; · intro x hx; simp at hx; subst hx; exact hV
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split <;> (intro x hx; simp at hx; subst hx; exact ⟨hV.validEc, hV.sess_le,
      hV.ideal_le, hV.sentOPK_le, hV.sentNoOPK_le, hV.validKem⟩)
  | roQuery secrets =>
    unfold authCkStepWith authCkOtherStep pqxdhAuthImpl; dsimp only
    split; · intro x hx; simp at hx; subst hx; exact hV
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      StateT.run_set, StateT.run_pure, bind_assoc, pure_bind]
    intro x hx
    simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
    rcases hx with ⟨_, _, rfl⟩
    exact ⟨hV.validEc, hV.sess_le, hV.ideal_le, hV.sentOPK_le, hV.sentNoOPK_le, hV.validKem⟩
  | roRootQuery rk dh =>
    unfold authCkStepWith authCkOtherStep pqxdhAuthImpl; dsimp only
    split; · intro x hx; simp at hx; subst hx; exact hV
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      StateT.run_set, StateT.run_pure, bind_assoc, pure_bind]
    intro x hx
    simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
    rcases hx with ⟨_, _, rfl⟩
    exact ⟨hV.validEc, hV.sess_le, hV.ideal_le, hV.sentOPK_le, hV.sentNoOPK_le, hV.validKem⟩
  | revealDhSecrets =>
    unfold authCkStepWith authCkOtherStep pqxdhAuthImpl; dsimp only
    split; · intro x hx; simp at hx; subst hx; exact hV
    intro x hx; simp at hx; subst hx; exact hV

@[simp] theorem runWithPrimStep_pure {ιI : Type} {GSpec : OracleSpec.{0, 0} ιI} {St α : Type}
    (step : (q : ιI) → St → OracleComp PrimBaseSpec (GSpec.Range q × St))
    (a : α) (st : St) :
    runWithPrimStep step (pure a) st = pure (a, st) := rfl

theorem runWithPrimStep_query_bind_inl {ιI : Type} {GSpec : OracleSpec.{0, 0} ιI} {St α : Type}
    (step : (q : ιI) → St → OracleComp PrimBaseSpec (GSpec.Range q × St))
    (uq : unifSpec.Domain)
    (k : (unifSpec + GSpec).Range (Sum.inl uq) → OracleComp (unifSpec + GSpec) α)
    (st : St) :
    runWithPrimStep step (liftM (OracleSpec.query (Sum.inl uq)) >>= k) st =
      (embedUnif (liftM (OracleSpec.query (spec := unifSpec) uq)) >>= fun u =>
        runWithPrimStep step (k u) st) := rfl

theorem runWithPrimStep_query_bind_inr {ιI : Type} {GSpec : OracleSpec.{0, 0} ιI} {St α : Type}
    (step : (q : ιI) → St → OracleComp PrimBaseSpec (GSpec.Range q × St))
    (gq : ιI)
    (k : (unifSpec + GSpec).Range (Sum.inr gq) → OracleComp (unifSpec + GSpec) α)
    (st : St) :
    runWithPrimStep step (liftM (OracleSpec.query (Sum.inr gq)) >>= k) st =
      (step gq st >>= fun x => runWithPrimStep step (k x.1) x.2) := rfl

theorem primBounded_runWithPrimStep {ιI : Type} {GSpec : OracleSpec.{0, 0} ιI} {St α : Type}
    (step : (q : ιI) → St → OracleComp PrimBaseSpec (GSpec.Range q × St))
    (stepCost : Nat)
    (hStep : ∀ q s, PrimBounded (step q s) stepCost)
    (mx : OracleComp (unifSpec + GSpec) α) (qTotal : Nat)
    (hMx : OracleComp.IsQueryBoundP mx (fun q => isGameQuery q = true) qTotal)
    (st : St) :
    PrimBounded (runWithPrimStep step mx st) (qTotal * stepCost) := by
  induction mx using OracleComp.inductionOn generalizing qTotal st with
  | pure a =>
    rw [runWithPrimStep_pure]
    exact primBounded_pure'
  | query_bind q k ih =>
    rw [isQueryBoundP_query_bind_iff] at hMx
    rcases q with uq | gq
    · rcases hMx with ⟨_, hCont⟩
      simp only [isGameQuery, Bool.false_eq_true, ↓reduceIte] at hCont
      rw [runWithPrimStep_query_bind_inl]
      exact primBounded_bind_le (qTotal * stepCost)
        (primBounded_embedUnif _ 0)
        (fun u => ih u qTotal (hCont u) st)
        (by omega)
    · rcases hMx with ⟨hFirst, hCont⟩
      have hPos : 0 < qTotal := by
        rcases hFirst with hAbs | hPos
        · exfalso; exact hAbs rfl
        · exact hPos
      simp only [isGameQuery, ↓reduceIte] at hCont
      rw [runWithPrimStep_query_bind_inr]
      have hMul : stepCost + (qTotal - 1) * stepCost ≤ qTotal * stepCost := by
        have hEq : (qTotal - 1) + 1 = qTotal := Nat.sub_add_cancel hPos
        calc stepCost + (qTotal - 1) * stepCost
            = ((qTotal - 1) + 1) * stepCost := by ring
          _ = qTotal * stepCost := by rw [hEq]
          _ ≤ qTotal * stepCost := le_rfl
      exact primBounded_bind_le ((qTotal - 1) * stepCost)
        (hStep gq st)
        (fun x => ih x.1 (qTotal - 1) (hCont x.1) x.2)
        hMul

theorem simulateQ_runWithPrimStep {ιI : Type} {GSpec : OracleSpec.{0, 0} ιI} {St α : Type}
    (P : Primitives)
    (step : (q : ιI) → St → OracleComp PrimBaseSpec (GSpec.Range q × St))
    (mx : OracleComp (unifSpec + GSpec) α) (st : St) :
    simulateQ (primBaseImpl P) (runWithPrimStep step mx st) =
      (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) +
        (fun gq => StateT.mk (fun s => simulateQ (primBaseImpl P) (step gq s)))) mx).run st := by
  induction mx using OracleComp.inductionOn generalizing st with
  | pure a =>
    simp [runWithPrimStep_pure, simulateQ_pure, StateT.run_pure]
  | query_bind q k ih =>
    rcases q with uq | gq
    · rw [runWithPrimStep_query_bind_inl, simulateQ_bind, simulateQ_embedUnif,
          simulateQ_run_query_inl_local]
      congr 1; funext u
      exact ih u st
    · rw [runWithPrimStep_query_bind_inr, simulateQ_bind, simulateQ_run_query_inr_local]
      congr 1; funext x
      exact ih x.1 x.2

theorem simulateQ_proj_inv_obs {ι α St1 St2 : Type}
    {QSpec : OracleSpec.{0, 0} ι}
    (proj : St1 → St2)
    (Inv : St1 → Prop)
    (impl1 : QueryImpl QSpec (StateT St1 ProbComp))
    (impl2 : QueryImpl QSpec (StateT St2 ProbComp))
    (hStep : ∀ (gq : ι) (st : St1), Inv st →
      ((impl2 gq).run (proj st) = Prod.map id proj <$> (impl1 gq).run st) ∧
      (∀ x ∈ support ((impl1 gq).run st), Inv x.2))
    (oa : OracleComp (unifSpec + QSpec) α)
    (st : St1) (hInv : Inv st)
    (obs1 : α × St1 → ProbComp Bool)
    (obs2 : α × St2 → ProbComp Bool)
    (hObs : ∀ x : α × St1, Inv x.2 → obs2 (x.1, proj x.2) = obs1 x) :
    let full1 := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St1 ProbComp) + impl1
    let full2 := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St2 ProbComp) + impl2
    ((simulateQ full2 oa).run (proj st) >>= obs2) =
      ((simulateQ full1 oa).run st >>= obs1) := by
  intro full1 full2
  induction oa using OracleComp.inductionOn generalizing st with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, pure_bind]
    exact hObs (a, st) hInv
  | query_bind q mx ih =>
    rcases q with uq | gq
    · rw [simulateQ_run_query_inl_local, simulateQ_run_query_inl_local,
          bind_assoc, bind_assoc]
      congr 1; funext u
      exact ih u st hInv
    · obtain ⟨hStepEq, hStepSupp⟩ := hStep gq st hInv
      rw [simulateQ_run_query_inr_local, simulateQ_run_query_inr_local,
          bind_assoc, bind_assoc, hStepEq, bind_map_left]
      refine bind_congr_of_support ((impl1 gq).run st) _ _ (fun x hx => ?_)
      exact ih x.1 x.2 (hStepSupp x hx)

theorem primBounded_authCkPreSampleRunPrim (S : Setup) (idx : Nat)
    (p : Bytes × Bytes) (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    PrimBounded (authCkPreSampleRunPrim S idx p A.1)
      (b.q_total * (S.N_dh * 26 + 21) + S.N_dh * 5) := by
  unfold authCkPreSampleRunPrim
  refine primBounded_bind_le (b.q_total * (S.N_dh * 26 + 21) + S.N_dh * 5)
    (primBounded_embedUnif ($ᵗ Bool) 0)
    (fun secb => ?_) (by omega)
  refine primBounded_bind_le (S.N_dh * 5)
    (primBounded_runWithPrimStep
      (authCkStepWithPrim S (sampAtCkPrim idx p))
      (S.N_dh * 26 + 21)
      (fun q s => primBounded_authCkStepWithPrim S (sampAtCkPrim idx p)
        (primBounded_sampAtCkPrim idx p) q s)
      A.1.run b.q_total (SignalPqxdh.QueryBounded.auth_total A.2)
      (AuthHybridStateFixed.empty S secb))
    (fun ⟨b', finalSt⟩ => primBounded_finalizeAuthFixedPrim S secb b' finalSt.toAuthHybridState)
    (by omega)

theorem prfCkReductionAuthFixed_bounded (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    (prfCkReductionAuthFixed S b A).Bounded := fun mkSeedChal ck1_1Chal =>
  primBounded_bind_le (b.q_total * (S.N_dh * 26 + 21) + S.N_dh * 5)
    (primBounded_embedUnif (sampleIndexRange (min b.q_total S.N_sess_tot)) 0)
    (fun idx => primBounded_authCkPreSampleRunPrim S idx (mkSeedChal, ck1_1Chal) b A)
    (by dsimp [prfCkReductionAuthFixed]; omega)

theorem prfCkReductionAuthFixed_prim_queries (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    (prfCkReductionAuthFixed S b A).q_prim ≤ primQueryBudget S b := by
  dsimp [prfCkReductionAuthFixed, primQueryBudget]
  nlinarith

private def projSlots0 {S : Setup} (hst : AuthHybridStateFixed S) : AuthHybridStateFixed S :=
  { hst with slots := {} }

private def authCkSlotsSendSlot (S : Setup) (P : Primitives) (idx : Nat)
    (samp : ProbComp (Bytes × Bytes)) (sid : SessionId S) (u : Fin S.N_id)
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes) (hst : AuthHybridStateFixed S) :
    SlotM (Bytes × Bytes) (AuthResponse × AuthHybridStateFixed S) := do
  let st := hst.toAuthHybridState.base
  if st.hasWonAuth then pure (.noneResp, hst)
  else if m0.length != m1.length then pure (.noneResp, hst)
  else if st.usedSendSessions.contains sid then pure (.noneResp, hst)
  else
    match st.principals.find? (fun (idx, _) => idx == u.val) with
    | none => pure (.noneResp, hst)
    | some (_, uEntry) =>
      let peerPrincipal? := findHonestPrincipal P st.principals bundle.ikB
      let isFreshPeer : Bool :=
        match peerPrincipal? with | some (_, pEntry) => !pEntry.corrupted | none => false
      if !isFreshPeer && m0 != m1 then pure (.noneResp, hst)
      else
        let msgPlain := if isFreshPeer then (if st.secb then m1 else m0) else m0
        if !koskBundleOk P st.principals st.spkBundles st.opkEntries st.advKeys bundle then
          pure (.noneResp, hst)
        else
          let ekASk ← (liftM sampleScalar32 : SlotM (Bytes × Bytes) Bytes)
          let kemCoins ← (liftM sampleCoins32 : SlotM (Bytes × Bytes) Bytes)
          let ephASk ← (liftM sampleScalar32 : SlotM (Bytes × Bytes) Bytes)
          let spqrCoins ← (liftM sampleCoins32 : SlotM (Bytes × Bytes) Bytes)
          let sigPkB := resolveSigPk P st.principals bundle.ikB
          if !(P.sigVerify sigPkB (encodeEC bundle.spkB) bundle.spkSig &&
               P.sigVerify sigPkB (encodeKEM bundle.pqspkB) bundle.pqspkSig) then
            pure (.noneResp, hst)
          else
            match P.kemEncaps bundle.pqspkB kemCoins with
            | none => pure (.noneResp, hst)
            | some (ss, kemCt) =>
              let ekAPk := P.x25519Base ekASk
              let ephAPk := P.x25519Base ephASk
              let prov := checkBundleProvenanceExact P st.principals st.spkBundles st.opkEntries bundle
              let spkHonIdeal := checkBundleSpkHonIdeal P st.principals st.spkBundles bundle
              let isIdealSend : Bool := isFreshPeer || (peerPrincipal?.isSome && spkHonIdeal && prov.2.2)
              if isIdealSend then
                let drKey ← (liftM sampleDRKey96 : SlotM (Bytes × Bytes) DRKey)
                let rk1 ← (liftM sampleBytes32 : SlotM (Bytes × Bytes) Bytes)
                match P.spqrInitSend drKey.pqrKey spqrCoins with
                | none => pure (.noneResp, hst)
                | some (_pqrStA, spqrSalt?, pqRatchetMsg) =>
                  let (sIdx, slots') := hst.slots.allocSend sid
                  let p ← getCkAtSlot idx samp P sIdx
                  pure (finishAuthSendCkSlots P sid uEntry peerPrincipal? bundle m0 m1
                    ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 spqrSalt?
                    pqRatchetMsg msgPlain { hst with slots := slots' } p)
              else
                let dh1 := P.x25519 uEntry.secIKA0 bundle.spkB
                let dh2 := P.x25519 ekASk bundle.ikB
                let dh3 := P.x25519 ekASk bundle.spkB
                let dh4? := bundle.opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk)
                let secrets := buildSecrets dh1 dh2 dh3 dh4? ss
                let (drKey, roCache') ← liftM (evalHkdfOrRo true P st.roCache secrets)
                let dhRatchet := P.x25519 ephASk bundle.spkB
                let ((rk1, ck1_0), rootRoCache') ←
                  liftM (evalRootKdfOrRo true P st.rootRoCache drKey.rootKey dhRatchet)
                let mkSeed := P.chainKdfSeed ck1_0
                let ck1_1 := P.chainKdfNext ck1_0
                match P.spqrInitSend drKey.pqrKey spqrCoins with
                | none => pure (.noneResp, hst)
                | some (_pqrStA, spqrSalt?, pqRatchetMsg) =>
                  let deriveMessageKeys := P.deriveMsgKeys mkSeed spqrSalt?
                  let ad := firstMsgAD uEntry.ikAPk bundle.ikB ephAPk pqRatchetMsg
                  let aeadCt := P.aeadEnc deriveMessageKeys ad msgPlain
                  let (resp, hst') := finishAuthHybridSend P sid uEntry peerPrincipal? isFreshPeer
                    bundle m0 m1 ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 ck1_0 mkSeed ck1_1
                    spqrSalt? pqRatchetMsg deriveMessageKeys ad aeadCt msgPlain roCache' rootRoCache'
                    hst.toAuthHybridState
                  pure (resp, { toAuthHybridState := hst', recvCount := hst.recvCount, slots := hst.slots })

private def authCkSlotsRecvSlot (S : Setup) (P : Primitives) (idx : Nat)
    (samp : ProbComp (Bytes × Bytes)) (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecv S))
    (hst : AuthHybridStateFixed S) :
    SlotM (Bytes × Bytes) (AuthResponse × AuthHybridStateFixed S) := do
  let recvCount' := hst.recvCount + 1
  match prep? with
  | none => pure (.noneResp, { hst with recvCount := recvCount' })
  | some prep =>
    let st := prep.hstDec.base
    let useIdealBranch : Bool := prep.matchedSess?.isSome || prep.isUncorruptedHonestSender
    if useIdealBranch then
      match prep.matchedSess? with
      | some s =>
        if prep.sameEph then
          match P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
          | none =>
            let (resp, hst') := prep.finish none
            pure (resp, { toAuthHybridState := hst', recvCount := recvCount', slots := hst.slots })
          | some (_pqrStB, spqrSalt?) =>
            pure (finishAuthRecvCkSlots P msg prep s.drKey s.rk1 spqrSalt? recvCount'
              (s.mkSeed, s.ck1_1) hst.slots)
        else
          let rk1 ← (liftM sampleBytes32 : SlotM (Bytes × Bytes) Bytes)
          match P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
          | none =>
            let (resp, hst') := prep.finish none
            pure (resp, { toAuthHybridState := hst', recvCount := recvCount', slots := hst.slots })
          | some (_pqrStB, spqrSalt?) =>
            let (rSlot, slots') := hst.slots.allocRecv hst.recvCount
            let p ← getCkAtSlot idx samp P rSlot
            pure (finishAuthRecvCkSlots P msg prep s.drKey rk1 spqrSalt? recvCount' p slots')
      | none =>
        let drKey ← (liftM sampleDRKey96 : SlotM (Bytes × Bytes) DRKey)
        let rk1 ← (liftM sampleBytes32 : SlotM (Bytes × Bytes) Bytes)
        match P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
        | none =>
          let (resp, hst') := prep.finish none
          pure (resp, { toAuthHybridState := hst', recvCount := recvCount', slots := hst.slots })
        | some (_pqrStB, spqrSalt?) =>
          let (rSlot, slots') := hst.slots.allocRecv hst.recvCount
          let p ← getCkAtSlot idx samp P rSlot
          pure (finishAuthRecvCkSlots P msg prep drKey rk1 spqrSalt? recvCount' p slots')
    else
      let (drKey, roCache') ← liftM (evalHkdfOrRo true P st.roCache prep.secrets)
      let ((rk1, ck1_0), rootRoCache') ←
        liftM (evalRootKdfOrRo true P st.rootRoCache drKey.rootKey prep.dhRatchet)
      let mkSeed := P.chainKdfSeed ck1_0
      let ck1_1 := P.chainKdfNext ck1_0
      match P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
      | none =>
        let (resp, hst') := prep.finish none
        pure (resp, { toAuthHybridState := hst', recvCount := recvCount', slots := hst.slots })
      | some (_pqrStB, spqrSalt?) =>
        let deriveMessageKeys := P.deriveMsgKeys mkSeed spqrSalt?
        let ad := firstMsgAD msg.hdr.ikAPk prep.kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg
        let res? := (P.aeadDec deriveMessageKeys ad msg.aeadCt).map (fun pt =>
          (drKey, rk1, ck1_1, pt, roCache', rootRoCache'))
        let (resp, hst') := prep.finish res?
        pure (resp, { toAuthHybridState := hst', recvCount := recvCount', slots := hst.slots })

private def authCkSlotsStepWith (S : Setup) (P : Primitives) (sampAt : Nat → ProbComp (Bytes × Bytes))
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    ProbComp ((authSpec S).Range q × AuthHybridStateFixed S) :=
  match q with
  | .sendOPK u i bundle m0 m1 =>
    if bundle.opkB?.isNone then pure (.noneResp, hst)
    else authCkSendWithSlots S P sampAt (.sendOPK u i) u bundle m0 m1 hst
  | .sendNoOPK u i bundle m0 m1 =>
    if bundle.opkB?.isSome then pure (.noneResp, hst)
    else authCkSendWithSlots S P sampAt (.sendNoOPK u i) u bundle m0 m1 hst
  | .recvOPK k j o msg =>
    authCkRecvWithSlots S P sampAt msg (prepareAuthHybridRecvOPK true P k j o msg hst.toAuthHybridState) hst
  | .recvNoOPK k j l msg =>
    authCkRecvWithSlots S P sampAt msg (prepareAuthHybridRecvNoOPK true P k j l msg hst.toAuthHybridState) hst
  | qOther => authCkOtherStep S P qOther hst

private def authCkSlotsStepSlot (S : Setup) (P : Primitives) (idx : Nat)
    (samp : ProbComp (Bytes × Bytes)) (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    SlotM (Bytes × Bytes) ((authSpec S).Range q × AuthHybridStateFixed S) :=
  match q with
  | .sendOPK u i bundle m0 m1 =>
    if bundle.opkB?.isNone then pure (.noneResp, hst)
    else authCkSlotsSendSlot S P idx samp (.sendOPK u i) u bundle m0 m1 hst
  | .sendNoOPK u i bundle m0 m1 =>
    if bundle.opkB?.isSome then pure (.noneResp, hst)
    else authCkSlotsSendSlot S P idx samp (.sendNoOPK u i) u bundle m0 m1 hst
  | .recvOPK k j o msg =>
    authCkSlotsRecvSlot S P idx samp msg (prepareAuthHybridRecvOPK true P k j o msg hst.toAuthHybridState) hst
  | .recvNoOPK k j l msg =>
    authCkSlotsRecvSlot S P idx samp msg (prepareAuthHybridRecvNoOPK true P k j l msg hst.toAuthHybridState) hst
  | qOther => liftM (authCkOtherStep S P qOther hst)

private noncomputable def authCkSlotsPreSampleRun (S : Setup) (P : Primitives) (idx : Nat)
    (p : Bytes × Bytes) (A : AuthAdversary S) : ProbComp Bool := do
  let secb ← $ᵗ Bool
  let stepImpl : QueryImpl (authSpec S) (StateT (AuthHybridStateFixed S) ProbComp) :=
    fun q => StateT.mk (fun hst =>
      authCkSlotsStepWith S P (fun s => if s == idx then pure p else sampCkPair P (s < idx)) q hst)
  let fullImpl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (AuthHybridStateFixed S) ProbComp) + stepImpl
  let (b', finalSt) ← (simulateQ fullImpl A.run).run (AuthHybridStateFixed.empty S secb)
  finalizeAuthFixed P secb b' finalSt.toAuthHybridState

private noncomputable def authCkSlotsCutoffExp (S : Setup) (P : Primitives) (cutoff : Nat)
    (A : AuthAdversary S) : ProbComp Bool := do
  let secb ← $ᵗ Bool
  let stepImpl : QueryImpl (authSpec S) (StateT (AuthHybridStateFixed S) ProbComp) :=
    fun q => StateT.mk (fun hst => authCkSlotsStepWith S P (fun s => sampCkPair P (s < cutoff)) q hst)
  let fullImpl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (AuthHybridStateFixed S) ProbComp) + stepImpl
  let (b', finalSt) ← (simulateQ fullImpl A.run).run (AuthHybridStateFixed.empty S secb)
  finalizeAuthFixed P secb b' finalSt.toAuthHybridState

private theorem map_ite_eq {α β : Type} (f : α → β) (c : Bool)
    (t1 e1 : ProbComp α) (t2 e2 : ProbComp β)
    (ht : f <$> t1 = t2) (he : f <$> e1 = e2) :
    f <$> (if c then t1 else e1) = if c then t2 else e2 := by cases c <;> assumption

private theorem map_projSlots0_authCkSendWithSlots (S : Setup) (P : Primitives)
    (sampAt1 sampAt2 : Nat → ProbComp (Bytes × Bytes))
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S)
    (hSampEq : ¬hst.toAuthHybridState.base.usedSendSessions.contains sid →
      sampAt1 (hst.slots.allocSend sid).1 = sampAt2 (sessionSlotIndex sid)) :
    Prod.map id projSlots0 <$> authCkSendWithSlots S P sampAt1 sid u bundle m0 m1 hst =
      authCkSendWith S P sampAt2 sid u bundle m0 m1 (projSlots0 hst) := by
  unfold authCkSendWithSlots authCkSendWith projSlots0; dsimp only
  refine map_ite_eq _ _ _ _ _ _ (by simp only [map_pure, Prod.map, id_eq]) ?_
  refine map_ite_eq _ _ _ _ _ _ (by simp only [map_pure, Prod.map, id_eq]) ?_
  cases hUsed : hst.toAuthHybridState.base.usedSendSessions.contains sid
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hSE := hSampEq (Bool.eq_false_iff.mp hUsed)
    cases hst.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == u.val) with
    | none => simp only [map_pure, Prod.map, id_eq]
    | some uPair =>
      rcases uPair with ⟨_, uEntry⟩; dsimp only
      refine map_ite_eq _ _ _ _ _ _ (by simp only [map_pure, Prod.map, id_eq]) ?_
      refine map_ite_eq _ _ _ _ _ _ (by simp only [map_pure, Prod.map, id_eq]) ?_
      simp only [map_bind]
      congr 1; funext ekASk; congr 1; funext kemCoins; congr 1; funext ephASk; congr 1; funext spqrCoins
      refine map_ite_eq _ _ _ _ _ _ (by simp only [map_pure, Prod.map, id_eq]) ?_
      cases P.kemEncaps bundle.pqspkB kemCoins with
      | none => simp only [map_pure, Prod.map, id_eq]
      | some pair =>
        rcases pair with ⟨ss, kemCt⟩; dsimp only
        refine map_ite_eq _ _ _ _ _ _ ?_ ?_
        · simp only [map_bind]; congr 1; funext drKey; congr 1; funext rk1
          cases P.spqrInitSend drKey.pqrKey spqrCoins with
          | none => simp only [map_pure, Prod.map, id_eq]
          | some spqrVal =>
            rcases spqrVal with ⟨_, spqrSalt?, pqRatchetMsg⟩; dsimp only; rw [hSE]
            simp only [map_bind, map_pure]; congr 1
        · simp only [map_bind]; congr 1; funext ⟨drKey, roCache'⟩; congr 1; funext ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
          cases P.spqrInitSend drKey.pqrKey spqrCoins with
          | none => simp only [map_pure, Prod.map, id_eq]
          | some spqrVal => rcases spqrVal with ⟨_, spqrSalt?, pqRatchetMsg⟩; rw [map_pure]; rfl
  · simp only [↓reduceIte, map_pure, Prod.map, id_eq]

private theorem map_projSlots0_authCkRecvWithSlots (S : Setup) (P : Primitives)
    (sampAt1 sampAt2 : Nat → ProbComp (Bytes × Bytes))
    (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecv S)) (hst : AuthHybridStateFixed S)
    (hSampEq : sampAt1 (hst.slots.allocRecv hst.recvCount).1 = sampAt2 (S.N_send_tot + hst.recvCount)) :
    Prod.map id projSlots0 <$> authCkRecvWithSlots S P sampAt1 msg prep? hst =
      authCkRecvWith S P sampAt2 msg prep? (projSlots0 hst) := by
  unfold authCkRecvWithSlots authCkRecvWith projSlots0
  cases prep? with
  | none => simp only [map_pure, Prod.map, id_eq]
  | some prep =>
    dsimp only
    cases (prep.matchedSess?.isSome || prep.isUncorruptedHonestSender) <;>
      simp only [Bool.false_eq_true, ↓reduceIte]
    · simp only [map_bind]; congr 1; funext ⟨drKey, roCache'⟩; congr 1; funext ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
      cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
      | none => simp only [map_pure, Prod.map, id_eq]
      | some pqr => rcases pqr with ⟨_, spqrSalt?⟩; simp only [map_pure, Prod.map, id_eq]
    · cases prep.matchedSess? with
      | none =>
        simp only [map_bind]; congr 1; funext drKey; congr 1; funext rk1
        cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
        | none => simp only [map_pure, Prod.map, id_eq]
        | some pqr =>
          rcases pqr with ⟨_, spqrSalt?⟩; dsimp only; rw [hSampEq]
          simp only [map_bind, map_pure, Prod.map, id_eq, finishAuthRecvCkSlots, finishAuthRecvCk]
      | some s =>
        dsimp only
        cases prep.sameEph <;> simp only [Bool.false_eq_true, ↓reduceIte]
        · simp only [map_bind]; congr 1; funext rk1
          cases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
          | none => simp only [map_pure, Prod.map, id_eq]
          | some pqr =>
            rcases pqr with ⟨_, spqrSalt?⟩; dsimp only; rw [hSampEq]
            simp only [map_bind, map_pure, Prod.map, id_eq, finishAuthRecvCkSlots, finishAuthRecvCk]
        · cases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
          | none => simp only [map_pure, Prod.map, id_eq]
          | some pqr =>
            rcases pqr with ⟨_, spqrSalt?⟩
            simp only [map_pure, Prod.map, id_eq, finishAuthRecvCkSlots, finishAuthRecvCk]

private theorem map_projSlots0_authCkOtherStep (S : Setup) (P : Primitives)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    Prod.map id projSlots0 <$> authCkOtherStep S P q hst = authCkOtherStep S P q (projSlots0 hst) := by
  unfold authCkOtherStep projSlots0; dsimp only
  cases hst.toAuthHybridState.base.hasWonAuth <;>
    simp only [Bool.false_eq_true, ↓reduceIte, map_pure, map_bind, Prod.map, id_eq]

private theorem simulateQ_authCkSlotsStepWithPrim (S : Setup) (P : Primitives)
    (sampAt : Nat → OracleComp PrimBaseSpec (Bytes × Bytes))
    (sampAtPure : Nat → ProbComp (Bytes × Bytes))
    (hSamp : ∀ s, simulateQ (primBaseImpl P) (sampAt s) = sampAtPure s)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) (hV : ValidAuthHybrid S P hst) :
    simulateQ (primBaseImpl P) (authCkStepWithPrim S sampAt q (cacheAuthAdvKeysFixed P hst)) =
      Prod.map id (cacheAuthAdvKeysFixed P) <$> authCkSlotsStepWith S P sampAtPure q hst := by
  have hVC : ValidAuthHybrid S P (cacheAuthAdvKeysFixed P hst) :=
    (validAuthHybrid_cacheAuthAdvKeysFixed P hst).mpr hV
  have hAdv : ValidAdvKeysPow8 P (cacheAuthAdvKeysFixed P hst).toAuthHybridState.base.advKeys :=
    validAdvKeysPow8_cacheAuthAdvKeys P hst.toAuthHybridState
  cases q with
  | sendOPK u i bundle m0 m1 =>
    unfold authCkStepWithPrim authCkSlotsStepWith; dsimp only
    cases bundle.opkB?.isNone <;> simp only [Bool.false_eq_true, ↓reduceIte, simulateQ_pure, map_pure, Prod.map, id_eq]
    rw [simulateQ_authCkSendWithSlotsPrim S P sampAt sampAtPure hSamp (.sendOPK u i) u bundle m0 m1
          (cacheAuthAdvKeysFixed P hst) hVC.principals_le hVC.spkBundles_le hVC.opkEntries_le hAdv,
        authCkSendWithSlots_cacheAuthAdvKeysFixed]
  | sendNoOPK u i bundle m0 m1 =>
    unfold authCkStepWithPrim authCkSlotsStepWith; dsimp only
    cases bundle.opkB?.isSome <;> simp only [Bool.false_eq_true, ↓reduceIte, simulateQ_pure, map_pure, Prod.map, id_eq]
    rw [simulateQ_authCkSendWithSlotsPrim S P sampAt sampAtPure hSamp (.sendNoOPK u i) u bundle m0 m1
          (cacheAuthAdvKeysFixed P hst) hVC.principals_le hVC.spkBundles_le hVC.opkEntries_le hAdv,
        authCkSendWithSlots_cacheAuthAdvKeysFixed]
  | recvOPK k j o msg =>
    unfold authCkStepWithPrim authCkSlotsStepWith; dsimp only
    rw [simulateQ_bind, simulateQ_prepareAuthHybridRecvOPKPrim S P k j o msg
          (cacheAuthAdvKeysFixed P hst).toAuthHybridState hVC.principals_le hVC.idealSessions_le hAdv, pure_bind]
    have hPrep : ∀ prep,
        prepareAuthHybridRecvOPKPure P k j o msg (cacheAuthAdvKeys P hst.toAuthHybridState) = some prep →
        prep.finishTag.hstDec.base.sentOPKEvents.length ≤ S.N_dh ∧
        prep.finishTag.hstDec.base.sentNoOPKEvents.length ≤ S.N_dh ∧
        prep.finishTag.hstDec.base.principals.length ≤ S.N_dh := fun prep hSome => by
      obtain ⟨hTag, hBase⟩ := prepareAuthHybridRecvOPKPure_finishTag_base P k j o msg _ prep hSome
      rw [hTag, hBase]; exact ⟨hVC.sentOPKEvents_le, hVC.sentNoOPKEvents_le, hVC.principals_le⟩
    change simulateQ (primBaseImpl P) (authCkRecvWithPrim S sampAt msg
      (prepareAuthHybridRecvOPKPure P k j o msg (cacheAuthAdvKeys P hst.toAuthHybridState))
      (cacheAuthAdvKeysFixed P hst)) = _
    rw [simulateQ_authCkRecvWithSlotsPrim S P sampAt sampAtPure hSamp msg _ _ hPrep,
        prepareAuthHybridRecvOPKPure_cacheAuthAdvKeys, authCkRecvWithSlots_cacheAuthAdvKeysFixed,
        ← prepareAuthHybridRecvOPKPure_map_toPure]
  | recvNoOPK k j l msg =>
    unfold authCkStepWithPrim authCkSlotsStepWith; dsimp only
    rw [simulateQ_bind, simulateQ_prepareAuthHybridRecvNoOPKPrim S P k j l msg
          (cacheAuthAdvKeysFixed P hst).toAuthHybridState hVC.principals_le hVC.idealSessions_le hAdv, pure_bind]
    have hPrep : ∀ prep,
        prepareAuthHybridRecvNoOPKPure P k j l msg (cacheAuthAdvKeys P hst.toAuthHybridState) = some prep →
        prep.finishTag.hstDec.base.sentOPKEvents.length ≤ S.N_dh ∧
        prep.finishTag.hstDec.base.sentNoOPKEvents.length ≤ S.N_dh ∧
        prep.finishTag.hstDec.base.principals.length ≤ S.N_dh := fun prep hSome => by
      obtain ⟨hTag, hBase⟩ := prepareAuthHybridRecvNoOPKPure_finishTag_base P k j l msg _ prep hSome
      rw [hTag, hBase]; exact ⟨hVC.sentOPKEvents_le, hVC.sentNoOPKEvents_le, hVC.principals_le⟩
    change simulateQ (primBaseImpl P) (authCkRecvWithPrim S sampAt msg
      (prepareAuthHybridRecvNoOPKPure P k j l msg (cacheAuthAdvKeys P hst.toAuthHybridState))
      (cacheAuthAdvKeysFixed P hst)) = _
    rw [simulateQ_authCkRecvWithSlotsPrim S P sampAt sampAtPure hSamp msg _ _ hPrep,
        prepareAuthHybridRecvNoOPKPure_cacheAuthAdvKeys, authCkRecvWithSlots_cacheAuthAdvKeysFixed,
        ← prepareAuthHybridRecvNoOPKPure_map_toPure]
  | initPrin u => exact simulateQ_stepAuthOtherPrim S P (.initPrin u) hst (fun h => nomatch h) (fun h => nomatch h)
  | corruptIK u => exact simulateQ_stepAuthOtherPrim S P (.corruptIK u) hst (fun h => nomatch h) (fun h => nomatch h)
  | genSPK u j => exact simulateQ_stepAuthOtherPrim S P (.genSPK u j) hst (fun h => nomatch h) (fun h => nomatch h)
  | genOPK u j o => exact simulateQ_stepAuthOtherPrim S P (.genOPK u j o) hst (fun h => nomatch h) (fun h => nomatch h)
  | registerKey sk => exact simulateQ_stepAuthOtherPrim S P (.registerKey sk) hst (fun h => nomatch h) (fun h => nomatch h)
  | roQuery secrets => exact simulateQ_stepAuthOtherPrim S P (.roQuery secrets) hst (fun h => nomatch h) (fun h => nomatch h)
  | roRootQuery rk dh => exact simulateQ_stepAuthOtherPrim S P (.roRootQuery rk dh) hst (fun h => nomatch h) (fun h => nomatch h)
  | revealDhSecrets => exact simulateQ_stepAuthOtherPrim S P .revealDhSecrets hst (fun h => nomatch h) (fun h => nomatch h)

private theorem authCkSlotsStepWith_validAuthHybrid (S : Setup) (P : Primitives)
    (sampAt : Nat → ProbComp (Bytes × Bytes))
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) (hV : ValidAuthHybrid S P hst) :
    ∀ x ∈ support (authCkSlotsStepWith S P sampAt q hst), ValidAuthHybrid S P x.2 := by
  have hVP0 : ValidAuthHybrid S P (projSlots0 hst) := ⟨hV.1, hV.2, hV.3, hV.4, hV.5, hV.6⟩
  have hSendV : ∀ (sid : SessionId S), IsSendSessionId S sid → ∀ u bundle m0 m1,
      ∀ x ∈ support (authCkSendWithSlots S P sampAt sid u bundle m0 m1 hst), ValidAuthHybrid S P x.2 := by
    intro sid hSid u bundle m0 m1 x hx
    have hMem : Prod.map id projSlots0 x ∈
        support (Prod.map id projSlots0 <$> authCkSendWithSlots S P sampAt sid u bundle m0 m1 hst) := by
      rw [support_map]; exact ⟨x, hx, rfl⟩
    rw [map_projSlots0_authCkSendWithSlots S P sampAt (fun _ => sampAt (hst.slots.allocSend sid).1)
          sid u bundle m0 m1 hst (fun _ => rfl)] at hMem
    have hVPx := authCkSendWith_validAuthHybrid S P _ sid hSid u bundle m0 m1 (projSlots0 hst) hVP0 _ hMem
    exact ⟨hVPx.1, hVPx.2, hVPx.3, hVPx.4, hVPx.5, hVPx.6⟩
  cases q with
  | sendOPK u i bundle m0 m1 =>
    unfold authCkSlotsStepWith; dsimp only; split
    · intro x hx; simp at hx; subst hx; exact hV
    · exact hSendV (.sendOPK u i) trivial u bundle m0 m1
  | sendNoOPK u i bundle m0 m1 =>
    unfold authCkSlotsStepWith; dsimp only; split
    · intro x hx; simp at hx; subst hx; exact hV
    · exact hSendV (.sendNoOPK u i) trivial u bundle m0 m1
  | recvOPK k j o msg =>
    unfold authCkSlotsStepWith; dsimp only; intro x hx
    have hMem : Prod.map id projSlots0 x ∈ support (Prod.map id projSlots0 <$>
        authCkRecvWithSlots S P sampAt msg (prepareAuthHybridRecvOPK true P k j o msg hst.toAuthHybridState) hst) := by
      rw [support_map]; exact ⟨x, hx, rfl⟩
    rw [map_projSlots0_authCkRecvWithSlots S P sampAt (fun _ => sampAt (hst.slots.allocRecv hst.recvCount).1)
          msg _ hst rfl] at hMem
    have hVPx := authCkRecvWith_validAuthHybrid S P _ msg _ (projSlots0 hst) hVP0
      (fun prep hPrep res? rc' => prepareAuthHybridRecvOPK_validAuthHybrid P k j o msg (projSlots0 hst) hVP0 prep hPrep res? rc')
      _ hMem
    exact ⟨hVPx.1, hVPx.2, hVPx.3, hVPx.4, hVPx.5, hVPx.6⟩
  | recvNoOPK k j l msg =>
    unfold authCkSlotsStepWith; dsimp only; intro x hx
    have hMem : Prod.map id projSlots0 x ∈ support (Prod.map id projSlots0 <$>
        authCkRecvWithSlots S P sampAt msg (prepareAuthHybridRecvNoOPK true P k j l msg hst.toAuthHybridState) hst) := by
      rw [support_map]; exact ⟨x, hx, rfl⟩
    rw [map_projSlots0_authCkRecvWithSlots S P sampAt (fun _ => sampAt (hst.slots.allocRecv hst.recvCount).1)
          msg _ hst rfl] at hMem
    have hVPx := authCkRecvWith_validAuthHybrid S P _ msg _ (projSlots0 hst) hVP0
      (fun prep hPrep res? rc' => prepareAuthHybridRecvNoOPK_validAuthHybrid P k j l msg (projSlots0 hst) hVP0 prep hPrep res? rc')
      _ hMem
    exact ⟨hVPx.1, hVPx.2, hVPx.3, hVPx.4, hVPx.5, hVPx.6⟩
  | initPrin u => exact authCkStepWith_validAuthHybrid S P sampAt (.initPrin u) hst hV
  | corruptIK u => exact authCkStepWith_validAuthHybrid S P sampAt (.corruptIK u) hst hV
  | genSPK u j => exact authCkStepWith_validAuthHybrid S P sampAt (.genSPK u j) hst hV
  | genOPK u j o => exact authCkStepWith_validAuthHybrid S P sampAt (.genOPK u j o) hst hV
  | registerKey sk => exact authCkStepWith_validAuthHybrid S P sampAt (.registerKey sk) hst hV
  | roQuery secrets => exact authCkStepWith_validAuthHybrid S P sampAt (.roQuery secrets) hst hV
  | roRootQuery rk dh => exact authCkStepWith_validAuthHybrid S P sampAt (.roRootQuery rk dh) hst hV
  | revealDhSecrets => exact authCkStepWith_validAuthHybrid S P sampAt .revealDhSecrets hst hV

private theorem simulateQ_authCkSlotsPreSampleRunPrim (S : Setup) (P : Primitives)
    (idx : Nat) (p : Bytes × Bytes) (A : AuthAdversary S) :
    simulateQ (primBaseImpl P) (authCkPreSampleRunPrim S idx p A) =
      authCkSlotsPreSampleRun S P idx p A := by
  unfold authCkPreSampleRunPrim authCkSlotsPreSampleRun
  simp only [simulateQ_bind, simulateQ_embedUnif]; congr 1; funext secb
  rw [simulateQ_runWithPrimStep]
  have hInit : cacheAuthAdvKeysFixed P (AuthHybridStateFixed.empty S secb) =
      AuthHybridStateFixed.empty S secb := rfl
  conv_lhs => rw [← hInit]
  exact simulateQ_proj_inv_obs
    (cacheAuthAdvKeysFixed P) (ValidAuthHybrid S P)
    (fun q => StateT.mk (fun hst =>
      authCkSlotsStepWith S P (fun s => if s == idx then pure p else sampCkPair P (s < idx)) q hst))
    (fun q => StateT.mk (fun hst =>
      simulateQ (primBaseImpl P) (authCkStepWithPrim S (sampAtCkPrim idx p) q hst)))
    (fun q hst hV =>
      ⟨simulateQ_authCkSlotsStepWithPrim S P (sampAtCkPrim idx p)
        (fun s => if s == idx then pure p else sampCkPair P (s < idx))
        (simulateQ_sampAtCkPrim P idx p) q hst hV,
       authCkSlotsStepWith_validAuthHybrid S P
        (fun s => if s == idx then pure p else sampCkPair P (s < idx)) q hst hV⟩)
    A.run (AuthHybridStateFixed.empty S secb) (validAuthHybrid_empty S P secb)
    (fun x => finalizeAuthFixed P secb x.1 x.2.toAuthHybridState)
    (fun y => simulateQ (primBaseImpl P) (finalizeAuthFixedPrim S secb y.1 y.2.toAuthHybridState))
    (fun x hVx => by
      have hVC : ValidAuthHybrid S P (cacheAuthAdvKeysFixed P x.2) :=
        (validAuthHybrid_cacheAuthAdvKeysFixed P x.2).mpr hVx
      rw [simulateQ_finalizeAuthFixedPrim S P secb x.1
            (cacheAuthAdvKeysFixed P x.2).toAuthHybridState
            hVC.principals_le hVC.spkBundles_le hVC.opkEntries_le hVC.sessions_le hVC.validKem]
      exact finalizeAuthFixed_cacheAuthAdvKeys P secb x.1 x.2.toAuthHybridState)

private structure CkSlotWf (S : Setup) (hst : AuthHybridStateFixed S) : Prop where
  send_fresh : ∀ sid : SessionId S,
    hst.toAuthHybridState.base.usedSendSessions.contains sid = false →
    hst.slots.lookupSend sid = none
  recv_fresh : ∀ rc : Nat, hst.recvCount ≤ rc → hst.slots.recvTbl rc = none

private theorem ckSlotWf_empty (S : Setup) (secb : Bool) :
    CkSlotWf S (AuthHybridStateFixed.empty S secb) :=
  ⟨fun sid _ => by cases sid <;> rfl, fun _ _ => rfl⟩

private theorem sessionId_beq_self {S : Setup} (sid : SessionId S) : (sid == sid) = true := by
  cases sid <;> simp

private theorem slotComp_ite {α : Type} (samp : ProbComp (Bytes × Bytes)) (c : Bool)
    (t e : SlotM (Bytes × Bytes) α) (ht : SlotM.SlotComp samp t) (he : SlotM.SlotComp samp e) :
    SlotM.SlotComp samp (if c then t else e) := by cases c <;> assumption

private theorem authCkSlotsStepSlot_slotComp (S : Setup) (P : Primitives) (idx : Nat)
    (samp : ProbComp (Bytes × Bytes)) (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    SlotM.SlotComp samp (authCkSlotsStepSlot S P idx samp q hst) := by
  have hSend : ∀ sid u bundle m0 m1,
      SlotM.SlotComp samp (authCkSlotsSendSlot S P idx samp sid u bundle m0 m1 hst) := by
    intro sid u bundle m0 m1; unfold authCkSlotsSendSlot; dsimp only
    refine slotComp_ite samp _ _ _ (SlotM.SlotComp.pure samp _) ?_
    refine slotComp_ite samp _ _ _ (SlotM.SlotComp.pure samp _) ?_
    refine slotComp_ite samp _ _ _ (SlotM.SlotComp.pure samp _) ?_
    cases hst.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == u.val) with
    | none => exact SlotM.SlotComp.pure samp _
    | some uPair =>
      rcases uPair with ⟨_, uEntry⟩; dsimp only
      refine slotComp_ite samp _ _ _ (SlotM.SlotComp.pure samp _) ?_
      refine slotComp_ite samp _ _ _ (SlotM.SlotComp.pure samp _) ?_
      refine SlotM.SlotComp.liftComp_bind samp _ (fun ekASk => ?_)
      refine SlotM.SlotComp.liftComp_bind samp _ (fun kemCoins => ?_)
      refine SlotM.SlotComp.liftComp_bind samp _ (fun ephASk => ?_)
      refine SlotM.SlotComp.liftComp_bind samp _ (fun spqrCoins => ?_)
      refine slotComp_ite samp _ _ _ (SlotM.SlotComp.pure samp _) ?_
      cases P.kemEncaps bundle.pqspkB kemCoins with
      | none => exact SlotM.SlotComp.pure samp _
      | some pair =>
        rcases pair with ⟨ss, kemCt⟩; dsimp only
        refine slotComp_ite samp _ _ _ ?_ ?_
        · refine SlotM.SlotComp.liftComp_bind samp _ (fun drKey => ?_)
          refine SlotM.SlotComp.liftComp_bind samp _ (fun rk1 => ?_)
          cases P.spqrInitSend drKey.pqrKey spqrCoins with
          | none => exact SlotM.SlotComp.pure samp _
          | some spqrVal =>
            rcases spqrVal with ⟨_, spqrSalt?, pqRatchetMsg⟩
            exact SlotM.SlotComp.getCkAtSlot_bind idx samp P _ (fun _ => SlotM.SlotComp.pure samp _)
        · refine SlotM.SlotComp.liftComp_bind samp _ (fun ⟨drKey, roCache'⟩ => ?_)
          refine SlotM.SlotComp.liftComp_bind samp _ (fun ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩ => ?_)
          cases P.spqrInitSend drKey.pqrKey spqrCoins with
          | none => exact SlotM.SlotComp.pure samp _
          | some spqrVal => rcases spqrVal with ⟨_, spqrSalt?, pqRatchetMsg⟩; exact SlotM.SlotComp.pure samp _
  have hRecv : ∀ msg prep?,
      SlotM.SlotComp samp (authCkSlotsRecvSlot S P idx samp msg prep? hst) := by
    intro msg prep?; unfold authCkSlotsRecvSlot
    cases prep? with
    | none => exact SlotM.SlotComp.pure samp _
    | some prep =>
      dsimp only
      refine slotComp_ite samp _ _ _ ?_ ?_
      · cases prep.matchedSess? with
        | some s =>
          dsimp only
          refine slotComp_ite samp _ _ _ ?_ ?_
          · cases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
            | none => exact SlotM.SlotComp.pure samp _
            | some pqr => rcases pqr with ⟨_, spqrSalt?⟩; exact SlotM.SlotComp.pure samp _
          · refine SlotM.SlotComp.liftComp_bind samp _ (fun rk1 => ?_)
            cases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
            | none => exact SlotM.SlotComp.pure samp _
            | some pqr =>
              rcases pqr with ⟨_, spqrSalt?⟩
              exact SlotM.SlotComp.getCkAtSlot_bind idx samp P _ (fun _ => SlotM.SlotComp.pure samp _)
        | none =>
          refine SlotM.SlotComp.liftComp_bind samp _ (fun drKey => ?_)
          refine SlotM.SlotComp.liftComp_bind samp _ (fun rk1 => ?_)
          cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
          | none => exact SlotM.SlotComp.pure samp _
          | some pqr =>
            rcases pqr with ⟨_, spqrSalt?⟩
            exact SlotM.SlotComp.getCkAtSlot_bind idx samp P _ (fun _ => SlotM.SlotComp.pure samp _)
      · refine SlotM.SlotComp.liftComp_bind samp _ (fun ⟨drKey, roCache'⟩ => ?_)
        refine SlotM.SlotComp.liftComp_bind samp _ (fun ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩ => ?_)
        cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
        | none => exact SlotM.SlotComp.pure samp _
        | some pqr => rcases pqr with ⟨_, spqrSalt?⟩; exact SlotM.SlotComp.pure samp _
  cases q <;> unfold authCkSlotsStepSlot <;> dsimp only
  case sendOPK u i bundle m0 m1 =>
    exact slotComp_ite samp _ _ _ (SlotM.SlotComp.pure samp _) (hSend (.sendOPK u i) u bundle m0 m1)
  case sendNoOPK u i bundle m0 m1 =>
    exact slotComp_ite samp _ _ _ (SlotM.SlotComp.pure samp _) (hSend (.sendNoOPK u i) u bundle m0 m1)
  case recvOPK k j o msg => exact hRecv msg _
  case recvNoOPK k j l msg => exact hRecv msg _
  all_goals exact SlotM.SlotComp.liftComp samp _

private theorem run'_ite_eq {σ α : Type} (o : Option σ) (c : Bool)
    (t1 e1 : SlotM σ α) (t2 e2 : ProbComp α)
    (ht : t1.run' o = t2) (he : e1.run' o = e2) :
    (if c then t1 else e1).run' o = if c then t2 else e2 := by cases c <;> assumption

private theorem authCkSlotsSendSlot_run'_eq (S : Setup) (P : Primitives) (idx : Nat)
    (samp : ProbComp (Bytes × Bytes)) (o : Option (Bytes × Bytes))
    (sampPure : Nat → ProbComp (Bytes × Bytes))
    (hGet : ∀ {α : Type} (sIdx : Nat) (f : Bytes × Bytes → α),
      (getCkAtSlot idx samp P sIdx >>= fun x => pure (f x)).run' o =
        (sampPure sIdx >>= fun x => pure (f x)))
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) :
    (authCkSlotsSendSlot S P idx samp sid u bundle m0 m1 hst).run' o =
      authCkSendWithSlots S P sampPure sid u bundle m0 m1 hst := by
  unfold authCkSlotsSendSlot authCkSendWithSlots; dsimp only
  refine run'_ite_eq o _ _ _ _ _ (SlotM.run'_pure _ _) ?_
  refine run'_ite_eq o _ _ _ _ _ (SlotM.run'_pure _ _) ?_
  refine run'_ite_eq o _ _ _ _ _ (SlotM.run'_pure _ _) ?_
  cases hst.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == u.val) with
  | none => exact SlotM.run'_pure _ _
  | some uPair =>
    rcases uPair with ⟨_, uEntry⟩; dsimp only
    refine run'_ite_eq o _ _ _ _ _ (SlotM.run'_pure _ _) ?_
    refine run'_ite_eq o _ _ _ _ _ (SlotM.run'_pure _ _) ?_
    rw [SlotM.run'_liftComp_bind]; congr 1; funext ekASk
    rw [SlotM.run'_liftComp_bind]; congr 1; funext kemCoins
    rw [SlotM.run'_liftComp_bind]; congr 1; funext ephASk
    rw [SlotM.run'_liftComp_bind]; congr 1; funext spqrCoins
    refine run'_ite_eq o _ _ _ _ _ (SlotM.run'_pure _ _) ?_
    cases P.kemEncaps bundle.pqspkB kemCoins with
    | none => exact SlotM.run'_pure _ _
    | some pair =>
      rcases pair with ⟨ss, kemCt⟩; dsimp only
      refine run'_ite_eq o _ _ _ _ _ ?_ ?_
      · rw [SlotM.run'_liftComp_bind]; congr 1; funext drKey
        rw [SlotM.run'_liftComp_bind]; congr 1; funext rk1
        cases P.spqrInitSend drKey.pqrKey spqrCoins with
        | none => exact SlotM.run'_pure _ _
        | some spqrVal => rcases spqrVal with ⟨_, spqrSalt?, pqRatchetMsg⟩; exact hGet _ _
      · rw [SlotM.run'_liftComp_bind]; congr 1; funext ⟨drKey, roCache'⟩
        rw [SlotM.run'_liftComp_bind]; congr 1; funext ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
        cases P.spqrInitSend drKey.pqrKey spqrCoins with
        | none => exact SlotM.run'_pure _ _
        | some spqrVal => rcases spqrVal with ⟨_, spqrSalt?, pqRatchetMsg⟩; exact SlotM.run'_pure _ _

private theorem authCkSlotsRecvSlot_run'_eq (S : Setup) (P : Primitives) (idx : Nat)
    (samp : ProbComp (Bytes × Bytes)) (o : Option (Bytes × Bytes))
    (sampPure : Nat → ProbComp (Bytes × Bytes))
    (hGet : ∀ {α : Type} (rSlot : Nat) (f : Bytes × Bytes → α),
      (getCkAtSlot idx samp P rSlot >>= fun x => pure (f x)).run' o =
        (sampPure rSlot >>= fun x => pure (f x)))
    (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecv S)) (hst : AuthHybridStateFixed S) :
    (authCkSlotsRecvSlot S P idx samp msg prep? hst).run' o =
      authCkRecvWithSlots S P sampPure msg prep? hst := by
  unfold authCkSlotsRecvSlot authCkRecvWithSlots
  cases prep? with
  | none => exact SlotM.run'_pure _ _
  | some prep =>
    dsimp only
    refine run'_ite_eq o _ _ _ _ _ ?_ ?_
    · cases prep.matchedSess? with
      | some s =>
        dsimp only
        refine run'_ite_eq o _ _ _ _ _ ?_ ?_
        · cases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
          | none => exact SlotM.run'_pure _ _
          | some pqr => rcases pqr with ⟨_, spqrSalt?⟩; exact SlotM.run'_pure _ _
        · rw [SlotM.run'_liftComp_bind]; congr 1; funext rk1
          cases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
          | none => exact SlotM.run'_pure _ _
          | some pqr => rcases pqr with ⟨_, spqrSalt?⟩; exact hGet _ _
      | none =>
        rw [SlotM.run'_liftComp_bind]; congr 1; funext drKey
        rw [SlotM.run'_liftComp_bind]; congr 1; funext rk1
        cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
        | none => exact SlotM.run'_pure _ _
        | some pqr => rcases pqr with ⟨_, spqrSalt?⟩; exact hGet _ _
    · rw [SlotM.run'_liftComp_bind]; congr 1; funext ⟨drKey, roCache'⟩
      rw [SlotM.run'_liftComp_bind]; congr 1; funext ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
      cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
      | none => exact SlotM.run'_pure _ _
      | some pqr => rcases pqr with ⟨_, spqrSalt?⟩; exact SlotM.run'_pure _ _

private theorem authCkSlotsStepSlot_run'_some (S : Setup) (P : Primitives) (idx : Nat)
    (samp : ProbComp (Bytes × Bytes)) (k : Bytes × Bytes)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    (authCkSlotsStepSlot S P idx samp q hst).run' (some k) =
      authCkSlotsStepWith S P
        (fun slotIdx => if slotIdx == idx then pure k else sampCkPair P (slotIdx < idx)) q hst := by
  let sampK := fun slotIdx => if slotIdx == idx then pure k else sampCkPair P (slotIdx < idx)
  cases q <;> unfold authCkSlotsStepSlot authCkSlotsStepWith <;> dsimp only
  case sendOPK u i bundle m0 m1 =>
    exact run'_ite_eq (some k) _ _ _ _ _ (SlotM.run'_pure _ _)
      (authCkSlotsSendSlot_run'_eq S P idx samp (some k) sampK
        (fun s f => run'_getCkAtSlot_bind_pure_some idx samp P k s f) (.sendOPK u i) u bundle m0 m1 hst)
  case sendNoOPK u i bundle m0 m1 =>
    exact run'_ite_eq (some k) _ _ _ _ _ (SlotM.run'_pure _ _)
      (authCkSlotsSendSlot_run'_eq S P idx samp (some k) sampK
        (fun s f => run'_getCkAtSlot_bind_pure_some idx samp P k s f) (.sendNoOPK u i) u bundle m0 m1 hst)
  case recvOPK k' j o msg =>
    exact authCkSlotsRecvSlot_run'_eq S P idx samp (some k) sampK
      (fun s f => run'_getCkAtSlot_bind_pure_some idx samp P k s f) msg _ hst
  case recvNoOPK k' j l msg =>
    exact authCkSlotsRecvSlot_run'_eq S P idx samp (some k) sampK
      (fun s f => run'_getCkAtSlot_bind_pure_some idx samp P k s f) msg _ hst
  all_goals rw [SlotM.run'_liftComp]

private theorem authCkSlotsStepSlot_run'_none_eq (S : Setup) (P : Primitives) (idx : Nat) (b : Bool)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    (authCkSlotsStepSlot S P idx (sampCkPair P (!b)) q hst).run' none =
      authCkSlotsStepWith S P (fun slotIdx => sampCkPair P (slotIdx < (if b then idx else idx + 1))) q hst := by
  let sampN := fun slotIdx => sampCkPair P (slotIdx < (if b then idx else idx + 1))
  cases q <;> unfold authCkSlotsStepSlot authCkSlotsStepWith <;> dsimp only
  case sendOPK u i bundle m0 m1 =>
    exact run'_ite_eq none _ _ _ _ _ (SlotM.run'_pure _ _)
      (authCkSlotsSendSlot_run'_eq S P idx (sampCkPair P (!b)) none sampN
        (fun s f => run'_getCkAtSlot_bind_pure_none idx b P s f) (.sendOPK u i) u bundle m0 m1 hst)
  case sendNoOPK u i bundle m0 m1 =>
    exact run'_ite_eq none _ _ _ _ _ (SlotM.run'_pure _ _)
      (authCkSlotsSendSlot_run'_eq S P idx (sampCkPair P (!b)) none sampN
        (fun s f => run'_getCkAtSlot_bind_pure_none idx b P s f) (.sendNoOPK u i) u bundle m0 m1 hst)
  case recvOPK k' j o msg =>
    exact authCkSlotsRecvSlot_run'_eq S P idx (sampCkPair P (!b)) none sampN
      (fun s f => run'_getCkAtSlot_bind_pure_none idx b P s f) msg _ hst
  case recvNoOPK k' j l msg =>
    exact authCkSlotsRecvSlot_run'_eq S P idx (sampCkPair P (!b)) none sampN
      (fun s f => run'_getCkAtSlot_bind_pure_none idx b P s f) msg _ hst
  all_goals rw [SlotM.run'_liftComp]

private def SlotFireAtCk (idx : Nat) {S : Setup}
    (mx : SlotM (Bytes × Bytes) (AuthResponse × AuthHybridStateFixed S)) : Prop :=
  ∀ y ∈ support (mx.run none), y.2.isSome = true → authCreationSlotFired idx y.1.2 = true

private theorem SlotFireAtCk.pure {S : Setup} (idx : Nat)
    (x : AuthResponse × AuthHybridStateFixed S) : SlotFireAtCk idx (pure x) := by
  intro y hy hSome; simp [StateT.run_pure] at hy; subst hy; cases hSome

private theorem SlotFireAtCk.liftComp {S : Setup} (idx : Nat)
    (c : ProbComp (AuthResponse × AuthHybridStateFixed S)) : SlotFireAtCk idx (liftM c) := by
  intro y hy hSome
  simp only [StateT.run_monadLift, monadLift_self, support_bind, support_pure,
    Set.mem_iUnion, Set.mem_singleton_iff] at hy
  rcases hy with ⟨_, _, rfl⟩; cases hSome

private theorem SlotFireAtCk.liftComp_bind {S : Setup} {α : Type} (idx : Nat)
    (c : ProbComp α) {f : α → SlotM (Bytes × Bytes) (AuthResponse × AuthHybridStateFixed S)}
    (hf : ∀ a, SlotFireAtCk idx (f a)) :
    SlotFireAtCk idx ((liftM c : SlotM (Bytes × Bytes) α) >>= f) := by
  intro y hy hSome
  simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind,
    MonadAttach.mem_support_bind] at hy
  rcases hy with ⟨a, _, hy'⟩; exact hf a y hy' hSome

private theorem SlotFireAtCk.getCkAtSlot_bind_pure {S : Setup} (idx : Nat)
    (samp : ProbComp (Bytes × Bytes)) (P : Primitives) (slotIdx : Nat)
    (f : Bytes × Bytes → AuthResponse × AuthHybridStateFixed S)
    (hLt : ∀ p, slotIdx < (f p).2.slots.nextSlot) :
    SlotFireAtCk idx (getCkAtSlot idx samp P slotIdx >>= fun p => Pure.pure (f p)) := by
  intro y hy hSome
  unfold getCkAtSlot at hy
  by_cases hEq : (slotIdx == idx) = true
  · simp only [hEq, ↓reduceIte, StateT.run_bind, SlotM.getSlot_run_none, bind_assoc, pure_bind,
      StateT.run_pure, MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
    rcases hy with ⟨p, _, rfl⟩; rw [beq_iff_eq] at hEq
    simp only [authCreationSlotFired, decide_eq_true_eq]; have := hLt p; omega
  · simp only [hEq, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
      monadLift_self, bind_assoc, pure_bind, StateT.run_pure,
      MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
    rcases hy with ⟨_, _, rfl⟩; cases hSome

private theorem SlotFireAtCk.ite {S : Setup} (idx : Nat) (c : Bool)
    (t e : SlotM (Bytes × Bytes) (AuthResponse × AuthHybridStateFixed S))
    (ht : SlotFireAtCk idx t) (he : SlotFireAtCk idx e) :
    SlotFireAtCk idx (if c then t else e) := by cases c <;> assumption

private theorem authCkSlotsStepSlot_fire (S : Setup) (P : Primitives) (idx : Nat)
    (samp : ProbComp (Bytes × Bytes)) (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (hWf : CkSlotWf S hst) :
    SlotFireAtCk idx (authCkSlotsStepSlot S P idx samp q hst) := by
  have hSend : ∀ sid, IsSendSessionId S sid → ∀ u bundle m0 m1,
      SlotFireAtCk idx (authCkSlotsSendSlot S P idx samp sid u bundle m0 m1 hst) := by
    intro sid hSid u bundle m0 m1; unfold authCkSlotsSendSlot; dsimp only
    refine SlotFireAtCk.ite idx _ _ _ (SlotFireAtCk.pure idx _) ?_
    refine SlotFireAtCk.ite idx _ _ _ (SlotFireAtCk.pure idx _) ?_
    by_cases hUsed : hst.toAuthHybridState.base.usedSendSessions.contains sid = true
    · simp only [hUsed, ↓reduceIte]; exact SlotFireAtCk.pure idx _
    · simp only [hUsed, Bool.false_eq_true, ↓reduceIte]
      have hAlloc := allocSend_of_none hst.slots sid hSid (hWf.send_fresh sid (Bool.eq_false_iff.mpr hUsed))
      cases hst.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none => exact SlotFireAtCk.pure idx _
      | some uPair =>
        rcases uPair with ⟨_, uEntry⟩; dsimp only
        refine SlotFireAtCk.ite idx _ _ _ (SlotFireAtCk.pure idx _) ?_
        refine SlotFireAtCk.ite idx _ _ _ (SlotFireAtCk.pure idx _) ?_
        refine SlotFireAtCk.liftComp_bind idx _ (fun ekASk => ?_)
        refine SlotFireAtCk.liftComp_bind idx _ (fun kemCoins => ?_)
        refine SlotFireAtCk.liftComp_bind idx _ (fun ephASk => ?_)
        refine SlotFireAtCk.liftComp_bind idx _ (fun spqrCoins => ?_)
        refine SlotFireAtCk.ite idx _ _ _ (SlotFireAtCk.pure idx _) ?_
        cases P.kemEncaps bundle.pqspkB kemCoins with
        | none => exact SlotFireAtCk.pure idx _
        | some pair =>
          rcases pair with ⟨ss, kemCt⟩; dsimp only
          refine SlotFireAtCk.ite idx _ _ _ ?_ ?_
          · refine SlotFireAtCk.liftComp_bind idx _ (fun drKey => ?_)
            refine SlotFireAtCk.liftComp_bind idx _ (fun rk1 => ?_)
            cases P.spqrInitSend drKey.pqrKey spqrCoins with
            | none => exact SlotFireAtCk.pure idx _
            | some spqrVal =>
              rcases spqrVal with ⟨_, spqrSalt?, pqRatchetMsg⟩
              exact SlotFireAtCk.getCkAtSlot_bind_pure idx samp P _ _
                (fun _ => by dsimp only [finishAuthSendCkSlots]; omega)
          · refine SlotFireAtCk.liftComp_bind idx _ (fun ⟨drKey, roCache'⟩ => ?_)
            refine SlotFireAtCk.liftComp_bind idx _ (fun ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩ => ?_)
            cases P.spqrInitSend drKey.pqrKey spqrCoins with
            | none => exact SlotFireAtCk.pure idx _
            | some spqrVal => rcases spqrVal with ⟨_, spqrSalt?, pqRatchetMsg⟩; exact SlotFireAtCk.pure idx _
  have hRecv : ∀ msg prep?, SlotFireAtCk idx (authCkSlotsRecvSlot S P idx samp msg prep? hst) := by
    intro msg prep?
    have hAlloc := allocRecv_of_none (S := S) hst.slots hst.recvCount (hWf.recv_fresh hst.recvCount le_rfl)
    unfold authCkSlotsRecvSlot
    cases prep? with
    | none => exact SlotFireAtCk.pure idx _
    | some prep =>
      dsimp only
      refine SlotFireAtCk.ite idx _ _ _ ?_ ?_
      · cases prep.matchedSess? with
        | some s =>
          dsimp only
          refine SlotFireAtCk.ite idx _ _ _ ?_ ?_
          · cases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
            | none => exact SlotFireAtCk.pure idx _
            | some pqr => rcases pqr with ⟨_, spqrSalt?⟩; exact SlotFireAtCk.pure idx _
          · refine SlotFireAtCk.liftComp_bind idx _ (fun rk1 => ?_)
            cases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
            | none => exact SlotFireAtCk.pure idx _
            | some pqr =>
              rcases pqr with ⟨_, spqrSalt?⟩
              exact SlotFireAtCk.getCkAtSlot_bind_pure idx samp P _ _
                (fun _ => by dsimp only [finishAuthRecvCkSlots]; omega)
        | none =>
          refine SlotFireAtCk.liftComp_bind idx _ (fun drKey => ?_)
          refine SlotFireAtCk.liftComp_bind idx _ (fun rk1 => ?_)
          cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
          | none => exact SlotFireAtCk.pure idx _
          | some pqr =>
            rcases pqr with ⟨_, spqrSalt?⟩
            exact SlotFireAtCk.getCkAtSlot_bind_pure idx samp P _ _
              (fun _ => by dsimp only [finishAuthRecvCkSlots]; omega)
      · refine SlotFireAtCk.liftComp_bind idx _ (fun ⟨drKey, roCache'⟩ => ?_)
        refine SlotFireAtCk.liftComp_bind idx _ (fun ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩ => ?_)
        cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
        | none => exact SlotFireAtCk.pure idx _
        | some pqr => rcases pqr with ⟨_, spqrSalt?⟩; exact SlotFireAtCk.pure idx _
  cases q <;> unfold authCkSlotsStepSlot <;> dsimp only
  case sendOPK u i bundle m0 m1 =>
    exact SlotFireAtCk.ite idx _ _ _ (SlotFireAtCk.pure idx _) (hSend (.sendOPK u i) trivial u bundle m0 m1)
  case sendNoOPK u i bundle m0 m1 =>
    exact SlotFireAtCk.ite idx _ _ _ (SlotFireAtCk.pure idx _) (hSend (.sendNoOPK u i) trivial u bundle m0 m1)
  case recvOPK k j o msg => exact hRecv msg _
  case recvNoOPK k j l msg => exact hRecv msg _
  all_goals exact SlotFireAtCk.liftComp idx _

private theorem forall_support_pure {α : Type} (a : α) (Q : α → Prop) (ha : Q a) :
    ∀ x ∈ support (pure a : ProbComp α), Q x := by
  intro x hx; simp only [support_pure, Set.mem_singleton_iff] at hx; subst hx; exact ha

private theorem forall_support_bind {α β : Type} (mx : ProbComp α) (f : α → ProbComp β)
    (Q : β → Prop) (hf : ∀ a, ∀ y ∈ support (f a), Q y) :
    ∀ y ∈ support (mx >>= f), Q y := by
  intro y hy; simp only [MonadAttach.mem_support_bind] at hy
  rcases hy with ⟨a, _, hy'⟩; exact hf a y hy'

private theorem support_authCkSlotsStepWith (S : Setup) (P : Primitives)
    (sampAt : Nat → ProbComp (Bytes × Bytes))
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) (hWf : CkSlotWf S hst) :
    ∀ x ∈ support (authCkSlotsStepWith S P sampAt q hst),
      CkSlotWf S x.2 ∧ hst.slots.nextSlot ≤ x.2.slots.nextSlot ∧
      x.2.slots.nextSlot ≤ hst.slots.nextSlot + (if isAuthSessQueryB (.inr q) then 1 else 0) := by
  have hSend : ∀ sid, IsSendSessionId S sid → ∀ u bundle m0 m1,
      ∀ x ∈ support (authCkSendWithSlots S P sampAt sid u bundle m0 m1 hst),
        CkSlotWf S x.2 ∧ hst.slots.nextSlot ≤ x.2.slots.nextSlot ∧
        x.2.slots.nextSlot ≤ hst.slots.nextSlot + 1 := by
    intro sid hSid u bundle m0 m1; unfold authCkSendWithSlots; dsimp only
    refine forall_mem_support_ite _ _ _ _ (forall_support_pure _ _ ⟨hWf, le_rfl, Nat.le_add_right _ 1⟩) ?_
    refine forall_mem_support_ite _ _ _ _ (forall_support_pure _ _ ⟨hWf, le_rfl, Nat.le_add_right _ 1⟩) ?_
    by_cases hUsed : hst.toAuthHybridState.base.usedSendSessions.contains sid = true
    · simp only [hUsed, ↓reduceIte]; exact forall_support_pure _ _ ⟨hWf, le_rfl, Nat.le_add_right _ 1⟩
    · simp only [hUsed, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨_, hNext, hRecvTbl, hLookup⟩ :=
        allocSend_of_none hst.slots sid hSid (hWf.send_fresh sid (Bool.eq_false_iff.mpr hUsed))
      have hIdealExit : ∀ uEntry peer? spqrSalt? pqRatchetMsg msgPlain ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 p,
          CkSlotWf S (finishAuthSendCkSlots P sid uEntry peer? bundle m0 m1 ekASk ekAPk ss kemCt
            ephASk ephAPk drKey rk1 spqrSalt? pqRatchetMsg msgPlain
            { hst with slots := (hst.slots.allocSend sid).2 } p).2 ∧
          hst.slots.nextSlot ≤ (hst.slots.allocSend sid).2.nextSlot ∧
          (hst.slots.allocSend sid).2.nextSlot ≤ hst.slots.nextSlot + 1 := by
        intro uEntry peer? spqrSalt? pqRatchetMsg msgPlain ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 p
        refine ⟨⟨fun sid' hCont => ?_, fun rc hrc => ?_⟩, by omega, by omega⟩
        · simp only [finishAuthSendCkSlots, finishAuthSendCk, finishAuthHybridSend,
            List.contains_cons, Bool.or_eq_false_iff] at hCont
          have hNe : sid' ≠ sid := by
            intro hEq; subst hEq; rw [sessionId_beq_self] at hCont; exact Bool.noConfusion hCont.1
          dsimp only [finishAuthSendCkSlots]; rw [hLookup sid']; simp only [hNe, ↓reduceIte]
          exact hWf.send_fresh sid' hCont.2
        · dsimp only [finishAuthSendCkSlots, finishAuthSendCk] at hrc ⊢
          rw [hRecvTbl]; exact hWf.recv_fresh rc hrc
      have hRealExit : ∀ uEntry peer? isFresh spqrSalt? pqRatchetMsg deriveMK ad aeadCt msgPlain
          ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 ck1_0 mkSeed ck1_1 roC rootRoC,
          CkSlotWf S
            { toAuthHybridState := (finishAuthHybridSend P sid uEntry peer? isFresh bundle m0 m1
                ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 ck1_0 mkSeed ck1_1 spqrSalt? pqRatchetMsg
                deriveMK ad aeadCt msgPlain roC rootRoC hst.toAuthHybridState).2,
              recvCount := hst.recvCount, slots := hst.slots } := by
        intro uEntry peer? isFresh spqrSalt? pqRatchetMsg deriveMK ad aeadCt msgPlain
          ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 ck1_0 mkSeed ck1_1 roC rootRoC
        refine ⟨fun sid' hCont => ?_, hWf.recv_fresh⟩
        simp only [finishAuthHybridSend, List.contains_cons, Bool.or_eq_false_iff] at hCont
        exact hWf.send_fresh sid' hCont.2
      cases hst.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none => exact forall_support_pure _ _ ⟨hWf, le_rfl, Nat.le_add_right _ 1⟩
      | some uPair =>
        rcases uPair with ⟨_, uEntry⟩; dsimp only
        refine forall_mem_support_ite _ _ _ _ (forall_support_pure _ _ ⟨hWf, le_rfl, Nat.le_add_right _ 1⟩) ?_
        refine forall_mem_support_ite _ _ _ _ (forall_support_pure _ _ ⟨hWf, le_rfl, Nat.le_add_right _ 1⟩) ?_
        refine forall_support_bind _ _ _ (fun ekASk => ?_)
        refine forall_support_bind _ _ _ (fun kemCoins => ?_)
        refine forall_support_bind _ _ _ (fun ephASk => ?_)
        refine forall_support_bind _ _ _ (fun spqrCoins => ?_)
        refine forall_mem_support_ite _ _ _ _ (forall_support_pure _ _ ⟨hWf, le_rfl, Nat.le_add_right _ 1⟩) ?_
        cases P.kemEncaps bundle.pqspkB kemCoins with
        | none => exact forall_support_pure _ _ ⟨hWf, le_rfl, Nat.le_add_right _ 1⟩
        | some pair =>
          rcases pair with ⟨ss, kemCt⟩; dsimp only
          refine forall_mem_support_ite _ _ _ _ ?_ ?_
          · refine forall_support_bind _ _ _ (fun drKey => ?_)
            refine forall_support_bind _ _ _ (fun rk1 => ?_)
            cases P.spqrInitSend drKey.pqrKey spqrCoins with
            | none => exact forall_support_pure _ _ ⟨hWf, le_rfl, Nat.le_add_right _ 1⟩
            | some spqrVal =>
              rcases spqrVal with ⟨_, spqrSalt?, pqRatchetMsg⟩
              exact forall_support_bind _ _ _ (fun p =>
                forall_support_pure _ _ (hIdealExit _ _ _ _ _ _ _ _ _ _ _ _ _ p))
          · refine forall_support_bind _ _ _ (fun ⟨drKey, roCache'⟩ => ?_)
            refine forall_support_bind _ _ _ (fun ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩ => ?_)
            cases P.spqrInitSend drKey.pqrKey spqrCoins with
            | none => exact forall_support_pure _ _ ⟨hWf, le_rfl, Nat.le_add_right _ 1⟩
            | some spqrVal =>
              rcases spqrVal with ⟨_, spqrSalt?, pqRatchetMsg⟩
              exact forall_support_pure _ _ ⟨hRealExit _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, le_rfl, Nat.le_add_right _ 1⟩
  have hRecv : ∀ msg prep?,
      (∀ prep, prep? = some prep → ∀ res?,
        (prep.finish res?).2.base.usedSendSessions = hst.toAuthHybridState.base.usedSendSessions) →
      ∀ x ∈ support (authCkRecvWithSlots S P sampAt msg prep? hst),
        CkSlotWf S x.2 ∧ hst.slots.nextSlot ≤ x.2.slots.nextSlot ∧
        x.2.slots.nextSlot ≤ hst.slots.nextSlot + 1 := by
    intro msg prep? hUsedPres
    obtain ⟨_, hNext, hLookup, hRecvTbl⟩ :=
      allocRecv_of_none (S := S) hst.slots hst.recvCount (hWf.recv_fresh hst.recvCount le_rfl)
    unfold authCkRecvWithSlots
    cases prep? with
    | none =>
      exact forall_support_pure _ _ ⟨⟨hWf.send_fresh, fun rc hrc => hWf.recv_fresh rc (by dsimp only at hrc; omega)⟩, le_rfl, Nat.le_add_right _ 1⟩
    | some prep =>
      have hUP := hUsedPres prep rfl
      have hSameSlots : ∀ res?, CkSlotWf S
          { toAuthHybridState := (prep.finish res?).2,
            recvCount := hst.recvCount + 1, slots := hst.slots } := fun res? =>
        ⟨fun sid' hC => hWf.send_fresh sid' (by dsimp only at hC; rwa [hUP res?] at hC),
         fun rc hrc => hWf.recv_fresh rc (by dsimp only at hrc; omega)⟩
      have hAllocSlots : ∀ drKey rk1 spqrSalt? p,
          CkSlotWf S (finishAuthRecvCkSlots P msg prep drKey rk1 spqrSalt? (hst.recvCount + 1) p
            (hst.slots.allocRecv hst.recvCount).2).2 := fun drKey rk1 spqrSalt? p => by
        refine ⟨fun sid' hC => ?_, fun rc hrc => ?_⟩
        · dsimp only [finishAuthRecvCkSlots, finishAuthRecvCk] at hC ⊢
          rw [hLookup sid']; rw [hUP _] at hC; exact hWf.send_fresh sid' hC
        · dsimp only [finishAuthRecvCkSlots, finishAuthRecvCk] at hrc ⊢
          have hNeRc : rc ≠ hst.recvCount := by omega
          rw [hRecvTbl rc]; simp only [hNeRc, ↓reduceIte]; exact hWf.recv_fresh rc (by omega)
      dsimp only
      refine forall_mem_support_ite _ _ _ _ ?_ ?_
      · cases prep.matchedSess? with
        | some s =>
          dsimp only
          refine forall_mem_support_ite _ _ _ _ ?_ ?_
          · cases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
            | none => exact forall_support_pure _ _ ⟨hSameSlots _, le_rfl, Nat.le_add_right _ 1⟩
            | some pqr =>
              rcases pqr with ⟨_, spqrSalt?⟩
              dsimp only [finishAuthRecvCkSlots, finishAuthRecvCk]
              exact forall_support_pure _ _ ⟨hSameSlots _, le_rfl, Nat.le_add_right _ 1⟩
          · refine forall_support_bind _ _ _ (fun rk1 => ?_)
            cases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
            | none => exact forall_support_pure _ _ ⟨hSameSlots _, le_rfl, Nat.le_add_right _ 1⟩
            | some pqr =>
              rcases pqr with ⟨_, spqrSalt?⟩
              exact forall_support_bind _ _ _ (fun p => forall_support_pure _ _
                ⟨hAllocSlots _ _ _ p, by dsimp only [finishAuthRecvCkSlots]; omega,
                 by dsimp only [finishAuthRecvCkSlots]; omega⟩)
        | none =>
          refine forall_support_bind _ _ _ (fun drKey => ?_)
          refine forall_support_bind _ _ _ (fun rk1 => ?_)
          cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
          | none => exact forall_support_pure _ _ ⟨hSameSlots _, le_rfl, Nat.le_add_right _ 1⟩
          | some pqr =>
            rcases pqr with ⟨_, spqrSalt?⟩
            exact forall_support_bind _ _ _ (fun p => forall_support_pure _ _
              ⟨hAllocSlots _ _ _ p, by dsimp only [finishAuthRecvCkSlots]; omega,
               by dsimp only [finishAuthRecvCkSlots]; omega⟩)
      · refine forall_support_bind _ _ _ (fun ⟨drKey, roCache'⟩ => ?_)
        refine forall_support_bind _ _ _ (fun ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩ => ?_)
        cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
        | none => exact forall_support_pure _ _ ⟨hSameSlots _, le_rfl, Nat.le_add_right _ 1⟩
        | some pqr => rcases pqr with ⟨_, spqrSalt?⟩; exact forall_support_pure _ _ ⟨hSameSlots _, le_rfl, Nat.le_add_right _ 1⟩
  have hNotSess : ∀ (qOther : AuthQuery S)
      (hS1 : ∀ u i b m0 m1, qOther ≠ .sendOPK u i b m0 m1)
      (hS2 : ∀ u i b m0 m1, qOther ≠ .sendNoOPK u i b m0 m1)
      (hR1 : ∀ k j o msg, qOther ≠ .recvOPK k j o msg)
      (hR2 : ∀ k j l msg, qOther ≠ .recvNoOPK k j l msg),
      ∀ x ∈ support (authCkOtherStep S P qOther hst),
        CkSlotWf S x.2 ∧ hst.slots.nextSlot ≤ x.2.slots.nextSlot ∧
        x.2.slots.nextSlot ≤ hst.slots.nextSlot := by
    intro qOther hS1 hS2 hR1 hR2
    have hPres : PreservesAt AuthState.usedSendSessions hst.toAuthHybridState.base
        (pqxdhAuthImpl true true S P qOther) := by
      cases qOther with
      | sendOPK u i b m0 m1 => exact False.elim (hS1 u i b m0 m1 rfl)
      | sendNoOPK u i b m0 m1 => exact False.elim (hS2 u i b m0 m1 rfl)
      | recvOPK k j o msg => exact False.elim (hR1 k j o msg rfl)
      | recvNoOPK k j l msg => exact False.elim (hR2 k j l msg rfl)
      | _ =>
        unfold pqxdhAuthImpl; dsimp only
        repeat (first
          | with_reducible apply PreservesAt.pure
          | with_reducible apply PreservesAt.get_bind
          | (with_reducible apply PreservesAt.liftM_bind; intro _)
          | ((with_reducible apply PreservesAt.set_bind); rfl)
          | split)
    intro x hx; unfold authCkOtherStep at hx; split at hx
    · simp only [support_pure, Set.mem_singleton_iff] at hx; subst hx; exact ⟨hWf, le_rfl, le_rfl⟩
    · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
      rcases hx with ⟨⟨resp, base'⟩, hbase, rfl⟩
      have hUEq := hPres (resp, base') hbase
      exact ⟨⟨fun sid' hC => hWf.send_fresh sid' (by dsimp only at hC; rwa [hUEq] at hC),
        hWf.recv_fresh⟩, le_rfl, le_rfl⟩
  cases q with
  | sendOPK u i bundle m0 m1 =>
    simp only [isAuthSessQueryB, ↓reduceIte, authCkSlotsStepWith]
    exact forall_mem_support_ite _ _ _ _
      (forall_support_pure _ _ ⟨hWf, le_rfl, Nat.le_add_right _ 1⟩)
      (hSend (.sendOPK u i) trivial u bundle m0 m1)
  | sendNoOPK u i bundle m0 m1 =>
    simp only [isAuthSessQueryB, ↓reduceIte, authCkSlotsStepWith]
    exact forall_mem_support_ite _ _ _ _
      (forall_support_pure _ _ ⟨hWf, le_rfl, Nat.le_add_right _ 1⟩)
      (hSend (.sendNoOPK u i) trivial u bundle m0 m1)
  | recvOPK k j o msg =>
    simp only [isAuthSessQueryB, ↓reduceIte, authCkSlotsStepWith]
    exact hRecv msg _ (fun prep hP res? => prepareAuthHybridRecvOPK_usedSendSessions true P k j o msg _ hP res?)
  | recvNoOPK k j l msg =>
    simp only [isAuthSessQueryB, ↓reduceIte, authCkSlotsStepWith]
    exact hRecv msg _ (fun prep hP res? => prepareAuthHybridRecvNoOPK_usedSendSessions true P k j l msg _ hP res?)
  | initPrin u =>
    simp only [isAuthSessQueryB, Bool.false_eq_true, ↓reduceIte, Nat.add_zero, authCkSlotsStepWith]
    exact hNotSess _ (fun _ _ _ _ _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h)
  | corruptIK u =>
    simp only [isAuthSessQueryB, Bool.false_eq_true, ↓reduceIte, Nat.add_zero, authCkSlotsStepWith]
    exact hNotSess _ (fun _ _ _ _ _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h)
  | genSPK u j =>
    simp only [isAuthSessQueryB, Bool.false_eq_true, ↓reduceIte, Nat.add_zero, authCkSlotsStepWith]
    exact hNotSess _ (fun _ _ _ _ _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h)
  | genOPK u j o =>
    simp only [isAuthSessQueryB, Bool.false_eq_true, ↓reduceIte, Nat.add_zero, authCkSlotsStepWith]
    exact hNotSess _ (fun _ _ _ _ _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h)
  | registerKey sk =>
    simp only [isAuthSessQueryB, Bool.false_eq_true, ↓reduceIte, Nat.add_zero, authCkSlotsStepWith]
    exact hNotSess _ (fun _ _ _ _ _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h)
  | roQuery secrets =>
    simp only [isAuthSessQueryB, Bool.false_eq_true, ↓reduceIte, Nat.add_zero, authCkSlotsStepWith]
    exact hNotSess _ (fun _ _ _ _ _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h)
  | roRootQuery rk dh =>
    simp only [isAuthSessQueryB, Bool.false_eq_true, ↓reduceIte, Nat.add_zero, authCkSlotsStepWith]
    exact hNotSess _ (fun _ _ _ _ _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h)
  | revealDhSecrets =>
    simp only [isAuthSessQueryB, Bool.false_eq_true, ↓reduceIte, Nat.add_zero, authCkSlotsStepWith]
    exact hNotSess _ (fun _ _ _ _ _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h)

private theorem ite_congr_eq {α : Type} (c : Bool) (t1 e1 t2 e2 : α)
    (ht : t1 = t2) (he : e1 = e2) :
    (if c then t1 else e1) = if c then t2 else e2 := by cases c <;> assumption

private theorem authCkSlotsStepWith_congr (S : Setup) (P : Primitives)
    (samp1 samp2 : Nat → ProbComp (Bytes × Bytes))
    (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (hSendEq : ∀ sid, IsSendSessionId S sid →
      hst.toAuthHybridState.base.usedSendSessions.contains sid = false →
      samp1 (hst.slots.allocSend sid).1 = samp2 (hst.slots.allocSend sid).1)
    (hRecvEq : samp1 (hst.slots.allocRecv hst.recvCount).1 = samp2 (hst.slots.allocRecv hst.recvCount).1) :
    authCkSlotsStepWith S P samp1 q hst = authCkSlotsStepWith S P samp2 q hst := by
  have hSend : ∀ sid, IsSendSessionId S sid → ∀ u bundle m0 m1,
      authCkSendWithSlots S P samp1 sid u bundle m0 m1 hst =
        authCkSendWithSlots S P samp2 sid u bundle m0 m1 hst := by
    intro sid hSid u bundle m0 m1; unfold authCkSendWithSlots; dsimp only
    refine ite_congr_eq _ _ _ _ _ rfl ?_
    refine ite_congr_eq _ _ _ _ _ rfl ?_
    cases hU : hst.toAuthHybridState.base.usedSendSessions.contains sid
    · simp only [Bool.false_eq_true, ↓reduceIte]; rw [hSendEq sid hSid hU]
    · simp only [↓reduceIte]
  cases q with
  | sendOPK u i bundle m0 m1 =>
    unfold authCkSlotsStepWith; dsimp only
    exact ite_congr_eq _ _ _ _ _ rfl (hSend (.sendOPK u i) trivial u bundle m0 m1)
  | sendNoOPK u i bundle m0 m1 =>
    unfold authCkSlotsStepWith; dsimp only
    exact ite_congr_eq _ _ _ _ _ rfl (hSend (.sendNoOPK u i) trivial u bundle m0 m1)
  | recvOPK k j o msg => unfold authCkSlotsStepWith authCkRecvWithSlots; dsimp only; rw [hRecvEq]
  | recvNoOPK k j l msg => unfold authCkSlotsStepWith authCkRecvWithSlots; dsimp only; rw [hRecvEq]
  | _ => rfl

private theorem authCkSlotsStepWith_after (S : Setup) (P : Primitives) (idx : Nat) (b : Bool)
    (k : Bytes × Bytes) (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (hWf : CkSlotWf S hst) (hFired : authCreationSlotFired idx hst = true) :
    authCkSlotsStepWith S P (fun s => if s == idx then pure k else sampCkPair P (s < idx)) q hst =
      authCkSlotsStepWith S P (fun s => sampCkPair P (s < (if b then idx else idx + 1))) q hst ∧
    ∀ x ∈ support
      (authCkSlotsStepWith S P (fun s => sampCkPair P (s < (if b then idx else idx + 1))) q hst),
      authCreationSlotFired idx x.2 = true := by
  simp only [authCreationSlotFired, decide_eq_true_eq] at hFired
  refine ⟨authCkSlotsStepWith_congr S P _ _ q hst (fun sid hSid hFresh => ?_) ?_, fun x hx => ?_⟩
  · have hSlot := (allocSend_of_none hst.slots sid hSid (hWf.send_fresh sid hFresh)).1
    have hne : (hst.slots.allocSend sid).1 ≠ idx := by omega
    simp only [beq_eq_false_iff_ne.mpr hne, Bool.false_eq_true, ↓reduceIte, lt_cutoff_bool_eq b hne]
  · have hSlot := (allocRecv_of_none (S := S) hst.slots hst.recvCount (hWf.recv_fresh hst.recvCount le_rfl)).1
    have hne : (hst.slots.allocRecv hst.recvCount).1 ≠ idx := by omega
    simp only [beq_eq_false_iff_ne.mpr hne, Bool.false_eq_true, ↓reduceIte, lt_cutoff_bool_eq b hne]
  · have hLe := (support_authCkSlotsStepWith S P _ q hst hWf x hx).2.1
    simp only [authCreationSlotFired, decide_eq_true_eq]; omega

private theorem evalDist_preSample_authCkSlots_eq_cutoff (S : Setup) (P : Primitives)
    (idx : Nat) (b : Bool) (A : AuthAdversary S) :
    𝒟[sampCkPair P (!b) >>= fun p => authCkSlotsPreSampleRun S P idx p A] =
      𝒟[authCkSlotsCutoffExp S P (if b then idx else idx + 1) A] := by
  unfold authCkSlotsPreSampleRun authCkSlotsCutoffExp
  rw [OracleComp.evalDist_bind_bind_swap]
  refine OracleComp.evalDist_bind_congr_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  exact SlotM.evalDist_preSample_eq_lazy_of_slotStep_inv
    (sampCkPair P (!b)) (CkSlotWf S) (authCreationSlotFired idx)
    (fun q => StateT.mk (fun hst =>
      authCkSlotsStepWith S P (fun s => sampCkPair P (s < (if b then idx else idx + 1))) q hst))
    (fun p q => StateT.mk (fun hst =>
      authCkSlotsStepWith S P (fun s => if s == idx then pure p else sampCkPair P (s < idx)) q hst))
    (authCkSlotsStepSlot S P idx (sampCkPair P (!b)))
    (authCkSlotsStepSlot_slotComp S P idx (sampCkPair P (!b)))
    (authCkSlotsStepSlot_run'_some S P idx (sampCkPair P (!b)))
    (fun q hst g _ => by dsimp only [StateT.run_mk]; rw [authCkSlotsStepSlot_run'_none_eq S P idx b q hst])
    (fun p q hst hWf hFired => authCkSlotsStepWith_after S P idx b p q hst hWf hFired)
    (fun q hst y hWf hy hSome => authCkSlotsStepSlot_fire S P idx (sampCkPair P (!b)) q hst hWf y hy hSome)
    (fun q hst hWf x hx => (support_authCkSlotsStepWith S P _ q hst hWf x hx).1)
    (fun q hst hWf => SlotM.wf_run_none_of_run'_eq _ _
      (authCkSlotsStepSlot_run'_none_eq S P idx b q hst)
      (fun x hx => (support_authCkSlotsStepWith S P _ q hst hWf x hx).1))
    A.run (AuthHybridStateFixed.empty S secb) (ckSlotWf_empty S secb)
    (fun x => finalizeAuthFixed P secb x.1 x.2.toAuthHybridState)

private theorem evalDist_authCkSlotsCutoffExp_zero_eq_g3_6 (S : Setup) (P : Primitives)
    (A : AuthAdversary S) :
    𝒟[authCkSlotsCutoffExp S P 0 A] = 𝒟[authFixedExpAtStage .g3_6 S P A] := by
  rw [← evalDist_authCkCutoffExp_zero_eq_g3_6 S P A]
  unfold authCkSlotsCutoffExp authCkCutoffExp
  refine OracleComp.evalDist_bind_congr_of_support ($ᵗ Bool) _ _ (fun secb _ =>
    congrArg (fun m => 𝒟[m]) ?_)
  have hInit : projSlots0 (AuthHybridStateFixed.empty S secb) = AuthHybridStateFixed.empty S secb := rfl
  conv_rhs => rw [← hInit]
  symm
  let samp0 := fun s => sampCkPair P (s < 0)
  exact simulateQ_proj_inv_obs
    projSlots0 (fun _ => True)
    (fun q => StateT.mk (fun hst => authCkSlotsStepWith S P samp0 q hst))
    (fun q => StateT.mk (fun hst => authCkStepWith S P samp0 q hst))
    (fun q hst _ => ⟨by
      dsimp only [StateT.run_mk]
      cases q with
      | sendOPK u i bundle m0 m1 =>
        unfold authCkSlotsStepWith authCkStepWith; dsimp only
        exact (map_ite_eq _ _ _ _ _ _ (by simp only [map_pure, Prod.map, id_eq, projSlots0])
          (map_projSlots0_authCkSendWithSlots S P samp0 samp0 (.sendOPK u i) u bundle m0 m1 hst (fun _ => rfl))).symm
      | sendNoOPK u i bundle m0 m1 =>
        unfold authCkSlotsStepWith authCkStepWith; dsimp only
        exact (map_ite_eq _ _ _ _ _ _ (by simp only [map_pure, Prod.map, id_eq, projSlots0])
          (map_projSlots0_authCkSendWithSlots S P samp0 samp0 (.sendNoOPK u i) u bundle m0 m1 hst (fun _ => rfl))).symm
      | recvOPK k j o msg => exact (map_projSlots0_authCkRecvWithSlots S P samp0 samp0 msg _ hst rfl).symm
      | recvNoOPK k j l msg => exact (map_projSlots0_authCkRecvWithSlots S P samp0 samp0 msg _ hst rfl).symm
      | initPrin u => exact (map_projSlots0_authCkOtherStep S P _ hst).symm
      | corruptIK u => exact (map_projSlots0_authCkOtherStep S P _ hst).symm
      | genSPK u j => exact (map_projSlots0_authCkOtherStep S P _ hst).symm
      | genOPK u j o => exact (map_projSlots0_authCkOtherStep S P _ hst).symm
      | registerKey sk => exact (map_projSlots0_authCkOtherStep S P _ hst).symm
      | roQuery secrets => exact (map_projSlots0_authCkOtherStep S P _ hst).symm
      | roRootQuery rk dh => exact (map_projSlots0_authCkOtherStep S P _ hst).symm
      | revealDhSecrets => exact (map_projSlots0_authCkOtherStep S P _ hst).symm,
      fun _ _ => trivial⟩)
    A.run (AuthHybridStateFixed.empty S secb) trivial
    (fun x => finalizeAuthFixed P secb x.1 x.2.toAuthHybridState)
    (fun x => finalizeAuthFixed P secb x.1 x.2.toAuthHybridState) (fun _ _ => rfl)

private theorem evalDist_authCkSlotsCutoffExp_end_eq_g3_7 (S : Setup) (P : Primitives)
    (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    𝒟[authCkSlotsCutoffExp S P (min b.q_total S.N_sess_tot) A.1] =
      𝒟[authFixedExpAtStage .g3_7 S P A.1] := by
  let M := min b.q_total S.N_sess_tot
  let sampM := fun s => sampCkPair P (s < M)
  let sampTrue : Nat → ProbComp (Bytes × Bytes) := fun _ => sampCkPair P true
  let sampN := fun s => sampCkPair P (s < S.N_sess_tot)
  rw [← evalDist_authCkCutoffExp_end_eq_g3_7 S P b A]
  unfold authCkSlotsCutoffExp authCkCutoffExp
  refine OracleComp.evalDist_bind_congr_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  let allIdealImpl : QueryImpl (authSpec S) (StateT (AuthHybridStateFixed S) ProbComp) :=
    fun q => StateT.mk (fun hst => authCkStepWith S P sampTrue q hst)
  let fullIdeal := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (AuthHybridStateFixed S) ProbComp) + allIdealImpl
  have hLeft :
      𝒟[(simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
            (StateT (AuthHybridStateFixed S) ProbComp) +
            fun q => StateT.mk (fun hst => authCkSlotsStepWith S P sampM q hst))
          A.1.run).run (AuthHybridStateFixed.empty S secb) >>=
          fun x => finalizeAuthFixed P secb x.1 x.2.toAuthHybridState] =
      𝒟[(simulateQ fullIdeal A.1.run).run (AuthHybridStateFixed.empty S secb) >>=
          fun x => finalizeAuthFixed P secb x.1 x.2.toAuthHybridState] :=
    evalDist_simulateQ_proj_inv_bound
      projSlots0 (CkSlotWf S) (fun hst => hst.slots.nextSlot)
      (isAuthSessQueryB (S := S)) (fun _ => rfl) M
      (fun q => StateT.mk (fun hst => authCkSlotsStepWith S P sampM q hst))
      allIdealImpl
      (fun q hst hWf hLt => ⟨fun k => by
        dsimp only [StateT.run_mk, allIdealImpl]
        have hMap : Prod.map id projSlots0 <$>
            authCkSlotsStepWith S P sampM q hst =
            authCkStepWith S P sampTrue q (projSlots0 hst) := by
          cases q with
          | sendOPK u i bundle m0 m1 =>
            have hM := hLt rfl; unfold authCkSlotsStepWith authCkStepWith; dsimp only
            exact map_ite_eq _ _ _ _ _ _ (by simp only [map_pure, Prod.map, id_eq, projSlots0])
              (map_projSlots0_authCkSendWithSlots S P sampM sampTrue (.sendOPK u i) u bundle m0 m1 hst (fun hnu => by
                have hS := (allocSend_of_none hst.slots (.sendOPK u i) trivial
                  (hWf.send_fresh _ (Bool.eq_false_iff.mpr hnu))).1
                exact congrArg (sampCkPair P) (decide_eq_true (hS ▸ hM))))
          | sendNoOPK u i bundle m0 m1 =>
            have hM := hLt rfl; unfold authCkSlotsStepWith authCkStepWith; dsimp only
            exact map_ite_eq _ _ _ _ _ _ (by simp only [map_pure, Prod.map, id_eq, projSlots0])
              (map_projSlots0_authCkSendWithSlots S P sampM sampTrue (.sendNoOPK u i) u bundle m0 m1 hst (fun hnu => by
                have hS := (allocSend_of_none hst.slots (.sendNoOPK u i) trivial
                  (hWf.send_fresh _ (Bool.eq_false_iff.mpr hnu))).1
                exact congrArg (sampCkPair P) (decide_eq_true (hS ▸ hM))))
          | recvOPK k' j o msg =>
            have hR := (allocRecv_of_none (S := S) hst.slots hst.recvCount (hWf.recv_fresh _ le_rfl)).1
            exact map_projSlots0_authCkRecvWithSlots S P sampM sampTrue msg _ hst
              (congrArg (sampCkPair P) (decide_eq_true (hR ▸ hLt rfl)))
          | recvNoOPK k' j l msg =>
            have hR := (allocRecv_of_none (S := S) hst.slots hst.recvCount (hWf.recv_fresh _ le_rfl)).1
            exact map_projSlots0_authCkRecvWithSlots S P sampM sampTrue msg _ hst
              (congrArg (sampCkPair P) (decide_eq_true (hR ▸ hLt rfl)))
          | initPrin u => exact map_projSlots0_authCkOtherStep S P _ hst
          | corruptIK u => exact map_projSlots0_authCkOtherStep S P _ hst
          | genSPK u j => exact map_projSlots0_authCkOtherStep S P _ hst
          | genOPK u j o => exact map_projSlots0_authCkOtherStep S P _ hst
          | registerKey sk => exact map_projSlots0_authCkOtherStep S P _ hst
          | roQuery secrets => exact map_projSlots0_authCkOtherStep S P _ hst
          | roRootQuery rk dh => exact map_projSlots0_authCkOtherStep S P _ hst
          | revealDhSecrets => exact map_projSlots0_authCkOtherStep S P _ hst
        rw [← hMap, bind_map_left]; rfl,
        fun x hx => by
          obtain ⟨hW, _, hB⟩ := support_authCkSlotsStepWith S P sampM q hst hWf x hx
          exact ⟨hW, hB⟩⟩)
      A.1.run M (isQueryBoundP_isAuthSessQueryB_min S b A)
      (AuthHybridStateFixed.empty S secb) (ckSlotWf_empty S secb) (by simp [AuthHybridStateFixed.empty])
      (fun x => finalizeAuthFixed P secb x.1 x.2.toAuthHybridState)
  have hRight :
      𝒟[(simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
            (StateT (AuthHybridStateFixed S) ProbComp) +
            fun q => StateT.mk (fun hst => authCkStepWith S P sampN q hst))
          A.1.run).run (AuthHybridStateFixed.empty S secb) >>=
          fun x => finalizeAuthFixed P secb x.1 x.2.toAuthHybridState] =
      𝒟[(simulateQ fullIdeal A.1.run).run (AuthHybridStateFixed.empty S secb) >>=
          fun x => finalizeAuthFixed P secb x.1 x.2.toAuthHybridState] := by
    have hRecvB : OracleComp.IsQueryBoundP A.1.run (fun q => isAuthRecvQueryB q = true) S.N_recv_tot := by
      simpa only [isAuthRecvQueryB_eq_true_iff] using A.2.2.2.1
    exact evalDist_simulateQ_proj_inv_bound
      id (fun _ => True) (fun hst => hst.recvCount)
      (isAuthRecvQueryB (S := S)) (fun _ => rfl) S.N_recv_tot
      (fun q => StateT.mk (fun hst => authCkStepWith S P sampN q hst))
      allIdealImpl
      (fun q hst _ hRecvLt => ⟨fun k => by
        dsimp only [StateT.run_mk, allIdealImpl, id_eq]
        have hEq : authCkStepWith S P sampN q hst =
            authCkStepWith S P sampTrue q hst := by
          cases q with
          | sendOPK u i bundle m0 m1 =>
            have hSid : sessionSlotIndex (SessionId.sendOPK u i) < S.N_sess_tot := by
              dsimp only [sessionSlotIndex, Setup.N_sess_tot, Setup.N_send_tot, Setup.N_send_opk_tot]
              have := Nat.mul_le_mul_right S.N_send_opk (Nat.succ_le_of_lt u.isLt)
              nlinarith [i.isLt]
            unfold authCkStepWith; dsimp only
            exact ite_congr_eq _ _ _ _ _ rfl
              (authCkSendWith_congr_slot S P sampN sampTrue _ u bundle m0 m1 hst
                (congrArg (sampCkPair P) (decide_eq_true hSid)))
          | sendNoOPK u i bundle m0 m1 =>
            have hSid : sessionSlotIndex (SessionId.sendNoOPK u i) < S.N_sess_tot := by
              dsimp only [sessionSlotIndex, Setup.N_sess_tot, Setup.N_send_tot, Setup.N_send_no_opk_tot]
              have := Nat.mul_le_mul_right S.N_send_no_opk (Nat.succ_le_of_lt u.isLt)
              nlinarith [i.isLt]
            unfold authCkStepWith; dsimp only
            exact ite_congr_eq _ _ _ _ _ rfl
              (authCkSendWith_congr_slot S P sampN sampTrue _ u bundle m0 m1 hst
                (congrArg (sampCkPair P) (decide_eq_true hSid)))
          | recvOPK k' j o msg =>
            have hLt : S.N_send_tot + hst.recvCount < S.N_sess_tot := by
              have := hRecvLt rfl; unfold Setup.N_sess_tot; omega
            exact authCkRecvWith_congr_slot S P sampN sampTrue msg _ hst
              (congrArg (sampCkPair P) (decide_eq_true hLt))
          | recvNoOPK k' j l msg =>
            have hLt : S.N_send_tot + hst.recvCount < S.N_sess_tot := by
              have := hRecvLt rfl; unfold Setup.N_sess_tot; omega
            exact authCkRecvWith_congr_slot S P sampN sampTrue msg _ hst
              (congrArg (sampCkPair P) (decide_eq_true hLt))
          | _ => rfl
        rw [hEq],
        fun x hx => ⟨trivial, by
          have hSendCnt : ∀ sid u bundle m0 m1,
              ∀ y ∈ support (authCkSendWith S P sampN sid u bundle m0 m1 hst),
                y.2.recvCount = hst.recvCount := by
            intro sid u bundle m0 m1; unfold authCkSendWith; dsimp only
            refine forall_mem_support_ite _ _ _ _ (forall_support_pure _ _ rfl) ?_
            refine forall_mem_support_ite _ _ _ _ (forall_support_pure _ _ rfl) ?_
            refine forall_mem_support_ite _ _ _ _ (forall_support_pure _ _ rfl) ?_
            cases hst.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == u.val) with
            | none => exact forall_support_pure _ _ rfl
            | some uPair =>
              rcases uPair with ⟨_, uEntry⟩; dsimp only
              refine forall_mem_support_ite _ _ _ _ (forall_support_pure _ _ rfl) ?_
              refine forall_mem_support_ite _ _ _ _ (forall_support_pure _ _ rfl) ?_
              refine forall_support_bind _ _ _ (fun ekASk => ?_)
              refine forall_support_bind _ _ _ (fun kemCoins => ?_)
              refine forall_support_bind _ _ _ (fun ephASk => ?_)
              refine forall_support_bind _ _ _ (fun spqrCoins => ?_)
              refine forall_mem_support_ite _ _ _ _ (forall_support_pure _ _ rfl) ?_
              cases P.kemEncaps bundle.pqspkB kemCoins with
              | none => exact forall_support_pure _ _ rfl
              | some pair =>
                rcases pair with ⟨ss, kemCt⟩; dsimp only
                refine forall_mem_support_ite _ _ _ _ ?_ ?_
                · refine forall_support_bind _ _ _ (fun drKey => ?_)
                  refine forall_support_bind _ _ _ (fun rk1 => ?_)
                  cases P.spqrInitSend drKey.pqrKey spqrCoins with
                  | none => exact forall_support_pure _ _ rfl
                  | some spqrVal =>
                    rcases spqrVal with ⟨_, spqrSalt?, pqRatchetMsg⟩
                    exact forall_support_bind _ _ _ (fun _ => forall_support_pure _ _ rfl)
                · refine forall_support_bind _ _ _ (fun ⟨drKey, roCache'⟩ => ?_)
                  refine forall_support_bind _ _ _ (fun ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩ => ?_)
                  cases P.spqrInitSend drKey.pqrKey spqrCoins with
                  | none => exact forall_support_pure _ _ rfl
                  | some spqrVal => rcases spqrVal with ⟨_, spqrSalt?, pqRatchetMsg⟩; exact forall_support_pure _ _ rfl
          have hRecvCnt : ∀ msg prep?,
              ∀ y ∈ support (authCkRecvWith S P sampN msg prep? hst),
                y.2.recvCount = hst.recvCount + 1 := by
            intro msg prep?; unfold authCkRecvWith
            cases prep? with
            | none => exact forall_support_pure _ _ rfl
            | some prep =>
              dsimp only
              refine forall_mem_support_ite _ _ _ _ ?_ ?_
              · cases prep.matchedSess? with
                | some s =>
                  dsimp only
                  refine forall_mem_support_ite _ _ _ _ ?_ ?_
                  · cases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
                    | none => exact forall_support_pure _ _ rfl
                    | some pqr => rcases pqr with ⟨_, spqrSalt?⟩; exact forall_support_pure _ _ rfl
                  · refine forall_support_bind _ _ _ (fun rk1 => ?_)
                    cases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
                    | none => exact forall_support_pure _ _ rfl
                    | some pqr =>
                      rcases pqr with ⟨_, spqrSalt?⟩
                      exact forall_support_bind _ _ _ (fun _ => forall_support_pure _ _ rfl)
                | none =>
                  refine forall_support_bind _ _ _ (fun drKey => ?_)
                  refine forall_support_bind _ _ _ (fun rk1 => ?_)
                  cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
                  | none => exact forall_support_pure _ _ rfl
                  | some pqr =>
                    rcases pqr with ⟨_, spqrSalt?⟩
                    exact forall_support_bind _ _ _ (fun _ => forall_support_pure _ _ rfl)
              · refine forall_support_bind _ _ _ (fun ⟨drKey, roCache'⟩ => ?_)
                refine forall_support_bind _ _ _ (fun ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩ => ?_)
                cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
                | none => exact forall_support_pure _ _ rfl
                | some pqr => rcases pqr with ⟨_, spqrSalt?⟩; exact forall_support_pure _ _ rfl
          cases q with
          | sendOPK u i bundle m0 m1 =>
            simp only [isAuthRecvQueryB, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
            exact le_of_eq (forall_mem_support_ite _ _ _ (fun y : AuthResponse × AuthHybridStateFixed S => y.2.recvCount = hst.recvCount)
              (forall_support_pure _ (fun y : AuthResponse × AuthHybridStateFixed S => y.2.recvCount = hst.recvCount) rfl)
              (hSendCnt _ u bundle m0 m1) x hx)
          | sendNoOPK u i bundle m0 m1 =>
            simp only [isAuthRecvQueryB, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
            exact le_of_eq (forall_mem_support_ite _ _ _ (fun y : AuthResponse × AuthHybridStateFixed S => y.2.recvCount = hst.recvCount)
              (forall_support_pure _ (fun y : AuthResponse × AuthHybridStateFixed S => y.2.recvCount = hst.recvCount) rfl)
              (hSendCnt _ u bundle m0 m1) x hx)
          | recvOPK k' j o msg => simp only [isAuthRecvQueryB, ↓reduceIte]; exact le_of_eq (hRecvCnt msg _ x hx)
          | recvNoOPK k' j l msg => simp only [isAuthRecvQueryB, ↓reduceIte]; exact le_of_eq (hRecvCnt msg _ x hx)
          | initPrin _ => simp only [isAuthRecvQueryB, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]; exact le_of_eq (support_authCkOtherStep P _ hst hx).2
          | corruptIK _ => simp only [isAuthRecvQueryB, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]; exact le_of_eq (support_authCkOtherStep P _ hst hx).2
          | genSPK _ _ => simp only [isAuthRecvQueryB, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]; exact le_of_eq (support_authCkOtherStep P _ hst hx).2
          | genOPK _ _ _ => simp only [isAuthRecvQueryB, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]; exact le_of_eq (support_authCkOtherStep P _ hst hx).2
          | registerKey _ => simp only [isAuthRecvQueryB, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]; exact le_of_eq (support_authCkOtherStep P _ hst hx).2
          | roQuery _ => simp only [isAuthRecvQueryB, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]; exact le_of_eq (support_authCkOtherStep P _ hst hx).2
          | roRootQuery _ _ => simp only [isAuthRecvQueryB, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]; exact le_of_eq (support_authCkOtherStep P _ hst hx).2
          | revealDhSecrets => simp only [isAuthRecvQueryB, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]; exact le_of_eq (support_authCkOtherStep P _ hst hx).2⟩⟩)
      A.1.run S.N_recv_tot hRecvB
      (AuthHybridStateFixed.empty S secb) trivial (by simp [AuthHybridStateFixed.empty])
      (fun x => finalizeAuthFixed P secb x.1 x.2.toAuthHybridState)
  exact hLeft.trans hRight.symm

/-- Advantage bound for the `G3.6 → G3.7` `PrfChainKey` sub-hop via `prfCkReductionAuthFixed`. -/
theorem hop_G3_6_G3_7 (S : Setup) : AuthHopG3_6G3_7Stmt S (prfCkReductionAuthFixed S) := by
  intro P _hP b A
  let M := min b.q_total S.N_sess_tot
  change |(𝒟[authFixedExpAtStage .g3_6 S P A.1].boolBias).toReal -
          (𝒟[authFixedExpAtStage .g3_7 S P A.1].boolBias).toReal| ≤
    2 * (S.N_sess_tot : ℝ) * (𝒟[prfCkExp P (prfCkReductionAuthFixed S b A)].boolBias).toReal
  rw [← evalDist_authCkSlotsCutoffExp_zero_eq_g3_6 S P A.1,
      ← evalDist_authCkSlotsCutoffExp_end_eq_g3_7 S P b A]
  have hPrfEq :
      𝒟[prfCkExp P (prfCkReductionAuthFixed S b A)] =
        𝒟[do
          let ch ← $ᵗ Bool
          let z ← if ch then (sampleIndexRange M >>= fun idx =>
                    sampCkPair P false >>= fun p => authCkSlotsPreSampleRun S P idx p A.1)
                  else (sampleIndexRange M >>= fun idx =>
                    sampCkPair P true >>= fun p => authCkSlotsPreSampleRun S P idx p A.1)
          return (ch == z)] := by
    rw [prfCkExp_eq_sampCkPair]
    refine OracleComp.evalDist_bind_congr_of_support ($ᵗ Bool) _ _ (fun ch _ => ?_)
    unfold prfCkReductionAuthFixed; dsimp only
    simp only [simulateQ_bind, simulateQ_embedUnif, simulateQ_authCkSlotsPreSampleRunPrim, bind_assoc]
    rw [OracleComp.evalDist_bind_bind_swap (sampCkPair P (!ch)) (sampleIndexRange M)]
    cases ch <;> simp only [Bool.not_true, Bool.not_false, ↓reduceIte, Bool.false_eq_true, Bool.beq_comm]
  have hStep :
      |(𝒟[authCkSlotsCutoffExp S P 0 A.1].boolBias).toReal -
       (𝒟[authCkSlotsCutoffExp S P M A.1].boolBias).toReal| ≤
        2 * (M : ℝ) * (𝒟[prfCkExp P (prfCkReductionAuthFixed S b A)].boolBias).toReal := by
    rw [hPrfEq]
    exact abs_sub_boolBias_le_two_mul_sampleIndexRange_coin_game M
      (fun k => authCkSlotsCutoffExp S P k A.1)
      (fun idx => sampCkPair P false >>= fun p => authCkSlotsPreSampleRun S P idx p A.1)
      (fun idx => sampCkPair P true >>= fun p => authCkSlotsPreSampleRun S P idx p A.1)
      (fun idx _ => by
        have h := evalDist_preSample_authCkSlots_eq_cutoff S P idx true A.1
        simp only [Bool.not_true, ↓reduceIte] at h; rw [h])
      (fun idx _ => by
        have h := evalDist_preSample_authCkSlots_eq_cutoff S P idx false A.1
        simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte] at h; rw [h])
  refine le_trans hStep ?_
  have hM : (M : ℝ) ≤ (S.N_sess_tot : ℝ) := Nat.cast_le.mpr (Nat.min_le_right _ _)
  have hBiasNonneg : 0 ≤ (𝒟[prfCkExp P (prfCkReductionAuthFixed S b A)].boolBias).toReal :=
    ENNReal.toReal_nonneg
  nlinarith

end AuthSubHops1to3

end SignalPqxdh.Security
