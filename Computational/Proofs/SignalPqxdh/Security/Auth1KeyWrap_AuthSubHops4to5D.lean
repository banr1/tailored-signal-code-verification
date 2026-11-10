/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5C
public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5B
public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5B3
public import Computational.Proofs.SignalPqxdh.Security.FgGapDhC
public import Computational.Proofs.SignalPqxdh.Security.RoKemHopA
public import Computational.Proofs.SignalPqxdh.Security.SigHop
public import VCVio.CryptoFoundations.SecExp.Measure
public import VCVio.EvalDist.Monad.Basic
public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5D
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyHybrid
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5B
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5B2
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5B3
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5C
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_Collisions
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_CollisionsB
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_TwoKeyAndAuthStatements
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrapBase
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyShallowSims

/-!
# One-Key `G3.8` to `G5` AEAD Sub-Hop Assembly

Equates `authSplitFixedExp1Key .g3_8 .g5` with the `IND-CPA` coin-cutoff experiment, bounds the
`G4` to `G5` `IND-CPA` sub-hop, and assembles `AuthSubHops4to5Bundle1Key` from a multi-key
INT-CTXT reduction.
-/

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 400000
open Classical
open OracleSpec OracleComp MeasureTheory ENNReal BigOperators
namespace SignalPqxdh.Security
open SignalPqxdh
open _root_.Proofs.SignalPqxdh.Security
open _root_.Proofs.SignalPqxdh.Security.FgGapDh (initSessionSlotIdx initSessionSlotIdx_sendOPK_lt
  initSessionSlotIdx_sendNoOPK_lt)

private structure ValidAuthCpaState (S : Setup) (P : Primitives) (secb : Bool)
    (hst : AuthHybridStateFixed S) : Prop where
  validEc      : ValidEcLists S hst.toAuthHybridState.base.principals
                   hst.toAuthHybridState.base.spkBundles
                   hst.toAuthHybridState.base.opkEntries
                   hst.toAuthHybridState.base.usedSendSessions
  sess_le      : hst.toAuthHybridState.base.sessions.length ≤
                   hst.toAuthHybridState.base.usedSendSessions.length
  ideal_le     : hst.toAuthHybridState.idealSessions.length ≤
                   hst.toAuthHybridState.base.usedSendSessions.length
  validKem     : ValidRecvKemRecords P hst.toAuthHybridState.recvKemRecs
  ideal_ik_mem : ∀ s ∈ hst.toAuthHybridState.idealSessions,
                   ∃ u e, (u, e) ∈ hst.toAuthHybridState.base.principals ∧ e.ikAPk = s.ikAPk
  secb_eq      : hst.toAuthHybridState.base.secb = secb
private theorem validAuthCpaState_empty (S : Setup) (P : Primitives) (secb : Bool) :
    ValidAuthCpaState S P secb (AuthHybridStateFixed.empty S secb) :=
  ⟨validEcLists_nil S, le_rfl, le_rfl, (fun _ h => by cases h), (fun _ h => by cases h), rfl⟩
private theorem ValidAuthCpaState.sum_lengths_le {S : Setup} {P : Primitives} {secb : Bool}
    {hst : AuthHybridStateFixed S} (h : ValidAuthCpaState S P secb hst) :
    hst.toAuthHybridState.base.principals.length +
    hst.toAuthHybridState.base.spkBundles.length +
    hst.toAuthHybridState.base.opkEntries.length +
    hst.toAuthHybridState.base.usedSendSessions.length ≤ S.N_dh := by
  let st := hst.toAuthHybridState.base
  let sessPks : List (SessionId S × Bytes) := st.usedSendSessions.map (fun sid => (sid, []))
  have hMap : sessPks.map Prod.fst = st.usedSendSessions := by
    simp [sessPks, List.map_map, Function.comp_def]
  have hV : ValidEcLists S st.principals st.spkBundles st.opkEntries (sessPks.map Prod.fst) := by
    rw [hMap]; exact h.validEc
  have hTag :=
    validTaggedPks_ecTaggedFromLists S P st.principals st.spkBundles st.opkEntries sessPks hV
  have hLen := validTaggedPks_length_le hTag
  unfold ecTaggedFromLists at hLen
  simp only [sessPks, List.length_append, List.length_map] at hLen
  exact hLen
private theorem ValidAuthCpaState.principals_le {S : Setup} {P : Primitives} {secb : Bool}
    {hst : AuthHybridStateFixed S} (h : ValidAuthCpaState S P secb hst) :
    hst.toAuthHybridState.base.principals.length ≤ S.N_dh := by
  have := h.sum_lengths_le; omega
private theorem ValidAuthCpaState.spkBundles_le {S : Setup} {P : Primitives} {secb : Bool}
    {hst : AuthHybridStateFixed S} (h : ValidAuthCpaState S P secb hst) :
    hst.toAuthHybridState.base.spkBundles.length ≤ S.N_dh := by
  have := h.sum_lengths_le; omega
private theorem ValidAuthCpaState.opkEntries_le {S : Setup} {P : Primitives} {secb : Bool}
    {hst : AuthHybridStateFixed S} (h : ValidAuthCpaState S P secb hst) :
    hst.toAuthHybridState.base.opkEntries.length ≤ S.N_dh := by
  have := h.sum_lengths_le; omega
private theorem ValidAuthCpaState.usedSend_le {S : Setup} {P : Primitives} {secb : Bool}
    {hst : AuthHybridStateFixed S} (h : ValidAuthCpaState S P secb hst) :
    hst.toAuthHybridState.base.usedSendSessions.length ≤ S.N_dh := by
  have := h.sum_lengths_le; omega
private theorem ValidAuthCpaState.sessions_le {S : Setup} {P : Primitives} {secb : Bool}
    {hst : AuthHybridStateFixed S} (h : ValidAuthCpaState S P secb hst) :
    hst.toAuthHybridState.base.sessions.length ≤ S.N_dh :=
  le_trans h.sess_le h.usedSend_le
private theorem ValidAuthCpaState.usedSend_le_send_tot {S : Setup} {P : Primitives} {secb : Bool}
    {hst : AuthHybridStateFixed S} (h : ValidAuthCpaState S P secb hst) :
    hst.toAuthHybridState.base.usedSendSessions.length ≤ S.N_send_tot := by
  have hVSess := h.validEc.2.2.2
  have hsub :
      (hst.toAuthHybridState.base.usedSendSessions.map (ecSessSlotIdx S)).Subperm
        ((List.range S.N_send_tot).map (fun x => S.N_id + S.N_spk_tot + S.N_opk_tot + x)) :=
    hVSess.2.subperm (fun y hy => by
      rw [List.mem_map] at hy
      rcases hy with ⟨sid, hsid, rfl⟩
      rw [List.mem_map]
      exact ⟨sessSlotFlatIdx S sid,
        List.mem_range.mpr (sessSlotFlatIdx_lt S sid (hVSess.1 sid hsid)), rfl⟩)
  simpa using hsub.length_le
private theorem ValidAuthCpaState.idealSessions_le_sess_tot {S : Setup} {P : Primitives} {secb :
  Bool}
    {hst : AuthHybridStateFixed S} (h : ValidAuthCpaState S P secb hst) :
    hst.toAuthHybridState.idealSessions.length ≤ S.N_sess_tot := by
  have h1 := h.ideal_le; have h2 := h.usedSend_le_send_tot
  unfold Setup.N_sess_tot; omega
private theorem ValidAuthCpaState.eraseAuthCpaFixed {S : Setup} {P : Primitives} {secb : Bool}
    {hst : AuthHybridStateFixed S} (h : ValidAuthCpaState S P secb hst) :
    ValidAuthCpaState S P true (_root_.SignalPqxdh.Security.eraseAuthCpaFixed P hst) := by
  refine ⟨h.validEc, h.sess_le, ?_, h.validKem, ?_, rfl⟩
  · simpa [ _root_.SignalPqxdh.Security.eraseAuthCpaFixed, eraseAuthCpa, eraseAuthEvents,
      cacheAuthAdvKeys] using h.ideal_le
  · intro s hs
    simp only [_root_.SignalPqxdh.Security.eraseAuthCpaFixed, eraseAuthCpa, eraseAuthEvents,
      cacheAuthAdvKeys, List.mem_map] at hs
    rcases hs with ⟨s0, hs0, rfl⟩
    exact h.ideal_ik_mem s0 hs0
private theorem validOpkEntries_map_consumed_cpa (S : Setup)
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
    rcases List.mem_map.mp he_fst with ⟨e', he', heq⟩
    rw [← heq]; exact hVO.1 e' he'
  · have h_slot : (opkEntries.map (fun (idx, e) =>
        if idx == target then (idx, { e with consumed := true }) else (idx,
          e))).map (fun e => ecOpkSlotIdx S e.1) =
        opkEntries.map (fun e => ecOpkSlotIdx S e.1) := by
      simpa [List.map_map, Function.comp_def] using congrArg (List.map (ecOpkSlotIdx S)) hFst
    rw [h_slot]; exact hVO.2
private theorem validAuthCpaState_finishAuthHybridSend {S : Setup} (P : Primitives) (secb : Bool)
    (sid : SessionId S) (hSend : IsSendSessionId S sid) (uIdx : Nat) (uEntry : PrincipalEntry)
    (peerPrincipal? : Option (Nat × PrincipalEntry)) (isFreshPeer : Bool)
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes) (ekASk ekAPk ss kemCt ephASk ephAPk : Bytes)
    (drKey : DRKey) (rk1 ck1_0 mkSeed ck1_1 : Bytes)
    (spqrSalt? : Option Bytes) (pqRatchetMsg : Bytes)
    (deriveMessageKeys : MessageKeys) (ad aeadCt msgPlain : Bytes)
    (roCache' : List (Bytes × DRKey)) (rootRoCache' : List ((Bytes × Bytes) × (Bytes × Bytes)))
    (hst : AuthHybridStateFixed S) (hV : ValidAuthCpaState S P secb hst)
    (hFresh : hst.toAuthHybridState.base.usedSendSessions.contains sid = false)
    (huMem : (uIdx, uEntry) ∈ hst.toAuthHybridState.base.principals) :
    ValidAuthCpaState S P secb
      { hst with toAuthHybridState :=
          (finishAuthHybridSend P sid uEntry peerPrincipal? isFreshPeer bundle m0 m1
            ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 ck1_0 mkSeed ck1_1
            spqrSalt? pqRatchetMsg deriveMessageKeys ad aeadCt msgPlain roCache' rootRoCache'
            hst.toAuthHybridState).2 } := by
  rcases hV with ⟨⟨hVP, hVS, hVO, hVSess⟩, hSessLe, hIdealLe, hVKem, hIkMem, hSecb⟩
  have hFresh' : hst.toAuthHybridState.base.usedSendSessions.any (fun s => s == sid) = false := by
    revert hFresh; simp; rintro h x hx rfl; exact h hx
  have hCons :=
    (validSessionIds_cons S sid hst.toAuthHybridState.base.usedSendSessions hSend hVSess hFresh').1
  refine ⟨⟨hVP, hVS, hVO, hCons⟩, ?_, ?_, hVKem, ?_, hSecb⟩
  · unfold finishAuthHybridSend; dsimp only; simp only [List.length_cons]; omega
  · unfold finishAuthHybridSend; dsimp only
    split <;> simp only [List.length_cons] <;> omega
  · intro s hs; unfold finishAuthHybridSend at hs; dsimp only at hs; split at hs
    · rcases List.mem_cons.mp hs with rfl | hs'
      · exact ⟨uIdx, uEntry, huMem, rfl⟩
      · exact hIkMem s hs'
    · exact hIkMem s hs
private theorem forall_mem_support_ite_cpa {α : Type} (c : Bool) (t e : ProbComp α) (Q : α → Prop)
    (ht : ∀ x ∈ support t, Q x) (he : ∀ x ∈ support e, Q x) :
    ∀ x ∈ support (if c then t else e), Q x := by
  cases c <;> [exact he; exact ht]
private theorem forall_mem_support_run_ite_cpa {σ α : Type} (c : Bool)
    (t e : StateT σ ProbComp α) (hst : σ) (Q : α × σ → Prop)
    (ht : ∀ x ∈ support (t.run hst), Q x) (he : ∀ x ∈ support (e.run hst), Q x) :
    ∀ x ∈ support ((if c then t else e).run hst), Q x := by
  cases c <;> [exact he; exact ht]
private theorem evalAuthHybridSendKosk_validAuthCpaState (sendStage : AuthHybridStage)
    (S : Setup) (P : Primitives) (secb : Bool) (sid : SessionId S) (hSend : IsSendSessionId S sid)
    (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) (hV : ValidAuthCpaState S P secb hst) :
    ∀ x ∈ support (evalAuthHybridSendKosk sendStage true S P sid u bundle m0 m1
      hst.toAuthHybridState),
      ValidAuthCpaState S P secb { hst with toAuthHybridState := x.2 } := by
  unfold evalAuthHybridSendKosk; dsimp only
  refine forall_mem_support_ite_cpa _ _ _ _ (fun x hx => by simp at hx; subst hx; exact hV) ?_
  cases hFresh : hst.toAuthHybridState.base.usedSendSessions.contains sid
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases hFind : hst.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == u.val) with
    | none => intro x hx; simp at hx; subst hx; exact hV
    | some up =>
      rcases up with ⟨uIdx, uEntry⟩; dsimp only
      have huMem := List.mem_of_find?_eq_some hFind
      refine forall_mem_support_ite_cpa _ _ _ _ (fun x hx => by simp at hx; subst hx; exact hV) ?_
      refine forall_mem_support_ite_cpa _ _ _ _ (fun x hx => by simp at hx; subst hx; exact hV) ?_
      intro x hx; simp only [MonadAttach.mem_support_bind] at hx
      rcases hx with ⟨ekASk, _, kemCoins, _, ephASk, _, spqrCoins, _, hx⟩; revert x hx
      refine forall_mem_support_ite_cpa _ _ _ _ (fun x hx => by simp at hx; subst hx; exact hV) ?_
      cases P.kemEncaps bundle.pqspkB kemCoins with
      | none => intro x hx; simp at hx; subst hx; exact hV
      | some sc =>
        rcases sc with ⟨ss, kemCt⟩; dsimp only; intro x hx
        simp only [MonadAttach.mem_support_bind] at hx
        rcases hx with ⟨⟨drKey, roCache', ⟨rk1, ck1_0⟩, rootRoCache', ⟨mkSeed, ck1_1⟩⟩, _, hx⟩
        revert x hx
        cases P.spqrInitSend drKey.pqrKey spqrCoins with
        | none => intro x hx; simp at hx; subst hx; exact hV
        | some pqr =>
          rcases pqr with ⟨_pqrStA, spqrSalt?, pqRatchetMsg⟩; dsimp only; intro x hx
          simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
          rcases hx with ⟨deriveMessageKeys, _, rfl⟩
          exact validAuthCpaState_finishAuthHybridSend P secb sid hSend uIdx uEntry _ _
            bundle m0 m1 ekASk _ ss kemCt ephASk _ drKey rk1 ck1_0 mkSeed ck1_1
            spqrSalt? pqRatchetMsg deriveMessageKeys _ _ _ roCache' rootRoCache' hst hV hFresh huMem
  · simp only [↓reduceIte]; intro x hx; simp at hx; subst hx; exact hV
private theorem pqxdhAuthHybridSplitFixedImpl_validAuthCpaState1Key (sendStage : AuthHybridStage)
    (S : Setup) (P : Primitives) (secb : Bool) (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (hV : ValidAuthCpaState S P secb hst) :
    ∀ x ∈ support ((pqxdhAuthHybridSplitFixedImpl1Key sendStage .g5 true false S P q).run hst),
      ValidAuthCpaState S P secb x.2 := by
  have hStage : (AuthHybridStage.g5).idealMsgKeys = true := rfl
  cases q with
  | sendOPK u i bundle m0 m1 =>
    unfold pqxdhAuthHybridSplitFixedImpl1Key pqxdhAuthHybridKoskImpl1Key
    simp only [hStage, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
      isAuthRecvQuery, StateT.run_bind, StateT.run_get, StateT.run_monadLift,
      monadLift_self, StateT.run_set, StateT.run_pure, pure_bind, bind_assoc]
    cases bundle.opkB?.isNone
    · simp only [Bool.false_eq_true, ↓reduceIte]; rw [runAuthHybridSendKosk_eq]; intro x hx
      simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
      rcases hx with ⟨y, hy, rfl⟩
      have h := evalAuthHybridSendKosk_validAuthCpaState sendStage S P secb (.sendOPK u i) trivial
        u bundle m0 m1 hst hV y hy
      exact ⟨h.validEc, h.sess_le, h.ideal_le, h.validKem, h.ideal_ik_mem, h.secb_eq⟩
    · simp only [↓reduceIte, StateT.run_pure, pure_bind]; intro x hx; simp at hx; subst hx
      exact ⟨hV.validEc, hV.sess_le, hV.ideal_le, hV.validKem, hV.ideal_ik_mem, hV.secb_eq⟩
  | sendNoOPK u i bundle m0 m1 =>
    unfold pqxdhAuthHybridSplitFixedImpl1Key pqxdhAuthHybridKoskImpl1Key
    simp only [hStage, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
      isAuthRecvQuery, StateT.run_bind, StateT.run_get, StateT.run_monadLift,
      monadLift_self, StateT.run_set, StateT.run_pure, pure_bind, bind_assoc]
    cases bundle.opkB?.isSome
    · simp only [Bool.false_eq_true, ↓reduceIte]; rw [runAuthHybridSendKosk_eq]; intro x hx
      simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
      rcases hx with ⟨y, hy, rfl⟩
      have h := evalAuthHybridSendKosk_validAuthCpaState sendStage S P secb (.sendNoOPK u i) trivial
        u bundle m0 m1 hst hV y hy
      exact ⟨h.validEc, h.sess_le, h.ideal_le, h.validKem, h.ideal_ik_mem, h.secb_eq⟩
    · simp only [↓reduceIte, StateT.run_pure, pure_bind]; intro x hx; simp at hx; subst hx
      exact ⟨hV.validEc, hV.sess_le, hV.ideal_le, hV.validKem, hV.ideal_ik_mem, hV.secb_eq⟩
  | recvOPK k j o msg =>
    rcases hV with ⟨⟨hVP, hVS, hVO, hVSess⟩, hSessLe, hIdealLe, hVKem, hIkMem, hSecb⟩
    have hV' : ValidAuthCpaState S P secb { hst with recvCount := hst.recvCount + 1 } :=
      ⟨⟨hVP, hVS, hVO, hVSess⟩, hSessLe, hIdealLe, hVKem, hIkMem, hSecb⟩
    unfold pqxdhAuthHybridSplitFixedImpl1Key pqxdhAuthHybridFixedImpl1Key
    simp only [hStage, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
      StateT.run_bind, StateT.run_get, pure_bind]
    refine forall_mem_support_run_ite_cpa _ _ _ hst _ (fun x hx => by
      simp [StateT.run_set] at hx; subst hx; exact hV') ?_
    refine forall_mem_support_run_ite_cpa _ _ _ hst _ (fun x hx => by
      simp [StateT.run_set] at hx; subst hx; exact hV') ?_
    refine forall_mem_support_run_ite_cpa _ _ _ hst _ (fun x hx => by
      simp [StateT.run_set] at hx; subst hx; exact hV') ?_
    cases hst.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == k.val) with
    | none =>
      intro x hx; simp [StateT.run_set] at hx; subst hx; exact hV'
    | some kp =>
      rcases kp with ⟨_, kEntry⟩; dsimp only
      cases hst.toAuthHybridState.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
      | none =>
        intro x hx; simp [StateT.run_set] at hx; subst hx; exact hV'
      | some bp =>
        rcases bp with ⟨_, bEntry⟩; dsimp only
        cases hst.toAuthHybridState.base.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val,
          o.val)) with
        | none =>
          intro x hx; simp [StateT.run_set] at hx; subst hx; exact hV'
        | some op =>
          rcases op with ⟨_, oEntry⟩; dsimp only
          refine forall_mem_support_run_ite_cpa _ _ _ hst _ (fun x hx => by
            simp [StateT.run_set] at hx; subst hx; exact hV') ?_
          refine forall_mem_support_run_ite_cpa _ _ _ hst _ (fun x hx => by
            simp [StateT.run_set] at hx; subst hx; exact hV') ?_
          cases hDec : P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
          | none =>
            intro x hx; simp [StateT.run_set] at hx; subst hx; exact hV'
          | some ss =>
            dsimp only; have hVKem' : ValidRecvKemRecords P
                ({ k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk, pqspkSk := bEntry.pqspkSk,
                   kemCt := msg.hdr.kemCt, kemSs := ss } :: hst.toAuthHybridState.recvKemRecs) := by
              intro r hr
              rcases List.mem_cons.mp hr with rfl | hr' <;> [exact hDec; exact hVKem r hr']
            have hVO' := validOpkEntries_map_consumed_cpa S (k.val, j.val, o.val)
              hst.toAuthHybridState.base.opkEntries hVO
            intro x hx
            simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
              MonadAttach.mem_support_bind] at hx
            rcases hx with ⟨⟨⟨res?, mkSaltCache'⟩, _⟩, _, hx⟩
            cases res? with
            | none =>
              simp [StateT.run_set] at hx; subst hx
              exact ⟨⟨hVP, hVS, hVO, hVSess⟩, hSessLe, hIdealLe, hVKem', hIkMem, hSecb⟩
            | some r =>
              rcases r with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩; revert hx
              cases findHonestPrincipal P hst.toAuthHybridState.base.principals msg.hdr.ikAPk with
              | none =>
                intro hx; simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
                  support_pure, Set.mem_singleton_iff] at hx; subst hx
                exact ⟨⟨hVP, hVS, hVO', hVSess⟩, hSessLe, hIdealLe, hVKem', hIkMem, hSecb⟩
              | some sp =>
                rcases sp with ⟨_, senderEntry⟩
                cases hCorr : senderEntry.corrupted <;> {
                  intro hx; simp only [hCorr, Bool.not_true, Bool.not_false, Bool.false_eq_true,
                    ↓reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
                      support_pure, Set.mem_singleton_iff] at hx; subst hx
                  exact ⟨⟨hVP, hVS, hVO', hVSess⟩, hSessLe, hIdealLe, hVKem', hIkMem, hSecb⟩
                }
  | recvNoOPK k j l msg =>
    rcases hV with ⟨⟨hVP, hVS, hVO, hVSess⟩, hSessLe, hIdealLe, hVKem, hIkMem, hSecb⟩
    have hV' : ValidAuthCpaState S P secb { hst with recvCount := hst.recvCount + 1 } :=
      ⟨⟨hVP, hVS, hVO, hVSess⟩, hSessLe, hIdealLe, hVKem, hIkMem, hSecb⟩
    unfold pqxdhAuthHybridSplitFixedImpl1Key pqxdhAuthHybridFixedImpl1Key
    simp only [hStage, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
      StateT.run_bind, StateT.run_get, pure_bind]
    refine forall_mem_support_run_ite_cpa _ _ _ hst _ (fun x hx => by
      simp [StateT.run_set] at hx; subst hx; exact hV') ?_
    refine forall_mem_support_run_ite_cpa _ _ _ hst _ (fun x hx => by
      simp [StateT.run_set] at hx; subst hx; exact hV') ?_
    refine forall_mem_support_run_ite_cpa _ _ _ hst _ (fun x hx => by
      simp [StateT.run_set] at hx; subst hx; exact hV') ?_
    cases hst.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == k.val) with
    | none =>
      intro x hx; simp [StateT.run_set] at hx; subst hx; exact hV'
    | some kp =>
      rcases kp with ⟨_, kEntry⟩; dsimp only
      cases hst.toAuthHybridState.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
      | none =>
        intro x hx; simp [StateT.run_set] at hx; subst hx; exact hV'
      | some bp =>
        rcases bp with ⟨_, bEntry⟩; dsimp only
        refine forall_mem_support_run_ite_cpa _ _ _ hst _ (fun x hx => by
          simp [StateT.run_set] at hx; subst hx; exact hV') ?_
        cases hDec : P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
        | none =>
          intro x hx; simp [StateT.run_set] at hx; subst hx; exact hV'
        | some ss =>
          dsimp only; have hVKem' : ValidRecvKemRecords P
              ({ k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk, pqspkSk := bEntry.pqspkSk,
                 kemCt := msg.hdr.kemCt, kemSs := ss } :: hst.toAuthHybridState.recvKemRecs) := by
            intro r hr
            rcases List.mem_cons.mp hr with rfl | hr' <;> [exact hDec; exact hVKem r hr']
          intro x hx
          simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
            MonadAttach.mem_support_bind] at hx
          rcases hx with ⟨⟨⟨res?, mkSaltCache'⟩, _⟩, _, hx⟩
          cases res? with
          | none =>
            simp [StateT.run_set] at hx; subst hx
            exact ⟨⟨hVP, hVS, hVO, hVSess⟩, hSessLe, hIdealLe, hVKem', hIkMem, hSecb⟩
          | some r =>
            rcases r with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩; revert hx
            cases findHonestPrincipal P hst.toAuthHybridState.base.principals msg.hdr.ikAPk with
            | none =>
              intro hx; simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
                support_pure, Set.mem_singleton_iff] at hx; subst hx
              exact ⟨⟨hVP, hVS, hVO, hVSess⟩, hSessLe, hIdealLe, hVKem', hIkMem, hSecb⟩
            | some sp =>
              rcases sp with ⟨_, senderEntry⟩
              cases hCorr : senderEntry.corrupted <;> {
                intro hx; simp only [hCorr, Bool.not_true, Bool.not_false, Bool.false_eq_true,
                  ↓reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
                    support_pure, Set.mem_singleton_iff] at hx; subst hx
                exact ⟨⟨hVP, hVS, hVO, hVSess⟩, hSessLe, hIdealLe, hVKem', hIkMem, hSecb⟩
              }
  | initPrin u =>
    rcases hV with ⟨⟨hVP, hVS, hVO, hVSess⟩, hSessLe, hIdealLe, hVKem, hIkMem, hSecb⟩
    unfold pqxdhAuthHybridSplitFixedImpl1Key pqxdhAuthHybridKoskImpl1Key liftAuthBase pqxdhAuthImpl1KeyG
    simp only [hStage, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
      isAuthRecvQuery, StateT.run_bind, StateT.run_get, StateT.run_monadLift,
      monadLift_self, StateT.run_set, StateT.run_pure, pure_bind, bind_assoc]
    cases hFresh : hst.toAuthHybridState.base.principals.any (fun (idx, _) => idx == u.val)
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind]
      intro x hx
      simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
      rcases hx with ⟨secIKA0, _, rfl⟩
      refine ⟨⟨(validPrincipals_cons S u _ hst.toAuthHybridState.base.principals hVP hFresh).1,
        hVS, hVO, hVSess⟩, hSessLe, hIdealLe, hVKem, ?_, hSecb⟩
      intro s hs
      rcases hIkMem s hs with ⟨u0, e0, hMem0, hEq0⟩
      exact ⟨u0, e0, List.mem_cons_of_mem _ hMem0, hEq0⟩
    · simp only [↓reduceIte, StateT.run_pure, pure_bind]
      intro x hx; simp at hx; subst hx
      exact ⟨⟨hVP, hVS, hVO, hVSess⟩, hSessLe, hIdealLe, hVKem, hIkMem, hSecb⟩
  | corruptIK u =>
    rcases hV with ⟨⟨hVP, hVS, hVO, hVSess⟩, hSessLe, hIdealLe, hVKem, hIkMem, hSecb⟩
    unfold pqxdhAuthHybridSplitFixedImpl1Key pqxdhAuthHybridKoskImpl1Key liftAuthBase pqxdhAuthImpl1KeyG
    simp only [hStage, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
      isAuthRecvQuery, StateT.run_bind, StateT.run_get, StateT.run_monadLift,
      monadLift_self, StateT.run_set, StateT.run_pure, pure_bind, bind_assoc]
    cases hst.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == u.val) with
    | none =>
      intro x hx; simp at hx; subst hx
      exact ⟨⟨hVP, hVS, hVO, hVSess⟩, hSessLe, hIdealLe, hVKem, hIkMem, hSecb⟩
    | some p =>
      rcases p with ⟨_, entry⟩
      dsimp only; simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
      have h_corr :=
        validPrincipals_map_corrupted S P u.val hst.toAuthHybridState.base.principals hVP
      intro x hx
      simp only [support_pure, Set.mem_singleton_iff] at hx
      subst hx
      refine ⟨⟨h_corr.1, hVS, hVO, hVSess⟩, hSessLe, hIdealLe, hVKem, ?_, hSecb⟩
      intro s hs
      rcases hIkMem s hs with ⟨u0, e0, hMem0, hEq0⟩
      refine ⟨u0, if u0 == u.val then { e0 with corrupted := true } else e0, ?_, ?_⟩
      · have hMap := List.mem_map_of_mem
          (f := fun (idx, e) => if idx == u.val then (idx, { e with corrupted := true }) else (idx,
            e))
          hMem0
        dsimp only at hMap
        split_ifs at hMap ⊢ <;> exact hMap
      · split_ifs <;> exact hEq0
  | genSPK u j =>
    rcases hV with ⟨⟨hVP, hVS, hVO, hVSess⟩, hSessLe, hIdealLe, hVKem, hIkMem, hSecb⟩
    unfold pqxdhAuthHybridSplitFixedImpl1Key pqxdhAuthHybridKoskImpl1Key liftAuthBase pqxdhAuthImpl1KeyG
    simp only [hStage, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
      isAuthRecvQuery, StateT.run_bind, StateT.run_get, StateT.run_monadLift,
      monadLift_self, StateT.run_set, StateT.run_pure, pure_bind, bind_assoc]
    cases hFresh : hst.toAuthHybridState.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases hst.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none =>
        intro x hx; simp at hx; subst hx
        exact ⟨⟨hVP, hVS, hVO, hVSess⟩, hSessLe, hIdealLe, hVKem, hIkMem, hSecb⟩
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
          hVO, hVSess⟩, hSessLe, hIdealLe, hVKem, hIkMem, hSecb⟩
    · simp only [↓reduceIte, StateT.run_pure, pure_bind]
      intro x hx; simp at hx; subst hx
      exact ⟨⟨hVP, hVS, hVO, hVSess⟩, hSessLe, hIdealLe, hVKem, hIkMem, hSecb⟩
  | genOPK u j o =>
    rcases hV with ⟨⟨hVP, hVS, hVO, hVSess⟩, hSessLe, hIdealLe, hVKem, hIkMem, hSecb⟩
    unfold pqxdhAuthHybridSplitFixedImpl1Key pqxdhAuthHybridKoskImpl1Key liftAuthBase pqxdhAuthImpl1KeyG
    simp only [hStage, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
      isAuthRecvQuery, StateT.run_bind, StateT.run_get, StateT.run_monadLift,
      monadLift_self, StateT.run_set, StateT.run_pure, pure_bind, bind_assoc]
    cases hFresh : hst.toAuthHybridState.base.opkEntries.any (fun (k, _) => k == (u.val, j.val,
      o.val))
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind]
      intro x hx
      simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
      rcases hx with ⟨opkSk, _, rfl⟩
      exact ⟨⟨hVP, hVS,
        (validOpkEntries_cons S u j o _ hst.toAuthHybridState.base.opkEntries hVO hFresh).1,
        hVSess⟩, hSessLe, hIdealLe, hVKem, hIkMem, hSecb⟩
    · simp only [↓reduceIte, StateT.run_pure, pure_bind]
      intro x hx; simp at hx; subst hx
      exact ⟨⟨hVP, hVS, hVO, hVSess⟩, hSessLe, hIdealLe, hVKem, hIkMem, hSecb⟩
  | registerKey sk =>
    unfold pqxdhAuthHybridSplitFixedImpl1Key pqxdhAuthHybridKoskImpl1Key liftAuthBase pqxdhAuthImpl1KeyG
      registerAdvKey
    simp only [hStage, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
      isAuthRecvQuery, StateT.run_bind, StateT.run_get, StateT.run_monadLift,
      monadLift_self, StateT.run_set, StateT.run_pure, pure_bind, bind_assoc]
    cases (sk.length != 32) <;> {
      intro x hx; simp [StateT.run_set, StateT.run_pure] at hx; subst hx
      exact ⟨hV.validEc, hV.sess_le, hV.ideal_le, hV.validKem, hV.ideal_ik_mem, hV.secb_eq⟩
    }
  | roQuery secrets =>
    unfold pqxdhAuthHybridSplitFixedImpl1Key pqxdhAuthHybridKoskImpl1Key liftAuthBase pqxdhAuthImpl1KeyG
    simp only [hStage, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
      isAuthRecvQuery, StateT.run_bind, StateT.run_get, StateT.run_monadLift,
      monadLift_self, StateT.run_set, StateT.run_pure, pure_bind, bind_assoc]
    intro x hx
    simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
    rcases hx with ⟨⟨dk, roCache'⟩, _, rfl⟩
    exact ⟨hV.validEc, hV.sess_le, hV.ideal_le, hV.validKem, hV.ideal_ik_mem, hV.secb_eq⟩
  | roRootQuery rk dh =>
    unfold pqxdhAuthHybridSplitFixedImpl1Key pqxdhAuthHybridKoskImpl1Key liftAuthBase pqxdhAuthImpl1KeyG
    simp only [hStage, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
      isAuthRecvQuery, StateT.run_bind, StateT.run_get, StateT.run_monadLift,
      monadLift_self, StateT.run_set, StateT.run_pure, pure_bind, bind_assoc]
    intro x hx
    simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
    rcases hx with ⟨⟨out, rootRoCache'⟩, _, rfl⟩
    exact ⟨hV.validEc, hV.sess_le, hV.ideal_le, hV.validKem, hV.ideal_ik_mem, hV.secb_eq⟩
  | revealDhSecrets =>
    unfold pqxdhAuthHybridSplitFixedImpl1Key pqxdhAuthHybridKoskImpl1Key liftAuthBase pqxdhAuthImpl1KeyG
    simp only [hStage, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
      isAuthRecvQuery, StateT.run_bind, StateT.run_get, StateT.run_monadLift,
      monadLift_self, StateT.run_set, StateT.run_pure, pure_bind]
    intro x hx; simp at hx; subst hx
    exact ⟨hV.validEc, hV.sess_le, hV.ideal_le, hV.validKem, hV.ideal_ik_mem, hV.secb_eq⟩

@[simp] private theorem eraseAuthCpa_principals {S :
    Setup} (P : Primitives) (hst : AuthHybridState S) : (eraseAuthCpa P hst).base.principals =
      hst.base.principals := rfl
@[simp] private theorem eraseAuthCpa_spkBundles {S :
    Setup} (P : Primitives) (hst : AuthHybridState S) : (eraseAuthCpa P hst).base.spkBundles =
      hst.base.spkBundles := rfl
@[simp] private theorem eraseAuthCpa_opkEntries {S :
    Setup} (P : Primitives) (hst : AuthHybridState S) : (eraseAuthCpa P hst).base.opkEntries =
      hst.base.opkEntries := rfl
@[simp] private theorem eraseAuthCpa_sessions {S :
    Setup} (P : Primitives) (hst : AuthHybridState S) : (eraseAuthCpa P hst).base.sessions =
      hst.base.sessions := rfl
@[simp] private theorem eraseAuthCpa_usedSendSessions {S :
    Setup} (P : Primitives) (hst : AuthHybridState S) : (eraseAuthCpa P hst).base.usedSendSessions =
      hst.base.usedSendSessions := rfl
@[simp] private theorem eraseAuthCpa_usedRecvOPK {S :
    Setup} (P : Primitives) (hst : AuthHybridState S) : (eraseAuthCpa P hst).base.usedRecvOPK =
      hst.base.usedRecvOPK := rfl
@[simp] private theorem eraseAuthCpa_usedRecvNoOPK {S :
    Setup} (P : Primitives) (hst : AuthHybridState S) : (eraseAuthCpa P hst).base.usedRecvNoOPK =
      hst.base.usedRecvNoOPK := rfl
@[simp] private theorem eraseAuthCpa_usedKyberTriples {S :
    Setup} (P : Primitives) (hst : AuthHybridState S) : (eraseAuthCpa P hst).base.seenKyberBaseKeys =
      hst.base.seenKyberBaseKeys := rfl
@[simp] private theorem eraseAuthCpa_roCache {S :
    Setup} (P : Primitives) (hst : AuthHybridState S) : (eraseAuthCpa P hst).base.roCache =
      hst.base.roCache := rfl
@[simp] private theorem eraseAuthCpa_rootRoCache {S :
    Setup} (P : Primitives) (hst : AuthHybridState S) : (eraseAuthCpa P hst).base.rootRoCache =
      hst.base.rootRoCache := rfl
@[simp] private theorem eraseAuthCpa_advKeys {S :
    Setup} (P : Primitives) (hst : AuthHybridState S) : (eraseAuthCpa P hst).base.advKeys =
      hst.base.advKeys.map (fun (_, pk) => (P.pow8 pk, pk)) := rfl
@[simp] private theorem eraseAuthCpa_secb {S :
    Setup} (P : Primitives) (hst : AuthHybridState S) : (eraseAuthCpa P hst).base.secb = true := rfl
@[simp] private theorem eraseAuthCpa_initKemRecs {S :
    Setup} (P : Primitives) (hst : AuthHybridState S) : (eraseAuthCpa P hst).initKemRecs =
      hst.initKemRecs := rfl
@[simp] private theorem eraseAuthCpa_recvKemRecs {S :
    Setup} (P : Primitives) (hst : AuthHybridState S) : (eraseAuthCpa P hst).recvKemRecs =
      hst.recvKemRecs := rfl
@[simp] private theorem eraseAuthCpa_idealSessions {S :
    Setup} (P : Primitives) (hst : AuthHybridState S) : (eraseAuthCpa P hst).idealSessions =
      hst.idealSessions.map eraseIdealSessionAead := rfl
@[simp] private theorem eraseAuthCpaFixed_toAuthHybridState {S :
    Setup} (P : Primitives) (hst : AuthHybridStateFixed S) : (eraseAuthCpaFixed P
      hst).toAuthHybridState = eraseAuthCpa P hst.toAuthHybridState := rfl
@[simp] private theorem eraseAuthCpaFixed_recvCount {S :
    Setup} (P : Primitives) (hst : AuthHybridStateFixed S) : (eraseAuthCpaFixed P hst).recvCount =
      hst.recvCount := rfl
@[simp] private theorem eraseAuthCpaFixed_mkSaltCache {S :
    Setup} (P : Primitives) (hst : AuthHybridStateFixed S) : (eraseAuthCpaFixed P hst).mkSaltCache =
      hst.mkSaltCache := rfl
private theorem simulateQ_stepAuthOtherPrim_eraseAuthCpaFixed1Key
    (sendStage : AuthHybridStage) (S : Setup) (P : Primitives) (q : AuthQuery S)
    (hst : AuthHybridStateFixed S) (hNotSend : ¬isAuthSendQuery (Sum.inr q))
    (hNotRecv : ¬isAuthRecvQuery (Sum.inr q)) :
    simulateQ (primBaseImpl P) (stepAuthOtherPrim1Key true S q (eraseAuthCpaFixed P hst)) =
      Prod.map id (eraseAuthCpaFixed P) <$>
        ((pqxdhAuthHybridSplitFixedImpl1Key sendStage .g5 true false S P q).run hst) := by
  have hStage : (AuthHybridStage.g5).idealMsgKeys = true := rfl
  unfold stepAuthOtherPrim1Key pqxdhAuthHybridSplitFixedImpl1Key pqxdhAuthHybridKoskImpl1Key
    liftAuthBase pqxdhAuthImpl1KeyG registerAdvKey eraseAuthCpaFixed eraseAuthCpa
    eraseAuthEvents cacheAuthAdvKeys
  cases q with
  | sendOPK _ _ _ _ _ => exact False.elim (hNotSend trivial)
  | sendNoOPK _ _ _ _ _ => exact False.elim (hNotSend trivial)
  | recvOPK _ _ _ _ => exact False.elim (hNotRecv trivial)
  | recvNoOPK _ _ _ _ => exact False.elim (hNotRecv trivial)
  | initPrin u =>
    simp only [hStage, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
      isAuthRecvQuery, StateT.run_bind, StateT.run_get, StateT.run_monadLift,
      monadLift_self, StateT.run_set, StateT.run_pure, pure_bind, bind_assoc]
    cases hst.toAuthHybridState.base.principals.any (fun (idx, _) => idx == u.val)
    · simp only [Bool.false_eq_true, ↓reduceIte, simulateQ_bind, simulateQ_embedUnif,
        simulateQ_pure, pure_bind, bind_assoc, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, map_bind, map_pure, Prod.map]; rfl
    · simp [StateT.run_pure, Prod.map]
  | corruptIK u =>
    simp only [hStage, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
      isAuthRecvQuery, StateT.run_bind, StateT.run_get, StateT.run_monadLift,
      monadLift_self, StateT.run_set, StateT.run_pure, pure_bind, bind_assoc]
    cases hst.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == u.val) <;>
      simp [StateT.run_set, StateT.run_pure, Prod.map]
  | genSPK u j =>
    simp only [hStage, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
      isAuthRecvQuery, StateT.run_bind, StateT.run_get, StateT.run_monadLift,
      monadLift_self, StateT.run_set, StateT.run_pure, pure_bind, bind_assoc]
    cases hst.toAuthHybridState.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases hst.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none => simp [StateT.run_pure, Prod.map]
      | some p =>
        rcases p with ⟨_, uEntry⟩; dsimp only
        simp only [simulateQ_bind, simulateQ_embedUnif, simulateQ_sampleKemKeyGenPrim,
          simulateQ_pure, pure_bind, bind_assoc, StateT.run_bind, StateT.run_monadLift,
          monadLift_self, StateT.run_set, StateT.run_pure, map_bind, map_pure, Prod.map]; rfl
    · simp [StateT.run_pure, Prod.map]
  | genOPK u j o =>
    simp only [hStage, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
      isAuthRecvQuery, StateT.run_bind, StateT.run_get, StateT.run_monadLift,
      monadLift_self, StateT.run_set, StateT.run_pure, pure_bind, bind_assoc]
    cases hst.toAuthHybridState.base.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val))
    · simp only [Bool.false_eq_true, ↓reduceIte, simulateQ_bind, simulateQ_embedUnif,
        simulateQ_pure, pure_bind, bind_assoc, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, map_bind, map_pure, Prod.map]; rfl
    · simp [StateT.run_pure, Prod.map]
  | registerKey sk =>
    simp only [hStage, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
      isAuthRecvQuery, StateT.run_bind, StateT.run_get, StateT.run_monadLift,
      monadLift_self, StateT.run_set, StateT.run_pure, pure_bind, bind_assoc]
    cases (sk.length != 32)
    · simp only [Bool.false_eq_true, ↓reduceIte, simulateQ_bind,
        simulateQ_pure, pure_bind, StateT.run_bind, StateT.run_set,
        StateT.run_pure, map_pure, Prod.map]; rfl
    · simp only [↓reduceIte, simulateQ_pure, StateT.run_pure, pure_bind, map_pure, Prod.map, id_eq]
  | roQuery secrets =>
    simp only [hStage, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
      isAuthRecvQuery,
      simulateQ_bind, simulateQ_evalHkdfOrRoPrim, simulateQ_pure,
      StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      StateT.run_set, StateT.run_pure, pure_bind, bind_assoc, map_bind, map_pure, Prod.map]; rfl
  | roRootQuery rk dh =>
    simp only [hStage, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
      isAuthRecvQuery,
      simulateQ_bind, simulateQ_embedUnif, evalRootKdfOrRo_true_eq_pure, simulateQ_pure,
      StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      StateT.run_set, StateT.run_pure, pure_bind, bind_assoc, map_bind, map_pure, Prod.map]; rfl
  | revealDhSecrets =>
    simp only [hStage, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
      isAuthRecvQuery,
      StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      StateT.run_set, StateT.run_pure, pure_bind, simulateQ_pure, map_pure, Prod.map];
        rfl
private theorem finishAuthCpaSendFixedPure_eq_eraseAuthCpaFixed {S : Setup} (P : Primitives)
    (sid : SessionId S) (uEntry : PrincipalEntry) (peerPrincipal? : Option (Nat × PrincipalEntry))
    (isFreshPeer : Bool) (bundle : PreKeyBundleInput) (m0 m1 ekASk ekAPk ss kemCt ephASk ephAPk :
      Bytes)
    (drKey : DRKey) (rk1 ck1_0 mkSeed ck1_1 : Bytes) (spqrSalt? : Option Bytes) (pqRatchetMsg :
      Bytes)
    (deriveMessageKeys : MessageKeys) (ad aeadCt msgPlain : Bytes) (roCache' : List (Bytes × DRKey))
    (rootRoCache' : List ((Bytes × Bytes) × (Bytes × Bytes))) (hst : AuthHybridStateFixed S) :
    let prov := checkBundleProvenanceExact P hst.toAuthHybridState.base.principals
      hst.toAuthHybridState.base.spkBundles hst.toAuthHybridState.base.opkEntries bundle
    let isIdealSend := isFreshPeer || (peerPrincipal?.isSome &&
      checkBundleSpkHonIdeal P hst.toAuthHybridState.base.principals
        hst.toAuthHybridState.base.spkBundles bundle && prov.2.2)
    let p : AuthCpaPausePayload S := {
      sid := sid, uEntry := uEntry, peerPrin? := peerPrincipal?, bundle := bundle,
      m0 := m0, m1 := m1, ekASk := ekASk, ekAPk := ekAPk, ss := ss, kemCt := kemCt,
      ephASk := ephASk, ephAPk := ephAPk, drKey := drKey, rk1 := rk1, ck1_0 := ck1_0,
      mkSeed := mkSeed, ck1_1 := ck1_1, spqrSalt? := spqrSalt?, pqRatchetMsg := pqRatchetMsg,
      deriveMessageKeys := (default : MessageKeys), ad := ad, msgPlain := msgPlain,
      spkHon := prov.1, opkHon := prov.2.1, pqspkHon := prov.2.2,
      roCache := roCache', rootRoCache := rootRoCache'
    }
    finishAuthCpaSendFixedPure isFreshPeer isIdealSend p aeadCt (eraseAuthCpaFixed P hst) =
      let (resp, hst') := finishAuthHybridSend P sid uEntry peerPrincipal? isFreshPeer bundle m0 m1
        ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 ck1_0 mkSeed ck1_1
        spqrSalt? pqRatchetMsg deriveMessageKeys ad aeadCt msgPlain roCache' rootRoCache'
          hst.toAuthHybridState
      (resp, eraseAuthCpaFixed P { hst with toAuthHybridState := hst' }) := by
  unfold finishAuthCpaSendFixedPure finishAuthHybridSend eraseAuthCpaFixed eraseAuthCpa
    eraseAuthEvents cacheAuthAdvKeys eraseIdealSessionAead
  dsimp only
  rcases checkBundleProvenanceExact P hst.toAuthHybridState.base.principals
    hst.toAuthHybridState.base.spkBundles hst.toAuthHybridState.base.opkEntries bundle with
    ⟨spkHon, opkHon, pqspkHon⟩
  cases isFreshPeer <;> cases peerPrincipal? <;> cases bundle.opkB? <;>
    cases checkBundleSpkHonIdeal P hst.toAuthHybridState.base.principals
      hst.toAuthHybridState.base.spkBundles bundle <;>
    cases pqspkHon <;> rfl
private def isFreshPeerOpt (peer? : Option (Nat × PrincipalEntry)) : Bool :=
  match peer? with | some (_, pEntry) => !pEntry.corrupted | none => false
private theorem freshPeer_not_eq
    {G : Option (Nat × PrincipalEntry) → (Nat → PrincipalEntry → Bool) → (Unit → Bool) → Bool} (o)
    (hS : ∀ i p, G (some (i, p)) (fun _ e => !e.corrupted) (fun () => false) = !p.corrupted)
    (hN : G none (fun _ e => !e.corrupted) (fun () => false) = false) :
    (!G o (fun _ e => !e.corrupted) (fun () => false)) = !isFreshPeerOpt o := by
  rcases o with _ | ⟨i, p⟩ <;> [rw [hN]; rw [hS]] <;> rfl
private theorem freshPeer_or_eq
    {G : Option (Nat × PrincipalEntry) → (Nat → PrincipalEntry → Bool) → (Unit → Bool) → Bool}
    {b : Bool} (o : Option (Nat × PrincipalEntry))
    (hS : ∀ i p, G (some (i, p)) (fun _ e => !e.corrupted) (fun () => false) = !p.corrupted)
    (hN : G none (fun _ e => !e.corrupted) (fun () => false) = false) :
    (G o (fun _ e => !e.corrupted) (fun () => false) || b) = (isFreshPeerOpt o || b) := by
  rcases o with _ | ⟨i, p⟩ <;> [rw [hN]; rw [hS]] <;> rfl
private theorem freshPeer_ite_eq {α : Type}
    {G : Option (Nat × PrincipalEntry) → (Nat → PrincipalEntry → Bool) → (Unit → Bool) → Bool}
    {x y : α} (o : Option (Nat × PrincipalEntry))
    (hS : ∀ i p, G (some (i, p)) (fun _ e => !e.corrupted) (fun () => false) = !p.corrupted)
    (hN : G none (fun _ e => !e.corrupted) (fun () => false) = false) :
    (if G o (fun _ e => !e.corrupted) (fun () => false) = true then x else y) =
      (if isFreshPeerOpt o = true then x else y) := by
  rcases o with _ | ⟨i, p⟩ <;> [rw [hN]; rw [hS]] <;> rfl
private theorem finishAuthHybridSend_freshPeer_eq {S : Setup}
    {G : Option (Nat × PrincipalEntry) → (Nat → PrincipalEntry → Bool) → (Unit → Bool) → Bool}
    (P : Primitives) (sid : SessionId S) (uEntry : PrincipalEntry) (o)
    (hS : ∀ i p, G (some (i, p)) (fun _ e => !e.corrupted) (fun () => false) = !p.corrupted)
    (hN : G none (fun _ e => !e.corrupted) (fun () => false) = false) :
    finishAuthHybridSend P sid uEntry o (G o (fun _ e => !e.corrupted) (fun () => false)) =
      finishAuthHybridSend P sid uEntry o (isFreshPeerOpt o) := by
  rcases o with _ | ⟨i, p⟩ <;> [rw [hN]; rw [hS]] <;> rfl
private def canonPeerOpt (b : Bool) : Option (Nat × PrincipalEntry) :=
  if b then some (0, ⟨[], [], [], [], false⟩) else none
private theorem reduce_peerOpt {P : Option (Nat × PrincipalEntry) → Prop}
    (hEq : ∀ i a b c d (corr : Bool), P (some (i, ⟨a, b, c, d, corr⟩)) = P (canonPeerOpt (!corr)))
    (h : ∀ s : Bool, P (canonPeerOpt s)) : ∀ o, P o := by
  intro o; rcases o with _ | ⟨i, a, b, c, d, corr⟩; · exact h false
  rw [hEq]; exact h (!corr)
private theorem sigVerify_resolve_eq
    {G : Option (Nat × PrincipalEntry) → (Nat → PrincipalEntry → Bytes) → (Unit → Bytes) → Bytes}
    (P : Primitives) (principals : List (Nat × PrincipalEntry)) (ikB msg sig : Bytes)
    (hS : ∀ i p, G (some (i, p)) (fun _ e => e.ikSignPk) (fun () => ikB) = p.ikSignPk)
    (hN : G none (fun _ e => e.ikSignPk) (fun () => ikB) = ikB) :
    P.sigVerify (G (findHonestPrincipal P principals ikB) (fun _ e => e.ikSignPk) (fun () => ikB))
      msg sig = P.sigVerify (resolveSigPk P principals ikB) msg sig := by
  unfold resolveSigPk; rcases findHonestPrincipal P principals ikB with _ | _ <;> [rw [hN]; rw [hS]]
private def prepAuthCpaSendFixedPure (S : Setup) (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) :
    ProbComp (Option (Bool × Bool × AuthCpaPausePayload S)) := do
  let st := hst.toAuthHybridState.base
  let some (_, uEntry) := st.principals.find? (fun (i, _) => i == u.val)
    | return none
  let peerPrincipal? := findHonestPrincipal P st.principals bundle.ikB
  let isFreshPeer : Bool := isFreshPeerOpt peerPrincipal?
  if !isFreshPeer && m0 != m1 then
    return none
  if !koskBundleOk P st.principals st.spkBundles st.opkEntries st.advKeys bundle then
    return none
  let ekASk ← sampleScalar32; let kemCoins ← sampleCoins32
  let ephASk ← sampleScalar32; let spqrCoins ← sampleCoins32
  let sigPkB := resolveSigPk P st.principals bundle.ikB
  if !(P.sigVerify sigPkB (encodeEC bundle.spkB) bundle.spkSig &&
       P.sigVerify sigPkB (encodeKEM bundle.pqspkB) bundle.pqspkSig) then
    return none
  let some (ss, kemCt) := P.kemEncaps bundle.pqspkB kemCoins
    | return none
  let ekAPk := P.x25519Base ekASk
  let prov := checkBundleProvenanceExact P st.principals st.spkBundles st.opkEntries bundle
  let spkHonIdeal := checkBundleSpkHonIdeal P st.principals st.spkBundles bundle
  let isIdealSend : Bool := isFreshPeer || (peerPrincipal?.isSome && spkHonIdeal && prov.2.2)
  let dh1 := P.x25519 uEntry.secIKA0 bundle.spkB; let dh2 := P.x25519 ekASk bundle.ikB
  let dh3 := P.x25519 ekASk bundle.spkB
  let dh4? := bundle.opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk)
  let secrets := buildSecrets dh1 dh2 dh3 dh4? ss
  let ephAPk := P.x25519Base ephASk; let dhRatchet := P.x25519 ephASk bundle.spkB
  let (drKey, roCache') ← (
    if isIdealSend then do let dk ← sampleDRKey96; pure (dk, st.roCache)
    else evalHkdfRoPure st.roCache secrets)
  let ((rk1, ck1_0), rootRoCache') ← (
    if isIdealSend then do
      let r ← sampleBytes32; let c ← sampleBytes32; pure ((r, c), st.rootRoCache)
    else
      evalRootKdfRoPure st.rootRoCache drKey.rootKey dhRatchet)
  let (mkSeed, ck1_1) ← (
    if isIdealSend then do let ms ← sampleBytes32; let cn ← sampleBytes32; pure (ms, cn)
    else
      pure (P.chainKdfSeed ck1_0, P.chainKdfNext ck1_0))
  let some (_pqrStA, spqrSalt?, pqRatchetMsg) := P.spqrInitSend drKey.pqrKey spqrCoins
    | return none
  let ad := firstMsgAD uEntry.ikAPk bundle.ikB ephAPk pqRatchetMsg
  let payload : AuthCpaPausePayload S := {
    sid := sid, uEntry := uEntry, peerPrin? := peerPrincipal?, bundle := bundle,
    m0 := m0, m1 := m1, ekASk := ekASk, ekAPk := ekAPk, ss := ss, kemCt := kemCt,
    ephASk := ephASk, ephAPk := ephAPk, drKey := drKey, rk1 := rk1, ck1_0 := ck1_0,
    mkSeed := mkSeed, ck1_1 := ck1_1, spqrSalt? := spqrSalt?, pqRatchetMsg := pqRatchetMsg,
    deriveMessageKeys := (default : MessageKeys), ad := ad, msgPlain := m0,
    spkHon := prov.1, opkHon := prov.2.1, pqspkHon := prov.2.2,
    roCache := roCache', rootRoCache := rootRoCache'
  }
  return some (isFreshPeer, isIdealSend, payload)
private theorem opkMap_x25519_eq (P : Primitives) (ekASk : Bytes)
    (opkB? : Option (KeyId × Bytes)) :
    opkB?.map (fun _ => P.x25519 ekASk (opkB?.map Prod.snd |>.getD [])) =
      opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk) := by
  cases opkB? <;> rfl
private theorem simulateQ_prepAuthCpaSendFixedPrim (S : Setup) (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) (hPrin : hst.toAuthHybridState.base.principals.length ≤ S.N_dh)
    (hSpk : hst.toAuthHybridState.base.spkBundles.length ≤ S.N_dh)
    (hOpk : hst.toAuthHybridState.base.opkEntries.length ≤ S.N_dh) :
    simulateQ (primBaseImpl P)
      (prepAuthCpaSendFixedPrim S sid u bundle m0 m1 (eraseAuthCpaFixed P hst)) =
    prepAuthCpaSendFixedPure S P sid u bundle m0 m1 hst := by
  have hAdv : ValidAdvKeysPow8 P (eraseAuthCpaFixed P hst).toAuthHybridState.base.advKeys :=
    validAdvKeysPow8_eraseAuthCpa P hst.toAuthHybridState
  unfold prepAuthCpaSendFixedPrim prepAuthCpaSendFixedPure
  dsimp only [eraseAuthCpaFixed_toAuthHybridState, eraseAuthCpa_principals,
    eraseAuthCpa_spkBundles, eraseAuthCpa_opkEntries, eraseAuthCpa_roCache,
    eraseAuthCpa_rootRoCache]
  cases hst.toAuthHybridState.base.principals.find? (fun (i, _) => i == u.val) with
  | none => simp only [simulateQ_pure]
  | some up =>
    rcases up with ⟨_, uEntry⟩; dsimp only; rw [simulateQ_bind,
        simulateQ_findHonestPrincipalPrim S P hst.toAuthHybridState.base.principals bundle.ikB
          hPrin,
        pure_bind]
    rw [freshPeer_not_eq (findHonestPrincipal P hst.toAuthHybridState.base.principals bundle.ikB)]
    all_goals try (intros; rfl)
    by_cases hFreshCond : (!isFreshPeerOpt (findHonestPrincipal P
      hst.toAuthHybridState.base.principals bundle.ikB) && (m0 != m1)) = true
    · simp only [hFreshCond, ↓reduceIte, simulateQ_pure]
    · have hFreshCondF := Bool.eq_false_iff.mpr hFreshCond
      simp only [hFreshCondF, Bool.false_eq_true, ↓reduceIte]
      rw [simulateQ_bind,
          simulateQ_koskBundleOkPrim S P hst.toAuthHybridState.base.principals
            hst.toAuthHybridState.base.spkBundles hst.toAuthHybridState.base.opkEntries
            (eraseAuthCpa P hst.toAuthHybridState).base.advKeys bundle hPrin hSpk hOpk hAdv,
          pure_bind, eraseAuthCpa_advKeys,
          koskBundleOk_map_cache P hst.toAuthHybridState.base.principals
            hst.toAuthHybridState.base.spkBundles hst.toAuthHybridState.base.opkEntries
            hst.toAuthHybridState.base.advKeys bundle]
      by_cases hKosk : (!koskBundleOk P hst.toAuthHybridState.base.principals
          hst.toAuthHybridState.base.spkBundles hst.toAuthHybridState.base.opkEntries
          hst.toAuthHybridState.base.advKeys bundle) = true
      · simp only [hKosk, ↓reduceIte, simulateQ_pure]
      · have hKoskF := Bool.eq_false_iff.mpr hKosk; simp only [hKoskF, Bool.false_eq_true,
          ↓reduceIte]
        rw [simulateQ_bind, simulateQ_embedUnif]; congr 1; funext ekASk
        rw [simulateQ_bind, simulateQ_embedUnif]; congr 1; funext kemCoins
        rw [simulateQ_bind, simulateQ_embedUnif]; congr 1; funext ephASk
        rw [simulateQ_bind, simulateQ_embedUnif]; congr 1; funext spqrCoins
        rw [simulateQ_bind, simulateQ_primQ_sigVerify, pure_bind,
            simulateQ_bind, simulateQ_primQ_sigVerify, pure_bind]
        rw [sigVerify_resolve_eq P hst.toAuthHybridState.base.principals bundle.ikB
              (encodeEC bundle.spkB) bundle.spkSig,
            sigVerify_resolve_eq P hst.toAuthHybridState.base.principals bundle.ikB
              (encodeKEM bundle.pqspkB) bundle.pqspkSig]
        all_goals try (intros; rfl)
        by_cases hSig : (!(P.sigVerify (resolveSigPk P hst.toAuthHybridState.base.principals
          bundle.ikB)
            (encodeEC bundle.spkB) bundle.spkSig &&
          P.sigVerify (resolveSigPk P hst.toAuthHybridState.base.principals bundle.ikB)
            (encodeKEM bundle.pqspkB) bundle.pqspkSig)) = true
        · simp only [hSig, ↓reduceIte, simulateQ_pure]
        · have hSigF := Bool.eq_false_iff.mpr hSig; simp only [hSigF, Bool.false_eq_true,
            ↓reduceIte]
          rw [simulateQ_bind, simulateQ_primQ_kemEncaps, pure_bind]
          cases P.kemEncaps bundle.pqspkB kemCoins with
          | none => simp only [simulateQ_pure]
          | some sc =>
            rcases sc with ⟨ss, kemCt⟩; dsimp only
            rw [simulateQ_bind, simulateQ_primQ_x25519Base, pure_bind,
                simulateQ_bind,
                simulateQ_checkBundleProvenanceExactPrim S P
                  hst.toAuthHybridState.base.principals hst.toAuthHybridState.base.spkBundles
                  hst.toAuthHybridState.base.opkEntries bundle hPrin hOpk,
                pure_bind,
                simulateQ_bind,
                simulateQ_checkBundleSpkHonIdealFromPeerPrim S P
                  hst.toAuthHybridState.base.principals hst.toAuthHybridState.base.spkBundles
                  bundle hSpk,
                pure_bind,
                simulateQ_bind, simulateQ_primQ_x25519, pure_bind,
                simulateQ_bind, simulateQ_primQ_x25519, pure_bind,
                simulateQ_bind, simulateQ_primQ_x25519, pure_bind,
                simulateQ_bind, simulateQ_primQ_x25519, pure_bind,
                simulateQ_bind, simulateQ_primQ_x25519Base, pure_bind,
                simulateQ_bind, simulateQ_primQ_x25519, pure_bind,
                opkMap_x25519_eq,
                freshPeer_or_eq
                  (findHonestPrincipal P hst.toAuthHybridState.base.principals bundle.ikB)]
            all_goals try (intros; rfl)
            generalize (isFreshPeerOpt (findHonestPrincipal P hst.toAuthHybridState.base.principals
              bundle.ikB) ||
              ((findHonestPrincipal P hst.toAuthHybridState.base.principals bundle.ikB).isSome &&
                checkBundleSpkHonIdeal P hst.toAuthHybridState.base.principals
                  hst.toAuthHybridState.base.spkBundles bundle &&
                (checkBundleProvenanceExact P hst.toAuthHybridState.base.principals
                  hst.toAuthHybridState.base.spkBundles hst.toAuthHybridState.base.opkEntries
                    bundle).2.2)) = isIdealSend
            cases isIdealSend
            · simp only [Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
              rw [simulateQ_bind, simulateQ_embedUnif]; congr 1; funext ⟨drKey, roCache'⟩
              rw [simulateQ_bind, simulateQ_embedUnif]; congr 1; funext ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
              dsimp only; rw [simulateQ_bind, simulateQ_primQ_chainKdfSeed, pure_bind,
                  simulateQ_bind, simulateQ_primQ_chainKdfNext, pure_bind,
                  simulateQ_bind, simulateQ_primQ_spqrInitSend, pure_bind]
              cases P.spqrInitSend drKey.pqrKey spqrCoins with
              | none => simp only [simulateQ_pure]
              | some _ =>
                simp only [simulateQ_pure]; rcases findHonestPrincipal P
                  hst.toAuthHybridState.base.principals bundle.ikB with _ | ⟨_, _⟩ <;> rfl
            · simp only [↓reduceIte, bind_assoc, pure_bind]
              rw [simulateQ_bind, simulateQ_embedUnif]; congr 1; funext dk
              rw [simulateQ_bind, simulateQ_embedUnif]; congr 1; funext r
              rw [simulateQ_bind, simulateQ_embedUnif]; congr 1; funext c
              rw [simulateQ_bind, simulateQ_embedUnif]; congr 1; funext ms
              rw [simulateQ_bind, simulateQ_embedUnif]; congr 1; funext cn
              rw [simulateQ_bind, simulateQ_primQ_spqrInitSend, pure_bind]
              cases P.spqrInitSend dk.pqrKey spqrCoins with
              | none => simp only [simulateQ_pure]
              | some _ =>
                simp only [simulateQ_pure]; rcases findHonestPrincipal P
                  hst.toAuthHybridState.base.principals bundle.ikB with _ | ⟨_, _⟩ <;> rfl
private theorem simulateQ_runAuthSendCpaCutoffPrim_eq
    (sendStage : AuthHybridStage) (cut : Nat) (S : Setup) (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S)
    (hDr : sendStage.idealDrKey = true) (hRk : sendStage.idealRk = true)
    (hCk : sendStage.idealCk = true) (hMk : sendStage.idealMsgKeys = true)
    (hCut : decide (initSessionSlotIdx sid < cut) =
      (sendStage.idealFreshAead || !hst.toAuthHybridState.base.secb))
    (hPrin : hst.toAuthHybridState.base.principals.length ≤ S.N_dh)
    (hSpk : hst.toAuthHybridState.base.spkBundles.length ≤ S.N_dh)
    (hOpk : hst.toAuthHybridState.base.opkEntries.length ≤ S.N_dh) :
    simulateQ (primBaseImpl P)
      (runAuthSendCpaCutoffPrim cut S sid u bundle m0 m1 (eraseAuthCpaFixed P hst)) =
    Prod.map id (eraseAuthCpaFixed P) <$>
      (evalAuthHybridSendKosk sendStage true S P sid u bundle m0 m1 hst.toAuthHybridState >>=
        fun (resp, hst') => pure (resp, { hst with toAuthHybridState := hst' })) := by
  unfold runAuthSendCpaCutoffPrim tryPauseAuthCpaSendFixedPrim evalAuthHybridSendKosk
    evalAuthHybridSendSchedule
  dsimp only [eraseAuthCpaFixed_toAuthHybridState, eraseAuthCpa_usedSendSessions]
  by_cases hLen : (m0.length != m1.length) = true
  · simp only [hLen, ↓reduceIte, pure_bind, simulateQ_pure, map_pure, Prod.map]; rfl
  · have hLenF := Bool.eq_false_iff.mpr hLen
    simp only [hLenF, Bool.false_eq_true, ↓reduceIte]
    by_cases hUsed : hst.toAuthHybridState.base.usedSendSessions.contains sid = true
    · simp only [hUsed, ↓reduceIte, pure_bind, simulateQ_pure, map_pure, Prod.map]; rfl
    · have hUsedF := Bool.eq_false_iff.mpr hUsed
      simp only [hUsedF, Bool.false_eq_true, ↓reduceIte, bind_assoc, simulateQ_bind]
      rw [simulateQ_prepAuthCpaSendFixedPrim S P sid u bundle m0 m1 hst hPrin hSpk hOpk]
      unfold prepAuthCpaSendFixedPure
      dsimp only; cases hst.toAuthHybridState.base.principals.find? (fun (i, _) => i == u.val) with
      | none => simp only [pure_bind, simulateQ_pure, map_pure, Prod.map]; rfl
      | some up =>
        rcases up with ⟨_, uEntry⟩
        dsimp only; rw [freshPeer_not_eq
          (findHonestPrincipal P hst.toAuthHybridState.base.principals bundle.ikB)]
        all_goals try (intros; rfl)
        by_cases hFreshCond : (!isFreshPeerOpt (findHonestPrincipal P
          hst.toAuthHybridState.base.principals bundle.ikB) && (m0 != m1)) = true
        · simp only [hFreshCond, ↓reduceIte, pure_bind, simulateQ_pure, map_pure, Prod.map]; rfl
        · have hFreshCondF := Bool.eq_false_iff.mpr hFreshCond
          simp only [hFreshCondF, Bool.false_eq_true, ↓reduceIte]
          by_cases hKosk : (!koskBundleOk P hst.toAuthHybridState.base.principals
              hst.toAuthHybridState.base.spkBundles hst.toAuthHybridState.base.opkEntries
              hst.toAuthHybridState.base.advKeys bundle) = true
          · simp only [hKosk, ↓reduceIte, pure_bind, simulateQ_pure, map_pure, Prod.map]; rfl
          · have hKoskF := Bool.eq_false_iff.mpr hKosk
            simp only [hKoskF, Bool.false_eq_true, ↓reduceIte, map_bind, bind_assoc, pure_bind]
            congr 1; funext ekASk; congr 1; funext kemCoins
            congr 1; funext ephASk; congr 1; funext spqrCoins
            by_cases hSig : (!(P.sigVerify (resolveSigPk P hst.toAuthHybridState.base.principals
              bundle.ikB)
                (encodeEC bundle.spkB) bundle.spkSig &&
              P.sigVerify (resolveSigPk P hst.toAuthHybridState.base.principals bundle.ikB)
                (encodeKEM bundle.pqspkB) bundle.pqspkSig)) = true
            · simp only [hSig, ↓reduceIte, pure_bind, simulateQ_pure, map_pure, Prod.map]; rfl
            · have hSigF := Bool.eq_false_iff.mpr hSig; simp only [hSigF, Bool.false_eq_true,
                ↓reduceIte]
              cases P.kemEncaps bundle.pqspkB kemCoins with
              | none => simp only [pure_bind, simulateQ_pure, map_pure, Prod.map]; rfl
              | some sc =>
                rcases sc with ⟨ss, kemCt⟩; dsimp only
                simp only [hDr, hRk, hCk, hMk, Bool.and_true, evalHkdfOrRo_true_eq_pure,
                  evalRootKdfOrRo_true_eq_pure]
                have hPlainEq :
                    (if decide (initSessionSlotIdx sid < cut) then m0 else m1) =
                      (if sendStage.idealFreshAead then m0
                       else if hst.toAuthHybridState.base.secb then m1 else m0) := by
                  rw [hCut]
                  cases sendStage.idealFreshAead <;> cases hst.toAuthHybridState.base.secb <;> rfl
                rw [freshPeer_or_eq
                      (findHonestPrincipal P hst.toAuthHybridState.base.principals bundle.ikB),
                    finishAuthHybridSend_freshPeer_eq P sid uEntry
                      (findHonestPrincipal P hst.toAuthHybridState.base.principals bundle.ikB)]
                all_goals try (intros; rfl)
                rw [freshPeer_ite_eq
                      (findHonestPrincipal P hst.toAuthHybridState.base.principals bundle.ikB)]
                all_goals try (intros; rfl)
                by_cases hFresh : isFreshPeerOpt (findHonestPrincipal P
                  hst.toAuthHybridState.base.principals bundle.ikB) = true
                · simp only [hFresh, Bool.true_or, ↓reduceIte, Bool.false_and, Bool.false_eq_true,
                    bind_assoc, pure_bind, hPlainEq]
                  congr 1; funext dk; congr 1; funext r; congr 1; funext c
                  congr 1; funext ms; congr 1; funext cn
                  cases P.spqrInitSend dk.pqrKey spqrCoins with
                  | none => simp only [pure_bind, simulateQ_pure, map_pure, Prod.map]; rfl
                  | some pqr =>
                    rcases pqr with ⟨_pqrStA, spqrSalt?, pqRatchetMsg⟩
                    rw [pure_bind]; dsimp only
                    simp only [↓reduceIte, simulateQ_bind, simulateQ_embedUnif,
                      simulateQ_pure, map_pure, bind_assoc, pure_bind]
                    congr 1; funext deriveMessageKeys
                    rw [simulateQ_primQ_aeadEnc, pure_bind, hPlainEq]
                    have hFin := finishAuthCpaSendFixedPure_eq_eraseAuthCpaFixed P sid uEntry
                      (findHonestPrincipal P hst.toAuthHybridState.base.principals bundle.ikB)
                      true bundle m0 m1 ekASk (P.x25519Base ekASk) ss kemCt
                      ephASk (P.x25519Base ephASk) dk r c ms cn
                      spqrSalt? pqRatchetMsg deriveMessageKeys
                      (firstMsgAD uEntry.ikAPk bundle.ikB (P.x25519Base ephASk) pqRatchetMsg)
                      (P.aeadEnc deriveMessageKeys (firstMsgAD uEntry.ikAPk bundle.ikB (P.x25519Base ephASk)
                        pqRatchetMsg)
                        (if sendStage.idealFreshAead then m0 else if hst.toAuthHybridState.base.secb
                          then m1 else m0))
                      (if sendStage.idealFreshAead then m0 else if hst.toAuthHybridState.base.secb
                        then m1 else m0)
                      hst.toAuthHybridState.base.roCache hst.toAuthHybridState.base.rootRoCache hst
                    simp only [Bool.true_or] at hFin; rw [hFin]
                    rcases findHonestPrincipal P hst.toAuthHybridState.base.principals bundle.ikB
                      with _ | ⟨_, _⟩ <;> rfl
                · have hFreshF : isFreshPeerOpt (findHonestPrincipal P
                    hst.toAuthHybridState.base.principals bundle.ikB) = false :=
                    Bool.eq_false_iff.mpr hFresh
                  simp only [hFreshF, Bool.false_or]
                  generalize hIdeal : ((findHonestPrincipal P hst.toAuthHybridState.base.principals
                    bundle.ikB).isSome &&
                    checkBundleSpkHonIdeal P hst.toAuthHybridState.base.principals
                      hst.toAuthHybridState.base.spkBundles bundle &&
                    (checkBundleProvenanceExact P hst.toAuthHybridState.base.principals
                      hst.toAuthHybridState.base.spkBundles hst.toAuthHybridState.base.opkEntries
                        bundle).2.2) = isIdealSend
                  cases isIdealSend
                  · simp only [Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
                    congr 1; funext ⟨drKey, roCache'⟩; congr 1; funext ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
                    cases P.spqrInitSend drKey.pqrKey spqrCoins with
                    | none => simp only [pure_bind, simulateQ_pure, map_pure, Prod.map]; rfl
                    | some pqr =>
                      rcases pqr with ⟨_pqrStA, spqrSalt?, pqRatchetMsg⟩
                      rw [pure_bind]; dsimp only; simp only [Bool.false_eq_true, ↓reduceIte,
                        simulateQ_bind, simulateQ_pure, pure_bind, bind_assoc, map_pure, Prod.map]
                      rw [simulateQ_primQ_deriveMsgKeys, pure_bind,
                          simulateQ_primQ_aeadEnc, pure_bind]
                      have hFin := finishAuthCpaSendFixedPure_eq_eraseAuthCpaFixed P sid uEntry
                        (findHonestPrincipal P hst.toAuthHybridState.base.principals bundle.ikB)
                        false bundle m0 m1 ekASk (P.x25519Base ekASk) ss kemCt
                        ephASk (P.x25519Base ephASk) drKey rk1 ck1_0
                        (P.chainKdfSeed ck1_0) (P.chainKdfNext ck1_0)
                        spqrSalt? pqRatchetMsg (P.deriveMsgKeys (P.chainKdfSeed ck1_0) spqrSalt?)
                        (firstMsgAD uEntry.ikAPk bundle.ikB (P.x25519Base ephASk) pqRatchetMsg)
                        (P.aeadEnc (P.deriveMsgKeys (P.chainKdfSeed ck1_0) spqrSalt?)
                          (firstMsgAD uEntry.ikAPk bundle.ikB (P.x25519Base ephASk) pqRatchetMsg)
                            m0)
                        m0 roCache' rootRoCache' hst
                      simp only [Bool.false_or, hIdeal] at hFin; rw [hFin]
                      rcases findHonestPrincipal P hst.toAuthHybridState.base.principals bundle.ikB
                        with _ | ⟨_, _⟩ <;> rfl
                  · simp only [↓reduceIte, bind_assoc, pure_bind]
                    congr 1; funext dk; congr 1; funext r; congr 1; funext c
                    congr 1; funext ms; congr 1; funext cn
                    cases P.spqrInitSend dk.pqrKey spqrCoins with
                    | none => simp only [pure_bind, simulateQ_pure, map_pure, Prod.map]; rfl
                    | some pqr =>
                      rcases pqr with ⟨_pqrStA, spqrSalt?, pqRatchetMsg⟩
                      rw [pure_bind]; dsimp only; simp only [Bool.false_eq_true, ↓reduceIte,
                        simulateQ_bind, simulateQ_embedUnif,
                        simulateQ_pure, map_pure, bind_assoc, pure_bind]
                      congr 1; funext deriveMessageKeys
                      rw [simulateQ_primQ_aeadEnc, pure_bind]
                      have hFin := finishAuthCpaSendFixedPure_eq_eraseAuthCpaFixed P sid uEntry
                        (findHonestPrincipal P hst.toAuthHybridState.base.principals bundle.ikB)
                        false bundle m0 m1 ekASk (P.x25519Base ekASk) ss kemCt
                        ephASk (P.x25519Base ephASk) dk r c ms cn
                        spqrSalt? pqRatchetMsg deriveMessageKeys
                        (firstMsgAD uEntry.ikAPk bundle.ikB (P.x25519Base ephASk) pqRatchetMsg)
                        (P.aeadEnc deriveMessageKeys (firstMsgAD uEntry.ikAPk bundle.ikB (P.x25519Base ephASk)
                          pqRatchetMsg) m0)
                        m0 hst.toAuthHybridState.base.roCache hst.toAuthHybridState.base.rootRoCache
                          hst
                      simp only [Bool.false_or, hIdeal] at hFin; rw [hFin]
                      rcases findHonestPrincipal P hst.toAuthHybridState.base.principals bundle.ikB
                        with _ | ⟨_, _⟩ <;> rfl
private theorem simulateQ_evalAuthRecvScheduleCpaFixedPrim (S : Setup) (P : Primitives)
    (hstDec : AuthHybridStateFixed S) (kEntry : PrincipalEntry)
    (bEntry : SpkBundleEntry) (opkPk? : Option Bytes) (secrets : Bytes) (msg : PreKeyMsg)
    (hPrin : hstDec.toAuthHybridState.base.principals.length ≤ S.N_dh)
    (hIdeal : hstDec.toAuthHybridState.idealSessions.length ≤ S.N_sess_tot) :
    simulateQ (primBaseImpl P)
      (evalAuthRecvScheduleCpaFixedPrim S hstDec kEntry bEntry opkPk? secrets msg) =
    evalAuthFixedRecvScheduleCached .g5 true P
      hstDec.toAuthHybridState hstDec.recvCount hstDec.mkSaltCache kEntry bEntry opkPk? secrets msg
        := by
  unfold evalAuthRecvScheduleCpaFixedPrim evalAuthFixedRecvScheduleCached; dsimp only
  rw [List.take_of_length_le hIdeal,
      simulateQ_bind,
      simulateQ_findHonestPrincipalPrim S P hstDec.toAuthHybridState.base.principals msg.hdr.ikAPk
        hPrin,
      pure_bind,
      simulateQ_bind,
      simulateQ_findMPrim P
        (matchIdealAuthHandshakePrim kEntry.ikAPk bEntry.spkPk opkPk? bEntry.pqspkPk msg.hdr)
        (matchIdealAuthHandshake P kEntry.ikAPk bEntry.spkPk opkPk? bEntry.pqspkPk msg.hdr)
        (fun s => simulateQ_matchIdealAuthHandshakePrim P kEntry.ikAPk bEntry.spkPk opkPk?
          bEntry.pqspkPk msg.hdr s)
        hstDec.toAuthHybridState.idealSessions,
      pure_bind]
  generalize findHonestPrincipal P hstDec.toAuthHybridState.base.principals msg.hdr.ikAPk = peer?
  revert peer?; refine reduce_peerOpt ?_ (fun isUncorruptedHonestSender => ?_)
  · intro _ _ _ _ _ corr; cases corr <;> rfl
  cases hstDec.toAuthHybridState.idealSessions.find?
      (matchIdealAuthHandshake P kEntry.ikAPk bEntry.spkPk opkPk? bEntry.pqspkPk msg.hdr) with
  | none =>
    dsimp only; cases isUncorruptedHonestSender <;> dsimp only [canonPeerOpt]
    · simp only [Option.isSome, AuthHybridStage.idealDrKey, AuthHybridStage.idealRk,
        AuthHybridStage.idealCk, AuthHybridStage.idealMsgKeys, Bool.false_or, Bool.false_and,
        Bool.false_eq_true, ↓reduceIte, evalHkdfOrRo_true_eq_pure,
        evalRootKdfOrRo_true_eq_pure, pure_bind, bind_assoc]
      rw [simulateQ_bind, simulateQ_embedUnif]; congr 1; funext ⟨drKey, roCache'⟩
      dsimp only; rw [simulateQ_bind, simulateQ_primQ_x25519, pure_bind,
          simulateQ_bind, simulateQ_embedUnif]; congr 1; funext ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
      dsimp only; rw [simulateQ_bind, simulateQ_primQ_chainKdfSeed, pure_bind,
          simulateQ_bind, simulateQ_primQ_chainKdfNext, pure_bind,
          simulateQ_bind, simulateQ_primQ_spqrInitRecv, pure_bind]
      cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
      | none => simp only [simulateQ_pure]
      | some pqr =>
        rcases pqr with ⟨_pqrStB, spqrSalt?⟩; dsimp only
        rw [simulateQ_bind, simulateQ_primQ_deriveMsgKeys, pure_bind,
            simulateQ_bind, simulateQ_primQ_aeadDec, pure_bind]
        cases P.aeadDec (P.deriveMsgKeys (P.chainKdfSeed ck1_0) spqrSalt?)
            (firstMsgAD msg.hdr.ikAPk kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg) msg.aeadCt <;>
          simp only [simulateQ_pure]
    · simp only [Option.isSome, AuthHybridStage.idealDrKey, AuthHybridStage.idealRk,
        AuthHybridStage.idealCk, AuthHybridStage.idealMsgKeys, AuthHybridStage.idealFreshAead,
        AuthHybridStage.idealUnmatchedRecvAead, Bool.false_or, Bool.true_and, Bool.false_and,
        Bool.not_false, Bool.false_eq_true, ↓reduceIte, pure_bind, bind_assoc]
      rw [simulateQ_bind, simulateQ_embedUnif]; congr 1; funext dk
      rw [simulateQ_bind, simulateQ_primQ_x25519, pure_bind,
          simulateQ_bind, simulateQ_embedUnif]; congr 1; funext r
      rw [simulateQ_bind, simulateQ_embedUnif]; congr 1; funext c
      rw [simulateQ_bind, simulateQ_embedUnif]; congr 1; funext ms
      rw [simulateQ_bind, simulateQ_embedUnif]; congr 1; funext cn
      rw [simulateQ_bind, simulateQ_primQ_spqrInitRecv, pure_bind]
      cases P.spqrInitRecv dk.pqrKey msg.pqRatchetMsg with
      | none => simp only [simulateQ_pure]
      | some pqr =>
        rcases pqr with ⟨_pqrStB, spqrSalt?⟩; dsimp only
        rw [simulateQ_bind, simulateQ_embedUnif]; congr 1
  | some s =>
    dsimp only; simp only [Option.isSome, AuthHybridStage.idealDrKey, AuthHybridStage.idealRk,
      AuthHybridStage.idealCk, AuthHybridStage.idealMsgKeys, AuthHybridStage.idealFreshAead,
      AuthHybridStage.idealUnmatchedRecvAead, Bool.true_or, Bool.true_and,
      ↓reduceIte, pure_bind, bind_assoc]
    rw [simulateQ_bind, simulateQ_primQ_x25519, pure_bind,
        simulateQ_bind, simulateQ_primQ_pow8, pure_bind,
        simulateQ_bind, simulateQ_primQ_pow8, pure_bind]
    by_cases hEph : (P.pow8 msg.ephAPk == P.pow8 s.ephAPk) = true
    · simp only [hEph, ↓reduceIte, Bool.true_and, pure_bind]
      rw [simulateQ_bind, simulateQ_primQ_spqrInitRecv, pure_bind]
      cases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
      | none => simp only [simulateQ_pure]
      | some pqr =>
        rcases pqr with ⟨_pqrStB, spqrSalt?⟩; dsimp only
        by_cases hSalt : (sameSaltKey spqrSalt? s.spqrSalt?) = true
        · simp only [hSalt, ↓reduceIte, Bool.true_and, pure_bind]
          split <;> simp only [simulateQ_pure]
        · have hSaltF : (sameSaltKey spqrSalt? s.spqrSalt?) = false := Bool.eq_false_iff.mpr hSalt
          simp only [hSaltF, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_and,
            Bool.false_and]
          cases hstDec.mkSaltCache.find? (fun (k, _) => mkSaltKeyMatch k s.sid spqrSalt?) with
          | some entry =>
            rcases entry with ⟨_, _, mk⟩; dsimp only; simp only [pure_bind]
            cases isUncorruptedHonestSender <;> dsimp only [canonPeerOpt]
            · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
              rw [simulateQ_bind, simulateQ_primQ_aeadDec, pure_bind]
              cases P.aeadDec mk (firstMsgAD msg.hdr.ikAPk kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg)
                msg.aeadCt <;>
                simp only [simulateQ_pure]
            · simp only [Bool.not_false, Bool.true_and, ↓reduceIte, simulateQ_pure]
          | none =>
            dsimp only; simp only [pure_bind, bind_assoc]
            rw [simulateQ_bind, simulateQ_embedUnif]; congr 1; funext mk
            cases isUncorruptedHonestSender <;> dsimp only [canonPeerOpt]
            · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
              rw [simulateQ_bind, simulateQ_primQ_aeadDec, pure_bind]
              cases P.aeadDec mk (firstMsgAD msg.hdr.ikAPk kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg)
                msg.aeadCt <;>
                simp only [simulateQ_pure]
            · simp only [Bool.not_false, Bool.true_and, ↓reduceIte, simulateQ_pure]
    · have hEphF : (P.pow8 msg.ephAPk == P.pow8 s.ephAPk) = false := Bool.eq_false_iff.mpr hEph
      simp only [hEphF, Bool.false_eq_true, ↓reduceIte, Bool.false_and, Bool.not_false,
        Bool.true_and, pure_bind, bind_assoc]
      rw [simulateQ_bind, simulateQ_embedUnif]; congr 1; funext r
      rw [simulateQ_bind, simulateQ_embedUnif]; congr 1; funext c
      rw [simulateQ_bind, simulateQ_embedUnif]; congr 1; funext ms
      rw [simulateQ_bind, simulateQ_embedUnif]; congr 1; funext cn
      rw [simulateQ_bind, simulateQ_primQ_spqrInitRecv, pure_bind]
      cases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
      | none => simp only [simulateQ_pure]
      | some pqr =>
        rcases pqr with ⟨_pqrStB, spqrSalt?⟩; dsimp only
        rw [simulateQ_bind, simulateQ_embedUnif]; congr 1; funext mk
        cases isUncorruptedHonestSender <;> dsimp only [canonPeerOpt]
        · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
          rw [simulateQ_bind, simulateQ_primQ_aeadDec, pure_bind]
          cases P.aeadDec mk (firstMsgAD msg.hdr.ikAPk kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg)
            msg.aeadCt <;>
            simp only [simulateQ_pure]
        · simp only [Bool.not_false, Bool.true_and, ↓reduceIte, simulateQ_pure]
private def clearRecvPt {S : Setup}
    (r : Option (DRKey × Bytes × Bytes × Bytes × List (Bytes × DRKey) × List ((Bytes × Bytes) ×
      (Bytes × Bytes))) ×
      AuthMkSaltCache S) :
    Option (DRKey × Bytes × Bytes × Bytes × List (Bytes × DRKey) × List ((Bytes × Bytes) × (Bytes ×
      Bytes))) ×
      AuthMkSaltCache S :=
  (r.1.map (fun (drKey, rk1, ck1_1, _pt, roCache', rootRoCache') =>
    (drKey, rk1, ck1_1, ([] : Bytes), roCache', rootRoCache')), r.2)
private theorem findHonestPrincipal_isSome_of_matchIdealAuthHandshake {S : Setup} (P : Primitives)
    (principals : List (Nat × PrincipalEntry))
    (kIkPk spkPk : Bytes) (opkPk? : Option Bytes) (pqspkPk : Bytes)
    (hdr : HandshakeHdr) (s : IdealAuthSession S)
    (hMatch : matchIdealAuthHandshake P kIkPk spkPk opkPk? pqspkPk hdr s = true)
    (hIk : ∃ u e, (u, e) ∈ principals ∧ e.ikAPk = s.ikAPk) :
    (findHonestPrincipal P principals hdr.ikAPk).isSome = true := by
  rcases hIk with ⟨u, e, heMem, heIk⟩
  have hPow : (P.pow8 hdr.ikAPk == P.pow8 e.ikAPk) = true := by
    rw [heIk]
    unfold matchIdealAuthHandshake at hMatch; revert hMatch
    cases (P.pow8 hdr.ikAPk == P.pow8 s.ikAPk) <;> simp
  unfold findHonestPrincipal
  cases hFind : principals.find? (fun (_, entry) => P.pow8 hdr.ikAPk == P.pow8 entry.ikAPk) with
  | some _ => rfl
  | none =>
    exact absurd hPow (List.find?_eq_none.mp hFind (u, e) heMem)
private theorem find?_eraseIdealSessionAead {S : Setup} (P : Primitives)
    (kIkPk spkPk : Bytes) (opkPk? : Option Bytes) (pqspkPk : Bytes)
    (hdr : HandshakeHdr) (sessions : List (IdealAuthSession S)) :
    (sessions.map eraseIdealSessionAead).find?
        (matchIdealAuthHandshake P kIkPk spkPk opkPk? pqspkPk hdr) =
      (sessions.find? (matchIdealAuthHandshake P kIkPk spkPk opkPk? pqspkPk hdr)).map
        eraseIdealSessionAead := by
  rw [List.find?_map]; rfl
private theorem evalAuthFixedRecvScheduleCached_eraseAuthCpa_bind {S : Setup} {α : Type}
    (P : Primitives) (hstDec : AuthHybridState S)
    (recvCount : Nat) (mkSaltCache : AuthMkSaltCache S)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry)
    (opkPk? : Option Bytes) (secrets : Bytes) (msg : PreKeyMsg)
    (cont : Option (DRKey × Bytes × Bytes × Bytes × List (Bytes × DRKey) × List ((Bytes × Bytes) ×
      (Bytes × Bytes))) ×
      AuthMkSaltCache S → α)
    (hIkMem : ∀ s ∈ hstDec.idealSessions,
      ∃ u e, (u, e) ∈ hstDec.base.principals ∧ e.ikAPk = s.ikAPk)
    (hCont : (findHonestPrincipal P hstDec.base.principals msg.hdr.ikAPk).isSome = true →
      ∀ r, cont (clearRecvPt r) = cont r) :
    (evalAuthFixedRecvScheduleCached .g5 true P (eraseAuthCpa P hstDec) recvCount mkSaltCache
      kEntry bEntry opkPk? secrets msg >>= fun r => pure (cont r)) =
    (evalAuthFixedRecvScheduleCached .g5 true P hstDec recvCount mkSaltCache
      kEntry bEntry opkPk? secrets msg >>= fun r => pure (cont r)) := by
  unfold evalAuthFixedRecvScheduleCached
  dsimp only [eraseAuthCpa_principals, eraseAuthCpa_roCache,
    eraseAuthCpa_rootRoCache, eraseAuthCpa_idealSessions]
  rw [find?_eraseIdealSessionAead]
  cases hMatch : hstDec.idealSessions.find?
      (matchIdealAuthHandshake P kEntry.ikAPk bEntry.spkPk opkPk? bEntry.pqspkPk msg.hdr) with
  | none => rfl
  | some s =>
    have hsMem : s ∈ hstDec.idealSessions := List.mem_of_find?_eq_some hMatch
    have hsOk : matchIdealAuthHandshake P kEntry.ikAPk bEntry.spkPk opkPk? bEntry.pqspkPk msg.hdr s
      = true :=
      List.find?_some hMatch
    have hHon : (findHonestPrincipal P hstDec.base.principals msg.hdr.ikAPk).isSome = true :=
      findHonestPrincipal_isSome_of_matchIdealAuthHandshake P hstDec.base.principals
        kEntry.ikAPk bEntry.spkPk opkPk? bEntry.pqspkPk msg.hdr s hsOk (hIkMem s hsMem)
    have hContEq : (fun r => pure (cont r) : _ → ProbComp α) =
        (fun r => pure (cont (clearRecvPt r))) := by
      funext r; rw [hCont hHon r]
    dsimp only [Option.map, eraseIdealSessionAead]
    simp only [Option.isSome, Bool.true_or, Bool.true_and,
      AuthHybridStage.idealDrKey, AuthHybridStage.idealRk, AuthHybridStage.idealCk,
      AuthHybridStage.idealMsgKeys, AuthHybridStage.idealFreshAead,
      AuthHybridStage.idealUnmatchedRecvAead, ↓reduceIte, pure_bind]
    by_cases hEph : (P.pow8 msg.ephAPk == P.pow8 s.ephAPk) = true
    · simp only [hEph, ↓reduceIte, Bool.true_and]
      cases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
      | none => rfl
      | some pqr =>
        rcases pqr with ⟨_pqrStB, spqrSalt?⟩; dsimp only
        by_cases hSalt : (sameSaltKey spqrSalt? s.spqrSalt?) = true
        · simp only [hSalt, ↓reduceIte, Bool.true_and]
          rw [hContEq]
          cases (firstMsgAD msg.hdr.ikAPk kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg ==
            s.ad && msg.aeadCt == s.aeadCt) <;> rfl
        · have hSaltF := Bool.eq_false_iff.mpr hSalt
          simp only [hSaltF, Bool.false_eq_true, ↓reduceIte, Bool.false_and]
    · have hEphF := Bool.eq_false_iff.mpr hEph
      simp only [hEphF, Bool.false_eq_true, ↓reduceIte, Bool.false_and]
private theorem simulateQ_stepAuthCpaNonSendPrim_recvOPK_eq1Key
    (sendStage : AuthHybridStage) (S : Setup) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (msg : PreKeyMsg)
    (hst : AuthHybridStateFixed S) (hPrin : hst.toAuthHybridState.base.principals.length ≤ S.N_dh)
    (hIdeal : hst.toAuthHybridState.idealSessions.length ≤ S.N_sess_tot)
    (hIkMem : ∀ s ∈ hst.toAuthHybridState.idealSessions,
      ∃ u e, (u, e) ∈ hst.toAuthHybridState.base.principals ∧ e.ikAPk = s.ikAPk) :
    simulateQ (primBaseImpl P)
      (stepAuthCpaNonSendPrim1Key S (.recvOPK k j o msg) (eraseAuthCpaFixed P hst)) =
    Prod.map id (eraseAuthCpaFixed P) <$>
      ((pqxdhAuthHybridSplitFixedImpl1Key sendStage .g5 true false S P (.recvOPK k j o msg)).run hst) :=
        by
  have hStage : (AuthHybridStage.g5).idealMsgKeys = true := rfl
  have hAdv : ValidAdvKeysPow8 P (eraseAuthCpaFixed P hst).toAuthHybridState.base.advKeys :=
    validAdvKeysPow8_eraseAuthCpa P hst.toAuthHybridState
  unfold stepAuthCpaNonSendPrim1Key pqxdhAuthHybridSplitFixedImpl1Key pqxdhAuthHybridFixedImpl1Key
  dsimp only [eraseAuthCpaFixed_toAuthHybridState, eraseAuthCpa_principals,
    eraseAuthCpa_spkBundles, eraseAuthCpa_opkEntries, eraseAuthCpa_usedRecvOPK,
    eraseAuthCpa_usedKyberTriples, eraseAuthCpaFixed_recvCount, eraseAuthCpaFixed_mkSaltCache]
  simp only [hStage, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
    StateT.run_get, pure_bind]
  by_cases h1 : (!(msg.hdr.spkId == UInt32.ofNat j.val &&
                   msg.hdr.pqspkId == UInt32.ofNat j.val &&
                   msg.hdr.opkId? == some (UInt32.ofNat o.val) &&
                   msg.hdr.ikAPk.length == 32 &&
                   msg.hdr.ekAPk.length == 32 &&
                   msg.ephAPk.length == 32)) = true
  · simp only [h1, ↓reduceIte, simulateQ_pure, StateT.run_bind, StateT.run_set, StateT.run_pure,
      pure_bind, map_pure, Prod.map, eraseAuthCpaFixed, id_eq]
  · have h1F := Bool.eq_false_iff.mpr h1; simp only [h1F, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : (hst.toAuthHybridState.base.usedRecvOPK.contains (k.val, j.val, o.val)) = true
    · simp only [h2, ↓reduceIte, simulateQ_pure, StateT.run_bind, StateT.run_set, StateT.run_pure,
        pure_bind, map_pure, Prod.map, eraseAuthCpaFixed, id_eq]
    · have h2F := Bool.eq_false_iff.mpr h2; simp only [h2F, Bool.false_eq_true, ↓reduceIte]
      rw [simulateQ_bind,
          simulateQ_koskSenderOkPrim S P hst.toAuthHybridState.base.principals
            (eraseAuthCpa P hst.toAuthHybridState).base.advKeys msg.hdr.ikAPk hPrin hAdv,
          pure_bind, eraseAuthCpa_advKeys,
          koskSenderOk_map_cache P hst.toAuthHybridState.base.principals
            hst.toAuthHybridState.base.advKeys msg.hdr.ikAPk]
      by_cases h3 : (!koskSenderOk P hst.toAuthHybridState.base.principals
          hst.toAuthHybridState.base.advKeys msg.hdr.ikAPk) = true
      · simp only [h3, ↓reduceIte, simulateQ_pure, StateT.run_bind, StateT.run_set, StateT.run_pure,
          pure_bind, map_pure, Prod.map, eraseAuthCpaFixed, id_eq]
      · have h3F := Bool.eq_false_iff.mpr h3; simp only [h3F, Bool.false_eq_true, ↓reduceIte]
        cases hst.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == k.val) with
        | none =>
          simp only [simulateQ_pure, StateT.run_bind, StateT.run_set, StateT.run_pure,
            pure_bind, map_pure, Prod.map, eraseAuthCpaFixed, id_eq]
        | some kp =>
          rcases kp with ⟨_, kEntry⟩; dsimp only
          cases hst.toAuthHybridState.base.spkBundles.find? (fun (idx, _) => idx == (k.val,
            j.val)) with
          | none =>
            simp only [simulateQ_pure, StateT.run_bind, StateT.run_set, StateT.run_pure,
              pure_bind, map_pure, Prod.map, eraseAuthCpaFixed, id_eq]
          | some bp =>
            rcases bp with ⟨_, bEntry⟩; dsimp only
            cases hst.toAuthHybridState.base.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val,
              o.val)) with
            | none =>
              simp only [simulateQ_pure, StateT.run_bind, StateT.run_set, StateT.run_pure,
                pure_bind, map_pure, Prod.map, eraseAuthCpaFixed, id_eq]
            | some op =>
              rcases op with ⟨_, oEntry⟩; dsimp only; by_cases h4 : oEntry.consumed = true
              · simp only [h4, ↓reduceIte, simulateQ_pure, StateT.run_bind, StateT.run_set,
                  StateT.run_pure,
                  pure_bind, map_pure, Prod.map, eraseAuthCpaFixed, id_eq]
              · have h4F := Bool.eq_false_iff.mpr h4; simp only [h4F, Bool.false_eq_true,
                  ↓reduceIte]
                rw [simulateQ_bind, simulateQ_primQ_isCanonical, pure_bind,
                    simulateQ_bind, simulateQ_primQ_isCanonical, pure_bind]
                by_cases h5 : (!(checkAndMarkKyberBaseKeySeen hst.toAuthHybridState.base.seenKyberBaseKeys
                  k.val msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk).1 ||
                    !P.isCanonical msg.hdr.ekAPk || !P.isCanonical msg.ephAPk) = true
                · simp only [h5, ↓reduceIte, simulateQ_pure, StateT.run_bind, StateT.run_set,
                    StateT.run_pure,
                    pure_bind, map_pure, Prod.map, eraseAuthCpaFixed, id_eq]
                · have h5F := Bool.eq_false_iff.mpr h5; simp only [h5F, Bool.false_eq_true,
                    ↓reduceIte]
                  rw [simulateQ_bind, simulateQ_primQ_kemDecaps, pure_bind]
                  cases P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
                  | none =>
                    simp only [simulateQ_pure, StateT.run_bind, StateT.run_set, StateT.run_pure,
                      pure_bind, map_pure, Prod.map, eraseAuthCpaFixed, id_eq]
                  | some ss =>
                    dsimp only; rw [simulateQ_bind, simulateQ_primQ_x25519, pure_bind,
                        simulateQ_bind, simulateQ_primQ_x25519, pure_bind,
                        simulateQ_bind, simulateQ_primQ_x25519, pure_bind,
                        simulateQ_bind, simulateQ_primQ_x25519, pure_bind,
                        simulateQ_bind]
                    simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, map_bind]
                    let rRec : RecvKemRecord :=
                      { k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk,
                        pqspkSk := bEntry.pqspkSk, kemCt := msg.hdr.kemCt, kemSs := ss }
                    let hstDec : AuthHybridState S :=
                      { hst.toAuthHybridState with recvKemRecs :=
                        rRec :: hst.toAuthHybridState.recvKemRecs }
                    have hIdealE : (eraseAuthCpa P hstDec).idealSessions.length ≤ S.N_sess_tot := by
                      simpa [eraseAuthCpa, eraseAuthEvents, cacheAuthAdvKeys, hstDec] using hIdeal
                    change (simulateQ (primBaseImpl P)
                      (evalAuthRecvScheduleCpaFixedPrim S
                        { toAuthHybridState := eraseAuthCpa P hstDec,
                          recvCount := hst.recvCount, mkSaltCache := hst.mkSaltCache }
                        kEntry bEntry (some oEntry.opkPk) _ msg) >>= _) = _
                    rw [simulateQ_evalAuthRecvScheduleCpaFixedPrim S P
                      { toAuthHybridState := eraseAuthCpa P hstDec,
                        recvCount := hst.recvCount, mkSaltCache := hst.mkSaltCache }
                      kEntry bEntry (some oEntry.opkPk) _ msg hPrin hIdealE]
                    dsimp only
                    let contPure := fun (resPair : Option (DRKey × Bytes × Bytes × Bytes ×
                      List (Bytes × DRKey) × List ((Bytes × Bytes) × (Bytes × Bytes))) ×
                        AuthMkSaltCache S) =>
                      match resPair.1 with
                      | none =>
                        (AuthResponse.noneResp,
                          ({ toAuthHybridState := eraseAuthCpa P hstDec,
                             recvCount := hst.recvCount + 1,
                             mkSaltCache := resPair.2 } : AuthHybridStateFixed S))
                      | some (drKey, rk1, ck1_1, pt, roCache', rootRoCache') =>
                        let opkEntries' := hst.toAuthHybridState.base.opkEntries.map (fun (idx,
                          (e : OpkEntry)) =>
                          if idx == (k.val, j.val, o.val) then (idx, { e with consumed :=
                            true }) else (idx, e))
                        let resp : AuthResponse :=
                          match findHonestPrincipal P hst.toAuthHybridState.base.principals
                            msg.hdr.ikAPk with
                          | some _ => .recvHonestResp
                          | none   => .recvUnfreshResp drKey rk1 ck1_1 pt
                        let hst' : AuthHybridState S := { (eraseAuthCpa P hstDec) with
                          base := { (eraseAuthCpa P hst.toAuthHybridState).base with
                            opkEntries       := opkEntries'
                            usedRecvOPK      := (k.val, j.val,
                              o.val) :: hst.toAuthHybridState.base.usedRecvOPK
                            seenKyberBaseKeys :=
                              (checkAndMarkKyberBaseKeySeen hst.toAuthHybridState.base.seenKyberBaseKeys
                                k.val msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk).2
                            roCache          := roCache'
                            rootRoCache      := rootRoCache' } }
                        (resp, ({ toAuthHybridState := hst',
                                  recvCount := hst.recvCount + 1,
                                  mkSaltCache := resPair.2 } : AuthHybridStateFixed S))
                    let secrets := buildSecrets (P.x25519 bEntry.spkSk msg.hdr.ikAPk)
                      (P.x25519 kEntry.secIKA0 msg.hdr.ekAPk) (P.x25519 bEntry.spkSk msg.hdr.ekAPk)
                      (some (P.x25519 oEntry.opkSk msg.hdr.ekAPk)) ss
                    trans (evalAuthFixedRecvScheduleCached .g5 true P (eraseAuthCpa P hstDec)
                      hst.recvCount hst.mkSaltCache kEntry bEntry (some oEntry.opkPk) secrets msg
                        >>=
                      fun resPair => pure (contPure resPair))
                    · apply bind_congr; intro ⟨res?, mkSaltCache'⟩
                      cases res? with
                      | none => rfl
                      | some r =>
                        rcases r with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩
                        dsimp only; rw [simulateQ_bind,
                            simulateQ_findHonestPrincipalPrim S P
                              hst.toAuthHybridState.base.principals msg.hdr.ikAPk hPrin,
                            pure_bind]
                        rfl
                    rw [evalAuthFixedRecvScheduleCached_eraseAuthCpa_bind P hstDec
                      hst.recvCount hst.mkSaltCache kEntry bEntry (some oEntry.opkPk) secrets msg
                        contPure hIkMem]
                    · simp only [bind_assoc, pure_bind]
                      apply bind_congr; intro ⟨res?, mkSaltCache'⟩
                      cases res? with
                      | none => rfl
                      | some r =>
                        rcases r with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩
                        dsimp only [contPure]
                        cases findHonestPrincipal P hst.toAuthHybridState.base.principals
                          msg.hdr.ikAPk with
                        | none => rfl
                        | some sp =>
                          rcases sp with ⟨_, senderEntry⟩
                          cases hCorr : senderEntry.corrupted <;>
                            simp [hCorr, StateT.run_set, Prod.map,
                              eraseAuthCpaFixed, eraseAuthCpa, eraseAuthEvents, cacheAuthAdvKeys,
                                hstDec, rRec]
                    · intro hHon ⟨res?, mkSaltCache'⟩
                      cases res? with
                      | none => rfl
                      | some r =>
                        rcases r with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩
                        unfold clearRecvPt
                        dsimp only [Option.map, contPure]
                        cases hfp : findHonestPrincipal P hst.toAuthHybridState.base.principals
                          msg.hdr.ikAPk with
                        | none =>
                          change (findHonestPrincipal P hst.toAuthHybridState.base.principals
                            msg.hdr.ikAPk).isSome = true at hHon
                          rw [hfp] at hHon; cases hHon
                        | some _ => rfl
private theorem simulateQ_stepAuthCpaNonSendPrim_recvNoOPK_eq1Key
    (sendStage : AuthHybridStage) (S : Setup) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg : PreKeyMsg)
    (hst : AuthHybridStateFixed S) (hPrin : hst.toAuthHybridState.base.principals.length ≤ S.N_dh)
    (hIdeal : hst.toAuthHybridState.idealSessions.length ≤ S.N_sess_tot)
    (hIkMem : ∀ s ∈ hst.toAuthHybridState.idealSessions,
      ∃ u e, (u, e) ∈ hst.toAuthHybridState.base.principals ∧ e.ikAPk = s.ikAPk) :
    simulateQ (primBaseImpl P)
      (stepAuthCpaNonSendPrim1Key S (.recvNoOPK k j l msg) (eraseAuthCpaFixed P hst)) =
    Prod.map id (eraseAuthCpaFixed P) <$>
      ((pqxdhAuthHybridSplitFixedImpl1Key sendStage .g5 true false S P (.recvNoOPK k j l msg)).run hst)
        := by
  have hStage : (AuthHybridStage.g5).idealMsgKeys = true := rfl
  have hAdv : ValidAdvKeysPow8 P (eraseAuthCpaFixed P hst).toAuthHybridState.base.advKeys :=
    validAdvKeysPow8_eraseAuthCpa P hst.toAuthHybridState
  unfold stepAuthCpaNonSendPrim1Key pqxdhAuthHybridSplitFixedImpl1Key pqxdhAuthHybridFixedImpl1Key
  dsimp only [eraseAuthCpaFixed_toAuthHybridState, eraseAuthCpa_principals,
    eraseAuthCpa_spkBundles, eraseAuthCpa_usedRecvNoOPK,
    eraseAuthCpa_usedKyberTriples, eraseAuthCpaFixed_recvCount, eraseAuthCpaFixed_mkSaltCache]
  simp only [hStage, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
    StateT.run_get, pure_bind]
  by_cases h1 : (!(msg.hdr.spkId == UInt32.ofNat j.val &&
                   msg.hdr.pqspkId == UInt32.ofNat j.val &&
                   msg.hdr.opkId? == none &&
                   msg.hdr.ikAPk.length == 32 &&
                   msg.hdr.ekAPk.length == 32 &&
                   msg.ephAPk.length == 32)) = true
  · simp only [h1, ↓reduceIte, simulateQ_pure, StateT.run_bind, StateT.run_set, StateT.run_pure,
      pure_bind, map_pure, Prod.map, eraseAuthCpaFixed, id_eq]
  · have h1F := Bool.eq_false_iff.mpr h1; simp only [h1F, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : (hst.toAuthHybridState.base.usedRecvNoOPK.contains (k.val, j.val, l.val)) = true
    · simp only [h2, ↓reduceIte, simulateQ_pure, StateT.run_bind, StateT.run_set, StateT.run_pure,
        pure_bind, map_pure, Prod.map, eraseAuthCpaFixed, id_eq]
    · have h2F := Bool.eq_false_iff.mpr h2; simp only [h2F, Bool.false_eq_true, ↓reduceIte]
      rw [simulateQ_bind,
          simulateQ_koskSenderOkPrim S P hst.toAuthHybridState.base.principals
            (eraseAuthCpa P hst.toAuthHybridState).base.advKeys msg.hdr.ikAPk hPrin hAdv,
          pure_bind, eraseAuthCpa_advKeys,
          koskSenderOk_map_cache P hst.toAuthHybridState.base.principals
            hst.toAuthHybridState.base.advKeys msg.hdr.ikAPk]
      by_cases h3 : (!koskSenderOk P hst.toAuthHybridState.base.principals
          hst.toAuthHybridState.base.advKeys msg.hdr.ikAPk) = true
      · simp only [h3, ↓reduceIte, simulateQ_pure, StateT.run_bind, StateT.run_set, StateT.run_pure,
          pure_bind, map_pure, Prod.map, eraseAuthCpaFixed, id_eq]
      · have h3F := Bool.eq_false_iff.mpr h3; simp only [h3F, Bool.false_eq_true, ↓reduceIte]
        cases hst.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == k.val) with
        | none =>
          simp only [simulateQ_pure, StateT.run_bind, StateT.run_set, StateT.run_pure,
            pure_bind, map_pure, Prod.map, eraseAuthCpaFixed, id_eq]
        | some kp =>
          rcases kp with ⟨_, kEntry⟩; dsimp only
          cases hst.toAuthHybridState.base.spkBundles.find? (fun (idx, _) => idx == (k.val,
            j.val)) with
          | none =>
            simp only [simulateQ_pure, StateT.run_bind, StateT.run_set, StateT.run_pure,
              pure_bind, map_pure, Prod.map, eraseAuthCpaFixed, id_eq]
          | some bp =>
            rcases bp with ⟨_, bEntry⟩; dsimp only
            rw [simulateQ_bind, simulateQ_primQ_isCanonical, pure_bind,
                simulateQ_bind, simulateQ_primQ_isCanonical, pure_bind]
            by_cases h5 : (!(checkAndMarkKyberBaseKeySeen hst.toAuthHybridState.base.seenKyberBaseKeys k.val
              msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk).1 ||
                !P.isCanonical msg.hdr.ekAPk || !P.isCanonical msg.ephAPk) = true
            · simp only [h5, ↓reduceIte, simulateQ_pure, StateT.run_bind, StateT.run_set,
                StateT.run_pure,
                pure_bind, map_pure, Prod.map, eraseAuthCpaFixed, id_eq]
            · have h5F := Bool.eq_false_iff.mpr h5; simp only [h5F, Bool.false_eq_true, ↓reduceIte]
              rw [simulateQ_bind, simulateQ_primQ_kemDecaps, pure_bind]
              cases P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
              | none =>
                simp only [simulateQ_pure, StateT.run_bind, StateT.run_set, StateT.run_pure,
                  pure_bind, map_pure, Prod.map, eraseAuthCpaFixed, id_eq]
              | some ss =>
                dsimp only; rw [simulateQ_bind, simulateQ_primQ_x25519, pure_bind,
                    simulateQ_bind, simulateQ_primQ_x25519, pure_bind,
                    simulateQ_bind, simulateQ_primQ_x25519, pure_bind,
                    simulateQ_bind]
                simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, map_bind]
                let rRec : RecvKemRecord :=
                  { k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk,
                    pqspkSk := bEntry.pqspkSk, kemCt := msg.hdr.kemCt, kemSs := ss }
                let hstDec : AuthHybridState S :=
                  { hst.toAuthHybridState with recvKemRecs :=
                    rRec :: hst.toAuthHybridState.recvKemRecs }
                have hIdealE : (eraseAuthCpa P hstDec).idealSessions.length ≤ S.N_sess_tot := by
                  simpa [eraseAuthCpa, eraseAuthEvents, cacheAuthAdvKeys, hstDec] using hIdeal
                change (simulateQ (primBaseImpl P)
                  (evalAuthRecvScheduleCpaFixedPrim S
                    { toAuthHybridState := eraseAuthCpa P hstDec,
                      recvCount := hst.recvCount, mkSaltCache := hst.mkSaltCache }
                    kEntry bEntry none _ msg) >>= _) = _
                rw [simulateQ_evalAuthRecvScheduleCpaFixedPrim S P
                  { toAuthHybridState := eraseAuthCpa P hstDec,
                    recvCount := hst.recvCount, mkSaltCache := hst.mkSaltCache }
                  kEntry bEntry none _ msg hPrin hIdealE]
                dsimp only
                let contPure := fun (resPair : Option (DRKey × Bytes × Bytes × Bytes × List (Bytes ×
                  DRKey) × List ((Bytes × Bytes) × (Bytes × Bytes))) × AuthMkSaltCache S) =>
                  match resPair.1 with
                  | none =>
                    (AuthResponse.noneResp,
                      ({ toAuthHybridState := eraseAuthCpa P hstDec,
                         recvCount := hst.recvCount + 1,
                         mkSaltCache := resPair.2 } : AuthHybridStateFixed S))
                  | some (drKey, rk1, ck1_1, pt, roCache', rootRoCache') =>
                    let resp : AuthResponse :=
                      match findHonestPrincipal P hst.toAuthHybridState.base.principals
                        msg.hdr.ikAPk with
                      | some _ => .recvHonestResp
                      | none   => .recvUnfreshResp drKey rk1 ck1_1 pt
                    let hst' : AuthHybridState S := { (eraseAuthCpa P hstDec) with
                      base := { (eraseAuthCpa P hst.toAuthHybridState).base with
                        usedRecvNoOPK    := (k.val, j.val,
                          l.val) :: hst.toAuthHybridState.base.usedRecvNoOPK
                        seenKyberBaseKeys :=
                          (checkAndMarkKyberBaseKeySeen hst.toAuthHybridState.base.seenKyberBaseKeys k.val
                            msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk).2
                        roCache          := roCache'
                        rootRoCache      := rootRoCache' } }
                    (resp, ({ toAuthHybridState := hst',
                              recvCount := hst.recvCount + 1,
                              mkSaltCache := resPair.2 } : AuthHybridStateFixed S))
                let secrets := buildSecrets (P.x25519 bEntry.spkSk msg.hdr.ikAPk)
                  (P.x25519 kEntry.secIKA0 msg.hdr.ekAPk) (P.x25519 bEntry.spkSk msg.hdr.ekAPk)
                  none ss
                trans (evalAuthFixedRecvScheduleCached .g5 true P (eraseAuthCpa P hstDec)
                  hst.recvCount hst.mkSaltCache kEntry bEntry none secrets msg >>=
                  fun resPair => pure (contPure resPair))
                · apply bind_congr; intro ⟨res?, mkSaltCache'⟩
                  cases res? with
                  | none => rfl
                  | some r =>
                    rcases r with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩; dsimp only
                    rw [simulateQ_bind,
                        simulateQ_findHonestPrincipalPrim S P hst.toAuthHybridState.base.principals
                          msg.hdr.ikAPk hPrin,
                        pure_bind]
                    rfl
                rw [evalAuthFixedRecvScheduleCached_eraseAuthCpa_bind P hstDec
                  hst.recvCount hst.mkSaltCache kEntry bEntry none secrets msg contPure hIkMem]
                · simp only [bind_assoc, pure_bind]
                  apply bind_congr; intro ⟨res?, mkSaltCache'⟩
                  cases res? with
                  | none => rfl
                  | some r =>
                    rcases r with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩;
                      dsimp only [contPure]
                    cases findHonestPrincipal P hst.toAuthHybridState.base.principals msg.hdr.ikAPk
                      with
                    | none => rfl
                    | some sp =>
                      rcases sp with ⟨_, senderEntry⟩
                      cases hCorr : senderEntry.corrupted <;>
                        simp [hCorr, StateT.run_set, Prod.map,
                          eraseAuthCpaFixed, eraseAuthCpa, eraseAuthEvents, cacheAuthAdvKeys,
                            hstDec, rRec]
                · intro hHon ⟨res?, mkSaltCache'⟩
                  cases res? with
                  | none => rfl
                  | some r =>
                    rcases r with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩
                    unfold clearRecvPt; dsimp only [Option.map, contPure]
                    cases hfp : findHonestPrincipal P hst.toAuthHybridState.base.principals
                      msg.hdr.ikAPk with
                    | none =>
                      change (findHonestPrincipal P hst.toAuthHybridState.base.principals
                        msg.hdr.ikAPk).isSome = true at hHon
                      rw [hfp] at hHon; cases hHon
                    | some _ => rfl
private theorem simulateQ_stepAuthCpaCutoffPrim_eq1Key
    (sendStage : AuthHybridStage) (cut : Nat) (S : Setup) (P : Primitives) (secb : Bool)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (hDr : sendStage.idealDrKey = true) (hRk : sendStage.idealRk = true)
    (hCk : sendStage.idealCk = true) (hMk : sendStage.idealMsgKeys = true)
    (hCut : ∀ sid : SessionId S, initSessionSlotIdx sid < S.N_send_tot →
      decide (initSessionSlotIdx sid < cut) = (sendStage.idealFreshAead || !secb))
    (hV : ValidAuthCpaState S P secb hst) :
    simulateQ (primBaseImpl P) (stepAuthCpaCutoffPrim1Key cut S q (eraseAuthCpaFixed P hst)) =
      Prod.map id (eraseAuthCpaFixed P) <$>
        ((pqxdhAuthHybridSplitFixedImpl1Key sendStage .g5 true false S P q).run hst) := by
  have hStage : (AuthHybridStage.g5).idealMsgKeys = true := rfl
  cases q with
  | sendOPK u i bundle m0 m1 =>
    unfold stepAuthCpaCutoffPrim1Key pqxdhAuthHybridSplitFixedImpl1Key pqxdhAuthHybridKoskImpl1Key
    simp only [hStage, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
      isAuthRecvQuery, StateT.run_bind, StateT.run_get, StateT.run_monadLift,
      monadLift_self, StateT.run_set, StateT.run_pure, pure_bind, bind_assoc]
    cases bundle.opkB?.isNone
    · simp only [Bool.false_eq_true, ↓reduceIte]; rw [runAuthHybridSendKosk_eq]
      have hCutSid : decide (initSessionSlotIdx (.sendOPK u i) < cut) =
          (sendStage.idealFreshAead || !hst.toAuthHybridState.base.secb) := by
        rw [hV.secb_eq]; exact hCut (.sendOPK u i)
          (Nat.lt_of_lt_of_le (initSessionSlotIdx_sendOPK_lt u i) (Nat.le_add_right _ _))
      rw [simulateQ_runAuthSendCpaCutoffPrim_eq sendStage cut S P (.sendOPK u i) u bundle m0 m1
        hst hDr hRk hCk hMk hCutSid hV.principals_le hV.spkBundles_le hV.opkEntries_le]
      simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind, Prod.map,
        eraseAuthCpaFixed, id_eq]
    · simp [StateT.run_pure, Prod.map, eraseAuthCpaFixed]
  | sendNoOPK u i bundle m0 m1 =>
    unfold stepAuthCpaCutoffPrim1Key pqxdhAuthHybridSplitFixedImpl1Key pqxdhAuthHybridKoskImpl1Key
    simp only [hStage, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
      isAuthRecvQuery, StateT.run_bind, StateT.run_get, StateT.run_monadLift,
      monadLift_self, StateT.run_set, StateT.run_pure, pure_bind, bind_assoc]
    cases bundle.opkB?.isSome
    · simp only [Bool.false_eq_true, ↓reduceIte]; rw [runAuthHybridSendKosk_eq]
      have hCutSid : decide (initSessionSlotIdx (.sendNoOPK u i) < cut) =
          (sendStage.idealFreshAead || !hst.toAuthHybridState.base.secb) := by
        rw [hV.secb_eq]; exact hCut (.sendNoOPK u i) (initSessionSlotIdx_sendNoOPK_lt u i)
      rw [simulateQ_runAuthSendCpaCutoffPrim_eq sendStage cut S P (.sendNoOPK u i) u bundle m0 m1
        hst hDr hRk hCk hMk hCutSid hV.principals_le hV.spkBundles_le hV.opkEntries_le]
      simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind, Prod.map,
        eraseAuthCpaFixed, id_eq]
    · simp [StateT.run_pure, Prod.map, eraseAuthCpaFixed]
  | recvOPK k j o msg =>
    unfold stepAuthCpaCutoffPrim1Key
    exact simulateQ_stepAuthCpaNonSendPrim_recvOPK_eq1Key sendStage S P k j o msg hst
      hV.principals_le hV.idealSessions_le_sess_tot hV.ideal_ik_mem
  | recvNoOPK k j l msg =>
    unfold stepAuthCpaCutoffPrim1Key
    exact simulateQ_stepAuthCpaNonSendPrim_recvNoOPK_eq1Key sendStage S P k j l msg hst
      hV.principals_le hV.idealSessions_le_sess_tot hV.ideal_ik_mem
  | initPrin _ | corruptIK _ | genSPK _ _ | genOPK _ _ _
  | registerKey _ | roQuery _ | roRootQuery _ _ | revealDhSecrets =>
    unfold stepAuthCpaCutoffPrim1Key stepAuthCpaNonSendPrim1Key
    exact simulateQ_stepAuthOtherPrim_eraseAuthCpaFixed1Key sendStage S P _ hst
      (by intro h; cases h) (by intro h; cases h)

private theorem simulateQ_runWithPrimStep_cpa {ιI : Type} {GSpec : OracleSpec.{0, 0} ιI}
    {St α : Type} (P : Primitives)
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
    · rw [runWithPrimStep_query_inl, simulateQ_bind, simulateQ_run_query_inl]
      congr 1; funext u; exact ih u st
    · rw [runWithPrimStep_query_inr, simulateQ_bind, simulateQ_run_query_inr]
      congr 1; funext x; exact ih x.1 x.2
private theorem simulateQ_proj_inv_obs_cpa {ι α St1 St2 : Type}
    {QSpec : OracleSpec.{0, 0} ι} (proj : St1 → St2) (Inv : St1 → Prop)
    (impl1 : QueryImpl QSpec (StateT St1 ProbComp)) (impl2 : QueryImpl QSpec (StateT St2 ProbComp))
    (hStep : ∀ (gq : ι) (st : St1), Inv st →
      ((impl2 gq).run (proj st) = Prod.map id proj <$> (impl1 gq).run st) ∧
      (∀ x ∈ support ((impl1 gq).run st), Inv x.2))
    (oa : OracleComp (unifSpec + QSpec) α) (st : St1) (hInv : Inv st)
    (obs1 : α × St1 → ProbComp Bool) (obs2 : α × St2 → ProbComp Bool)
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
    · rw [simulateQ_run_query_inl, simulateQ_run_query_inl,
          bind_assoc, bind_assoc]
      congr 1; funext u; exact ih u st hInv
    · obtain ⟨hStepEq, hStepSupp⟩ := hStep gq st hInv
      rw [simulateQ_run_query_inr, simulateQ_run_query_inr,
          bind_assoc, bind_assoc, hStepEq, bind_map_left]
      refine bind_congr_of_mem_support ((impl1 gq).run st) _ _ (fun x hx => ?_)
      exact ih x.1 x.2 (hStepSupp x hx)
private theorem finalizeAeadCpaGameNoAuthPrim_eraseAuthCpa_eq (S : Setup) (P : Primitives)
    (b' : Bool) (hst : AuthHybridState S) :
    finalizeAeadCpaGameNoAuthPrim S b' (eraseAuthCpa P hst) =
      finalizeAuthGameNoAuthPrim S b' (eraseAuthCpa P hst) := by
  unfold finalizeAeadCpaGameNoAuthPrim finalizeAuthGameNoAuthPrim
  dsimp only [eraseAuthCpa_secb]; cases b' <;> rfl
private theorem authCpaCutoffExp_eq_simulateQ_splitFixed1Key
    (sendStage : AuthHybridStage) (cut : Nat) (S : Setup) (P : Primitives) (secb : Bool)
    (A : AuthAdversary S) (hDr : sendStage.idealDrKey = true) (hRk : sendStage.idealRk = true)
    (hCk : sendStage.idealCk = true) (hMk : sendStage.idealMsgKeys = true)
    (hCut : ∀ sid : SessionId S, initSessionSlotIdx sid < S.N_send_tot →
      decide (initSessionSlotIdx sid < cut) = (sendStage.idealFreshAead || !secb)) :
    authCpaCutoffExp1Key cut S P A =
      (do
        let (b', finalSt) ←
          (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridStateFixed
            S) ProbComp) +
            pqxdhAuthHybridSplitFixedImpl1Key sendStage .g5 true false S P) A.run).run
            (AuthHybridStateFixed.empty S secb)
        finalizeAuthGame (σ :=
          AuthHybridState S) true false S P b' (eraseAuthCpa P finalSt.toAuthHybridState)) := by
  unfold authCpaCutoffExp1Key
  rw [simulateQ_bind, simulateQ_runWithPrimStep_cpa]
  have hInit : eraseAuthCpaFixed P (AuthHybridStateFixed.empty S secb) =
      AuthHybridStateFixed.empty S true := rfl
  rw [← hInit]
  exact simulateQ_proj_inv_obs_cpa (eraseAuthCpaFixed P) (ValidAuthCpaState S P secb)
    (pqxdhAuthHybridSplitFixedImpl1Key sendStage .g5 true false S P) (fun q => StateT.mk (fun hst =>
      simulateQ (primBaseImpl P) (stepAuthCpaCutoffPrim1Key cut S q hst)))
    (fun q hst hV =>
      ⟨simulateQ_stepAuthCpaCutoffPrim_eq1Key sendStage cut S P secb q hst hDr hRk hCk hMk hCut hV,
       pqxdhAuthHybridSplitFixedImpl_validAuthCpaState1Key sendStage S P secb q hst hV⟩)
    A.run (AuthHybridStateFixed.empty S secb) (validAuthCpaState_empty S P secb)
    (fun x => finalizeAuthGame (σ := AuthHybridState S) true false S P x.1
      (eraseAuthCpa P x.2.toAuthHybridState))
    (fun y => simulateQ (primBaseImpl P)
      (finalizeAeadCpaGameNoAuthPrim S y.1 y.2.toAuthHybridState))
    (fun x hVx => by
      have hVE : ValidAuthCpaState S P true (eraseAuthCpaFixed P x.2) := hVx.eraseAuthCpaFixed
      change simulateQ (primBaseImpl P)
          (finalizeAeadCpaGameNoAuthPrim S x.1 (eraseAuthCpa P x.2.toAuthHybridState)) = _
      rw [finalizeAeadCpaGameNoAuthPrim_eraseAuthCpa_eq,
          simulateQ_finalizeAuthGameNoAuthPrim S P x.1 (eraseAuthCpa P x.2.toAuthHybridState)
            hVE.principals_le hVE.spkBundles_le hVE.opkEntries_le hVE.sessions_le hVE.validKem])
private theorem evalDist_finalizeAuthGame_eraseAuthCpa_beq (S : Setup) (P : Primitives)
    (secb b' : Bool) (finalSt : AuthHybridStateFixed S) :
    𝒟[finalizeAuthGame (σ := AuthHybridState S) true false S P b'
        (eraseAuthCpa P finalSt.toAuthHybridState) >>= fun z => pure (secb == z)] =
    𝒟[let allChallengedClean := finalSt.toAuthHybridState.base.sessions.all (fun s =>
        !s.challenged || authInitCorruptionClause P true finalSt.toAuthHybridState.base.principals s)
      if hasEcPkCollisionAuth P finalSt.toAuthHybridState ||
         hasBadSigAuth finalSt.toAuthHybridState ||
         hasKemPkCollisionAuth finalSt.toAuthHybridState ||
         hasBadKemShCrAuth P finalSt.toAuthHybridState then
        $ᵗ Bool
      else if false && finalSt.toAuthHybridState.base.hasWonAuth then
        return true
      else if !allChallengedClean then
        $ᵗ Bool
      else
        return (b' == secb)] := by
  unfold finalizeAuthGame
  have hEc : hasEcPkCollisionAuth P (eraseAuthCpa P finalSt.toAuthHybridState) =
      hasEcPkCollisionAuth P finalSt.toAuthHybridState := rfl
  have hSig : hasBadSigAuth (eraseAuthCpa P finalSt.toAuthHybridState) =
      hasBadSigAuth finalSt.toAuthHybridState := rfl
  have hKem : hasKemPkCollisionAuth (eraseAuthCpa P finalSt.toAuthHybridState) =
      hasKemPkCollisionAuth finalSt.toAuthHybridState := rfl
  have hShCr : hasBadKemShCrAuth P (eraseAuthCpa P finalSt.toAuthHybridState) =
      hasBadKemShCrAuth P finalSt.toAuthHybridState := rfl
  dsimp only [eraseAuthCpa_sessions, eraseAuthCpa_principals, eraseAuthCpa_secb]
  simp only [hEc, hSig, hKem, hShCr, Bool.false_and, Bool.false_eq_true, ↓reduceIte, beq_true]
  generalize (hasEcPkCollisionAuth P finalSt.toAuthHybridState ||
    hasBadSigAuth finalSt.toAuthHybridState ||
    hasKemPkCollisionAuth finalSt.toAuthHybridState ||
    hasBadKemShCrAuth P finalSt.toAuthHybridState) = bad
  generalize (!finalSt.toAuthHybridState.base.sessions.all (fun s =>
    !s.challenged || authInitCorruptionClause P true finalSt.toAuthHybridState.base.principals s)) =
      unclean
  cases bad
  · cases unclean
    · simp [Bool.beq_comm]
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact evalDist_uniformBool_beq_local secb
  · simp only [↓reduceIte]
    exact evalDist_uniformBool_beq_local secb

noncomputable def authCpaCoinCutoffExp1Key (cut : Nat) (S : Setup) (P : Primitives)
    (A : AuthAdversary S) : ProbComp Bool := do
  let secb ← $ᵗ Bool
  let z ← if secb then authCpaCutoffExp1Key cut S P A else authCpaCutoffExp1Key S.N_send_tot S P A
  return (secb == z)

theorem evalDist_authSplitFixedExp_g3_8_g5_false_eq_coinCutoff_zero1Key
    (S : Setup) (P : Primitives) (A : AuthAdversary S) :
    𝒟[authSplitFixedExp1Key .g3_8 .g5 false S P A] = 𝒟[authCpaCoinCutoffExp1Key 0 S P A] := by
  unfold authSplitFixedExp1Key authCpaCoinCutoffExp1Key
  refine OracleComp.evalDist_bind_congr_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  cases secb
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [authCpaCutoffExp_eq_simulateQ_splitFixed1Key .g3_8 S.N_send_tot S P false A rfl rfl rfl rfl
          (fun sid hLt => by simp [AuthHybridStage.idealFreshAead, hLt]),
        bind_assoc]
    refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun ⟨b', finalSt⟩ _ => ?_)
    exact (evalDist_finalizeAuthGame_eraseAuthCpa_beq S P false b' finalSt).symm
  · simp only [↓reduceIte]
    rw [authCpaCutoffExp_eq_simulateQ_splitFixed1Key .g3_8 0 S P true A rfl rfl rfl rfl
          (fun sid _hLt => by simp [AuthHybridStage.idealFreshAead]),
        bind_assoc]
    refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun ⟨b', finalSt⟩ _ => ?_)
    exact (evalDist_finalizeAuthGame_eraseAuthCpa_beq S P true b' finalSt).symm

theorem evalDist_authSplitFixedExp_g3_8_g5_true_eq_coinCutoff_zero1Key
    (S : Setup) (P : Primitives) (hWF : WellFormedPrimitivesδ P) (A : AuthAdversary S) :
    𝒟[authSplitFixedExp1Key .g3_8 .g5 true S P A] = 𝒟[authCpaCoinCutoffExp1Key 0 S P A] := by
  rw [authSplitFixedExp_g5_checkAuth_eq1Key .g3_8 S P hWF A]
  exact evalDist_authSplitFixedExp_g3_8_g5_false_eq_coinCutoff_zero1Key S P A

theorem authSplitFixedExp_g3_8_g5_boolBias_eq1Key
    (S : Setup) (P : Primitives) (hWF : WellFormedPrimitivesδ P)
    (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    (𝒟[authSplitFixedExp1Key .g3_8 .g5 true S P A.1].boolBias).toReal =
      ((min b.q_total S.N_send_tot : Nat) : ℝ) *
        AeadIndCpaReal P (aeadCpaReductionAuthFixed1Key S b A) := by
  rw [evalDist_authSplitFixedExp_g3_8_g5_true_eq_coinCutoff_zero1Key S P hWF A.1]
  unfold authCpaCoinCutoffExp1Key
  rw [evalDist_boolBias_bind_uniformBool, MeasureTheory.Measure.toReal_boolDist,
      abs_sub_authCpaCutoffExp_eq_mul_aeadIndCpa1Key S P b A]

theorem authSplitFixedExp_g3_8_g5_le1Key
    (S : Setup) (P : Primitives) (hWF : WellFormedPrimitivesδ P)
    (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    |(𝒟[authSplitFixedExp1Key .g3_8 .g5 true S P A.1].boolBias).toReal -
     (𝒟[authSplitFixedExp1Key .g5 .g5 true S P A.1].boolBias).toReal| ≤
      2 * (S.N_send_tot : ℝ) * AeadIndCpaReal P (aeadCpaReductionAuthFixed1Key S b A) := by
  rw [authSplitFixedExp_g3_8_g5_boolBias_eq1Key S P hWF b A,
      authSplitFixedExp_g5_g5_true_boolBias_eq_zero1Key S P hWF A.1,
      sub_zero]
  have hNonneg :
      0 ≤ ((min b.q_total S.N_send_tot : Nat) : ℝ) *
        AeadIndCpaReal P (aeadCpaReductionAuthFixed1Key S b A) :=
    mul_nonneg (Nat.cast_nonneg _) (aeadIndCpa_nonneg _ _)
  have hLe :
      ((min b.q_total S.N_send_tot : Nat) : ℝ) *
        AeadIndCpaReal P (aeadCpaReductionAuthFixed1Key S b A) ≤
      (S.N_send_tot : ℝ) * AeadIndCpaReal P (aeadCpaReductionAuthFixed1Key S b A) :=
    mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.min_le_right _ _))
      (aeadIndCpa_nonneg _ _)
  have hAdvNonneg : 0 ≤ AeadIndCpaReal P (aeadCpaReductionAuthFixed1Key S b A) :=
    aeadIndCpa_nonneg _ _
  rw [abs_of_nonneg hNonneg]
  nlinarith

/-- Bounds the `G4` to `G5` (`IND-CPA`) sub-hop over `pqxdhAuthImpl1KeyG` via `aeadCpaReductionAuthFixed1Key`. -/
theorem authHopG4G5_le1Key
    (S : Setup) (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    |(𝒟[authSplitFixedExp1Key .g3_8 .g5 true S P A.1].boolBias).toReal -
     authFixedAdvG5_1Key S P A.1| ≤
      2 * (S.N_send_tot : ℝ) * AeadIndCpaReal P (aeadCpaReductionAuthFixed1Key S b A) := by
  unfold authFixedAdvG5_1Key
  rw [← evalDist_authSplitFixedExp_g5_g5_true_eq_authFixedExpG5_1Key S P hP.toWellFormedPrimitivesδ A.1]
  exact authSplitFixedExp_g3_8_g5_le1Key S P hP.toWellFormedPrimitivesδ b A

theorem authHopG3_8G5_of_int1Key (S : Setup)
    (int : (b : QueryBudget) → BoundedAdv (AuthAdversary S) b → AeadMuIntCtxtAdv)
    (hInt : ∀ (P : Primitives), CryptoWellFormedPrimitivesδ P →
      ∀ (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b),
        |authFixedAdvG3_8_1Key S P A.1 -
         (𝒟[authSplitFixedExp1Key .g3_8 .g5 true S P A.1].boolBias).toReal| ≤
          2 * AeadMuIntCtxt P (int b A)) :
    AuthHopG3_8G5Stmt1Key S (aeadCpaReductionAuthFixed1Key S) int := by
  intro P hP b A; have h1 := hInt P hP b A; have h2 := authHopG4G5_le1Key S P hP b A
  have htri := abs_sub_le
    (authFixedAdvG3_8_1Key S P A.1) ((𝒟[authSplitFixedExp1Key .g3_8 .g5 true S P A.1].boolBias).toReal)
    (authFixedAdvG5_1Key S P A.1)
  linarith

/-- Assembles `AuthSubHops4to5Bundle1Key` from `aeadCpaReductionAuthFixed1Key` and a multi-key INT-CTXT reduction. -/
def authSubHops4to5Bundle_of_int1Key (S : Setup)
    (int : (b : QueryBudget) → BoundedAdv (AuthAdversary S) b → AeadMuIntCtxtAdv)
    (hIntQ : ∀ b A, (int b A).q_dec ≤ S.N_recv_tot)
    (hIntEncQ : ∀ b A, (int b A).q_enc ≤ S.N_send_tot)
    (hIntPrimQ : ∀ b A, (int b A).q_prim ≤ primQueryBudget S b)
    (hIntHop : ∀ (P : Primitives), CryptoWellFormedPrimitivesδ P →
      ∀ (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b),
        |authFixedAdvG3_8_1Key S P A.1 -
         (𝒟[authSplitFixedExp1Key .g3_8 .g5 true S P A.1].boolBias).toReal| ≤
          2 * AeadMuIntCtxt P (int b A)) :
    AuthSubHops4to5Bundle1Key S where
  cpa              := aeadCpaReductionAuthFixed1Key S
  int              := int
  int_queries      := hIntQ
  int_enc_queries  := hIntEncQ
  cpa_prim_queries := aeadCpaReductionAuthFixed_prim_queries1Key S
  int_prim_queries := hIntPrimQ
  hop_G3_8_G5      := authHopG3_8G5_of_int1Key S int hIntHop
end SignalPqxdh.Security
