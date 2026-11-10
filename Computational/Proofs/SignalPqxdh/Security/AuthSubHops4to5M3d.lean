/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5M3c
public import Computational.Proofs.SignalPqxdh.Security.AuthPrfHmacHA2
public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5M2
import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5M1
import Computational.Proofs.SignalPqxdh.Security.FgGapDhC
import VCVio.EvalDist.Monad.Basic

/-!
# Multi-Key `INT-CTXT` Receive Coupling and Final Bound

Proves the receiver key-schedule coupling between `pqxdhAuthForgeAllImpl` and
`aeadMuIntReductionAuth`, connects `runMu` to `aeadMuIntCtxtExp` on first-message ADs, and derives
the multi-key `INT-CTXT` sub-hop bound `auth_hop_G3_8_split_g5_boolBias_le_mu`.
-/

@[expose] public section

set_option autoImplicit false

open OracleSpec OracleComp MeasureTheory ENNReal BigOperators

namespace SignalPqxdh.Security

open SignalPqxdh
open _root_.Proofs.SignalPqxdh.Security
open _root_.Proofs.SignalPqxdh.Security.FgGapDh

theorem chal_beq_eq_false_M3 {ad1 ct1 ad2 ct2 : Bytes}
    (h : (ad2 == ad1 && ct2 == ct1) = false) :
    (some (ad1, ct1) == some (ad2, ct2)) = false := by
  rw [Bool.eq_false_iff] at h ⊢
  intro hEq; apply h
  have hPair : (ad1, ct1) = (ad2, ct2) := Option.some.inj (beq_iff_eq.mp hEq)
  rcases Prod.mk.inj hPair with ⟨rfl, rfl⟩; simp

theorem pt_isFreshSenderM3_eq {S : Setup} (stage : AuthHybridStage) (P : Primitives) (u c : Bool)
    {G : Option (Nat × PrincipalEntry) → (Nat → PrincipalEntry → Bool) → (Unit → Bool) → Bool}
    (o : Option (Nat × PrincipalEntry))
    (hSome : ∀ a b,
      G (some (a, b)) (fun _ sEntry => !sEntry.corrupted) (fun _ => false) = !b.corrupted)
    (hNone : G none (fun _ sEntry => !sEntry.corrupted) (fun _ => false) = false) :
    authRecvPtAtStage (S := S) stage P u c
      (G o (fun _ sEntry => !sEntry.corrupted) (fun _ => false)) =
      authRecvPtAtStage (S := S) stage P u c (isFreshSenderM3 o) := by
  rcases o with _ | ⟨a, b⟩
  · exact congrArg (authRecvPtAtStage (S := S) stage P u c) hNone
  · exact congrArg (authRecvPtAtStage (S := S) stage P u c) (hSome a b)

theorem forged_isFreshSenderM3_eq {S : Setup} (P : Primitives) (u c : Bool)
    {G : Option (Nat × PrincipalEntry) → (Nat → PrincipalEntry → Bool) → (Unit → Bool) → Bool}
    (o : Option (Nat × PrincipalEntry))
    (hSome : ∀ a b,
      G (some (a, b)) (fun _ sEntry => !sEntry.corrupted) (fun _ => false) = !b.corrupted)
    (hNone : G none (fun _ sEntry => !sEntry.corrupted) (fun _ => false) = false) :
    authIntForgedAll (S := S) P u c
      (G o (fun _ sEntry => !sEntry.corrupted) (fun _ => false)) =
      authIntForgedAll (S := S) P u c (isFreshSenderM3 o) := by
  rcases o with _ | ⟨a, b⟩
  · exact congrArg (authIntForgedAll (S := S) P u c) hNone
  · exact congrArg (authIntForgedAll (S := S) P u c) (hSome a b)

theorem authRecvPtAtStage_g5_none_of_aeadDec_none {S : Setup} (P : Primitives)
    (u f : Bool) (m : Option (IdealAuthSession S)) (mk : MessageKeys) (ad ct : Bytes)
    (hDec : P.aeadDec mk ad ct = none) :
    authRecvPtAtStage .g5 P u false f m mk ad ct = none := by
  unfold authRecvPtAtStage
  cases u <;> cases f <;>
    simp [AuthHybridStage.idealFreshAead, AuthHybridStage.idealUnmatchedRecvAead, hDec]

theorem authIntForgedAll_false_of_aeadDec_none {S : Setup} (P : Primitives)
    (u sm f : Bool) (m : Option (IdealAuthSession S)) (mk : MessageKeys) (ad ct : Bytes)
    (hDec : P.aeadDec mk ad ct = none) :
    authIntForgedAll P u sm f m mk ad ct = false := by
  unfold authIntForgedAll
  cases u <;> cases sm <;> cases m <;> simp [hDec]

theorem relProbDom_drKey_step_M3 {S : Setup} {α5 α6 : Type}
    {R : α5 → α6 → Prop} {bad : α6 → Bool}
    (c : Bool) (m : Option (IdealAuthSession S))
    (ro : List (Bytes × DRKey)) (f : ProbComp (DRKey × List (Bytes × DRKey)))
    (jp5 : DRKey × List (Bytes × DRKey) → ProbComp α5)
    (jp6 : DRKey × List (Bytes × DRKey) → ProbComp α6)
    (hjp : ∀ a, RelProbDom R bad (jp5 a) (jp6 a)) :
    RelProbDom R bad
      (if c then
        match m with
        | some s => pure (s.drKey, ro) >>= jp5
        | none => sampleDRKey96 >>= fun dk => pure (dk, ro) >>= jp5
      else f >>= jp5)
      ((if c then
        match m with
        | some s => pure (s.drKey, ro)
        | none => sampleDRKey96 >>= fun dk => pure (dk, ro)
      else f) >>= jp6) := by
  cases c
  · exact RelProbDom.bind_same f hjp
  · cases m with
    | none =>
      simp only [↓reduceIte, bind_assoc, pure_bind]
      exact RelProbDom.bind_same sampleDRKey96 (fun dk => hjp (dk, ro))
    | some s => simp only [↓reduceIte, pure_bind]; exact hjp (s.drKey, ro)

theorem relProbDom_rk_ck_step_M3 {S : Setup} {α α5 α6 : Type}
    {R : α5 → α6 → Prop} {bad : α6 → Bool}
    (c : Bool) (m : Option (IdealAuthSession S)) (sameEph : Bool)
    (sVal : IdealAuthSession S → α) (wrap : Bytes → Bytes → α) (f : ProbComp α)
    (jp5 : α → ProbComp α5) (jp6 : α → ProbComp α6)
    (hjp : ∀ a, RelProbDom R bad (jp5 a) (jp6 a)) :
    RelProbDom R bad
      (if c then
        match m with
        | some s =>
          if sameEph then pure (sVal s) >>= jp5
          else sampleBytes32 >>= fun r => sampleBytes32 >>= fun d => pure (wrap r d) >>= jp5
        | none => sampleBytes32 >>= fun r => sampleBytes32 >>= fun d => pure (wrap r d) >>= jp5
      else f >>= jp5)
      ((if c then
        match m with
        | some s =>
          if sameEph then pure (sVal s)
          else sampleBytes32 >>= fun r => sampleBytes32 >>= fun d => pure (wrap r d)
        | none => sampleBytes32 >>= fun r => sampleBytes32 >>= fun d => pure (wrap r d)
      else f) >>= jp6) := by
  cases c
  · exact RelProbDom.bind_same f hjp
  · cases m with
    | none =>
      simp only [↓reduceIte, bind_assoc, pure_bind]
      exact RelProbDom.bind_same sampleBytes32 (fun r =>
        RelProbDom.bind_same sampleBytes32 (fun d => hjp (wrap r d)))
    | some s =>
      cases sameEph
      · simp only [Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
        exact RelProbDom.bind_same sampleBytes32 (fun r =>
          RelProbDom.bind_same sampleBytes32 (fun d => hjp (wrap r d)))
      · simp only [↓reduceIte, pure_bind]; exact hjp (sVal s)

theorem relProbDom_evalAuthRecvSchedule_mu {S : Setup} (P : Primitives)
    (hstDec : AuthHybridState S) (rc : Nat) (cache : AuthMkSaltCache S)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry) (opkPk? : Option Bytes)
    (secrets : Bytes) (msg : PreKeyMsg)
    (keys : List (Nat × MessageKeys)) (chal : List (Nat × (Bytes × Bytes)))
    (hPrinLen : hstDec.base.principals.length ≤ S.N_dh)
    (hSessLen : hstDec.idealSessions.length ≤ S.N_sess_tot)
    (hSess : ∀ s ∈ hstDec.idealSessions,
      keys.lookup (initSessionSlotIdx s.sid) = some s.deriveMessageKeys ∧
      chal.lookup (initSessionSlotIdx s.sid) = some (s.ad, s.aeadCt))
    (hChalLt : ∀ i, S.N_send_tot ≤ i → chal.lookup i = none)
    (hRecv : MuRecvInv S rc cache keys) :
    RelProbDom
      (fun p5 p6 =>
        p5.1.1 = p6.1.1 ∧ p6.1.2 = maskMuCache p5.1.2 ∧ p5.2 = false ∧ p6.2.2.2 = false ∧
        p6.2.2.1 = chal ∧ (∀ i, i < S.N_send_tot → p6.2.1.lookup i = keys.lookup i) ∧
        MuRecvInv S (rc + 1) p5.1.2 p6.2.1)
      (fun p6 => p6.2.2.2)
      (evalAuthRecvScheduleForgeAll true .g5 P hstDec rc cache kEntry bEntry opkPk? secrets msg)
      (runMu P (evalAuthRecvScheduleMuPrim S (projectMuHybrid P hstDec) rc (maskMuCache cache)
        kEntry bEntry opkPk? secrets msg) (keys, chal, false)) := by
  have hPostSame : MuRecvInv S (rc + 1) cache keys := hRecv.succ
  have hFreshC : chal.lookup (S.N_send_tot + rc) = none := hChalLt _ (Nat.le_add_right _ _)
  have hFreshK : keys.lookup (S.N_send_tot + rc) = none := hRecv.2 rc le_rfl
  have hKeysCons : ∀ mk : MessageKeys, ∀ i, i < S.N_send_tot →
      ((S.N_send_tot + rc, mk) :: keys).lookup i = keys.lookup i :=
    fun mk i hi => lookup_cons_ne _ _ _ _ (by omega)
  unfold evalAuthRecvScheduleForgeAll evalAuthRecvScheduleMuPrim
  rw [runMu_embedPrimMu_bind,
      simulateQ_prepAuthIntRecvSchedPrim_mu P hstDec kEntry bEntry opkPk? secrets msg
          hPrinLen hSessLen]
  dsimp only; simp only [bind_assoc]
  have hMemSess : ∀ s, hstDec.idealSessions.find?
      (matchIdealAuthHandshake P kEntry.ikAPk bEntry.spkPk opkPk? bEntry.pqspkPk msg.hdr) = some s →
      s ∈ hstDec.idealSessions := fun _ => List.mem_of_find?_eq_some
  revert hMemSess
  generalize hstDec.idealSessions.find?
    (matchIdealAuthHandshake P kEntry.ikAPk bEntry.spkPk opkPk? bEntry.pqspkPk msg.hdr)
        = matchedSess?
  intro hMemSess
  repeat (rw [or_r_isFreshSenderM3_eq matchedSess?.isSome
    (findHonestPrincipal P hstDec.base.principals msg.hdr.ikAPk)]; all_goals try (intros; rfl))
  repeat (rw [prep_isFreshSenderM3_eq
    (findHonestPrincipal P hstDec.base.principals msg.hdr.ikAPk)]; all_goals try (intros; rfl))
  generalize hSenderEq :
    isFreshSenderM3 (findHonestPrincipal P hstDec.base.principals msg.hdr.ikAPk)
      = isUncorruptedHonestSender
  refine relProbDom_drKey_step_M3 _ _ _ _ _ _ (fun ⟨drKey, roCache'⟩ => ?_); dsimp only
  refine relProbDom_rk_ck_step_M3 _ _ _ (fun s => ((s.rk1, s.ck1_0), hstDec.base.rootRoCache))
    (fun r c => ((r, c), hstDec.base.rootRoCache)) _ _ _ (fun ⟨⟨rk1, ck1_0⟩,
        rootRoCache'⟩ => ?_); dsimp only
  refine relProbDom_rk_ck_step_M3 _ _ _ (fun s => (s.mkSeed, s.ck1_1))
    (fun ms cn => (ms, cn)) _ _ _ (fun ⟨mkSeed, ck1_1⟩ => ?_); dsimp only
  cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
  | none =>
    simp only [pure_bind, runMu_pure]
    exact RelProbDom.of_pure ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, hPostSame⟩
  | some spqrPair =>
    rcases spqrPair with ⟨_pqrStB, spqrSalt?⟩
    simp only [pure_bind]
    repeat (rw [pt_isFreshSenderM3_eq .g5 P _ _
      (findHonestPrincipal P hstDec.base.principals msg.hdr.ikAPk)]; all_goals try (intros; rfl))
    repeat (rw [forged_isFreshSenderM3_eq P _ _
      (findHonestPrincipal P hstDec.base.principals msg.hdr.ikAPk)]; all_goals try (intros; rfl))
    rw [hSenderEq]; clear hSenderEq
    unfold finishAuthRecvScheduleMuPrim; dsimp only
    generalize firstMsgAD msg.hdr.ikAPk kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg = ad
    cases hIdeal : (matchedSess?.isSome || isUncorruptedHonestSender) with
    | false =>
      simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, pure_bind,
        runMu_bind, runMu_deriveMsgKeys, runMu_aeadDec]
      unfold authRecvPtAtStage authIntForgedAll
      simp only [Bool.false_eq_true, ↓reduceIte]
      cases P.aeadDec (P.deriveMsgKeys mkSeed spqrSalt?) ad msg.aeadCt <;>
        (dsimp only [runMu_pure]
         exact RelProbDom.of_pure ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, hPostSame⟩)
    | true =>
      simp only [Bool.true_and, ↓reduceIte]
      cases matchedSess? with
      | none =>
        dsimp only [Option.map]
        simp only [runMu_bind,
          runMu_tryForgeMuQ_fresh P _ _ _ keys chal false hFreshC hFreshK,
          bind_assoc]
        refine RelProbDom.bind_same sampleMessageKeys80 (fun mk => ?_)
        cases hDec : P.aeadDec mk ad msg.aeadCt with
        | some pt => exact RelProbDom.bad6 _ _ (by simp)
        | none =>
          simp only [authRecvPtAtStage_g5_none_of_aeadDec_none _ _ _ _ _ _ _ hDec,
            authIntForgedAll_false_of_aeadDec_none _ _ _ _ _ _ _ _ hDec, pure_bind, runMu_pure]
          exact RelProbDom.of_pure ⟨rfl, rfl, rfl, rfl, rfl, hKeysCons mk,
            hRecv.push_fresh mk⟩
      | some s =>
        have hsMem : s ∈ hstDec.idealSessions := hMemSess s rfl
        clear hMemSess
        dsimp only [Option.map]
        simp only [maskMuSession_spqrSalt?, maskMuSession_sid, maskMuSession_ad,
          maskMuSession_aeadCt, maskMuSession_msgPlain]
        rcases Bool.eq_false_or_eq_true (P.pow8 msg.ephAPk == P.pow8 s.ephAPk) with hEph | hEph
        ·
          simp only [hEph, Bool.true_and]
          rcases Bool.eq_false_or_eq_true (sameSaltKey spqrSalt? s.spqrSalt?) with hSm | hSm
          ·
            simp only [hSm, ↓reduceIte]
            rcases hSess s hsMem with ⟨hK, hC⟩
            cases hAdCt : (ad == s.ad && msg.aeadCt == s.aeadCt) with
            | true =>
              unfold authRecvPtAtStage authIntForgedAll
              simp only [hAdCt, ↓reduceIte, Bool.not_true, Bool.false_and, runMu_pure,
                AuthHybridStage.idealFreshAead, Bool.and_true]
              exact RelProbDom.of_pure ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, hPostSame⟩
            | false =>
              have hC' : (chal.lookup (initSessionSlotIdx s.sid) == some (ad, msg.aeadCt)) =
                  false := by rw [hC]; exact chal_beq_eq_false_M3 hAdCt
              simp only [Bool.false_eq_true, ↓reduceIte, runMu_bind,
                runMu_tryForgeMuQ_some P _ _ _ keys chal false s.deriveMessageKeys hC' hK]
              cases hDec : P.aeadDec s.deriveMessageKeys ad msg.aeadCt with
              | some pt => exact RelProbDom.bad6 _ _ (by simp)
              | none =>
                unfold authRecvPtAtStage authIntForgedAll
                simp only [hAdCt, hDec, ↓reduceIte, Bool.not_false,
                  Bool.false_eq_true, Option.isSome_none, Bool.and_false, pure_bind, runMu_pure,
                  AuthHybridStage.idealFreshAead, Bool.and_true]
                exact RelProbDom.of_pure ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, hPostSame⟩
          · simp only [hSm, Bool.false_eq_true, ↓reduceIte,
              find?_maskMuCache_pred (p := fun k => mkSaltKeyMatch k s.sid spqrSalt?)]
            cases hFind : cache.find? (fun (k, _) => mkSaltKeyMatch k s.sid spqrSalt?) with
            | some entry =>
              rcases entry with ⟨k0, r0, mk0⟩
              have hMem0 := List.mem_of_find?_eq_some hFind
              rcases hRecv.1 k0 r0 mk0 hMem0 with ⟨_, hK0⟩
              have hC0 : (chal.lookup (S.N_send_tot + r0) == some (ad, msg.aeadCt)) = false := by
                rw [hChalLt _ (Nat.le_add_right _ _)]; rfl
              simp only [Option.map, runMu_bind,
                runMu_tryForgeMuQ_some P _ _ _ keys chal false mk0 hC0 hK0]
              cases hDec : P.aeadDec mk0 ad msg.aeadCt with
              | some pt => exact RelProbDom.bad6 _ _ (by simp)
              | none =>
                simp only [authRecvPtAtStage_g5_none_of_aeadDec_none _ _ _ _ _ _ _ hDec,
                  authIntForgedAll_false_of_aeadDec_none _ _ _ _ _ _ _ _ hDec, pure_bind,
                  runMu_pure]
                exact RelProbDom.of_pure ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, hPostSame⟩
            | none =>
              simp only [Option.map, runMu_bind,
                runMu_tryForgeMuQ_fresh P _ _ _ keys chal false hFreshC hFreshK, bind_assoc]
              refine RelProbDom.bind_same sampleMessageKeys80 (fun mk => ?_)
              cases hDec : P.aeadDec mk ad msg.aeadCt with
              | some pt => exact RelProbDom.bad6 _ _ (by simp)
              | none =>
                simp only [authRecvPtAtStage_g5_none_of_aeadDec_none _ _ _ _ _ _ _ hDec,
                  authIntForgedAll_false_of_aeadDec_none _ _ _ _ _ _ _ _ hDec, pure_bind,
                  runMu_pure]
                exact RelProbDom.of_pure ⟨rfl, rfl, rfl, rfl, rfl, hKeysCons mk,
                  hRecv.push_cache _ mk⟩

        ·
          simp only [hEph, Bool.false_and, Bool.false_eq_true, ↓reduceIte, runMu_bind,
            runMu_tryForgeMuQ_fresh P _ _ _ keys chal false hFreshC hFreshK,
            bind_assoc]
          refine RelProbDom.bind_same sampleMessageKeys80 (fun mk => ?_)
          cases hDec : P.aeadDec mk ad msg.aeadCt with
          | some pt => exact RelProbDom.bad6 _ _ (by simp)
          | none =>
            simp only [authRecvPtAtStage_g5_none_of_aeadDec_none _ _ _ _ _ _ _ hDec,
              authIntForgedAll_false_of_aeadDec_none _ _ _ _ _ _ _ _ hDec, pure_bind, runMu_pure]
            exact RelProbDom.of_pure ⟨rfl, rfl, rfl, rfl, rfl, hKeysCons mk,
              hRecv.push_fresh mk⟩

theorem initSessionSlotIdx_lt_of_isSend {S : Setup} {sid : SessionId S}
    (h : IsSendSessionId S sid) : initSessionSlotIdx sid < S.N_send_tot := by
  cases sid with
  | sendOPK u i =>
    exact Nat.lt_of_lt_of_le (initSessionSlotIdx_sendOPK_lt u i) (Nat.le_add_right _ _)
  | sendNoOPK u i => exact initSessionSlotIdx_sendNoOPK_lt u i
  | recvOPK _ _ _ => exact h.elim
  | recvNoOPK _ _ _ => exact h.elim

theorem MuInv.of_recv_none {S : Setup} {P : Primitives}
    {hst : AuthHybridStateFixed S} {keys : List (Nat × MessageKeys)}
    {chal : List (Nat × (Bytes × Bytes))}
    (hInv : MuInv S P hst (projectMuState P hst) keys chal) :
    MuInv S P { hst with recvCount := hst.recvCount + 1 }
      { projectMuState P hst with recvCount := hst.recvCount + 1 } keys chal :=
  ⟨rfl, hInv.hValid, hInv.hSess, hInv.hFresh, hInv.hChalLt, hInv.hRecv.succ⟩

theorem MuInv.of_recv_finish {S : Setup} {P : Primitives}
    {hst : AuthHybridStateFixed S} {keys keys' : List (Nat × MessageKeys)}
    {chal : List (Nat × (Bytes × Bytes))}
    (hInv : MuInv S P hst (projectMuState P hst) keys chal)
    (hst' : AuthHybridState S) (cache' : AuthMkSaltCache S)
    (hV : ValidAuthLengths S hst')
    (hUsed : hst'.base.usedSendSessions = hst.toAuthHybridState.base.usedSendSessions)
    (hIdeal : hst'.idealSessions = hst.toAuthHybridState.idealSessions)
    (hKeys : ∀ i, i < S.N_send_tot → keys'.lookup i = keys.lookup i)
    (hRecv : MuRecvInv S (hst.recvCount + 1) cache' keys') :
    MuInv S P { toAuthHybridState := hst', recvCount := hst.recvCount + 1, mkSaltCache := cache' }
      { toAuthHybridState := projectMuHybrid P hst', recvCount := hst.recvCount + 1,
        mkSaltCache := maskMuCache cache' } keys' chal := by
  refine ⟨rfl, hV, ?_, ?_, hInv.hChalLt, hRecv⟩
  · intro s hs; dsimp only at hs ⊢; rw [hIdeal] at hs; rw [hUsed]
    rcases hInv.hSess s hs with ⟨h1, h2, h3, h4, h5⟩
    exact ⟨h1, h2, h3, (hKeys _ h3).trans h4, h5⟩
  · intro sid hSend hNot; dsimp only at hNot ⊢; rw [hUsed] at hNot
    rcases hInv.hFresh sid hSend hNot with ⟨h1, h2⟩
    exact ⟨(hKeys _ (initSessionSlotIdx_lt_of_isSend hSend)).trans h1, h2⟩

theorem relProbDom_stepAuthMu {S : Setup} (P : Primitives)
    (q : AuthQuery S) (hst hst6 : AuthHybridStateFixed S)
    (keys : List (Nat × MessageKeys)) (chal : List (Nat × (Bytes × Bytes)))
    (hInv : MuInv S P hst hst6 keys chal)
    (hNoWin : hst.toAuthHybridState.base.hasWonAuth = false) :
    RelProbDom
      (fun p5 p6 => p5.1 = p6.1.1 ∧ p5.2.2 = false ∧ p6.2.2.2 = false ∧
        MuInv S P p5.2.1 p6.1.2 p6.2.1 p6.2.2.1)
      (fun p6 => p6.2.2.2)
      ((pqxdhAuthForgeAllImpl true .g5 S P q).run (hst, false))
      (runMu P (stepAuthMuPrim S q hst6) (keys, chal, false)) := by
  have hStage : (AuthHybridStage.g3_8).idealMsgKeys = true := rfl
  cases q with
  | sendOPK u i bundle m0 m1 =>
    unfold pqxdhAuthForgeAllImpl stepAuthMuPrim pqxdhAuthHybridSplitFixedImpl
        pqxdhAuthHybridKoskImpl
    simp only [hStage, hNoWin, Bool.not_true, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
      isAuthRecvQuery,
      StateT.run_mk, StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      StateT.run_set, StateT.run_pure, pure_bind, bind_assoc]
    cases bundle.opkB?.isNone
    · simp only [Bool.false_eq_true, ↓reduceIte, runAuthHybridSendKosk_eq,
        map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]
      simpa only [map_eq_bind_pure_comp, Function.comp_def]
          using relProbDom_runAuthSend_mu P (.sendOPK u i) trivial
        (Nat.lt_of_lt_of_le (initSessionSlotIdx_sendOPK_lt u i) (Nat.le_add_right _ _))
        u bundle m0 m1 hst hst6 keys chal hInv
    · rcases hInv.hProj with rfl
      simp only [↓reduceIte, StateT.run_pure, pure_bind, map_pure, runMu_pure]
      exact RelProbDom.of_pure ⟨rfl, rfl, rfl, hInv.of_base_eq rfl hInv.hValid rfl rfl rfl rfl⟩
  | sendNoOPK u i bundle m0 m1 =>
    unfold pqxdhAuthForgeAllImpl stepAuthMuPrim pqxdhAuthHybridSplitFixedImpl
        pqxdhAuthHybridKoskImpl
    simp only [hStage, hNoWin, Bool.not_true, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
      isAuthRecvQuery,
      StateT.run_mk, StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      StateT.run_set, StateT.run_pure, pure_bind, bind_assoc]
    cases bundle.opkB?.isSome
    · simp only [Bool.false_eq_true, ↓reduceIte, runAuthHybridSendKosk_eq,
        map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]
      simpa only [map_eq_bind_pure_comp, Function.comp_def]
          using relProbDom_runAuthSend_mu P (.sendNoOPK u i) trivial
        (initSessionSlotIdx_sendNoOPK_lt u i) u bundle m0 m1 hst hst6 keys chal hInv
    · rcases hInv.hProj with rfl
      simp only [↓reduceIte, StateT.run_pure, pure_bind, map_pure, runMu_pure]
      exact RelProbDom.of_pure ⟨rfl, rfl, rfl, hInv.of_base_eq rfl hInv.hValid rfl rfl rfl rfl⟩
  | recvOPK k j o msg =>
    rcases hInv.hProj with rfl
    rcases validAuthLengths_bounds S P hInv.hValid with ⟨hPrinLen, _, _, hSessLen⟩
    unfold pqxdhAuthForgeAllImpl stepAuthMuPrim
    dsimp only [StateT.run_mk]
    have hTo : (projectMuState P hst).toAuthHybridState =
        projectMuHybrid P hst.toAuthHybridState := rfl
    have hRc : (projectMuState P hst).recvCount = hst.recvCount := rfl
    have hMc : (projectMuState P hst).mkSaltCache = maskMuCache hst.mkSaltCache := rfl
    rw [runMu_embedPrimMu_bind, hTo,
        simulateQ_prepareAuthRecvOPKPrim_mu P k j o msg hst.toAuthHybridState hPrinLen hNoWin,
        pure_bind]
    cases hprep : prepareAuthHybridRecvOPK true P k j o msg hst.toAuthHybridState with
    | none =>
      simp only [Option.map_none, runMu_pure]
      exact RelProbDom.of_pure ⟨rfl, rfl, rfl, hInv.of_recv_none⟩
    | some prep =>
      rcases prepareAuthHybridRecvOPK_valid_mu true P k j o msg hst.toAuthHybridState hInv.hValid
          hprep with ⟨hDecPrin, hDecUsed, hDecIdeal, hFinValid⟩
      simp only [Option.map_some, map_eq_bind_pure_comp, Function.comp_def, runMu_bind, hRc, hMc]
      refine RelProbDom.bind_rel
        (relProbDom_evalAuthRecvSchedule_mu P prep.hstDec hst.recvCount hst.mkSaltCache
          prep.kEntry prep.bEntry prep.opkPk? prep.secrets msg keys chal
          (hDecPrin ▸ hPrinLen) (hDecIdeal ▸ hSessLen)
          (by rw [hDecIdeal]; exact fun s hs => ⟨(hInv.hSess s hs).2.2.2.1,
            (hInv.hSess s hs).2.2.2.2⟩)
          hInv.hChalLt hInv.hRecv)
        (fun b6 hb6 y6 hy6 => by
          simp only [runMu_pure, support_pure, Set.mem_singleton_iff] at hy6
          subst hy6; exact hb6)
        (fun b5 b6 ⟨hRes, hMc', hf5, hw6, hChal', hKeys', hRecv'⟩ => ?_)
      rcases b5 with ⟨⟨res5?, mkSaltCache5'⟩, forged5⟩
      rcases b6 with ⟨⟨res6?, mkSaltCache6'⟩, keys', chal', w'⟩
      dsimp only at hRes hMc' hf5 hw6 hChal' hKeys' hRecv'
      subst hRes hMc' hf5 hw6 hChal'
      simp only [Bool.false_or, runMu_pure]
      rcases hFinValid res5? with ⟨hVFin, hUsedFin, hIdealFin⟩
      exact RelProbDom.of_pure ⟨rfl, rfl, rfl,
        hInv.of_recv_finish _ _ hVFin hUsedFin hIdealFin hKeys' hRecv'⟩
  | recvNoOPK k j l msg =>
    rcases hInv.hProj with rfl
    rcases validAuthLengths_bounds S P hInv.hValid with ⟨hPrinLen, _, _, hSessLen⟩
    unfold pqxdhAuthForgeAllImpl stepAuthMuPrim
    dsimp only [StateT.run_mk]
    have hTo : (projectMuState P hst).toAuthHybridState =
        projectMuHybrid P hst.toAuthHybridState := rfl
    have hRc : (projectMuState P hst).recvCount = hst.recvCount := rfl
    have hMc : (projectMuState P hst).mkSaltCache = maskMuCache hst.mkSaltCache := rfl
    rw [runMu_embedPrimMu_bind, hTo,
        simulateQ_prepareAuthRecvNoOPKPrim_mu P k j l msg hst.toAuthHybridState hPrinLen hNoWin,
        pure_bind]
    cases hprep : prepareAuthHybridRecvNoOPK true P k j l msg hst.toAuthHybridState with
    | none =>
      simp only [Option.map_none, runMu_pure]
      exact RelProbDom.of_pure ⟨rfl, rfl, rfl, hInv.of_recv_none⟩
    | some prep =>
      rcases prepareAuthHybridRecvNoOPK_valid_mu true P k j l msg hst.toAuthHybridState
          hInv.hValid hprep with ⟨hDecPrin, hDecUsed, hDecIdeal, hFinValid⟩
      simp only [Option.map_some, map_eq_bind_pure_comp, Function.comp_def, runMu_bind, hRc, hMc]
      refine RelProbDom.bind_rel
        (relProbDom_evalAuthRecvSchedule_mu P prep.hstDec hst.recvCount hst.mkSaltCache
          prep.kEntry prep.bEntry prep.opkPk? prep.secrets msg keys chal
          (hDecPrin ▸ hPrinLen) (hDecIdeal ▸ hSessLen)
          (by rw [hDecIdeal]; exact fun s hs => ⟨(hInv.hSess s hs).2.2.2.1,
            (hInv.hSess s hs).2.2.2.2⟩)
          hInv.hChalLt hInv.hRecv)
        (fun b6 hb6 y6 hy6 => by
          simp only [runMu_pure, support_pure, Set.mem_singleton_iff] at hy6
          subst hy6; exact hb6)
        (fun b5 b6 ⟨hRes, hMc', hf5, hw6, hChal', hKeys', hRecv'⟩ => ?_)
      rcases b5 with ⟨⟨res5?, mkSaltCache5'⟩, forged5⟩
      rcases b6 with ⟨⟨res6?, mkSaltCache6'⟩, keys', chal', w'⟩
      dsimp only at hRes hMc' hf5 hw6 hChal' hKeys' hRecv'
      subst hRes hMc' hf5 hw6 hChal'
      simp only [Bool.false_or, runMu_pure]
      rcases hFinValid res5? with ⟨hVFin, hUsedFin, hIdealFin⟩
      exact RelProbDom.of_pure ⟨rfl, rfl, rfl,
        hInv.of_recv_finish _ _ hVFin hUsedFin hIdealFin hKeys' hRecv'⟩
  | initPrin _ | corruptIK _ | genSPK _ _ | genOPK _ _ _ | registerKey _ | roQuery _
  | roRootQuery _ _ | revealDhSecrets =>
    rcases hInv.hProj with rfl
    unfold pqxdhAuthForgeAllImpl stepAuthMuPrim
    dsimp only [StateT.run_mk]
    rw [runMu_embedPrimMu,
        simulateQ_stepAuthOtherPrim_projectMuState P _ hst (by intro h; cases h)
            (by intro h; cases h) hNoWin]
    simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind, Prod.map]
    refine RelProbDom.bind_same_of_support _ (fun ⟨resp, hst'⟩ hy => ?_)
    rcases validAuthLengths_stepAuthOther_mu P _ hst (by intro h; cases h) (by intro h; cases h)
        hNoWin hInv.hValid hy with
      ⟨hV', hUsed', hIdeal', hRc', hMc'⟩
    exact RelProbDom.of_pure ⟨rfl, rfl, rfl, hInv.of_base_eq rfl hV' hUsed' hIdeal' hRc' hMc'⟩

def RelProbDomZ {α5 α6 : Type} (R : α5 → α6 → Prop) (bad5 : α5 → Bool)
    (bad6 : α6 → Bool) (m5 : ProbComp α5) (m6 : ProbComp α6) : Prop :=
  ∀ (w5 : α5 → ℝ≥0∞) (w6 : α6 → ℝ≥0∞),
    (∀ y5, w5 y5 ≤ 1) →
    (∀ y5, bad5 y5 = false → w5 y5 = 0) →
    (∀ y6, bad6 y6 = true → w6 y6 = 1) →
    (∀ y5 y6, R y5 y6 → w5 y5 ≤ w6 y6) →
    probExpect m5 w5 ≤ probExpect m6 w6

theorem RelProbDomZ.of_pure {α5 α6 : Type} {R : α5 → α6 → Prop}
    {bad5 : α5 → Bool} {bad6 : α6 → Bool} {x5 : α5} {x6 : α6} (h : R x5 x6) :
    RelProbDomZ R bad5 bad6 (pure x5) (pure x6) :=
  fun _ _ _ _ _ hle => by simp only [probExpect_pure]; exact hle x5 x6 h

theorem RelProbDomZ.of_bad5_false {α5 α6 : Type} {R : α5 → α6 → Prop}
    {bad5 : α5 → Bool} {bad6 : α6 → Bool} (m5 : ProbComp α5) (m6 : ProbComp α6)
    (h0 : ∀ y5 ∈ support m5, bad5 y5 = false) :
    RelProbDomZ R bad5 bad6 m5 m6 :=
  fun w5 _ _ hw5_0 _ _ =>
    (probExpect_const_le_of_support m5 w5 0 (fun y5 hy5 => (hw5_0 y5 (h0 y5 hy5)).le)).trans
      zero_le

theorem RelProbDomZ.bind_same {β α5 α6 : Type} {R : α5 → α6 → Prop}
    {bad5 : α5 → Bool} {bad6 : α6 → Bool} (mx : ProbComp β)
    {f5 : β → ProbComp α5} {f6 : β → ProbComp α6}
    (h : ∀ b, RelProbDomZ R bad5 bad6 (f5 b) (f6 b)) :
    RelProbDomZ R bad5 bad6 (mx >>= f5) (mx >>= f6) :=
  fun w5 w6 hw5 hw5_0 hw6 hle => by
    rw [probExpect_bind, probExpect_bind]
    exact probExpect_mono_of_support mx _ _ (fun b _ => h b w5 w6 hw5 hw5_0 hw6 hle)

theorem RelProbDomZ.bind_rel {β5 β6 α5 α6 : Type}
    {R1 : β5 → β6 → Prop} {bad1 : β6 → Bool}
    {R2 : α5 → α6 → Prop} {bad5 : α5 → Bool} {bad6 : α6 → Bool}
    {m5 : ProbComp β5} {m6 : ProbComp β6} {f5 : β5 → ProbComp α5} {f6 : β6 → ProbComp α6}
    (hm : RelProbDom R1 bad1 m5 m6)
    (hbad : ∀ b6, bad1 b6 = true → ∀ y6 ∈ support (f6 b6), bad6 y6 = true)
    (hf : ∀ b5 b6, R1 b5 b6 → RelProbDomZ R2 bad5 bad6 (f5 b5) (f6 b6)) :
    RelProbDomZ R2 bad5 bad6 (m5 >>= f5) (m6 >>= f6) :=
  fun w5 w6 hw5 hw5_0 hw6 hle => by
    rw [probExpect_bind, probExpect_bind]
    exact hm _ _ (fun _ => probExpect_const_le_of_support _ _ 1 (fun y5 _ => hw5 y5))
      (fun b6 hb6 =>
        probExpect_eq_const_of_support _ _ 1 (fun y6 hy6 => hw6 y6 (hbad b6 hb6 y6 hy6)))
      (fun b5 b6 hR1 => hf b5 b6 hR1 w5 w6 hw5 hw5_0 hw6 hle)

theorem RelProbDomZ.evalDist_le {α5 α6 : Type} {R : α5 → α6 → Prop}
    {bad5 : α5 → Bool} {bad6 : α6 → Bool} {m5 : ProbComp α5} {m6 : ProbComp α6}
    (hm : RelProbDomZ R bad5 bad6 m5 m6) (hR : ∀ y5 y6, R y5 y6 → bad5 y5 = false) :
    𝒟[m5 >>= fun y5 => pure (bad5 y5)] {true} ≤ 𝒟[m6 >>= fun y6 => pure (bad6 y6)] {true} := by
  rw [evalDist_bind_true_eq_probExpect m5 bad5, evalDist_bind_true_eq_probExpect m6 bad6]
  exact hm _ _ (fun _ => MeasureTheory.prob_le_one)
    (fun y5 hy5 => by rw [hy5]; simp)
    (fun y6 hb6 => by rw [hb6]; simp)
    (fun y5 y6 h => by rw [hR y5 y6 h]; simp)

theorem pqxdhAuthForgeAllImpl_frozen_of_hasWonAuth
    {S : Setup} (P : Primitives) (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (hWin : hst.toAuthHybridState.base.hasWonAuth = true)
    {p : (authSpec S).Range q × (AuthHybridStateFixed S × Bool)}
    (hp : p ∈ support ((pqxdhAuthForgeAllImpl true .g5 S P q).run (hst, false))) :
    p.2.1.toAuthHybridState.base.hasWonAuth = true ∧ p.2.2 = false := by
  have hStage : (AuthHybridStage.g3_8).idealMsgKeys = true := rfl
  cases q with
  | recvOPK k j o msg =>
    unfold pqxdhAuthForgeAllImpl prepareAuthHybridRecvOPK at hp
    simp only [hWin, Bool.true_and, ↓reduceIte, StateT.run_mk, support_pure,
      Set.mem_singleton_iff] at hp
    subst hp; exact ⟨hWin, rfl⟩
  | recvNoOPK k j l msg =>
    unfold pqxdhAuthForgeAllImpl prepareAuthHybridRecvNoOPK at hp
    simp only [hWin, Bool.true_and, ↓reduceIte, StateT.run_mk, support_pure,
      Set.mem_singleton_iff] at hp
    subst hp; exact ⟨hWin, rfl⟩
  | _ =>
    unfold pqxdhAuthForgeAllImpl pqxdhAuthHybridSplitFixedImpl
      pqxdhAuthHybridKoskImpl at hp
    simp only [hStage, hWin, Bool.not_true, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
      StateT.run_mk, StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      StateT.run_set, StateT.run_pure, pure_bind, bind_assoc, map_pure, support_pure,
      Set.mem_singleton_iff] at hp
    subst hp; exact ⟨hWin, rfl⟩

theorem simulateQ_authForgeAll_forged_false_of_hasWonAuth
    {S : Setup} {α : Type} (P : Primitives)
    (oa : OracleComp (unifSpec + authSpec S) α) (hst : AuthHybridStateFixed S)
    (hWin : hst.toAuthHybridState.base.hasWonAuth = true)
    {p : α × (AuthHybridStateFixed S × Bool)}
    (hp : p ∈ support ((simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (AuthHybridStateFixed S × Bool) ProbComp) +
      pqxdhAuthForgeAllImpl true .g5 S P) oa).run (hst, false))) :
    p.2.1.toAuthHybridState.base.hasWonAuth = true ∧ p.2.2 = false := by
  induction oa using OracleComp.inductionOn generalizing hst with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst hp; exact ⟨hWin, rfl⟩
  | query_bind q mx ih =>
    rcases q with uq | aq
    · rw [FgGapDh.simulateQ_run_query_inl] at hp
      rcases MonadAttach.mem_support_bind.mp hp with ⟨u, _, hp'⟩
      exact ih u hst hWin hp'
    · rw [FgGapDh.simulateQ_run_query_inr] at hp
      rcases MonadAttach.mem_support_bind.mp hp with ⟨⟨r, hst', f'⟩, hq, hp'⟩
      rcases pqxdhAuthForgeAllImpl_frozen_of_hasWonAuth P aq hst hWin hq with ⟨hWin', rfl⟩
      exact ih r hst' hWin' hp'

theorem relProbDomZ_runWithMuStep {S : Setup} {α : Type} (P : Primitives)
    (oa : OracleComp (unifSpec + authSpec S) α)
    (hst hst6 : AuthHybridStateFixed S)
    (keys : List (Nat × MessageKeys)) (chal : List (Nat × (Bytes × Bytes)))
    (hInv : MuInv S P hst hst6 keys chal) :
    let impl :=
        (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridStateFixed S × Bool)
            ProbComp) +
      pqxdhAuthForgeAllImpl true .g5 S P
    RelProbDomZ
      (fun p5 p6 => p5.1 = p6.1.1 ∧ p5.2.2 = false ∧ p6.2.2.2 = false ∧
        MuInv S P p5.2.1 p6.1.2 p6.2.1 p6.2.2.1)
      (fun p5 => p5.2.2)
      (fun p6 => p6.2.2.2)
      ((simulateQ impl oa).run (hst, false))
      (runMu P (runWithMuStep (stepAuthMuPrim S) oa hst6) (keys, chal, false)) := by
  intro impl
  induction oa using OracleComp.inductionOn generalizing hst hst6 keys chal with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, runWithMuStep_pure, runMu_pure]
    exact RelProbDomZ.of_pure ⟨rfl, rfl, rfl, hInv⟩
  | query_bind q mx ih =>
    rcases q with uq | aq
    · dsimp only [impl]
      rw [FgGapDh.simulateQ_run_query_inl, runWithMuStep_query_inl, runMu_bind,
          runMu_query_inl, bind_assoc]
      refine RelProbDomZ.bind_same (QueryImpl.ofLift unifSpec ProbComp uq) (fun u => ?_)
      rw [pure_bind]
      exact ih u hst hst6 keys chal hInv
    · by_cases hWin : hst.toAuthHybridState.base.hasWonAuth = true
      · exact RelProbDomZ.of_bad5_false _ _ (fun y5 hy5 =>
          (simulateQ_authForgeAll_forged_false_of_hasWonAuth P
            (liftM (OracleSpec.query (Sum.inr aq)) >>= mx) hst hWin hy5).2)
      · have hNoWin := Bool.eq_false_iff.mpr hWin
        dsimp only [impl]
        rw [FgGapDh.simulateQ_run_query_inr, runWithMuStep_query_inr, runMu_bind]
        refine RelProbDomZ.bind_rel
          (relProbDom_stepAuthMu P aq hst hst6 keys chal hInv hNoWin)
          (fun b6 hb6 y6 hy6 => by
            rcases b6 with ⟨⟨r6, hst6'⟩, keys', chal', w'⟩
            dsimp only at hb6; subst hb6
            exact runMu_w_mono P _ keys' chal' y6 hy6)
          (fun b5 b6 ⟨h1, h2, h3, hInv'⟩ => ?_)
        rcases b5 with ⟨r5, hst5', forged5⟩
        rcases b6 with ⟨⟨r6, hst6'⟩, keys', chal', w'⟩
        dsimp only at h1 h2 h3 hInv'
        subst h1 h2 h3
        exact ih r5 hst5' hst6' keys' chal' hInv'

theorem simulateQ_run_congr_of_bound {ι σ : Type} {spec : OracleSpec.{0, 0} ι}
    (impl₁ impl₂ : QueryImpl spec (StateT σ ProbComp)) (Q : ι → Prop) [DecidablePred Q]
    (h : ∀ t, ¬ Q t → impl₁ t = impl₂ t) {α : Type} (oa : OracleComp spec α) :
    IsQueryBoundP oa Q 0 → ∀ s, (simulateQ impl₁ oa).run s = (simulateQ impl₂ oa).run s := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro _ s; simp
  | query_bind t k ih =>
    intro hQ s
    rw [isQueryBoundP_query_bind_iff] at hQ
    obtain ⟨h1, h2⟩ := hQ
    have hnQ : ¬ Q t := by
      rcases h1 with h | h
      · exact h
      · exact absurd h (Nat.lt_irrefl 0)
    simp only [hnQ, ↓reduceIte] at h2
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind, h t hnQ]
    exact bind_congr fun p => ih p.1 (h2 p.1) p.2

theorem haMuFull_eq_aeadMuFullImpl (P : Primitives) (t : (ℕ ⊕ PrimQuery) ⊕ AeadMuIntQuery)
    (ht : ¬ badAdQuery goodFirstMsgAD t) : haMuFull P t = aeadMuFullImpl P t := by
  rcases t with pq | (⟨i, ad, pt⟩ | ⟨i, ad, ct⟩)
  · rfl
  · have hg : goodFirstMsgAD ad = true := by simpa [badAdQuery] using ht
    simp only [haMuFull, aeadMuFullImpl, QueryImpl.add_apply_inr, haMuImpl, aeadMuImpl, hg,
      Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rfl
  · have hg : goodFirstMsgAD ad = true := by simpa [badAdQuery] using ht
    simp only [haMuFull, aeadMuFullImpl, QueryImpl.add_apply_inr, haMuImpl, aeadMuImpl, hg,
      Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rfl

theorem aeadMuIntCtxtExp_eq_runMu_of_disciplined (P : Primitives) (A : AeadMuIntCtxtAdv)
    (hA : MacInputDisciplined' P goodFirstMsgAD A) :
    aeadMuIntCtxtExp P A = (runMu P A.run ([], [], false) >>= fun p => pure p.2.2.2) := by
  have h1 := simulateQ_primDet_run P (haMuFull P)
    (fun op s => by simp [haMuFull, primBaseImpl, primImpl_eq_pure]) A.run ([], [], false)
  have h2 := simulateQ_primDet_run P (aeadMuFullImpl P)
    (fun op s => by simp [aeadMuFullImpl, primBaseImpl, primImpl_eq_pure]) A.run ([], [], false)
  have h3 := simulateQ_run_congr_of_bound (haMuFull P) (aeadMuFullImpl P) _
    (haMuFull_eq_aeadMuFullImpl P) _ hA ([], [], false)
  rw [ha_exp_eq, ← h1, h3, h2]

/-- Bounds the all-sessions forgery probability of `split(.g3_8, .g5, true)` by the multi-key
    `INT-CTXT` advantage of `aeadMuIntReductionAuth`. -/
theorem authIntForgeAllExp_le_aeadMuIntCtxt (S : Setup) (P : Primitives)
    (hP : WellFormedPrimitivesδ P)
    (hLaw : ∀ p e, P.pow8 p = P.pow8 (P.x25519Base e) → p.length = 32) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    (𝒟[authIntForgeAllExp S P A.1] {true}).toReal ≤
      AeadMuIntCtxt P (aeadMuIntReductionAuth S b A) := by
  unfold AeadMuIntCtxt
  rw [aeadMuIntCtxtExp_eq_runMu_of_disciplined P (aeadMuIntReductionAuth S b A)
    (aeadMuIntReductionAuth_disciplined S P hP hLaw b A)]
  have hRed : (runMu P (aeadMuIntReductionAuth S b A).run ([], [], false) >>=
      fun p => pure p.2.2.2) =
    ($ᵗ Bool >>= fun secb =>
      runMu P (runWithMuStep (stepAuthMuPrim S) A.1.run (AuthHybridStateFixed.empty S secb))
        ([], [], false) >>= fun p6 => pure p6.2.2.2) := by
    unfold aeadMuIntReductionAuth aeadMuIntReductionAuthRun
    dsimp only
    simp only [runMu_bind, runMu_unifMu, runMu_pure, bind_assoc, pure_bind]
  have hForge : authIntForgeAllExp S P A.1 =
    ($ᵗ Bool >>= fun secb =>
      (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridStateFixed S ×
          Bool) ProbComp) +
        pqxdhAuthForgeAllImpl true .g5 S P) A.1.run).run
        (AuthHybridStateFixed.empty S secb, false) >>= fun p5 => pure p5.2.2) := by
    unfold authIntForgeAllExp; rfl
  rw [hRed, hForge]
  have hDom : RelProbDomZ
      (fun (p5 : Bool × (AuthHybridStateFixed S × Bool)) p6 =>
        p5.1 = p6.1.1 ∧ p5.2.2 = false ∧ p6.2.2.2 = false ∧
        MuInv S P p5.2.1 p6.1.2 p6.2.1 p6.2.2.1)
      (fun p5 => p5.2.2)
      (fun p6 => p6.2.2.2)
      ($ᵗ Bool >>= fun secb =>
        (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridStateFixed S
            × Bool) ProbComp) +
          pqxdhAuthForgeAllImpl true .g5 S P) A.1.run).run
          (AuthHybridStateFixed.empty S secb, false))
      ($ᵗ Bool >>= fun secb =>
        runMu P (runWithMuStep (stepAuthMuPrim S) A.1.run (AuthHybridStateFixed.empty S secb))
          ([], [], false)) :=
    RelProbDomZ.bind_same ($ᵗ Bool) (fun secb =>
      relProbDomZ_runWithMuStep P A.1.run
        (AuthHybridStateFixed.empty S secb) (AuthHybridStateFixed.empty S secb) [] []
        (muInv_empty S P secb))
  have hLe := RelProbDomZ.evalDist_le hDom (fun _ _ ⟨_, hFalse, _, _⟩ => hFalse)
  simp only [bind_assoc] at hLe
  exact ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top MeasureTheory.prob_le_one) hLe

theorem auth_hop_G3_8_split_g5_le_mu (S : Setup) (P : Primitives) (hWF : WellFormedPrimitivesδ P)
    (hLaw : ∀ p e, P.pow8 p = P.pow8 (P.x25519Base e) → p.length = 32) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    |(𝒟[authFixedExpG3_8 S P A.1] {true}).toReal -
     (𝒟[authSplitFixedExp .g3_8 .g5 true S P A.1] {true}).toReal| ≤
      AeadMuIntCtxt P (aeadMuIntReductionAuth S b A) :=
  (auth_hop_G3_8_split_g5_le_forgeAll S P hWF A.1).trans
    (authIntForgeAllExp_le_aeadMuIntCtxt S P hWF hLaw b A)

/-- Bounds the `boolBias` gap between `G3.8` and `split(.g3_8, .g5, true)` by twice the multi-key
    `INT-CTXT` advantage. -/
theorem auth_hop_G3_8_split_g5_boolBias_le_mu (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    |authFixedAdvG3_8 S P A.1 -
     (𝒟[authSplitFixedExp .g3_8 .g5 true S P A.1].boolBias).toReal| ≤
      2 * AeadMuIntCtxt P (aeadMuIntReductionAuth S b A) := by
  unfold authFixedAdvG3_8
  have hBias := abs_sub_boolBias_toReal_le_two_mul_abs_sub
    (authFixedExpG3_8 S P A.1) (authSplitFixedExp .g3_8 .g5 true S P A.1)
  have hHop :=
    auth_hop_G3_8_split_g5_le_mu S P hP.toWellFormedPrimitivesδ hP.pow8_base_len b A
  linarith

end SignalPqxdh.Security
