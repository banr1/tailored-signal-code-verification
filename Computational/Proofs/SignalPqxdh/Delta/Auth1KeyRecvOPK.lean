/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Delta.AuthDefs
public import Computational.Proofs.SignalPqxdh.Security.FgGapDh
public import Computational.Proofs.SignalPqxdh.Delta.Auth.RecvOPK
public import Computational.Proofs.SignalPqxdh.Delta.Auth1KeyAuthDefs
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthGapDhHopC2
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthGapDhHopC2b
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthGapDhHopC3b
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthGapDhHopC6b
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthGapDhHopC6c
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthGapDhHopC6c1
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthGapDhHopC6c2
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthGapDhHopC6c3
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthGapDhHopC6c4
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthGapDhHopC6c5
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthHopInterface
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrapBase
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyShallowSims
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyHybrid
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyGapDhIdSim

/-!
# One-key authentication: `.recvOPK` step coupling

Proves `authRecvOPKδ1Key` (`AuthRecvOPKδStmt1Key`), the one-key counterpart of
`Delta/Auth/RecvOPK.lean` over `pqxdhAuthImpl1KeyG`.
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal
open MeasureTheory
open OracleSpec OracleComp
open SignalPqxdh SignalPqxdh.Security
open Proofs.SignalPqxdh.Security

namespace Proofs.SignalPqxdh.Security.PqxdhDelta

private theorem ar1_hasBadAuthKemCorr_finishLatchedRecvOPK {S : Setup} (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry) (oEntry : OpkEntry)
    (usedTriples' : List (Nat × KeyId × KeyId × Bytes)) (msg : PreKeyMsg)
    (s : AuthAdvLatchedState S) (hstDec : AuthHybridState S)
    (res? : Option (DRKey × Bytes × Bytes × Bytes ×
      List (Bytes × DRKey) × List ((Bytes × Bytes) × (Bytes × Bytes)))) :
    hasBadAuthKemCorr P
      (finishLatchedRecvOPK P k j o kEntry bEntry oEntry usedTriples' msg s hstDec res?).2.hyb =
    hasBadAuthKemCorr P hstDec := by
  cases res? with
  | none => rfl
  | some r =>
    rcases r with ⟨dk, rk1, ck1_1, pt, roCache', rootRoCache'⟩
    unfold finishLatchedRecvOPK finishAuthHybridRecvOPK wrapAuthAdvLatchedRecv
      AuthAdvLatchedState.hyb
    dsimp only
    rcases findHonestPrincipal P hstDec.base.principals msg.hdr.ikAPk with
      _ | ⟨_, senderEntry⟩
    · rfl
    · dsimp only
      split_ifs <;> rfl

private theorem ar1_recv_subcaseA_roCache_find_eq_some {S : Setup} (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) {s35 s3 : AuthAdvLatchedState S}
    (hRc : AuthRoCacheCoupled P s35 s3) (hKS : ValidAuthKeyStores S P s3.hyb.base)
    {k : Fin S.N_id} {j : Fin S.N_recv} {kEntry : PrincipalEntry} {bEntry : SpkBundleEntry}
    {opkPk? dh4? : Option Bytes} {ss : Bytes}
    {rRec : _root_.SignalPqxdh.Security.RecvKemRecord} {hdr : HandshakeHdr}
    {s : IdealAuthSession S}
    (hNoCorr : hasBadAuthKemCorr P { s3.hyb with recvKemRecs := rRec :: s3.hyb.recvKemRecs } = false)
    (hRespV : ValidAuthRespHandshake S P
      { s3.hyb with recvKemRecs := rRec :: s3.hyb.recvKemRecs }
      k j kEntry bEntry opkPk? dh4? ss rRec hdr)
    (hMatch : s3.hyb.idealSessions.find?
      (matchIdealAuthHandshake P kEntry.ikAPk bEntry.spkPk opkPk? bEntry.pqspkPk hdr) = some s) :
    let secrets := recvHandshakeSecrets P kEntry bEntry dh4? ss hdr
    s3.hyb.base.roCache.find? (fun (inp, _) => inp == secrets) = some (secrets, s.drKey) := by
  intro secrets
  have hsMem : s ∈ s3.hyb.idealSessions := List.mem_of_find?_eq_some hMatch
  have hMatchB :
      matchIdealAuthHandshake P kEntry.ikAPk bEntry.spkPk opkPk? bEntry.pqspkPk hdr s = true :=
    List.find?_some hMatch
  rcases hRc.2.1 s hsMem with ⟨sessEntry, u, uEntry1, kemCoins, ss_s, initRec, hVi1, _, hFind1⟩
  have hSubDec : AuthHybridTraceSub s3.hyb
      { s3.hyb with recvKemRecs := rRec :: s3.hyb.recvKemRecs } :=
    ⟨⟨List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _,
      List.Sublist.refl _, List.Sublist.refl _⟩,
      List.Sublist.refl _, List.sublist_cons_self _ _, List.Sublist.refl _⟩
  rcases validIdealAuthSession_of_traceSub P hSubDec hVi1 with ⟨uEntry2, hSecEq, _, hVi2⟩
  have hSecretsEq := matchIdealAuthHandshake_imp_secrets_eqδ P hP
    { s3.hyb with recvKemRecs := rRec :: s3.hyb.recvKemRecs } hKS hNoCorr hVi2 hRespV hMatchB
  have hIdealSecEq : idealSessionSecrets P uEntry1 sessEntry.ekASk ss_s s = secrets := by
    change idealSessionSecrets P uEntry1 sessEntry.ekASk ss_s s =
      recvHandshakeSecrets P kEntry bEntry dh4? ss hdr
    rw [← hSecretsEq]; unfold idealSessionSecrets; rw [hSecEq]
  dsimp only at hFind1
  rwa [hIdealSecEq] at hFind1

private theorem ar1_hasWonAuth_false_of_parseAuthRecvOPKPre_some {S : Setup} (P : Primitives)
    {k : Fin S.N_id} {j : Fin S.N_recv} {o : Fin S.N_opk} {msg : PreKeyMsg}
    {st : AuthState S} {x} (hPre : parseAuthRecvOPKPre P k j o msg st = some x) :
    st.hasWonAuth = false := by
  unfold parseAuthRecvOPKPre at hPre
  cases h : st.hasWonAuth <;> simp_all

private theorem ar1_authRoCacheCoupled_of_or_won_false {S : Setup} (P : Primitives)
    {s35 s3 : AuthAdvLatchedState S}
    (h : AuthRoCacheCoupled P s35 s3 ∨
      (s35.hyb.base.hasWonAuth = true ∧ s3.hyb.base.hasWonAuth = true))
    (hF : s3.hyb.base.hasWonAuth = false) :
    AuthRoCacheCoupled P s35 s3 :=
  h.resolve_right (fun ⟨_, hW⟩ => by rw [hF] at hW; nomatch hW)

private theorem ar1_finishLatchedRecvOPK_snd_of_agree {S : Setup} (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry) (oEntry : OpkEntry)
    (usedTriples' : List (Nat × KeyId × KeyId × Bytes)) (msg : PreKeyMsg)
    {s35 s3 : AuthAdvLatchedState S} (hAg : AuthAdvLatchedAgreeOffRo s35 s3)
    (hstDec : AuthHybridState S) (dk : DRKey) (rk1 ck1_1 pt : Bytes)
    (rc35 rc3 : List (Bytes × DRKey))
    (rootRoCache' : List ((Bytes × Bytes) × (Bytes × Bytes))) :
    (finishLatchedRecvOPK P k j o kEntry bEntry oEntry usedTriples' msg
      s35 (withAuthHybRoCache s35.hyb.base.roCache hstDec)
      (some (dk, rk1, ck1_1, pt, rc35, rootRoCache'))).2 =
    withAuthAdvLatchedRoCache rc35
      (finishLatchedRecvOPK P k j o kEntry bEntry oEntry usedTriples' msg
        s3 hstDec (some (dk, rk1, ck1_1, pt, rc3, rootRoCache'))).2 := by
  conv_lhs => rw [hAg]
  exact congrArg Prod.snd (finishLatchedRecvOPK_withAuthAdvLatchedRoCache_some P k j o
    kEntry bEntry oEntry usedTriples' msg s35.adv.hyb.base.roCache rc35 rc3 s3 hstDec
    dk rk1 ck1_1 pt rootRoCache')

private theorem ar1_cutoff_latched_recvOPK_roCacheOrWon1Key {S : Setup} (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (maxRo : ℕ)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (msg : PreKeyMsg)
    (s35 s3 : AuthAdvLatchedState S) (hWin : AuthWinGuardedG3G3_5CoupledInv P s35 s3)
    (hAbF : isAuthG3Abort P s3.hyb = false)
    (hbF : badAuthFgAnyLatchedMono P maxRo s3.toFg = false)
    (hRoLen : s3.adv.advRoLog.length ≤ maxRo)
    (hRespLen : s3.adv.respRecs.length ≤ S.N_sess_tot)
    (hNoBadDec : ∀ kEntry bEntry oEntry usedTriples' ss,
      parseAuthRecvOPKPre P k j o msg s3.hyb.base =
        some (kEntry, bEntry, oEntry, usedTriples', ss) →
      let rRec : _root_.SignalPqxdh.Security.RecvKemRecord := {
        k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk,
        pqspkSk := bEntry.pqspkSk, kemCt := msg.hdr.kemCt, kemSs := ss }
      hasBadAuthKemCorr P { s3.hyb with recvKemRecs := rRec :: s3.hyb.recvKemRecs } = false) :
    RelProbUpToBad (fun y35 y3 => (y35.1 = y3.1 ∧ AuthRoCacheOrWon P y35.2 y3.2) ∨
        (isAuthG3Abort P y35.2.hyb = true ∧ isAuthG3Abort P y3.2.hyb = true))
      (fun y3 => badAuthFgAnyLatchedMono P maxRo y3.2.toFg)
      ((pqxdhAuthAdvLatchedStageImpl1Key .g3_5 S P (.recvOPK k j o msg)).run s35)
      ((pqxdhAuthAdvLatchedStageImpl1Key .g3 S P (.recvOPK k j o msg)).run s3) := by
  rcases hWin with ⟨hAg, hRunInv, hOrig, hRcOrWon⟩
  refine fgAuthStepCoupling_cutoff_latched_recvOPK1Key P hP maxRo (AuthRoCacheOrWon P)
    k j o msg s35 s3 ⟨hAg, hRcOrWon⟩ hAg hRunInv hAbF hbF ?_ ?_ ?_ ?_ ?_
  · intro _
    left
    have hWrapEq : (wrapAuthAdvLatchedRecv k j msg s35 (.noneResp, s35.hyb)).2 =
        withAuthAdvLatchedRoCache s35.adv.hyb.base.roCache
          (wrapAuthAdvLatchedRecv k j msg s3 (.noneResp, s3.hyb)).2 := by
      (conv_lhs => rw [hAg]); rfl
    rw [hWrapEq]
    rcases hRcOrWon with hRc | ⟨_, hWon3⟩
    · have hSub : AuthHybridTraceSub s3.hyb
          (wrapAuthAdvLatchedRecv k j msg s3 (.noneResp, s3.hyb)).2.hyb :=
        ⟨⟨List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _,
          List.Sublist.refl _, List.Sublist.refl _⟩,
          List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _⟩
      exact ⟨AuthAdvLatchedAgreeOffRo.of_withAuthAdvLatchedRoCache _ _,
        Or.inl (authRoCacheCoupled_of_traceSub_eq_roCache P hRc hSub rfl rfl
          (fun _ hx => hx) (fun _ hx => hx) (fun _ hx => List.mem_cons_of_mem _ hx))⟩
    · exact ⟨AuthAdvLatchedAgreeOffRo.of_withAuthAdvLatchedRoCache _ _, Or.inr ⟨hWon3, hWon3⟩⟩
  · intro kEntry bEntry oEntry usedTriples' ss hPre rRec hstDec _
    have hRc := ar1_authRoCacheCoupled_of_or_won_false P hRcOrWon
      (ar1_hasWonAuth_false_of_parseAuthRecvOPKPre_some P hPre)
    left
    have hFinEq : (finishLatchedRecvOPK P k j o kEntry bEntry oEntry usedTriples' msg
          s35 (withAuthHybRoCache s35.hyb.base.roCache hstDec) none).2 =
        withAuthAdvLatchedRoCache s35.adv.hyb.base.roCache
          (finishLatchedRecvOPK P k j o kEntry bEntry oEntry usedTriples' msg
            s3 hstDec none).2 := by
      conv_lhs => rw [hAg]
      exact congrArg Prod.snd (finishLatchedRecvOPK_withAuthAdvLatchedRoCache_none P k j o
        kEntry bEntry oEntry usedTriples' msg s35.adv.hyb.base.roCache s3 hstDec)
    rw [hFinEq]
    have hSub : AuthHybridTraceSub s3.hyb
        (finishLatchedRecvOPK P k j o kEntry bEntry oEntry usedTriples' msg s3 hstDec none).2.hyb :=
      ⟨⟨List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _,
        List.Sublist.refl _, List.Sublist.refl _⟩,
        List.Sublist.refl _, List.sublist_cons_self _ _, List.Sublist.refl _⟩
    exact ⟨AuthAdvLatchedAgreeOffRo.of_withAuthAdvLatchedRoCache _ _,
      Or.inl (authRoCacheCoupled_of_traceSub_eq_roCache P hRc hSub rfl rfl
        (fun _ hx => hx) (fun _ hx => hx) (fun _ hx => List.mem_cons_of_mem _ hx))⟩
  · intro kEntry bEntry oEntry usedTriples' ss s hPre rRec hstDec dh4 secrets _ hMatch
    have hRc := ar1_authRoCacheCoupled_of_or_won_false P hRcOrWon
      (ar1_hasWonAuth_false_of_parseAuthRecvOPKPre_some P hPre)
    have hRespV :=
      (parseAuthRecvOPKPre_some_props P k j o msg s3.hyb hPre).2.2.2.2.2.2.2.2.2.2.2.2.2.2
    have hNoCorr := hNoBadDec kEntry bEntry oEntry usedTriples' ss hPre
    refine ⟨ar1_recv_subcaseA_roCache_find_eq_some P hP hRc hRunInv.1.1 hNoCorr hRespV hMatch,
      fun rk1 ck1_1 pt rootRoCache' _ => Or.inl ?_⟩
    rw [ar1_finishLatchedRecvOPK_snd_of_agree P k j o kEntry bEntry oEntry usedTriples' msg
      hAg hstDec s.drKey rk1 ck1_1 pt s35.hyb.base.roCache s3.hyb.base.roCache rootRoCache']
    rcases finishLatchedRecvOPK_some_ext P k j o kEntry bEntry oEntry usedTriples' msg
        s3 rRec s.drKey rk1 ck1_1 pt s3.hyb.base.roCache rootRoCache' with
      ⟨hSub, hRoEq, hIdEq, hAdvEq, hUsedEq, hRespSub, _⟩
    exact ⟨AuthAdvLatchedAgreeOffRo.of_withAuthAdvLatchedRoCache _ _,
      Or.inl (authRoCacheCoupled_of_traceSub_eq_roCache P hRc hSub hRoEq hIdEq
        (fun _ hx => hAdvEq ▸ hx) (fun _ hx => hUsedEq ▸ hx)
        (fun _ hx => hRespSub.subset hx))⟩
  · intro kEntry bEntry oEntry usedTriples' ss hPre rRec hstDec dh4 secrets hAbDecF hMatchNone _
    have hRc := ar1_authRoCacheCoupled_of_or_won_false P hRcOrWon
      (ar1_hasWonAuth_false_of_parseAuthRecvOPKPre_some P hPre)
    have hRespV :=
      (parseAuthRecvOPKPre_some_props P k j o msg s3.hyb hPre).2.2.2.2.2.2.2.2.2.2.2.2.2.2
    rcases recv_subcaseB_roCache_cases P hP hRc hRunInv.1.1 hAbDecF hRespV hMatchNone with
      ⟨sec35, sec3, dk, hF35, hF3⟩ | ⟨hF35, hF3⟩
    · left
      refine ⟨sec35, sec3, dk, hF35, hF3, fun rk1 ck1_1 pt rootRoCache' _ => Or.inl ?_⟩
      rw [ar1_finishLatchedRecvOPK_snd_of_agree P k j o kEntry bEntry oEntry usedTriples' msg
        hAg hstDec dk rk1 ck1_1 pt s35.hyb.base.roCache s3.hyb.base.roCache rootRoCache']
      rcases finishLatchedRecvOPK_some_ext P k j o kEntry bEntry oEntry usedTriples' msg
          s3 rRec dk rk1 ck1_1 pt s3.hyb.base.roCache rootRoCache' with
        ⟨hSub, hRoEq, hIdEq, hAdvEq, hUsedEq, hRespSub, _⟩
      exact ⟨AuthAdvLatchedAgreeOffRo.of_withAuthAdvLatchedRoCache _ _,
        Or.inl (authRoCacheCoupled_of_traceSub_eq_roCache P hRc hSub hRoEq hIdEq
          (fun _ hx => hAdvEq ▸ hx) (fun _ hx => hUsedEq ▸ hx)
          (fun _ hx => hRespSub.subset hx))⟩
    · right
      refine ⟨hF35, hF3, fun dk _ rk1 ck1_1 pt rootRoCache' _ => Or.inl ?_⟩
      rw [ar1_finishLatchedRecvOPK_snd_of_agree P k j o kEntry bEntry oEntry usedTriples' msg hAg
        hstDec dk rk1 ck1_1 pt ((secrets, dk) :: s35.hyb.base.roCache)
        ((secrets, dk) :: s3.hyb.base.roCache) rootRoCache']
      rcases finishLatchedRecvOPK_some_ext P k j o kEntry bEntry oEntry usedTriples' msg
          s3 rRec dk rk1 ck1_1 pt ((secrets, dk) :: s3.hyb.base.roCache) rootRoCache' with
        ⟨hSub, hRoEq, hIdEq, hAdvEq, hUsedEq, hRespSub, _⟩
      have hNewResp := (authRespRoOrigin_finishLatchedRecvOPK P hP k j o msg s3 hPre dk
          rk1 ck1_1 pt ((secrets, dk) :: s3.hyb.base.roCache) rootRoCache').1
      exact ⟨AuthAdvLatchedAgreeOffRo.of_withAuthAdvLatchedRoCache _ _,
        Or.inl (authRoCacheCoupled_of_traceSub_cons_both_resp P hRc hF35 hF3 hSub hRoEq hIdEq
          (fun _ hx => hAdvEq ▸ hx) (fun _ hx => hUsedEq ▸ hx)
          (fun _ hx => hRespSub.subset hx) hNewResp)⟩
  · intro kEntry bEntry oEntry usedTriples' ss u_r senderEntry hPre rRec hstDec dh4 secrets
      hAbDecF hMatchNone hFp hHon
    rcases parseAuthRecvOPKPre_some_props P k j o msg s3.hyb hPre with
      ⟨hSpkId, hPqspkId, _, _, _, _, _, _, _, hReplayOk, _, _, _, _, hRespV⟩
    refine ⟨roCache_find_eq_none_of_recv_unmatched_honest P hP maxRo s3 hRunInv hOrig
      hAbF hAbDecF hbF hRoLen hRespLen hRespV hMatchNone hFp hHon hSpkId hPqspkId
      (congrArg Prod.fst hReplayOk),
      fun dk _ rk1 ck1_1 pt rootRoCache' _ hConsF => Or.inl ?_⟩
    rw [ar1_finishLatchedRecvOPK_snd_of_agree P k j o kEntry bEntry oEntry usedTriples' msg hAg
      hstDec dk rk1 ck1_1 pt s35.hyb.base.roCache
      ((secrets, dk) :: s3.hyb.base.roCache) rootRoCache']
    have hWon3 := finishLatchedRecvOPK_hasWonAuth_true_of_consume_false P k j o kEntry bEntry
      oEntry usedTriples' msg s3 hstDec dk rk1 ck1_1 pt
      ((secrets, dk) :: s3.hyb.base.roCache) rootRoCache' hFp hHon hConsF
    exact ⟨AuthAdvLatchedAgreeOffRo.of_withAuthAdvLatchedRoCache _ _, Or.inr ⟨hWon3, hWon3⟩⟩

private theorem ar1_cutoff_latched_recvOPK_winGuarded1Key {S : Setup} (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (maxRo : ℕ)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (msg : PreKeyMsg)
    (s35 s3 : AuthAdvLatchedState S) (hWin : AuthWinGuardedG3G3_5CoupledInv P s35 s3)
    (hAbF : isAuthG3Abort P s3.hyb = false)
    (hbF : badAuthFgAnyLatchedMono P maxRo s3.toFg = false)
    (hRoLen : s3.adv.advRoLog.length ≤ maxRo)
    (hRespLen : s3.adv.respRecs.length ≤ S.N_sess_tot)
    (hNoBadDec : ∀ kEntry bEntry oEntry usedTriples' ss,
      parseAuthRecvOPKPre P k j o msg s3.hyb.base =
        some (kEntry, bEntry, oEntry, usedTriples', ss) →
      let rRec : _root_.SignalPqxdh.Security.RecvKemRecord := {
        k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk,
        pqspkSk := bEntry.pqspkSk, kemCt := msg.hdr.kemCt, kemSs := ss }
      hasBadAuthKemCorr P { s3.hyb with recvKemRecs := rRec :: s3.hyb.recvKemRecs } = false) :
    RelProbUpToBad (fun y35 y3 =>
        (y35.1 = y3.1 ∧ AuthWinGuardedG3G3_5CoupledInv P y35.2 y3.2) ∨
        (isAuthG3Abort P y35.2.hyb = true ∧ isAuthG3Abort P y3.2.hyb = true))
      (fun y3 => badAuthFgAnyLatchedMono P maxRo y3.2.toFg)
      ((pqxdhAuthAdvLatchedStageImpl1Key .g3_5 S P (.recvOPK k j o msg)).run s35)
      ((pqxdhAuthAdvLatchedStageImpl1Key .g3 S P (.recvOPK k j o msg)).run s3) := by
  refine relProbUpToBad_of_imp_support_right ?_
  have hStep := ar1_cutoff_latched_recvOPK_roCacheOrWon1Key P hP maxRo
    k j o msg s35 s3 hWin hAbF hbF hRoLen hRespLen hNoBadDec
  refine RelProbUpToBad.mono hStep (fun y35 y3 hRel _ hy3 => ?_) (fun _ h => h)
  rcases hRel with ⟨hEq, hAg', hRcOrWon⟩ | hAb
  · exact Or.inl ⟨hEq, hAg',
      validAuthHybridRunInv_pqxdhAuthAdvLatchedStageImpl1Key .g3 P _ s3 hWin.2.1 hy3,
      authRecvOriginInv_of_recvOPK1Key P hP k j o msg s3 hWin.2.2.1 hy3, hRcOrWon⟩
  · exact Or.inr hAb

/-- The one-key `.recvOPK` step coupling on `AuthSendLatchedState` holds under
`CryptoWellFormedPrimitivesδ` with bad event `badSendδ`. -/
theorem authRecvOPKδ1Key (S : Setup) : AuthRecvOPKδStmt1Key S := by
  intro P hP maxRo k j o msg s35 s3 hInv hAbF hNotWon hbSendF hRoLen hRespLen
  have hbFgF : badAuthFgAnyLatchedMono P maxRo s3.toFg = false := by
    unfold badSendδ at hbSendF
    simp only [Bool.or_eq_false_iff] at hbSendF
    exact hbSendF.1.1
  by_cases hBadDec : ∃ kEntry bEntry oEntry usedTriples' ss,
      parseAuthRecvOPKPre P k j o msg s3.hyb.base =
        some (kEntry, bEntry, oEntry, usedTriples', ss) ∧
      let rRec : _root_.SignalPqxdh.Security.RecvKemRecord := {
        k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk,
        pqspkSk := bEntry.pqspkSk, kemCt := msg.hdr.kemCt, kemSs := ss }
      hasBadAuthKemCorr P { s3.hyb with recvKemRecs := rRec :: s3.hyb.recvKemRecs } = true
  · rcases hBadDec with ⟨kEntry, bEntry, oEntry, usedTriples', ss, hPre, hCorr⟩
    refine FgGapDh.RelProbUpToBad.bad6 _ _ (fun y3 hy3 => ?_)
    unfold pqxdhAuthSendLatchedStageImpl1Key at hy3
    dsimp only [StateT.run_mk] at hy3
    rw [pqxdhAuthAdvLatchedStageImpl_recvOPK_run_eq1Key, hPre] at hy3
    dsimp only at hy3
    rw [mem_support_bind_iff] at hy3
    rcases hy3 with ⟨p, hp, hy3⟩
    rw [mem_support_bind_iff] at hp
    rcases hp with ⟨res?, _, hp⟩
    rw [mem_support_pure_iff] at hp hy3
    subst hp; subst hy3
    unfold badSendδ
    apply Bool.or_eq_true_iff.mpr; right
    change hasBadAuthKemCorr P
      (finishLatchedRecvOPK P k j o kEntry bEntry oEntry usedTriples' msg
        s3.toAuthAdvLatchedState
        { s3.hyb with recvKemRecs := _ :: s3.hyb.recvKemRecs } res?).2.hyb = true
    rw [ar1_hasBadAuthKemCorr_finishLatchedRecvOPK]
    exact hCorr
  · have hNoBadDec : ∀ kEntry bEntry oEntry usedTriples' ss,
        parseAuthRecvOPKPre P k j o msg s3.hyb.base =
          some (kEntry, bEntry, oEntry, usedTriples', ss) →
        let rRec : _root_.SignalPqxdh.Security.RecvKemRecord := {
          k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk,
          pqspkSk := bEntry.pqspkSk, kemCt := msg.hdr.kemCt, kemSs := ss }
        hasBadAuthKemCorr P { s3.hyb with recvKemRecs := rRec :: s3.hyb.recvKemRecs } = false := by
      intro kEntry bEntry oEntry usedTriples' ss hPre
      apply Bool.eq_false_iff.mpr
      intro hT
      exact hBadDec ⟨kEntry, bEntry, oEntry, usedTriples', ss, hPre, hT⟩
    have hStep := ar1_cutoff_latched_recvOPK_winGuarded1Key P hP maxRo
      k j o msg s35.toAuthAdvLatchedState s3.toAuthAdvLatchedState hInv.1
      hAbF hbFgF hRoLen hRespLen hNoBadDec
    unfold pqxdhAuthSendLatchedStageImpl1Key; dsimp only [StateT.run_mk]
    refine ⟨fun w5 w6 hw5 hw6 hle => ?_, fun w6 w5 hw6 hle => ?_⟩
    · simp only [probExpect_bind, probExpect_pure]
      exact hStep.1 (fun x => w5 (x.1, { s35 with toAuthAdvLatchedState := x.2 }))
        (fun y => w6 (y.1, { s3 with toAuthAdvLatchedState := y.2 })) (fun x => hw5 _)
        (fun y hy => hw6 _ (by
          unfold badSendδ
          exact Bool.or_eq_true_iff.mpr (Or.inl (Bool.or_eq_true_iff.mpr (Or.inl hy)))))
        (fun x y hR => hle _ _ (hR.imp (fun ⟨hEq, hW⟩ => ⟨hEq, hW, hInv.2⟩) id))
    · simp only [probExpect_bind, probExpect_pure]
      exact hStep.2 (fun y => w6 (y.1, { s3 with toAuthAdvLatchedState := y.2 }))
        (fun x => w5 (x.1, { s35 with toAuthAdvLatchedState := x.2 }))
        (fun y hy => hw6 _ (by
          unfold badSendδ
          exact Bool.or_eq_true_iff.mpr (Or.inl (Bool.or_eq_true_iff.mpr (Or.inl hy)))))
        (fun x y hR => hle _ _ (hR.imp (fun ⟨hEq, hW⟩ => ⟨hEq, hW, hInv.2⟩) id))

end Proofs.SignalPqxdh.Security.PqxdhDelta
