/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.Notation

/-!
# Potential-based FS-AEAD query bounds

Proves `MakesAtMostQueries _ (min (2 * q) (q + 2))` and `MakesAtMostDecQueries _ q` for the
FS-AEAD reductions in `RedFS`.
-/

namespace Computational.Proofs.ReductionDsl.SM.RedFSPotOK

public section

set_option autoImplicit false

open OracleSpec OracleComp
open _root_.ReductionDsl
  (Sig Ty Ops Iface Env Expr Comp GameCodec CostedReduction handlerImpl isGameQuery)
open _root_.CryptoGames (Party)
open _root_.CryptoGames.CKA (CKAOp ckaSMQ ckaHdrCtTy)
open _root_.CryptoGames.PRFPRNG (prngSig prngOps fsaeadHeaderAdIface)
open _root_.CryptoGames.SM
  (Adversary MakesAtMostQueries posTy partyDec_partyEnc otherE pGet isSomeE)
open _root_.CryptoGames.SM.Engine
  (ConfigEC Policy modeCfgEC cGsTy
   esG esH esMk esSetG esSetH esSetAbort
   cGsSt cGsEpoch cGsB cGsMk cGsInitE mkPartiesE cRecPos
   vpMk vSendC vSendStep1C vRecvC vRecvStep1C
   commitEC transmitEC challEC deliverEC injectEC corrEC implEC
   eval_bind eval_bind_ret)
open _root_.CryptoGames.SM.Construction
  (Header PartyState Mode
   fsVpTy fsEsTy fsHsEmptyE extOfE hooksFSC initFSEStateC fsHdrDecWt
   redFSAuthProg redFSAuthProg_totalQueries
   redFSPrivProg redFSPrivProg_totalQueries
   redFSPrivCoinProg redFSPrivCoinProg_totalQueries
   redFsPolUni implUniEC
   redFSPrivUniProg redFSPrivUniCoinProg)
open Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks
  (fsVpInv fsEsInv fsHPot fsPot
   pGet_eval_st_fs fsVpInv_pGet fsVpInv_pSet
   cEpMgmtE_some_st_fs cAcceptE_st_fs cGsSetStP_st_fs cGsSetWin_st_fs
   cRecordE_st_fs cAfterCorrE_st_fs ite_fst_eq_fs
   fsHPot_extOfE extOfE_none_fst
   isQueryBoundP_min_fs fsIface_fwdU_zero
   PotOKInvFS potInvFS_ret potInvFS_ite potInvFS_caseOpt potInvFS_caseSum potInvFS_comp_const
   potOKInvFS_simulateQ_handlerImpl_step1
   rootFSC_potOKInv fsCommitC_potOKInv fsRevealC_potOKInv
   vSendC_hooksFSC_potOKInv vRecvC_hooksFSC_potOKInv)

section FsPotOK

variable
  {KC Γ CCoins T I KR RSt K SS RS M E : Type}
  {ckaInitA ckaInitB : KC → Γ} {ckaSend : Γ → CCoins → Γ × T × I} {ckaReceive : Γ → T → Γ × I}
  {prngInit : KR → RSt} {prngUp : RSt → I → RSt × K}
  {fsInitSender : K → SS} {fsInitReceiver : K → RS}
  {fsSend : SS → Header T → M → SS × E} {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
  {eqT : T → T → Bool} {eqI : I → I → Bool} {eqM : M → M → Bool} {eqE : E → E → Bool}
  {lam : I} {defaultE : E}
  {sampKR : ProbComp KR} {sampKC : ProbComp KC} {sampCCoins : ProbComp CCoins}
  {sampI : ProbComp I} {sampK : ProbComp K}

local notation "S" => prngSig KC Γ CCoins T I KR RSt K SS RS M E
local notation "hdrCtTy" => ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "vpTyFS" => fsVpTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "esTyFS" => fsEsTy KC Γ CCoins T I KR RSt K SS RS M E

local notation "OO" =>
  prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE

local notation "II" =>
  fsaeadHeaderAdIface KC Γ CCoins T I KR RSt K SS RS M E sampKR sampKC sampCCoins sampI sampK

local notation "P_fs" => isGameQuery (G := CryptoGames.FSAEAD.spec SS RS (Header T) M E)

theorem fsEsInv_of_st_eq {t : ℕ} {es : (esTyFS).denote} {st : ((vpTyFS).prod vpTyFS : Ty S).denote}
    (h : es.1.1 = st) (hSt : fsVpInv t st.1 ∧ fsVpInv t st.2) : fsEsInv t es := by
  unfold fsEsInv; rwa [h]

theorem commitEC_hooksFSC_potOKInv (L B Δcka : ℕ) (mo : Mode) (j : ℕ)
    {Γ' : List (Ty S)} (esE : Expr OO Γ' esTyFS)
    (sE : Expr OO Γ' (cGsTy vpTyFS)) (pE : Expr OO Γ' .bool)
    (oldE newE : Expr OO Γ' vpTyFS) (posE : Expr OO Γ' posTy)
    (ρ : Env Γ') (m : ℕ)
    (hEs : fsEsInv mo.tStar (esE.eval ρ))
    (hS : fsVpInv mo.tStar (sE.eval ρ).1.1 ∧ fsVpInv mo.tStar (sE.eval ρ).1.2)
    (hNew : fsVpInv mo.tStar (newE.eval ρ)) :
    PotOKInvFS P_fs
      (fun res => fsEsInv mo.tStar res.2 ∧
        ∀ s_acc, res.1 = some s_acc → fsVpInv mo.tStar s_acc.1.1 ∧ fsVpInv mo.tStar s_acc.1.2)
      (fun res => m + fsPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) res.2)
      ((commitEC (hooksFSC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) L B Δcka mo j) L esE sE pE oldE newE posE).eval ρ)
      (m + fsPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (esE.eval ρ)) := by
  unfold commitEC; dsimp only [hooksFSC]; rw [eval_bind_ret, eval_bind]
  have hFC := fsCommitC_potOKInv (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
    (esH (.fst (Expr.v0 (O := OO)))) (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))
    (.fst (.snd (.snd (.snd .v0)))) (.fst (.snd (.snd (.snd (.snd .v0)))))
    (.cons ((esE.pair (sE.pair (pE.pair (oldE.pair (newE.pair posE))))).eval ρ) ρ) m
  simp only [esH, Expr.eval, Expr.v0, Env.get_cons_zero] at hFC
  refine PotOKInvFS.bindPot hFC (fun cOut hcEq => ?_)
  refine potInvFS_caseOpt
    (fun _ => potInvFS_ret ⟨by simpa [fsEsInv, esMk, esG, Expr.eval, Expr.v1] using hEs,
        fun _ h => by simp [Expr.eval] at h⟩
      (by simp [fsPot, esMk, Expr.eval, Expr.v0]))
    (fun new' hSome => potInvFS_ret ?_ (by simp [fsPot, esMk, Expr.eval, Expr.v1]))
  simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hSome
  rw [hcEq] at hSome; injection hSome with hNewEq; subst hNewEq
  refine ⟨by simpa [fsEsInv, esMk, esG, Expr.eval, Expr.v2] using hEs, fun s_acc hs => ?_⟩
  injection hs with hs
  subst hs
  simp only [cGsSetStP_st_fs, cAcceptE_st_fs, Expr.eval, Expr.v0, Expr.v2,
    Env.get_cons_zero, Env.get_cons_succ]
  cases (pE.eval ρ : Bool) <;> simp [hS.1, hS.2, hNew]

theorem transmitEC_hooksFSC_potOKInv (L B Δcka qep : ℕ) (mo : Mode) (j : ℕ) (π : Policy)
    {Γ' : List (Ty S)} (esE : Expr OO Γ' esTyFS)
    (argE : Expr OO Γ' (.prod .bool (.prod (.base .msg) (.opt (.base .ccoins)))))
    (ρ : Env Γ') (m : ℕ) (hInv : fsEsInv mo.tStar (esE.eval ρ)) :
    PotOKInvFS P_fs (fun x => fsEsInv mo.tStar x.2)
      (fun x => m + fsPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) x.2)
      ((transmitEC (hooksFSC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) L B Δcka mo j) L (2 + Δcka) qep π esE argE).eval ρ)
      (1 + m + fsPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (esE.eval ρ)) := by
  unfold transmitEC; rw [eval_bind_ret]
  refine potInvFS_ite
    (fun _ => potInvFS_ret (by simpa [Expr.eval, Expr.v0] using hInv)
      (by simp only [Expr.eval, Expr.v0, Env.get_cons_zero]; omega))
    (fun _ => potInvFS_caseOpt
      (fun _ => potInvFS_ret (by simpa [Expr.eval, Expr.v0] using hInv)
        (by simp only [Expr.eval, Expr.v0, Env.get_cons_zero]; omega))
      (fun s1 hs1 => ?_))
  refine potInvFS_ite
    (fun _ => potInvFS_ret
      (by simpa [fsEsInv, esSetAbort, esMk, esG, Expr.eval, Expr.v0, Expr.v1] using hInv)
      (by simp [fsPot, esSetAbort, esMk, esH, Expr.eval, Expr.v0, Expr.v1]))
    (fun _ => ?_)
  rw [eval_bind]
  have hs1_st : s1.1 = (esE.eval ρ).1.1 := by
    have hs1' := cEpMgmtE_some_st_fs (2 + Δcka) qep (esG (.fst .v0))
      (.fst (.snd .v0)) (isSomeE (.snd (.snd (.snd .v0)))) (.cons (esE.eval ρ, argE.eval ρ) ρ) hs1
    simpa [esG, Expr.eval, Expr.v0, Env.get_cons_zero] using hs1'
  have hs1AB : fsVpInv mo.tStar s1.1.1 ∧ fsVpInv mo.tStar s1.1.2 := by rwa [hs1_st]
  have hSend := vSendC_hooksFSC_potOKInv (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
    L B Δcka mo j (esH (.fst (Expr.v1 (O := OO)))) .v0 (.fst (.snd .v1))
    (pGet (cGsSt .v0) (.fst (.snd .v1))) (.fst (.snd (.snd .v1))) .none (.snd (.snd (.snd .v1)))
    (.cons s1 (.cons (esE.eval ρ, argE.eval ρ) ρ)) m
    (by
      simp only [pGet_eval_st_fs, cGsSt, Expr.eval, Expr.v0, Expr.v1,
        Env.get_cons_zero, Env.get_cons_succ]
      exact fsVpInv_pGet mo.tStar s1.1 (argE.eval ρ).1 hs1AB)
  simp only [esH, Expr.eval, Expr.v1, Env.get_cons_zero, Env.get_cons_succ] at hSend
  refine PotOKInvFS.bindPot hSend (fun sendOut hSendInv => ?_)
  refine potInvFS_caseOpt
    (fun _ => potInvFS_ret (by simpa [fsEsInv, esMk, esG, Expr.eval, Expr.v2] using hInv)
      (by simp [fsPot, esMk, Expr.eval, Expr.v0]))
    (fun stCt hSome => ?_)
  simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hSome
  refine potInvFS_ret ?_ (by simp [fsPot, esMk, Expr.eval, Expr.v1])
  simp only [fsEsInv, esMk, cRecordE_st_fs,
    Expr.eval, Expr.v0, Expr.v2, Expr.v3, Env.get_cons_zero, Env.get_cons_succ]
  exact fsVpInv_pSet mo.tStar s1.1 (argE.eval ρ).1 stCt.1 hs1AB (hSendInv stCt hSome)

theorem challEC_hooksFSC_potOKInv (L B Δcka qep : ℕ) (mo : Mode) (j : ℕ)
    (cfg : ConfigEC OO) (π : Policy)
    {Γ' : List (Ty S)} (esE : Expr OO Γ' esTyFS)
    (argE : Expr OO Γ'
      (.prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .ccoins))))))
    (ρ : Env Γ') (m : ℕ) (hInv : fsEsInv mo.tStar (esE.eval ρ)) :
    PotOKInvFS P_fs (fun x => fsEsInv mo.tStar x.2)
      (fun x => m + fsPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) x.2)
      ((challEC (hooksFSC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) L B Δcka mo j) L (2 + Δcka) qep cfg π esE argE).eval ρ)
      (1 + m + fsPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (esE.eval ρ)) := by
  unfold challEC; rw [eval_bind_ret]
  refine potInvFS_ite
    (fun _ => potInvFS_ret (by simpa [Expr.eval, Expr.v0] using hInv)
      (by simp only [Expr.eval, Expr.v0, Env.get_cons_zero]; omega))
    (fun _ => potInvFS_caseOpt
      (fun _ => potInvFS_ret (by simpa [Expr.eval, Expr.v0] using hInv)
        (by simp only [Expr.eval, Expr.v0, Env.get_cons_zero]; omega))
      (fun s1 hs1 => ?_))
  refine potInvFS_ite
    (fun _ => potInvFS_ret (by simpa [Expr.eval, Expr.v1] using hInv)
      (by simp only [Expr.eval, Expr.v1, Env.get_cons_succ, Env.get_cons_zero]; omega))
    (fun _ => ?_)
  refine potInvFS_ite
    (fun _ => potInvFS_ret
      (by simpa [fsEsInv, esSetAbort, esMk, esG, Expr.eval, Expr.v0, Expr.v1] using hInv)
      (by simp [fsPot, esSetAbort, esMk, esH, Expr.eval, Expr.v0, Expr.v1]))
    (fun _ => ?_)
  rw [eval_bind]
  have hs1_st : s1.1 = (esE.eval ρ).1.1 := by
    have hs1' := cEpMgmtE_some_st_fs (2 + Δcka) qep (esG (.fst .v0))
      (.fst (.snd .v0)) (isSomeE (.snd (.snd (.snd (.snd .v0)))))
      (.cons (esE.eval ρ, argE.eval ρ) ρ) hs1
    simpa [esG, Expr.eval, Expr.v0, Env.get_cons_zero] using hs1'
  have hs1AB : fsVpInv mo.tStar s1.1.1 ∧ fsVpInv mo.tStar s1.1.2 := by rwa [hs1_st]
  have hSend := vSendC_hooksFSC_potOKInv (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
    L B Δcka mo j (esH (.fst (Expr.v1 (O := OO)))) .v0 (.fst (.snd .v1))
    (pGet (cGsSt .v0) (.fst (.snd .v1)))
    (cfg.challMsgE (pGet (cGsEpoch .v0) (.fst (.snd .v1))) (cGsB (esG (.fst .v1)))
      (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd .v1)))))
    (.some (.pair (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd .v1))))))
    (.snd (.snd (.snd (.snd .v1)))) (.cons s1 (.cons (esE.eval ρ, argE.eval ρ) ρ)) m
    (by
      simp only [pGet_eval_st_fs, cGsSt, Expr.eval, Expr.v0, Expr.v1,
        Env.get_cons_zero, Env.get_cons_succ]
      exact fsVpInv_pGet mo.tStar s1.1 (argE.eval ρ).1 hs1AB)
  simp only [esH, Expr.eval, Expr.v1, Env.get_cons_zero, Env.get_cons_succ] at hSend
  refine PotOKInvFS.bindPot hSend (fun sendOut hSendInv => ?_)
  refine potInvFS_caseOpt
    (fun _ => potInvFS_ret (by simpa [fsEsInv, esMk, esG, Expr.eval, Expr.v2] using hInv)
      (by simp [fsPot, esMk, Expr.eval, Expr.v0]))
    (fun stCt hSome => ?_)
  simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hSome
  refine potInvFS_ret ?_ (by simp [fsPot, esMk, Expr.eval, Expr.v1])
  simp only [fsEsInv, esMk, cRecordE_st_fs,
    Expr.eval, Expr.v0, Expr.v2, Expr.v3, Env.get_cons_zero, Env.get_cons_succ]
  exact fsVpInv_pSet mo.tStar s1.1 (argE.eval ρ).1 stCt.1 hs1AB (hSendInv stCt hSome)

theorem deliverEC_hooksFSC_potOKInv (L B Δcka maxSkip : ℕ) (mo : Mode) (j : ℕ) (cfg : ConfigEC OO)
    {Γ' : List (Ty S)} (esE : Expr OO Γ' esTyFS) (argE : Expr OO Γ' (.prod .bool hdrCtTy))
    (ρ : Env Γ') (m : ℕ) (hInv : fsEsInv mo.tStar (esE.eval ρ)) :
    PotOKInvFS P_fs (fun x => fsEsInv mo.tStar x.2)
      (fun x => m + fsPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) x.2)
      ((deliverEC (hooksFSC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) L B Δcka mo j) L maxSkip cfg esE argE).eval ρ)
      (1 + m + fsPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (esE.eval ρ)) := by
  unfold deliverEC; rw [eval_bind_ret]
  refine potInvFS_ite
    (fun _ => potInvFS_ret (by simpa [Expr.eval, Expr.v0] using hInv)
      (by simp only [Expr.eval, Expr.v0, Env.get_cons_zero]; omega))
    (fun _ => potInvFS_caseOpt
      (fun _ => potInvFS_ret (by simpa [Expr.eval, Expr.v0] using hInv)
        (by simp only [Expr.eval, Expr.v0, Env.get_cons_zero]; omega))
      (fun r1 _ => ?_))
  rw [eval_bind]
  have hRecv := vRecvC_hooksFSC_potOKInv (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
    L B Δcka mo j (esH (.fst (Expr.v1 (O := OO)))) (esG (.fst .v1))
    (.fst (.snd .v1)) (pGet (cGsSt (esG (.fst .v1))) (.fst (.snd .v1))) (.snd (.snd .v1)) (.some .v0)
    (.cons r1 (.cons (esE.eval ρ, argE.eval ρ) ρ)) m
    (by
      simp only [pGet_eval_st_fs, cGsSt, esG, Expr.eval, Expr.v1, Env.get_cons_zero, Env.get_cons_succ]
      exact fsVpInv_pGet mo.tStar (esE.eval ρ).1.1 (argE.eval ρ).1 hInv)
  simp only [esH, Expr.eval, Expr.v1, Env.get_cons_zero, Env.get_cons_succ] at hRecv
  refine PotOKInvFS.bindPot hRecv (fun recvOut hRecvInv => ?_)
  refine potInvFS_caseOpt
    (fun _ => potInvFS_ret (by simpa [fsEsInv, esMk, esG, Expr.eval, Expr.v2] using hInv)
      (by simp [fsPot, esMk, Expr.eval, Expr.v0]))
    (fun resIn hSome => ?_)
  simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hSome
  refine potInvFS_caseOpt
    (fun _ => potInvFS_ret ?_ (by simp [fsPot, esMk, Expr.eval, Expr.v1]))
    (fun tup hInSome => ?_)
  · refine fsEsInv_of_st_eq ?_ hInv
    simp only [esMk, Expr.eval]
    apply ite_fst_eq_fs
    · simp [cGsSetWin_st_fs, esG, Expr.eval, Expr.v3]
    · simp [esG, Expr.eval, Expr.v3]
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hInSome
    rw [eval_bind]
    have hCom := commitEC_hooksFSC_potOKInv (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
      L B Δcka mo j (esSetH (.fst (Expr.v4 (O := OO))) (.snd .v2))
      (esG (.fst .v4)) (.fst (.snd .v4)) (pGet (cGsSt (esG (.fst .v4))) (.fst (.snd .v4)))
      (.fst .v0) (cRecPos .v3)
      (.cons tup (.cons resIn (.cons recvOut (.cons r1 (.cons (esE.eval ρ, argE.eval ρ) ρ))))) m
      (by simpa [fsEsInv, esSetH, esMk, esG, Expr.eval, Expr.v0, Expr.v4] using hInv)
      (by simpa [fsEsInv, esG, Expr.eval, Expr.v4] using hInv)
      (by simpa [Expr.eval, Expr.v0, Env.get_cons_zero] using hRecvInv tup (by rw [hSome, hInSome]))
    simp only [fsPot, esSetH, esMk, Expr.eval, Expr.v0, Expr.v2, Env.get_cons_zero, Env.get_cons_succ] at hCom
    refine PotOKInvFS.bindPot hCom (fun comOut hComInv => ?_)
    refine potInvFS_caseOpt
      (fun _ => potInvFS_ret (by simpa [Expr.eval, Expr.v0] using hComInv.1)
        (by simp [fsPot, Expr.eval, Expr.v0]))
      (fun s_acc hs_acc => ?_)
    simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hs_acc
    refine potInvFS_ret ?_ (by simp [fsPot, esSetG, esMk, esH, Expr.eval, Expr.v0, Expr.v1])
    refine fsEsInv_of_st_eq ?_ (hComInv.2 s_acc hs_acc)
    simp only [esSetG, esMk, Expr.eval, Expr.v0, Env.get_cons_zero]
    apply ite_fst_eq_fs
    · simp [cGsSetWin_st_fs, Expr.eval]
    · rfl

theorem injectEC_hooksFSC_potOKInv (L B Δcka qep : ℕ) (mo : Mode) (j : ℕ) (cfg : ConfigEC OO)
    {Γ' : List (Ty S)} (esE : Expr OO Γ' esTyFS) (argE : Expr OO Γ' (.prod .bool hdrCtTy))
    (ρ : Env Γ') (m : ℕ) (hInv : fsEsInv mo.tStar (esE.eval ρ)) :
    PotOKInvFS P_fs (fun x => fsEsInv mo.tStar x.2)
      (fun x => m + fsPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) x.2)
      ((injectEC (hooksFSC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) L B Δcka mo j) L (2 + Δcka) qep cfg esE argE).eval ρ)
      (1 + m + fsPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (esE.eval ρ)) := by
  unfold injectEC; rw [eval_bind_ret]
  refine potInvFS_ite
    (fun _ => potInvFS_ret (by simpa [Expr.eval, Expr.v0] using hInv)
      (by simp only [Expr.eval, Expr.v0, Env.get_cons_zero]; omega))
    (fun _ => ?_)
  rw [eval_bind]
  have hRecv := vRecvC_hooksFSC_potOKInv (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
    L B Δcka mo j (esH (.fst (Expr.v0 (O := OO)))) (esG (.fst .v0))
    (.fst (.snd .v0)) (pGet (cGsSt (esG (.fst .v0))) (.fst (.snd .v0))) (.snd (.snd .v0)) .none
    (.cons (esE.eval ρ, argE.eval ρ) ρ) m
    (by
      simp only [pGet_eval_st_fs, cGsSt, esG, Expr.eval, Expr.v0, Env.get_cons_zero]
      exact fsVpInv_pGet mo.tStar (esE.eval ρ).1.1 (argE.eval ρ).1 hInv)
  simp only [esH, Expr.eval, Expr.v0, Env.get_cons_zero] at hRecv
  refine PotOKInvFS.bindPot hRecv (fun recvOut hRecvInv => ?_)
  refine potInvFS_caseOpt
    (fun _ => potInvFS_ret (by simpa [fsEsInv, esMk, esG, Expr.eval, Expr.v1] using hInv)
      (by simp [fsPot, esMk, Expr.eval, Expr.v0]))
    (fun resIn hSome => ?_)
  simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hSome
  refine potInvFS_caseOpt
    (fun _ => potInvFS_ret
      (by simpa [fsEsInv, esSetH, esMk, esG, Expr.eval, Expr.v0, Expr.v2] using hInv)
      (by simp [fsPot, esSetH, esMk, Expr.eval, Expr.v0, Expr.v1]))
    (fun tup hInSome => ?_)
  simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hInSome
  refine potInvFS_ite
    (fun _ => potInvFS_ret
      (by simpa [fsEsInv, esSetH, esMk, esG, Expr.eval, Expr.v0, Expr.v3] using hInv)
      (by simp [fsPot, esSetH, esMk, Expr.eval, Expr.v0, Expr.v2]))
    (fun _ => potInvFS_ite (fun _ => ?_) (fun _ => ?_))
  · rw [eval_bind]
    have hCom := commitEC_hooksFSC_potOKInv (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
      L B Δcka mo j (esSetH (.fst (Expr.v3 (O := OO))) (.snd .v2))
      (esG (.fst .v3)) (.fst (.snd .v3)) (pGet (cGsSt (esG (.fst .v3))) (.fst (.snd .v3)))
      (.fst .v0) (.pair (otherE (.fst (.snd .v3)))
        (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
      (.cons tup (.cons resIn (.cons recvOut (.cons (esE.eval ρ, argE.eval ρ) ρ)))) m
      (by simpa [fsEsInv, esSetH, esMk, esG, Expr.eval, Expr.v0, Expr.v3] using hInv)
      (by simpa [fsEsInv, esG, Expr.eval, Expr.v3] using hInv)
      (by simpa [Expr.eval, Expr.v0, Env.get_cons_zero] using hRecvInv tup (by rw [hSome, hInSome]))
    simp only [fsPot, esSetH, esMk, Expr.eval, Expr.v0, Expr.v2, Env.get_cons_zero, Env.get_cons_succ] at hCom
    refine PotOKInvFS.bindPot hCom (fun comOut hComInv => ?_)
    refine potInvFS_caseOpt
      (fun _ => potInvFS_ret (by simpa [Expr.eval, Expr.v0] using hComInv.1)
        (by simp [fsPot, Expr.eval, Expr.v0]))
      (fun s_acc hs_acc => ?_)
    simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hs_acc
    refine potInvFS_ret ?_ (by simp [fsPot, esSetG, esMk, esH, Expr.eval, Expr.v0, Expr.v1])
    simpa [fsEsInv, esSetG, esMk, Expr.eval, Expr.v0] using hComInv.2 s_acc hs_acc
  · refine potInvFS_ret ?_
      (by simp [fsPot, esSetG, esSetH, esMk, esH, Expr.eval, Expr.v0, Expr.v2])
    refine fsEsInv_of_st_eq ?_ hInv
    simp only [esSetG, esSetH, esMk, Expr.eval, Expr.v0, Env.get_cons_zero]
    split
    · simp [cGsSetWin_st_fs, esG, Expr.eval, Expr.v3]
    · simp [esG, Expr.eval, Expr.v3]

theorem corrEC_hooksFSC_potOKInv (L B Δcka : ℕ) (mo : Mode) (j : ℕ) (π : Policy)
    {Γ' : List (Ty S)} (esE : Expr OO Γ' esTyFS) (pE : Expr OO Γ' .bool)
    (ρ : Env Γ') (m : ℕ) (hInv : fsEsInv mo.tStar (esE.eval ρ)) :
    PotOKInvFS P_fs (fun x => fsEsInv mo.tStar x.2)
      (fun x => m + fsPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) x.2)
      ((corrEC (hooksFSC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) L B Δcka mo j) L π esE pE).eval ρ)
      (1 + m + fsPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (esE.eval ρ)) := by
  unfold corrEC; rw [eval_bind_ret]
  refine potInvFS_ite
    (fun _ => potInvFS_ret (by simpa [Expr.eval, Expr.v0] using hInv)
      (by simp only [Expr.eval, Expr.v0, Env.get_cons_zero]; omega))
    (fun _ => potInvFS_ite
      (fun _ => potInvFS_ret
        (by simpa [fsEsInv, esSetAbort, esMk, esG, Expr.eval, Expr.v0] using hInv)
        (by simp only [fsPot, esSetAbort, esMk, esH, Expr.eval, Expr.v0,
          Env.get_cons_zero]; omega))
      (fun _ => ?_))
  dsimp only [hooksFSC]; rw [eval_bind]
  have hRev := fsRevealC_potOKInv (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
    L mo (esH (.fst (Expr.v0 (O := OO)))) (esG (.fst .v0)) (.snd .v0)
    (pGet (cGsSt (esG (.fst .v0))) (.snd .v0))
    (.cons (esE.eval ρ, pE.eval ρ) ρ) m
    (by
      simp only [pGet_eval_st_fs, cGsSt, esG, Expr.eval, Expr.v0, Env.get_cons_zero]
      exact fsVpInv_pGet mo.tStar (esE.eval ρ).1.1 (pE.eval ρ) hInv)
  simp only [esH, Expr.eval, Expr.v0, Env.get_cons_zero] at hRev
  refine PotOKInvFS.bindPot hRev (fun _ _ => ?_)
  exact potInvFS_caseOpt
    (fun _ => potInvFS_ret (by simpa [fsEsInv, esMk, esG, Expr.eval, Expr.v1] using hInv)
      (by simp [fsPot, esMk, Expr.eval, Expr.v0]))
    (fun _ _ => potInvFS_ret
      (by simpa [fsEsInv, esMk, esG, cAfterCorrE_st_fs, Expr.eval, Expr.v2] using hInv)
      (by simp [fsPot, esMk, Expr.eval, Expr.v1]))

theorem implEC_hooksFSC_potOKInv (L B Δcka qep maxSkip : ℕ) (mo : Mode) (j : ℕ)
    (cfg : ConfigEC OO) (π : Policy)
    {Γ' : List (Ty S)} (esE : Expr OO Γ' esTyFS)
    (qE : Expr OO Γ' (ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E))
    (ρ : Env Γ') (m : ℕ) (hInv : fsEsInv mo.tStar (esE.eval ρ)) :
    PotOKInvFS P_fs (fun x => fsEsInv mo.tStar x.2)
      (fun x => m + fsPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) x.2)
      ((implEC (hooksFSC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) L B Δcka mo j) L (2 + Δcka) qep maxSkip cfg π esE qE).eval ρ)
      (1 + m + fsPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (esE.eval ρ)) := by
  unfold implEC; rw [eval_bind_ret]
  refine potInvFS_caseSum (fun _ _ => ?_) (fun _ _ => ?_)
  · refine potInvFS_caseSum (fun _ _ => ?_) (fun _ _ => ?_)
    · refine potInvFS_caseSum (fun _ _ => ?_) (fun _ _ => ?_)
      · refine potInvFS_caseSum (fun _ _ => ?_) (fun _ _ => ?_)
        · rw [eval_bind]; exact PotOKInvFS.bindPot
            (transmitEC_hooksFSC_potOKInv L B Δcka qep mo j π (.fst (Expr.v4 (O := OO))) .v0 _ m
              (by simpa [Expr.eval, Expr.v4] using hInv))
            (fun _ hx => potInvFS_ret (by simpa [Expr.eval, Expr.v0] using hx)
              (by simp [Expr.eval, Expr.v0]))
        · rw [eval_bind]; exact PotOKInvFS.bindPot
            (challEC_hooksFSC_potOKInv L B Δcka qep mo j cfg π (.fst (Expr.v4 (O := OO))) .v0 _ m
              (by simpa [Expr.eval, Expr.v4] using hInv))
            (fun _ hx => potInvFS_ret (by simpa [Expr.eval, Expr.v0] using hx)
              (by simp [Expr.eval, Expr.v0]))
      · rw [eval_bind]; exact PotOKInvFS.bindPot
          (deliverEC_hooksFSC_potOKInv L B Δcka maxSkip mo j cfg (.fst (Expr.v3 (O := OO))) .v0 _ m
            (by simpa [Expr.eval, Expr.v3] using hInv))
          (fun _ hx => potInvFS_ret (by simpa [Expr.eval, Expr.v0] using hx)
            (by simp [Expr.eval, Expr.v0]))
    · rw [eval_bind]; exact PotOKInvFS.bindPot
        (injectEC_hooksFSC_potOKInv L B Δcka qep mo j cfg (.fst (Expr.v2 (O := OO))) .v0 _ m
          (by simpa [Expr.eval, Expr.v2] using hInv))
        (fun _ hx => potInvFS_ret (by simpa [Expr.eval, Expr.v0] using hx)
          (by simp [Expr.eval, Expr.v0]))
  · rw [eval_bind]; exact PotOKInvFS.bindPot
      (corrEC_hooksFSC_potOKInv L B Δcka mo j π (.fst (Expr.v1 (O := OO))) .v0 _ m
        (by simpa [Expr.eval, Expr.v1] using hInv))
      (fun _ hx => potInvFS_ret (by simpa [Expr.eval, Expr.v0] using hx)
        (by simp [Expr.eval, Expr.v0]))

theorem implUniEC_potOKInv (L B Δcka qep maxSkip t : ℕ)
    {Γ' : List (Ty S)} (esE : Expr OO Γ' esTyFS)
    (qE : Expr OO Γ' (ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E))
    (ρ : Env Γ') (m : ℕ) (hInv : fsEsInv t (esE.eval ρ)) :
    PotOKInvFS P_fs (fun x => fsEsInv t x.2)
      (fun x => m + fsPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) x.2)
      ((implUniEC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) L B Δcka qep maxSkip t esE qE).eval ρ)
      (1 + m + fsPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (esE.eval ρ)) :=
  implEC_hooksFSC_potOKInv L B Δcka qep maxSkip ⟨false, none, t⟩ 0
    (modeCfgEC OO ⟨false, none, t⟩) (redFsPolUni Δcka t) esE qE ρ m hInv

theorem initFSEStateC_potOKInv (L : ℕ) (mo : Mode) (j : ℕ) {Γ' : List (Ty S)}
    (bE : Expr OO Γ' .bool) (ρ : Env Γ') (m : ℕ) :
    PotOKInvFS P_fs (fun es => fsEsInv mo.tStar es)
      (fun es => m + fsPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) es)
      ((initFSEStateC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L mo j bE).eval ρ) (m + 1) := by
  unfold initFSEStateC; rw [eval_bind_ret, eval_bind]
  refine PotOKInvFS.bindPot
    (potInvFS_comp_const _ _ (m + 1) (m + 1) (fun _ => Nat.le_refl _) (by simp [Comp.queries]))
    (fun kr _ => ?_)
  rw [eval_bind]
  refine PotOKInvFS.bindPot
    (potInvFS_comp_const _ _ (m + 1) (m + 1) (fun _ => Nat.le_refl _) (by simp [Comp.queries]))
    (fun kc _ => ?_)
  rw [eval_bind]
  set ρ₁ := Env.cons kc (Env.cons kr (Env.cons (bE.eval ρ) ρ))
  have hRoot := rootFSC_potOKInv (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
    L mo fsHsEmptyE (.nat 0) (Expr.op (O := OO) CKAOp.lamI .unit)
    (Expr.op (O := OO) CKAOp.prngInit .v1) ρ₁ m
  have hEmpPot : fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M)
      ((fsHsEmptyE (O' := OO)).eval ρ₁) = 1 := rfl
  rw [hEmpPot] at hRoot
  refine PotOKInvFS.bindPot hRoot (fun rootOut hRootInv => ?_)
  refine potInvFS_ret ?_ (by simp [fsPot, esMk, fsHPot_extOfE, Expr.eval, Expr.v0])
  simp only [fsEsInv, fsVpInv, esMk, cGsInitE, cGsMk, mkPartiesE, vpMk,
    Expr.eval, Expr.v0, Expr.v1, Expr.v3, Env.get_cons_zero, Env.get_cons_succ]
  refine ⟨⟨fun h => (by cases h), fun hvr => ?_⟩, ⟨fun hvS => ?_, fun h => (by cases h)⟩⟩
  · by_cases ht0 : mo.tStar = 0
    · rw [ht0]; simp [partyDec_partyEnc, Party.sendsIn]
    · simp [ht0] at hvr
  · simp only [Option.some.injEq] at hvS
    have hSidNe : rootOut.1.2.2 ≠ none := by
      intro hNone
      have hExtF := extOfE_none_fst L j (.snd (Expr.v0 (O := OO))) (.snd (.snd (.fst .v0)))
        (.cons rootOut ρ₁)
        (by simpa [Expr.eval, Expr.v0, Env.get_cons_zero] using hNone)
      dsimp only [Expr.v0] at hExtF
      simp [hExtF] at hvS
    have ht0 : 0 = mo.tStar := hRootInv hSidNe
    rw [← ht0]; simp [partyDec_partyEnc, Party.sendsIn]

/-- Generic `min (2 * q) (q + 2)` FS-AEAD query-bound combinator for any `CostedReduction` over
`prngOps` and `fsaeadHeaderAdIface`. -/
theorem costedReduction_makesAtMostQueries_fs
    {κ : Type} {G : OracleSpec.{0, 0} κ} {C : GameCodec S G}
    (R : CostedReduction OO II G C .unit .unit .bool .bool)
    (inv : R.σ.denote → Prop) (pot : R.σ.denote → ℕ) (q : ℕ)
    (A : OracleComp (unifSpec + G) Bool)
    (hA' : A.IsQueryBoundP (isGameQuery (G := G)) q)
    (hTot : R.totalQueries (fun _ => 1) (fun _ => 0) q = q * 2)
    (hInit : PotOKInvFS P_fs (fun as : (Ty.prod .unit R.σ : Ty S).denote => inv as.2)
      (fun as : (Ty.prod .unit R.σ : Ty S).denote => q + pot as.2)
      (R.init.eval (Env.cons (t := .unit) () .nil)) (q + 2))
    (hStep : ∀ (m : ℕ) qv sv, inv sv →
      PotOKInvFS P_fs (fun x => inv x.2) (fun x => m + pot x.2)
        (R.handle.eval (.cons sv (.cons qv .nil))) (1 + m + pot sv))
    (hFin : R.finish.queries (fun _ => 1) (fun _ => 0) = 0) :
    CryptoGames.FSAEAD.MakesAtMostQueries (R.eval (fun _ => A) ()) (min (2 * q) (q + 2)) := by
  have h2q : (R.eval (fun _ => A) ()).IsQueryBoundP P_fs (2 * q) := by
    have hSyn := CostedReduction.queryBound_eval R P_fs (fun _ => 1) (fun _ => 0)
      (fun _ _ _ => Nat.le_refl 1) fsIface_fwdU_zero (fun _ => A) q (fun _ => hA') ()
    rwa [hTot, Nat.mul_comm] at hSyn
  have hq2 : (R.eval (fun _ => A) ()).IsQueryBoundP P_fs (q + 2) := by
    unfold CostedReduction.eval CostedReduction.impl
    refine hInit.run _ ?_
    rintro ⟨_, s0⟩ hs0
    have hSim := potOKInvFS_simulateQ_handlerImpl_step1 inv pot fsIface_fwdU_zero
      R.handle hStep hA' s0 hs0
    refine hSim.run _ ?_
    rintro ⟨bOut, sOut⟩ _
    have hF := Comp.queryBound_eval P_fs (fun _ => 1) (fun _ => 0)
      (fun _ _ _ => Nat.le_refl 1) fsIface_fwdU_zero R.finish (.cons sOut (.cons bOut .nil))
    exact hF.mono (by simp [hFin])
  refine (isQueryBoundP_min_fs h2q hq2).of_imp (fun x hx => ?_)
  rcases x with _ | _ <;> simp_all [isGameQuery]

theorem costedReduction_makesAtMostDecQueries_fs
    {κ : Type} {G : OracleSpec.{0, 0} κ} {C : GameCodec S G}
    (R : CostedReduction OO II G C .unit .unit .bool .bool) (q : ℕ)
    (A : OracleComp (unifSpec + G) Bool)
    (hA' : A.IsQueryBoundP (isGameQuery (G := G)) q)
    (hTotDec : R.totalQueries fsHdrDecWt (fun _ => 0) q = q) :
    CryptoGames.FSAEAD.MakesAtMostDecQueries (R.eval (fun _ => A) ()) q := by
  have h := CostedReduction.queryBound_eval R
    (fun t => CryptoGames.FSAEAD.isDecQuery (SS := SS) (RS := RS) (AD := Header T) (Msg := M) (C := E) t = true)
    fsHdrDecWt (fun _ => 0)
    (fun g x hg => by cases g <;> simp_all [CryptoGames.FSAEAD.isDecQuery, fsHdrDecWt, fsaeadHeaderAdIface])
    (fun n => by
      change OracleComp.IsQueryBoundP
        (liftM (OracleSpec.query (spec := unifSpec + CryptoGames.FSAEAD.spec SS RS (Header T) M E) (.inl n))) _ 0
      rw [← bind_pure (liftM _), isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl (by simp [CryptoGames.FSAEAD.isDecQuery]), fun _ => by simp⟩)
    (fun _ => A) q (fun _ => hA') ()
  rwa [hTotDec] at h

@[local simp] private theorem implUniEC_queries (L B Δcka qep maxSkip t : ℕ)
    {Γ' : List (Ty S)} (es : Expr OO Γ' esTyFS)
    (q : Expr OO Γ' (ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E)) :
    (implUniEC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B Δcka qep maxSkip t es q).queries
      (fun _ => 1) (fun _ => 0) = 2 := by
  simp [implUniEC, implEC, transmitEC, challEC, deliverEC, injectEC, corrEC,
    vSendC, vSendStep1C, vRecvC, vRecvStep1C, commitEC, hooksFSC, Comp.queries]

@[local simp] private theorem implUniEC_decQueries (L B Δcka qep maxSkip t : ℕ)
    {Γ' : List (Ty S)} (es : Expr OO Γ' esTyFS)
    (q : Expr OO Γ' (ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E)) :
    (implUniEC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B Δcka qep maxSkip t es q).queries
      fsHdrDecWt (fun _ => 0) = 1 := by
  simp [implUniEC, implEC, transmitEC, challEC, deliverEC, injectEC, corrEC,
    vSendC, vSendStep1C, vRecvC, vRecvStep1C, commitEC, hooksFSC, Comp.queries]

theorem redFSAuthProg_makesAtMostQueries (L B Δcka qep maxSkip : ℕ) (j : ℕ)
    (tL : Option ℕ) (t q : ℕ)
    (A : _root_.CryptoGames.SM.Adversary (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
    (hA : MakesAtMostQueries A q) :
    CryptoGames.FSAEAD.MakesAtMostQueries
      ((redFSAuthProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
          (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK)
          L B Δcka qep maxSkip j tL t).eval (fun _ => A) ())
      (min (2 * q) (q + 2)) := by
  refine costedReduction_makesAtMostQueries_fs _ (fsEsInv t) fsPot q A
    (hA.of_imp (fun x hx => by cases x <;> [cases hx; rfl]))
    (redFSAuthProg_totalQueries L B Δcka qep maxSkip j tL t q) ?_ ?_
    (by simp [redFSAuthProg, Comp.queries])
  · dsimp only [redFSAuthProg]; rw [eval_bind]
    exact (PotOKInvFS.bindPot (initFSEStateC_potOKInv L ⟨true, tL, t⟩ j (.bool false) _ q)
      (fun _ hes => potInvFS_ret (by simpa [Expr.eval, Expr.v0] using hes)
        (by simp [Expr.eval, Expr.v0]))).mono (by omega)
  · intro m qv sv hsv
    exact implEC_hooksFSC_potOKInv L B Δcka qep maxSkip ⟨true, tL, t⟩ j
      (modeCfgEC OO ⟨true, tL, t⟩) (⟨true, tL, t⟩ : Mode).policy .v0 .v1
      (.cons sv (.cons qv .nil)) m hsv

theorem redFSPrivProg_makesAtMostQueries (L B Δcka qep maxSkip : ℕ)
    (tL : Option ℕ) (t q : ℕ)
    (A : _root_.CryptoGames.SM.Adversary (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
    (hA : MakesAtMostQueries A q) :
    CryptoGames.FSAEAD.MakesAtMostQueries
      ((redFSPrivProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
          (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK)
          L B Δcka qep maxSkip tL t).eval (fun _ => A) ())
      (min (2 * q) (q + 2)) := by
  refine costedReduction_makesAtMostQueries_fs _ (fsEsInv t) fsPot q A
    (hA.of_imp (fun x hx => by cases x <;> [cases hx; rfl]))
    (redFSPrivProg_totalQueries L B Δcka qep maxSkip tL t q) ?_ ?_
    (by simp [redFSPrivProg, Comp.queries])
  · dsimp only [redFSPrivProg]; rw [eval_bind]
    exact (PotOKInvFS.bindPot (initFSEStateC_potOKInv L ⟨false, tL, t⟩ 0 (.bool false) _ q)
      (fun _ hes => potInvFS_ret (by simpa [Expr.eval, Expr.v0] using hes)
        (by simp [Expr.eval, Expr.v0]))).mono (by omega)
  · intro m qv sv hsv
    exact implEC_hooksFSC_potOKInv L B Δcka qep maxSkip ⟨false, tL, t⟩ 0
      (modeCfgEC OO ⟨false, tL, t⟩) (⟨false, tL, t⟩ : Mode).policy .v0 .v1
      (.cons sv (.cons qv .nil)) m hsv

theorem redFSPrivCoinProg_makesAtMostQueries (L B Δcka qep maxSkip : ℕ)
    (tL : Option ℕ) (t q : ℕ)
    (A : _root_.CryptoGames.SM.Adversary (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
    (hA : MakesAtMostQueries A q) :
    CryptoGames.FSAEAD.MakesAtMostQueries
      ((redFSPrivCoinProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
          (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK)
          L B Δcka qep maxSkip tL t).eval (fun _ => A) ())
      (min (2 * q) (q + 2)) := by
  refine costedReduction_makesAtMostQueries_fs _ (fsEsInv t) fsPot q A
    (hA.of_imp (fun x hx => by cases x <;> [cases hx; rfl]))
    (redFSPrivCoinProg_totalQueries L B Δcka qep maxSkip tL t q) ?_ ?_
    (by simp [redFSPrivCoinProg, Comp.queries])
  · dsimp only [redFSPrivCoinProg]; rw [eval_bind]
    exact (PotOKInvFS.bindPot (initFSEStateC_potOKInv L ⟨false, tL, t⟩ 0 (.bool false) _ q)
      (fun _ hes => potInvFS_ret (by simpa [Expr.eval, Expr.v0] using hes)
        (by simp [Expr.eval, Expr.v0]))).mono (by omega)
  · intro m qv sv hsv
    exact implEC_hooksFSC_potOKInv L B Δcka qep maxSkip ⟨false, tL, t⟩ 0
      (modeCfgEC OO ⟨false, tL, t⟩) (⟨false, tL, t⟩ : Mode).policy .v0 .v1
      (.cons sv (.cons qv .nil)) m hsv

theorem redFSPrivUniProg_makesAtMostQueries (L B Δcka qep maxSkip t q : ℕ)
    (A : _root_.CryptoGames.SM.Adversary (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
    (hA : MakesAtMostQueries A q) :
    CryptoGames.FSAEAD.MakesAtMostQueries
      ((redFSPrivUniProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
          (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK)
          L B Δcka qep maxSkip t).eval (fun _ => A) ())
      (min (2 * q) (q + 2)) := by
  refine costedReduction_makesAtMostQueries_fs _ (fsEsInv t) fsPot q A
    (hA.of_imp (fun x hx => by cases x <;> [cases hx; rfl]))
    (by simp [CostedReduction.totalQueries, redFSPrivUniProg, Comp.queries]) ?_ ?_
    (by simp [redFSPrivUniProg, Comp.queries])
  · dsimp only [redFSPrivUniProg]; rw [eval_bind]
    exact (PotOKInvFS.bindPot (initFSEStateC_potOKInv L ⟨false, none, t⟩ 0 (.bool false) _ q)
      (fun _ hes => potInvFS_ret (by simpa [Expr.eval, Expr.v0] using hes)
        (by simp [Expr.eval, Expr.v0]))).mono (by omega)
  · intro m qv sv hsv
    exact implUniEC_potOKInv L B Δcka qep maxSkip t .v0 .v1 (.cons sv (.cons qv .nil)) m hsv

theorem redFSPrivUniCoinProg_makesAtMostQueries (L B Δcka qep maxSkip t q : ℕ)
    (A : _root_.CryptoGames.SM.Adversary (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
    (hA : MakesAtMostQueries A q) :
    CryptoGames.FSAEAD.MakesAtMostQueries
      ((redFSPrivUniCoinProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
          (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK)
          L B Δcka qep maxSkip t).eval (fun _ => A) ())
      (min (2 * q) (q + 2)) := by
  refine costedReduction_makesAtMostQueries_fs _ (fsEsInv t) fsPot q A
    (hA.of_imp (fun x hx => by cases x <;> [cases hx; rfl]))
    (by simp [CostedReduction.totalQueries, redFSPrivUniCoinProg, Comp.queries]) ?_ ?_
    (by simp [redFSPrivUniCoinProg, Comp.queries])
  · dsimp only [redFSPrivUniCoinProg]; rw [eval_bind]
    exact (PotOKInvFS.bindPot (initFSEStateC_potOKInv L ⟨false, none, t⟩ 0 (.bool false) _ q)
      (fun _ hes => potInvFS_ret (by simpa [Expr.eval, Expr.v0] using hes)
        (by simp [Expr.eval, Expr.v0]))).mono (by omega)
  · intro m qv sv hsv
    exact implUniEC_potOKInv L B Δcka qep maxSkip t .v0 .v1 (.cons sv (.cons qv .nil)) m hsv

theorem redFSAuthProg_makesAtMostDecQueries (L B Δcka qep maxSkip : ℕ) (j : ℕ)
    (tL : Option ℕ) (t q : ℕ)
    (A : _root_.CryptoGames.SM.Adversary (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
    (hA : MakesAtMostQueries A q) :
    CryptoGames.FSAEAD.MakesAtMostDecQueries
      ((redFSAuthProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
          (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK)
          L B Δcka qep maxSkip j tL t).eval (fun _ => A) ())
      q :=
  costedReduction_makesAtMostDecQueries_fs _ q A
    (hA.of_imp (fun x hx => by cases x <;> [cases hx; rfl]))
    (by simp [CostedReduction.totalQueries, redFSAuthProg, Comp.queries])

theorem redFSPrivProg_makesAtMostDecQueries (L B Δcka qep maxSkip : ℕ)
    (tL : Option ℕ) (t q : ℕ)
    (A : _root_.CryptoGames.SM.Adversary (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
    (hA : MakesAtMostQueries A q) :
    CryptoGames.FSAEAD.MakesAtMostDecQueries
      ((redFSPrivProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
          (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK)
          L B Δcka qep maxSkip tL t).eval (fun _ => A) ())
      q :=
  costedReduction_makesAtMostDecQueries_fs _ q A
    (hA.of_imp (fun x hx => by cases x <;> [cases hx; rfl]))
    (by simp [CostedReduction.totalQueries, redFSPrivProg, Comp.queries])

theorem redFSPrivCoinProg_makesAtMostDecQueries (L B Δcka qep maxSkip : ℕ)
    (tL : Option ℕ) (t q : ℕ)
    (A : _root_.CryptoGames.SM.Adversary (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
    (hA : MakesAtMostQueries A q) :
    CryptoGames.FSAEAD.MakesAtMostDecQueries
      ((redFSPrivCoinProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
          (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK)
          L B Δcka qep maxSkip tL t).eval (fun _ => A) ())
      q :=
  costedReduction_makesAtMostDecQueries_fs _ q A
    (hA.of_imp (fun x hx => by cases x <;> [cases hx; rfl]))
    (by simp [CostedReduction.totalQueries, redFSPrivCoinProg, Comp.queries])

theorem redFSPrivUniProg_makesAtMostDecQueries (L B Δcka qep maxSkip t q : ℕ)
    (A : _root_.CryptoGames.SM.Adversary (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
    (hA : MakesAtMostQueries A q) :
    CryptoGames.FSAEAD.MakesAtMostDecQueries
      ((redFSPrivUniProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
          (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK)
          L B Δcka qep maxSkip t).eval (fun _ => A) ())
      q :=
  costedReduction_makesAtMostDecQueries_fs _ q A
    (hA.of_imp (fun x hx => by cases x <;> [cases hx; rfl]))
    (by simp [CostedReduction.totalQueries, redFSPrivUniProg, Comp.queries])

theorem redFSPrivUniCoinProg_makesAtMostDecQueries (L B Δcka qep maxSkip t q : ℕ)
    (A : _root_.CryptoGames.SM.Adversary (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
    (hA : MakesAtMostQueries A q) :
    CryptoGames.FSAEAD.MakesAtMostDecQueries
      ((redFSPrivUniCoinProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
          (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK)
          L B Δcka qep maxSkip t).eval (fun _ => A) ())
      q :=
  costedReduction_makesAtMostDecQueries_fs _ q A
    (hA.of_imp (fun x hx => by cases x <;> [cases hx; rfl]))
    (by simp [CostedReduction.totalQueries, redFSPrivUniCoinProg, Comp.queries])

end FsPotOK

end

end Computational.Proofs.ReductionDsl.SM.RedFSPotOK
