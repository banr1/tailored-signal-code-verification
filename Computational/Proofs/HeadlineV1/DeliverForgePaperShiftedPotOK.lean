/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedReds -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.Bundles -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.SM.RedPRNGPotOK
import Computational.Proofs.SessionCostedFig8.BundlesEval
import Computational.Proofs.SessionCostedFig8.QuerySubsumes

/-!
# Shifted Paper PRF-PRNG Potential Query Bounds

Proves `min (2 + 2 * q) (q + 3)` query bounds for the shifted paper `DeliverForge` PRF-PRNG
reductions and lifts `MakesAtMostQueries` through `compilePrngDFAtomic` and `compileFsDFAtomic`.
-/

namespace Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedPotOK

public section

set_option autoImplicit false

open OracleSpec OracleComp
open _root_.ReductionDsl
  (Sig Ty Ops Iface Env Expr Comp GameCodec CostedReduction handlerImpl isGameQuery prngTargetIface)
open _root_.Computational.Proofs.ReductionDsl.MacroLift
  (toVal guardRed dummyRed)
open _root_.Computational.Proofs.ReductionDsl.SM.RedPRNGPotOK
  (prngVpReady prngPot prngOtherPot pGet_eval_st_prng prngOtherPot_add_pGet cLeakE_st_prng
   cGsSetWin_st_prng prngIface_fwdU_zero PotOKSPrng potSPrng_ret potSPrng_ite potSPrng_caseOpt
   potSPrng_caseSum ite_fst_eq_prng prngPot_mk_eq potSPrng_comp_const hooksPRNGC_spec
   prngVRecvPost vRecvC_potOKS prngCommitECPost commitEC_potOKS transmitEC_potOKS challEC_potOKS
   deliverEC_potOKS injectEC_potOKS initPRNGEStateC_potOKS
   costedReduction_makesAtMostQueries_prng)
open _root_.Computational.Proofs.SessionCostedFig8.QuerySubsumes
  (QuerySubsumes)
open _root_.Computational.Proofs.SessionCostedFig8.Bundles
  (prngPureAuxBundle fSortCKA toDenCKA querySubsumes_liftP_of_support_subset
   fig8CkaOpsShallow compilePrngDFAtomic compileFsDFAtomic
   ckaDFToFig8Adapters fig8SplitIn_eval ckaOpMacro_eval prngPureAuxBundle_query_eval
   fig8AdaptQDF_eval_cka fig8AdaptRDF_eval_cka)
open _root_.Computational.Proofs.SessionCostedFig8.BundlesEval
  (compileFsDFAtomic_querySubsumes)
open _root_.CryptoGames (Party)
open _root_.CryptoGames.CKA (CKASamp ckaSMQ ckaSMQDF ckaHdrCtTy)
open _root_.CryptoGames.PRFPRNG (prngSig prngOps prngIface prngSMCodecDF)
open _root_.CryptoGames.SM (otherE pGet orE letE_eval)
open _root_.CryptoGames.SM.Engine
  (ConfigEC Policy modeCfgEC cGsTy esG esH esAbort esMk esSetG esSetH esSetAbort
   cGsSt cGsMk cGsSetWin cAfterCorrShiftedE
   deliverForgeEC injectECB1 deliverForgeECB1 injectECGen deliverForgeECGen
   corrECShiftedPaper implECShiftedPaperGen implECDFShiftedPaperGen
   eval_bind eval_bind_ret)
open _root_.CryptoGames.SM.Construction
  (Header PartyState Mode prngEsTy prngRevealC_queries hooksPRNGC
   redPRNGAuthDFShiftedPaperGenProg redPRNGAuthDFShiftedPaperProg
   redPRNGAuthDFShiftedDir2PaperProg)
open _root_.CryptoGames.SM.Construction.DeliverForge
  (SchemeAdversaryDF MakesAtMostQueriesDF)

section ShiftedPrngPotOK

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
local notation "OO" =>
  prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE
local notation "II" =>
  prngIface KC Γ CCoins T I KR RSt K SS RS M E sampKR sampKC sampCCoins sampI sampK
local notation "P_prng_sh" => isGameQuery (G := _root_.CryptoGames.PRFPRNG.spec RSt I K)

private theorem cAfterCorrShiftedE_st_prng {O' : Ops S} {vpT : Ty S} {Γ' : List (Ty S)}
    (L l : ℕ) (s : Expr O' Γ' (cGsTy vpT)) (p : Expr O' Γ' .bool) (ρ : Env Γ') :
    ((cAfterCorrShiftedE L l s p).eval ρ).1 = (s.eval ρ).1 := by
  simp [cAfterCorrShiftedE, cGsMk, cGsSt, cLeakE_st_prng, Expr.eval, Expr.v0]

private theorem deliverForgeEC_hooksPRNGC_potOKS_shifted (L B Δ qep : ℕ) (mo : Mode)
    (cfg : ConfigEC OO)
    {Γ' : List (Ty S)} (esE : Expr OO Γ' prngEsTy)
    (argE : Expr OO Γ' (.prod .bool (.prod hdrCtTy hdrCtTy)))
    (ρ : Env Γ') (m : ℕ) :
    PotOKSPrng P_prng_sh (fun x => m + prngPot mo x.2)
      ((deliverForgeEC (hooksPRNGC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) B mo) L Δ qep cfg esE argE).eval ρ)
      (1 + m + prngPot mo (esE.eval ρ)) := by
  have hhk := hooksPRNGC_spec (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B mo
  unfold deliverForgeEC
  rw [eval_bind_ret]
  refine potSPrng_ite (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0])) (fun hNotRef => ?_)
  have hab : (esE.eval ρ).2.2 = false := by
    simp only [orE, esAbort, Expr.eval, Expr.v0, Env.get_cons_zero] at hNotRef
    cases h : (esE.eval ρ).2.2 <;> simp_all
  refine potSPrng_caseOpt (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0])) (fun r1 _ => ?_)
  refine potSPrng_ite (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v1])) (fun _ => ?_)
  rw [eval_bind]
  set m_other := prngOtherPot mo (esE.eval ρ).1.1 (argE.eval ρ).1
  have hRecv := vRecvC_potOKS hhk (esH (.fst (Expr.v1 (O := OO)))) (esG (.fst .v1))
    (.fst (.snd .v1)) (pGet (cGsSt (esG (.fst .v1))) (.fst (.snd .v1))) (.snd (.snd (.snd .v1))) .none
    (.cons r1 (.cons (esE.eval ρ, argE.eval ρ) ρ)) m m_other
  simp only [pGet_eval_st_prng, cGsSt, esG, Expr.eval, Expr.v1,
    Env.get_cons_zero, Env.get_cons_succ] at hRecv
  change PotOKSPrng P_prng_sh
      (prngVRecvPost mo m m_other
        (if ((argE.eval ρ).1 : Bool) then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1))
      _ _ at hRecv
  have hSum : m_other +
      prngVpReady mo (if (argE.eval ρ).1 then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1) =
      prngPot mo (esE.eval ρ) := by
    rw [prngOtherPot_add_pGet]
    simp [prngPot, hab]
  rw [show 1 + m + prngPot mo (esE.eval ρ) =
      1 + m + m_other +
        prngVpReady mo (if (argE.eval ρ).1 then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1)
      by omega]
  refine PotOKSPrng.bindPot hRecv (fun recvOut => ?_)
  refine potSPrng_caseOpt (fun hNone => ?_) (fun resInner hSome => ?_)
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hNone
    exact potSPrng_ret (by simp [prngVRecvPost, hNone, prngPot, esMk, Expr.eval])
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hSome
    refine potSPrng_caseOpt (fun hInNone => ?_) (fun tup hInSome => ?_)
    · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hInNone
      refine potSPrng_ret ?_
      simp only [prngVRecvPost, hSome, hInNone, prngPot, esSetH, letE_eval, esMk, esAbort, esG,
        Expr.eval, Expr.v0, Expr.v1, Expr.v3, Env.get_cons_zero, Env.get_cons_succ, hab,
        Bool.false_eq_true, ↓reduceIte]
      have hEqSum : prngVpReady mo (esE.eval ρ).1.1.1 + prngVpReady mo (esE.eval ρ).1.1.2 =
          m_other + prngVpReady mo
            (if (argE.eval ρ).1 then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1) := by
        simpa [prngPot, hab] using hSum.symm
      omega
    · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hInSome
      refine potSPrng_ite (fun _ => ?_) (fun _ => ?_)
      · refine potSPrng_ret ?_
        simp only [prngVRecvPost, hSome, hInSome, prngPot, esSetH, letE_eval, esMk, esAbort, esG,
          Expr.eval, Expr.v0, Expr.v2, Expr.v4, Env.get_cons_zero, Env.get_cons_succ, hab,
          Bool.false_eq_true, ↓reduceIte]
        have hEqSum : prngVpReady mo (esE.eval ρ).1.1.1 + prngVpReady mo (esE.eval ρ).1.1.2 =
            m_other + prngVpReady mo
              (if (argE.eval ρ).1 then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1) := by
          simpa [prngPot, hab] using hSum.symm
        omega
      · refine potSPrng_ite (fun _ => ?_) (fun _ => ?_)
        · rw [eval_bind]
          have hCom := commitEC_potOKS hhk L (esSetH (.fst (Expr.v4 (O := OO))) (.snd .v2))
            (esG (.fst .v4)) (.fst (.snd .v4))
            (pGet (cGsSt (esG (.fst .v4))) (.fst (.snd .v4)))
            (.fst .v0) (.pair (otherE (.fst (.snd .v4)))
              (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
            (.cons tup (.cons resInner (.cons recvOut
              (.cons r1 (.cons (esE.eval ρ, argE.eval ρ) ρ))))) m
            (by simp [esSetH, letE_eval, esMk, esAbort, Expr.eval, Expr.v0, Expr.v4, hab])
          simp only [esG, Expr.eval, Expr.v0, Expr.v4,
            Env.get_cons_zero, Env.get_cons_succ] at hCom
          have hPre :
              m + prngOtherPot mo (esE.eval ρ).1.1 (argE.eval ρ).1 + prngVpReady mo tup.1 ≤
                prngVRecvPost mo m m_other
                  (if (argE.eval ρ).1 then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1)
                  recvOut := by
            simp [prngVRecvPost, hSome, hInSome, m_other]
          refine ⟨fun {_} k hk => (PotOKSPrng.bindPot hCom (fun comOut => ?_)).run k hk |>.mono hPre⟩
          refine potSPrng_caseOpt (fun hCNone => ?_) (fun _ hCSome => ?_)
          · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hCNone
            exact potSPrng_ret (by simp [prngCommitECPost, hCNone, Expr.eval, Expr.v0])
          · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hCSome
            exact potSPrng_ret (by
              simp [prngCommitECPost, hCSome, prngPot, esSetG, letE_eval, esMk, esH, esAbort,
                Expr.eval, Expr.v0, Expr.v1])
        · refine potSPrng_ret ?_
          simp only [prngVRecvPost, hSome, hInSome, esSetG, esSetH, letE_eval, esMk, esAbort, esG,
            Expr.eval, Expr.v0, Expr.v2, Expr.v4, Env.get_cons_zero, Env.get_cons_succ, hab]
          refine Nat.le_trans
            (Nat.add_le_add_left (Nat.le_of_eq
              (prngPot_mk_eq mo (g2 := (esE.eval ρ).1) (h2 := (esE.eval ρ).2.1)
                (ite_fst_eq_prng (by rw [cGsSetWin_st_prng]; rfl) rfl))) m) ?_
          simp only [prngPot, Bool.false_eq_true, ↓reduceIte]
          have hEqSum : prngVpReady mo (esE.eval ρ).1.1.1 + prngVpReady mo (esE.eval ρ).1.1.2 =
              m_other + prngVpReady mo
                (if (argE.eval ρ).1 then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1) := by
            simpa [prngPot, hab] using hSum.symm
          omega

private theorem injectECB1_hooksPRNGC_potOKS (L B qep tStar : ℕ) (mo : Mode)
    (cfg : ConfigEC OO)
    {Γ' : List (Ty S)} (esE : Expr OO Γ' prngEsTy)
    (argE : Expr OO Γ' (.prod .bool hdrCtTy))
    (ρ : Env Γ') (m : ℕ) :
    PotOKSPrng P_prng_sh (fun x => m + prngPot mo x.2)
      ((injectECB1 (hooksPRNGC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) B mo) L qep tStar cfg esE argE).eval ρ)
      (1 + m + prngPot mo (esE.eval ρ)) := by
  have hhk := hooksPRNGC_spec (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B mo
  unfold injectECB1
  rw [eval_bind_ret]
  refine potSPrng_ite (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0])) (fun hNotRef => ?_)
  have hab : (esE.eval ρ).2.2 = false := by
    simp only [orE, esAbort, Expr.eval, Expr.v0, Env.get_cons_zero] at hNotRef
    cases h : (esE.eval ρ).2.2 <;> simp_all
  rw [eval_bind]
  set m_other := prngOtherPot mo (esE.eval ρ).1.1 (argE.eval ρ).1
  have hRecv := vRecvC_potOKS hhk (esH (.fst (Expr.v0 (O := OO)))) (esG (.fst .v0))
    (.fst (.snd .v0)) (pGet (cGsSt (esG (.fst .v0))) (.fst (.snd .v0))) (.snd (.snd .v0)) .none
    (.cons (esE.eval ρ, argE.eval ρ) ρ) m m_other
  simp only [pGet_eval_st_prng, cGsSt, esG, Expr.eval, Expr.v0, Env.get_cons_zero] at hRecv
  change PotOKSPrng P_prng_sh
      (prngVRecvPost mo m m_other
        (if ((argE.eval ρ).1 : Bool) then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1))
      _ _ at hRecv
  have hSum : m_other +
      prngVpReady mo (if (argE.eval ρ).1 then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1) =
      prngPot mo (esE.eval ρ) := by
    rw [prngOtherPot_add_pGet]
    simp [prngPot, hab]
  rw [show 1 + m + prngPot mo (esE.eval ρ) =
      1 + m + m_other +
        prngVpReady mo (if (argE.eval ρ).1 then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1)
      by omega]
  refine PotOKSPrng.bindPot hRecv (fun recvOut => ?_)
  refine potSPrng_caseOpt (fun hNone => ?_) (fun resInner hSome => ?_)
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hNone
    exact potSPrng_ret (by simp [prngVRecvPost, hNone, prngPot, esMk, Expr.eval])
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hSome
    refine potSPrng_caseOpt (fun hInNone => ?_) (fun tup hInSome => ?_)
    · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hInNone
      refine potSPrng_ret ?_
      simp only [prngVRecvPost, hSome, hInNone, prngPot, esSetH, letE_eval, esMk, esAbort, esG,
        Expr.eval, Expr.v0, Expr.v1, Expr.v2, Env.get_cons_zero, Env.get_cons_succ, hab,
        Bool.false_eq_true, ↓reduceIte]
      have hEqSum : prngVpReady mo (esE.eval ρ).1.1.1 + prngVpReady mo (esE.eval ρ).1.1.2 =
          m_other + prngVpReady mo
            (if (argE.eval ρ).1 then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1) := by
        simpa [prngPot, hab] using hSum.symm
      omega
    · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hInSome
      refine potSPrng_ite (fun _ => ?_) (fun _ => ?_)
      · refine potSPrng_ret ?_
        simp only [prngVRecvPost, hSome, hInSome, prngPot, esSetH, letE_eval, esMk, esAbort, esG,
          Expr.eval, Expr.v0, Expr.v2, Expr.v3, Env.get_cons_zero, Env.get_cons_succ, hab,
          Bool.false_eq_true, ↓reduceIte]
        have hEqSum : prngVpReady mo (esE.eval ρ).1.1.1 + prngVpReady mo (esE.eval ρ).1.1.2 =
            m_other + prngVpReady mo
              (if (argE.eval ρ).1 then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1) := by
          simpa [prngPot, hab] using hSum.symm
        omega
      · refine potSPrng_ite (fun _ => ?_) (fun _ => ?_)
        · rw [eval_bind]
          have hCom := commitEC_potOKS hhk L (esSetH (.fst (Expr.v3 (O := OO))) (.snd .v2))
            (esG (.fst .v3)) (.fst (.snd .v3))
            (pGet (cGsSt (esG (.fst .v3))) (.fst (.snd .v3)))
            (.fst .v0) (.pair (otherE (.fst (.snd .v3)))
              (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
            (.cons tup (.cons resInner (.cons recvOut
              (.cons (esE.eval ρ, argE.eval ρ) ρ)))) m
            (by simp [esSetH, letE_eval, esMk, esAbort, Expr.eval, Expr.v0, Expr.v3, hab])
          simp only [esG, Expr.eval, Expr.v0, Expr.v3,
            Env.get_cons_zero, Env.get_cons_succ] at hCom
          have hPre :
              m + prngOtherPot mo (esE.eval ρ).1.1 (argE.eval ρ).1 + prngVpReady mo tup.1 ≤
                prngVRecvPost mo m m_other
                  (if (argE.eval ρ).1 then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1)
                  recvOut := by
            simp [prngVRecvPost, hSome, hInSome, m_other]
          refine ⟨fun {_} k hk => (PotOKSPrng.bindPot hCom (fun comOut => ?_)).run k hk |>.mono hPre⟩
          refine potSPrng_caseOpt (fun hCNone => ?_) (fun _ hCSome => ?_)
          · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hCNone
            exact potSPrng_ret (by simp [prngCommitECPost, hCNone, Expr.eval, Expr.v0])
          · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hCSome
            exact potSPrng_ret (by
              simp [prngCommitECPost, hCSome, prngPot, esSetG, letE_eval, esMk, esH, esAbort,
                Expr.eval, Expr.v0, Expr.v1])
        · refine potSPrng_ret ?_
          simp only [prngVRecvPost, hSome, hInSome, esSetG, esSetH, letE_eval, esMk, esAbort, esG,
            Expr.eval, Expr.v0, Expr.v2, Expr.v3, Env.get_cons_zero, Env.get_cons_succ, hab]
          refine Nat.le_trans
            (Nat.add_le_add_left (Nat.le_of_eq
              (prngPot_mk_eq mo (g2 := (esE.eval ρ).1) (h2 := (esE.eval ρ).2.1)
                (ite_fst_eq_prng (by rw [cGsSetWin_st_prng]; rfl) rfl))) m) ?_
          simp only [prngPot, Bool.false_eq_true, ↓reduceIte]
          have hEqSum : prngVpReady mo (esE.eval ρ).1.1.1 + prngVpReady mo (esE.eval ρ).1.1.2 =
              m_other + prngVpReady mo
                (if (argE.eval ρ).1 then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1) := by
            simpa [prngPot, hab] using hSum.symm
          omega

private theorem deliverForgeECB1_hooksPRNGC_potOKS (L B qep tStar : ℕ) (mo : Mode)
    (cfg : ConfigEC OO)
    {Γ' : List (Ty S)} (esE : Expr OO Γ' prngEsTy)
    (argE : Expr OO Γ' (.prod .bool (.prod hdrCtTy hdrCtTy)))
    (ρ : Env Γ') (m : ℕ) :
    PotOKSPrng P_prng_sh (fun x => m + prngPot mo x.2)
      ((deliverForgeECB1 (hooksPRNGC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) B mo) L qep tStar cfg esE argE).eval ρ)
      (1 + m + prngPot mo (esE.eval ρ)) := by
  have hhk := hooksPRNGC_spec (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B mo
  unfold deliverForgeECB1
  rw [eval_bind_ret]
  refine potSPrng_ite (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0])) (fun hNotRef => ?_)
  have hab : (esE.eval ρ).2.2 = false := by
    simp only [orE, esAbort, Expr.eval, Expr.v0, Env.get_cons_zero] at hNotRef
    cases h : (esE.eval ρ).2.2 <;> simp_all
  refine potSPrng_caseOpt (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0])) (fun r1 _ => ?_)
  refine potSPrng_ite (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v1])) (fun _ => ?_)
  rw [eval_bind]
  set m_other := prngOtherPot mo (esE.eval ρ).1.1 (argE.eval ρ).1
  have hRecv := vRecvC_potOKS hhk (esH (.fst (Expr.v1 (O := OO)))) (esG (.fst .v1))
    (.fst (.snd .v1)) (pGet (cGsSt (esG (.fst .v1))) (.fst (.snd .v1))) (.snd (.snd (.snd .v1))) .none
    (.cons r1 (.cons (esE.eval ρ, argE.eval ρ) ρ)) m m_other
  simp only [pGet_eval_st_prng, cGsSt, esG, Expr.eval, Expr.v1,
    Env.get_cons_zero, Env.get_cons_succ] at hRecv
  change PotOKSPrng P_prng_sh
      (prngVRecvPost mo m m_other
        (if ((argE.eval ρ).1 : Bool) then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1))
      _ _ at hRecv
  have hSum : m_other +
      prngVpReady mo (if (argE.eval ρ).1 then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1) =
      prngPot mo (esE.eval ρ) := by
    rw [prngOtherPot_add_pGet]
    simp [prngPot, hab]
  rw [show 1 + m + prngPot mo (esE.eval ρ) =
      1 + m + m_other +
        prngVpReady mo (if (argE.eval ρ).1 then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1)
      by omega]
  refine PotOKSPrng.bindPot hRecv (fun recvOut => ?_)
  refine potSPrng_caseOpt (fun hNone => ?_) (fun resInner hSome => ?_)
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hNone
    exact potSPrng_ret (by simp [prngVRecvPost, hNone, prngPot, esMk, Expr.eval])
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hSome
    refine potSPrng_caseOpt (fun hInNone => ?_) (fun tup hInSome => ?_)
    · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hInNone
      refine potSPrng_ret ?_
      simp only [prngVRecvPost, hSome, hInNone, prngPot, esSetH, letE_eval, esMk, esAbort, esG,
        Expr.eval, Expr.v0, Expr.v1, Expr.v3, Env.get_cons_zero, Env.get_cons_succ, hab,
        Bool.false_eq_true, ↓reduceIte]
      have hEqSum : prngVpReady mo (esE.eval ρ).1.1.1 + prngVpReady mo (esE.eval ρ).1.1.2 =
          m_other + prngVpReady mo
            (if (argE.eval ρ).1 then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1) := by
        simpa [prngPot, hab] using hSum.symm
      omega
    · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hInSome
      refine potSPrng_ite (fun _ => ?_) (fun _ => ?_)
      · refine potSPrng_ret ?_
        simp only [prngVRecvPost, hSome, hInSome, prngPot, esSetH, letE_eval, esMk, esAbort, esG,
          Expr.eval, Expr.v0, Expr.v2, Expr.v4, Env.get_cons_zero, Env.get_cons_succ, hab,
          Bool.false_eq_true, ↓reduceIte]
        have hEqSum : prngVpReady mo (esE.eval ρ).1.1.1 + prngVpReady mo (esE.eval ρ).1.1.2 =
            m_other + prngVpReady mo
              (if (argE.eval ρ).1 then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1) := by
          simpa [prngPot, hab] using hSum.symm
        omega
      · refine potSPrng_ite (fun _ => ?_) (fun _ => ?_)
        · rw [eval_bind]
          have hCom := commitEC_potOKS hhk L (esSetH (.fst (Expr.v4 (O := OO))) (.snd .v2))
            (esG (.fst .v4)) (.fst (.snd .v4))
            (pGet (cGsSt (esG (.fst .v4))) (.fst (.snd .v4)))
            (.fst .v0) (.pair (otherE (.fst (.snd .v4)))
              (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
            (.cons tup (.cons resInner (.cons recvOut
              (.cons r1 (.cons (esE.eval ρ, argE.eval ρ) ρ))))) m
            (by simp [esSetH, letE_eval, esMk, esAbort, Expr.eval, Expr.v0, Expr.v4, hab])
          simp only [esG, Expr.eval, Expr.v0, Expr.v4,
            Env.get_cons_zero, Env.get_cons_succ] at hCom
          have hPre :
              m + prngOtherPot mo (esE.eval ρ).1.1 (argE.eval ρ).1 + prngVpReady mo tup.1 ≤
                prngVRecvPost mo m m_other
                  (if (argE.eval ρ).1 then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1)
                  recvOut := by
            simp [prngVRecvPost, hSome, hInSome, m_other]
          refine ⟨fun {_} k hk => (PotOKSPrng.bindPot hCom (fun comOut => ?_)).run k hk |>.mono hPre⟩
          refine potSPrng_caseOpt (fun hCNone => ?_) (fun _ hCSome => ?_)
          · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hCNone
            exact potSPrng_ret (by simp [prngCommitECPost, hCNone, Expr.eval, Expr.v0])
          · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hCSome
            exact potSPrng_ret (by
              simp [prngCommitECPost, hCSome, prngPot, esSetG, letE_eval, esMk, esH, esAbort,
                Expr.eval, Expr.v0, Expr.v1])
        · refine potSPrng_ret ?_
          simp only [prngVRecvPost, hSome, hInSome, esSetG, esSetH, letE_eval, esMk, esAbort, esG,
            Expr.eval, Expr.v0, Expr.v2, Expr.v4, Env.get_cons_zero, Env.get_cons_succ, hab]
          refine Nat.le_trans
            (Nat.add_le_add_left (Nat.le_of_eq
              (prngPot_mk_eq mo (g2 := (esE.eval ρ).1) (h2 := (esE.eval ρ).2.1)
                (ite_fst_eq_prng (by rw [cGsSetWin_st_prng]; rfl) rfl))) m) ?_
          simp only [prngPot, Bool.false_eq_true, ↓reduceIte]
          have hEqSum : prngVpReady mo (esE.eval ρ).1.1.1 + prngVpReady mo (esE.eval ρ).1.1.2 =
              m_other + prngVpReady mo
                (if (argE.eval ρ).1 then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1) := by
            simpa [prngPot, hab] using hSum.symm
          omega

private theorem injectECGen_hooksPRNGC_potOKS (b1 : Bool) (L B Δcka qep tStar : ℕ) (mo : Mode)
    (cfg : ConfigEC OO)
    {Γ' : List (Ty S)} (esE : Expr OO Γ' prngEsTy)
    (argE : Expr OO Γ' (.prod .bool hdrCtTy))
    (ρ : Env Γ') (m : ℕ) :
    PotOKSPrng P_prng_sh (fun x => m + prngPot mo x.2)
      ((injectECGen b1 (hooksPRNGC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) B mo) L (2 + Δcka) qep tStar cfg esE argE).eval ρ)
      (1 + m + prngPot mo (esE.eval ρ)) := by
  have hhk := hooksPRNGC_spec (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B mo
  cases b1
  · dsimp only [injectECGen]; simp only [Bool.false_eq_true, ↓reduceIte]
    exact injectEC_potOKS hhk L Δcka qep cfg esE argE ρ m
  · dsimp only [injectECGen]; simp only [↓reduceIte]
    exact injectECB1_hooksPRNGC_potOKS L B qep tStar mo cfg esE argE ρ m

private theorem deliverForgeECGen_hooksPRNGC_potOKS (b1 : Bool) (L B Δ qep tStar : ℕ) (mo : Mode)
    (cfg : ConfigEC OO)
    {Γ' : List (Ty S)} (esE : Expr OO Γ' prngEsTy)
    (argE : Expr OO Γ' (.prod .bool (.prod hdrCtTy hdrCtTy)))
    (ρ : Env Γ') (m : ℕ) :
    PotOKSPrng P_prng_sh (fun x => m + prngPot mo x.2)
      ((deliverForgeECGen b1 (hooksPRNGC (sampKR := sampKR) (sampKC := sampKC)
          (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) B mo)
          L Δ qep tStar cfg esE argE).eval ρ)
      (1 + m + prngPot mo (esE.eval ρ)) := by
  cases b1
  · dsimp only [deliverForgeECGen]; simp only [Bool.false_eq_true, ↓reduceIte]
    exact deliverForgeEC_hooksPRNGC_potOKS_shifted L B Δ qep mo cfg esE argE ρ m
  · dsimp only [deliverForgeECGen]; simp only [↓reduceIte]
    exact deliverForgeECB1_hooksPRNGC_potOKS L B qep tStar mo cfg esE argE ρ m

private theorem corrECShiftedPaper_hooksPRNGC_potOKS (L l B : ℕ) (mo : Mode) (π : Policy)
    {Γ' : List (Ty S)} (esE : Expr OO Γ' prngEsTy) (pE : Expr OO Γ' .bool)
    (ρ : Env Γ') (m : ℕ) :
    PotOKSPrng P_prng_sh (fun x => m + prngPot mo x.2)
      ((corrECShiftedPaper (hooksPRNGC (sampKR := sampKR) (sampKC := sampKC)
          (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) B mo) L l π esE pE).eval ρ)
      (1 + m + prngPot mo (esE.eval ρ)) := by
  unfold corrECShiftedPaper
  rw [eval_bind_ret]
  refine potSPrng_ite (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0])) (fun _ => ?_)
  refine potSPrng_ite
    (fun _ => potSPrng_ret (by simp [prngPot, esSetAbort, letE_eval, esMk, Expr.eval, Expr.v0]; omega))
    (fun _ => ?_)
  rw [eval_bind]
  refine PotOKSPrng.bindPot
    (potSPrng_comp_const _ _ (m + prngPot mo (esE.eval ρ)) (1 + m + prngPot mo (esE.eval ρ))
      (fun _ => Nat.le_refl _)
      (by simp [hooksPRNGC, prngRevealC_queries]))
    (fun _ => ?_)
  refine potSPrng_caseOpt (fun _ => ?_) (fun _ _ => ?_)
  · exact potSPrng_ret (by simp [prngPot, esMk, Expr.eval])
  · exact potSPrng_ret (by
      simp [prngPot, esMk, esAbort, esG, cAfterCorrShiftedE_st_prng, Expr.eval, Expr.v2])

private theorem implECShiftedPaperGen_hooksPRNGC_potOKS (b1 : Bool) (L l B Δcka qep maxSkip tStar : ℕ)
    (mo : Mode) (cfg : ConfigEC OO) (π : Policy)
    {Γ' : List (Ty S)} (esE : Expr OO Γ' prngEsTy)
    (qE : Expr OO Γ' (ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E))
    (ρ : Env Γ') (m : ℕ) :
    PotOKSPrng P_prng_sh (fun x => m + prngPot mo x.2)
      ((implECShiftedPaperGen b1 (hooksPRNGC (sampKR := sampKR) (sampKC := sampKC)
          (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) B mo)
        L l (2 + Δcka) qep maxSkip tStar cfg π esE qE).eval ρ)
      (1 + m + prngPot mo (esE.eval ρ)) := by
  have hhk := hooksPRNGC_spec (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B mo
  unfold implECShiftedPaperGen
  rw [eval_bind_ret]
  refine potSPrng_caseSum (fun _ _ => ?_) (fun _ _ => ?_)
  · refine potSPrng_caseSum (fun _ _ => ?_) (fun _ _ => ?_)
    · refine potSPrng_caseSum (fun _ _ => ?_) (fun _ _ => ?_)
      · refine potSPrng_caseSum (fun _ _ => ?_) (fun _ _ => ?_)
        · rw [eval_bind]
          exact PotOKSPrng.bindPot
            (transmitEC_potOKS hhk L Δcka qep π (.fst (Expr.v4 (O := OO))) .v0 _ m)
            (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0]))
        · rw [eval_bind]
          exact PotOKSPrng.bindPot
            (challEC_potOKS hhk L Δcka qep cfg π (.fst (Expr.v4 (O := OO))) .v0 _ m)
            (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0]))
      · rw [eval_bind]
        exact PotOKSPrng.bindPot
          (deliverEC_potOKS hhk L maxSkip cfg (.fst (Expr.v3 (O := OO))) .v0 _ m)
          (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0]))
    · rw [eval_bind]
      exact PotOKSPrng.bindPot
        (injectECGen_hooksPRNGC_potOKS b1 L B Δcka qep tStar mo cfg
          (.fst (Expr.v2 (O := OO))) .v0 _ m)
        (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0]))
  · rw [eval_bind]
    exact PotOKSPrng.bindPot
      (corrECShiftedPaper_hooksPRNGC_potOKS L l B mo π (.fst (Expr.v1 (O := OO))) .v0 _ m)
      (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0]))

private theorem implECDFShiftedPaperGen_hooksPRNGC_potOKS (b1 : Bool) (L l B Δcka qep maxSkip tStar : ℕ)
    (mo : Mode) (cfg : ConfigEC OO) (π : Policy)
    {Γ' : List (Ty S)} (esE : Expr OO Γ' prngEsTy)
    (qE : Expr OO Γ' (ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E))
    (ρ : Env Γ') (m : ℕ) :
    PotOKSPrng P_prng_sh (fun x => m + prngPot mo x.2)
      ((implECDFShiftedPaperGen b1 (hooksPRNGC (sampKR := sampKR) (sampKC := sampKC)
          (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) B mo)
        L l (2 + Δcka) qep maxSkip tStar cfg π esE qE).eval ρ)
      (1 + m + prngPot mo (esE.eval ρ)) := by
  unfold implECDFShiftedPaperGen
  rw [eval_bind_ret]
  refine potSPrng_caseSum (fun _ _ => ?_) (fun _ _ => ?_)
  · rw [eval_bind]
    exact PotOKSPrng.bindPot
      (implECShiftedPaperGen_hooksPRNGC_potOKS b1 L l B Δcka qep maxSkip tStar mo cfg π
        (.fst (Expr.v1 (O := OO))) .v0 _ m)
      (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0]))
  · rw [eval_bind]
    exact PotOKSPrng.bindPot
      (deliverForgeECGen_hooksPRNGC_potOKS b1 L B (2 + Δcka) qep tStar mo cfg
        (.fst (Expr.v1 (O := OO))) .v0 _ m)
      (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0]))

theorem redPRNGAuthDFShiftedPaperGenProg_makesAtMostQueries (L B Δcka qep maxSkip l tStar q : ℕ)
    (authH : Bool)
    (A : SchemeAdversaryDF Γ T RSt SS RS M CCoins E)
    (hA : MakesAtMostQueriesDF A q) :
    (((redPRNGAuthDFShiftedPaperGenProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B Δcka qep maxSkip l tStar authH).eval
        (fun _ => A) ())).IsQueryBoundP
      (· matches .inr _) (min (2 + 2 * q) (q + 3)) := by
  have hA' : A.IsQueryBoundP
      (isGameQuery (G := _root_.CryptoGames.SM.specDF (PartyState Γ T RSt SS RS) M CCoins
        (Header T × E))) q := by
    refine hA.of_imp (fun x hx => ?_)
    rcases x with _ | _ <;> simp_all [isGameQuery]
  let mo : Mode := ⟨authH, some (l - 1), tStar⟩
  let mo' : Mode := ⟨true, some (l - 1), tStar⟩
  refine costedReduction_makesAtMostQueries_prng _ (prngPot mo) q A hA' ?_ ?_ ?_ ?_
  · simp [CostedReduction.totalQueries, redPRNGAuthDFShiftedPaperGenProg, Comp.queries]
  · dsimp only [redPRNGAuthDFShiftedPaperGenProg]
    rw [eval_bind]
    exact PotOKSPrng.bindPot
      (initPRNGEStateC_potOKS (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) mo (.bool false)
        (Env.cons (t := .unit) () .nil) q)
      (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0]))
  · intro m qv sv
    exact implECDFShiftedPaperGen_hooksPRNGC_potOKS (!authH) L l B Δcka qep maxSkip
      tStar mo (modeCfgEC OO mo') mo'.policy .v0 .v1 (.cons sv (.cons qv .nil)) m
  · simp [redPRNGAuthDFShiftedPaperGenProg, Comp.queries]

theorem redPRNGAuthDFShiftedPaperProg_makesAtMostQueries (L B Δcka qep maxSkip l tStar q : ℕ)
    (A : SchemeAdversaryDF Γ T RSt SS RS M CCoins E)
    (hA : MakesAtMostQueriesDF A q) :
    (((redPRNGAuthDFShiftedPaperProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B Δcka qep maxSkip l tStar).eval
        (fun _ => A) ())).IsQueryBoundP
      (· matches .inr _) (min (2 + 2 * q) (q + 3)) :=
  redPRNGAuthDFShiftedPaperGenProg_makesAtMostQueries L B Δcka qep maxSkip l tStar q true A hA

theorem redPRNGAuthDFShiftedDir2PaperProg_makesAtMostQueries (L B qep maxSkip l tStar q : ℕ)
    (A : SchemeAdversaryDF Γ T RSt SS RS M CCoins E)
    (hA : MakesAtMostQueriesDF A q) :
    (((redPRNGAuthDFShiftedDir2PaperProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B qep maxSkip l tStar).eval
        (fun _ => A) ())).IsQueryBoundP
      (· matches .inr _) (min (2 + 2 * q) (q + 3)) :=
  redPRNGAuthDFShiftedPaperGenProg_makesAtMostQueries L B 0 qep maxSkip l tStar q false A hA

end ShiftedPrngPotOK

section AtomicQueryLifts

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (ℓ : ℕ) (C : _root_.CryptoGames.LibsignalSession.Crypto)
  (Dh : _root_.CryptoGames.CKA.DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
  (encT : Pt → _root_.CryptoGames.LibsignalSession.PublicKey)
  (idOf : Party → _root_.CryptoGames.LibsignalSession.IdentityKey) (lam : Pt)

private local instance : Inhabited Pt := ⟨0⟩

private theorem liftP_congr {ι : Type} {T : OracleSpec.{0, 0} ι} {S₁' S₂' : Sig}
    (I₂ : Iface S₂' T) (I₁ : Iface S₁' T) (hFwdU : ∀ n, I₂.fwdU n = I₁.fwdU n)
    {α : Type} (p : ProbComp α) : I₂.liftP p = I₁.liftP p := by
  unfold Iface.liftP
  rw [funext hFwdU]

private theorem prngPureAuxBundle_samp_querySubsumes (B0 : ℕ) (s : CKASamp)
    (z : ((_root_.CryptoGames.PRFPRNG.prngIface (BitVec 256) (_root_.CryptoGames.CKA.DDH.State (BitVec 256) Pt)
      (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
      (_root_.CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (_root_.CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
      (_root_.CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × _root_.CryptoGames.CBC.Plain ℓ)
      (ℕ × _root_.CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32)
      ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256))).smp.sDom s).denote) :
    QuerySubsumes
      (((prngPureAuxBundle ℓ Pt C Dh encPt encT idOf lam B0 ($ᵗ (BitVec 256))).sampMacro s).eval
        (.cons (toVal (fSortCKA ℓ Pt) (toDenCKA ℓ Pt) _ z)
          (.cons (idOf .A, idOf .B) .nil)))
      (toVal (fSortCKA ℓ Pt) (toDenCKA ℓ Pt)
        ((_root_.CryptoGames.PRFPRNG.prngIface (BitVec 256) (_root_.CryptoGames.CKA.DDH.State (BitVec 256) Pt)
          (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
          (_root_.CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
          (_root_.CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
          (_root_.CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × _root_.CryptoGames.CBC.Plain ℓ)
          (ℕ × _root_.CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32)
          ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256))).smp.sTy s) <$>
        (_root_.CryptoGames.PRFPRNG.prngIface (BitVec 256) (_root_.CryptoGames.CKA.DDH.State (BitVec 256) Pt)
          (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
          (_root_.CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
          (_root_.CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
          (_root_.CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × _root_.CryptoGames.CBC.Plain ℓ)
          (ℕ × _root_.CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32)
          ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256))).liftP
          ((_root_.CryptoGames.PRFPRNG.prngIface (BitVec 256) (_root_.CryptoGames.CKA.DDH.State (BitVec 256) Pt)
            (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
            (_root_.CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
            (_root_.CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
            (_root_.CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × _root_.CryptoGames.CBC.Plain ℓ)
            (ℕ × _root_.CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32)
            ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256))).smp.samp s z)) := by
  cases s with
  | bit | i =>
    apply QuerySubsumes.of_eq
    exact (liftP_congr (prngTargetIface ℓ Pt) _ (fun _ => rfl) _).trans (id_map _).symm
  | kr | kc | ccoins | k =>
    exact
      querySubsumes_liftP_of_support_subset (prngTargetIface ℓ Pt)
        (_root_.CryptoGames.PRFPRNG.prngIface (BitVec 256) (_root_.CryptoGames.CKA.DDH.State (BitVec 256) Pt)
          (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
          (_root_.CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
          (_root_.CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
          (_root_.CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × _root_.CryptoGames.CBC.Plain ℓ)
          (ℕ × _root_.CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32)
          ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
        (fun _ => rfl) (fun _ => rfl) (fun _ _ => by simp)

private theorem pureRetRed_isQueryBoundP
    {S' : Sig} {O : Ops S'} {ι κ : Type} {T₀ : OracleSpec.{0, 0} ι}
    {I : Iface S' (unifSpec + T₀)}
    {G : OracleSpec.{0, 0} κ} {GC : GameCodec S' G}
    {rIn aIn aOut out σ : Ty S'}
    (initE : Expr O [rIn] (.prod aIn σ))
    (handleE : Expr O [σ, GC.Q] (.prod GC.R σ))
    (finishE : Expr O [σ, aOut] out)
    {P : (unifSpec + T₀).Domain → Prop} [DecidablePred P]
    (hFwdU : ∀ n, I.fwdU n = liftM (OracleSpec.query (spec := unifSpec + T₀) (.inl n)))
    (hP : ∀ n, ¬ P (.inl n))
    (A : aIn.denote → OracleComp (unifSpec + G) aOut.denote) (x : rIn.denote) (k : ℕ) :
    (({ σ := σ, init := .ret initE, handle := .ret handleE, finish := .ret finishE } :
        CostedReduction O I G GC rIn aIn aOut out).eval A x).IsQueryBoundP P k := by
  let R : CostedReduction O I G GC rIn aIn aOut out :=
    { σ := σ, init := .ret initE, handle := .ret handleE, finish := .ret finishE }
  suffices hSim : ∀ (oa : OracleComp (unifSpec + G) aOut.denote) (s : σ.denote),
      (((simulateQ R.impl oa).run s) >>= fun bs =>
        pure (finishE.eval (.cons bs.2 (.cons bs.1 .nil)))).IsQueryBoundP P k by
    change (R.eval A x).IsQueryBoundP P k
    unfold CostedReduction.eval
    simp only [R, Comp.eval, pure_bind]
    exact hSim (A (initE.eval (.cons x .nil)).1) (initE.eval (.cons x .nil)).2
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure b =>
    intro s
    simp [simulateQ_pure, StateT.run_pure]
  | query_bind q mx ih =>
    intro s
    rcases q with n | t
    · have hStep : ((simulateQ R.impl
          (liftM (OracleSpec.query (spec := unifSpec + G) (.inl n)) >>= mx)).run s) >>=
            (fun bs => pure (finishE.eval (.cons bs.2 (.cons bs.1 .nil)))) =
          liftM (OracleSpec.query (spec := unifSpec + T₀) (.inl n)) >>= fun u =>
            (((simulateQ R.impl (mx u)).run s) >>=
              fun bs => pure (finishE.eval (.cons bs.2 (.cons bs.1 .nil)))) := by
        simp [R, CostedReduction.impl, handlerImpl,
          StateT.run_bind, StateT.run_lift, hFwdU, map_eq_bind_pure_comp, bind_assoc]
      rw [hStep, isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl (hP n), fun u => by simpa [hP n] using ih u s⟩
    · have hStep : ((simulateQ R.impl
          (liftM (OracleSpec.query (spec := unifSpec + G) (.inr t)) >>= mx)).run s) >>=
            (fun bs => pure (finishE.eval (.cons bs.2 (.cons bs.1 .nil)))) =
          (((simulateQ R.impl
              (mx (GC.rdec t (handleE.eval (.cons s (.cons (GC.qenc t) .nil))).1))).run
            (handleE.eval (.cons s (.cons (GC.qenc t) .nil))).2) >>=
              fun bs => pure (finishE.eval (.cons bs.2 (.cons bs.1 .nil)))) := by
        simp [R, CostedReduction.impl, handlerImpl, Comp.eval,
          StateT.run_bind, StateT.run_mk, pure_bind]
      rw [hStep]
      exact ih _ _

theorem compilePrngDFAtomic_makesAtMostQueries (B0 qOut : ℕ)
    (R : CostedReduction (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
      (_root_.CryptoGames.PRFPRNG.prngIface (BitVec 256) (_root_.CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (_root_.CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
        (_root_.CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
        (_root_.CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × _root_.CryptoGames.CBC.Plain ℓ)
        (ℕ × _root_.CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32)
        ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
      (_root_.CryptoGames.SM.specDF (_root_.CryptoGames.Ratchet.LibsignalSim.Fig8St Pt)
        (_root_.CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × _root_.CryptoGames.CBC.Plain ℓ)
        (BitVec 256) (_root_.CryptoGames.Ratchet.LibsignalSim.Fig8C Pt))
      (prngSMCodecDF (BitVec 256) (_root_.CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (_root_.CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
        (_root_.CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
        (_root_.CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × _root_.CryptoGames.CBC.Plain ℓ)
        (ℕ × _root_.CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32))
      .unit .unit .bool .bool)
    (A : OracleComp (unifSpec + _root_.CryptoGames.SM.specDF (_root_.CryptoGames.Ratchet.LibsignalSim.Fig8St Pt)
      (_root_.CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × _root_.CryptoGames.CBC.Plain ℓ)
      (BitVec 256) (_root_.CryptoGames.Ratchet.LibsignalSim.Fig8C Pt)) Bool)
    (hR : (R.eval (fun _ => A) ()).IsQueryBoundP (· matches .inr _) qOut) :
    _root_.CryptoGames.PRFPRNG.MakesAtMostQueries
      ((compilePrngDFAtomic ℓ Pt C Dh encPt encT idOf lam B0 R).eval (fun _ => A) ()) qOut := by
  unfold compilePrngDFAtomic guardRed
  split_ifs with hℓ
  · have hsub := QuerySubsumes.compilePureAuxRed_querySubsumes
      (prngPureAuxBundle ℓ Pt C Dh encPt encT idOf lam B0 ($ᵗ (BitVec 256)))
      (ckaDFToFig8Adapters ℓ Pt C Dh encPt encT idOf lam)
      R (toDenCKA ℓ Pt) () () (idOf .A, idOf .B)
      (fig8SplitIn_eval ℓ Pt C Dh encPt encT idOf lam)
      (ckaOpMacro_eval ℓ Pt C Dh encPt encT idOf lam B0)
      (prngPureAuxBundle_samp_querySubsumes ℓ C Dh encPt encT idOf lam B0)
      (fun g z => .of_eq (prngPureAuxBundle_query_eval ℓ Pt C Dh encPt encT idOf lam B0 _ g z))
      (fun _ => rfl) (fun _ => rfl)
      (fig8AdaptQDF_eval_cka ℓ Pt C Dh encPt encT lam)
      (fig8AdaptRDF_eval_cka ℓ Pt C Dh encPt encT lam)
      (fun _ => A) (fun _ => A) id
      (fun _ => .of_eq (id_map A).symm)
      (fun _ => rfl)
      (outEq := id) (fun _ => rfl)
    rw [id_map] at hsub
    exact hsub.isQueryBoundP (fun _ => nofun)
      (_root_.CryptoGames.LibsignalSM.Proofs.QueryBounds.isQueryBoundP_congr
        (by rintro (_ | _) <;> rfl) hR)
  · unfold dummyRed
    apply pureRetRed_isQueryBoundP
    · intro; rfl
    · intro _ h; nomatch h

theorem compileFsDFAtomic_makesAtMostQueries (B0 qOut : ℕ)
    (R : CostedReduction (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
      (_root_.CryptoGames.PRFPRNG.fsaeadHeaderAdIface (BitVec 256) (_root_.CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (_root_.CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
        (_root_.CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
        (_root_.CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × _root_.CryptoGames.CBC.Plain ℓ)
        (ℕ × _root_.CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32)
        ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
      (_root_.CryptoGames.SM.specDF (_root_.CryptoGames.Ratchet.LibsignalSim.Fig8St Pt)
        (_root_.CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × _root_.CryptoGames.CBC.Plain ℓ)
        (BitVec 256) (_root_.CryptoGames.Ratchet.LibsignalSim.Fig8C Pt))
      (prngSMCodecDF (BitVec 256) (_root_.CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (_root_.CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
        (_root_.CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
        (_root_.CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × _root_.CryptoGames.CBC.Plain ℓ)
        (ℕ × _root_.CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32))
      .unit .unit .bool .bool)
    (A : OracleComp (unifSpec + _root_.CryptoGames.SM.specDF (_root_.CryptoGames.Ratchet.LibsignalSim.Fig8St Pt)
      (_root_.CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × _root_.CryptoGames.CBC.Plain ℓ)
      (BitVec 256) (_root_.CryptoGames.Ratchet.LibsignalSim.Fig8C Pt)) Bool)
    (hR : _root_.CryptoGames.FSAEAD.MakesAtMostQueries (R.eval (fun _ => A) ()) qOut) :
    _root_.CryptoGames.FSAEAD.MakesAtMostQueries
      ((compileFsDFAtomic ℓ Pt C Dh encPt encT idOf lam B0 R).eval (fun _ => A) ()) qOut := by
  by_cases hℓ : ℓ < 10 ^ 6
  · exact QuerySubsumes.fsaeadMakesAtMostQueries_of_querySubsumes
      (compileFsDFAtomic_querySubsumes ℓ Pt C Dh encPt encT idOf lam hℓ B0 R A) hR
  · unfold compileFsDFAtomic guardRed
    simp only [hℓ, ↓reduceIte]
    unfold dummyRed
    apply pureRetRed_isQueryBoundP
    · intro; rfl
    · intro _ h; nomatch h

end AtomicQueryLifts

end

end Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedPotOK
