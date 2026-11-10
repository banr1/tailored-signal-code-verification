/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedReds2 -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.SM.DeliverForgePaperPRNG -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.SM.DeliverForgePaperFS -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.DFProgBoundsPaper -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.Bundles -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.SM.RedPRNGPotOK
import Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks
import Computational.Proofs.ReductionDsl.SM.RedFSPotOK
import Computational.Proofs.ReductionDsl.SM.DeliverForgePotOK
import Computational.Proofs.SessionCostedFig8.QuerySubsumes
import Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedPotOK

/-!
# Potential Query Bounds for Paper `DeliverForge` Reductions

Proves `min (2 + 2 * q) (q + 3)` PRF-PRNG and `min (2 * q) (q + 2)` FS-AEAD query bounds for the
unshifted, shifted, and case-split paper `DeliverForge` costed reductions.
-/

set_option autoImplicit false

namespace Computational.Proofs.HeadlineV1.DeliverForgePaperUnshiftedPotOK

public section

open OracleSpec OracleComp
open _root_.ReductionDsl
  (Sig Ty Ops Iface Env Expr Comp GameCodec CostedReduction handlerImpl isGameQuery prngTargetIface)
open _root_.Computational.Proofs.ReductionDsl.MacroLift
  (toVal guardRed dummyRed)
open _root_.Computational.Proofs.ReductionDsl.SM.RedPRNGPotOK
  (prngVpReady prngPot prngOtherPot pGet_eval_st_prng prngOtherPot_add_pGet cLeakE_st_prng
   cAfterCorrE_st_prng cGsSetWin_st_prng prngIface_fwdU_zero PotOKSPrng potSPrng_ret potSPrng_ite
   potSPrng_caseOpt potSPrng_caseSum ite_fst_eq_prng prngPot_mk_eq potSPrng_comp_const
   hooksPRNGC_spec prngVRecvPost vRecvC_potOKS prngCommitECPost commitEC_potOKS transmitEC_potOKS
   challEC_potOKS deliverEC_potOKS injectEC_potOKS initPRNGEStateC_potOKS
   costedReduction_makesAtMostQueries_prng)
open _root_.Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks
  (fsVpInv fsEsInv fsPot pGet_eval_st_fs fsVpInv_pGet cLeakE_st_fs cAfterCorrE_st_fs
   cGsSetWin_st_fs PotOKInvFS potInvFS_ret potInvFS_ite potInvFS_caseOpt potInvFS_caseSum
   fsRevealC_potOKInv vRecvC_hooksFSC_potOKInv)
open _root_.Computational.Proofs.ReductionDsl.SM.RedFSPotOK
  (fsEsInv_of_st_eq commitEC_hooksFSC_potOKInv
   transmitEC_hooksFSC_potOKInv challEC_hooksFSC_potOKInv
   deliverEC_hooksFSC_potOKInv injectEC_hooksFSC_potOKInv
   initFSEStateC_potOKInv costedReduction_makesAtMostQueries_fs)
open _root_.Computational.Proofs.ReductionDsl.SM.DeliverForgePotOK
  (deliverForgeEC_hooksFSC_potOKInv)
open _root_.Computational.Proofs.SessionCostedFig8.QuerySubsumes
  (QuerySubsumes)
open _root_.Computational.Proofs.SessionCostedFig8.Bundles
  (prngPureAuxBundle fSortCKA toDenCKA querySubsumes_liftP_of_support_subset
   fig8CkaOpsShallow compilePrngDFAtomic compileFsDFAtomic
   ckaDFToFig8Adapters fig8SplitIn_eval ckaOpMacro_eval prngPureAuxBundle_query_eval
   fig8AdaptQDF_eval_cka fig8AdaptRDF_eval_cka)
open _root_.CryptoGames (Party)
open _root_.CryptoGames.CKA (CKASamp ckaSMQ ckaSMQDF ckaHdrCtTy)
open _root_.CryptoGames.PRFPRNG (prngSig prngOps prngIface fsaeadHeaderAdIface prngSMCodecDF)
open _root_.CryptoGames.SM (otherE pGet orE letE_eval)
open _root_.CryptoGames.SM.Engine
  (ConfigEC Policy modeCfgEC cGsTy esG esH esAbort esMk esSetG esSetH esSetAbort
   cGsSt cGsMk cGsSetWin cLeakE cAfterCorrE cAfterCorrShiftedE
   vRecvC commitEC transmitEC challEC deliverEC injectEC
   deliverForgeEC injectECB1 deliverForgeECB1 injectECGen deliverForgeECGen
   corrECPaper corrECShiftedPaper
   implECPaper implECDFPaper implECShiftedPaperGen implECDFShiftedPaperGen
   eval_bind eval_bind_ret)
open _root_.CryptoGames.SM.Construction
  (Header PartyState Mode prngEsTy prngRevealC_queries hooksPRNGC
   fsVpTy fsEsTy hooksFSC initFSEStateC
   redPRNGAuthDFPaperProg
   redFSAuthDFPaperProg redFSAuthDFPaperProg_totalQueries
   redFSAuthDFShiftedPaperGenProg redFSAuthDFShiftedPaperProg redFSAuthDFShiftedDir2PaperProg)
open _root_.CryptoGames.SM.Construction.DeliverForge
  (SchemeAdversaryDF MakesAtMostQueriesDF)

section UnshiftedPrngPotOK

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
local notation "P_prng_u" => isGameQuery (G := _root_.CryptoGames.PRFPRNG.spec RSt I K)

private theorem deliverForgeEC_hooksPRNGC_potOKS_unshifted (L B Δ qep : ℕ) (mo : Mode)
    (cfg : ConfigEC OO)
    {Γ' : List (Ty S)} (esE : Expr OO Γ' prngEsTy)
    (argE : Expr OO Γ' (.prod .bool (.prod hdrCtTy hdrCtTy)))
    (ρ : Env Γ') (m : ℕ) :
    PotOKSPrng P_prng_u (fun x => m + prngPot mo x.2)
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
  change PotOKSPrng P_prng_u
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

private theorem corrECPaper_hooksPRNGC_potOKS (L B : ℕ) (mo : Mode) (π : Policy)
    {Γ' : List (Ty S)} (esE : Expr OO Γ' prngEsTy) (pE : Expr OO Γ' .bool)
    (ρ : Env Γ') (m : ℕ) :
    PotOKSPrng P_prng_u (fun x => m + prngPot mo x.2)
      ((corrECPaper (hooksPRNGC (sampKR := sampKR) (sampKC := sampKC)
          (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) B mo) L π esE pE).eval ρ)
      (1 + m + prngPot mo (esE.eval ρ)) := by
  unfold corrECPaper
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
      simp [prngPot, esMk, esAbort, esG, cAfterCorrE_st_prng, Expr.eval, Expr.v2])

private theorem implECPaper_hooksPRNGC_potOKS (L B Δcka qep maxSkip : ℕ)
    (mo : Mode) (cfg : ConfigEC OO) (π : Policy)
    {Γ' : List (Ty S)} (esE : Expr OO Γ' prngEsTy)
    (qE : Expr OO Γ' (ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E))
    (ρ : Env Γ') (m : ℕ) :
    PotOKSPrng P_prng_u (fun x => m + prngPot mo x.2)
      ((implECPaper (hooksPRNGC (sampKR := sampKR) (sampKC := sampKC)
          (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) B mo)
        L (2 + Δcka) qep maxSkip cfg π esE qE).eval ρ)
      (1 + m + prngPot mo (esE.eval ρ)) := by
  have hhk := hooksPRNGC_spec (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B mo
  unfold implECPaper
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
        (injectEC_potOKS hhk L Δcka qep cfg (.fst (Expr.v2 (O := OO))) .v0 _ m)
        (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0]))
  · rw [eval_bind]
    exact PotOKSPrng.bindPot
      (corrECPaper_hooksPRNGC_potOKS L B mo π (.fst (Expr.v1 (O := OO))) .v0 _ m)
      (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0]))

private theorem implECDFPaper_hooksPRNGC_potOKS (L B Δcka qep maxSkip : ℕ)
    (mo : Mode) (cfg : ConfigEC OO) (π : Policy)
    {Γ' : List (Ty S)} (esE : Expr OO Γ' prngEsTy)
    (qE : Expr OO Γ' (ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E))
    (ρ : Env Γ') (m : ℕ) :
    PotOKSPrng P_prng_u (fun x => m + prngPot mo x.2)
      ((implECDFPaper (hooksPRNGC (sampKR := sampKR) (sampKC := sampKC)
          (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) B mo)
        L (2 + Δcka) qep maxSkip cfg π esE qE).eval ρ)
      (1 + m + prngPot mo (esE.eval ρ)) := by
  unfold implECDFPaper
  rw [eval_bind_ret]
  refine potSPrng_caseSum (fun _ _ => ?_) (fun _ _ => ?_)
  · rw [eval_bind]
    exact PotOKSPrng.bindPot
      (implECPaper_hooksPRNGC_potOKS L B Δcka qep maxSkip mo cfg π
        (.fst (Expr.v1 (O := OO))) .v0 _ m)
      (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0]))
  · rw [eval_bind]
    exact PotOKSPrng.bindPot
      (deliverForgeEC_hooksPRNGC_potOKS_unshifted L B (2 + Δcka) qep mo cfg
        (.fst (Expr.v1 (O := OO))) .v0 _ m)
      (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0]))

theorem redPRNGAuthDFPaperProg_makesAtMostQueries (L B Δcka qep maxSkip : ℕ)
    (tL : Option ℕ) (t q : ℕ)
    (A : SchemeAdversaryDF Γ T RSt SS RS M CCoins E)
    (hA : MakesAtMostQueriesDF A q) :
    (((redPRNGAuthDFPaperProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B Δcka qep maxSkip tL t).eval
        (fun _ => A) ())).IsQueryBoundP
      (· matches .inr _) (min (2 + 2 * q) (q + 3)) := by
  have hA' : A.IsQueryBoundP
      (isGameQuery (G := _root_.CryptoGames.SM.specDF (PartyState Γ T RSt SS RS) M CCoins
        (Header T × E))) q := by
    refine hA.of_imp (fun x hx => ?_)
    rcases x with _ | _ <;> simp_all [isGameQuery]
  let mo : Mode := ⟨true, tL, t⟩
  refine costedReduction_makesAtMostQueries_prng _ (prngPot mo) q A hA' ?_ ?_ ?_ ?_
  · simp [CostedReduction.totalQueries, redPRNGAuthDFPaperProg, Comp.queries]
  · dsimp only [redPRNGAuthDFPaperProg]
    rw [eval_bind]
    exact PotOKSPrng.bindPot
      (initPRNGEStateC_potOKS (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) mo (.bool false)
        (Env.cons (t := .unit) () .nil) q)
      (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0]))
  · intro m qv sv
    exact implECDFPaper_hooksPRNGC_potOKS L B Δcka qep maxSkip mo
      (modeCfgEC OO mo) mo.policy .v0 .v1 (.cons sv (.cons qv .nil)) m
  · simp [redPRNGAuthDFPaperProg, Comp.queries]

end UnshiftedPrngPotOK

section AtomicUnshiftedPrng

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (ℓ : ℕ) (C : _root_.CryptoGames.LibsignalSession.Crypto)
  (Dh : _root_.CryptoGames.CKA.DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
  (encT : Pt → _root_.CryptoGames.LibsignalSession.PublicKey)
  (idOf : Party → _root_.CryptoGames.LibsignalSession.IdentityKey) (lam : Pt)

theorem compilePrngDFAtomic_makesAtMostQueries_u (B0 qOut : ℕ)
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
      ((compilePrngDFAtomic ℓ Pt C Dh encPt encT idOf lam B0 R).eval (fun _ => A) ()) qOut :=
  _root_.Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedPotOK.compilePrngDFAtomic_makesAtMostQueries
    ℓ C Dh encPt encT idOf lam B0 qOut R A hR

theorem redPRNGAuthDFPaperAtomicProg_makesAtMostQueries
    (qep q : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : OracleComp (unifSpec + _root_.CryptoGames.SM.specDF (_root_.CryptoGames.Ratchet.LibsignalSim.Fig8St Pt)
      (_root_.CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × _root_.CryptoGames.CBC.Plain ℓ)
      (BitVec 256) (_root_.CryptoGames.Ratchet.LibsignalSim.Fig8C Pt)) Bool)
    (hA : A.IsQueryBoundP (· matches .inr _) q) :
    _root_.CryptoGames.PRFPRNG.MakesAtMostQueries
      ((_root_.Computational.Proofs.SessionCostedFig8.DFProgBoundsPaper.redPRNGAuthDFPaperAtomicProg
        Dh encPt C ℓ encT idOf lam qep q tL t).eval (fun _ => A) ())
      (min (2 + 2 * q) (q + 3)) := by
  unfold _root_.Computational.Proofs.SessionCostedFig8.DFProgBoundsPaper.redPRNGAuthDFPaperAtomicProg
  exact compilePrngDFAtomic_makesAtMostQueries_u ℓ C Dh encPt encT idOf lam
    ((q + 1) * (_root_.CryptoGames.LibsignalSession.maxForwardJumps + 1)) (min (2 + 2 * q) (q + 3)) _ A
    (redPRNGAuthDFPaperProg_makesAtMostQueries (q + 1)
      ((q + 1) * (_root_.CryptoGames.LibsignalSession.maxForwardJumps + 1)) 1 qep
      _root_.CryptoGames.LibsignalSession.maxForwardJumps tL t q A
      (hA.of_imp (by rintro (_ | _) <;> simp)))

theorem redPRNGAuthDFCasePaperAtomicProg_makesAtMostQueries
    (qep q : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : OracleComp (unifSpec + _root_.CryptoGames.SM.specDF (_root_.CryptoGames.Ratchet.LibsignalSim.Fig8St Pt)
      (_root_.CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × _root_.CryptoGames.CBC.Plain ℓ)
      (BitVec 256) (_root_.CryptoGames.Ratchet.LibsignalSim.Fig8C Pt)) Bool)
    (hA : A.IsQueryBoundP (· matches .inr _) q) :
    _root_.CryptoGames.PRFPRNG.MakesAtMostQueries
      ((_root_.Computational.Proofs.SessionCostedFig8.DFProgBoundsPaper.redPRNGAuthDFCasePaperAtomicProg
        Dh encPt C ℓ encT idOf lam qep q tL t).eval (fun _ => A) ())
      (min (2 + 2 * q) (q + 3)) := by
  have hA' : MakesAtMostQueriesDF A q := hA.of_imp (by rintro (_ | _) <;> simp)
  unfold _root_.Computational.Proofs.SessionCostedFig8.DFProgBoundsPaper.redPRNGAuthDFCasePaperAtomicProg
  dsimp only
  split
  · exact compilePrngDFAtomic_makesAtMostQueries_u ℓ C Dh encPt encT idOf lam
      ((q + 1) * (_root_.CryptoGames.LibsignalSession.maxForwardJumps + 1)) (min (2 + 2 * q) (q + 3)) _ A
      (_root_.Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedPotOK.redPRNGAuthDFShiftedDir2PaperProg_makesAtMostQueries
        (q + 1) ((q + 1) * (_root_.CryptoGames.LibsignalSession.maxForwardJumps + 1)) qep
        _root_.CryptoGames.LibsignalSession.maxForwardJumps (t - 1) t q A hA')
  · split
    · exact compilePrngDFAtomic_makesAtMostQueries_u ℓ C Dh encPt encT idOf lam
        ((q + 1) * (_root_.CryptoGames.LibsignalSession.maxForwardJumps + 1)) (min (2 + 2 * q) (q + 3)) _ A
        (_root_.Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedPotOK.redPRNGAuthDFShiftedPaperProg_makesAtMostQueries
          (q + 1) ((q + 1) * (_root_.CryptoGames.LibsignalSession.maxForwardJumps + 1)) 1 qep
          _root_.CryptoGames.LibsignalSession.maxForwardJumps (t - 2) t q A hA')
    · exact compilePrngDFAtomic_makesAtMostQueries_u ℓ C Dh encPt encT idOf lam
        ((q + 1) * (_root_.CryptoGames.LibsignalSession.maxForwardJumps + 1)) (min (2 + 2 * q) (q + 3)) _ A
        (redPRNGAuthDFPaperProg_makesAtMostQueries
          (q + 1) ((q + 1) * (_root_.CryptoGames.LibsignalSession.maxForwardJumps + 1)) 1 qep
          _root_.CryptoGames.LibsignalSession.maxForwardJumps tL t q A hA')

end AtomicUnshiftedPrng

/-! ## FS-AEAD query bounds -/

section PaperFsPotOK

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
local notation "esTyFS" => fsEsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "OO" =>
  prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE
local notation "P_fs" => isGameQuery (G := _root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E)

private theorem cAfterCorrShiftedE_st_fs {O' : Ops S} {vpT : Ty S} {Γ' : List (Ty S)}
    (L l : ℕ) (s : Expr O' Γ' (cGsTy vpT)) (p : Expr O' Γ' .bool) (ρ : Env Γ') :
    ((cAfterCorrShiftedE L l s p).eval ρ).1 = (s.eval ρ).1 := by
  simp [cAfterCorrShiftedE, letE_eval, cGsMk, cGsSt, cLeakE_st_fs, Expr.eval, Expr.v0, Expr.v1]

private theorem corrECPaper_hooksFSC_potOKInv (L B Δcka : ℕ) (mo : Mode) (j : ℕ) (π : Policy)
    {Γ' : List (Ty S)} (esE : Expr OO Γ' esTyFS) (pE : Expr OO Γ' .bool)
    (ρ : Env Γ') (m : ℕ) (hInv : fsEsInv mo.tStar (esE.eval ρ)) :
    PotOKInvFS P_fs (fun x => fsEsInv mo.tStar x.2)
      (fun x => m + fsPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) x.2)
      ((corrECPaper (hooksFSC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) L B Δcka mo j) L π esE pE).eval ρ)
      (1 + m + fsPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (esE.eval ρ)) := by
  unfold corrECPaper; rw [eval_bind_ret]
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

private theorem corrECShiftedPaper_hooksFSC_potOKInv (L l B Δcka : ℕ) (mo : Mode) (j : ℕ)
    (π : Policy)
    {Γ' : List (Ty S)} (esE : Expr OO Γ' esTyFS) (pE : Expr OO Γ' .bool)
    (ρ : Env Γ') (m : ℕ) (hInv : fsEsInv mo.tStar (esE.eval ρ)) :
    PotOKInvFS P_fs (fun x => fsEsInv mo.tStar x.2)
      (fun x => m + fsPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) x.2)
      ((corrECShiftedPaper (hooksFSC (sampKR := sampKR) (sampKC := sampKC)
          (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B Δcka mo j)
        L l π esE pE).eval ρ)
      (1 + m + fsPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (esE.eval ρ)) := by
  unfold corrECShiftedPaper; rw [eval_bind_ret]
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
      (by simpa [fsEsInv, esMk, esG, cAfterCorrShiftedE_st_fs, Expr.eval, Expr.v2] using hInv)
      (by simp [fsPot, esMk, Expr.eval, Expr.v1]))

private theorem injectECB1_hooksFSC_potOKInv (L B Δcka qep tStar : ℕ) (mo : Mode) (j : ℕ)
    (cfg : ConfigEC OO)
    {Γ' : List (Ty S)} (esE : Expr OO Γ' esTyFS)
    (argE : Expr OO Γ' (.prod .bool hdrCtTy))
    (ρ : Env Γ') (m : ℕ) (hInv : fsEsInv mo.tStar (esE.eval ρ)) :
    PotOKInvFS P_fs (fun x => fsEsInv mo.tStar x.2)
      (fun x => m + fsPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) x.2)
      ((injectECB1 (hooksFSC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) L B Δcka mo j) L qep tStar cfg esE argE).eval ρ)
      (1 + m + fsPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (esE.eval ρ)) := by
  unfold injectECB1; rw [eval_bind_ret]
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

private theorem deliverForgeECB1_hooksFSC_potOKInv (L B Δcka qep tStar : ℕ) (mo : Mode) (j : ℕ)
    (cfg : ConfigEC OO)
    {Γ' : List (Ty S)} (esE : Expr OO Γ' esTyFS)
    (argE : Expr OO Γ' (.prod .bool (.prod hdrCtTy hdrCtTy)))
    (ρ : Env Γ') (m : ℕ) (hInv : fsEsInv mo.tStar (esE.eval ρ)) :
    PotOKInvFS P_fs (fun x => fsEsInv mo.tStar x.2)
      (fun x => m + fsPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) x.2)
      ((deliverForgeECB1 (hooksFSC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) L B Δcka mo j) L qep tStar cfg esE argE).eval ρ)
      (1 + m + fsPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (esE.eval ρ)) := by
  unfold deliverForgeECB1; rw [eval_bind_ret]
  refine potInvFS_ite
    (fun _ => potInvFS_ret (by simpa [Expr.eval, Expr.v0] using hInv)
      (by simp only [Expr.eval, Expr.v0, Env.get_cons_zero]; omega))
    (fun _ => ?_)
  refine potInvFS_caseOpt
    (fun _ => potInvFS_ret (by simpa [Expr.eval, Expr.v0] using hInv)
      (by simp only [Expr.eval, Expr.v0, Env.get_cons_zero]; omega))
    (fun r1 _ => potInvFS_ite
      (fun _ => potInvFS_ret (by simpa [Expr.eval, Expr.v1] using hInv)
        (by simp only [Expr.eval, Expr.v1, Env.get_cons_succ, Env.get_cons_zero]; omega))
      (fun _ => ?_))
  rw [eval_bind]
  have hRecv := vRecvC_hooksFSC_potOKInv (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
    L B Δcka mo j (esH (.fst (Expr.v1 (O := OO)))) (esG (.fst .v1))
    (.fst (.snd .v1)) (pGet (cGsSt (esG (.fst .v1))) (.fst (.snd .v1)))
    (.snd (.snd (.snd .v1))) .none
    (.cons r1 (.cons (esE.eval ρ, argE.eval ρ) ρ)) m
    (by
      simp only [pGet_eval_st_fs, cGsSt, esG, Expr.eval, Expr.v1,
        Env.get_cons_zero, Env.get_cons_succ]
      exact fsVpInv_pGet mo.tStar (esE.eval ρ).1.1 (argE.eval ρ).1 hInv)
  simp only [esH, Expr.eval, Expr.v1, Env.get_cons_zero, Env.get_cons_succ] at hRecv
  refine PotOKInvFS.bindPot hRecv (fun recvOut hRecvInv => ?_)
  refine potInvFS_caseOpt
    (fun _ => potInvFS_ret (by simpa [fsEsInv, esMk, esG, Expr.eval, Expr.v2] using hInv)
      (by simp [fsPot, esMk, Expr.eval, Expr.v0]))
    (fun resIn hSome => ?_)
  simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hSome
  refine potInvFS_caseOpt
    (fun _ => potInvFS_ret
      (by simpa [fsEsInv, esSetH, esMk, esG, Expr.eval, Expr.v0, Expr.v3] using hInv)
      (by simp [fsPot, esSetH, esMk, Expr.eval, Expr.v0, Expr.v1]))
    (fun tup hInSome => ?_)
  simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hInSome
  refine potInvFS_ite
    (fun _ => potInvFS_ret
      (by simpa [fsEsInv, esSetH, esMk, esG, Expr.eval, Expr.v0, Expr.v4] using hInv)
      (by simp [fsPot, esSetH, esMk, Expr.eval, Expr.v0, Expr.v2]))
    (fun _ => potInvFS_ite (fun _ => ?_) (fun _ => ?_))
  · rw [eval_bind]
    have hCom := commitEC_hooksFSC_potOKInv (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
      L B Δcka mo j (esSetH (.fst (Expr.v4 (O := OO))) (.snd .v2))
      (esG (.fst .v4)) (.fst (.snd .v4)) (pGet (cGsSt (esG (.fst .v4))) (.fst (.snd .v4)))
      (.fst .v0) (.pair (otherE (.fst (.snd .v4)))
        (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
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
    simpa [fsEsInv, esSetG, esMk, Expr.eval, Expr.v0] using hComInv.2 s_acc hs_acc
  · refine potInvFS_ret ?_
      (by simp [fsPot, esSetG, esSetH, esMk, esH, Expr.eval, Expr.v0, Expr.v2])
    refine fsEsInv_of_st_eq ?_ hInv
    simp only [esSetG, esSetH, esMk, Expr.eval, Expr.v0, Env.get_cons_zero]
    split
    · simp [cGsSetWin_st_fs, esG, Expr.eval, Expr.v4]
    · simp [esG, Expr.eval, Expr.v4]

private theorem injectECGen_hooksFSC_potOKInv (b1 : Bool) (L B Δcka qep tStar : ℕ) (mo : Mode)
    (j : ℕ) (cfg : ConfigEC OO)
    {Γ' : List (Ty S)} (esE : Expr OO Γ' esTyFS)
    (argE : Expr OO Γ' (.prod .bool hdrCtTy))
    (ρ : Env Γ') (m : ℕ) (hInv : fsEsInv mo.tStar (esE.eval ρ)) :
    PotOKInvFS P_fs (fun x => fsEsInv mo.tStar x.2)
      (fun x => m + fsPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) x.2)
      ((injectECGen b1 (hooksFSC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) L B Δcka mo j) L (2 + Δcka) qep tStar cfg esE argE).eval ρ)
      (1 + m + fsPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (esE.eval ρ)) := by
  cases b1
  · exact injectEC_hooksFSC_potOKInv L B Δcka qep mo j cfg esE argE ρ m hInv
  · exact injectECB1_hooksFSC_potOKInv L B Δcka qep tStar mo j cfg esE argE ρ m hInv

private theorem deliverForgeECGen_hooksFSC_potOKInv (b1 : Bool) (L B Δcka qep tStar : ℕ)
    (mo : Mode) (j : ℕ) (cfg : ConfigEC OO)
    {Γ' : List (Ty S)} (esE : Expr OO Γ' esTyFS)
    (argE : Expr OO Γ' (.prod .bool (.prod hdrCtTy hdrCtTy)))
    (ρ : Env Γ') (m : ℕ) (hInv : fsEsInv mo.tStar (esE.eval ρ)) :
    PotOKInvFS P_fs (fun x => fsEsInv mo.tStar x.2)
      (fun x => m + fsPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) x.2)
      ((deliverForgeECGen b1 (hooksFSC (sampKR := sampKR) (sampKC := sampKC)
          (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B Δcka mo j)
        L (2 + Δcka) qep tStar cfg esE argE).eval ρ)
      (1 + m + fsPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (esE.eval ρ)) := by
  cases b1
  · exact deliverForgeEC_hooksFSC_potOKInv L B Δcka qep mo j cfg esE argE ρ m hInv
  · exact deliverForgeECB1_hooksFSC_potOKInv L B Δcka qep tStar mo j cfg esE argE ρ m hInv

private theorem implECPaper_hooksFSC_potOKInv (L B Δcka qep maxSkip : ℕ) (mo : Mode) (j : ℕ)
    (cfg : ConfigEC OO) (π : Policy)
    {Γ' : List (Ty S)} (esE : Expr OO Γ' esTyFS)
    (qE : Expr OO Γ' (ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E))
    (ρ : Env Γ') (m : ℕ) (hInv : fsEsInv mo.tStar (esE.eval ρ)) :
    PotOKInvFS P_fs (fun x => fsEsInv mo.tStar x.2)
      (fun x => m + fsPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) x.2)
      ((implECPaper (hooksFSC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) L B Δcka mo j)
        L (2 + Δcka) qep maxSkip cfg π esE qE).eval ρ)
      (1 + m + fsPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (esE.eval ρ)) := by
  unfold implECPaper; rw [eval_bind_ret]
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
      (corrECPaper_hooksFSC_potOKInv L B Δcka mo j π (.fst (Expr.v1 (O := OO))) .v0 _ m
        (by simpa [Expr.eval, Expr.v1] using hInv))
      (fun _ hx => potInvFS_ret (by simpa [Expr.eval, Expr.v0] using hx)
        (by simp [Expr.eval, Expr.v0]))

private theorem implECDFPaper_hooksFSC_potOKInv (L B Δcka qep maxSkip : ℕ) (mo : Mode) (j : ℕ)
    (cfg : ConfigEC OO) (π : Policy)
    {Γ' : List (Ty S)} (esE : Expr OO Γ' esTyFS)
    (qE : Expr OO Γ' (ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E))
    (ρ : Env Γ') (m : ℕ) (hInv : fsEsInv mo.tStar (esE.eval ρ)) :
    PotOKInvFS P_fs (fun x => fsEsInv mo.tStar x.2)
      (fun x => m + fsPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) x.2)
      ((implECDFPaper (hooksFSC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) L B Δcka mo j)
        L (2 + Δcka) qep maxSkip cfg π esE qE).eval ρ)
      (1 + m + fsPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (esE.eval ρ)) := by
  unfold implECDFPaper; rw [eval_bind_ret]
  refine potInvFS_caseSum (fun _ _ => ?_) (fun _ _ => ?_)
  · rw [eval_bind]
    exact PotOKInvFS.bindPot
      (implECPaper_hooksFSC_potOKInv L B Δcka qep maxSkip mo j cfg π (.fst (Expr.v1 (O := OO))) .v0 _ m
        (by simpa [Expr.eval, Expr.v1] using hInv))
      (fun _ h' => potInvFS_ret (by simpa [Expr.eval, Expr.v0] using h')
        (by simp [Expr.eval, Expr.v0]))
  · rw [eval_bind]
    exact PotOKInvFS.bindPot
      (deliverForgeEC_hooksFSC_potOKInv L B Δcka qep mo j cfg (.fst (Expr.v1 (O := OO))) .v0 _ m
        (by simpa [Expr.eval, Expr.v1] using hInv))
      (fun _ h' => potInvFS_ret (by simpa [Expr.eval, Expr.v0] using h')
        (by simp [Expr.eval, Expr.v0]))

private theorem implECShiftedPaperGen_hooksFSC_potOKInv (b1 : Bool) (L l B Δcka qep maxSkip tStar : ℕ)
    (mo : Mode) (j : ℕ) (cfg : ConfigEC OO) (π : Policy)
    {Γ' : List (Ty S)} (esE : Expr OO Γ' esTyFS)
    (qE : Expr OO Γ' (ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E))
    (ρ : Env Γ') (m : ℕ) (hInv : fsEsInv mo.tStar (esE.eval ρ)) :
    PotOKInvFS P_fs (fun x => fsEsInv mo.tStar x.2)
      (fun x => m + fsPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) x.2)
      ((implECShiftedPaperGen b1 (hooksFSC (sampKR := sampKR) (sampKC := sampKC)
          (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B Δcka mo j)
        L l (2 + Δcka) qep maxSkip tStar cfg π esE qE).eval ρ)
      (1 + m + fsPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (esE.eval ρ)) := by
  unfold implECShiftedPaperGen; rw [eval_bind_ret]
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
        (injectECGen_hooksFSC_potOKInv b1 L B Δcka qep tStar mo j cfg (.fst (Expr.v2 (O := OO))) .v0 _ m
          (by simpa [Expr.eval, Expr.v2] using hInv))
        (fun _ hx => potInvFS_ret (by simpa [Expr.eval, Expr.v0] using hx)
          (by simp [Expr.eval, Expr.v0]))
  · rw [eval_bind]; exact PotOKInvFS.bindPot
      (corrECShiftedPaper_hooksFSC_potOKInv L l B Δcka mo j π (.fst (Expr.v1 (O := OO))) .v0 _ m
        (by simpa [Expr.eval, Expr.v1] using hInv))
      (fun _ hx => potInvFS_ret (by simpa [Expr.eval, Expr.v0] using hx)
        (by simp [Expr.eval, Expr.v0]))

private theorem implECDFShiftedPaperGen_hooksFSC_potOKInv (b1 : Bool)
    (L l B Δcka qep maxSkip tStar : ℕ) (mo : Mode) (j : ℕ) (cfg : ConfigEC OO) (π : Policy)
    {Γ' : List (Ty S)} (esE : Expr OO Γ' esTyFS)
    (qE : Expr OO Γ' (ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E))
    (ρ : Env Γ') (m : ℕ) (hInv : fsEsInv mo.tStar (esE.eval ρ)) :
    PotOKInvFS P_fs (fun x => fsEsInv mo.tStar x.2)
      (fun x => m + fsPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) x.2)
      ((implECDFShiftedPaperGen b1 (hooksFSC (sampKR := sampKR) (sampKC := sampKC)
          (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B Δcka mo j)
        L l (2 + Δcka) qep maxSkip tStar cfg π esE qE).eval ρ)
      (1 + m + fsPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (esE.eval ρ)) := by
  unfold implECDFShiftedPaperGen; rw [eval_bind_ret]
  refine potInvFS_caseSum (fun _ _ => ?_) (fun _ _ => ?_)
  · rw [eval_bind]
    exact PotOKInvFS.bindPot
      (implECShiftedPaperGen_hooksFSC_potOKInv b1 L l B Δcka qep maxSkip tStar mo j cfg π
        (.fst (Expr.v1 (O := OO))) .v0 _ m
        (by simpa [Expr.eval, Expr.v1] using hInv))
      (fun _ h' => potInvFS_ret (by simpa [Expr.eval, Expr.v0] using h')
        (by simp [Expr.eval, Expr.v0]))
  · rw [eval_bind]
    exact PotOKInvFS.bindPot
      (deliverForgeECGen_hooksFSC_potOKInv b1 L B Δcka qep tStar mo j cfg
        (.fst (Expr.v1 (O := OO))) .v0 _ m
        (by simpa [Expr.eval, Expr.v1] using hInv))
      (fun _ h' => potInvFS_ret (by simpa [Expr.eval, Expr.v0] using h')
        (by simp [Expr.eval, Expr.v0]))

theorem redFSAuthDFPaperProg_makesAtMostQueries (L B Δcka qep maxSkip : ℕ) (j : ℕ)
    (tL : Option ℕ) (t q : ℕ)
    (A : OracleComp (unifSpec + _root_.CryptoGames.SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)) Bool)
    (hA : A.IsQueryBoundP (· matches .inr _) q) :
    _root_.CryptoGames.FSAEAD.MakesAtMostQueries
      ((redFSAuthDFPaperProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
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
    (redFSAuthDFPaperProg_totalQueries L B Δcka qep maxSkip j tL t q) ?_ ?_
    (by simp [redFSAuthDFPaperProg, Comp.queries])
  · dsimp only [redFSAuthDFPaperProg]; rw [eval_bind]
    exact (PotOKInvFS.bindPot (initFSEStateC_potOKInv L ⟨true, tL, t⟩ j (.bool false) _ q)
      (fun _ hes => potInvFS_ret (by simpa [Expr.eval, Expr.v0] using hes)
        (by simp [Expr.eval, Expr.v0]))).mono (by omega)
  · intro m qv sv hsv
    exact implECDFPaper_hooksFSC_potOKInv L B Δcka qep maxSkip ⟨true, tL, t⟩ j
      (modeCfgEC OO ⟨true, tL, t⟩) (⟨true, tL, t⟩ : Mode).policy .v0 .v1
      (.cons sv (.cons qv .nil)) m hsv

theorem redFSAuthDFShiftedPaperGenProg_makesAtMostQueries
    (L B Δcka qep maxSkip j l tStar : ℕ) (authH : Bool) (q : ℕ)
    (A : OracleComp (unifSpec + _root_.CryptoGames.SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)) Bool)
    (hA : A.IsQueryBoundP (· matches .inr _) q) :
    _root_.CryptoGames.FSAEAD.MakesAtMostQueries
      ((redFSAuthDFShiftedPaperGenProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
          (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK)
          L B Δcka qep maxSkip j l tStar authH).eval (fun _ => A) ())
      (min (2 * q) (q + 2)) := by
  let mo : Mode := ⟨authH, some (l - 1), tStar⟩
  let mo' : Mode := ⟨true, some (l - 1), tStar⟩
  refine costedReduction_makesAtMostQueries_fs _ (fsEsInv mo.tStar) fsPot q A
    (hA.of_imp (fun x hx => by cases x <;> [cases hx; rfl]))
    (by simp [CostedReduction.totalQueries, redFSAuthDFShiftedPaperGenProg, Comp.queries]) ?_ ?_
    (by simp [redFSAuthDFShiftedPaperGenProg, Comp.queries])
  · dsimp only [redFSAuthDFShiftedPaperGenProg]; rw [eval_bind]
    exact (PotOKInvFS.bindPot (initFSEStateC_potOKInv L mo j (.bool false) _ q)
      (fun _ hes => potInvFS_ret (by simpa [Expr.eval, Expr.v0] using hes)
        (by simp [Expr.eval, Expr.v0]))).mono (by omega)
  · intro m qv sv hsv
    exact implECDFShiftedPaperGen_hooksFSC_potOKInv (!authH) L l B Δcka qep maxSkip tStar mo j
      (modeCfgEC OO mo') mo'.policy .v0 .v1
      (.cons sv (.cons qv .nil)) m hsv

end PaperFsPotOK

section AtomicPaperFs

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (ℓ : ℕ) (C : _root_.CryptoGames.LibsignalSession.Crypto)
  (Dh : _root_.CryptoGames.CKA.DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
  (encT : Pt → _root_.CryptoGames.LibsignalSession.PublicKey)
  (idOf : Party → _root_.CryptoGames.LibsignalSession.IdentityKey) (lam : Pt)

theorem redFSAuthDFPaperAtomicProg_makesAtMostQueries
    (qep q j : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : OracleComp (unifSpec + _root_.CryptoGames.SM.specDF (_root_.CryptoGames.Ratchet.LibsignalSim.Fig8St Pt)
      (_root_.CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × _root_.CryptoGames.CBC.Plain ℓ)
      (BitVec 256) (_root_.CryptoGames.Ratchet.LibsignalSim.Fig8C Pt)) Bool)
    (hA : A.IsQueryBoundP (· matches .inr _) q) :
    _root_.CryptoGames.FSAEAD.MakesAtMostQueries
      ((_root_.Computational.Proofs.SessionCostedFig8.DFProgBoundsPaper.redFSAuthDFPaperAtomicProg
        Dh encPt C ℓ encT idOf lam qep q j tL t).eval (fun _ => A) ())
      (min (2 * q) (q + 2)) := by
  unfold _root_.Computational.Proofs.SessionCostedFig8.DFProgBoundsPaper.redFSAuthDFPaperAtomicProg
  exact _root_.Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedPotOK.compileFsDFAtomic_makesAtMostQueries
    ℓ C Dh encPt encT idOf lam
    ((q + 1) * (_root_.CryptoGames.LibsignalSession.maxForwardJumps + 1)) (min (2 * q) (q + 2)) _ A
    (redFSAuthDFPaperProg_makesAtMostQueries (q + 1)
      ((q + 1) * (_root_.CryptoGames.LibsignalSession.maxForwardJumps + 1)) 1 qep
      _root_.CryptoGames.LibsignalSession.maxForwardJumps j tL t q A
      (hA.of_imp (by rintro (_ | _) <;> simp)))

theorem redFSAuthDFCasePaperAtomicProg_makesAtMostQueries
    (qep q j : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : OracleComp (unifSpec + _root_.CryptoGames.SM.specDF (_root_.CryptoGames.Ratchet.LibsignalSim.Fig8St Pt)
      (_root_.CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × _root_.CryptoGames.CBC.Plain ℓ)
      (BitVec 256) (_root_.CryptoGames.Ratchet.LibsignalSim.Fig8C Pt)) Bool)
    (hA : A.IsQueryBoundP (· matches .inr _) q) :
    _root_.CryptoGames.FSAEAD.MakesAtMostQueries
      ((_root_.Computational.Proofs.SessionCostedFig8.DFProgBoundsPaper.redFSAuthDFCasePaperAtomicProg
        Dh encPt C ℓ encT idOf lam qep q j tL t).eval (fun _ => A) ())
      (min (2 * q) (q + 2)) := by
  unfold _root_.Computational.Proofs.SessionCostedFig8.DFProgBoundsPaper.redFSAuthDFCasePaperAtomicProg
  dsimp only
  split
  · exact _root_.Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedPotOK.compileFsDFAtomic_makesAtMostQueries
      ℓ C Dh encPt encT idOf lam
      ((q + 1) * (_root_.CryptoGames.LibsignalSession.maxForwardJumps + 1)) (min (2 * q) (q + 2)) _ A
      (redFSAuthDFShiftedPaperGenProg_makesAtMostQueries
        (q + 1) ((q + 1) * (_root_.CryptoGames.LibsignalSession.maxForwardJumps + 1)) 0 qep
        _root_.CryptoGames.LibsignalSession.maxForwardJumps j (t - 1) t false q A
        (hA.of_imp (by rintro (_ | _) <;> simp)))
  · split
    · exact _root_.Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedPotOK.compileFsDFAtomic_makesAtMostQueries
        ℓ C Dh encPt encT idOf lam
        ((q + 1) * (_root_.CryptoGames.LibsignalSession.maxForwardJumps + 1)) (min (2 * q) (q + 2)) _ A
        (redFSAuthDFShiftedPaperGenProg_makesAtMostQueries
          (q + 1) ((q + 1) * (_root_.CryptoGames.LibsignalSession.maxForwardJumps + 1)) 1 qep
          _root_.CryptoGames.LibsignalSession.maxForwardJumps j (t - 2) t true q A
          (hA.of_imp (by rintro (_ | _) <;> simp)))
    · exact _root_.Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedPotOK.compileFsDFAtomic_makesAtMostQueries
        ℓ C Dh encPt encT idOf lam
        ((q + 1) * (_root_.CryptoGames.LibsignalSession.maxForwardJumps + 1)) (min (2 * q) (q + 2)) _ A
        (redFSAuthDFPaperProg_makesAtMostQueries
          (q + 1) ((q + 1) * (_root_.CryptoGames.LibsignalSession.maxForwardJumps + 1)) 1 qep
          _root_.CryptoGames.LibsignalSession.maxForwardJumps j tL t q A
          (hA.of_imp (by rintro (_ | _) <;> simp)))

end AtomicPaperFs

end

end Computational.Proofs.HeadlineV1.DeliverForgePaperUnshiftedPotOK
