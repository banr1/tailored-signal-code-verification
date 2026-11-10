/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.SM.RedPRNGPotOK -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.SM.DeliverForgePaperPRNG -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.Notation

/-!
# Potential-Based PRF-PRNG Query Bounds for `DeliverForge`

Proves the `min (2 + 2 * q) (q + 3)` PRF-PRNG query bound (`PRFPRNG.MakesAtMostQueries`) for
`redPRNGAuthDFProg` and `redPRNGAuthDFPaperProg`.
-/

namespace Computational.Proofs.ReductionDsl.SM.DeliverForgePaperPRNGPotOK

public section

set_option autoImplicit false

open OracleSpec OracleComp
open _root_.ReductionDsl
  (Sig Ty Ops Iface Env Expr Comp GameCodec CostedReduction isGameQuery)
open _root_.CryptoGames.CKA (ckaSMQ ckaSMQDF ckaHdrCtTy)
open _root_.CryptoGames.PRFPRNG (prngSig prngOps prngIface)
open _root_.CryptoGames.SM (pGet otherE letE_eval orE_eval)
open _root_.CryptoGames.SM.Engine
  (HooksC ConfigEC Policy modeCfgEC
   cGsSt esG esH esAbort esMk esSetG esSetH esSetAbort
   vRecvC commitEC transmitEC challEC deliverEC injectEC implEC
   deliverForgeEC implECDF corrECPaper implECPaper implECDFPaper
   eval_bind eval_bind_ret)
open _root_.CryptoGames.SM.Construction
  (Header PartyState Mode prngHsTy prngEsTy prngRevealC_queries
   hooksPRNGC initPRNGEStateC
   redPRNGAuthDFProg redPRNGAuthDFProg_totalQueries
   redPRNGAuthDFPaperProg redPRNGAuthDFPaperProg_totalQueries)
open Computational.Proofs.ReductionDsl.SM.RedPRNGPotOK
  (prngVpReady prngPot prngOtherPot
   pGet_eval_st_prng prngOtherPot_add_pGet cGsSetWin_st_prng cAfterCorrE_st_prng
   PotOKSPrng potSPrng_ret potSPrng_ite potSPrng_caseOpt potSPrng_caseSum
   ite_fst_eq_prng prngPot_mk_eq potSPrng_comp_const
   PrngHooksSpec hooksPRNGC_spec
   prngVRecvPost vRecvC_potOKS prngCommitECPost commitEC_potOKS
   transmitEC_potOKS challEC_potOKS deliverEC_potOKS injectEC_potOKS implEC_potOKS
   initPRNGEStateC_potOKS costedReduction_makesAtMostQueries_prng)

section DFPrngPotOK

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
local notation "P_prng" => isGameQuery (G := CryptoGames.PRFPRNG.spec RSt I K)

theorem deliverForgeEC_potOKS {B : ℕ} {mo : Mode}
    {hk : HooksC OO II (.base .γ) (.opt (.base .sig)) (.base .ss) (.base .rs) prngHsTy}
    (hhk : PrngHooksSpec B mo hk) (L Δcka qep : ℕ) (cfg : ConfigEC OO)
    {Γ' : List (Ty S)} (esE : Expr OO Γ' prngEsTy)
    (argE : Expr OO Γ' (.prod .bool (.prod hdrCtTy hdrCtTy)))
    (ρ : Env Γ') (m : ℕ) :
    PotOKSPrng P_prng (fun x => m + prngPot mo x.2)
      ((deliverForgeEC hk L (2 + Δcka) qep cfg esE argE).eval ρ)
      (1 + m + prngPot mo (esE.eval ρ)) := by
  unfold deliverForgeEC; rw [eval_bind_ret]
  refine potSPrng_ite (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0])) (fun hNotAbWin => ?_)
  have hab : (esE.eval ρ).2.2 = false := by
    simp [orE_eval, esAbort, Expr.eval, Expr.v0] at hNotAbWin; exact hNotAbWin.1
  refine potSPrng_caseOpt (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0])) (fun r1 _ => ?_)
  refine potSPrng_ite (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v1])) (fun _ => ?_)
  rw [eval_bind]
  set m_other := prngOtherPot mo (esE.eval ρ).1.1 (argE.eval ρ).1
  have hRecv := vRecvC_potOKS hhk (esH (.fst (Expr.v1 (O := OO)))) (esG (.fst .v1))
    (.fst (.snd .v1)) (pGet (cGsSt (esG (.fst .v1))) (.fst (.snd .v1)))
    (.snd (.snd (.snd .v1))) .none
    (.cons r1 (.cons (esE.eval ρ, argE.eval ρ) ρ)) m m_other
  simp only [pGet_eval_st_prng, cGsSt, esG, Expr.eval, Expr.v1,
    Env.get_cons_zero, Env.get_cons_succ] at hRecv
  change PotOKSPrng P_prng
    (prngVRecvPost mo m m_other
      (if ((argE.eval ρ).1 : Bool) then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1)) _ _ at hRecv
  have hSum : m_other +
      prngVpReady mo (if (argE.eval ρ).1 then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1) =
      prngPot mo (esE.eval ρ) := by
    rw [prngOtherPot_add_pGet]; simp [prngPot, hab]
  rw [show 1 + m + prngPot mo (esE.eval ρ) =
      1 + m + m_other +
        prngVpReady mo (if (argE.eval ρ).1 then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1) by omega]
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
            (esG (.fst .v4)) (.fst (.snd .v4)) (pGet (cGsSt (esG (.fst .v4))) (.fst (.snd .v4)))
            (.fst .v0) (.pair (otherE (.fst (.snd .v4)))
              (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
            (.cons tup (.cons resInner (.cons recvOut (.cons r1 (.cons (esE.eval ρ, argE.eval ρ) ρ))))) m
            (by simp [esSetH, esMk, esAbort, Expr.eval, Expr.v0, Expr.v4, hab])
          simp only [esG, Expr.eval, Expr.v0, Expr.v4, Env.get_cons_zero, Env.get_cons_succ] at hCom
          have hPre :
              m + prngOtherPot mo (esE.eval ρ).1.1 (argE.eval ρ).1 + prngVpReady mo tup.1 ≤
                prngVRecvPost mo m m_other
                  (if (argE.eval ρ).1 then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1) recvOut := by
            simp [prngVRecvPost, hSome, hInSome, m_other]
          refine ⟨fun {_} k hk' => (PotOKSPrng.bindPot hCom (fun comOut => ?_)).run k hk' |>.mono hPre⟩
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

theorem implECDF_potOKS {B : ℕ} {mo : Mode}
    {hk : HooksC OO II (.base .γ) (.opt (.base .sig)) (.base .ss) (.base .rs) prngHsTy}
    (hhk : PrngHooksSpec B mo hk) (L Δcka qep maxSkip : ℕ) (cfg : ConfigEC OO) (π : Policy)
    {Γ' : List (Ty S)} (esE : Expr OO Γ' prngEsTy)
    (qE : Expr OO Γ' (ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E))
    (ρ : Env Γ') (m : ℕ) :
    PotOKSPrng P_prng (fun x => m + prngPot mo x.2)
      ((implECDF hk L (2 + Δcka) qep maxSkip cfg π esE qE).eval ρ)
      (1 + m + prngPot mo (esE.eval ρ)) := by
  unfold implECDF; rw [eval_bind_ret]
  refine potSPrng_caseSum (fun _ _ => ?_) (fun _ _ => ?_)
  · rw [eval_bind]
    exact PotOKSPrng.bindPot
      (implEC_potOKS hhk L Δcka qep maxSkip cfg π (.fst (Expr.v1 (O := OO))) .v0 _ m)
      (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0]))
  · rw [eval_bind]
    exact PotOKSPrng.bindPot
      (deliverForgeEC_potOKS hhk L Δcka qep cfg (.fst (Expr.v1 (O := OO))) .v0 _ m)
      (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0]))

theorem redPRNGAuthDFProg_makesAtMostQueries (L B Δcka qep maxSkip : ℕ) (tL : Option ℕ) (t q : ℕ)
    (A : OracleComp (unifSpec + _root_.CryptoGames.SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)) Bool)
    (hA : A.IsQueryBoundP (· matches .inr _) q) :
    (((redPRNGAuthDFProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK)
        L B Δcka qep maxSkip tL t).eval (fun _ => A) ())).IsQueryBoundP
      (· matches .inr _) (min (2 + 2 * q) (q + 3)) := by
  refine costedReduction_makesAtMostQueries_prng _ (prngPot ⟨true, tL, t⟩) q A
    (hA.of_imp (fun x hx => by cases x <;> [cases hx; rfl]))
    (redPRNGAuthDFProg_totalQueries L B Δcka qep maxSkip tL t q) ?_ ?_
    (by simp [redPRNGAuthDFProg, Comp.queries])
  · dsimp only [redPRNGAuthDFProg]; rw [eval_bind]
    exact PotOKSPrng.bindPot (initPRNGEStateC_potOKS ⟨true, tL, t⟩ (.bool false) _ q)
      (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0]))
  · intro m qv sv
    exact implECDF_potOKS (hooksPRNGC_spec B ⟨true, tL, t⟩) L Δcka qep maxSkip
      (modeCfgEC OO ⟨true, tL, t⟩) (⟨true, tL, t⟩ : Mode).policy .v0 .v1 (.cons sv (.cons qv .nil)) m

theorem corrECPaper_potOKS {B : ℕ} {mo : Mode}
    {hk : HooksC OO II (.base .γ) (.opt (.base .sig)) (.base .ss) (.base .rs) prngHsTy}
    (hhk : PrngHooksSpec B mo hk) (L : ℕ) (π : Policy)
    {Γ' : List (Ty S)} (esE : Expr OO Γ' prngEsTy) (pE : Expr OO Γ' .bool)
    (ρ : Env Γ') (m : ℕ) :
    PotOKSPrng P_prng (fun x => m + prngPot mo x.2)
      ((corrECPaper hk L π esE pE).eval ρ)
      (1 + m + prngPot mo (esE.eval ρ)) := by
  unfold corrECPaper; rw [eval_bind_ret]
  refine potSPrng_ite (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0])) (fun _ => ?_)
  refine potSPrng_ite
    (fun _ => potSPrng_ret (by simp [prngPot, esSetAbort, letE_eval, esMk, Expr.eval, Expr.v0]; omega))
    (fun _ => ?_)
  rw [hhk.hReveal, eval_bind]
  refine PotOKSPrng.bindPot
    (potSPrng_comp_const _ _ (m + prngPot mo (esE.eval ρ)) (1 + m + prngPot mo (esE.eval ρ))
      (fun _ => Nat.le_refl _) (by simp [prngRevealC_queries])) (fun _ => ?_)
  exact potSPrng_caseOpt (fun _ => potSPrng_ret (by simp [prngPot, esMk, Expr.eval]))
    (fun _ _ => potSPrng_ret (by
      simp [prngPot, esMk, esAbort, esG, cAfterCorrE_st_prng, Expr.eval, Expr.v2]))

theorem implECPaper_potOKS {B : ℕ} {mo : Mode}
    {hk : HooksC OO II (.base .γ) (.opt (.base .sig)) (.base .ss) (.base .rs) prngHsTy}
    (hhk : PrngHooksSpec B mo hk) (L Δcka qep maxSkip : ℕ) (cfg : ConfigEC OO) (π : Policy)
    {Γ' : List (Ty S)} (esE : Expr OO Γ' prngEsTy)
    (qE : Expr OO Γ' (ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E)) (ρ : Env Γ') (m : ℕ) :
    PotOKSPrng P_prng (fun x => m + prngPot mo x.2)
      ((implECPaper hk L (2 + Δcka) qep maxSkip cfg π esE qE).eval ρ)
      (1 + m + prngPot mo (esE.eval ρ)) := by
  unfold implECPaper; rw [eval_bind_ret]
  refine potSPrng_caseSum (fun _ _ => ?_) (fun _ _ => ?_)
  · refine potSPrng_caseSum (fun _ _ => ?_) (fun _ _ => ?_)
    · refine potSPrng_caseSum (fun _ _ => ?_) (fun _ _ => ?_)
      · refine potSPrng_caseSum (fun _ _ => ?_) (fun _ _ => ?_)
        · rw [eval_bind]; exact PotOKSPrng.bindPot
            (transmitEC_potOKS hhk L Δcka qep π (.fst (Expr.v4 (O := OO))) .v0 _ m)
            (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0]))
        · rw [eval_bind]; exact PotOKSPrng.bindPot
            (challEC_potOKS hhk L Δcka qep cfg π (.fst (Expr.v4 (O := OO))) .v0 _ m)
            (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0]))
      · rw [eval_bind]; exact PotOKSPrng.bindPot
          (deliverEC_potOKS hhk L maxSkip cfg (.fst (Expr.v3 (O := OO))) .v0 _ m)
          (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0]))
    · rw [eval_bind]; exact PotOKSPrng.bindPot
        (injectEC_potOKS hhk L Δcka qep cfg (.fst (Expr.v2 (O := OO))) .v0 _ m)
        (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0]))
  · rw [eval_bind]; exact PotOKSPrng.bindPot
      (corrECPaper_potOKS hhk L π (.fst (Expr.v1 (O := OO))) .v0 _ m)
      (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0]))

theorem implECDFPaper_potOKS {B : ℕ} {mo : Mode}
    {hk : HooksC OO II (.base .γ) (.opt (.base .sig)) (.base .ss) (.base .rs) prngHsTy}
    (hhk : PrngHooksSpec B mo hk) (L Δcka qep maxSkip : ℕ) (cfg : ConfigEC OO) (π : Policy)
    {Γ' : List (Ty S)} (esE : Expr OO Γ' prngEsTy)
    (qE : Expr OO Γ' (ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E))
    (ρ : Env Γ') (m : ℕ) :
    PotOKSPrng P_prng (fun x => m + prngPot mo x.2)
      ((implECDFPaper hk L (2 + Δcka) qep maxSkip cfg π esE qE).eval ρ)
      (1 + m + prngPot mo (esE.eval ρ)) := by
  unfold implECDFPaper; rw [eval_bind_ret]
  refine potSPrng_caseSum (fun _ _ => ?_) (fun _ _ => ?_)
  · rw [eval_bind]
    exact PotOKSPrng.bindPot
      (implECPaper_potOKS hhk L Δcka qep maxSkip cfg π (.fst (Expr.v1 (O := OO))) .v0 _ m)
      (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0]))
  · rw [eval_bind]
    exact PotOKSPrng.bindPot
      (deliverForgeEC_potOKS hhk L Δcka qep cfg (.fst (Expr.v1 (O := OO))) .v0 _ m)
      (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0]))

theorem redPRNGAuthDFPaperProg_makesAtMostQueries (L B Δcka qep maxSkip : ℕ) (tL : Option ℕ) (t q : ℕ)
    (A : OracleComp (unifSpec + _root_.CryptoGames.SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)) Bool)
    (hA : A.IsQueryBoundP (· matches .inr _) q) :
    (((redPRNGAuthDFPaperProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK)
        L B Δcka qep maxSkip tL t).eval (fun _ => A) ())).IsQueryBoundP
      (· matches .inr _) (min (2 + 2 * q) (q + 3)) := by
  refine costedReduction_makesAtMostQueries_prng _ (prngPot ⟨true, tL, t⟩) q A
    (hA.of_imp (fun x hx => by cases x <;> [cases hx; rfl]))
    (redPRNGAuthDFPaperProg_totalQueries L B Δcka qep maxSkip tL t q) ?_ ?_
    (by simp [redPRNGAuthDFPaperProg, Comp.queries])
  · dsimp only [redPRNGAuthDFPaperProg]; rw [eval_bind]
    exact PotOKSPrng.bindPot (initPRNGEStateC_potOKS ⟨true, tL, t⟩ (.bool false) _ q)
      (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0]))
  · intro m qv sv
    exact implECDFPaper_potOKS (hooksPRNGC_spec B ⟨true, tL, t⟩) L Δcka qep maxSkip
      (modeCfgEC OO ⟨true, tL, t⟩) (⟨true, tL, t⟩ : Mode).policy .v0 .v1 (.cons sv (.cons qv .nil)) m

end DFPrngPotOK

end

end Computational.Proofs.ReductionDsl.SM.DeliverForgePaperPRNGPotOK
