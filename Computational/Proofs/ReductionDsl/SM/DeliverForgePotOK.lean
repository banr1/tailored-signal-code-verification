/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.SM.RedFSPotOK -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.SM.DeliverForge -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.Notation

/-!
# Potential-Based FS-AEAD Query Bounds for `DeliverForge`

Proves the `min (2 * q) (q + 2)` total query bound and `q` decryption query bound for
`redFSAuthDFProg` over `SM.specDF`.
-/

namespace Computational.Proofs.ReductionDsl.SM.DeliverForgePotOK

public section

set_option autoImplicit false

open OracleSpec OracleComp
open _root_.ReductionDsl (Ty Env Expr Comp CostedReduction isGameQuery)
open _root_.CryptoGames.CKA (ckaSMQDF ckaHdrCtTy)
open _root_.CryptoGames.PRFPRNG (prngSig prngOps)
open _root_.CryptoGames.SM (pGet otherE)
open _root_.CryptoGames.SM.Engine
  (ConfigEC Policy modeCfgEC
   cGsSt esG esH esMk esSetG esSetH
   vRecvC commitEC deliverForgeEC implECDF
   eval_bind eval_bind_ret)
open _root_.CryptoGames.SM.Construction
  (Header PartyState Mode
   fsEsTy hooksFSC initFSEStateC fsHdrDecWt
   redFSAuthDFProg redFSAuthDFProg_totalQueries)
open Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks
  (fsEsInv fsPot pGet_eval_st_fs fsVpInv_pGet cGsSetWin_st_fs
   PotOKInvFS potInvFS_ret potInvFS_ite potInvFS_caseOpt potInvFS_caseSum
   vRecvC_hooksFSC_potOKInv)
open Computational.Proofs.ReductionDsl.SM.RedFSPotOK
  (fsEsInv_of_st_eq commitEC_hooksFSC_potOKInv implEC_hooksFSC_potOKInv initFSEStateC_potOKInv
   costedReduction_makesAtMostQueries_fs costedReduction_makesAtMostDecQueries_fs)

section DeliverForgeFsPotOK

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
local notation "P_fs" => isGameQuery (G := CryptoGames.FSAEAD.spec SS RS (Header T) M E)

theorem deliverForgeEC_hooksFSC_potOKInv (L B Δcka qep : ℕ) (mo : Mode) (j : ℕ) (cfg : ConfigEC OO)
    {Γ' : List (Ty S)} (esE : Expr OO Γ' esTyFS)
    (argE : Expr OO Γ' (.prod .bool (.prod hdrCtTy hdrCtTy)))
    (ρ : Env Γ') (m : ℕ) (hInv : fsEsInv mo.tStar (esE.eval ρ)) :
    PotOKInvFS P_fs (fun x => fsEsInv mo.tStar x.2)
      (fun x => m + fsPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) x.2)
      ((deliverForgeEC (hooksFSC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) L B Δcka mo j) L (2 + Δcka) qep cfg esE argE).eval ρ)
      (1 + m + fsPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (esE.eval ρ)) := by
  unfold deliverForgeEC; rw [eval_bind_ret]
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

theorem implECDF_hooksFSC_potOKInv (L B Δcka qep maxSkip : ℕ) (mo : Mode) (j : ℕ)
    (cfg : ConfigEC OO) (π : Policy)
    {Γ' : List (Ty S)} (esE : Expr OO Γ' esTyFS)
    (qE : Expr OO Γ' (ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E))
    (ρ : Env Γ') (m : ℕ) (hInv : fsEsInv mo.tStar (esE.eval ρ)) :
    PotOKInvFS P_fs (fun x => fsEsInv mo.tStar x.2)
      (fun x => m + fsPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) x.2)
      ((implECDF (hooksFSC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) L B Δcka mo j)
        L (2 + Δcka) qep maxSkip cfg π esE qE).eval ρ)
      (1 + m + fsPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (esE.eval ρ)) := by
  unfold implECDF; rw [eval_bind_ret]
  refine potInvFS_caseSum (fun _ _ => ?_) (fun _ _ => ?_)
  · rw [eval_bind]
    exact PotOKInvFS.bindPot
      (implEC_hooksFSC_potOKInv L B Δcka qep maxSkip mo j cfg π (.fst (Expr.v1 (O := OO))) .v0 _ m
        (by simpa [Expr.eval, Expr.v1] using hInv))
      (fun _ h' => potInvFS_ret (by simpa [Expr.eval, Expr.v0] using h')
        (by simp [Expr.eval, Expr.v0]))
  · rw [eval_bind]
    exact PotOKInvFS.bindPot
      (deliverForgeEC_hooksFSC_potOKInv L B Δcka qep mo j cfg (.fst (Expr.v1 (O := OO))) .v0 _ m
        (by simpa [Expr.eval, Expr.v1] using hInv))
      (fun _ h' => potInvFS_ret (by simpa [Expr.eval, Expr.v0] using h')
        (by simp [Expr.eval, Expr.v0]))

theorem redFSAuthDFProg_makesAtMostQueries (L B Δcka qep maxSkip : ℕ) (j : ℕ)
    (tL : Option ℕ) (t q : ℕ)
    (A : OracleComp (unifSpec + _root_.CryptoGames.SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)) Bool)
    (hA : A.IsQueryBoundP (· matches .inr _) q) :
    CryptoGames.FSAEAD.MakesAtMostQueries
      ((redFSAuthDFProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
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
    (redFSAuthDFProg_totalQueries L B Δcka qep maxSkip j tL t q) ?_ ?_
    (by simp [redFSAuthDFProg, Comp.queries])
  · dsimp only [redFSAuthDFProg]; rw [eval_bind]
    exact (PotOKInvFS.bindPot (initFSEStateC_potOKInv L ⟨true, tL, t⟩ j (.bool false) _ q)
      (fun _ hes => potInvFS_ret (by simpa [Expr.eval, Expr.v0] using hes)
        (by simp [Expr.eval, Expr.v0]))).mono (by omega)
  · intro m qv sv hsv
    exact implECDF_hooksFSC_potOKInv L B Δcka qep maxSkip ⟨true, tL, t⟩ j
      (modeCfgEC OO ⟨true, tL, t⟩) (⟨true, tL, t⟩ : Mode).policy .v0 .v1
      (.cons sv (.cons qv .nil)) m hsv

theorem redFSAuthDFProg_makesAtMostDecQueries (L B Δcka qep maxSkip : ℕ) (j : ℕ)
    (tL : Option ℕ) (t q : ℕ)
    (A : OracleComp (unifSpec + _root_.CryptoGames.SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)) Bool)
    (hA : A.IsQueryBoundP (· matches .inr _) q) :
    CryptoGames.FSAEAD.MakesAtMostDecQueries
      ((redFSAuthDFProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
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
    (by simp [CostedReduction.totalQueries, redFSAuthDFProg, Comp.queries])

end DeliverForgeFsPotOK

end

end Computational.Proofs.ReductionDsl.SM.DeliverForgePotOK
