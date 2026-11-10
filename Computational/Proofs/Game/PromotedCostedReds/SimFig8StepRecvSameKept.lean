/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.SimFig8StepRecvSameCost

/-!
# Pure and `Kept` Receive Sub-Branch Evaluation Lemmas for `SimFig8`

Proves `.eval` agreement for the pure accept/answer, `Kept` evaluation, seed-decryption, and wire
helper programs used in the `SimFig8` receive step.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.SimFig8StepRecvSameKept

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Var Env Ops Iface Expr Comp
  atomicSig atomicSessionOps fig8SmIface AtomicPureOp
  B PK PtT PlainT lpubV lctT lctV lctOfV fig8CtT fig8CtV fig8CtOfV
  fig8StT fig8StV fig8StOfV fsSendStV fsSendStOfV fsRecvStV fsRecvStOfV
  ckaStV ckaStOfV wireSaltCtV wireSaltCtOfV
  partyToBool boolToParty smRrEnc recvResultEnc)
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart LibsignalCiphertextWithSalt32
  ratchetKeyAdmissible)
open CryptoGames.Ratchet.LibsignalSim (SimFig8C SimState GhostChain pushChain toWire
  fig8Clamp fsClampSim onAcceptPure onAnswerPure)
open CryptoGames.Ratchet.LibsignalSimC (Kept LibsignalToModularSchemeSimState
  predictReceive sentEval)
open CryptoGames.SM (Pos RecvResult partyEnc partyDec posTy posEnc posDec
  orE boolEq isSomeE otherE senderOfE pGet pSet
  ite_eval orE_eval boolEq_eval isSomeE_eval otherE_eval senderOfE_eval
  pGet_eval pSet_eval partyEnc_other)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.E2E (Bytes paramsV1)
open Computational.Proofs.ReductionDsl.Fig8Atomic (salt32V_salt32OfV)
open Computational.Proofs.Game.PromotedCostedReds.SanOracleCore (figS fsS evalCKS)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8LoopAndCost
  (simFullT simFullEnc simFullDec simBaseT simBaseEnc simBaseDec
   simMirT simMirEnc simMirDec simRecT simRecEnc simRecDec
   ghostChainT ghostChainEnc ghostChainDec honestPairEnc honestPairDec
   keptT keptEnc keptDec snapT snapEnc snapDec sentEntryT sentEntryEnc sentEntryDec)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8State
  (sOpPure eval_sOpPure eLet eval_eLet eMapOpt eval_eMapOpt srecPos
   mSafeInjE mSafeInjE_eval mInTransitE mInTransitE_eval mAcceptE mAcceptE_eval
   mChallContainsE mChallContainsE_eval mTrivialE mTrivialE_eval
   ghostAcceptC ghostAcceptC_eval pushChainE eval_pushChainE
   modifyChainAcceptC modifyChainAcceptC_eval
   ssMir ssPq ssPn ssUnackA ssHonest ssChains ssAmb ssStopped ssMk
   ssSetMirWin eval_ssSetMirWin scBase scKept scSent scSnaps)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8Kept
  (eqFig8CAtomicE eqFig8CAtomicE_eval keptEvalAtomicE keptEvalAtomicE_eval
   sentEvalAtomicE sentEvalAtomicE_eval)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8Crypto
  (kDecOutV orElseOptE eval_orElseOptE knownSeedDecryptAtomicFastC
   knownSeedDecryptAtomicFastC_eval_snapEnc
   lctSaltEqOfLctAtomicE lctSaltEqOfLctAtomicE_eval
   injOKAtomicE injOKAtomicE_eval SnapWFProd toWireAtomicE toWireAtomicE_eval)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8SanCoupling (SnapWF)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8StepRecvSameCost
  (onAcceptInpT onAnswerInpT evalCKInpT
   onAccBase onAccQ onAccW onAccIsDel onAccT onAccI onAccM onAccCi? onAccPk onAccPq'
   ssAcceptUpdate onAcceptPureAtomicC onAnsRes onAnswerPureAtomicC
   evalCKSAtomicC inTransitHonestE honestFindE mkCE recvRefuseE)

section RoundTripHelpers

variable {ℓ : ℕ} {Pt : Type}

private theorem fig8CtV_fig8CtOfV (v : (fig8CtT (ℓ := ℓ) (Pt := Pt)).denote) :
    fig8CtV (ℓ := ℓ) (Pt := Pt) (fig8CtOfV v) = v := by
  rcases v with ⟨h, n, ws, sv⟩
  simp [fig8CtV, fig8CtOfV, lctV, lctOfV, wireSaltCtV, wireSaltCtOfV, salt32V_salt32OfV]

private theorem fig8StV_fig8StOfV (v : (fig8StT (ℓ := ℓ) (Pt := Pt)).denote) :
    fig8StV (ℓ := ℓ) (Pt := Pt) (fig8StOfV v) = v := by
  rcases v with ⟨p, rk, vs?, vrTbl, γv, cur?, tc⟩
  simp only [fig8StV, fig8StOfV]
  have hp : partyToBool (boolToParty p) = p := by cases p <;> rfl
  have hvs : (vs?.map (fsSendStOfV (ℓ := ℓ) (Pt := Pt))).map fsSendStV = vs? := by
    rcases vs? with _ | ⟨ck, li⟩ <;> rfl
  have hvr : (fun t => ((vrTbl t).map (fsRecvStOfV (ℓ := ℓ) (Pt := Pt))).map fsRecvStV) =
      vrTbl := by
    funext t; rcases vrTbl t with _ | ⟨ck, li, sk⟩ <;> rfl
  have hγ : ckaStV (ℓ := ℓ) (Pt := Pt) (ckaStOfV γv) = γv := by
    rcases γv with h | x <;> rfl
  rw [hp, hvs, hvr, hγ]

private theorem simMirEnc_simMirDec (v : (simMirT ℓ Pt).denote) :
    simMirEnc (Pt := Pt) (simMirDec v) = v := by
  rcases v with ⟨b, win, ⟨epA, epB⟩, ⟨idA, idB⟩, tL, trs, chall, comp, ⟨maA, maB⟩, leaks, corrs⟩
  simp only [simMirEnc, simMirDec, List.map_map]
  have htr : (simRecEnc (Pt := Pt) ∘ simRecDec :
      (simRecT ℓ Pt).denote → (simRecT ℓ Pt).denote) = id := by
    funext ⟨⟨p, e, i⟩, m, c⟩; cases p <;> rfl
  have hpos : (posEnc ∘ posDec :
      (posTy (S' := atomicSig ℓ Pt)).denote → (posTy (S' := atomicSig ℓ Pt)).denote) = id := by
    funext ⟨p, e, i⟩; cases p <;> rfl
  have hcor : ((fun pe : Party × ℕ => (partyEnc pe.1, pe.2)) ∘
      (fun pe : Bool × ℕ => (partyDec pe.1, pe.2))) = id := by
    funext ⟨p, e⟩; cases p <;> rfl
  simp only [htr, hpos, hcor, List.map_id]

private theorem simBaseEnc_simBaseDec (v : (simBaseT ℓ Pt).denote) :
    simBaseEnc (simBaseDec v) = v := by
  rcases v with ⟨mir, ⟨pqA, pqB⟩, ⟨pnA, pnB⟩, unackA, honest, ⟨chA, chB⟩, amb, stopped⟩
  simp only [simBaseEnc, simBaseDec, simMirEnc_simMirDec, List.map_map]
  have hhon : (honestPairEnc (ℓ := ℓ) (Pt := Pt) ∘ honestPairDec) = id := by
    funext ⟨w, cv⟩; simp [honestPairEnc, honestPairDec, fig8CtV_fig8CtOfV]
  have hgc : (ghostChainEnc (ℓ := ℓ) (Pt := Pt) ∘ ghostChainDec) = id := by
    funext ⟨k, ep, la, sk⟩; rfl
  simp only [hhon, hgc, List.map_id]

private theorem keptEnc_keptDec (v : (keptT ℓ Pt).denote) :
    keptEnc (ℓ := ℓ) (Pt := Pt) (keptDec v) = v := by
  rcases v with ⟨full?, rsTbl⟩
  simp only [keptEnc, keptDec]
  congr 1
  · rcases full? with _ | stv
    · rfl
    · exact congrArg some (fig8StV_fig8StOfV stv)
  · funext t; rcases rsTbl t with _ | ⟨ck, li, sk⟩ <;> rfl

end RoundTripHelpers

section EvalSubLemmas

set_option linter.unusedSectionVars false

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
variable {ℓ : ℕ} {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt}
variable {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

theorem simFullEnc_simFullDec (v : (simFullT ℓ Pt).denote) :
    simFullEnc (simFullDec v) = v := by
  rcases v with ⟨base, ⟨kA, kB⟩, sent, snaps⟩
  simp only [simFullEnc, simFullDec, simBaseEnc_simBaseDec, keptEnc_keptDec, List.map_map]
  have hse : (sentEntryEnc (ℓ := ℓ) (Pt := Pt) ∘ sentEntryDec) = id := by
    funext ⟨cv, ⟨ck, li⟩⟩
    simp [sentEntryEnc, sentEntryDec, fig8CtV_fig8CtOfV, fsSendStV, fsSendStOfV]
  have hsn : (snapEnc (ℓ := ℓ) (Pt := Pt) ∘ snapDec) = id := by
    funext ⟨p, ep, g⟩; cases p <;> rfl
  simp only [hse, hsn, List.map_id]

private theorem ssAcceptUpdate_eval {O' : Ops (atomicSig ℓ Pt)} {Γ : List (Ty (atomicSig ℓ Pt))}
    (sE : Expr O' Γ (simBaseT ℓ Pt)) (qE : Expr O' Γ .bool)
    (mirE : Expr O' Γ (simMirT ℓ Pt))
    (csE : Expr O' Γ (.list (ghostChainT ℓ Pt)))
    (pq'E : Expr O' Γ (B 32)) (ρ : Env Γ)
    (s : SimState Bytes Pt ℓ) (Q : Party)
    (mir' : CryptoGames.SM.GameState Unit (Plain ℓ) Bytes)
    (cs : List GhostChain) (pq' : Bytes)
    (hs : sE.eval ρ = simBaseEnc s)
    (hq : qE.eval ρ = partyToBool Q)
    (hmir : mirE.eval ρ = simMirEnc mir')
    (hcs : csE.eval ρ = cs.map ghostChainEnc)
    (hpq' : pq'E.eval ρ = pq') :
    (ssAcceptUpdate sE qE mirE csE pq'E).eval ρ =
      simBaseEnc
        { s with
          mir := mir'
          chains := Function.update s.chains Q cs
          pq := Function.update s.pq Q pq'
          unackA := s.unackA && Q != Party.A } := by
  unfold ssAcceptUpdate
  cases Q <;>
    simp [ssMk, ssPq, ssPn, ssUnackA, ssHonest, ssChains, ssAmb, ssStopped,
      pSet, hs, hq, hmir, hcs, hpq', simBaseEnc, partyToBool, Function.update,
      Expr.eval, Expr.v0, bne]

theorem onAcceptPureAtomicC_eval (L qep : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (inpE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (onAcceptInpT ℓ Pt))
    (ρ : Env Γ)
    (s : SimState Bytes Pt ℓ) (Q : Party) (w : Bytes) (isDel : Bool)
    (t i : ℕ) (m : Plain ℓ) (ci? : Option ℕ) (Tpk : PublicKey) (pq' : Bytes)
    (hinp : inpE.eval ρ =
      (simBaseEnc s, (partyToBool Q, (w, (isDel, (t, (i, (m, (ci?, (Tpk, pq'))))))))))
    (htrans : s.mir.trans.length ≤ L)
    (hchall : s.mir.chall.length ≤ L)
    (hcomp : s.mir.comp.length ≤ L)
    (hchains : (s.chains Q).length ≤ 5 ∧ ∀ g ∈ s.chains Q, g.skipped.length ≤ 2000) :
    (onAcceptPureAtomicC (Pt := Pt) (ℓ := ℓ) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) L qep inpE).eval ρ =
    pure
      (let (rr, base') := onAcceptPure qep Q w isDel t i m ci? Tpk pq' s
       (rr.map recvResultEnc, simBaseEnc base')) := by
  let AOps := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam
  set vInp : (onAcceptInpT ℓ Pt).denote :=
    (simBaseEnc s, (partyToBool Q, (w, (isDel, (t, (i, (m, (ci?, (Tpk, pq')))))))))
  set cs : List GhostChain := match ci? with
    | some ci => (s.chains Q).modify ci (·.accept i)
    | none => pushChain (s.chains Q) (GhostChain.accept ⟨some Tpk, t, 0, []⟩ i)
  unfold onAcceptPureAtomicC
  change (pure (inpE.eval ρ) >>= fun x0 =>
    (Comp.caseOpt (O := AOps) (I := fig8SmIface ℓ Pt) (onAccCi? .v0)
      (.bind
        (ghostAcceptC (fig8SmIface ℓ Pt)
          (.pair (.some (onAccPk .v0)) (.pair (onAccT .v0) (.pair (.nat 0) .nil)))
          (onAccI .v0))
        (.ret (pushChainE (pGet (ssChains (onAccBase .v1)) (onAccQ .v1)) .v0)))
      (modifyChainAcceptC (fig8SmIface ℓ Pt)
        (pGet (ssChains (onAccBase .v1)) (onAccQ .v1)) .v0 (onAccI .v1))).eval (.cons x0 ρ) >>=
    _) = _
  rw [hinp, pure_bind]
  have hcs_step :
      (Comp.caseOpt (O := AOps) (I := fig8SmIface ℓ Pt) (onAccCi? .v0)
        (.bind
          (ghostAcceptC (fig8SmIface ℓ Pt)
            (.pair (.some (onAccPk .v0)) (.pair (onAccT .v0) (.pair (.nat 0) .nil)))
            (onAccI .v0))
          (.ret (pushChainE (pGet (ssChains (onAccBase .v1)) (onAccQ .v1)) .v0)))
        (modifyChainAcceptC (fig8SmIface ℓ Pt)
          (pGet (ssChains (onAccBase .v1)) (onAccQ .v1)) .v0 (onAccI .v1))).eval
        (.cons vInp ρ) =
      pure (cs.map (ghostChainEnc (ℓ := ℓ) (Pt := Pt))) := by
    rcases ci? with _ | ci
    · dsimp only [cs, Comp.eval, onAccCi?, vInp, Expr.eval, Expr.v0, Env.get_cons_zero]
      have hga := ghostAcceptC_eval (O' := AOps) (fig8SmIface ℓ Pt)
        (.pair (.some (onAccPk .v0)) (.pair (onAccT .v0) (.pair (.nat 0) .nil)))
        (onAccI .v0) (.cons vInp ρ) ⟨some Tpk, t, 0, []⟩ rfl (by simp)
      erw [hga]
      rw [pure_bind]
      dsimp only [Comp.eval, onAccI, vInp, Expr.eval, Expr.v0, Env.get_cons_zero]
      congr 1
      exact eval_pushChainE (O' := AOps)
        (pGet (ssChains (onAccBase .v1)) (onAccQ .v1)) .v0
        (.cons (ghostChainEnc (GhostChain.accept ⟨some Tpk, t, 0, []⟩ i)) (.cons vInp ρ))
        (s.chains Q) (GhostChain.accept ⟨some Tpk, t, 0, []⟩ i)
        (by cases Q <;> rfl) hchains.1 rfl
    · dsimp only [cs, Comp.eval, onAccCi?, vInp, Expr.eval, Expr.v0, Env.get_cons_zero]
      have hmc := modifyChainAcceptC_eval (O' := AOps) (fig8SmIface ℓ Pt)
        (pGet (ssChains (onAccBase .v1)) (onAccQ .v1)) .v0 (onAccI .v1)
        (.cons ci (.cons vInp ρ)) (s.chains Q) (by cases Q <;> rfl) hchains.1 hchains.2
      simpa [onAccI, vInp, Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ]
        using hmc
  erw [hcs_step]
  rw [pure_bind]
  dsimp only [Comp.eval]
  congr 1
  set ρ2 := Env.cons (t := .list (ghostChainT ℓ Pt))
    (cs.map (ghostChainEnc (ℓ := ℓ) (Pt := Pt))) (.cons vInp ρ)
  unfold onAcceptPure
  rw [ite_eval]
  have hisDel : (onAccIsDel (O' := AOps) .v1).eval ρ2 = isDel := rfl
  rw [hisDel]
  cases isDel
  · dsimp only [Bool.false_eq_true, ↓reduceIte]
    rw [ite_eval]
    have hltE : (Expr.lt (O := AOps) (.nat (qep + 1)) (onAccT .v1)).eval ρ2 =
        decide (qep + 1 < t) := rfl
    rw [hltE]
    by_cases hqt : qep + 1 < t
    · simp [hqt, onAccBase, ρ2, vInp, recvResultEnc, Expr.eval, Expr.v1]
    · simp only [hqt, decide_false, Bool.false_eq_true, ↓reduceIte]
      set pos₀ : Pos := ⟨Q.other, t, i⟩
      have hpos : (Expr.pair (O := AOps) (otherE (onAccQ .v1))
          (.pair (onAccT .v1) (onAccI .v1))).eval ρ2 = posEnc pos₀ := by
        cases Q <;> rfl
      have htriv := mTrivialE_eval (O' := AOps) L (ssMir (onAccBase .v1))
        (.pair (otherE (onAccQ .v1)) (.pair (onAccT .v1) (onAccI .v1)))
        ρ2 s.mir pos₀ htrans hcomp rfl hpos
      rw [ite_eval, htriv]
      rcases s.mir.trivial 3 pos₀
      · simp only [Bool.false_eq_true, ↓reduceIte, Option.map, recvResultEnc]
        exact Prod.ext rfl (eval_ssSetMirWin (onAccBase .v1) ρ2 s rfl)
      · simp only [↓reduceIte, Option.map, recvResultEnc]
        have hacc := mAcceptE_eval (O' := AOps) L (ssMir (onAccBase .v1)) (onAccQ .v1)
          (.pair (otherE (onAccQ .v1)) (.pair (onAccT .v1) (onAccI .v1)))
          ρ2 s.mir Q pos₀ htrans hchall hcomp rfl (by cases Q <;> rfl) hpos
        have hupd := ssAcceptUpdate_eval (onAccBase .v1) (onAccQ .v1)
          (mAcceptE L (ssMir (onAccBase .v1)) (onAccQ .v1)
            (.pair (otherE (onAccQ .v1)) (.pair (onAccT .v1) (onAccI .v1))))
          .v0 (onAccPq' .v1) ρ2 s Q (s.mir.accept Q () pos₀) cs pq' rfl rfl hacc rfl rfl
        exact Prod.ext rfl (hupd.trans (by cases ci? <;> rfl))
  · dsimp only [↓reduceIte]
    have htr := mInTransitE_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) L
      (ssMir (onAccBase .v1)) (otherE (onAccQ .v1)) (onAccW .v1)
      ρ2 s.mir Q.other htrans rfl (by cases Q <;> rfl)
    have hcase : ∀ {α β : Ty (atomicSig ℓ Pt)} (o : Expr AOps _ (.opt α))
        (n : Expr AOps _ β) (sm : Expr AOps _ β),
        (Expr.caseOpt o n sm).eval ρ2 = match o.eval ρ2 with
          | none => n.eval ρ2
          | some x => sm.eval (.cons x ρ2) := by
      intro _ _ o _ _; dsimp only [Expr.eval]; cases o.eval ρ2 <;> rfl
    rw [hcase, htr]
    have hwE : (onAccW (O' := AOps) .v1).eval ρ2 = w := rfl
    rw [hwE]
    rcases s.mir.inTransit Q.other w with _ | r
    · rfl
    · dsimp only [Option.map]
      set ρ3 := Env.cons (t := simRecT ℓ Pt) (simRecEnc (ℓ := ℓ) (Pt := Pt) r) ρ2
      have hch := mChallContainsE_eval (O' := AOps) L (ssMir (onAccBase .v2)) (srecPos .v0)
        ρ3 s.mir r.pos hchall rfl rfl
      have hacc := mAcceptE_eval (O' := AOps) L (ssMir (onAccBase .v2)) (onAccQ .v2) (srecPos .v0)
        ρ3 s.mir Q r.pos htrans hchall hcomp rfl (by cases Q <;> rfl) rfl
      have hupd := ssAcceptUpdate_eval (onAccBase .v2) (onAccQ .v2)
        (mAcceptE L (ssMir (onAccBase .v2)) (onAccQ .v2) (srecPos .v0))
        .v1 (onAccPq' .v2) ρ3 s Q (s.mir.accept Q () r.pos) cs pq' rfl rfl hacc rfl rfl
      refine Prod.ext ?_ (hupd.trans (by cases ci? <;> rfl))
      change some (Sum.inr (t, (i, (Expr.ite (mChallContainsE L (ssMir (onAccBase .v2)) (srecPos .v0))
        .none (.some (onAccM .v2))).eval ρ3))) = _
      rw [ite_eval, hch]
      cases s.mir.chall.contains r.pos <;> rfl

theorem onAnswerPureAtomicC_eval (L qep : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (inpE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (onAnswerInpT ℓ Pt))
    (ρ : Env Γ)
    (s : SimState Bytes Pt ℓ) (Q : Party) (w : Bytes) (isDel : Bool)
    (ci? : Option ℕ) (Tpk : PublicKey) (pq' : Bytes)
    (res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)))
    (hinp : inpE.eval ρ =
      (simBaseEnc s, (partyToBool Q, (w, (isDel, (ci?, (Tpk, (pq',
        res.map (smRrEnc fun (pub, m) => (lpubV pub, m))))))))))
    (htrans : s.mir.trans.length ≤ L)
    (hchall : s.mir.chall.length ≤ L)
    (hcomp : s.mir.comp.length ≤ L)
    (hchains : (s.chains Q).length ≤ 5 ∧ ∀ g ∈ s.chains Q, g.skipped.length ≤ 2000) :
    (onAnswerPureAtomicC (Pt := Pt) (ℓ := ℓ) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) L qep inpE).eval ρ =
    pure
      (let (rr, base') := onAnswerPure qep Q w isDel ci? Tpk pq' res s
       (rr.map recvResultEnc, simBaseEnc base')) := by
  unfold onAnswerPureAtomicC onAnswerPure
  dsimp only [Comp.eval]
  rw [hinp, pure_bind]
  rcases res with _ | rr
  · rfl
  · rcases rr with _ | ⟨t, i, pm⟩
    · rfl
    · dsimp only [Option.map, smRrEnc, Comp.eval, onAnsRes, Expr.eval, Expr.v0, Env.get_cons_zero]
      refine onAcceptPureAtomicC_eval L qep _ _ s Q w isDel t i ((pm.map (·.2)).getD default)
        ci? Tpk pq' ?_ htrans hchall hcomp hchains
      rcases pm with _ | ⟨pub, m⟩
      · dsimp only [Option.map, Option.getD, Expr.eval, Env.get_cons_zero]
        rw [eval_sOpPure]
        refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (Prod.ext rfl
          (Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ rfl))))))
        apply List.Vector.toList_injective
        dsimp [AtomicPureOp.eval, default, Inhabited.default]
        simp [List.Vector.replicate, List.Vector.toList_mk]
      · rfl

theorem evalCKSAtomicC_eval (idA idB : IdentityKey) (L B_cap T Kc : ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (inpE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (evalCKInpT ℓ Pt))
    (ρ : Env Γ)
    (sC : LibsignalToModularSchemeSimState Bytes Pt ℓ) (Q : Party) (w : Bytes)
    (c c' : SimFig8C Pt)
    (hinp : inpE.eval ρ = (simFullEnc sC, (partyToBool Q, (w, (fig8CtV c, fig8CtV c')))))
    (hsent : sC.sent.length ≤ L)
    (hsnaps : sC.snaps.length ≤ L)
    (hWF : ∀ e ∈ sC.snaps, SnapWF e.2.2) :
    (evalCKSAtomicC (Pt := Pt) (ℓ := ℓ) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
      idA idB L B_cap T Kc inpE).eval ρ =
    pure
      ((evalCKS (paramsV1 C K idA idB) Dh encPt encT lam T Kc B_cap sC Q w c c').map
        (Option.map (kDecOutV (ℓ := ℓ) (Pt := Pt)))) := by
  unfold evalCKSAtomicC
  dsimp only [Comp.eval]
  rw [hinp, pure_bind]
  set ρ1 := Env.cons (t := evalCKInpT ℓ Pt)
    (simFullEnc sC, (partyToBool Q, (w, (fig8CtV c, fig8CtV c')))) ρ
  have hkget :
      (pGet (scKept (.fst (.v0 : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) _ _)))
        (.fst (.snd .v0))).eval ρ1 = keptEnc (sC.kept Q) := by
    cases Q <;> rfl
  have hke := keptEvalAtomicE_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB T B_cap
    (pGet (scKept (.fst .v0)) (.fst (.snd .v0))) (.snd (.snd (.snd (.snd .v0))))
    ρ1 (sC.kept Q) c' hkget rfl
  have hse := sentEvalAtomicE_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB L T B_cap
    (scSent (.fst .v0)) (.fst (.snd (.snd (.snd .v0)))) (.snd (.snd (.snd (.snd .v0))))
    ρ1 sC.sent c c' rfl rfl rfl hsent
  have hkfun : (fun (x : ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ)) =>
      (x.1, (x.2.1, (lpubV x.2.2.1, x.2.2.2)))) = kDecOutV (ℓ := ℓ) (Pt := Pt) := by
    funext ⟨t, i, p, m⟩; rfl
  have hpred :
      (orElseOptE
        (keptEvalAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
          (decT := decT) (lam := lam) idA idB T B_cap
          (pGet (scKept (.fst .v0)) (.fst (.snd .v0))) (.snd (.snd (.snd (.snd .v0)))))
        (sentEvalAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
          (decT := decT) (lam := lam) idA idB L B_cap
          (scSent (.fst .v0)) (.fst (.snd (.snd (.snd .v0))))
          (.snd (.snd (.snd (.snd .v0)))))).eval ρ1 =
      (predictReceive
        (fig := fig8Clamp B_cap (figS (paramsV1 C K idA idB) Dh encPt encT lam T))
        (fs := fsClampSim B_cap (fsS (paramsV1 C K idA idB) encT T))
        sC Q c c').map (Option.map (kDecOutV (ℓ := ℓ) (Pt := Pt))) := by
    rw [eval_orElseOptE, hke, hse, hkfun]
    unfold predictReceive
    cases Kept.eval
      (fig := fig8Clamp B_cap (figS (paramsV1 C K idA idB) Dh encPt encT lam T))
      (fs := fsClampSim B_cap (fsS (paramsV1 C K idA idB) encT T))
      c' (sC.kept Q) <;> rfl
  rw [hpred]
  unfold evalCKS
  rcases hp : predictReceive
      (fig := fig8Clamp B_cap (figS (paramsV1 C K idA idB) Dh encPt encT lam T))
      (fs := fsClampSim B_cap (fsS (paramsV1 C K idA idB) encT T))
      sC Q c c' with _ | r
  · simp only [Option.map, Option.orElse]
    exact knownSeedDecryptAtomicFastC_eval_snapEnc idA idB L Kc B_cap (fig8SmIface ℓ Pt)
      (scSnaps (.fst .v0)) (.fst (.snd .v0)) (.fst (.fst (.fst (.snd (.snd (.snd .v0))))))
      (.fst (.snd (.snd .v0))) (.snd (.snd (.snd (.snd .v0)))) ρ1
      sC.snaps Q c.1.1 w c' rfl hsnaps (by cases Q <;> rfl) rfl rfl rfl
      (fun e he => hWF e he)
  · rfl

private theorem any_and_wire_eq_local {α β : Type} [DecidableEq β]
    (l : List (α × β)) (c₀ : β) (p : α → Bool) (f : β → α)
    (h : ∀ wc ∈ l, wc.1 = f wc.2) :
    ((l.any fun wc => decide (wc.2 = c₀)) && p (f c₀)) =
      (l.any fun wc => decide (wc.2 = c₀) && p wc.1) := by
  induction l with
  | nil => rfl
  | cons wc tl ih =>
    have hwc : (decide (wc.2 = c₀) && p wc.1) = (decide (wc.2 = c₀) && p (f c₀)) := by
      by_cases heq : wc.2 = c₀
      · rw [decide_eq_true heq, h wc (.head _), heq]
      · simp [heq]
    have htl := ih (fun x hx => h x (.tail _ hx))
    simp only [List.any_cons, hwc, ← htl]
    cases decide (wc.2 = c₀) <;> cases (tl.any fun x => decide (x.2 = c₀)) <;> cases p (f c₀) <;> rfl

theorem inTransitHonestE_eval (L : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (sCE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (simFullT ℓ Pt))
    (qBE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ .bool)
    (c'E : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (fig8CtT (ℓ := ℓ) (Pt := Pt)))
    (ρ : Env Γ)
    (sC : LibsignalToModularSchemeSimState Bytes Pt ℓ) (Q : Party) (c' : SimFig8C Pt)
    (hsC : sCE.eval ρ = simFullEnc sC)
    (hqB : qBE.eval ρ = partyToBool Q)
    (hc' : c'E.eval ρ = fig8CtV c')
    (hhon : sC.base.honest.length ≤ L)
    (htrans : sC.base.mir.trans.length ≤ L)
    (hhonWire : ∀ wc ∈ sC.base.honest, wc.1 = toWire wc.2) :
    (inTransitHonestE (Pt := Pt) (ℓ := ℓ) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) L sCE qBE c'E).eval ρ =
    (sC.base.honest.any fun wc =>
      decide (wc.2 = c') && (sC.base.mir.inTransit Q.other wc.1).isSome) := by
  rw [← any_and_wire_eq_local sC.base.honest c'
    (fun w => (sC.base.mir.inTransit Q.other w).isSome) toWire hhonWire]
  unfold inTransitHonestE
  rw [eval_eLet]
  have hp : (Expr.pair sCE (.pair qBE c'E)).eval ρ =
      (simFullEnc sC, (partyToBool Q, fig8CtV c')) := by
    simp [Expr.eval, hsC, hqB, hc']
  rw [hp]
  set ρ1 := Env.cons (t := .prod (simFullT ℓ Pt) (.prod .bool (fig8CtT (ℓ := ℓ) (Pt := Pt))))
    (simFullEnc sC, (partyToBool Q, fig8CtV c')) ρ
  have hand1 : ∀ (a b : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) _ .bool),
      (Expr.and a b).eval ρ1 = (a.eval ρ1 && b.eval ρ1) := fun _ _ => rfl
  rw [hand1]
  have hany : (Expr.anyB L (ssHonest (scBase (.fst .v0)))
      (eqFig8CAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) (.snd .v0) (.snd (.snd .v1)))).eval ρ1 =
      (sC.base.honest.any fun wc => decide (wc.2 = c')) := by
    have hlist : (ssHonest (scBase (.fst (.v0 : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) _ _)))).eval ρ1 =
        sC.base.honest.map (honestPairEnc (ℓ := ℓ) (Pt := Pt)) := rfl
    have htake : (sC.base.honest.map (honestPairEnc (ℓ := ℓ) (Pt := Pt))).take L =
        sC.base.honest.map (honestPairEnc (ℓ := ℓ) (Pt := Pt)) :=
      List.take_of_length_le (by simpa using hhon)
    change (((ssHonest (scBase (.fst .v0))).eval ρ1).take L).any
        (fun x => (eqFig8CAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam) (.snd .v0) (.snd (.snd .v1))).eval (.cons x ρ1)) = _
    rw [hlist, htake, List.any_map]
    congr 1; funext ⟨w0, c0⟩
    dsimp only [Function.comp]
    exact eqFig8CAtomicE_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) (.snd .v0) (.snd (.snd .v1))
      (.cons (t := .prod (B 32) (fig8CtT (ℓ := ℓ) (Pt := Pt))) (honestPairEnc (w0, c0)) ρ1)
      c0 c' rfl rfl
  have htw := toWireAtomicE_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (.snd (.snd .v0)) ρ1 c' rfl
  have htr := mInTransitE_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) L
    (ssMir (scBase (.fst .v0))) (otherE (.fst (.snd .v0))) (toWireAtomicE (.snd (.snd .v0)))
    ρ1 sC.base.mir Q.other htrans rfl (by cases Q <;> rfl)
  rw [hany, isSomeE_eval, htr, htw]
  cases sC.base.mir.inTransit Q.other (toWire c') <;> rfl

private theorem list_find?_map_local {α β : Type} (f : α → β) (p : β → Bool) :
    ∀ xs : List α, (xs.map f).find? p = (xs.find? (fun x => p (f x))).map f
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, List.find?_cons]
    cases p (f x) <;> simp [list_find?_map_local]

theorem honestFindE_eval (L : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (sCE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (simFullT ℓ Pt))
    (qBE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ .bool)
    (wE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (B 32))
    (ρ : Env Γ)
    (sC : LibsignalToModularSchemeSimState Bytes Pt ℓ) (Q : Party) (w : Bytes)
    (hsC : sCE.eval ρ = simFullEnc sC)
    (hqB : qBE.eval ρ = partyToBool Q)
    (hw : wE.eval ρ = w)
    (hhon : sC.base.honest.length ≤ L) :
    (honestFindE (Pt := Pt) (ℓ := ℓ) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) L sCE qBE wE).eval ρ =
    ((sC.base.honest.find? fun wc =>
      wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map fig8CtV := by
  unfold honestFindE
  rw [eval_eLet, eval_eMapOpt]
  have hp : (Expr.pair sCE (.pair qBE wE)).eval ρ =
      (simFullEnc sC, (partyToBool Q, w)) := by
    simp [Expr.eval, hsC, hqB, hw]
  rw [hp]
  have htake : (sC.base.honest.map (honestPairEnc (ℓ := ℓ) (Pt := Pt))).take L =
      sC.base.honest.map (honestPairEnc (ℓ := ℓ) (Pt := Pt)) :=
    List.take_of_length_le (by simpa using hhon)
  have hfind :
      (Expr.findB (O := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) L
        (ssHonest (scBase (.fst .v0)))
        (.and
          (sOpPure (.bytesEq 32 32) (.pair (.fst .v0) (.snd (.snd .v1))))
          (boolEq (senderOfE (.fst (.fst (.snd .v0)))) (otherE (.fst (.snd .v1)))))).eval
        (.cons (simFullEnc sC, (partyToBool Q, w)) ρ) =
      (sC.base.honest.find? fun wc =>
        wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map honestPairEnc := by
    dsimp only [Expr.eval, scBase, ssHonest, simFullEnc, simBaseEnc, Expr.v0, Env.get_cons_zero]
    rw [htake, list_find?_map_local]
    congr 2; funext ⟨w0, c0⟩
    simp only [Expr.eval, eval_sOpPure, AtomicPureOp.eval, boolEq_eval, senderOfE_eval,
      otherE_eval, honestPairEnc, fig8CtV, Expr.v1, Env.get_cons_zero, Env.get_cons_succ]
    cases Party.senderOf c0.1.1 <;> cases Q <;> rfl
  rw [hfind]
  simp only [Option.map_map]
  congr 1

theorem mkCE_eval {Γ : List (Ty (atomicSig ℓ Pt))}
    (honestCE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ
      (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))))
    (tE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ .nat)
    (T?E : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (.opt PtT))
    (lctE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (lctT (ℓ := ℓ) (Pt := Pt)))
    (ρ : Env Γ)
    (honestC : Option (SimFig8C Pt)) (t : ℕ) (T? : Option Pt)
    (lct : ℕ × LibsignalCiphertextWithSalt32)
    (hhonC : honestCE.eval ρ = honestC.map fig8CtV)
    (ht : tE.eval ρ = t)
    (hT? : T?E.eval ρ = T?)
    (hlct : lctE.eval ρ = lctV lct) :
    (mkCE (Pt := Pt) (ℓ := ℓ) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
      honestCE tE T?E lctE).eval ρ =
    fig8CtV
      (match honestC with
       | some c => if c.2.2.2 = lct.2.2 then c else ((t, T?), lct)
       | none => ((t, T?), lct)) := by
  unfold mkCE
  rw [eval_eLet]
  have hp : (Expr.pair honestCE (.pair (.pair tE T?E) lctE)).eval ρ =
      (honestC.map fig8CtV, ((t, T?), lctV lct)) := by
    simp [Expr.eval, hhonC, ht, hT?, hlct]
  rw [hp]
  rcases honestC with _ | c
  · rfl
  · dsimp only [Option.map]
    set ρ1 := Env.cons
      (t := .prod (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt)))
        (.prod (.prod .nat (.opt PtT)) (lctT (ℓ := ℓ) (Pt := Pt))))
      (some (fig8CtV c), ((t, T?), lctV lct)) ρ
    set ρ2 := Env.cons (t := fig8CtT (ℓ := ℓ) (Pt := Pt)) (fig8CtV c) ρ1
    have hsalt := lctSaltEqOfLctAtomicE_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) .v0 (.snd (.snd .v1))
      ρ2 c lct rfl rfl
    change (if (lctSaltEqOfLctAtomicE .v0 (.snd (.snd .v1))).eval ρ2 = true
      then (Expr.v0 : Expr _ _ _).eval ρ2
      else (Expr.snd .v1).eval ρ2) = _
    rw [hsalt]
    by_cases hs : c.2.2.2 = lct.2.2 <;> simp [hs, ρ2, ρ1, fig8CtV, Expr.eval, Expr.v0, Expr.v1]

theorem recvRefuseE_eval (L : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (sCE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (simFullT ℓ Pt))
    (qBE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ .bool)
    (wE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (B 32))
    (isDelE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ .bool)
    (ρ : Env Γ)
    (sC : LibsignalToModularSchemeSimState Bytes Pt ℓ) (Q : Party) (w : Bytes) (isDel : Bool)
    (hsC : sCE.eval ρ = simFullEnc sC)
    (hqB : qBE.eval ρ = partyToBool Q)
    (hw : wE.eval ρ = w)
    (hisDel : isDelE.eval ρ = isDel)
    (htrans : sC.base.mir.trans.length ≤ L) :
    (recvRefuseE (Pt := Pt) (ℓ := ℓ) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) L sCE qBE wE isDelE).eval ρ =
    (sC.base.stopped || sC.base.mir.win ||
      (isDel && (sC.base.mir.inTransit Q.other w).isNone) ||
      (!isDel && ((sC.base.mir.inTransit Q.other w).isSome || !(sC.base.mir.safeInj 3) ||
        !(ratchetKeyAdmissible protoSignalCodec decT encT w)))) := by
  unfold recvRefuseE
  rw [eval_eLet]
  have hp : (Expr.pair sCE (.pair qBE (.pair wE isDelE))).eval ρ =
      (simFullEnc sC, (partyToBool Q, (w, isDel))) := by
    simp [Expr.eval, hsC, hqB, hw, hisDel]
  rw [hp]
  set ρ1 := Env.cons (t := .prod (simFullT ℓ Pt) (.prod .bool (.prod (B 32) .bool)))
    (simFullEnc sC, (partyToBool Q, (w, isDel))) ρ
  have htr := mInTransitE_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) L
    (ssMir (scBase (.fst .v0))) (otherE (.fst (.snd .v0))) (.fst (.snd (.snd .v0)))
    ρ1 sC.base.mir Q.other htrans rfl (by cases Q <;> rfl)
  have hsi := mSafeInjE_eval (O' := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
    (ssMir (scBase (.fst .v0))) ρ1 sC.base.mir rfl
  have hstop : (ssStopped (scBase (.fst (.v0 : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) _ _)))).eval ρ1 =
      sC.base.stopped := rfl
  have hwin : (Expr.fst (.snd (ssMir (scBase (.fst (.v0 : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) _ _)))))).eval ρ1 =
      sC.base.mir.win := rfl
  have hisDel1 : (Expr.snd (.snd (.snd (.v0 : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) _ _)))).eval ρ1 =
      isDel := rfl
  have hinj : (injOKAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) (.fst (.snd (.snd .v0)))).eval ρ1 =
      ratchetKeyAdmissible protoSignalCodec decT encT w := by
    rw [injOKAtomicE_eval]; rfl
  have htr' : (isSomeE (mInTransitE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) L
      (ssMir (scBase (.fst .v0))) (otherE (.fst (.snd .v0))) (.fst (.snd (.snd .v0))))).eval ρ1 =
      (sC.base.mir.inTransit Q.other w).isSome := by
    rw [isSomeE_eval, htr]
    have hw1 : (Expr.fst (.snd (.snd (.v0 : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) _ _)))).eval ρ1 =
        w := rfl
    rw [hw1]
    cases sC.base.mir.inTransit Q.other w <;> rfl
  have hand : ∀ (a b : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) _ .bool),
      (Expr.and a b).eval ρ1 = (a.eval ρ1 && b.eval ρ1) := fun _ _ => rfl
  have hnot : ∀ (a : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) _ .bool),
      (Expr.not a).eval ρ1 = !(a.eval ρ1) := fun _ => rfl
  simp only [orE_eval, hand, hnot, hstop, hwin, hisDel1, htr', hsi, hinj]
  rcases sC.base.mir.inTransit Q.other w with _ | r <;> simp [Bool.or_assoc]

end EvalSubLemmas

end Computational.Proofs.Game.PromotedCostedReds.SimFig8StepRecvSameKept
