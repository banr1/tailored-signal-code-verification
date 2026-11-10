/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeStepSendCorrCost

/-!
# Send and Corrupt Step Equivalence for `SimDeliverForge`

Proves semantic `.eval` equivalence for the atomic `.send` and `.corrupt` step computations of
`SimDeliverForge` against `simDeliverForgeOracleSan`.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeStepSendCorr

open OracleSpec OracleComp
open _root_.ReductionDsl (Ty Expr Comp Ops Env bits atomicSig atomicSessionOps fig8SmIfaceDF
  GhostStT PlainT BV256 BV512 U32 B smRT smRdec
  fig8CtT fig8CtV fig8CtOfV fig8StT fig8StV fig8StOfV
  lpubT lpubV lpubOfV ckaStT fsSendStT fsSendStV fsSendStOfV
  partyToBool boolToParty)
open _root_.CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart lFig8)
open CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C SimState GhostChain SimCStateBounded
  mkPub toWire toGhost simToGhost_eq scPostSendPure semDrawSendCoins semSendHook deliverForgeSemHook)
open CryptoGames.Ratchet.LibsignalSimC (Kept LibsignalToModularSchemeSimState)
open CryptoGames.SM (Pos Record GameState partyEnc partyDec posTy posEnc posDec
  pGet pSet sendsInE sendsInE_eval)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey GhostState)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.LibsignalSession (ratchetCostBudget)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.E2E (Bytes paramsV1)
open Computational.Proofs.ReductionDsl.Fig8Atomic (salt32V_salt32OfV)
open Computational.Proofs.Game.PromotedCostedReds.SanOracleCore
  (semCorrHookTGB fig8StTruncSkB figS fig8San)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8SanCoupling (SanSnapExtra)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8LoopAndCost
  (simFullT simFullEnc simFullDec simFullDec_simFullEnc
   simMirT simMirEnc simMirDec
   simBaseT simBaseEnc simBaseDec
   ghostChainT ghostChainEnc ghostChainDec
   keptT keptEnc keptDec
   snapT snapEnc snapDec
   sentEntryT sentEntryEnc sentEntryDec
   honestPairEnc honestPairDec
   simRecT simRecEnc simRecDec simRecEnc_simRecDec
   fig8CtOfV_fig8CtV fsSendStOfV_fsSendStV fig8StTruncSk)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8State
  (sOpPure sOpPtEnc sOpGrp eval_sOpPure eval_sOpPtEnc eval_sOpGrp eval_eLet
   mWin mEpoch mIdx mSafeChE mSafeChE_eval mEpMgmtE mEpMgmtE_eval mRecordE mRecordE_eval
   mCorrAllowedFastE mCorrAllowedFastE_eval mAfterCorrFastE mAfterCorrFastE_eval
   mInWinE mInWinE_eval mNoBobEpoch0E mNoBobEpoch0E_eval mNoSpkCorrE mNoSpkCorrE_eval
   revealSpkChainsE eval_revealSpkChainsE toGhostE eval_toGhostE
   ssMir ssPq ssPn ssUnackA ssHonest ssChains ssAmb ssStopped ssMk
   scBase scKept scSent scSnaps scMk)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8WireSnap
  (optBytesLitE optBytesLitE_eval mkPubAtomicC_eval toWireAtomicE toWireAtomicE_eval)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8Kept
  (f8Id f8VS f8Gamma f8Tcur keptOfStAtomicE keptOfStAtomicE_eval
   keptSendAtomicE keptSendAtomicE_eval)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost
  (atomicSessionOpDescBits atomicExprDescBits atomicCompDescBits)
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeStepSendCorrCost
  (dfOrE dfIsSomeE dfNatNeE dfSmRNoneE dfSmRSendSomeE dfSmRCorrSomeE
   dfIdxPredU32E dfDrawSendCoinsC dfPostSendArgT dfPostSendStateE dfSendInpT dfSendStepC
   dfPostCorrStateE dfCorrStepC
   dfSendStepC_queries dfCorrStepC_queries
   dfSendStepC_cost dfCorrStepC_cost dfSendStepC_descBits_le dfCorrStepC_descBits_le)

noncomputable section

@[reducible] def dfSendCorrStateT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  SimDeliverForgeStepSendCorrCost.dfSendCorrStateT ℓ Pt

@[reducible] def dfSendCorrStateDec {ℓ : ℕ} {Pt : Type} (v : (dfSendCorrStateT ℓ Pt).denote) :
    LibsignalToModularSchemeSimState Bytes Pt ℓ × List (Fig8C Pt) :=
  SimDeliverForgeStepSendCorrCost.dfSendCorrStateDec v

/-- Specification bundle for the atomic `.send` and `.corrupt` step branches of `SimDeliverForge`. -/
structure SimDeliverForgeSendCorrSpec (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) where
  sendC : ∀ {Γ : List (Ty (atomicSig ℓ Pt))},
    Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (dfSendCorrStateT ℓ Pt) →
    Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ .bool →
    Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ PlainT →
    Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (.opt PlainT) →
    Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (.opt BV512) →
    Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIfaceDF ℓ Pt) Γ
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (dfSendCorrStateT ℓ Pt))
  corrC : ∀ {Γ : List (Ty (atomicSig ℓ Pt))},
    Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (dfSendCorrStateT ℓ Pt) →
    Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ .bool →
    Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIfaceDF ℓ Pt) Γ
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (dfSendCorrStateT ℓ Pt))
  hsend_q : ∀ {Γ} stE qE m0E chalE rE,
    (sendC (Γ := Γ) stE qE m0E chalE rE).queries (fun _ => 1) (fun _ => 0) ≤ 1
  hcorr_q : ∀ {Γ} stE qE,
    (corrC (Γ := Γ) stE qE).queries (fun _ => 1) (fun _ => 0) ≤ 1
  hsend_c : ℓ < 10 ^ 6 → ∀ {Γ} stE qE m0E chalE rE,
    (sendC (Γ := Γ) stE qE m0E chalE rE).cost ≤
      stE.cost + qE.cost + m0E.cost + chalE.cost + rE.cost +
        20000000 + 30000000 * q + 512 * bits (qep + 1)
  hcorr_c : ℓ < 10 ^ 6 → ∀ {Γ} stE qE,
    (corrC (Γ := Γ) stE qE).cost ≤
      stE.cost + qE.cost + 20000000 + 30000000 * q
  hsend_d : ℓ < 10 ^ 6 → ∀ {Γ} stE qE m0E chalE rE,
    atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8)
        (sendC (Γ := Γ) stE qE m0E chalE rE) ≤
      8 * (atomicExprDescBits atomicSessionOpDescBits stE +
           atomicExprDescBits atomicSessionOpDescBits qE +
           atomicExprDescBits atomicSessionOpDescBits m0E +
           atomicExprDescBits atomicSessionOpDescBits chalE +
           atomicExprDescBits atomicSessionOpDescBits rE) +
        2 ^ 18 + 2 ^ 10 * bits (ratchetCostBudget q (qep + 1) + (qep + 1))
  hcorr_d : ℓ < 10 ^ 6 → ∀ {Γ} stE qE,
    atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8)
        (corrC (Γ := Γ) stE qE) ≤
      8 * (atomicExprDescBits atomicSessionOpDescBits stE +
           atomicExprDescBits atomicSessionOpDescBits qE) +
        2 ^ 18 + 2 ^ 10 * bits (ratchetCostBudget q (qep + 1) + (qep + 1))
  hsend_eval : ℓ < 10 ^ 6 → ∀ {Γ} stE qE m0E chalE rE (ρ : Env Γ) (Q : Party),
    qE.eval ρ = partyEnc Q →
    SimCStateBounded q (dfSendCorrStateDec (stE.eval ρ)).1 →
    SanSnapExtra C K (dfSendCorrStateDec (stE.eval ρ)).1 →
    (Prod.map (fun r => r.1) dfSendCorrStateDec <$>
      (sendC stE qE m0E chalE rE).eval ρ) =
    semSendHook (paramsV1 C K idA idB) Dh encPt encT lam
      (deliverForgeSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ))
      qep (dfSendCorrStateDec (stE.eval ρ)).1 (dfSendCorrStateDec (stE.eval ρ)).2
      Q (m0E.eval ρ) (chalE.eval ρ) (rE.eval ρ)
  hcorr_eval : ℓ < 10 ^ 6 → ∀ {Γ} stE qE (ρ : Env Γ) (Q : Party),
    qE.eval ρ = partyEnc Q →
    SimCStateBounded q (dfSendCorrStateDec (stE.eval ρ)).1 →
    SanSnapExtra C K (dfSendCorrStateDec (stE.eval ρ)).1 →
    (Prod.map (fun r => r.2.2) dfSendCorrStateDec <$>
      (corrC stE qE).eval ρ) =
    semCorrHookTGB (paramsV1 C K idA idB) Dh encT
      (deliverForgeSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ))
      (25000 * q) (dfSendCorrStateDec (stE.eval ρ)).1 (dfSendCorrStateDec (stE.eval ρ)).2 Q

private theorem boolToParty_partyEnc (Q : Party) :
    boolToParty (partyEnc Q) = Q := by
  cases Q <;> rfl

private theorem fig8CtV_fig8CtOfV {ℓ : ℕ} {Pt : Type}
    (v : (fig8CtT (ℓ := ℓ) (Pt := Pt)).denote) :
    fig8CtV (ℓ := ℓ) (Pt := Pt) (fig8CtOfV v) = v := by
  rcases v with ⟨h, n, ws, sv⟩
  simp [fig8CtV, fig8CtOfV, _root_.ReductionDsl.lctV, _root_.ReductionDsl.lctOfV,
    _root_.ReductionDsl.wireSaltCtV, _root_.ReductionDsl.wireSaltCtOfV, salt32V_salt32OfV]

private theorem fig8StV_fig8StOfV {ℓ : ℕ} {Pt : Type}
    (v : (fig8StT (ℓ := ℓ) (Pt := Pt)).denote) :
    fig8StV (ℓ := ℓ) (Pt := Pt) (fig8StOfV v) = v := by
  rcases v with ⟨p, rk, vs?, vrTbl, γv, cur?, tc⟩
  simp only [fig8StV, fig8StOfV]
  have hp : partyToBool (boolToParty p) = p := by cases p <;> rfl
  have hvs : (vs?.map (fsSendStOfV (ℓ := ℓ) (Pt := Pt))).map fsSendStV = vs? := by
    rcases vs? with _ | ⟨ck, li⟩ <;> rfl
  have hvr : (fun t => ((vrTbl t).map (_root_.ReductionDsl.fsRecvStOfV (ℓ := ℓ) (Pt := Pt))).map
      _root_.ReductionDsl.fsRecvStV) = vrTbl := by
    funext t; rcases vrTbl t with _ | ⟨ck, li, sk⟩ <;> rfl
  have hγ : _root_.ReductionDsl.ckaStV (ℓ := ℓ) (Pt := Pt)
      (_root_.ReductionDsl.ckaStOfV γv) = γv := by
    rcases γv with h | x <;> rfl
  rw [hp, hvs, hvr, hγ]

private theorem simMirEnc_simMirDec {ℓ : ℕ} {Pt : Type}
    (v : (simMirT ℓ Pt).denote) :
    simMirEnc (Pt := Pt) (simMirDec v) = v := by
  rcases v with ⟨b, win, ⟨epA, epB⟩, ⟨idA, idB⟩, tL, trs, chall, comp, ⟨maA, maB⟩, leaks, corrs⟩
  simp only [simMirEnc, simMirDec, List.map_map]
  have htr : (simRecEnc (Pt := Pt) ∘ simRecDec :
      (simRecT ℓ Pt).denote → (simRecT ℓ Pt).denote) = id := by
    funext ⟨⟨p, e, i⟩, m, c⟩
    cases p <;> rfl
  have hpos : (posEnc ∘ posDec :
      (posTy (S' := atomicSig ℓ Pt)).denote → (posTy (S' := atomicSig ℓ Pt)).denote) = id := by
    funext ⟨p, e, i⟩; cases p <;> rfl
  have hcor : ((fun pe : Party × ℕ => (partyEnc pe.1, pe.2)) ∘
      (fun pe : Bool × ℕ => (partyDec pe.1, pe.2))) = id := by
    funext ⟨p, e⟩; cases p <;> rfl
  simp only [htr, hpos, hcor, List.map_id]

private theorem simBaseEnc_simBaseDec {ℓ : ℕ} {Pt : Type}
    (v : (simBaseT ℓ Pt).denote) :
    simBaseEnc (simBaseDec v) = v := by
  rcases v with ⟨mir, ⟨pqA, pqB⟩, ⟨pnA, pnB⟩, unackA, honest, ⟨chA, chB⟩, amb, stopped⟩
  simp only [simBaseEnc, simBaseDec, simMirEnc_simMirDec, List.map_map]
  have hhon : (honestPairEnc (ℓ := ℓ) (Pt := Pt) ∘ honestPairDec) = id := by
    funext ⟨w, cv⟩; simp [honestPairEnc, honestPairDec, fig8CtV_fig8CtOfV]
  have hgc : (ghostChainEnc (ℓ := ℓ) (Pt := Pt) ∘ ghostChainDec) = id := by
    funext ⟨k, ep, la, sk⟩; rfl
  simp only [hhon, hgc, List.map_id]

private theorem keptEnc_keptDec {ℓ : ℕ} {Pt : Type} (v : (keptT ℓ Pt).denote) :
    keptEnc (ℓ := ℓ) (Pt := Pt) (keptDec v) = v := by
  rcases v with ⟨full?, rsTbl⟩
  simp only [keptEnc, keptDec]
  congr 1
  · rcases full? with _ | stv
    · rfl
    · exact congrArg some (fig8StV_fig8StOfV stv)
  · funext t; rcases rsTbl t with _ | ⟨ck, li, sk⟩ <;> rfl

private theorem simFullEnc_simFullDec {ℓ : ℕ} {Pt : Type}
    (v : (simFullT ℓ Pt).denote) :
    simFullEnc (simFullDec v) = v := by
  rcases v with ⟨base, ⟨kA, kB⟩, sent, snaps⟩
  simp only [simFullEnc, simFullDec, simBaseEnc_simBaseDec, keptEnc_keptDec, List.map_map]
  have hse : (sentEntryEnc (ℓ := ℓ) (Pt := Pt) ∘ sentEntryDec) = id := by
    funext ⟨cv, ⟨ck, li⟩⟩
    simp [sentEntryEnc, sentEntryDec, fig8CtV_fig8CtOfV, fsSendStV, fsSendStOfV]
  have hsn : (snapEnc (ℓ := ℓ) (Pt := Pt) ∘ snapDec) = id := by
    funext ⟨p, ep, g⟩; cases p <;> rfl
  simp only [hse, hsn, List.map_id]

private theorem kept_send_figS_eq {ℓ : ℕ} {Pt : Type} [Zero Pt]
    (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt)
    (k : Kept Pt) :
    Kept.send (ℓ := ℓ)
      (fig := figS (ℓ := ℓ) (paramsV1 C K idA idB) Dh encPt encT lam 0) k =
    Kept.send (ℓ := ℓ)
      (fig := lFig8 Dh encPt C protoSignalCodec ℓ encT
        (fun R => if R == Party.A then idA else idB) 25000 lam) k := by
  unfold Kept.send figS fig8San
  have h1 : (paramsV1 C K idA idB).C = C := rfl
  have h2 : (paramsV1 C K idA idB).codec = protoSignalCodec := rfl
  have h3 : (paramsV1 C K idA idB).idA = idA := rfl
  have h4 : (paramsV1 C K idA idB).idB = idB := rfl
  rw [h1, h2, h3, h4]

private theorem lpubOfV_lpubV {ℓ : ℕ} {Pt : Type}
    (p : LibsignalMsgPublicPart) :
    _root_.ReductionDsl.lpubOfV (ℓ := ℓ) (Pt := Pt)
      (_root_.ReductionDsl.lpubV (ℓ := ℓ) (Pt := Pt) p) = p :=
  Computational.Proofs.ReductionDsl.Fig8Atomic.lpubOfV_lpubV p

private theorem dfOrE_eval {ℓ : ℕ} {Pt : Type} {O' : Ops (atomicSig ℓ Pt)}
    {Γ} (a b : Expr O' Γ .bool) (ρ : Env Γ) :
    (dfOrE a b).eval ρ = (a.eval ρ || b.eval ρ) := by
  simp only [dfOrE, Expr.eval]
  cases a.eval ρ <;> rfl

private theorem dfIsSomeE_eval {ℓ : ℕ} {Pt : Type} {O' : Ops (atomicSig ℓ Pt)}
    {Γ} {t : Ty (atomicSig ℓ Pt)} (e : Expr O' Γ (.opt t)) (ρ : Env Γ) :
    (dfIsSomeE e).eval ρ = (e.eval ρ).isSome := by
  simp only [dfIsSomeE, Expr.eval]
  cases e.eval ρ <;> rfl

private theorem dfNatNeE_eval {ℓ : ℕ} {Pt : Type} {O' : Ops (atomicSig ℓ Pt)}
    {Γ} (a b : Expr O' Γ .nat) (ρ : Env Γ) :
    (dfNatNeE a b).eval ρ = decide (a.eval ρ ≠ b.eval ρ) := by
  simp only [dfNatNeE, eval_eLet, dfOrE_eval, Expr.eval, Expr.v0, Env.get]
  set x : ℕ := a.eval ρ
  set y : ℕ := b.eval ρ
  by_cases h : x = y
  · rw [h]; simp
  · rcases Nat.lt_or_gt_of_ne h with h1 | h1
    · have h2 : ¬ y < x := by omega
      simp [h, h1, h2]
    · have h2 : ¬ x < y := by omega
      simp [h, h1, h2]

private theorem dfIdxPredU32E_eval
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {ℓ : ℕ} {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt}
    {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (idxE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ .nat) (ρ : Env Γ) :
    (dfIdxPredU32E idxE).eval ρ = BitVec.ofNat 32 (idxE.eval ρ - 1) := by
  simp only [dfIdxPredU32E, eval_eLet]
  set n : ℕ := idxE.eval ρ
  change (if decide (n < 1) = true then _ else _) = BitVec.ofNat 32 (n - 1)
  by_cases h : n < 1
  · have h0 : n = 0 := by omega
    rw [h0]
    simp [eval_sOpPure, _root_.ReductionDsl.AtomicPureOp.eval]
  · have hd : decide (n < 1) = false := decide_eq_false h
    rw [hd]
    simp only [Bool.false_eq_true, ↓reduceIte, eval_sOpPure,
      _root_.ReductionDsl.AtomicPureOp.eval, Expr.eval, Expr.v0, Env.get]
    have hn : n = (n - 1) + 1 := by omega
    conv_lhs => rw [hn]
    rw [BitVec.ofNat_add]
    exact BitVec.add_sub_cancel _ _

private theorem dfIface_liftP_eq {ℓ : ℕ} {Pt : Type} [SampleableType Pt]
    {α : Type} (p : ProbComp α) :
    (fig8SmIfaceDF ℓ Pt).liftP p =
      (liftM p : OracleComp (unifSpec +
        CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
          (BitVec 256) (Fig8C Pt)) α) := by
  rfl

private theorem dfDrawSendCoinsC_eval
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {ℓ : ℕ} {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt}
    {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (rE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (.opt (BV512 (ℓ := ℓ) (Pt := Pt))))
    (ρ : Env Γ) :
    (dfDrawSendCoinsC rE).eval ρ =
      semDrawSendCoins (deliverForgeSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ)) (rE.eval ρ) := by
  simp only [dfDrawSendCoinsC, semDrawSendCoins, deliverForgeSemHook, Comp.eval, Expr.eval]
  cases hr : rE.eval ρ <;>
    simp only [dfIface_liftP_eq, Expr.eval, Expr.v0, Expr.v1] <;>
    rfl

private theorem dfPostSendStateE_eval
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (stE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (dfSendCorrStateT ℓ Pt))
    (s1E : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (simMirT ℓ Pt))
    (qE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ .bool)
    (m0E : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (PlainT (ℓ := ℓ) (Pt := Pt)))
    (isChallE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ .bool)
    (pq'E : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (B (ℓ := ℓ) (Pt := Pt) 32))
    (pnE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (U32 (ℓ := ℓ) (Pt := Pt)))
    (cE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (fig8CtT (ℓ := ℓ) (Pt := Pt)))
    (ρ : Env Γ)
    (v : (dfSendCorrStateT ℓ Pt).denote)
    (s₁ : GameState Unit (Plain ℓ) Bytes) (Q : Party) (m₀ : Plain ℓ) (isChall : Bool)
    (pq' : Bytes) (pn : BitVec 32) (c : Fig8C Pt)
    (hst : stE.eval ρ = v) (hs1 : s1E.eval ρ = simMirEnc s₁)
    (hq : qE.eval ρ = partyEnc Q) (hm0 : m0E.eval ρ = m₀) (hch : isChallE.eval ρ = isChall)
    (hpq : pq'E.eval ρ = pq') (hpn : pnE.eval ρ = pn)
    (hc : cE.eval ρ = fig8CtV (ℓ := ℓ) (Pt := Pt) c) :
    Prod.map (fun r => r.1) dfSendCorrStateDec
      ((dfPostSendStateE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) idA idB stE s1E qE m0E isChallE pq'E pnE cE).eval ρ) =
    (some (toWire c),
      (scPostSendPure (paramsV1 C K idA idB) Dh encPt encT lam
        (dfSendCorrStateDec v).1 s₁ Q m₀ isChall pq' pn c,
       c :: (dfSendCorrStateDec v).2)) := by
  let AOps := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam
  set sC := (dfSendCorrStateDec v).1
  set ex := (dfSendCorrStateDec v).2
  have hv1 : v.1 = simFullEnc sC := (simFullEnc_simFullDec v.1).symm
  dsimp only [dfPostSendStateE]
  rw [eval_eLet, eval_eLet]
  let tup : (dfPostSendArgT ℓ Pt).denote :=
    (v, (simMirEnc (Pt := Pt) s₁, (partyEnc Q, (m₀, (isChall, (pq', (pn, fig8CtV (ℓ := ℓ) (Pt := Pt) c)))))))
  have htup : (Expr.pair stE (.pair s1E (.pair qE (.pair m0E (.pair isChallE (.pair pq'E (.pair pnE cE))))))).eval ρ = tup := by
    simp [tup, Expr.eval, hst, hs1, hq, hm0, hch, hpq, hpn, hc]
  rw [htup]
  set ρ1 := Env.cons (t := dfPostSendArgT ℓ Pt) tup ρ
  have hw : (toWireAtomicE (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))) :
      Expr AOps _ (B (ℓ := ℓ) (Pt := Pt) 32)).eval ρ1 = toWire c :=
    toWireAtomicE_eval _ ρ1 c rfl
  rw [hw]
  set ρ2 := Env.cons (t := B (ℓ := ℓ) (Pt := Pt) 32) (toWire c) ρ1
  have hkQ : (pGet (scKept (.fst (.fst .v1))) (.fst (.snd (.snd .v1))) :
      Expr AOps _ (keptT ℓ Pt)).eval ρ2 = keptEnc (ℓ := ℓ) (sC.kept Q) := by
    cases Q <;> simp [ρ2, ρ1, tup, hv1, pGet, scKept, simFullEnc, partyEnc, Expr.eval, Expr.v0, Expr.v1]
  have hks : (keptSendAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB
      (pGet (scKept (.fst (.fst .v1))) (.fst (.snd (.snd .v1))))).eval ρ2 =
      keptEnc (ℓ := ℓ) (Kept.send (ℓ := ℓ)
        (fig := lFig8 Dh encPt C protoSignalCodec ℓ encT
          (fun R => if R == Party.A then idA else idB) 25000 lam) (sC.kept Q)) := by
    rw [keptSendAtomicE_eval idA idB 0 _ ρ2 (sC.kept Q) hkQ, kept_send_figS_eq]
  have hmir' : (mRecordE (.fst (.snd .v1)) (.fst (.snd (.snd .v1)))
      (.pair (.pair (.fst (.snd (.snd .v1)))
        (.pair (pGet (mEpoch (.fst (.snd .v1))) (.fst (.snd (.snd .v1))))
          (.add (pGet (mIdx (.fst (.snd .v1))) (.fst (.snd (.snd .v1)))) (.nat 1))))
        (.pair (.fst (.snd (.snd (.snd .v1)))) .v0))
      (.fst (.snd (.snd (.snd (.snd .v1))))) : Expr AOps _ (simMirT ℓ Pt)).eval ρ2 =
      simMirEnc (s₁.record 3 Q () ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, m₀, toWire c⟩ isChall) := by
    refine mRecordE_eval _ _ _ _ ρ2 s₁ Q ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, m₀, toWire c⟩ rfl rfl ?_
    cases Q <;> rfl
  dsimp only [dfSmRSendSomeE, scMk, ssMk, Expr.eval, Prod.map, dfSendCorrStateDec, scPostSendPure]
  rw [hmir']
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · have hFull :
        (((simMirEnc (Pt := Pt) (s₁.record 3 Q () ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, m₀, toWire c⟩ isChall),
           ((pSet (ssPq (scBase (.fst (.fst .v1)))) (.fst (.snd (.snd .v1)))
               (.fst (.snd (.snd (.snd (.snd (.snd .v1)))))) : Expr AOps _ _).eval ρ2,
            ((pSet (ssPn (scBase (.fst (.fst .v1)))) (.fst (.snd (.snd .v1)))
                (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v1))))))) : Expr AOps _ _).eval ρ2,
             ((ssUnackA (scBase (.fst (.fst .v1))) : Expr AOps _ _).eval ρ2,
              ((toWire c, fig8CtV (ℓ := ℓ) (Pt := Pt) c) ::
                (ssHonest (scBase (.fst (.fst .v1))) : Expr AOps _ _).eval ρ2,
               ((ssChains (scBase (.fst (.fst .v1))) : Expr AOps _ _).eval ρ2,
                ((ssAmb (scBase (.fst (.fst .v1))) : Expr AOps _ _).eval ρ2,
                 (ssStopped (scBase (.fst (.fst .v1))) : Expr AOps _ _).eval ρ2))))))),
          ((pSet (scKept (.fst (.fst .v1))) (.fst (.snd (.snd .v1)))
              (keptSendAtomicE idA idB (pGet (scKept (.fst (.fst .v1))) (.fst (.snd (.snd .v1))))) :
              Expr AOps _ _).eval ρ2,
           ((Expr.caseOpt (.fst (pGet (scKept (.fst (.fst .v1))) (.fst (.snd (.snd .v1)))))
              (scSent (.fst (.fst .v1)))
              (.ite (sendsInE (f8Id .v0) (.add (f8Tcur .v0) (.nat 1)))
                (scSent (.fst (.fst .v2)))
                (.caseOpt (f8VS .v0)
                  (scSent (.fst (.fst .v2)))
                  (.cons (.pair (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.var (.succ (.succ (.succ .zero))))))))))) .v0)
                    (scSent (.fst (.fst (.var (.succ (.succ (.succ .zero)))))))))) : Expr AOps _ _).eval ρ2,
            (scSnaps (.fst (.fst .v1)) : Expr AOps _ _).eval ρ2)))) =
        simFullEnc
          { sC with
            base := { sC.base with
              mir := s₁.record 3 Q () ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, m₀, toWire c⟩ isChall
              pq := Function.update sC.base.pq Q pq'
              pn := Function.update sC.base.pn Q pn
              honest := (toWire c, c) :: sC.base.honest }
            kept := Function.update sC.kept Q
              (Kept.send (ℓ := ℓ)
                (fig := lFig8 Dh encPt C protoSignalCodec ℓ encT
                  (fun R => if R == Party.A then idA else idB) 25000 lam) (sC.kept Q))
            sent := match (sC.kept Q).full with
              | some st =>
                if st.id.sendsIn (st.tcur + 1) then sC.sent
                else match st.vS with
                  | some vs => (c, vs) :: sC.sent
                  | none => sC.sent
              | none => sC.sent } := by
      dsimp only [simFullEnc, simBaseEnc]
      refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
      · cases Q <;> simp [ρ2, ρ1, tup, hv1, pSet, ssPq, ssPn, ssUnackA, ssHonest, ssChains,
          ssAmb, ssStopped, scBase, simFullEnc, simBaseEnc, honestPairEnc, partyEnc,
          Function.update, Expr.eval, Expr.v0, Expr.v1]
      · dsimp only [pSet, Expr.eval]
        rw [hks]
        cases Q <;> simp [ρ2, ρ1, tup, hv1, scKept, simFullEnc, partyEnc,
          Function.update, Expr.eval, Expr.v0, Expr.v1]
      · simp only [Expr.eval, hkQ]
        rcases hfull : (sC.kept Q).full with _ | st
        · simp [keptEnc, hfull, ρ2, ρ1, tup, hv1, scSent, simFullEnc, Expr.eval, Expr.v1]
        · simp only [keptEnc, hfull, Option.map]
          set ρ3 := Env.cons (t := fig8StT (ℓ := ℓ) (Pt := Pt)) (fig8StV (ℓ := ℓ) (Pt := Pt) st) ρ2
          have hsn : (sendsInE (f8Id .v0) (.add (f8Tcur .v0) (.nat 1)) :
              Expr AOps _ .bool).eval ρ3 = st.id.sendsIn (st.tcur + 1) := by
            have hid : (f8Id .v0 : Expr AOps _ .bool).eval ρ3 = partyEnc st.id := by
              simp only [ρ3, f8Id, fig8StV, Expr.eval, Expr.v0, _root_.ReductionDsl.Env.get_cons_zero]
              cases st.id <;> rfl
            rw [sendsInE_eval _ _ _ st.id hid]
            rfl
          rw [hsn]
          by_cases hs : st.id.sendsIn (st.tcur + 1) = true
          · simp [hs, ρ3, ρ2, ρ1, tup, hv1, scSent, simFullEnc, Expr.eval, Expr.v2]
          · have hs0 : st.id.sendsIn (st.tcur + 1) = false := Bool.eq_false_iff.mpr hs
            simp only [hs0, Bool.false_eq_true, ↓reduceIte]
            rcases hvs : st.vS with _ | vs
            · simp [ρ3, ρ2, ρ1, tup, hv1, f8VS, fig8StV, hvs, scSent, simFullEnc,
                Expr.eval, Expr.v0, Expr.v2]
            · simp [ρ3, ρ2, ρ1, tup, hv1, f8VS, fig8StV, hvs, scSent, simFullEnc, sentEntryEnc,
                Expr.eval, Expr.v0]
      · simp [ρ2, ρ1, tup, hv1, scSnaps, simFullEnc, Expr.eval, Expr.v1]
    dsimp only [paramsV1]
    exact (congrArg simFullDec hFull).trans (simFullDec_simFullEnc _)
  · simp [ρ2, ρ1, tup, ex, fig8CtOfV_fig8CtV, Expr.eval, Expr.v1]

theorem dfSendStepC_eval
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) (hℓ : ℓ < 10 ^ 6)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (stE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (dfSendCorrStateT ℓ Pt))
    (qE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ .bool)
    (m0E : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ PlainT)
    (chalE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (.opt PlainT))
    (rE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (.opt BV512))
    (ρ : Env Γ) (Q : Party)
    (hq : qE.eval ρ = partyEnc Q)
    (hBnd : SimCStateBounded q (dfSendCorrStateDec (stE.eval ρ)).1)
    (hEx : SanSnapExtra C K (dfSendCorrStateDec (stE.eval ρ)).1) :
    (Prod.map (fun r => r.1) dfSendCorrStateDec <$>
      (dfSendStepC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) idA idB qep stE qE m0E chalE rE).eval ρ) =
    semSendHook (paramsV1 C K idA idB) Dh encPt encT lam
      (deliverForgeSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ))
      qep (dfSendCorrStateDec (stE.eval ρ)).1 (dfSendCorrStateDec (stE.eval ρ)).2
      Q (m0E.eval ρ) (chalE.eval ρ) (rE.eval ρ) := by
  let _ := q
  let _ := hℓ
  let _ := hBnd
  let AOps := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam
  set v := stE.eval ρ
  set sC := (dfSendCorrStateDec v).1
  set ex := (dfSendCorrStateDec v).2
  generalize hm0 : m0E.eval ρ = m₀
  generalize hchal : chalE.eval ρ = chal
  generalize hr : rE.eval ρ = r
  have hv1 : v.1 = simFullEnc sC := (simFullEnc_simFullDec v.1).symm
  have hvDec : dfSendCorrStateDec v = (sC, ex) := rfl
  dsimp only [dfSendStepC, semSendHook]
  let inp : (dfSendInpT ℓ Pt).denote := (v, (partyEnc Q, (m₀, (chal, r))))
  have hinp : (Expr.pair stE (.pair qE (.pair m0E (.pair chalE rE)))).eval ρ = inp := by
    simp [inp, Expr.eval, v, hq, hm0, hchal, hr]
  rw [Comp.eval, Comp.eval, hinp, pure_bind]
  let ρ0 : Env (dfSendInpT ℓ Pt :: Γ) := Env.cons inp ρ
  have hmir0 : (ssMir (scBase (.fst (.fst .v0))) : Expr AOps _ (simMirT ℓ Pt)).eval ρ0 =
      simMirEnc sC.base.mir := by
    dsimp only [ρ0, inp, ssMir, scBase, Expr.eval, Expr.v0]
    rw [_root_.ReductionDsl.Env.get_cons_zero, hv1]
    rfl
  have hq0 : (Expr.fst (.snd .v0) : Expr AOps _ .bool).eval ρ0 = partyEnc Q := rfl
  have hg1 :
      (dfOrE (ssStopped (scBase (.fst (.fst .v0))))
        (dfOrE (mWin (ssMir (scBase (.fst (.fst .v0)))))
          (.not (mNoBobEpoch0E (ssMir (scBase (.fst (.fst .v0)))) (.fst (.snd .v0))))) :
        Expr AOps _ .bool).eval ρ0 =
      (sC.base.stopped || sC.base.mir.win ||
        !(CryptoGames.SM.noBobSendInEpoch0 sC.base.mir Q)) := by
    simp only [dfOrE_eval, Expr.eval]
    rw [mNoBobEpoch0E_eval _ _ ρ0 sC.base.mir Q hmir0 hq0]
    have hst : (ssStopped (scBase (.fst (.fst .v0))) : Expr AOps _ .bool).eval ρ0 =
        sC.base.stopped := by
      dsimp only [ρ0, inp, ssStopped, scBase, Expr.eval, Expr.v0]
      rw [_root_.ReductionDsl.Env.get_cons_zero, hv1]
      rfl
    have hw : (mWin (ssMir (scBase (.fst (.fst .v0)))) : Expr AOps _ .bool).eval ρ0 =
        sC.base.mir.win := by
      dsimp only [ρ0, inp, mWin, ssMir, scBase, Expr.eval, Expr.v0]
      rw [_root_.ReductionDsl.Env.get_cons_zero, hv1]
      rfl
    rw [hst, hw, Bool.or_assoc]
  rw [Comp.eval, hg1]
  cases hstop : (sC.base.stopped || sC.base.mir.win ||
      !(CryptoGames.SM.noBobSendInEpoch0 sC.base.mir Q))
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hep : (mEpMgmtE qep (ssMir (scBase (.fst (.fst .v0)))) (.fst (.snd .v0))
        (dfIsSomeE (.snd (.snd (.snd (.snd .v0))))) :
        Expr AOps _ (.opt (simMirT ℓ Pt))).eval ρ0 =
        (sC.base.mir.epMgmt 3 qep Q r.isSome).map (simMirEnc (Pt := Pt)) := by
      rw [mEpMgmtE_eval qep _ _ _ ρ0 sC.base.mir Q hmir0 hq0, dfIsSomeE_eval]
      rfl
    rw [Comp.eval, hep]
    rcases hep_res : sC.base.mir.epMgmt 3 qep Q r.isSome with _ | s₁
    · dsimp only [Option.map, Comp.eval, dfSmRNoneE, Expr.eval, Expr.v0, ρ0, inp]
      rw [_root_.ReductionDsl.Env.get_cons_zero, map_pure]
      exact congrArg pure (Prod.ext rfl hvDec)
    · dsimp only [Option.map]
      let ρ1 : Env (simMirT ℓ Pt :: dfSendInpT ℓ Pt :: Γ) :=
        Env.cons (simMirEnc (Pt := Pt) s₁) ρ0
      have hg2 : (Expr.and (dfIsSomeE (.fst (.snd (.snd (.snd .v1)))))
          (.not (mSafeChE .v0 (.fst (.snd .v1)))) : Expr AOps _ .bool).eval ρ1 =
          (chal.isSome && !(s₁.safeCh 3 Q)) := by
        have hsf : (mSafeChE .v0 (.fst (.snd .v1)) : Expr AOps _ .bool).eval ρ1 =
            s₁.safeCh 3 Q := mSafeChE_eval _ _ ρ1 s₁ Q rfl rfl
        change ((dfIsSomeE (.fst (.snd (.snd (.snd .v1))))).eval ρ1 &&
          !((mSafeChE .v0 (.fst (.snd .v1))).eval ρ1)) = _
        rw [dfIsSomeE_eval, hsf]
        rfl
      rw [Comp.eval, hg2]
      cases hsf_guard : (chal.isSome && !(s₁.safeCh 3 Q))
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have hdc : (dfDrawSendCoinsC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
            (encT := encT) (decT := decT) (lam := lam)
            (.snd (.snd (.snd (.snd .v1))))).eval ρ1 =
            semDrawSendCoins
              (deliverForgeSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ)) r :=
          dfDrawSendCoinsC_eval _ ρ1
        rw [Comp.eval, hdc, map_bind]
        refine bind_congr fun ⟨rq, rc⟩ => ?_
        rw [show (deliverForgeSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ)).onSendCoins Q rq ex =
              pure (ex, ex) from rfl, pure_bind]
        let ρ2 : Env (.prod (BV512 (ℓ := ℓ) (Pt := Pt)) (.opt (BV256 (ℓ := ℓ) (Pt := Pt))) ::
            simMirT ℓ Pt :: dfSendInpT ℓ Pt :: Γ) := Env.cons (rq, rc) ρ1
        let pn : BitVec 32 := if s₁.epoch Q ≠ sC.base.mir.epoch Q then
          BitVec.ofNat 32 (sC.base.mir.idx Q - 1) else sC.base.pn Q
        have hpn : (Expr.ite
            (dfNatNeE (pGet (mEpoch .v1) (.fst (.snd .v2)))
              (pGet (mEpoch (ssMir (scBase (.fst (.fst .v2))))) (.fst (.snd .v2))))
            (dfIdxPredU32E (pGet (mIdx (ssMir (scBase (.fst (.fst .v2))))) (.fst (.snd .v2))))
            (pGet (ssPn (scBase (.fst (.fst .v2)))) (.fst (.snd .v2))) :
            Expr AOps _ (U32 (ℓ := ℓ) (Pt := Pt))).eval ρ2 = pn := by
          have hv2 : (Expr.fst (.fst .v2) : Expr AOps _ (simFullT ℓ Pt)).eval ρ2 = simFullEnc sC :=
            hv1
          have hep1 : (pGet (mEpoch .v1) (.fst (.snd .v2)) : Expr AOps _ .nat).eval ρ2 =
              s₁.epoch Q := by cases Q <;> rfl
          have hep0 : (pGet (mEpoch (ssMir (scBase (.fst (.fst .v2))))) (.fst (.snd .v2)) :
              Expr AOps _ .nat).eval ρ2 = sC.base.mir.epoch Q := by
            change (if partyEnc Q then (((Expr.fst (.fst .v2)).eval ρ2).1.1.2.2.1).2
              else (((Expr.fst (.fst .v2)).eval ρ2).1.1.2.2.1).1) = _
            rw [hv2]; cases Q <;> rfl
          have hidx0 : (pGet (mIdx (ssMir (scBase (.fst (.fst .v2))))) (.fst (.snd .v2)) :
              Expr AOps _ .nat).eval ρ2 = sC.base.mir.idx Q := by
            change (if partyEnc Q then (((Expr.fst (.fst .v2)).eval ρ2).1.1.2.2.2.1).2
              else (((Expr.fst (.fst .v2)).eval ρ2).1.1.2.2.2.1).1) = _
            rw [hv2]; cases Q <;> rfl
          have hpn0 : (pGet (ssPn (scBase (.fst (.fst .v2)))) (.fst (.snd .v2)) :
              Expr AOps _ (U32 (ℓ := ℓ) (Pt := Pt))).eval ρ2 = sC.base.pn Q := by
            change (if partyEnc Q then (((Expr.fst (.fst .v2)).eval ρ2).1.2.2.1).2
              else (((Expr.fst (.fst .v2)).eval ρ2).1.2.2.1).1) = _
            rw [hv2]; cases Q <;> rfl
          change (if (dfNatNeE _ _).eval ρ2 then (dfIdxPredU32E _).eval ρ2
            else (pGet _ _).eval ρ2) = pn
          rw [dfNatNeE_eval, dfIdxPredU32E_eval, hep1, hep0, hidx0, hpn0]
          dsimp only [pn]
          by_cases heq : s₁.epoch Q = sC.base.mir.epoch Q <;> simp [heq]
        rw [Comp.eval, Comp.eval, hpn, pure_bind]
        let Γ3 : List (Ty (atomicSig ℓ Pt)) :=
          U32 (ℓ := ℓ) (Pt := Pt) ::
            .prod (BV512 (ℓ := ℓ) (Pt := Pt)) (.opt (BV256 (ℓ := ℓ) (Pt := Pt))) ::
            simMirT ℓ Pt :: dfSendInpT ℓ Pt :: Γ
        let ρ3 : Env Γ3 := Env.cons (t := U32 (ℓ := ℓ) (Pt := Pt)) pn ρ2
        let inp3E : Expr AOps Γ3 (dfSendInpT ℓ Pt) := .var (.succ (.succ (.succ .zero)))
        let base3E : Expr AOps Γ3 (simBaseT ℓ Pt) := scBase (.fst (.fst inp3E))
        let q3E : Expr AOps Γ3 .bool := .fst (.snd inp3E)
        let addr3E : Expr AOps Γ3 (.opt (B (ℓ := ℓ) (Pt := Pt) 32)) :=
          .ite (.and (.not q3E) (ssUnackA base3E))
            (optBytesLitE (paramsV1 C K idA idB).addrAB) .none
        let addr : Option Bytes :=
          if Q == Party.A && sC.base.unackA then (paramsV1 C K idA idB).addrAB else none
        have hv3 : (Expr.fst (.fst inp3E)).eval ρ3 = simFullEnc sC := hv1
        have hpq3 : (pGet (ssPq base3E) q3E).eval ρ3 = sC.base.pq Q := by
          change (if partyEnc Q then (((Expr.fst (.fst inp3E)).eval ρ3).1.2.1).2
            else (((Expr.fst (.fst inp3E)).eval ρ3).1.2.1).1) = _
          rw [hv3]; cases Q <;> rfl
        have haddr : addr3E.eval ρ3 = addr := by
          change (if _ then (optBytesLitE (paramsV1 C K idA idB).addrAB).eval ρ3 else none) = addr
          rw [optBytesLitE_eval]
          have hq3 : q3E.eval ρ3 = partyEnc Q := rfl
          have hun : (ssUnackA base3E).eval ρ3 = sC.base.unackA := by
            change (((Expr.fst (.fst inp3E)).eval ρ3).1.2.2.2.1) = _
            rw [hv3]; rfl
          cases Q <;> simp [addr, Expr.eval, hq3, hun, partyEnc]
        have hmk_inp : (Expr.pair (pGet (ssPq base3E) q3E)
            (.pair (.fst .v1) (.pair .v0 addr3E))).eval ρ3 =
            (sC.base.pq Q, (rq, (pn, addr))) :=
          Prod.ext hpq3 (Prod.ext rfl (Prod.ext rfl haddr))
        rw [Comp.eval,
            mkPubAtomicC_eval (fig8SmIfaceDF ℓ Pt) _ ρ3 (sC.base.pq Q) rq pn addr hmk_inp (hEx.1 Q),
            pure_bind]
        have hspqr_eq : (paramsV1 C K idA idB).spqr = spqrV1SessionUniformCoins C.F K := rfl
        dsimp only [mkPub]
        rw [hspqr_eq]
        let pubPairT : Ty (atomicSig ℓ Pt) :=
          .prod (B (ℓ := ℓ) (Pt := Pt) 32) (lpubT (ℓ := ℓ) (Pt := Pt))
        rcases hspqr : (spqrV1SessionUniformCoins C.F K).send
            (sC.base.pq Q) rq with _ | ⟨pq', salt, pqmsg⟩
        · dsimp only [Option.map]
          rw [Comp.eval, show (Expr.v0 : Expr AOps _ _).eval
                (Env.cons (t := .opt pubPairT) none ρ3) = none from rfl]
          dsimp only [Comp.eval, dfSmRNoneE, Expr.eval, ρ3, ρ2, ρ1, ρ0, inp]
          simp only [_root_.ReductionDsl.Env.get_cons_zero, _root_.ReductionDsl.Env.get_cons_succ,
            map_pure]
          exact congrArg pure (Prod.ext rfl hvDec)
        · dsimp only [Option.map]
          let pub : LibsignalMsgPublicPart :=
            ⟨pn, pqmsg, CryptoGames.effectiveHkdfSalt32 salt, addr⟩
          let ρ4 := Env.cons (t := .opt pubPairT) (some (pq', lpubV (ℓ := ℓ) (Pt := Pt) pub)) ρ3
          let ρ5 := Env.cons (t := pubPairT) (pq', lpubV (ℓ := ℓ) (Pt := Pt) pub) ρ4
          let rawQry := match chal with
            | none => CryptoGames.SM.Construction.DeliverForge.transmitQueryDF
                (St := CryptoGames.Ratchet.LibsignalSim.SimFig8St Pt)
                (Msg := LibsignalMsgPublicPart × Plain ℓ)
                (Coins := BitVec 256) (C := CryptoGames.Ratchet.LibsignalSim.SimFig8C Pt)
                Q (pub, m₀) rc
            | some m₁ => CryptoGames.SM.Construction.DeliverForge.challQueryDF
                (St := CryptoGames.Ratchet.LibsignalSim.SimFig8St Pt)
                (Msg := LibsignalMsgPublicPart × Plain ℓ)
                (Coins := BitVec 256) (C := CryptoGames.Ratchet.LibsignalSim.SimFig8C Pt)
                Q (pub, m₀) (pub, m₁) rc
          let Γ5 : List (Ty (atomicSig ℓ Pt)) :=
            pubPairT :: .opt pubPairT :: U32 (ℓ := ℓ) (Pt := Pt) ::
              .prod (BV512 (ℓ := ℓ) (Pt := Pt)) (.opt (BV256 (ℓ := ℓ) (Pt := Pt))) ::
              simMirT ℓ Pt :: dfSendInpT ℓ Pt :: Γ
          let inp5E : Expr AOps Γ5 (dfSendInpT ℓ Pt) :=
            .var (.succ (.succ (.succ (.succ (.succ .zero)))))
          let inp6E : Expr AOps (PlainT (ℓ := ℓ) (Pt := Pt) :: Γ5) (dfSendInpT ℓ Pt) :=
            .var (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))
          let qComp : Comp AOps (fig8SmIfaceDF ℓ Pt) Γ5 (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))) :=
            .caseOpt (.fst (.snd (.snd (.snd inp5E))))
              (.query (I := fig8SmIfaceDF ℓ Pt) (g := .tr)
                (.pair (.fst (.snd inp5E))
                  (.pair (.pair (.snd .v0) (.fst (.snd (.snd inp5E))))
                    (.snd (.var (.succ (.succ (.succ .zero))))))))
              (.query (I := fig8SmIfaceDF ℓ Pt) (g := .ch)
                (.pair (.fst (.snd inp6E))
                  (.pair (.pair (.snd .v1) (.fst (.snd (.snd inp6E))))
                    (.pair (.pair (.snd .v1) .v0)
                      (.snd (.var (.succ (.succ (.succ (.succ .zero))))))))))
          have hq_lhs : qComp.eval ρ5 =
              Option.map (fig8CtV (ℓ := ℓ) (Pt := Pt)) <$> rawQry := by
            rcases chal with _ | m₁
            · dsimp only [qComp, inp5E, rawQry, Comp.eval, fig8SmIfaceDF,
                CryptoGames.SM.Construction.DeliverForge.transmitQueryDF, Expr.eval, Expr.v0,
                ρ5, ρ4, ρ3, ρ2, ρ1, ρ0, inp]
              simp only [_root_.ReductionDsl.Env.get_cons_zero,
                _root_.ReductionDsl.Env.get_cons_succ]
              rw [boolToParty_partyEnc, lpubOfV_lpubV]
              rfl
            · dsimp only [qComp, inp5E, inp6E, rawQry, Comp.eval, fig8SmIfaceDF,
                CryptoGames.SM.Construction.DeliverForge.challQueryDF, Expr.eval, Expr.v0, Expr.v1,
                ρ5, ρ4, ρ3, ρ2, ρ1, ρ0, inp]
              simp only [_root_.ReductionDsl.Env.get_cons_zero,
                _root_.ReductionDsl.Env.get_cons_succ]
              rw [boolToParty_partyEnc, lpubOfV_lpubV]
              rfl
          have hq_rhs :
              (match chal with
                | none => (deliverForgeSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ)).onTr Q (pub, m₀) rc ex
                | some m₁ => (deliverForgeSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ)).onCh Q (pub, m₀) (pub, m₁) rc ex) =
              (fun res => (res, match res with | none => ex | some c => c :: ex)) <$> rawQry := by
            rcases chal with _ | m₁ <;>
              exact bind_pure_comp _ _
          rw [Comp.eval,
              show (Expr.v0 : Expr AOps _ _).eval ρ4 =
                some (pq', lpubV (ℓ := ℓ) (Pt := Pt) pub) from rfl]
          dsimp only
          refine Eq.trans ?_ (?_ :
            (((fun res => (res, match res with | none => ex | some c => c :: ex)) <$> rawQry) >>=
              fun x : Option (CryptoGames.Ratchet.LibsignalSim.SimFig8C Pt) ×
                  List (CryptoGames.Ratchet.LibsignalSim.SimFig8C Pt) =>
                match x.1 with
                | none => pure (none, (sC, ex))
                | some c =>
                  pure (some (toWire c),
                    (scPostSendPure (paramsV1 C K idA idB) Dh encPt encT lam
                      sC s₁ Q m₀ chal.isSome pq' pn c, x.2))) = _)
          · rw [Comp.eval, hq_lhs, map_bind, bind_map_left, bind_map_left]
            refine bind_congr fun res => ?_
            rcases res with _ | c
            · dsimp only [Option.map]
              rw [Comp.eval, show (Expr.v0 : Expr AOps _ _).eval
                    (Env.cons (t := .opt (fig8CtT (ℓ := ℓ) (Pt := Pt))) none ρ5) = none from rfl]
              dsimp only [Comp.eval, dfSmRNoneE, Expr.eval, ρ5, ρ4, ρ3, ρ2, ρ1, ρ0, inp]
              simp only [_root_.ReductionDsl.Env.get_cons_zero,
                _root_.ReductionDsl.Env.get_cons_succ, map_pure]
              exact congrArg pure (Prod.ext rfl hvDec)
            · dsimp only [Option.map]
              let ρ6 := Env.cons (t := .opt (fig8CtT (ℓ := ℓ) (Pt := Pt)))
                (some (fig8CtV (ℓ := ℓ) (Pt := Pt) c)) ρ5
              let ρ7 := Env.cons (t := fig8CtT (ℓ := ℓ) (Pt := Pt))
                (fig8CtV (ℓ := ℓ) (Pt := Pt) c) ρ6
              rw [Comp.eval,
                  show (Expr.v0 : Expr AOps _ _).eval ρ6 = some (fig8CtV (ℓ := ℓ) (Pt := Pt) c) from rfl]
              dsimp only
              rw [Comp.eval, map_pure]
              congr 1
              exact dfPostSendStateE_eval ℓ C K idA idB Dh encPt encT decT lam
                _ _ _ _ _ _ _ _ ρ7 v s₁ Q m₀ chal.isSome pq' pn c
                rfl rfl rfl rfl (dfIsSomeE_eval _ ρ7) rfl rfl rfl
          · congr 1
            rw [← hq_rhs]
            rcases chal with _ | m₁ <;> rfl
      · simp only [↓reduceIte]
        dsimp only [Comp.eval, dfSmRNoneE, Expr.eval, Expr.v1, ρ1, ρ0, inp]
        simp only [_root_.ReductionDsl.Env.get_cons_zero,
          _root_.ReductionDsl.Env.get_cons_succ, map_pure]
        exact congrArg pure (Prod.ext rfl hvDec)
  · simp only [↓reduceIte]
    dsimp only [Comp.eval, dfSmRNoneE, Expr.eval, Expr.v0, ρ0, inp]
    rw [_root_.ReductionDsl.Env.get_cons_zero, map_pure]
    exact congrArg pure (Prod.ext rfl hvDec)

theorem dfCorrStepC_eval
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (q : ℕ) (hℓ : ℓ < 10 ^ 6)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (stE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (dfSendCorrStateT ℓ Pt))
    (qE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ .bool)
    (ρ : Env Γ) (Q : Party)
    (hq : qE.eval ρ = partyEnc Q)
    (hBnd : SimCStateBounded q (dfSendCorrStateDec (stE.eval ρ)).1)
    (hEx : SanSnapExtra C K (dfSendCorrStateDec (stE.eval ρ)).1) :
    (Prod.map (fun r => r.2.2) dfSendCorrStateDec <$>
      (dfCorrStepC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) idA idB q stE qE).eval ρ) =
    semCorrHookTGB (paramsV1 C K idA idB) Dh encT
      (deliverForgeSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ))
      (25000 * q) (dfSendCorrStateDec (stE.eval ρ)).1 (dfSendCorrStateDec (stE.eval ρ)).2 Q := by
  let _ := hℓ
  let AOps := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam
  set v := stE.eval ρ
  set sC := (dfSendCorrStateDec v).1
  set ex := (dfSendCorrStateDec v).2
  have hv1 : v.1 = simFullEnc sC := (simFullEnc_simFullDec v.1).symm
  have hvDec : dfSendCorrStateDec v = (sC, ex) := rfl
  dsimp only [dfCorrStepC, semCorrHookTGB]
  have hPair : (Expr.pair stE qE).eval ρ = (v, partyEnc Q) := by
    simp [Expr.eval, v, hq]
  rw [Comp.eval, Comp.eval, hPair, pure_bind]
  let ρ0 : Env (.prod (dfSendCorrStateT ℓ Pt) .bool :: Γ) := Env.cons (v, partyEnc Q) ρ
  have hmir0 : (ssMir (scBase (.fst (.fst .v0))) : Expr AOps _ (simMirT ℓ Pt)).eval ρ0 =
      simMirEnc sC.base.mir := by
    dsimp only [ρ0, ssMir, scBase, Expr.eval, Expr.v0]
    rw [_root_.ReductionDsl.Env.get_cons_zero]
    dsimp only
    rw [hv1]
    rfl
  have hq0 : (Expr.snd .v0 : Expr AOps _ .bool).eval ρ0 = partyEnc Q := rfl
  have hGuard :
      (dfOrE (ssStopped (scBase (.fst (.fst .v0))))
        (dfOrE (mWin (ssMir (scBase (.fst (.fst .v0)))))
          (dfOrE (.not (mCorrAllowedFastE q (ssMir (scBase (.fst (.fst .v0)))) (.snd .v0)))
            (dfOrE (mInWinE (ssMir (scBase (.fst (.fst .v0)))) (.snd .v0))
              (.not (mNoSpkCorrE (ssMir (scBase (.fst (.fst .v0)))) (.snd .v0)))))) :
        Expr AOps _ .bool).eval ρ0 =
      (sC.base.stopped || sC.base.mir.win || !sC.base.mir.corrAllowed Q ||
        CryptoGames.Ratchet.LibsignalSim.inReceiveOnlyEpoch sC.base.mir Q ||
        !CryptoGames.SM.noAliceCorrWhileAliceBelowEpoch10 sC.base.mir Q) := by
    simp only [dfOrE_eval, Expr.eval]
    rw [mCorrAllowedFastE_eval q _ _ ρ0 sC.base.mir Q
          hBnd.base.trans_le hBnd.base.chall_le hBnd.base.comp_le hmir0 hq0,
        mInWinE_eval _ _ ρ0 sC.base.mir Q hmir0 hq0,
        mNoSpkCorrE_eval _ _ ρ0 sC.base.mir Q hmir0 hq0]
    have hst : (ssStopped (scBase (.fst (.fst .v0))) : Expr AOps _ .bool).eval ρ0 =
        sC.base.stopped := by
      dsimp only [ρ0, ssStopped, scBase, Expr.eval, Expr.v0]
      rw [_root_.ReductionDsl.Env.get_cons_zero]
      dsimp only
      rw [hv1]
      rfl
    have hw : (mWin (ssMir (scBase (.fst (.fst .v0)))) : Expr AOps _ .bool).eval ρ0 =
        sC.base.mir.win := by
      dsimp only [ρ0, mWin, ssMir, scBase, Expr.eval, Expr.v0]
      rw [_root_.ReductionDsl.Env.get_cons_zero]
      dsimp only
      rw [hv1]
      rfl
    rw [hst, hw]
    simp only [Bool.or_assoc]
  rw [Comp.eval, hGuard]
  cases hG : (sC.base.stopped || sC.base.mir.win || !sC.base.mir.corrAllowed Q ||
      CryptoGames.Ratchet.LibsignalSim.inReceiveOnlyEpoch sC.base.mir Q ||
      !CryptoGames.SM.noAliceCorrWhileAliceBelowEpoch10 sC.base.mir Q)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    let crQ := CryptoGames.SM.Construction.DeliverForge.corrQueryDF
      (St := CryptoGames.Ratchet.LibsignalSim.SimFig8St Pt)
      (Msg := LibsignalMsgPublicPart × Plain ℓ)
      (Coins := BitVec 256) (C := CryptoGames.Ratchet.LibsignalSim.SimFig8C Pt) Q
    let crComp : Comp AOps (fig8SmIfaceDF ℓ Pt)
        (.prod (dfSendCorrStateT ℓ Pt) .bool :: Γ)
        (.opt (fig8StT (ℓ := ℓ) (Pt := Pt))) :=
      .query (I := fig8SmIfaceDF ℓ Pt) (g := .cr) (.snd .v0)
    have hcr_lhs : crComp.eval ρ0 =
        Option.map (fig8StV (ℓ := ℓ) (Pt := Pt)) <$> crQ := by
      dsimp only [crComp, crQ, Comp.eval, fig8SmIfaceDF,
        CryptoGames.SM.Construction.DeliverForge.corrQueryDF, Expr.eval, Expr.v0]
      rw [_root_.ReductionDsl.Env.get_cons_zero, boolToParty_partyEnc]
      rfl
    have hcr_rhs : (deliverForgeSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ)).onCr Q ex =
        (fun res => (res, ex)) <$> crQ := by
      simp [crQ, deliverForgeSemHook, bind_pure_comp]
    rw [Comp.eval]
    change Prod.map (fun r : (smRT (ℓ := ℓ) (Pt := Pt) (GhostStT (ℓ := ℓ) (Pt := Pt))).denote => r.2.2)
      dfSendCorrStateDec <$> (crComp.eval ρ0 >>= _) = _
    rw [hcr_lhs, hcr_rhs, map_bind, bind_map_left, bind_map_left]
    refine bind_congr fun res => ?_
    cases res with
    | none =>
        dsimp only [Option.map]
        rw [Comp.eval, show (Expr.v0 : Expr AOps _ _).eval
              (Env.cons (t := .opt (fig8StT (ℓ := ℓ) (Pt := Pt))) none ρ0) = none from rfl]
        dsimp only [Comp.eval, dfSmRNoneE, Expr.eval, Expr.v1, ρ0]
        rw [_root_.ReductionDsl.Env.get_cons_succ, _root_.ReductionDsl.Env.get_cons_zero, map_pure]
        exact congrArg pure (Prod.ext rfl hvDec)
    | some fig8st =>
        dsimp only [Option.map]
        rw [Comp.eval, show (Expr.v0 : Expr AOps _ _).eval
              (Env.cons (t := .opt (fig8StT (ℓ := ℓ) (Pt := Pt)))
                (some (fig8StV (ℓ := ℓ) (Pt := Pt) fig8st)) ρ0) =
              some (fig8StV (ℓ := ℓ) (Pt := Pt) fig8st) from rfl]
        dsimp only
        rw [Comp.eval, map_pure]
        congr 1
        set ρs := Env.cons (t := fig8StT (ℓ := ℓ) (Pt := Pt)) (fig8StV (ℓ := ℓ) (Pt := Pt) fig8st)
          (Env.cons (t := .opt (fig8StT (ℓ := ℓ) (Pt := Pt)))
            (some (fig8StV (ℓ := ℓ) (Pt := Pt) fig8st)) ρ0)
        dsimp only [dfPostCorrStateE]
        rw [eval_eLet, eval_eLet, eval_eLet]
        have htup : (Expr.pair (.fst .v2) (.pair (.snd .v2) .v0) :
            Expr AOps _ _).eval ρs = (v, (partyEnc Q, fig8StV (ℓ := ℓ) (Pt := Pt) fig8st)) := rfl
        rw [htup]
        set ρc0 := Env.cons
          (t := .prod (dfSendCorrStateT ℓ Pt) (.prod .bool (fig8StT (ℓ := ℓ) (Pt := Pt))))
          (v, (partyEnc Q, fig8StV (ℓ := ℓ) (Pt := Pt) fig8st)) ρs
        let chains' : Party → List GhostChain :=
          if Q == Party.B && sC.base.mir.epoch Party.B == 0 then
            match fig8st.γ with
            | .exp x => Function.update sC.base.chains Party.A
                ((sC.base.chains Party.A).map fun g =>
                  if g.key.isNone then { g with key := some (encT (Dh.dh x Dh.base)) } else g)
            | _ => sC.base.chains
          else sC.base.chains
        have hCond : (Expr.and (.fst (.snd .v0))
            (.lt (.snd (mEpoch (ssMir (scBase (.fst (.fst .v0)))))) (.nat 1)) :
            Expr AOps _ .bool).eval ρc0 = (Q == Party.B && sC.base.mir.epoch Party.B == 0) := by
          have hEpB : (Expr.snd (mEpoch (ssMir (scBase (.fst (.fst .v0))))) :
              Expr AOps _ .nat).eval ρc0 = sC.base.mir.epoch Party.B := by
            dsimp only [ρc0, mEpoch, ssMir, scBase, Expr.eval, Expr.v0]
            rw [_root_.ReductionDsl.Env.get_cons_zero]
            exact congrArg (fun x => x.1.1.2.2.1.2) hv1
          change ((Expr.fst (.snd .v0)).eval ρc0 &&
            decide ((Expr.snd (mEpoch (ssMir (scBase (.fst (.fst .v0)))))).eval ρc0 < 1)) = _
          simp only [hEpB]
          change (partyEnc Q && decide (sC.base.mir.epoch Party.B < 1)) = _
          cases Q <;> cases sC.base.mir.epoch Party.B <;> simp [partyEnc]
        have hExCh : ∀ R, (sC.base.chains R).length ≤ 5 ∧
            ∀ g ∈ sC.base.chains R, g.skipped.length ≤ 2000 :=
          hEx.2.1
        have hChains : (Expr.ite (.and (.fst (.snd .v0))
              (.lt (.snd (mEpoch (ssMir (scBase (.fst (.fst .v0)))))) (.nat 1)))
            (.caseSum (f8Gamma (.snd (.snd .v0)))
              (ssChains (scBase (.fst (.fst .v1))))
              (.pair
                (revealSpkChainsE (.fst (ssChains (scBase (.fst (.fst .v1)))))
                  (sOpPtEnc .ptEncPk (sOpGrp .ptDh (.pair .v0 (sOpGrp .ptBase .unit)))))
                (.snd (ssChains (scBase (.fst (.fst .v1)))))))
            (ssChains (scBase (.fst (.fst .v0)))) : Expr AOps _ _).eval ρc0 =
            ((chains' Party.A).map (ghostChainEnc (ℓ := ℓ) (Pt := Pt)),
             (chains' Party.B).map (ghostChainEnc (ℓ := ℓ) (Pt := Pt))) := by
          change (if (Expr.and (.fst (.snd .v0))
                (.lt (.snd (mEpoch (ssMir (scBase (.fst (.fst .v0)))))) (.nat 1))).eval ρc0
              then _ else _) = _
          rw [hCond]
          dsimp only [chains']
          by_cases hB0 : (Q == Party.B && sC.base.mir.epoch Party.B == 0) = true
          · rw [hB0]
            simp only [↓reduceIte]
            rcases hγ : fig8st.γ with h | x
            · have hfg : (f8Gamma (.snd (.snd .v0)) :
                  Expr AOps _ (ckaStT (ℓ := ℓ) (Pt := Pt))).eval ρc0 = Sum.inl h := by
                simp [ρc0, f8Gamma, fig8StV, hγ, _root_.ReductionDsl.ckaStV, Expr.eval, Expr.v0]
              rw [Expr.eval, hfg]
              dsimp only [ρc0, ssChains, scBase, Expr.eval, Expr.v1]
              rw [_root_.ReductionDsl.Env.get_cons_succ, _root_.ReductionDsl.Env.get_cons_zero]
              dsimp only
              rw [hv1]
              rfl
            · have hfg : (f8Gamma (.snd (.snd .v0)) :
                  Expr AOps _ (ckaStT (ℓ := ℓ) (Pt := Pt))).eval ρc0 = Sum.inr x := by
                simp [ρc0, f8Gamma, fig8StV, hγ, _root_.ReductionDsl.ckaStV, Expr.eval, Expr.v0]
              rw [Expr.eval, hfg]
              dsimp only
              let ρx := Env.cons (t := BV256 (ℓ := ℓ) (Pt := Pt)) x ρc0
              have hcsA : (Expr.fst (ssChains (scBase (.fst (.fst .v1)))) :
                  Expr AOps _ _).eval ρx =
                  (sC.base.chains Party.A).map (ghostChainEnc (ℓ := ℓ) (Pt := Pt)) := by
                dsimp only [ρx, ρc0, ssChains, scBase, Expr.eval, Expr.v1]
                rw [_root_.ReductionDsl.Env.get_cons_succ, _root_.ReductionDsl.Env.get_cons_zero]
                dsimp only
                rw [hv1]
                rfl
              have hpk : (sOpPtEnc .ptEncPk (sOpGrp .ptDh (.pair .v0 (sOpGrp .ptBase .unit))) :
                  Expr AOps _ _).eval ρx = encT (Dh.dh x Dh.base) := by
                simp [ρx, _root_.ReductionDsl.AtomicGroupOp.eval, Expr.eval, Expr.v0]
              change ((revealSpkChainsE _ _).eval ρx,
                (Expr.snd (ssChains (scBase (.fst (.fst .v1))))).eval ρx) = _
              rw [eval_revealSpkChainsE _ _ ρx (sC.base.chains Party.A) hcsA (hExCh Party.A).1,
                  hpk]
              dsimp only [ρx, ρc0, ssChains, scBase, Expr.eval, Expr.v1]
              rw [_root_.ReductionDsl.Env.get_cons_succ, _root_.ReductionDsl.Env.get_cons_zero]
              dsimp only
              rw [hv1, Function.update_self, Function.update_of_ne (by decide : Party.B ≠ Party.A)]
              rfl
          · have hB0f : (Q == Party.B && sC.base.mir.epoch Party.B == 0) = false :=
              Bool.eq_false_iff.mpr hB0
            rw [hB0f]
            dsimp only [Bool.false_eq_true, ↓reduceIte, ρc0, ssChains, scBase, Expr.eval, Expr.v0]
            rw [_root_.ReductionDsl.Env.get_cons_zero]
            dsimp only
            rw [hv1]
            rfl
        rw [hChains]
        let chainsPairT : Ty (atomicSig ℓ Pt) :=
          .prod (.list (ghostChainT ℓ Pt)) (.list (ghostChainT ℓ Pt))
        set csVal : chainsPairT.denote :=
          ((chains' Party.A).map (ghostChainEnc (ℓ := ℓ) (Pt := Pt)),
           (chains' Party.B).map (ghostChainEnc (ℓ := ℓ) (Pt := Pt)))
        set ρc1 := Env.cons (t := chainsPairT) csVal ρc0
        have hcsLen : (chains' Q).length ≤ 5 := by
          dsimp only [chains']
          split_ifs
          · cases fig8st.γ with
            | pub _ => exact (hExCh Q).1
            | exp _ =>
                cases Q <;> simp [Function.update, (hExCh Party.A).1, (hExCh Party.B).1]
          · exact (hExCh Q).1
        have hcsSk : ∀ g ∈ chains' Q, g.skipped.length ≤ 2000 := by
          intro g hg
          dsimp only [chains'] at hg
          split_ifs at hg
          · cases hγ : fig8st.γ with
            | pub _ =>
                rw [hγ] at hg
                exact (hExCh Q).2 g hg
            | exp x =>
                rw [hγ] at hg
                cases Q with
                | B => exact (hExCh Party.B).2 g hg
                | A =>
                    simp only [Function.update_self, List.mem_map] at hg
                    rcases hg with ⟨g0, hg0, rfl⟩
                    split_ifs <;> exact (hExCh Party.A).2 g0 hg0
          · exact (hExCh Q).2 g hg
        have hBaseG : (ssMk (ssMir (scBase (.fst (.fst .v1))))
            (ssPq (scBase (.fst (.fst .v1)))) (ssPn (scBase (.fst (.fst .v1))))
            (ssUnackA (scBase (.fst (.fst .v1)))) .nil .v0
            (ssAmb (scBase (.fst (.fst .v1)))) (ssStopped (scBase (.fst (.fst .v1)))) :
            Expr AOps _ (simBaseT ℓ Pt)).eval ρc1 =
            simBaseEnc { sC.base with chains := chains', honest := [] } := by
          dsimp only [ρc1, ρc0, csVal, ssMk, ssMir, ssPq, ssPn, ssUnackA, ssAmb, ssStopped,
            scBase, Expr.eval, Expr.v0, Expr.v1]
          simp only [_root_.ReductionDsl.Env.get_cons_zero, _root_.ReductionDsl.Env.get_cons_succ]
          rw [hv1]
          rfl
        have hGhost : (toGhostE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
            (decT := decT) (lam := lam) idA idB (25000 * q)
            (ssMk (ssMir (scBase (.fst (.fst .v1))))
              (ssPq (scBase (.fst (.fst .v1)))) (ssPn (scBase (.fst (.fst .v1))))
              (ssUnackA (scBase (.fst (.fst .v1)))) .nil .v0
              (ssAmb (scBase (.fst (.fst .v1)))) (ssStopped (scBase (.fst (.fst .v1)))))
            (.fst (.snd .v1)) (.snd (.snd .v1))).eval ρc1 =
            toGhost (P := paramsV1 C K idA idB) { sC.base with chains := chains' } Q
              (fig8StTruncSkB (25000 * q) fig8st) := by
          rw [eval_toGhostE idA idB (25000 * q) _ _ _ ρc1
                { sC.base with chains := chains', honest := [] } Q fig8st
                hBaseG rfl rfl hcsLen hcsSk]
          rw [← simToGhost_eq, ← simToGhost_eq]
          rfl
        rw [hGhost]
        set ghostOut := toGhost (P := paramsV1 C K idA idB) { sC.base with chains := chains' } Q
          (fig8StTruncSkB (25000 * q) fig8st)
        set ρc2 := Env.cons (t := GhostStT (ℓ := ℓ) (Pt := Pt)) ghostOut ρc1
        have hMir2 : (ssMir (scBase (.fst (.fst .v2))) : Expr AOps _ (simMirT ℓ Pt)).eval ρc2 =
            simMirEnc sC.base.mir := by
          dsimp only [ρc2, ρc1, ρc0, ssMir, scBase, Expr.eval, Expr.v2]
          simp only [_root_.ReductionDsl.Env.get_cons_zero, _root_.ReductionDsl.Env.get_cons_succ]
          rw [hv1]
          rfl
        have hAfter : (mAfterCorrFastE q (ssMir (scBase (.fst (.fst .v2)))) (.fst (.snd .v2)) :
            Expr AOps _ (simMirT ℓ Pt)).eval ρc2 =
            simMirEnc (Computational.Proofs.GameHop.CompDedup.afterCorrDedup sC.base.mir Q) :=
          mAfterCorrFastE_eval q _ _ ρc2 sC.base.mir Q hBnd.base.trans_le hBnd.base.comp_u hMir2 rfl
        have hKeptSt : (keptOfStAtomicE (.snd (.snd .v2)) : Expr AOps _ (keptT ℓ Pt)).eval ρc2 =
            keptEnc (Kept.ofSt fig8st) :=
          keptOfStAtomicE_eval _ ρc2 fig8st rfl
        have hKeptUpd : (pSet (scKept (.fst (.fst .v2))) (.fst (.snd .v2))
            (keptOfStAtomicE (.snd (.snd .v2))) : Expr AOps _ _).eval ρc2 =
            (keptEnc (Function.update sC.kept Q (Kept.ofSt fig8st) Party.A),
             keptEnc (Function.update sC.kept Q (Kept.ofSt fig8st) Party.B)) := by
          dsimp only [pSet, Expr.eval]
          rw [hKeptSt]
          cases Q <;>
            simp [ρc2, ρc1, ρc0, hv1, scKept, simFullEnc, partyEnc, Function.update,
              Expr.eval, Expr.v0, Expr.v2]
        dsimp only [dfSmRCorrSomeE, scMk, ssMk, dfSendCorrStateDec,
          SimDeliverForgeStepSendCorrCost.dfSendCorrStateDec, Expr.eval, Prod.map]
        rw [hAfter, hKeptUpd]
        refine Prod.ext rfl (Prod.ext ?_ rfl)
        have hsC' :
            ((simMirEnc (Pt := Pt) (Computational.Proofs.GameHop.CompDedup.afterCorrDedup sC.base.mir Q),
              ((ssPq (scBase (.fst (.fst .v2))) : Expr AOps _ _).eval ρc2,
               ((ssPn (scBase (.fst (.fst .v2))) : Expr AOps _ _).eval ρc2,
                ((ssUnackA (scBase (.fst (.fst .v2))) : Expr AOps _ _).eval ρc2,
                 ((ssHonest (scBase (.fst (.fst .v2))) : Expr AOps _ _).eval ρc2,
                  ((Expr.v1 : Expr AOps _ chainsPairT).eval ρc2,
                   ((ssAmb (scBase (.fst (.fst .v2))) : Expr AOps _ _).eval ρc2,
                    (ssStopped (scBase (.fst (.fst .v2))) : Expr AOps _ _).eval ρc2))))))),
             ((keptEnc (Function.update sC.kept Q (Kept.ofSt fig8st) Party.A),
               keptEnc (Function.update sC.kept Q (Kept.ofSt fig8st) Party.B)),
              ((scSent (.fst (.fst .v2)) : Expr AOps _ _).eval ρc2,
               (((Expr.v2 : Expr AOps _ _).eval ρc2).2.1,
                ((pGet (mEpoch (ssMir (scBase (.fst (.fst .v2))))) (.fst (.snd .v2)) :
                   Expr AOps _ _).eval ρc2,
                 (Expr.v0 : Expr AOps _ (GhostStT (ℓ := ℓ) (Pt := Pt))).eval ρc2)) ::
                (scSnaps (.fst (.fst .v2)) : Expr AOps _ _).eval ρc2))) =
            simFullEnc
              { base := { sC.base with
                  mir := Computational.Proofs.GameHop.CompDedup.afterCorrDedup sC.base.mir Q
                  chains := chains' }
                kept := Function.update sC.kept Q (Kept.ofSt fig8st)
                sent := sC.sent
                snaps := (Q, sC.base.mir.epoch Q, ghostOut) :: sC.snaps } := by
          cases Q <;>
            simp [ρc2, ρc1, ρc0, csVal, hv1, pGet, mEpoch, ssMir, ssPq, ssPn, ssUnackA,
              ssHonest, ssAmb, ssStopped, scBase, scSent, scSnaps,
              simFullEnc, simBaseEnc, simMirEnc, snapEnc, partyEnc,
              Expr.eval, Expr.v0, Expr.v1, Expr.v2]
        exact (congrArg simFullDec hsC').trans (simFullDec_simFullEnc _)
  · simp only [↓reduceIte]
    dsimp only [Comp.eval, dfSmRNoneE, Expr.eval, Expr.v0, ρ0]
    rw [_root_.ReductionDsl.Env.get_cons_zero, map_pure]
    exact congrArg pure (Prod.ext rfl hvDec)

def simDeliverForgeSendCorrSpec
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) :
    SimDeliverForgeSendCorrSpec Pt ℓ C K idA idB Dh encPt encT decT lam qep q where
  sendC stE qE m0E chalE rE := dfSendStepC idA idB qep stE qE m0E chalE rE
  corrC stE qE := dfCorrStepC idA idB q stE qE
  hsend_q stE qE m0E chalE rE :=
    dfSendStepC_queries ℓ C K idA idB Dh encPt encT decT lam qep stE qE m0E chalE rE
  hcorr_q stE qE :=
    dfCorrStepC_queries ℓ C K idA idB Dh encPt encT decT lam q stE qE
  hsend_c hℓ {_} stE qE m0E chalE rE :=
    dfSendStepC_cost ℓ C K idA idB Dh encPt encT decT lam qep q hℓ stE qE m0E chalE rE
  hcorr_c hℓ {_} stE qE :=
    dfCorrStepC_cost ℓ C K idA idB Dh encPt encT decT lam q hℓ stE qE
  hsend_d hℓ {_} stE qE m0E chalE rE :=
    dfSendStepC_descBits_le ℓ C K idA idB Dh encPt encT decT lam qep q hℓ stE qE m0E chalE rE
  hcorr_d hℓ {_} stE qE :=
    dfCorrStepC_descBits_le ℓ C K idA idB Dh encPt encT decT lam qep q hℓ stE qE
  hsend_eval hℓ {_} stE qE m0E chalE rE ρ Q hq hBnd hEx :=
    dfSendStepC_eval ℓ C K idA idB Dh encPt encT decT lam qep q hℓ stE qE m0E chalE rE ρ Q hq hBnd hEx
  hcorr_eval hℓ {_} stE qE ρ Q hq hBnd hEx :=
    dfCorrStepC_eval ℓ C K idA idB Dh encPt encT decT lam q hℓ stE qE ρ Q hq hBnd hEx

theorem simDeliverForgeSendCorrSpec_nonempty
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) :
    Nonempty (SimDeliverForgeSendCorrSpec Pt ℓ C K idA idB Dh encPt encT decT lam qep q) :=
  ⟨simDeliverForgeSendCorrSpec ℓ C K idA idB Dh encPt encT decT lam qep q⟩

end

end Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeStepSendCorr
