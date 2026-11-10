/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeHaltedBase
public import Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeSanSem -- proof-setup: allow-public-import
import Computational.Proofs.E2E.Dsl.SpqrSimChain

/-!
# Operational `.eval` Proofs for `SimDeliverForgeHalted`

Proves forward-encoding `.eval` agreement (`dfHaltedEnc`) for the braid send step, all five `SM`
query branches of `dfStepHaltedC`, and `simDeliverForgeInitHaltedC`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeHaltedEval

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ops Iface Ty Expr Comp Env Var
  atomicSig atomicSessionOps fig8SmIfaceDF e2eSessionCodec handlerImpl
  GhostStT PlainT BV256 BV512 U32 U64 B smQT smRT smQenc smRdec lpubT lpubV lpubOfV
  fig8StT fig8StV fig8StOfV fsSendStV fsSendStOfV fig8CtT fig8CtV fig8CtOfV
  partyToBool boolToParty recvResultT recvResultEnc recvResultDec smRrEnc smRrDec)
open _root_.CryptoGames (Party)
open CryptoGames.Ratchet (keyToBytesVec32)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.SM (GameState RecvResult partyEnc partyDec pGet pSet sendsInE sendsInE_eval
  noBobSendInEpoch0 posTy posEnc posDec)
open CryptoGames.SM.Construction.DeliverForge
  (AdversaryCompDF specDF transmitQueryDF challQueryDF)
open CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart lFig8)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoGames.Ratchet.LibsignalSim
  (Fig8St Fig8C kemTrackEnc mkPub toWire SimCStateBounded SimKemFailTrack SimBraidSt simStepKemFailSend
   deliverForgeSemHook scPostSendPure semSendHook)
open CryptoGames.Ratchet.LibsignalSimC (LibsignalToModularSchemeSimState Kept initSimC)
open CryptoGames.LibsignalSession
  (Crypto ShaCompress IdentityKey PublicKey GhostState)
open CryptoGames.LibsignalSM.Proofs.Refinement
  (KemFailTrackState stepKemFailSend stepKemFailDeliver)
open CryptoVerification.LibsignalSpqrV1 (MlKem V1State coinBytes coinBytes_length spqrV1SessionUniformCoins)
open CryptoVerification.SpqrV1Sync.SendTotal (BOkTight)
open CryptoVerification.E2E (Bytes paramsV1)
open Computational.Proofs.ReductionDsl.Fig8Atomic (salt32V_salt32OfV)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8State
  (sOpSpqr eval_eLet mWin mEpoch mIdx mSafeChE mSafeChE_eval mEpMgmtE mEpMgmtE_eval
   mRecordE mRecordE_eval mNoBobEpoch0E mNoBobEpoch0E_eval
   ssMir ssPq ssPn ssUnackA ssHonest ssChains ssAmb ssStopped ssMk
   scBase scKept scSent scSnaps scMk)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8LoopAndCost
  (simMirT simMirEnc simMirDec simRecT simRecEnc simRecDec
   simBaseT simBaseEnc simBaseDec honestPairEnc honestPairDec ghostChainEnc ghostChainDec
   keptT keptEnc keptDec sentEntryEnc sentEntryDec snapEnc snapDec
   simFullT simFullEnc simFullDec simFullDec_simFullEnc)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8WireSnap
  (optBytesLitE optBytesLitE_eval mkPubAtomicC mkPubAtomicC_eval toWireAtomicE toWireAtomicE_eval)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8Kept
  (f8Id f8VS f8Tcur keptSendAtomicE keptSendAtomicE_eval)
open Computational.Proofs.Game.PromotedCostedReds.SanOracleCore (figS fig8San)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8SanCoupling (SanSnapExtra)
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeSanOracle
  (dfFullT dfFullEnc dfFullDec dfFullDec_dfFullEnc)
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeStepSendCorrCost
  (dfOrE dfIsSomeE dfNatNeE dfSmRNoneE dfSmRSendSomeE dfIdxPredU32E dfPostSendArgT dfPostSendStateE)
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeStepSendCorr
  (simDeliverForgeSendCorrSpec dfSendCorrStateDec)
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeStepRecvFwdCost
  (dfRecvOutT dfRecvOutDec)
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeStepRecvFwd (dfRecvHookC dfRecvHookC_eval)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedInit
  (kemCoinsT kemTrackT kemTrackAtomicEnc)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedSendCorrSub
  (boolEqE trE_e trE_c trE_st trE_sentB trE_sendCtr trE_cand trMk
   ekSideIsAE isKeysUnsampledV1E isKeysUnsampledV1E_eval
   isHeaderReceivedV1E isHeaderReceivedV1E_eval
   encRandBvAtomicE nextKemCoinsAtomicE stepPostKemSendE)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedDeliverWitnessSub
  (findRevHonestIdxE kemOnDeliverPostAtomicE findRevHonestIdxE_eval)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedDeliverWitness
  (KemTrackDeliverInv kemOnDeliverPostAtomicE_eval)
open Computational.Proofs.Game.PromotedCostedReds.KemFailBadHalted
  (honestExchangeFailsPolyC honestExchangeFailsPolyC_eval)
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeHaltedBase
  (dfHaltedT nextKemCandPolyC stepKemFailSendPolyC dfDrawRqC dfDrawRcOptC
   dfSendHaltedInpT dfSendStepHaltedC wkTop1CompH smRRecvPackEH
   dfSendArgTH dfRecvArgTH classifySmQEH dfStepHaltedC
   semSendTrackHalted simDeliverForgeOracleSanQTrackHalted)

noncomputable section

@[expose] def dfHaltedEnc {ℓ : ℕ} {Pt : Type} {F : ShaCompress}
    (st : (LibsignalToModularSchemeSimState Bytes Pt ℓ × List (Fig8C Pt)) ×
      KemFailTrackState F) :
    (dfHaltedT ℓ Pt).denote :=
  (dfFullEnc st.1, kemTrackAtomicEnc (ℓ := ℓ) (Pt := Pt) (kemTrackEnc st.2))

private theorem boolToParty_partyEnc (Q : Party) :
    boolToParty (partyEnc Q) = Q := by
  cases Q <;> rfl

theorem partyToBool_eq_partyEnc (Q : Party) :
    partyToBool Q = partyEnc Q := by
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

theorem dfFullEnc_dfFullDec {ℓ : ℕ} {Pt : Type}
    (v : (dfFullT ℓ Pt).denote) :
    dfFullEnc (dfFullDec v) = v := by
  rcases v with ⟨s, ex⟩
  dsimp only [dfFullEnc, dfFullDec]
  simp only [simFullEnc_simFullDec, List.map_map]
  have hct : (fig8CtV (ℓ := ℓ) (Pt := Pt) ∘ fig8CtOfV) = id := by
    funext cv; exact fig8CtV_fig8CtOfV cv
  simp only [hct, List.map_id]

private theorem dfIface_liftP_eq {ℓ : ℕ} {Pt : Type} [SampleableType Pt]
    {α : Type} (p : ProbComp α) :
    (fig8SmIfaceDF ℓ Pt).liftP p =
      (liftM p : AdversaryCompDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
        (BitVec 256) (Fig8C Pt) α) :=
  rfl

private theorem advDF_bind_congr {ℓ : ℕ} {Pt : Type} {α β : Type}
    {mx my : AdversaryCompDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt) α}
    {f g : α → AdversaryCompDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt) β}
    (hxy : mx = my) (hfg : ∀ a, f a = g a) :
    (mx >>= f) = (my >>= g) := by
  rw [hxy, funext hfg]

private theorem dfDrawRqC_eval
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {ℓ : ℕ} {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt}
    {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (rE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ
      (.opt (BV512 (ℓ := ℓ) (Pt := Pt))))
    (ρ : Env Γ) :
    (dfDrawRqC rE).eval ρ =
      (match rE.eval ρ with
       | some rq => pure rq
       | none => (liftM ($ᵗ (BitVec 512) : ProbComp (BitVec 512)) :
           AdversaryCompDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
             (BitVec 256) (Fig8C Pt) (BitVec 512))) := by
  dsimp only [dfDrawRqC, Comp.eval, Expr.eval]
  cases rE.eval ρ with
  | none => exact dfIface_liftP_eq ($ᵗ (BitVec 512))
  | some rq => rfl

private theorem dfDrawRcOptC_eval
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {ℓ : ℕ} {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt}
    {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (rE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ
      (.opt (BV512 (ℓ := ℓ) (Pt := Pt))))
    (ρ : Env Γ) :
    (dfDrawRcOptC rE).eval ρ =
      (match rE.eval ρ with
       | some _ => some <$> (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) :
           AdversaryCompDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
             (BitVec 256) (Fig8C Pt) (BitVec 256))
       | none => pure none) := by
  dsimp only [dfDrawRcOptC, Comp.eval, Expr.eval]
  cases rE.eval ρ with
  | none => rfl
  | some _ =>
    simp only [dfIface_liftP_eq, Expr.eval, Expr.v0, map_eq_bind_pure_comp,
      Function.comp_def]
    rfl

/-! ## Braid send step `.eval` -/

section TrackerSendEval

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  {ℓ : ℕ} {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt}
  {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam

private theorem bytesToWordLE256_eq_bytesToKey32 (bs : Bytes) (h : bs.length = 32) :
    _root_.ReductionDsl.bytesToWordLE 256 bs = CryptoGames.HKDF.bytesToKey32 bs := by
  calc _root_.ReductionDsl.bytesToWordLE 256 bs
      = _root_.ReductionDsl.bytesToWordLE 256
          (CryptoGames.HMAC.keyToBytes32 (CryptoGames.HKDF.bytesToKey32 bs)) := by
        rw [SimFig8LoopAndCost.keyToBytes32_bytesToKey32 bs h]
    _ = CryptoGames.HKDF.bytesToKey32 bs :=
        KemFailRedLoopAndCost.bytesToWordLE256_keyToBytes32 _

omit [SampleableType Pt] in
private theorem encRandBvAtomicE_eval_local {Γ : List (Ty ASig)}
    (rqE : Expr AOps Γ BV512) (ρ : Env Γ) (rq : BitVec 512) (hrq : rqE.eval ρ = rq) :
    (encRandBvAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) rqE).eval ρ =
      _root_.ReductionDsl.bytesToWordLE 256
        (CryptoGames.Ratchet.LibsignalSim.simEncRandOf rq).toList := by
  have hlen : ((coinBytes rq).take 32).length = 32 := by simp [coinBytes_length]
  simp only [encRandBvAtomicE, hrq, SimFig8State.eval_sOpPure,
    _root_.ReductionDsl.AtomicPureOp.eval, CryptoGames.Ratchet.LibsignalSim.simEncRandOf]
  exact (bytesToWordLE256_eq_bytesToKey32 ((coinBytes rq).take 32) hlen).symm

private theorem keyToBytesVec32_simEncRandOf_local (rq : BitVec 512) :
    keyToBytesVec32
      (_root_.ReductionDsl.bytesToWordLE 256
        (CryptoGames.Ratchet.LibsignalSim.simEncRandOf rq).toList) =
      CryptoGames.Ratchet.LibsignalSim.simEncRandOf rq :=
  Subtype.ext (KemFailRedLoopAndCost.keyToBytes32_bytesToWordLE256 _
    (CryptoGames.Ratchet.LibsignalSim.simEncRandOf rq).2)

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem spqrBraidSendEval_of_bOkTight_local (st : SimBraidSt C.F)
    (hbok : BOkTight st) (coins : BitVec 512) :
    _root_.ReductionDsl.spqrBraidSendEval (ℓ := ℓ) (Pt := Pt) C.F K
      (V1State.encodeRaw st.into_pb) coins =
      match st.send K (coinBytes coins) with
      | .error (.panic _) => (true, none)
      | .error (.err _) => (false, none)
      | .ok (sOut, _) =>
        (false, some (V1State.encodeRaw sOut.state.into_pb,
          (sOut.msg.epoch,
           (sOut.key.map (fun es => (es.epoch, CryptoGames.HKDF.bytesToKey32 es.secret)),
            _root_.ReductionDsl.spqrMsgPayloadSuffix sOut.msg)))) := by
  have hSendEq : _root_.ReductionDsl.spqrBraidSendEval (ℓ := ℓ) (Pt := Pt) C.F K
      (V1State.encodeRaw st.into_pb) coins =
      Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.spqrBraidSendEval
        (ℓ := ℓ) C.F K (V1State.encodeRaw st.into_pb) coins := rfl
  rw [hSendEq,
    Computational.Proofs.E2E.Dsl.SpqrSimChain.spqrBraidSendEval_of_bOkTight (ℓ := ℓ) C.F K st hbok coins]
  rcases st.send K (coinBytes coins) with ⟨err⟩ | ⟨out, _⟩
  · cases err <;> rfl
  · rfl

omit [SampleableType Pt] in
private theorem eval_pGet_party_local {Γ : List (Ty ASig)} {t : Ty ASig}
    (pE : Expr AOps Γ (.prod t t)) (qE : Expr AOps Γ .bool) (ρ : Env Γ)
    (f : Party → t.denote) (Q : Party)
    (hp : pE.eval ρ = (f .A, f .B)) (hq : qE.eval ρ = partyToBool Q) :
    (pGet pE qE).eval ρ = f Q := by
  cases Q <;> simp [pGet, Expr.eval, Expr.v0, hp, hq, partyToBool]

omit [SampleableType Pt] in
private theorem eval_pSet_party_local {Γ : List (Ty ASig)} {t : Ty ASig}
    (pE : Expr AOps Γ (.prod t t)) (qE : Expr AOps Γ .bool) (vE : Expr AOps Γ t) (ρ : Env Γ)
    (f : Party → t.denote) (Q : Party) (v : t.denote)
    (hp : pE.eval ρ = (f .A, f .B)) (hq : qE.eval ρ = partyToBool Q) (hv : vE.eval ρ = v) :
    (pSet pE qE vE).eval ρ = (Function.update f Q v .A, Function.update f Q v .B) := by
  cases Q <;> simp [pSet, Expr.eval, Expr.v0, hp, hq, hv, partyToBool, Function.update]

omit [SampleableType Pt] in
private theorem nextKemCoinsAtomicE_eval_local {Γ : List (Ty ASig)}
    (cE : Expr AOps Γ (kemCoinsT ℓ Pt)) (v1QE : Expr AOps Γ (B 32))
    (rqE : Expr AOps Γ BV512) (ρ : Env Γ)
    (c : CryptoGames.Ratchet.LibsignalSim.SimKemCoins) (stQ : SimBraidSt C.F) (rq : BitVec 512)
    (hc : cE.eval ρ = KemFailRedInit.kemCoinsAtomicEnc c)
    (hv1 : v1QE.eval ρ = V1State.encodeRaw stQ.into_pb)
    (hrq : rqE.eval ρ = rq) :
    (nextKemCoinsAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) cE v1QE rqE).eval ρ =
      KemFailRedInit.kemCoinsAtomicEnc
        (CryptoGames.Ratchet.LibsignalSim.simNextKemCoins C.F c stQ (coinBytes rq)) := by
  simp only [nextKemCoinsAtomicE, SimFig8State.eval_eLet, Expr.eval, hc, hv1, hrq]
  rcases c with _ | ⟨s⟩ | ⟨s, r⟩
  · simp only [KemFailRedInit.kemCoinsAtomicEnc, Expr.eval, Expr.v0, Expr.v1, Env.get]
    rw [isKeysUnsampledV1E_eval _ _ stQ (by simp [Expr.eval])]
    cases stQ <;>
      simp [CryptoGames.Ratchet.LibsignalSim.simNextKemCoins,
        coinBytes_length, List.take_of_length_le, KemFailRedLoopAndCost.bytesToWordLE512_coinBytes]
  · simp only [KemFailRedInit.kemCoinsAtomicEnc, Expr.eval, Expr.v0, Expr.v2, Env.get]
    rw [isHeaderReceivedV1E_eval _ _ stQ (by simp [Expr.eval])]
    cases stQ <;>
      simp [CryptoGames.Ratchet.LibsignalSim.simNextKemCoins, coinBytes_length]
    exact encRandBvAtomicE_eval_local _ _ rq (by simp [Expr.eval])
  · simp only [KemFailRedInit.kemCoinsAtomicEnc, Expr.eval, Expr.v0, Env.get]
    cases stQ <;> simp [CryptoGames.Ratchet.LibsignalSim.simNextKemCoins]

private def simNextKemCand (tr : SimKemFailTrack C.F) (Q : Party) (r : BitVec 512) :
    Option (CryptoGames.Ratchet.LibsignalSim.SimKemSeed ×
      CryptoGames.Ratchet.LibsignalSim.SimKemEncRand) :=
  match tr.cand with
  | some p => some p
  | none =>
    if CryptoGames.Ratchet.LibsignalSim.simEkSideIsA tr.e != (Q == .A) then
      match tr.c, tr.st Q with
      | .seed s, .headerReceived _ =>
        if K.honestExchangeFails s (CryptoGames.Ratchet.LibsignalSim.simEncRandOf r) then
          some (s, CryptoGames.Ratchet.LibsignalSim.simEncRandOf r)
        else none
      | _, _ => none
    else none

omit [SampleableType Pt] in
private theorem nextKemCandPolyC_eval {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    {Γ : List (Ty ASig)}
    (trE : Expr AOps Γ (kemTrackT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (rqE : Expr AOps Γ BV512) (ρ : Env Γ)
    (tr : SimKemFailTrack C.F) (Q : Party) (rq : BitVec 512)
    (htr : trE.eval ρ = kemTrackAtomicEnc tr) (hqB : qBE.eval ρ = partyToBool Q)
    (hrq : rqE.eval ρ = rq) :
    (nextKemCandPolyC (I := I) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) trE qBE rqE).eval ρ =
      pure ((simNextKemCand (C := C) (K := K) tr Q rq).map
        KemFailRedLoopAndCost.kemCandVecToBv) := by
  simp only [nextKemCandPolyC, Comp.eval, Expr.eval, htr, hqB, hrq, pure_bind]
  set p0 : (Ty.prod (kemTrackT ℓ Pt) (Ty.prod .bool BV512)).denote :=
    (kemTrackAtomicEnc tr, (partyToBool Q, rq))
  rcases hCand : tr.cand with _ | candVal
  · have hCandE : (trE_cand (O' := AOps) (.fst .v0)).eval (.cons p0 ρ) = none := by
      simp [trE_cand, p0, kemTrackAtomicEnc, hCand, Expr.eval, Expr.v0]
    simp only [hCandE, simNextKemCand, hCand]
    have hv1Q : (pGet (trE_st (O' := AOps) (.fst .v0)) (.fst (.snd .v0))).eval (.cons p0 ρ) =
        V1State.encodeRaw (tr.st Q).into_pb := by
      refine eval_pGet_party_local (t := B 32) _ _ _ (fun P => V1State.encodeRaw (tr.st P).into_pb) Q ?_ ?_
      · simp [trE_st, p0, kemTrackAtomicEnc, Expr.eval, Expr.v0]
      · simp [p0, Expr.eval, Expr.v0]
    have hEkEq : (boolEqE
        (ekSideIsAE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
          (decT := decT) (lam := lam) (trE_e (.fst .v0)))
        (.fst (.snd .v0))).eval (.cons p0 ρ) =
        (CryptoGames.Ratchet.LibsignalSim.simEkSideIsA tr.e != (Q == .A)) := by
      simp only [boolEqE, ekSideIsAE, trE_e, p0, kemTrackAtomicEnc, Expr.eval, Expr.v0, Env.get,
        SimFig8State.eval_sOpPure, _root_.ReductionDsl.AtomicPureOp.eval,
        CryptoGames.Ratchet.LibsignalSim.simEkSideIsA]
      cases Q <;> cases decide (tr.e.toNat % 2 = 1) <;> rfl
    simp only [hEkEq, isHeaderReceivedV1E_eval _ _ (tr.st Q) hv1Q]
    cases hSide : (CryptoGames.Ratchet.LibsignalSim.simEkSideIsA tr.e != (Q == .A))
    · simp
    · simp only [Bool.true_and, ↓reduceIte]
      generalize tr.st Q = stQ at hv1Q ⊢
      rcases stQ with _ | _ | _ | _ | _ | _ | _ | hdrSt | _ | _ | _ | _ <;>
        try (rcases tr.c with _ | _ | _ <;> (simp; done))
      rcases hC : tr.c with _ | ⟨s⟩ | ⟨s, r0⟩
      · simp [trE_c, p0, kemTrackAtomicEnc, hC, KemFailRedInit.kemCoinsAtomicEnc,
          Expr.eval, Expr.v0]
      · set sBv : (BV512 (ℓ := ℓ) (Pt := Pt)).denote :=
          _root_.ReductionDsl.bytesToWordLE 512 s.toList
        set sInl : (Ty.sum (S := ASig) BV512 (.prod BV512 BV256)).denote := Sum.inl sBv
        have hTrC : (trE_c (O' := AOps) (.fst .v0)).eval (.cons p0 ρ) = Sum.inr sInl := by
          simp [trE_c, p0, kemTrackAtomicEnc, hC, KemFailRedInit.kemCoinsAtomicEnc, sInl, sBv,
            Expr.eval, Expr.v0]
        have hV0Inl : (Expr.v0 : Expr AOps _ _).eval (.cons sInl (.cons p0 ρ)) = Sum.inl sBv := by
          simp [sInl, Expr.eval, Expr.v0]
        simp only [hTrC, hV0Inl]
        have hHef : (honestExchangeFailsPolyC (I := I) (C := C) (K := K) (Dh := Dh)
            (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) .v0
            (encRandBvAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
              (decT := decT) (lam := lam) (.snd (.snd .v2)))).eval
            (.cons sBv (.cons sInl (.cons p0 ρ))) =
            pure (K.honestExchangeFails s (CryptoGames.Ratchet.LibsignalSim.simEncRandOf rq)) := by
          rw [honestExchangeFailsPolyC_eval _ _ _ sBv
            (_root_.ReductionDsl.bytesToWordLE 256
              (CryptoGames.Ratchet.LibsignalSim.simEncRandOf rq).toList)
            (by simp [Expr.eval, Expr.v0])
            (encRandBvAtomicE_eval_local _ _ rq (by simp [p0, Expr.eval, Expr.v2]))]
          have hsVec : (⟨coinBytes sBv, coinBytes_length _⟩ : List.Vector (BitVec 8) 64) = s :=
            Subtype.ext (KemFailRedLoopAndCost.coinBytes_bytesToWordLE512 s.toList s.2)
          rw [hsVec, keyToBytesVec32_simEncRandOf_local rq]
        rw [hHef, pure_bind]
        have hRand3 (b : Ty.bool.denote) :
            (encRandBvAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
              (decT := decT) (lam := lam) (.snd (.snd .v3))).eval
              (.cons b (.cons sBv (.cons sInl (.cons p0 ρ)))) =
            _root_.ReductionDsl.bytesToWordLE 256
              (CryptoGames.Ratchet.LibsignalSim.simEncRandOf rq).toList :=
          encRandBvAtomicE_eval_local _ _ rq (by simp [p0, Expr.eval, Expr.v3])
        cases K.honestExchangeFails s (CryptoGames.Ratchet.LibsignalSim.simEncRandOf rq) <;>
          simp [sBv, Expr.eval, Expr.v0, Expr.v1, hRand3,
            KemFailRedLoopAndCost.kemCandVecToBv]
      · simp [trE_c, p0, kemTrackAtomicEnc, hC, KemFailRedInit.kemCoinsAtomicEnc,
          Expr.eval, Expr.v0]
  · simp [trE_cand, p0, kemTrackAtomicEnc, hCand, simNextKemCand,
      Expr.eval, Expr.v0]

private theorem simStepKemFailSend_eq_local (tr : SimKemFailTrack C.F) (Q : Party) (r : BitVec 512) :
    simStepKemFailSend C.F K tr Q r =
      let cand' := simNextKemCand (C := C) (K := K) tr Q r
      let tape := coinBytes r
      match (tr.st Q).send K tape with
      | .ok (out, _) =>
        let E := out.msg.epoch.toNat - 1
        let n := tr.sendCtr Q E
        { tr with
          c := CryptoGames.Ratchet.LibsignalSim.simNextKemCoins C.F tr.c (tr.st Q) tape
          st := Function.update tr.st Q out.state
          sentB := tr.sentB ++ [(out.msg, BitVec.ofNat 32 (n + 1))]
          sendCtr := Function.update tr.sendCtr Q (Function.update (tr.sendCtr Q) E (n + 1))
          cand := cand' }
      | .error _ => { tr with cand := cand' } := by
  simp only [simStepKemFailSend, simNextKemCand]
  rcases (tr.st Q).send K (coinBytes r) with _ | ⟨out, _⟩ <;> (
    dsimp only; congr 1
    rcases tr.cand with _ | _
    · by_cases hS : (CryptoGames.Ratchet.LibsignalSim.simEkSideIsA tr.e != (Q == .A)) = true
      · simp only [hS, ↓reduceIte]; rcases tr.c with _ | _ | _ <;> rcases tr.st Q <;> rfl
      · simp [hS]
    · rfl)

omit [SampleableType Pt] in
theorem stepKemFailSendPolyC_eval (q : ℕ) {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    {Γ : List (Ty ASig)}
    (trE : Expr AOps Γ (kemTrackT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (rqE : Expr AOps Γ BV512) (ρ : Env Γ)
    (tr : KemFailTrackState C.F) (Q : Party) (rq : BitVec 512)
    (htr : trE.eval ρ = kemTrackAtomicEnc (kemTrackEnc tr)) (hqB : qBE.eval ρ = partyToBool Q)
    (hrq : rqE.eval ρ = rq)
    (hBOk : BOkTight (tr.st Q)) (hSentLen : tr.sentB.length ≤ q) :
    (stepKemFailSendPolyC q (I := I) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) trE qBE rqE).eval ρ =
      let tr' := stepKemFailSend C.F K tr Q rq
      pure (kemTrackAtomicEnc (kemTrackEnc tr'),
            kemTrackAtomicEnc (kemTrackEnc { tr with cand := tr'.cand })) := by
  set sTr := kemTrackEnc tr
  have hBOk' : BOkTight (sTr.st Q) := by simpa [sTr, kemTrackEnc] using hBOk
  have hSentLen' : sTr.sentB.length ≤ q := by simpa [sTr, kemTrackEnc] using hSentLen
  simp only [stepKemFailSendPolyC, Comp.eval, Expr.eval, htr, hqB, hrq, pure_bind]
  set p0 : (Ty.prod (kemTrackT ℓ Pt) (Ty.prod .bool BV512)).denote :=
    (kemTrackAtomicEnc sTr, (partyToBool Q, rq))
  rw [nextKemCandPolyC_eval _ _ _ (.cons p0 ρ) sTr Q rq
    (by simp [p0, Expr.eval, Expr.v0])
    (by simp [p0, Expr.eval, Expr.v0])
    (by simp [p0, Expr.eval, Expr.v0]), pure_bind]
  set cand' := simNextKemCand (C := C) (K := K) sTr Q rq
  set candBvD : (Ty.opt (Ty.prod (S := ASig) BV512 BV256)).denote :=
    cand'.map KemFailRedLoopAndCost.kemCandVecToBv
  set ρ0 := Env.cons candBvD (.cons p0 ρ)
  set pPost : (Ty.prod (kemTrackT ℓ Pt)
      (Ty.prod .bool (Ty.prod BV512 (.opt (.prod BV512 BV256))))).denote :=
    (kemTrackAtomicEnc sTr, (partyToBool Q, (rq, candBvD)))
  have hTup : (Expr.pair (O := AOps) (.fst .v1)
      (.pair (.fst (.snd .v1)) (.pair (.snd (.snd .v1)) .v0))).eval ρ0 = pPost := by
    simp [ρ0, p0, pPost, Expr.eval, Expr.v0, Expr.v1]
  simp only [stepPostKemSendE, SimFig8State.eval_eLet]
  rw [hTup]
  have hv1Q : (pGet (trE_st (O' := AOps) (.fst .v0)) (.fst (.snd .v0))).eval (.cons pPost ρ0) =
      V1State.encodeRaw (sTr.st Q).into_pb := by
    refine eval_pGet_party_local (t := B 32) _ _ _ (fun P => V1State.encodeRaw (sTr.st P).into_pb) Q ?_ ?_
    · simp [trE_st, pPost, kemTrackAtomicEnc, Expr.eval, Expr.v0]
    · simp [pPost, Expr.eval, Expr.v0]
  have hOptEval : (Expr.snd (sOpSpqr (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) .spqrBraidSend
      (.pair (pGet (trE_st (.fst .v0)) (.fst (.snd .v0))) (.fst (.snd (.snd .v0)))))).eval
      (.cons pPost ρ0) =
      (_root_.ReductionDsl.spqrBraidSendEval (ℓ := ℓ) (Pt := Pt) C.F K
        (V1State.encodeRaw (sTr.st Q).into_pb) rq).2 := by
    simp only [Expr.eval, SimFig8State.eval_sOpSpqr, _root_.ReductionDsl.AtomicSpqrKemOp.eval]
    rw [hv1Q]; simp [pPost, Expr.eval, Expr.v0]
  have hCaseOpt {Γ' : List (Ty ASig)} {α β : Ty ASig} (e : Expr AOps Γ' (.opt α))
      (nB : Expr AOps Γ' β) (sB : Expr AOps (α :: Γ') β) (ρ' : Env Γ') :
      (Expr.caseOpt e nB sB).eval ρ' =
        match e.eval ρ' with | none => nB.eval ρ' | some x => sB.eval (.cons x ρ') := by
    simp only [Expr.eval]; cases e.eval ρ' <;> rfl
  rw [hCaseOpt, hOptEval, spqrBraidSendEval_of_bOkTight_local (sTr.st Q) hBOk' rq,
    ← CryptoGames.Ratchet.LibsignalSim.simStepKemFailSend_kemTrackEnc,
    simStepKemFailSend_eq_local (C := C) (K := K) sTr Q rq]
  have hCandEq : (kemTrackEnc { tr with cand := (stepKemFailSend C.F K tr Q rq).cand }) =
      { sTr with cand := (simStepKemFailSend C.F K sTr Q rq).cand } := by
    rw [CryptoGames.Ratchet.LibsignalSim.simStepKemFailSend_kemTrackEnc]
    rfl
  rw [hCandEq, simStepKemFailSend_eq_local (C := C) (K := K) sTr Q rq]
  dsimp only
  rcases hSend : (sTr.st Q).send K (coinBytes rq) with ⟨err⟩ | ⟨out, tape'⟩
  · cases err <;>
      simp [trMk, trE_e, trE_c, trE_st, trE_sentB, trE_sendCtr, pPost, candBvD, cand',
        kemTrackAtomicEnc, Expr.eval, Expr.v0]
  · dsimp only
    set sOutD : (Ty.prod (B (ℓ := ℓ) (Pt := Pt) 32)
        (Ty.prod U64 (Ty.prod (.opt (.prod U64 BV256)) (B (ℓ := ℓ) (Pt := Pt) 64)))).denote :=
      (V1State.encodeRaw out.state.into_pb, (out.msg.epoch,
        (out.key.map (fun es => (es.epoch, CryptoGames.HKDF.bytesToKey32 es.secret)),
          _root_.ReductionDsl.spqrMsgPayloadSuffix out.msg)))
    set ρS := Env.cons sOutD (.cons pPost ρ0)
    have hv1Q1 : (pGet (trE_st (O' := AOps) (.fst .v1)) (.fst (.snd .v1))).eval ρS =
        V1State.encodeRaw (sTr.st Q).into_pb := by
      refine eval_pGet_party_local (t := B 32) _ _ _ (fun P => V1State.encodeRaw (sTr.st P).into_pb) Q ?_ ?_
      · simp [trE_st, ρS, pPost, kemTrackAtomicEnc, Expr.eval, Expr.v1]
      · simp [ρS, pPost, Expr.eval, Expr.v1]
    have hCtrQ : (pGet (trE_sendCtr (O' := AOps) (.fst .v1)) (.fst (.snd .v1))).eval ρS =
        sTr.sendCtr Q := by
      refine eval_pGet_party_local (trE_sendCtr (O' := AOps) (.fst .v1)) _ _ sTr.sendCtr Q ?_ ?_
      · simp [trE_sendCtr, ρS, pPost, kemTrackAtomicEnc, Expr.eval, Expr.v1]
      · simp [ρS, pPost, Expr.eval, Expr.v1]
    have hC' : (nextKemCoinsAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) (trE_c (.fst .v1))
        (pGet (trE_st (.fst .v1)) (.fst (.snd .v1))) (.fst (.snd (.snd .v1)))).eval ρS =
        KemFailRedInit.kemCoinsAtomicEnc
          (CryptoGames.Ratchet.LibsignalSim.simNextKemCoins C.F sTr.c (sTr.st Q) (coinBytes rq)) := by
      refine nextKemCoinsAtomicE_eval_local _ _ _ ρS sTr.c (sTr.st Q) rq ?_ hv1Q1 ?_
      · simp [trE_c, ρS, pPost, kemTrackAtomicEnc, Expr.eval, Expr.v1]
      · simp [ρS, pPost, Expr.eval, Expr.v1]
    have hSt' : (pSet (trE_st (O' := AOps) (.fst .v1)) (.fst (.snd .v1)) (.fst .v0)).eval ρS =
        (V1State.encodeRaw (Function.update sTr.st Q out.state .A).into_pb,
         V1State.encodeRaw (Function.update sTr.st Q out.state .B).into_pb) := by
      have hSet0 : (pSet (trE_st (O' := AOps) (.fst .v1)) (.fst (.snd .v1)) (.fst .v0)).eval ρS =
          (Function.update (fun P => V1State.encodeRaw (sTr.st P).into_pb) Q
             (V1State.encodeRaw out.state.into_pb) .A,
           Function.update (fun P => V1State.encodeRaw (sTr.st P).into_pb) Q
             (V1State.encodeRaw out.state.into_pb) .B) := by
        refine eval_pSet_party_local (t := B 32) _ _ _ ρS
          (fun P => V1State.encodeRaw (sTr.st P).into_pb) Q
          (V1State.encodeRaw out.state.into_pb) ?_ ?_ ?_
        · simp [trE_st, ρS, pPost, kemTrackAtomicEnc, Expr.eval, Expr.v1]
        · simp [ρS, pPost, Expr.eval, Expr.v1]
        · simp [ρS, sOutD, Expr.eval, Expr.v0]
      rw [hSet0]; cases Q <;> simp [Function.update]
    simp only [trMk, Expr.eval, hC', hSt', hCtrQ, SimFig8State.eval_sOpPure,
      _root_.ReductionDsl.AtomicPureOp.eval]
    simp only [pSet, Expr.eval, hCtrQ, SimFig8State.eval_sOpPure,
      _root_.ReductionDsl.AtomicPureOp.eval]
    have hTake : (List.map (fun x => ((x.1.epoch, _root_.ReductionDsl.spqrMsgPayloadSuffix x.1), x.2))
        sTr.sentB ++ [((out.msg.epoch, _root_.ReductionDsl.spqrMsgPayloadSuffix out.msg),
          BitVec.ofNat 32 (sTr.sendCtr Q (out.msg.epoch.toNat - 1) + 1))]).take (q + 1) =
        List.map (fun x => ((x.1.epoch, _root_.ReductionDsl.spqrMsgPayloadSuffix x.1), x.2))
          (sTr.sentB ++ [(out.msg, BitVec.ofNat 32 (sTr.sendCtr Q (out.msg.epoch.toNat - 1) + 1))]) := by
      rw [List.take_of_length_le (by simp; omega), List.map_append]; rfl
    cases Q <;> (
      simp [ρS, sOutD, pPost, candBvD, cand', trE_e, trE_c, trE_st, trE_sentB, trE_sendCtr,
        partyToBool, kemTrackAtomicEnc, Expr.eval, Expr.v0, Expr.v1, hTake, Function.update]
      ext j; by_cases hj : j = out.msg.epoch.toNat - 1 <;> simp [hj, Function.update])

end TrackerSendEval

/-! ## Halted `.send` step `.eval` -/

section SendStepEval

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
  simp only [dfNatNeE, eval_eLet, dfOrE_eval, Expr.eval, Expr.v0, _root_.ReductionDsl.Env.get]
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
    simp [SimFig8State.eval_sOpPure, _root_.ReductionDsl.AtomicPureOp.eval]
  · have hd : decide (n < 1) = false := decide_eq_false h
    rw [hd]
    simp only [Bool.false_eq_true, ↓reduceIte, SimFig8State.eval_sOpPure,
      _root_.ReductionDsl.AtomicPureOp.eval, Expr.eval, Expr.v0, _root_.ReductionDsl.Env.get]
    have hn : n = (n - 1) + 1 := by omega
    conv_lhs => rw [hn]
    rw [BitVec.ofNat_add]
    exact BitVec.add_sub_cancel _ _

private theorem dfPostSendStateE_eval_halted
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (stE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (dfFullT ℓ Pt))
    (s1E : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (simMirT ℓ Pt))
    (qE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ .bool)
    (m0E : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (PlainT (ℓ := ℓ) (Pt := Pt)))
    (isChallE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ .bool)
    (pq'E : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (B (ℓ := ℓ) (Pt := Pt) 32))
    (pnE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (U32 (ℓ := ℓ) (Pt := Pt)))
    (cE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (fig8CtT (ℓ := ℓ) (Pt := Pt)))
    (ρ : Env Γ)
    (sC : LibsignalToModularSchemeSimState Bytes Pt ℓ) (ex : List (Fig8C Pt))
    (s₁ : GameState Unit (Plain ℓ) Bytes) (Q : Party) (m₀ : Plain ℓ) (isChall : Bool)
    (pq' : Bytes) (pn : BitVec 32) (c : Fig8C Pt)
    (hst : stE.eval ρ = dfFullEnc (sC, ex)) (hs1 : s1E.eval ρ = simMirEnc s₁)
    (hq : qE.eval ρ = partyEnc Q) (hm0 : m0E.eval ρ = m₀) (hch : isChallE.eval ρ = isChall)
    (hpq : pq'E.eval ρ = pq') (hpn : pnE.eval ρ = pn)
    (hc : cE.eval ρ = fig8CtV (ℓ := ℓ) (Pt := Pt) c) :
    (dfPostSendStateE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB stE s1E qE m0E isChallE pq'E pnE cE).eval ρ =
    ((some (toWire c), (none, none)),
     dfFullEnc
       (scPostSendPure (paramsV1 C K idA idB) Dh encPt encT lam sC s₁ Q m₀ isChall pq' pn c,
        c :: ex)) := by
  let AOps := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam
  dsimp only [dfPostSendStateE]
  rw [eval_eLet, eval_eLet]
  let tup : (dfPostSendArgT ℓ Pt).denote :=
    (dfFullEnc (sC, ex),
     (simMirEnc (Pt := Pt) s₁,
      (partyEnc Q, (m₀, (isChall, (pq', (pn, fig8CtV (ℓ := ℓ) (Pt := Pt) c)))))))
  have htup : (Expr.pair stE (.pair s1E (.pair qE (.pair m0E
      (.pair isChallE (.pair pq'E (.pair pnE cE))))))).eval ρ = tup := by
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
    cases Q <;> simp [ρ2, ρ1, tup, dfFullEnc, pGet, scKept, simFullEnc, partyEnc,
      Expr.eval, Expr.v0, Expr.v1]
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
  dsimp only [dfSmRSendSomeE, scMk, ssMk, Expr.eval, dfFullEnc, scPostSendPure]
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
      · cases Q <;> simp [ρ2, ρ1, tup, dfFullEnc, pSet, ssPq, ssPn, ssUnackA, ssHonest, ssChains,
          ssAmb, ssStopped, scBase, simFullEnc, simBaseEnc, honestPairEnc, partyEnc,
          Function.update, Expr.eval, Expr.v0, Expr.v1]
      · dsimp only [pSet, Expr.eval]
        rw [hks]
        cases Q <;> simp [ρ2, ρ1, tup, dfFullEnc, scKept, simFullEnc, partyEnc,
          Function.update, Expr.eval, Expr.v0, Expr.v1]
      · simp only [Expr.eval, hkQ]
        rcases hfull : (sC.kept Q).full with _ | st
        · simp [keptEnc, hfull, ρ2, ρ1, tup, dfFullEnc, scSent, simFullEnc, Expr.eval, Expr.v1]
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
          · simp [hs, ρ3, ρ2, ρ1, tup, dfFullEnc, scSent, simFullEnc, Expr.eval, Expr.v2]
          · have hs0 : st.id.sendsIn (st.tcur + 1) = false := Bool.eq_false_iff.mpr hs
            simp only [hs0, Bool.false_eq_true, ↓reduceIte]
            rcases hvs : st.vS with _ | vs
            · simp [ρ3, ρ2, ρ1, tup, dfFullEnc, f8VS, fig8StV, hvs, scSent, simFullEnc,
                Expr.eval, Expr.v0, Expr.v2]
            · simp [ρ3, ρ2, ρ1, tup, dfFullEnc, f8VS, fig8StV, hvs, scSent, simFullEnc, sentEntryEnc,
                Expr.eval, Expr.v0]
      · simp [ρ2, ρ1, tup, dfFullEnc, scSnaps, simFullEnc, Expr.eval, Expr.v1]
    dsimp only [paramsV1]
    exact hFull
  · simp [ρ2, ρ1, tup, dfFullEnc, Expr.eval, Expr.v1]

theorem dfSendStepHaltedC_eval
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (stHaltedE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (dfHaltedT ℓ Pt))
    (qE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ .bool)
    (m0E : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (PlainT (ℓ := ℓ) (Pt := Pt)))
    (chalE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ
      (.opt (PlainT (ℓ := ℓ) (Pt := Pt))))
    (rE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ
      (.opt (BV512 (ℓ := ℓ) (Pt := Pt))))
    (ρ : Env Γ)
    (sC : LibsignalToModularSchemeSimState Bytes Pt ℓ) (ex : List (Fig8C Pt))
    (tr : KemFailTrackState C.F) (Q : Party)
    (hst : stHaltedE.eval ρ = dfHaltedEnc ((sC, ex), tr))
    (hq : qE.eval ρ = partyEnc Q)
    (hEx : SanSnapExtra C K sC)
    (hBOk : BOkTight (tr.st Q))
    (hSentLen : tr.sentB.length ≤ q) :
    (dfSendStepHaltedC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB qep q stHaltedE qE m0E chalE rE).eval ρ =
    Prod.map (fun r => (r, (none, none))) dfHaltedEnc <$>
      semSendTrackHalted (paramsV1 C K idA idB) K Dh encPt encT lam qep
        sC ex tr Q (m0E.eval ρ) (chalE.eval ρ) (rE.eval ρ) := by
  let AOps := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam
  generalize hm0 : m0E.eval ρ = m₀
  generalize hchal : chalE.eval ρ = chal
  generalize hr : rE.eval ρ = r
  dsimp only [dfSendStepHaltedC, semSendTrackHalted]
  let inp : (dfSendHaltedInpT ℓ Pt).denote :=
    (dfHaltedEnc ((sC, ex), tr), (partyEnc Q, (m₀, (chal, r))))
  have hinp : (Expr.pair stHaltedE (.pair qE (.pair m0E (.pair chalE rE)))).eval ρ = inp := by
    simp [inp, Expr.eval, hst, hq, hm0, hchal, hr]
  rw [Comp.eval, Comp.eval, hinp, pure_bind]
  let ρ0 : Env (dfSendHaltedInpT ℓ Pt :: Γ) := Env.cons inp ρ
  have hmir0 : (ssMir (scBase (.fst (.fst (.fst .v0)))) : Expr AOps _ (simMirT ℓ Pt)).eval ρ0 =
      simMirEnc sC.base.mir := rfl
  have hq0 : (Expr.fst (.snd .v0) : Expr AOps _ .bool).eval ρ0 = partyEnc Q := rfl
  have hg1 :
      (dfOrE (ssStopped (scBase (.fst (.fst (.fst .v0)))))
        (dfOrE (mWin (ssMir (scBase (.fst (.fst (.fst .v0))))))
          (.not (mNoBobEpoch0E (ssMir (scBase (.fst (.fst (.fst .v0))))) (.fst (.snd .v0))))) :
        Expr AOps _ .bool).eval ρ0 =
      (sC.base.stopped || sC.base.mir.win || !(noBobSendInEpoch0 sC.base.mir Q)) := by
    simp only [dfOrE_eval, Expr.eval]
    rw [mNoBobEpoch0E_eval _ _ ρ0 sC.base.mir Q hmir0 hq0]
    have hstop0 : (ssStopped (scBase (.fst (.fst (.fst .v0)))) : Expr AOps _ .bool).eval ρ0 =
        sC.base.stopped := rfl
    have hwin0 : (mWin (ssMir (scBase (.fst (.fst (.fst .v0))))) : Expr AOps _ .bool).eval ρ0 =
        sC.base.mir.win := rfl
    rw [hstop0, hwin0, Bool.or_assoc]
  rw [Comp.eval, hg1]
  cases hstop : (sC.base.stopped || sC.base.mir.win || !(noBobSendInEpoch0 sC.base.mir Q))
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hep : (mEpMgmtE qep (ssMir (scBase (.fst (.fst (.fst .v0))))) (.fst (.snd .v0))
        (dfIsSomeE (.snd (.snd (.snd (.snd .v0))))) :
        Expr AOps _ (.opt (simMirT ℓ Pt))).eval ρ0 =
        (sC.base.mir.epMgmt 3 qep Q r.isSome).map (simMirEnc (Pt := Pt)) := by
      rw [mEpMgmtE_eval qep _ _ _ ρ0 sC.base.mir Q hmir0 hq0, dfIsSomeE_eval]
      rfl
    rw [Comp.eval, hep]
    rcases hep_res : sC.base.mir.epMgmt 3 qep Q r.isSome with _ | s₁
    · dsimp only [Option.map, Comp.eval, dfSmRNoneE, Expr.eval, Expr.v0, ρ0, inp]
      rw [_root_.ReductionDsl.Env.get_cons_zero, map_pure]
      rfl
    · dsimp only [Option.map]
      let ρ1 : Env (simMirT ℓ Pt :: dfSendHaltedInpT ℓ Pt :: Γ) :=
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
        have hr1 : (Expr.snd (.snd (.snd (.snd .v1))) :
            Expr AOps _ (.opt (BV512 (ℓ := ℓ) (Pt := Pt)))).eval ρ1 = r := rfl
        rw [Comp.eval, map_bind]
        refine advDF_bind_congr ?_ fun rq => ?_
        · rw [dfDrawRqC_eval _ ρ1, hr1]
          cases r with
          | none =>
            exact congrArg (fun p : ProbComp (BitVec 512) =>
              (liftM p : AdversaryCompDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
                (BitVec 256) (Fig8C Pt) (BitVec 512))) rfl
          | some _ => rfl
        let ρ2 : Env (BV512 (ℓ := ℓ) (Pt := Pt) :: simMirT ℓ Pt ::
            dfSendHaltedInpT ℓ Pt :: Γ) := Env.cons rq ρ1
        have hStepTr := stepKemFailSendPolyC_eval (C := C) (K := K) (Dh := Dh)
          (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
          q (I := fig8SmIfaceDF ℓ Pt) (.snd (.fst .v2)) (.fst (.snd .v2)) .v0 ρ2
          tr Q rq rfl (partyToBool_eq_partyEnc Q).symm rfl hBOk hSentLen
        rw [Comp.eval, hStepTr, pure_bind]
        set tr' := stepKemFailSend C.F K tr Q rq
        let trPairT : Ty (atomicSig ℓ Pt) := .prod (kemTrackT ℓ Pt) (kemTrackT ℓ Pt)
        let trPairVal : trPairT.denote :=
          (kemTrackAtomicEnc (ℓ := ℓ) (Pt := Pt) (kemTrackEnc tr'),
           kemTrackAtomicEnc (ℓ := ℓ) (Pt := Pt) (kemTrackEnc { tr with cand := tr'.cand }))
        let ρ3 : Env (trPairT :: BV512 (ℓ := ℓ) (Pt := Pt) :: simMirT ℓ Pt ::
            dfSendHaltedInpT ℓ Pt :: Γ) := Env.cons trPairVal ρ2
        have hCandIsSome :
            (dfIsSomeE (trE_cand (.fst .v0)) : Expr AOps _ .bool).eval ρ3 =
              tr'.cand.isSome := by
          rw [dfIsSomeE_eval]
          dsimp only [ρ3, trPairVal, trE_cand, kemTrackAtomicEnc, kemTrackEnc,
            Expr.eval, Expr.v0]
          rw [_root_.ReductionDsl.Env.get_cons_zero]
          rcases tr'.cand with _ | _ <;> rfl
        have htr'_eq : stepKemFailSend (paramsV1 C K idA idB).C.F K tr Q rq = tr' := rfl
        rw [Comp.eval, hCandIsSome, htr'_eq]
        cases hcand : tr'.cand.isSome
        · simp only [Bool.false_eq_true, ↓reduceIte]
          have hr3 : (Expr.snd (.snd (.snd (.snd .v3))) :
              Expr AOps _ (.opt (BV512 (ℓ := ℓ) (Pt := Pt)))).eval ρ3 = r := rfl
          rw [Comp.eval, map_bind]
          refine advDF_bind_congr ?_ fun rc => ?_
          · rw [dfDrawRcOptC_eval _ ρ3, hr3]
            cases r with
            | none => rfl
            | some _ =>
              exact congrArg (fun p : ProbComp (BitVec 256) =>
                some <$> (liftM p : AdversaryCompDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
                  (BitVec 256) (Fig8C Pt) (BitVec 256))) rfl
          let Γ4 : List (Ty (atomicSig ℓ Pt)) :=
            .opt (BV256 (ℓ := ℓ) (Pt := Pt)) :: trPairT ::
              BV512 (ℓ := ℓ) (Pt := Pt) :: simMirT ℓ Pt :: dfSendHaltedInpT ℓ Pt :: Γ
          let ρ4 : Env Γ4 := Env.cons rc ρ3
          let pn : BitVec 32 := if s₁.epoch Q ≠ sC.base.mir.epoch Q then
            BitVec.ofNat 32 (sC.base.mir.idx Q - 1) else sC.base.pn Q
          let inp4E : Expr AOps Γ4 (dfSendHaltedInpT ℓ Pt) :=
            .var (.succ (.succ (.succ (.succ .zero))))
          have hpn : (Expr.ite
              (dfNatNeE (pGet (mEpoch .v3) (.fst (.snd inp4E)))
                (pGet (mEpoch (ssMir (scBase (.fst (.fst (.fst inp4E)))))) (.fst (.snd inp4E))))
              (dfIdxPredU32E (pGet (mIdx (ssMir (scBase (.fst (.fst (.fst inp4E))))))
                (.fst (.snd inp4E))))
              (pGet (ssPn (scBase (.fst (.fst (.fst inp4E))))) (.fst (.snd inp4E))) :
              Expr AOps _ (U32 (ℓ := ℓ) (Pt := Pt))).eval ρ4 = pn := by
            have hep1 : (pGet (mEpoch .v3) (.fst (.snd inp4E)) : Expr AOps _ .nat).eval ρ4 =
                s₁.epoch Q := by cases Q <;> rfl
            have hep0 : (pGet (mEpoch (ssMir (scBase (.fst (.fst (.fst inp4E))))))
                (.fst (.snd inp4E)) : Expr AOps _ .nat).eval ρ4 = sC.base.mir.epoch Q := by
              cases Q <;> rfl
            have hidx0 : (pGet (mIdx (ssMir (scBase (.fst (.fst (.fst inp4E))))))
                (.fst (.snd inp4E)) : Expr AOps _ .nat).eval ρ4 = sC.base.mir.idx Q := by
              cases Q <;> rfl
            have hpn0 : (pGet (ssPn (scBase (.fst (.fst (.fst inp4E))))) (.fst (.snd inp4E)) :
                Expr AOps _ (U32 (ℓ := ℓ) (Pt := Pt))).eval ρ4 = sC.base.pn Q := by
              cases Q <;> rfl
            change (if (dfNatNeE _ _).eval ρ4 then (dfIdxPredU32E _).eval ρ4
              else (pGet _ _).eval ρ4) = pn
            rw [dfNatNeE_eval, dfIdxPredU32E_eval, hep1, hep0, hidx0, hpn0]
            dsimp only [pn]
            by_cases heq : s₁.epoch Q = sC.base.mir.epoch Q <;> simp [heq]
          rw [Comp.eval, Comp.eval, hpn, pure_bind]
          let Γ5 : List (Ty (atomicSig ℓ Pt)) :=
            U32 (ℓ := ℓ) (Pt := Pt) :: .opt (BV256 (ℓ := ℓ) (Pt := Pt)) :: trPairT ::
              BV512 (ℓ := ℓ) (Pt := Pt) :: simMirT ℓ Pt :: dfSendHaltedInpT ℓ Pt :: Γ
          let ρ5 : Env Γ5 := Env.cons (t := U32 (ℓ := ℓ) (Pt := Pt)) pn ρ4
          let inp5E : Expr AOps Γ5 (dfSendHaltedInpT ℓ Pt) :=
            .var (.succ (.succ (.succ (.succ (.succ .zero)))))
          let base5E : Expr AOps Γ5 (simBaseT ℓ Pt) := scBase (.fst (.fst (.fst inp5E)))
          let q5E : Expr AOps Γ5 .bool := .fst (.snd inp5E)
          let addr5E : Expr AOps Γ5 (.opt (B (ℓ := ℓ) (Pt := Pt) 32)) :=
            .ite (.and (.not q5E) (ssUnackA base5E))
              (optBytesLitE (paramsV1 C K idA idB).addrAB) .none
          let addr : Option Bytes :=
            if Q == Party.A && sC.base.unackA then (paramsV1 C K idA idB).addrAB else none
          have hpq5 : (pGet (ssPq base5E) q5E).eval ρ5 = sC.base.pq Q := by
            cases Q <;> rfl
          have haddr : addr5E.eval ρ5 = addr := by
            change (if _ then (optBytesLitE (paramsV1 C K idA idB).addrAB).eval ρ5 else none) = addr
            rw [optBytesLitE_eval]
            have hq5 : q5E.eval ρ5 = partyEnc Q := rfl
            have hun : (ssUnackA base5E).eval ρ5 = sC.base.unackA := rfl
            cases Q <;> simp [addr, Expr.eval, hq5, hun, partyEnc]
          have hmk_inp : (Expr.pair (pGet (ssPq base5E) q5E)
              (.pair .v3 (.pair .v0 addr5E))).eval ρ5 =
              (sC.base.pq Q, (rq, (pn, addr))) :=
            Prod.ext hpq5 (Prod.ext rfl (Prod.ext rfl haddr))
          rw [Comp.eval,
              mkPubAtomicC_eval (fig8SmIfaceDF ℓ Pt) _ ρ5 (sC.base.pq Q) rq pn addr
                hmk_inp (hEx.1 Q),
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
                  (Env.cons (t := .opt pubPairT) none ρ5) = none from rfl]
            dsimp only [Comp.eval, dfSmRNoneE, Expr.eval, ρ5, ρ4, ρ3, ρ2, ρ1, ρ0, inp,
              trPairVal, dfHaltedEnc]
            simp only [_root_.ReductionDsl.Env.get_cons_zero,
              _root_.ReductionDsl.Env.get_cons_succ, map_pure]
            rfl
          · dsimp only [Option.map]
            let pub : LibsignalMsgPublicPart :=
              ⟨pn, pqmsg, CryptoGames.effectiveHkdfSalt32 salt, addr⟩
            let ρ6 := Env.cons (t := .opt pubPairT) (some (pq', lpubV (ℓ := ℓ) (Pt := Pt) pub)) ρ5
            let ρ7 := Env.cons (t := pubPairT) (pq', lpubV (ℓ := ℓ) (Pt := Pt) pub) ρ6
            let rawQry := match chal with
              | none => transmitQueryDF
                  (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ)
                  (Coins := BitVec 256) (C := Fig8C Pt) Q (pub, m₀) rc
              | some m₁ => challQueryDF
                  (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ)
                  (Coins := BitVec 256) (C := Fig8C Pt) Q (pub, m₀) (pub, m₁) rc
            let Γ7 : List (Ty (atomicSig ℓ Pt)) :=
              pubPairT :: .opt pubPairT :: Γ5
            let inp7E : Expr AOps Γ7 (dfSendHaltedInpT ℓ Pt) :=
              .var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))
            let inp7cE : Expr AOps (PlainT (ℓ := ℓ) (Pt := Pt) :: Γ7) (dfSendHaltedInpT ℓ Pt) :=
              .var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))
            let qComp : Comp AOps (fig8SmIfaceDF ℓ Pt) Γ7 (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))) :=
              .caseOpt (.fst (.snd (.snd (.snd inp7E))))
                (.query (I := fig8SmIfaceDF ℓ Pt) (g := .tr)
                  (.pair (.fst (.snd inp7E))
                    (.pair (.pair (.snd .v0) (.fst (.snd (.snd inp7E)))) .v3)))
                (.query (I := fig8SmIfaceDF ℓ Pt) (g := .ch)
                  (.pair (.fst (.snd inp7cE))
                    (.pair (.pair (.snd .v1) (.fst (.snd (.snd inp7cE))))
                      (.pair (.pair (.snd .v1) .v0)
                        (.var (.succ (.succ (.succ (.succ .zero)))))))))
            have hq_lhs : qComp.eval ρ7 =
                Option.map (fig8CtV (ℓ := ℓ) (Pt := Pt)) <$> rawQry := by
              rcases chal with _ | m₁
              · dsimp only [qComp, inp7E, rawQry, Comp.eval, fig8SmIfaceDF,
                  transmitQueryDF, Expr.eval, Expr.v0, Expr.v3,
                  ρ7, ρ6, ρ5, ρ4, ρ3, ρ2, ρ1, ρ0, inp]
                simp only [_root_.ReductionDsl.Env.get_cons_zero,
                  _root_.ReductionDsl.Env.get_cons_succ]
                rw [boolToParty_partyEnc, lpubOfV_lpubV]
                rfl
              · dsimp only [qComp, inp7E, inp7cE, rawQry, Comp.eval, fig8SmIfaceDF,
                  challQueryDF, Expr.eval, Expr.v0, Expr.v1,
                  ρ7, ρ6, ρ5, ρ4, ρ3, ρ2, ρ1, ρ0, inp]
                simp only [_root_.ReductionDsl.Env.get_cons_zero,
                  _root_.ReductionDsl.Env.get_cons_succ]
                rw [boolToParty_partyEnc, lpubOfV_lpubV]
                rfl
            rw [Comp.eval,
                show (Expr.v0 : Expr AOps _ _).eval ρ6 =
                  some (pq', lpubV (ℓ := ℓ) (Pt := Pt) pub) from rfl]
            dsimp only
            rw [Comp.eval, hq_lhs, bind_map_left, map_bind]
            refine advDF_bind_congr (by cases chal <;> rfl) fun res => ?_
            rcases res with _ | c
            · dsimp only [Option.map]
              rw [Comp.eval, show (Expr.v0 : Expr AOps _ _).eval
                    (Env.cons (t := .opt (fig8CtT (ℓ := ℓ) (Pt := Pt))) none ρ7) = none from rfl]
              dsimp only [Comp.eval, dfSmRNoneE, Expr.eval, ρ7, ρ6, ρ5, ρ4, ρ3, ρ2, ρ1, ρ0, inp,
                trPairVal, dfHaltedEnc]
              simp only [_root_.ReductionDsl.Env.get_cons_zero,
                _root_.ReductionDsl.Env.get_cons_succ, map_pure]
              rfl
            · dsimp only [Option.map]
              let ρ8 := Env.cons (t := .opt (fig8CtT (ℓ := ℓ) (Pt := Pt)))
                (some (fig8CtV (ℓ := ℓ) (Pt := Pt) c)) ρ7
              let ρ9 := Env.cons (t := fig8CtT (ℓ := ℓ) (Pt := Pt))
                (fig8CtV (ℓ := ℓ) (Pt := Pt) c) ρ8
              rw [Comp.eval,
                  show (Expr.v0 : Expr AOps _ _).eval ρ8 =
                    some (fig8CtV (ℓ := ℓ) (Pt := Pt) c) from rfl]
              dsimp only
              rw [Comp.eval, eval_eLet, map_pure]
              let Γ9 : List (Ty (atomicSig ℓ Pt)) :=
                fig8CtT (ℓ := ℓ) (Pt := Pt) :: .opt (fig8CtT (ℓ := ℓ) (Pt := Pt)) :: Γ7
              let inp9E : Expr AOps Γ9 (dfSendHaltedInpT ℓ Pt) :=
                .var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))
              let s1_9E : Expr AOps Γ9 (simMirT ℓ Pt) :=
                .var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))
              let pn9E : Expr AOps Γ9 (U32 (ℓ := ℓ) (Pt := Pt)) :=
                .var (.succ (.succ (.succ (.succ .zero))))
              have hpost := dfPostSendStateE_eval_halted ℓ C K idA idB Dh encPt encT decT lam
                (.fst (.fst inp9E)) s1_9E (.fst (.snd inp9E)) (.fst (.snd (.snd inp9E)))
                (dfIsSomeE (.fst (.snd (.snd (.snd inp9E))))) (.fst .v2) pn9E .v0
                ρ9 sC ex s₁ Q m₀ chal.isSome pq' pn c
                rfl rfl rfl rfl (dfIsSomeE_eval _ ρ9) rfl rfl rfl
              rw [hpost]
              dsimp only [Expr.eval, Expr.v0, ρ9, ρ8, ρ7, ρ6, ρ5, ρ4, ρ3, trPairVal, dfHaltedEnc]
              simp only [_root_.ReductionDsl.Env.get_cons_zero,
                _root_.ReductionDsl.Env.get_cons_succ]
              rfl
        · simp only [↓reduceIte]
          dsimp only [Comp.eval, dfSmRNoneE, Expr.eval, Expr.v0, Expr.v3,
            ρ3, ρ2, ρ1, ρ0, inp, trPairVal, dfHaltedEnc]
          simp only [_root_.ReductionDsl.Env.get_cons_zero,
            _root_.ReductionDsl.Env.get_cons_succ, map_pure]
          rfl
      · simp only [↓reduceIte]
        dsimp only [Comp.eval, dfSmRNoneE, Expr.eval, Expr.v1, ρ1, ρ0, inp]
        simp only [_root_.ReductionDsl.Env.get_cons_zero,
          _root_.ReductionDsl.Env.get_cons_succ, map_pure]
        rfl
  · simp only [↓reduceIte]
    dsimp only [Comp.eval, dfSmRNoneE, Expr.eval, Expr.v0, ρ0, inp]
    rw [_root_.ReductionDsl.Env.get_cons_zero, map_pure]
    rfl

end SendStepEval

end

end Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeHaltedEval
