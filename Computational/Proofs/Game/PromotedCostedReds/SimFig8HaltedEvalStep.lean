/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.HiddenSaltBound -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8Halted -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.Fig8Atomic
import Computational.Proofs.ReductionDsl.SM.GameCosted
import Computational.Proofs.Game.PromotedCostedReds.SimFig8SanOracle
import Computational.Proofs.Game.PromotedCostedReds.SimFig8SanSem
import Computational.Proofs.Game.PromotedCostedReds.SimFig8SanCoupling
import Computational.Proofs.Game.PromotedCostedReds.SimFig8StepRecvNewSkip

/-!
# Forward-Encoder Step Simulation for `simFig8RedProgHalted`

Proves per-step forward-encoder simulation for `simFig8HaltedRawStepC` and full sanitized
evaluation equivalence `simFig8RedProgHalted_eval_san`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.SimFig8HaltedEvalStep

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Var Env Ops Iface Expr Comp CostedReduction
  handlerImpl isGameQuery atomicSig atomicSessionOps fig8SmIface
  coinOnlyIface e2eSessionCodec GhostStT smQT smRT smQenc smRdec smRrDec
  recvResultT recvResultEnc recvResultDec
  B U32 BV256 BV512 PlainT lpubT lpubV SMTag UniformSamplerTag AtomicPureOp
  partyToBool boolToParty fig8CtT fig8CtV fig8CtOfV
  fig8StT fig8StV fig8StOfV fsSendStV fsSendStOfV)
open Computational.Proofs.ReductionDsl.Fig8Atomic (salt32V_salt32OfV)
open CryptoGames (Party SMScheme FSAEADScheme)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.SM (Record GameState RecvResult initState noBobSendInEpoch0
  noAliceCorrWhileAliceBelowEpoch10 partyEnc partyDec posTy posEnc posDec
  orE isSomeE pGet orE_eval isSomeE_eval ite_eval)
open CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart LibsignalCiphertextWithSalt32
  lFig8 lFS ratchetKeyAdmissible)
open CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C Fig8Comp SimState SimCStateBounded
  SimCStateInv mkPub toWire semSendHook semSendHook_preserves_sC_inv kemTrackEnc)
open CryptoGames.Ratchet.LibsignalSimC (Kept LibsignalToModularSchemeSimState Hook
  idHook initSimC)
open CryptoGames.LibsignalSession (Params Crypto ShaCompress IdentityKey PublicKey GhostState)
open CryptoGames.LibsignalSM.Proofs.Refinement
  (KemFailTrackState initKemFailTrack stepKemFailSend stepKemFailDeliver)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.E2E (Bytes paramsV1)
open Computational.Proofs.Game.PromotedCostedReds.SanOracleCore
  (semRecvHookS semHandleHookDedupS semHandleHookDedupS_preserves_sC_inv)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8SanOracle
  (simFig8OracleSan)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8SanCoupling
  (SanSnapExtra sanSnapExtra_init sanSnapExtra_step)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedInit
  (kemTrackT kemTrackAtomicEnc kemTrackEnc_initKemFailTrack
   initSimCAtomicE_eval initKemTrackAtomicE_eval)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedSendCorrSub
  (trE_cand stepKemFailSendAtomicC stepKemFailSendAtomicC_eval)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedDeliverWitness
  (KemTrackDeliverInv kemTrackDeliverInv_init kemTrackDeliverInv_step
   kemTrackDeliverInv_stepSend findRevHonestIdxE findRevHonestIdxE_eval
   kemOnDeliverPostAtomicE kemOnDeliverPostAtomicE_eval)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8LoopAndCost
  (simMirT simMirEnc simMirDec simRecT simRecEnc simRecDec
   simBaseT simBaseEnc simBaseDec honestPairEnc honestPairDec
   ghostChainEnc ghostChainDec keptT keptEnc keptDec
   sentEntryEnc sentEntryDec snapEnc snapDec
   simFullT simFullEnc simFullDec simFullDec_simFullEnc
   simCStateInv_initSimC fig8IdSemHook)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8State
  (eLet eval_eLet sOpPure eval_sOpPure mWin mEpoch mIdx mSafeChE mSafeChE_eval
   mEpMgmtE mEpMgmtE_eval mNoBobEpoch0E mNoBobEpoch0E_eval
   ssMir ssPn ssStopped ssHonest scBase)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8Crypto
  (mkPubAtomicC mkPubAtomicC_eval)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8StepSend
  (simSendQueryC simSendQueryC_eval scPostSendAtomicE scPostSendAtomicE_eval unpackSendQE)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8StepCorr
  (simFig8StepCorrC simFig8StepCorrC_run)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8StepRecvSame
  (simFig8FwdHookSpec simFig8RecvSameSpec semRecvSameBranch)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8StepRecvNewCost
  (recvOutT recvHookInpT callSub1C recvHookOfBranchesC)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8StepRecvNewSkip
  (callSub1C_eval)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8StepRecvNew
  (simFig8RecvNewSpec_of_fwd recvHookOfBranchesC_eval
   simFig8OracleSan_deliver_eq simFig8OracleSan_inject_eq)
open Computational.Proofs.Game.PromotedCostedReds.SessionProgCommon
  (eval_eq_simulateQ_of_enc isQueryBoundP_of_makesAtMostQueries)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8Halted
  (simSendCTrackHalted semSendHookHalted simFig8OracleSanHalted simFig8ClampSanHalted
   simHaltedT simFig8HaltedInitC simFig8HaltedFinishC
   callSub2C liftCoinToFig8C stepKemFailSendFig8C
   haltedSendInpT simFig8HaltedSendHookC simFig8HaltedStepSendC
   extractHaltedRecvOptE isHaltedSendOrChallE simHaltedStepDispatchC
   simFig8HaltedRawStepC simFig8RedProgHaltedReal simFig8RedProgHalted)

noncomputable section

section EvalHelpers

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

/-- Encodes `(sC, tr)` into `(simHaltedT ℓ Pt).denote`. -/
@[expose] def simHaltedEnc {F : ShaCompress}
    (st : LibsignalToModularSchemeSimState Bytes Pt ℓ × KemFailTrackState F) :
    (simHaltedT ℓ Pt).denote :=
  (simFullEnc st.1, kemTrackAtomicEnc (kemTrackEnc st.2))

theorem semSendHookHalted_eq {PQ Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt) (qep : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (tr : KemFailTrackState P.C.F)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option (BitVec 512)) :
    semSendHookHalted P K Dh encPt encT lam qep (sC, tr) Q m₀ chal r =
      let fig := lFig8 Dh encPt P.C P.codec ℓ encT
        (fun R => if R == Party.A then P.idA else P.idB) 25000 lam
      if sC.base.stopped || sC.base.mir.win || !(noBobSendInEpoch0 sC.base.mir Q) then
        pure (none, (sC, tr))
      else
        match sC.base.mir.epMgmt 3 qep Q r.isSome with
        | none => pure (none, (sC, tr))
        | some s₁ =>
          if chal.isSome && !(s₁.safeCh 3 Q) then pure (none, (sC, tr))
          else (do
            let rq ← (match r with
              | some rq => pure rq
              | none => (liftM ($ᵗ BitVec 512 : ProbComp (BitVec 512)) : Fig8Comp Pt ℓ (BitVec 512)))
            let tr' := stepKemFailSend P.C.F K tr Q rq
            if tr'.cand.isSome then pure (none, (sC, { tr with cand := tr'.cand }))
            else
              let pn := if s₁.epoch Q ≠ sC.base.mir.epoch Q then
                BitVec.ofNat 32 (sC.base.mir.idx Q - 1) else sC.base.pn Q
              let rc : Option (BitVec 256) ← (match r with
                | some _ =>
                  some <$> (liftM ($ᵗ BitVec 256 : ProbComp (BitVec 256)) : Fig8Comp Pt ℓ (BitVec 256))
                | none => pure none)
              match mkPub (P := P) sC.base Q rq pn with
              | none => pure (none, (sC, { tr with cand := tr'.cand }))
              | some (pq', pub) => do
                let res ← (match chal with
                  | none => CryptoGames.SM.transmitQuery (St := Fig8St Pt) Q (pub, m₀) rc
                  | some m₁ => CryptoGames.SM.challQuery (St := Fig8St Pt) Q (pub, m₀) (pub, m₁) rc)
                match res with
                | none => pure (none, (sC, { tr with cand := tr'.cand }))
                | some c =>
                  let w := toWire c
                  let rec' : Record (Plain ℓ) (List (BitVec 8)) := ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, m₀, w⟩
                  let base' : SimState PQ Pt ℓ := { sC.base with
                    mir := s₁.record 3 Q () rec' chal.isSome, pq := Function.update sC.base.pq Q pq',
                    pn := Function.update sC.base.pn Q pn, honest := (w, c) :: sC.base.honest }
                  let sent' := (match (sC.kept Q).full, base'.honest.head? with
                    | some st, some (_, c₀) => if st.id.sendsIn (st.tcur + 1) then sC.sent
                      else match st.vS with | some v => (c₀, v) :: sC.sent | none => sC.sent
                    | _, _ => sC.sent)
                  pure (some w,
                    ({ sC with base := base',
                               kept := Function.update sC.kept Q (Kept.send (fig := fig) (sC.kept Q)),
                               sent := sent' }, tr'))) := by
  unfold semSendHookHalted simSendCTrackHalted idHook
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases h1 : (sC.base.stopped || sC.base.mir.win || !(noBobSendInEpoch0 sC.base.mir Q)) = true
  · simp [h1, StateT.run_pure]
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    rcases sC.base.mir.epMgmt 3 qep Q r.isSome with _ | s₁
    · simp [StateT.run_pure]
    · by_cases h2 : (chal.isSome && !(s₁.safeCh 3 Q)) = true
      · simp [h2, StateT.run_pure]
      · simp only [h2, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift,
          bind_assoc, pure_bind]
        refine bind_congr fun rq => ?_
        by_cases h3 : (stepKemFailSend P.C.F K tr Q rq).cand.isSome = true
        · simp [h3, StateT.run_map, StateT.run_set]
        · simp only [h3, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift,
            bind_assoc, pure_bind]
          refine bind_congr fun rc => ?_
          rcases mkPub (P := P) sC.base Q rq
              (if s₁.epoch Q ≠ sC.base.mir.epoch Q then
                BitVec.ofNat 32 (sC.base.mir.idx Q - 1) else sC.base.pn Q) with _ | ⟨pq', pub⟩
          · simp [StateT.run_map, StateT.run_set]
          · simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
            refine bind_congr fun res => ?_
            rcases res with _ | c
            · simp [StateT.run_map, StateT.run_set]
            · simp [StateT.run_map, StateT.run_set]; rfl

private theorem partyToBool_eq_partyEnc (Q : Party) : partyToBool Q = partyEnc Q := by
  cases Q <;> rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem trE_cand_isSome {F : ShaCompress} (tr : KemFailTrackState F) :
    ((kemTrackAtomicEnc (ℓ := ℓ) (Pt := Pt) (kemTrackEnc tr)).2.2.2.2.2).isSome =
      tr.cand.isSome := by
  unfold kemTrackAtomicEnc kemTrackEnc
  cases tr.cand <;> rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem fig8CtV_fig8CtOfV (v : (fig8CtT (ℓ := ℓ) (Pt := Pt)).denote) :
    fig8CtV (ℓ := ℓ) (Pt := Pt) (fig8CtOfV v) = v := by
  rcases v with ⟨h, n, ws, sv⟩
  simp [fig8CtV, fig8CtOfV, _root_.ReductionDsl.lctV, _root_.ReductionDsl.lctOfV,
    _root_.ReductionDsl.wireSaltCtV, _root_.ReductionDsl.wireSaltCtOfV, salt32V_salt32OfV]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem fig8StV_fig8StOfV (v : (fig8StT (ℓ := ℓ) (Pt := Pt)).denote) :
    fig8StV (ℓ := ℓ) (Pt := Pt) (fig8StOfV v) = v := by
  rcases v with ⟨p, rk, vs?, vrTbl, γv, cur?, tc⟩
  simp only [fig8StV, fig8StOfV]
  have hp : partyToBool (boolToParty p) = p := by cases p <;> rfl
  have hvs : (vs?.map (_root_.ReductionDsl.fsSendStOfV (ℓ := ℓ) (Pt := Pt))).map
      _root_.ReductionDsl.fsSendStV = vs? := by rcases vs? with _ | ⟨_, _⟩ <;> rfl
  have hvr : (fun t => ((vrTbl t).map (_root_.ReductionDsl.fsRecvStOfV (ℓ := ℓ) (Pt := Pt))).map
      _root_.ReductionDsl.fsRecvStV) = vrTbl := by
    funext t; rcases vrTbl t with _ | ⟨_, _, _⟩ <;> rfl
  have hγ : _root_.ReductionDsl.ckaStV (ℓ := ℓ) (Pt := Pt) (_root_.ReductionDsl.ckaStOfV γv) = γv := by
    rcases γv with _ | _ <;> rfl
  rw [hp, hvs, hvr, hγ]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem simMirEnc_simMirDec (v : (simMirT ℓ Pt).denote) :
    simMirEnc (Pt := Pt) (simMirDec v) = v := by
  rcases v with ⟨b, win, ⟨epA, epB⟩, ⟨idA, idB⟩, tL, trs, chall, comp, ⟨maA, maB⟩, leaks, corrs⟩
  simp only [simMirEnc, simMirDec, List.map_map]
  have htr : (simRecEnc (Pt := Pt) ∘ simRecDec :
      (simRecT ℓ Pt).denote → (simRecT ℓ Pt).denote) = id := by
    funext ⟨⟨p, _, _⟩, _, _⟩; cases p <;> rfl
  have hpos : (posEnc ∘ posDec : (posTy (S' := atomicSig ℓ Pt)).denote → _) = id := by
    funext ⟨p, _, _⟩; cases p <;> rfl
  have hcor : ((fun pe : Party × ℕ => (partyEnc pe.1, pe.2)) ∘
      (fun pe : Bool × ℕ => (partyDec pe.1, pe.2))) = id := by
    funext ⟨p, _⟩; cases p <;> rfl
  simp only [htr, hpos, hcor, List.map_id]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem simBaseEnc_simBaseDec (v : (simBaseT ℓ Pt).denote) :
    simBaseEnc (simBaseDec v) = v := by
  rcases v with ⟨mir, ⟨pqA, pqB⟩, ⟨pnA, pnB⟩, unackA, honest, ⟨chA, chB⟩, amb, stopped⟩
  simp only [simBaseEnc, simBaseDec, simMirEnc_simMirDec, List.map_map]
  have hhon : (honestPairEnc (ℓ := ℓ) (Pt := Pt) ∘ honestPairDec) = id := by
    funext ⟨w, cv⟩; simp [honestPairEnc, honestPairDec, fig8CtV_fig8CtOfV]
  have hgc : (ghostChainEnc (ℓ := ℓ) (Pt := Pt) ∘ ghostChainDec) = id := by
    funext ⟨_, _, _, _⟩; rfl
  simp only [hhon, hgc, List.map_id]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem keptEnc_keptDec (v : (keptT ℓ Pt).denote) :
    keptEnc (ℓ := ℓ) (Pt := Pt) (keptDec v) = v := by
  rcases v with ⟨full?, rsTbl⟩
  simp only [keptEnc, keptDec]
  congr 1
  · rcases full? with _ | stv
    · rfl
    · exact congrArg some (fig8StV_fig8StOfV stv)
  · funext t; rcases rsTbl t with _ | ⟨_, _, _⟩ <;> rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem simFullEnc_simFullDec (v : (simFullT ℓ Pt).denote) :
    simFullEnc (simFullDec v) = v := by
  rcases v with ⟨base, ⟨kA, kB⟩, sent, snaps⟩
  simp only [simFullEnc, simFullDec, simBaseEnc_simBaseDec, keptEnc_keptDec, List.map_map]
  have hse : (sentEntryEnc (ℓ := ℓ) (Pt := Pt) ∘ sentEntryDec) = id := by
    funext ⟨cv, ⟨_, _⟩⟩
    simp [sentEntryEnc, sentEntryDec, fig8CtV_fig8CtOfV, fsSendStV, fsSendStOfV]
  have hsn : (snapEnc (ℓ := ℓ) (Pt := Pt) ∘ snapDec) = id := by
    funext ⟨p, _, _⟩; cases p <;> rfl
  simp only [hse, hsn, List.map_id]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem recvResultDec_eq_smRrDec_id (v : (recvResultT (ℓ := ℓ) (Pt := Pt)).denote) :
    recvResultDec v = smRrDec id v := by rcases v with ⟨⟩ | ⟨_, _, _ | _⟩ <;> rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem recvResultEnc_recvResultDec_local (v : (recvResultT (ℓ := ℓ) (Pt := Pt)).denote) :
    recvResultEnc (ℓ := ℓ) (Pt := Pt) (recvResultDec (ℓ := ℓ) (Pt := Pt) v) = v := by
  rcases v with ⟨⟩ | ⟨_, _, _ | _⟩ <;> rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem recvResultDec_recvResultEnc_local (r : RecvResult (Plain ℓ)) :
    recvResultDec (ℓ := ℓ) (Pt := Pt) (recvResultEnc (ℓ := ℓ) (Pt := Pt) r) = r := by
  rcases r with _ | ⟨_, _, _ | _⟩ <;> rfl

private def simRecvOutEnc
    (p : Option (RecvResult (Plain ℓ)) × LibsignalToModularSchemeSimState Bytes Pt ℓ) :
    (recvOutT ℓ Pt).denote :=
  (p.1.map (recvResultEnc (ℓ := ℓ) (Pt := Pt)), simFullEnc p.2)

private def simRecvOutDec (v : (recvOutT ℓ Pt).denote) :
    Option (RecvResult (Plain ℓ)) × LibsignalToModularSchemeSimState Bytes Pt ℓ :=
  (v.1.map recvResultDec, simFullDec v.2)

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem simRecvOutEnc_simRecvOutDec (v : (recvOutT ℓ Pt).denote) :
    simRecvOutEnc (simRecvOutDec v) = v := by
  rcases v with ⟨_ | r, st⟩
  · exact Prod.ext rfl (simFullEnc_simFullDec st)
  · exact Prod.ext (congrArg some (recvResultEnc_recvResultDec_local r)) (simFullEnc_simFullDec st)

omit [DecidableEq Pt] [Zero Pt] in
private theorem coinOnlyIface_liftP_eq_self {α : Type} (p : ProbComp α) :
    (coinOnlyIface ℓ Pt).liftP p = p := by
  induction p using OracleComp.inductionOn with
  | pure a => simp [Iface.liftP]
  | query_bind n mx ih =>
    dsimp only [Iface.liftP, coinOnlyIface] at ih ⊢
    rw [simulateQ_bind, simulateQ_query]; exact bind_congr ih

omit [DecidableEq Pt] [Zero Pt] in
private theorem fig8SmIface_liftP_eq_liftM {α : Type} (p : ProbComp α) :
    (fig8SmIface ℓ Pt).liftP p = (liftM p : Fig8Comp Pt ℓ α) := by
  induction p using OracleComp.inductionOn with
  | pure a => simp [Iface.liftP]
  | query_bind n mx ih =>
    dsimp only [Iface.liftP, fig8SmIface] at ih ⊢
    rw [simulateQ_bind, simulateQ_query]; exact bind_congr ih

private theorem callSub2C_eval {S : Sig} {O' : Ops S} {ι : Type} {T : OracleSpec ι}
    {I' : Iface S T} {Γ : List (Ty S)} {A B_ty R : Ty S}
    (c : Comp O' I' [A, B_ty] R) (aE : Expr O' Γ A) (bE : Expr O' Γ B_ty) (ρ : Env Γ) :
    (callSub2C c aE bE).eval ρ = c.eval (.cons (aE.eval ρ) (.cons (bE.eval ρ) .nil)) := by
  dsimp only [callSub2C, Comp.eval, Expr.eval]
  rw [pure_bind, pure_bind]
  have ha : (Expr.renameM (fun ⦃_⦄ v => .succ v) aE).eval (.cons (bE.eval ρ) ρ) = aE.eval ρ :=
    Expr.renameM_eval aE fun ⦃_⦄ _ => rfl
  rw [ha, Comp.wkTop2_eval]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem iterM_liftM {α : Type} (f : α → ProbComp α) (n : ℕ) (a : α) :
    _root_.ReductionDsl.iterM (fun x => (liftM (f x) : Fig8Comp Pt ℓ α)) n a =
      liftM (_root_.ReductionDsl.iterM f n a) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => dsimp only [_root_.ReductionDsl.iterM]; rw [liftM_bind]; exact bind_congr ih

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem findML_liftM {α : Type} (p : α → ProbComp Bool) (xs : List α) :
    _root_.ReductionDsl.findML (fun x => (liftM (p x) : Fig8Comp Pt ℓ Bool)) xs =
      liftM (_root_.ReductionDsl.findML p xs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    dsimp only [_root_.ReductionDsl.findML]; rw [liftM_bind]
    refine bind_congr fun b => ?_
    cases b
    · exact ih
    · rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem anyML_liftM {α : Type} (p : α → ProbComp Bool) (xs : List α) :
    _root_.ReductionDsl.anyML (fun x => (liftM (p x) : Fig8Comp Pt ℓ Bool)) xs =
      liftM (_root_.ReductionDsl.anyML p xs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    dsimp only [_root_.ReductionDsl.anyML]; rw [liftM_bind]
    refine bind_congr fun b => ?_
    cases b
    · exact ih
    · rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem mapML_liftM {α β : Type} (f : α → ProbComp β) (xs : List α) :
    _root_.ReductionDsl.mapML (fun x => (liftM (f x) : Fig8Comp Pt ℓ β)) xs =
      liftM (_root_.ReductionDsl.mapML f xs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    dsimp only [_root_.ReductionDsl.mapML]; rw [liftM_bind]
    refine bind_congr fun _ => ?_; rw [ih, liftM_bind]; rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem consumeFirstML_liftM {α : Type} (p : α → ProbComp Bool) (mark : α → α)
    (xs : List α) :
    _root_.ReductionDsl.consumeFirstML (fun x => (liftM (p x) : Fig8Comp Pt ℓ Bool)) mark xs =
      liftM (_root_.ReductionDsl.consumeFirstML p mark xs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    dsimp only [_root_.ReductionDsl.consumeFirstML]; rw [liftM_bind]
    refine bind_congr fun b => ?_
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]; rw [ih, liftM_bind]; rfl
    · rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem foldML_liftM {α β : Type} (f : α → β → ProbComp β) (b : β) (xs : List α) :
    _root_.ReductionDsl.foldML (fun x acc => (liftM (f x acc) : Fig8Comp Pt ℓ β)) b xs =
      liftM (_root_.ReductionDsl.foldML f b xs) := by
  induction xs generalizing b with
  | nil => rfl
  | cons x xs ih => dsimp only [_root_.ReductionDsl.foldML]; rw [liftM_bind]; exact bind_congr ih

omit [DecidableEq Pt] [Zero Pt] in
private theorem liftCoinToFig8C_eval {O' : Ops (atomicSig ℓ Pt)}
    {Γ : List (Ty (atomicSig ℓ Pt))} {τ : Ty (atomicSig ℓ Pt)}
    (c : Comp O' (coinOnlyIface ℓ Pt) Γ τ) (ρ : Env Γ) :
    (liftCoinToFig8C c).eval ρ = (liftM (c.eval ρ) : Fig8Comp Pt ℓ τ.denote) := by
  induction c with
  | ret _ => rfl
  | bind c k ihc ihk =>
    dsimp only [liftCoinToFig8C, Comp.eval]; rw [ihc, liftM_bind]
    exact bind_congr fun x => ihk (.cons x _)
  | ite b _ _ iht ihf =>
    dsimp only [liftCoinToFig8C, Comp.eval]
    cases b.eval ρ
    · exact ihf ρ
    · exact iht ρ
  | caseOpt b _ _ ihn ihs =>
    dsimp only [liftCoinToFig8C, Comp.eval]
    cases b.eval ρ with | none => exact ihn ρ | some x => exact ihs (.cons x ρ)
  | caseSum b _ _ ihl ihr =>
    dsimp only [liftCoinToFig8C, Comp.eval]
    cases b.eval ρ with | inl x => exact ihl (.cons x ρ) | inr y => exact ihr (.cons y ρ)
  | sample _ _ =>
    dsimp only [liftCoinToFig8C, Comp.eval]
    rw [fig8SmIface_liftP_eq_liftM, coinOnlyIface_liftP_eq_self]
  | query g _ => nomatch g
  | iter _ _ body ih =>
    dsimp only [liftCoinToFig8C, Comp.eval]
    rw [show (fun a => (liftCoinToFig8C body).eval (.cons a ρ)) =
      (fun a => (liftM (body.eval (.cons a ρ)) : Fig8Comp Pt ℓ _)) from funext fun a => ih (.cons a ρ),
      iterM_liftM]
  | findM _ _ p ih =>
    dsimp only [liftCoinToFig8C, Comp.eval]
    rw [show (fun x => (liftCoinToFig8C p).eval (.cons x ρ)) =
      (fun x => (liftM (p.eval (.cons x ρ)) : Fig8Comp Pt ℓ Bool)) from funext fun x => ih (.cons x ρ),
      findML_liftM]
  | anyM _ _ p ih =>
    dsimp only [liftCoinToFig8C, Comp.eval]
    rw [show (fun x => (liftCoinToFig8C p).eval (.cons x ρ)) =
      (fun x => (liftM (p.eval (.cons x ρ)) : Fig8Comp Pt ℓ Bool)) from funext fun x => ih (.cons x ρ),
      anyML_liftM]
  | mapM _ _ f ih =>
    dsimp only [liftCoinToFig8C, Comp.eval]
    rw [show (fun x => (liftCoinToFig8C f).eval (.cons x ρ)) =
      (fun x => (liftM (f.eval (.cons x ρ)) : Fig8Comp Pt ℓ _)) from funext fun x => ih (.cons x ρ),
      mapML_liftM]
  | consumeFirstM _ _ p _ ih =>
    dsimp only [liftCoinToFig8C, Comp.eval]
    rw [show (fun x => (liftCoinToFig8C p).eval (.cons x ρ)) =
      (fun x => (liftM (p.eval (.cons x ρ)) : Fig8Comp Pt ℓ Bool)) from funext fun x => ih (.cons x ρ),
      consumeFirstML_liftM]
  | foldM _ _ _ f ih =>
    dsimp only [liftCoinToFig8C, Comp.eval]
    rw [show (fun x acc => (liftCoinToFig8C f).eval (.cons x (.cons acc ρ))) =
      (fun x acc => (liftM (f.eval (.cons x (.cons acc ρ))) : Fig8Comp Pt ℓ _)) from
        funext fun x => funext fun acc => ih (.cons x (.cons acc ρ)),
      foldML_liftM]

private theorem stepKemFailSendFig8C_eval {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt}
    {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    (q : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (trE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (kemTrackT ℓ Pt))
    (qBE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ .bool)
    (rqE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ BV512)
    (ρ : Env Γ) (tr : KemFailTrackState C.F) (Q : Party) (rq : BitVec 512)
    (htr : trE.eval ρ = kemTrackAtomicEnc (kemTrackEnc tr))
    (hqB : qBE.eval ρ = partyToBool Q) (hrq : rqE.eval ρ = rq)
    (hBOk : CryptoVerification.SpqrV1Sync.SendTotal.BOkTight (tr.st Q))
    (hSentLen : tr.sentB.length ≤ q) :
    (stepKemFailSendFig8C (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) q trE qBE rqE).eval ρ =
      let tr' := stepKemFailSend C.F K tr Q rq
      pure (kemTrackAtomicEnc (kemTrackEnc tr'),
            kemTrackAtomicEnc (kemTrackEnc { tr with cand := tr'.cand })) := by
  dsimp only [stepKemFailSendFig8C]
  rw [liftCoinToFig8C_eval,
      stepKemFailSendAtomicC_eval q trE qBE rqE ρ tr Q rq htr hqB hrq hBOk hSentLen]
  rfl

private theorem simFig8HaltedSendHookC_eval {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt}
    {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    (idA idB : IdentityKey) (qep q : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (stE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (simHaltedT ℓ Pt))
    (qBE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ .bool)
    (m0E : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ PlainT)
    (chalE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (.opt PlainT))
    (rE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (.opt BV512))
    (ρ : Env Γ) (sC : LibsignalToModularSchemeSimState Bytes Pt ℓ) (tr : KemFailTrackState C.F)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option (BitVec 512))
    (hst : stE.eval ρ = simHaltedEnc (sC, tr)) (hq : qBE.eval ρ = partyEnc Q)
    (hm0 : m0E.eval ρ = m₀) (hch : chalE.eval ρ = chal) (hr : rE.eval ρ = r)
    (htight : CryptoVerification.SpqrV1Sync.SendTotal.TopStateTight C.F K (sC.base.pq Q))
    (hBOk : CryptoVerification.SpqrV1Sync.SendTotal.BOkTight (tr.st Q))
    (hSentLen : tr.sentB.length ≤ q) :
    (simFig8HaltedSendHookC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB qep q stE qBE m0E chalE rE).eval ρ =
      Prod.map id simHaltedEnc <$>
        semSendHookHalted (paramsV1 C K idA idB) K Dh encPt encT lam qep (sC, tr) Q m₀ chal r := by
  let AOps := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam
  erw [semSendHookHalted_eq]
  dsimp only [simFig8HaltedSendHookC, Comp.eval]
  let inp : (haltedSendInpT ℓ Pt).denote := (simHaltedEnc (sC, tr), (partyEnc Q, (m₀, (chal, r))))
  have hinp : (Expr.pair stE (.pair qBE (.pair m0E (.pair chalE rE)))).eval ρ = inp := by
    simp [inp, Expr.eval, hst, hq, hm0, hch, hr]
  rw [hinp, pure_bind]
  let ρ1 := Env.cons (t := haltedSendInpT ℓ Pt) inp ρ
  have hg1 : (orE (orE (ssStopped (scBase (.fst (.fst .v0))))
        (mWin (ssMir (scBase (.fst (.fst .v0))))))
      (.not (mNoBobEpoch0E (ssMir (scBase (.fst (.fst .v0)))) (.fst (.snd .v0)))) :
      Expr AOps _ .bool).eval ρ1 =
      (sC.base.stopped || sC.base.mir.win || !(noBobSendInEpoch0 sC.base.mir Q)) := by
    have hs1 : (ssStopped (scBase (.fst (.fst .v0))) : Expr AOps _ .bool).eval ρ1 =
        sC.base.stopped := rfl
    have hw1 : (mWin (ssMir (scBase (.fst (.fst .v0)))) : Expr AOps _ .bool).eval ρ1 =
        sC.base.mir.win := rfl
    have hnb : (mNoBobEpoch0E (ssMir (scBase (.fst (.fst .v0)))) (.fst (.snd .v0)) :
        Expr AOps _ .bool).eval ρ1 = noBobSendInEpoch0 sC.base.mir Q :=
      mNoBobEpoch0E_eval _ _ ρ1 sC.base.mir Q rfl rfl
    rw [orE_eval, orE_eval, hs1, hw1]; dsimp only [Expr.eval]; rw [hnb]
  rw [hg1]
  cases hstop : (sC.base.stopped || sC.base.mir.win || !(noBobSendInEpoch0 sC.base.mir Q))
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hep : (mEpMgmtE qep (ssMir (scBase (.fst (.fst .v0)))) (.fst (.snd .v0))
        (isSomeE (.snd (.snd (.snd (.snd .v0))))) :
        Expr AOps _ (.opt (simMirT ℓ Pt))).eval ρ1 =
        (sC.base.mir.epMgmt 3 qep Q r.isSome).map (simMirEnc (Pt := Pt)) := by
      rw [mEpMgmtE_eval qep _ _ _ ρ1 sC.base.mir Q rfl rfl, isSomeE_eval]; rfl
    rw [hep]
    rcases hep_res : sC.base.mir.epMgmt 3 qep Q r.isSome with _ | s₁
    · simp only [map_pure]; rfl
    · dsimp only [Option.map]
      let ρ2 := Env.cons (t := simMirT ℓ Pt) (simMirEnc (Pt := Pt) s₁) ρ1
      have hg2 : (Expr.and (isSomeE (.fst (.snd (.snd (.snd .v1)))))
          (.not (mSafeChE .v0 (.fst (.snd .v1)))) : Expr AOps _ .bool).eval ρ2 =
          (chal.isSome && !(s₁.safeCh 3 Q)) := by
        have his : (isSomeE (.fst (.snd (.snd (.snd .v1)))) : Expr AOps _ .bool).eval ρ2 =
            chal.isSome := isSomeE_eval _ ρ2
        have hsf : (mSafeChE .v0 (.fst (.snd .v1)) : Expr AOps _ .bool).eval ρ2 =
            s₁.safeCh 3 Q := mSafeChE_eval _ _ ρ2 s₁ Q rfl rfl
        dsimp only [Expr.eval]; rw [his, hsf]
      rw [hg2]
      cases hsf_guard : (chal.isSome && !(s₁.safeCh 3 Q))
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have hrq : (Comp.caseOpt (.snd (.snd (.snd (.snd .v1))))
            (Comp.sample (I := fig8SmIface ℓ Pt) (UniformSamplerTag.base .bv512) .unit)
            (.ret .v0) : Comp AOps (fig8SmIface ℓ Pt) _ BV512).eval ρ2 =
            (match r with
             | some rq => pure rq
             | none => (liftM ($ᵗ BitVec 512 : ProbComp (BitVec 512)) : Fig8Comp Pt ℓ (BitVec 512))) := by
          cases r with
          | none => dsimp only [ρ2, ρ1, inp, Comp.eval, Expr.eval]; rw [fig8SmIface_liftP_eq_liftM]; rfl
          | some _ => rfl
        dsimp only [Comp.eval, ρ2, ρ1] at hrq
        erw [hrq]; clear hrq; simp only [map_bind]
        refine OracleComp.bind_congr' (by cases r <;> rfl) fun rq => ?_
        let ρ3 := Env.cons (t := BV512) rq ρ2
        have htr_step := stepKemFailSendFig8C_eval (C := C) (K := K) (Dh := Dh)
          (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
          q (.snd (.fst .v2)) (.fst (.snd .v2)) .v0 ρ3 tr Q rq
          rfl (partyToBool_eq_partyEnc Q).symm rfl hBOk hSentLen
        erw [htr_step]; rw [pure_bind]
        let tr' := stepKemFailSend C.F K tr Q rq
        let trPair : (Ty.prod (kemTrackT ℓ Pt) (kemTrackT ℓ Pt)).denote :=
          (kemTrackAtomicEnc (kemTrackEnc tr'),
           kemTrackAtomicEnc (kemTrackEnc { tr with cand := tr'.cand }))
        let ρ4 := Env.cons (t := .prod (kemTrackT ℓ Pt) (kemTrackT ℓ Pt)) trPair ρ3
        have hcand : (isSomeE (trE_cand (.fst .v0)) : Expr AOps _ .bool).eval ρ4 =
            tr'.cand.isSome := by rw [isSomeE_eval]; exact trE_cand_isSome tr'
        erw [hcand]
        cases hcand_b : tr'.cand.isSome
        · erw [hcand_b]; simp only [Bool.false_eq_true, ↓reduceIte]
          have hrc : (Comp.caseOpt (.snd (.snd (.snd (.snd .v3))))
              (.ret .none)
              (.bind (Comp.sample (I := fig8SmIface ℓ Pt) (UniformSamplerTag.base .bv256) .unit)
                (.ret (.some .v0))) : Comp AOps (fig8SmIface ℓ Pt) _ (.opt BV256)).eval ρ4 =
              (match r with
               | some _ => some <$> (liftM ($ᵗ BitVec 256 : ProbComp (BitVec 256)) :
                   Fig8Comp Pt ℓ (BitVec 256))
               | none => pure none) := by
            cases r with
            | none => rfl
            | some _ =>
              dsimp only [ρ4, ρ3, ρ2, ρ1, inp, Comp.eval, Expr.eval]
              rw [fig8SmIface_liftP_eq_liftM, map_eq_bind_pure_comp]; rfl
          dsimp only [Comp.eval, ρ4, ρ3, ρ2, ρ1] at hrc
          erw [hrc]; clear hrc; simp only [map_bind]
          refine OracleComp.bind_congr' (by cases r <;> rfl) fun rc => ?_
          let ρ5 := Env.cons (t := .opt BV256) rc ρ4
          let pn := if s₁.epoch Q ≠ sC.base.mir.epoch Q then
            BitVec.ofNat 32 (sC.base.mir.idx Q - 1) else sC.base.pn Q
          let Γ5 := Ty.opt BV256 :: .prod (kemTrackT ℓ Pt) (kemTrackT ℓ Pt) :: BV512 ::
            simMirT ℓ Pt :: haltedSendInpT ℓ Pt :: Γ
          let v4 : Expr AOps Γ5 (haltedSendInpT ℓ Pt) :=
            .var (.succ (.succ (.succ (.succ .zero))))
          have hpn : (Expr.ite (.not (.eqN (pGet (mEpoch .v3) (.fst (.snd v4)))
                (pGet (mEpoch (ssMir (scBase (.fst (.fst v4))))) (.fst (.snd v4)))))
              (sOpPure .u32OfNat (.sub (pGet (mIdx (ssMir (scBase (.fst (.fst v4)))))
                (.fst (.snd v4))) (.nat 1)))
              (pGet (ssPn (scBase (.fst (.fst v4)))) (.fst (.snd v4))) :
              Expr AOps Γ5 U32).eval ρ5 = pn := by
            have hep1 : (pGet (mEpoch .v3) (.fst (.snd v4)) : Expr AOps Γ5 .nat).eval ρ5 =
                s₁.epoch Q := by cases Q <;> rfl
            have hep0 : (pGet (mEpoch (ssMir (scBase (.fst (.fst v4))))) (.fst (.snd v4)) :
                Expr AOps Γ5 .nat).eval ρ5 = sC.base.mir.epoch Q := by cases Q <;> rfl
            have hidx0 : (pGet (mIdx (ssMir (scBase (.fst (.fst v4))))) (.fst (.snd v4)) :
                Expr AOps Γ5 .nat).eval ρ5 = sC.base.mir.idx Q := by cases Q <;> rfl
            have hpn0 : (pGet (ssPn (scBase (.fst (.fst v4)))) (.fst (.snd v4)) :
                Expr AOps Γ5 U32).eval ρ5 = sC.base.pn Q := by cases Q <;> rfl
            dsimp only [pn]; rw [ite_eval]
            simp only [Expr.eval, eval_sOpPure, AtomicPureOp.eval, hep1, hep0, hidx0, hpn0]
            by_cases heq : s₁.epoch Q = sC.base.mir.epoch Q <;> simp [heq]
          erw [hpn]; rw [pure_bind]
          let Γ6 := U32 :: Γ5
          let ρ6 := Env.cons (t := U32) pn ρ5
          have hpQ_dec : partyDec (partyEnc Q) = Q := by cases Q <;> rfl
          let v5 : Expr AOps Γ6 (haltedSendInpT ℓ Pt) :=
            .var (.succ (.succ (.succ (.succ (.succ .zero)))))
          have hmk : (mkPubAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
              (decT := decT) (lam := lam) (fig8SmIface ℓ Pt) idA idB
              (scBase (.fst (.fst v5))) (.fst (.snd v5)) .v3 .v0).eval ρ6 =
              pure ((mkPub (P := paramsV1 C K idA idB) sC.base Q rq pn).map
                fun (pq', pub) => (pq', lpubV (ℓ := ℓ) (Pt := Pt) pub)) := by
            rw [mkPubAtomicC_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
              (decT := decT) (lam := lam) (fig8SmIface ℓ Pt) idA idB _ _ _ _ ρ6
              sC.base (partyEnc Q) rq pn rfl rfl rfl rfl (hpQ_dec.symm ▸ htight), hpQ_dec]
          erw [hmk]; rw [pure_bind]
          let mkOpt := (mkPub (P := paramsV1 C K idA idB) sC.base Q rq pn).map
            fun (pq', pub) => (pq', lpubV (ℓ := ℓ) (Pt := Pt) pub)
          let Γ7 := Ty.opt (.prod (B 32) (lpubT (ℓ := ℓ) (Pt := Pt))) :: Γ6
          let ρ7 := Env.cons (t := .opt (.prod (B 32) (lpubT (ℓ := ℓ) (Pt := Pt)))) mkOpt ρ6
          have hv0_mk : (Expr.v0 : Expr AOps Γ7 _).eval ρ7 = mkOpt := rfl
          erw [hv0_mk]
          rcases hmk_res : mkPub (P := paramsV1 C K idA idB) sC.base Q rq pn with _ | ⟨pq', pub⟩
          · dsimp only [mkOpt]; rw [hmk_res]; simp only [map_pure]; rfl
          · dsimp only [mkOpt]; rw [hmk_res]; dsimp only [Option.map]
            let ρ7' := Env.cons (t := .opt (.prod (B 32) (lpubT (ℓ := ℓ) (Pt := Pt))))
              (some (pq', lpubV (ℓ := ℓ) (Pt := Pt) pub)) ρ6
            let Γ8 := Ty.prod (B 32) (lpubT (ℓ := ℓ) (Pt := Pt)) :: Γ7
            let ρ8 := Env.cons (t := .prod (B 32) (lpubT (ℓ := ℓ) (Pt := Pt)))
              (pq', lpubV (ℓ := ℓ) (Pt := Pt) pub) ρ7'
            let v7 : Expr AOps Γ8 (haltedSendInpT ℓ Pt) :=
              .var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))
            have hsq := simSendQueryC_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt)
              (encT := encT) (decT := decT) (lam := lam) (Γ := Γ8)
              (.fst (.snd v7)) (.snd .v0) (.fst (.snd (.snd v7)))
              (.fst (.snd (.snd (.snd v7)))) .v3 ρ8 Q pub m₀ chal rc rfl rfl rfl rfl rfl
            have hq_unif :
                ((fun p : Option (Fig8C Pt) × Unit => p.1.map (fig8CtV (ℓ := ℓ) (Pt := Pt))) <$>
                  (match chal with
                    | none => (fig8IdSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ) none).onTr
                        Q (pub, m₀) rc ()
                    | some m₁ => (fig8IdSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ) none).onCh
                        Q (pub, m₀) (pub, m₁) rc ())) =
                Option.map (fig8CtV (ℓ := ℓ) (Pt := Pt)) <$> (match chal with
                  | none => CryptoGames.SM.transmitQuery (St := Fig8St Pt) Q (pub, m₀) rc
                  | some m₁ => CryptoGames.SM.challQuery (St := Fig8St Pt) Q (pub, m₀) (pub, m₁) rc) := by
              cases chal <;> simp [fig8IdSemHook, map_eq_bind_pure_comp]
            erw [hsq, hq_unif]; simp only [bind_map_left, map_bind]
            refine OracleComp.bind_congr' (by cases chal <;> rfl) fun res => ?_
            let Γ9 := Ty.opt (fig8CtT (ℓ := ℓ) (Pt := Pt)) :: Γ8
            have hv0_ct : (Expr.v0 : Expr AOps Γ9 _).eval
                (Env.cons (t := .opt (fig8CtT (ℓ := ℓ) (Pt := Pt)))
                  (res.map (fig8CtV (ℓ := ℓ) (Pt := Pt))) ρ8) =
                res.map (fig8CtV (ℓ := ℓ) (Pt := Pt)) := rfl
            erw [hv0_ct]
            rcases res with _ | c
            · dsimp only [Option.map]; simp only [map_pure]; rfl
            · dsimp only [Option.map]
              let ρ9 := Env.cons (t := .opt (fig8CtT (ℓ := ℓ) (Pt := Pt))) (some (fig8CtV c)) ρ8
              let Γ10 := fig8CtT (ℓ := ℓ) (Pt := Pt) :: Γ9
              let ρ10 := Env.cons (t := fig8CtT (ℓ := ℓ) (Pt := Pt)) (fig8CtV c) ρ9
              let v4_pn : Expr AOps Γ10 U32 := .var (.succ (.succ (.succ (.succ .zero))))
              let v8_s1 : Expr AOps Γ10 (simMirT ℓ Pt) :=
                .var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))
              let v9 : Expr AOps Γ10 (haltedSendInpT ℓ Pt) :=
                .var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))
              have hpost := scPostSendAtomicE_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                (encT := encT) (decT := decT) (lam := lam) idA idB
                (.fst (.fst v9)) v8_s1 (.fst (.snd v9)) (.fst (.snd (.snd v9)))
                (isSomeE (.fst (.snd (.snd (.snd v9))))) (.fst .v2) v4_pn .v0 ρ10
                sC s₁ Q m₀ chal.isSome pq' pn c rfl rfl rfl rfl
                (isSomeE_eval _ ρ10) rfl rfl rfl
              erw [eval_eLet, hpost]; simp only [map_pure]
              unfold CryptoGames.Ratchet.LibsignalSim.scPostSendPure
              cases (sC.kept Q).full <;> rfl
        · erw [hcand_b]; simp only [↓reduceIte, map_pure]; rfl
      · simp only [↓reduceIte, map_pure]; rfl
  · simp only [↓reduceIte, map_pure]; rfl

private theorem simFig8HaltedFinishC_eval (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (s_raw : (simHaltedT ℓ Pt).denote) (b : Bool) :
    (simFig8HaltedFinishC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam).eval
        (.cons s_raw (.cons b .nil)) = pure b :=
  rfl

private theorem simFig8HaltedInitC_eval (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) :
    (simFig8HaltedInitC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam).eval (.cons () .nil) =
      Prod.map id (simHaltedEnc (ℓ := ℓ) (Pt := Pt)) <$>
        (do
          let pqrKey ← (liftM ($ᵗ BitVec 256 : ProbComp (BitVec 256)) : Fig8Comp Pt ℓ (BitVec 256))
          return ((),
            (initSimC ((paramsV1 C K idA idB).spqr.init .a2b pqrKey)
              ((paramsV1 C K idA idB).spqr.init .b2a pqrKey),
             initKemFailTrack C.F pqrKey))) := by
  dsimp only [simFig8HaltedInitC, Comp.eval]
  rw [fig8SmIface_liftP_eq_liftM, map_bind]
  refine bind_congr fun pqrKey => ?_
  rw [map_pure]; dsimp only [Expr.eval, Prod.map, id_eq, simHaltedEnc]
  erw [initSimCAtomicE_eval, initKemTrackAtomicE_eval]
  rw [← kemTrackEnc_initKemFailTrack]; rfl

private def HaltedEvalInv (C : Crypto) (K : MlKem) (q m : ℕ)
    (st : LibsignalToModularSchemeSimState Bytes Pt ℓ × KemFailTrackState C.F) : Prop :=
  m ≤ q ∧ SimCStateInv q m st.1 ∧ SanSnapExtra C K st.1 ∧
    KemTrackDeliverInv C.F K (q - m) (kemTrackEnc st.2)

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem HaltedEvalInv.mono {C : Crypto} {K : MlKem} {q m n : ℕ}
    {st : LibsignalToModularSchemeSimState Bytes Pt ℓ × KemFailTrackState C.F}
    (hmn : m ≤ n) (h : HaltedEvalInv C K q n st) : HaltedEvalInv C K q m st :=
  ⟨hmn.trans h.1, h.2.1.mono hmn, h.2.2.1, h.2.2.2.mono (by omega)⟩

omit [SampleableType Pt] in
private theorem semSendHookHalted_mem_inv {C : Crypto} {K : MlKem} {idA idB : IdentityKey}
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes} {encT : Pt → PublicKey}
    {decT : PublicKey → Option Pt} {lam : Pt} {qep q m : ℕ}
    {sC : LibsignalToModularSchemeSimState Bytes Pt ℓ} {tr : KemFailTrackState C.F}
    (hInv : HaltedEvalInv C K q (m + 1) (sC, tr))
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option (BitVec 512)) :
    ∀ x ∈ support (semSendHookHalted (paramsV1 C K idA idB) K Dh encPt encT lam qep
        (sC, tr) Q m₀ chal r),
      HaltedEvalInv C K q m x.2 := by
  intro ⟨res, sC', tr_out⟩ hx
  let tr_out' : KemFailTrackState C.F := tr_out
  change HaltedEvalInv C K q m (sC', tr_out')
  rcases hInv with ⟨hm, hSim, hExtra, hTr⟩
  have hKeep : ∀ c, HaltedEvalInv C K q m (sC, { tr with cand := c }) := fun _ =>
    ⟨by omega, hSim.mono (by omega), hExtra,
     ⟨hTr.sentB_len.trans (by omega), hTr.bOk, hTr.sentB_deser⟩⟩
  have hClose : ∀ c, sC' = sC → tr_out = { tr with cand := c } →
      HaltedEvalInv C K q m (sC', tr_out') := by
    intro c hs ht; have ht' : tr_out' = { tr with cand := c } := ht; rw [hs, ht']; exact hKeep c
  erw [semSendHookHalted_eq] at hx
  by_cases hc1 : (sC.base.stopped || sC.base.mir.win || !(noBobSendInEpoch0 sC.base.mir Q)) = true
  · simp [hc1] at hx; exact hClose tr.cand (Prod.mk.inj hx.2).1 (Prod.mk.inj hx.2).2
  · simp only [hc1, Bool.false_eq_true, ↓reduceIte] at hx
    rcases hep : sC.base.mir.epMgmt 3 qep Q r.isSome with _ | s₁
    · simp [hep] at hx; exact hClose tr.cand (Prod.mk.inj hx.2).1 (Prod.mk.inj hx.2).2
    · rw [hep] at hx
      by_cases hc2 : (chal.isSome && !(s₁.safeCh 3 Q)) = true
      · simp [hc2] at hx; exact hClose tr.cand (Prod.mk.inj hx.2).1 (Prod.mk.inj hx.2).2
      · simp only [hc2, Bool.false_eq_true, ↓reduceIte, mem_support_bind_iff] at hx
        rcases hx with ⟨rq, hrq, hx⟩
        set tr' := stepKemFailSend (paramsV1 C K idA idB).C.F K tr Q rq
        by_cases hcand : tr'.cand.isSome = true
        · simp [hcand] at hx; exact hClose tr'.cand hx.2.1 hx.2.2
        · simp only [hcand, Bool.false_eq_true, ↓reduceIte, mem_support_bind_iff] at hx
          rcases hx with ⟨rc, hrc, hx⟩
          set pn : BitVec 32 := if s₁.epoch Q ≠ sC.base.mir.epoch Q
            then BitVec.ofNat 32 (sC.base.mir.idx Q - 1) else sC.base.pn Q
          rcases hmk : mkPub (P := paramsV1 C K idA idB) sC.base Q rq pn with _ | ⟨pq', pub⟩
          · simp [hmk] at hx; exact hClose tr'.cand hx.2.1 hx.2.2
          · rw [hmk] at hx; simp only [mem_support_bind_iff] at hx
            rcases hx with ⟨res_q, hres_q, hx⟩
            rcases res_q with _ | c
            · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
              exact hClose tr'.cand hx.2.1 hx.2.2
            · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
              rcases hx.2 with ⟨hsC, htr⟩
              have htr_eq : tr_out' = tr' := htr
              rw [htr_eq]
              have hTr' : KemTrackDeliverInv C.F K (q - m) (kemTrackEnc (tr' : KemFailTrackState C.F)) := by
                have h1 := kemTrackDeliverInv_stepSend C.F K (q - (m + 1)) tr Q rq hTr
                rwa [show q - (m + 1) + 1 = q - m by omega] at h1
              have hcoins : (rq, rc) ∈ support
                  (CryptoGames.Ratchet.LibsignalSim.semDrawSendCoins
                    (fig8IdSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ) none) r) := by
                cases r with
                | none =>
                  dsimp only at hrq
                  simp only [support_pure, Set.mem_singleton_iff] at hrc; subst hrc
                  dsimp only [CryptoGames.Ratchet.LibsignalSim.semDrawSendCoins, fig8IdSemHook]
                  generalize ($ᵗ BitVec 512 : ProbComp (BitVec 512)) = samp at hrq ⊢
                  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
                  exact ⟨rq, hrq, rfl⟩
                | some rq0 =>
                  simp only [support_pure, Set.mem_singleton_iff] at hrq; subst hrq
                  simp only [support_map, Set.mem_image] at hrc; rcases hrc with ⟨rc0, hrc0, rfl⟩
                  dsimp only [CryptoGames.Ratchet.LibsignalSim.semDrawSendCoins, fig8IdSemHook]
                  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
                  exact ⟨rc0, hrc0, rfl⟩
              have hmem_sem : (some (toWire c), (sC', ())) ∈ support
                  (semSendHook (paramsV1 C K idA idB) Dh encPt encT lam
                    (fig8IdSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ) none)
                    qep sC () Q m₀ chal r) := by
                rw [hsC]; unfold semSendHook
                simp only [hc1, Bool.false_eq_true, ↓reduceIte, hep, hc2, mem_support_bind_iff]
                refine ⟨(rq, rc), hcoins, ?_⟩
                dsimp only [fig8IdSemHook]
                simp only [support_pure, Set.mem_singleton_iff]
                refine ⟨((), ()), trivial, ?_⟩
                rw [show (if s₁.epoch Q ≠ sC.base.mir.epoch Q
                  then BitVec.ofNat 32 (sC.base.mir.idx Q - 1) else sC.base.pn Q) = pn from rfl, hmk]
                cases chal with
                | none =>
                  simp only [mem_support_bind_iff, CryptoGames.SM.transmitQuery] at hres_q ⊢
                  exact ⟨(some c, ()), ⟨some c, hres_q, rfl⟩, by
                    unfold CryptoGames.Ratchet.LibsignalSim.scPostSendPure
                    simp only [support_pure, Set.mem_singleton_iff]
                    cases (sC.kept Q).full <;> rfl⟩
                | some m₁ =>
                  simp only [mem_support_bind_iff, CryptoGames.SM.challQuery] at hres_q ⊢
                  exact ⟨(some c, ()), ⟨some c, hres_q, rfl⟩, by
                    unfold CryptoGames.Ratchet.LibsignalSim.scPostSendPure
                    simp only [support_pure, Set.mem_singleton_iff]
                    cases (sC.kept Q).full <;> rfl⟩
              have hSim' := semSendHook_preserves_sC_inv (P := paramsV1 C K idA idB)
                Dh encPt encT lam (fig8IdSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ) none)
                q m qep sC () Q m₀ chal r hSim _ hmem_sem
              have hExtra' : SanSnapExtra C K sC' := by
                cases chal with
                | none =>
                  refine sanSnapExtra_step C K idA idB Dh encPt encT decT lam qep
                    (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000) (25000 * q)
                    (.inl (.inl (.inl (.inl (Q, m₀, r))))) sC hExtra (some (toWire c), sC') ?_
                  simp only [simFig8OracleSan, StateT.run_mk, semHandleHookDedupS,
                    support_map, Set.mem_image]
                  exact ⟨(some (toWire c), (sC', ())), hmem_sem, rfl⟩
                | some m₁ =>
                  refine sanSnapExtra_step C K idA idB Dh encPt encT decT lam qep
                    (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000) (25000 * q)
                    (.inl (.inl (.inl (.inr (Q, m₀, m₁, r))))) sC hExtra (some (toWire c), sC') ?_
                  simp only [simFig8OracleSan, StateT.run_mk, semHandleHookDedupS,
                    support_map, Set.mem_image]
                  exact ⟨(some (toWire c), (sC', ())), hmem_sem, rfl⟩
              exact ⟨by omega, hSim', hExtra', hTr'⟩

private theorem simFig8HaltedRawStepC_step (hℓ : ℓ < 10 ^ 6)
    (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q m : ℕ)
    (t : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (st : LibsignalToModularSchemeSimState Bytes Pt ℓ × KemFailTrackState C.F)
    (hInv : HaltedEvalInv C K q (m + 1) st) :
    ((handlerImpl (C := e2eSessionCodec ℓ Pt)
        (simFig8HaltedRawStepC (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam qep q)
        (.inr t)).run (simHaltedEnc st)) =
      Prod.map id simHaltedEnc <$>
        ((simFig8OracleSanHalted (paramsV1 C K idA idB) K Dh encPt encT decT lam qep
          (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000) (25000 * q) (.inr t)).run st) ∧
    ∀ r ∈ support ((simFig8OracleSanHalted (paramsV1 C K idA idB) K Dh encPt encT decT lam qep
        (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000) (25000 * q) (.inr t)).run st),
      HaltedEvalInv C K q m r.2 := by
  rcases st with ⟨sC, tr⟩
  rcases hInv with ⟨hm, hSim, hExtra, hTr⟩
  have hBnd : SimCStateBounded q sC := hSim.toBounded
  have hTrQ : KemTrackDeliverInv C.F K q (kemTrackEnc tr) := hTr.mono (by omega)
  let fwdSpec := simFig8FwdHookSpec (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam qep q
  let sameSpec := simFig8RecvSameSpec (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam qep q
  let newSpec := simFig8RecvNewSpec_of_fwd C K Dh encPt encT decT lam
    idA idB qep q fwdSpec.comp fwdSpec.hq fwdSpec.hcost fwdSpec.hdesc fwdSpec.heval
  let cRecv := recvHookOfBranchesC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB q sameSpec.comp newSpec.comp
  have hrecv : ∀ (Q : Party) (w : Bytes) (isDel : Bool),
      cRecv.eval (.cons (simFullEnc sC, (partyToBool Q, (w, isDel))) .nil) =
        simRecvOutEnc <$> (Prod.map id Prod.fst <$>
          semRecvHookS (paramsV1 C K idA idB) Dh encPt encT decT lam (50000 * q) (25001 * q + 25000)
            (fig8IdSemHook (PQC := BitVec 512) none) qep (2 ^ 32 + q + 2) sC () Q w isDel) := by
    intro Q w isDel
    have h0 := recvHookOfBranchesC_eval C K Dh encPt encT decT lam idA idB
      q qep (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000) sameSpec.comp newSpec.comp
      (fun sC₀ Q₀ w₀ isDel₀ pq'₀ i₀ pk₀ T?₀ lct₀ honestC₀ ci₀ hb₀ hs₀ => by
        rw [sameSpec.heval hℓ sC₀ Q₀ w₀ isDel₀ pq'₀ i₀ pk₀ T?₀ lct₀ honestC₀ ci₀ hb₀ hs₀]
        dsimp only [semRecvSameBranch]; split_ifs
        · simp only [map_pure, Prod.map, id_eq]
        · rfl)
      (newSpec.heval hℓ) sC Q w isDel hBnd hExtra
    have h1 := congrArg (Functor.map (simRecvOutEnc (ℓ := ℓ) (Pt := Pt))) h0
    rwa [Functor.map_map, show (fun a => simRecvOutEnc (ℓ := ℓ) (Pt := Pt)
        (Prod.map (Option.map recvResultDec) simFullDec a)) = id from
        funext simRecvOutEnc_simRecvOutDec, id_map] at h1
  have hBaseInv : ∀ (o : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
      {res sC'}, (res, sC') ∈ support ((simFig8OracleSan (paramsV1 C K idA idB) Dh encPt encT
        decT lam qep (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000) (25000 * q)
        (.inr o)).run sC) → SimCStateInv q m sC' ∧ SanSnapExtra C K sC' := by
    intro o res sC' hmem
    have hE := sanSnapExtra_step C K idA idB Dh encPt encT decT lam qep
      (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000) (25000 * q) o sC hExtra _ hmem
    simp only [simFig8OracleSan, StateT.run_mk, support_map, Set.mem_image] at hmem
    rcases hmem with ⟨⟨_, sC₁, _⟩, hmem_s, hEq⟩; cases hEq
    exact ⟨semHandleHookDedupS_preserves_sC_inv (P := paramsV1 C K idA idB) Dh encPt encT decT lam
      (50000 * q) (25001 * q + 25000) (25000 * q) (fig8IdSemHook (PQC := BitVec 512) none)
      q m qep (2 ^ 32 + q + 2) o sC () hSim _ hmem_s, hE⟩
  have hrrDec : ∀ (res : Option (RecvResult (Plain ℓ))),
      (res.map (recvResultEnc (ℓ := ℓ) (Pt := Pt))).map recvResultDec = res := by
    rintro (_ | r); · rfl
    · exact congrArg some (recvResultDec_recvResultEnc_local r)
  rcases t with (((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q
  · refine ⟨?_, semSendHookHalted_mem_inv (decT := decT) ⟨hm, hSim, hExtra, hTr⟩ Q m₀ none r⟩
    change ((handlerImpl (C := e2eSessionCodec ℓ Pt) (simFig8HaltedStepSendC idA idB qep q)
        (.inr (.inl (.inl (.inl (.inl (Q, m₀, r))))))).run (simHaltedEnc (sC, tr))) = _
    let ρ0 := Env.cons (t := .prod .bool (.prod PlainT (.prod (.opt PlainT) (.opt BV512))))
      (partyToBool Q, (m₀, (none, r)))
      (.cons (simHaltedEnc (sC, tr))
        (.cons (t := smQT (ℓ := ℓ) (Pt := Pt)) (Sum.inl (partyToBool Q, (m₀, r))) .nil))
    have hh := simFig8HaltedSendHookC_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) idA idB qep q
      .v1 (.fst .v0) (.fst (.snd .v0)) (.fst (.snd (.snd .v0))) (.snd (.snd (.snd .v0))) ρ0
      sC tr Q m₀ none r rfl (partyToBool_eq_partyEnc Q) rfl rfl rfl (hExtra.1 Q) (hTr.bOk Q) hTrQ.sentB_len
    dsimp only [handlerImpl, e2eSessionCodec, smQenc, smRdec, simFig8OracleSanHalted,
      HAdd.hAdd, QueryImpl.instHAddSumHAddOracleSpec, QueryImpl.add, StateT.run, StateT.mk]
    dsimp only [simFig8HaltedStepSendC, Comp.eval]
    change ((simFig8HaltedSendHookC idA idB qep q .v1 (.fst .v0) (.fst (.snd .v0))
        (.fst (.snd (.snd .v0))) (.snd (.snd (.snd .v0)))).eval ρ0 >>=
        fun x => pure ((x.1, (none, none)), x.2)) >>= (fun p => pure (p.1.1, p.2)) = _
    simp only [bind_assoc, pure_bind, Prod.mk.eta, bind_pure, hh]; rfl
  · refine ⟨?_, semSendHookHalted_mem_inv (decT := decT) ⟨hm, hSim, hExtra, hTr⟩ Q m₀ (some m₁) r⟩
    change ((handlerImpl (C := e2eSessionCodec ℓ Pt) (simFig8HaltedStepSendC idA idB qep q)
        (.inr (.inl (.inl (.inl (.inr (Q, m₀, m₁, r))))))).run (simHaltedEnc (sC, tr))) = _
    let ρ0 := Env.cons (t := .prod .bool (.prod PlainT (.prod (.opt PlainT) (.opt BV512))))
      (partyToBool Q, (m₀, (some m₁, r)))
      (.cons (simHaltedEnc (sC, tr))
        (.cons (t := smQT (ℓ := ℓ) (Pt := Pt)) (Sum.inr (Sum.inl (partyToBool Q, (m₀, (m₁, r))))) .nil))
    have hh := simFig8HaltedSendHookC_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) idA idB qep q
      .v1 (.fst .v0) (.fst (.snd .v0)) (.fst (.snd (.snd .v0))) (.snd (.snd (.snd .v0))) ρ0
      sC tr Q m₀ (some m₁) r rfl (partyToBool_eq_partyEnc Q) rfl rfl rfl (hExtra.1 Q) (hTr.bOk Q) hTrQ.sentB_len
    dsimp only [handlerImpl, e2eSessionCodec, smQenc, smRdec, simFig8OracleSanHalted,
      HAdd.hAdd, QueryImpl.instHAddSumHAddOracleSpec, QueryImpl.add, StateT.run, StateT.mk]
    dsimp only [simFig8HaltedStepSendC, Comp.eval]
    change ((simFig8HaltedSendHookC idA idB qep q .v1 (.fst .v0) (.fst (.snd .v0))
        (.fst (.snd (.snd .v0))) (.snd (.snd (.snd .v0)))).eval ρ0 >>=
        fun x => pure ((x.1, (none, none)), x.2)) >>= (fun p => pure (p.1.1, p.2)) = _
    simp only [bind_assoc, pure_bind, Prod.mk.eta, bind_pure, hh]; rfl
  · refine ⟨?_, ?_⟩
    · dsimp only [simFig8HaltedRawStepC, simHaltedStepDispatchC,
        handlerImpl, e2eSessionCodec, smQenc, smRdec, simFig8OracleSanHalted,
        HAdd.hAdd, QueryImpl.instHAddSumHAddOracleSpec, QueryImpl.add, StateT.run, StateT.mk]
      let ρ0 := Env.cons (t := .prod .bool (.prod (B 32) .bool)) (partyToBool Q, (w, true))
        (.cons (simHaltedEnc (sC, tr))
          (.cons (t := smQT (ℓ := ℓ) (Pt := Pt))
            (Sum.inr (Sum.inr (Sum.inl (partyToBool Q, w)))) .nil))
      let j? := sC.base.honest.reverse.findIdx? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
      have hj : (Expr.ite (.snd (.snd .v0))
          (findRevHonestIdxE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
            (decT := decT) (lam := lam) q (ssHonest (scBase (.fst .v1))) (.fst .v0) (.fst (.snd .v0)))
          .none).eval ρ0 = j? := by
        rw [ite_eval]; dsimp only [Expr.eval, ↓reduceIte]
        exact findRevHonestIdxE_eval q _ _ _ ρ0 sC.base.honest Q w rfl rfl rfl hBnd.base.honest_le
      change (((Comp.ret (.ite (.snd (.snd .v0))
            (findRevHonestIdxE q (ssHonest (scBase (.fst .v1))) (.fst .v0) (.fst (.snd .v0))) .none)).bind
          (.bind (callSub1C cRecv (.pair (.fst .v2) .v1))
            (.ret (.pair (.pair .none (.pair (.fst .v0) .none))
              (.pair (.snd .v0) (kemOnDeliverPostAtomicE q (.fst .v2) .v1 (.fst .v0) (.snd .v3))))))).eval ρ0 >>=
          fun p => pure (p.1.2.1.map recvResultDec, p.2)) = _
      rw [Comp.eval, Comp.eval, hj, pure_bind, Comp.eval, callSub1C_eval]
      have harg : (Expr.pair (.fst .v2) .v1 :
          Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) _ (recvHookInpT ℓ Pt)).eval
          (Env.cons (t := .opt .nat) j? ρ0) = (simFullEnc sC, (partyToBool Q, (w, true))) := rfl
      rw [harg, hrecv Q w true, ← simFig8OracleSan_deliver_eq C K Dh encPt encT decT lam idA idB qep
        (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000) (25000 * q) Q w sC]
      simp only [bind_map_left, map_bind, bind_assoc]
      refine bind_congr fun ⟨res, sC'⟩ => ?_
      let ρ2 := Env.cons (t := recvOutT ℓ Pt) (simRecvOutEnc (res, sC'))
        (Env.cons (t := .opt .nat) j? ρ0)
      have hpost := kemOnDeliverPostAtomicE_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) q (.fst .v2) .v1 (.fst .v0) (.snd .v3) ρ2
        Q j? res tr rfl rfl rfl rfl hTrQ
      change (pure ((none, ((res.map recvResultEnc, none) : _)),
          (simFullEnc sC', (kemOnDeliverPostAtomicE q (.fst .v2) .v1 (.fst .v0) (.snd .v3)).eval ρ2)) >>=
        fun p => pure (p.1.2.1.map recvResultDec, p.2)) = _
      rw [hpost, pure_bind, map_pure]; dsimp only [Prod.map, id_eq, simHaltedEnc, j?]; rw [hrrDec res]
      rcases res with _ | (_ | _) <;>
        cases sC.base.honest.reverse.findIdx? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) <;> rfl
    · rintro ⟨res₀, sC₀, tr₀⟩ hr
      let tr₀' : KemFailTrackState C.F := tr₀
      change HaltedEvalInv C K q m (sC₀, tr₀')
      dsimp only [simFig8OracleSanHalted, HAdd.hAdd, QueryImpl.instHAddSumHAddOracleSpec,
        QueryImpl.add, StateT.run, StateT.mk] at hr
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
      rcases hr with ⟨x, hmem, heq⟩
      have hsC : sC₀ = x.2 := (Prod.mk.inj (Prod.mk.inj heq).2).1
      have htr : tr₀ = _ := (Prod.mk.inj (Prod.mk.inj heq).2).2
      rcases x with ⟨res, sC'⟩; subst hsC
      obtain ⟨hSim', hExtra'⟩ := hBaseInv (.inl (.inl (.inr (Q, w)))) hmem
      refine ⟨by omega, hSim', hExtra', ?_⟩
      rcases res with _ | (_ | _)
      · dsimp only at htr; have htr' : tr₀' = tr := htr; rw [htr']; exact hTr.mono (by omega)
      · dsimp only at htr; have htr' : tr₀' = tr := htr; rw [htr']; exact hTr.mono (by omega)
      · rcases hfind : sC.base.honest.reverse.findIdx?
            (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) with _ | j
        · rw [hfind] at htr; dsimp only at htr
          have htr' : tr₀' = tr := htr; rw [htr']; exact hTr.mono (by omega)
        · rw [hfind] at htr; dsimp only at htr
          have htr' : tr₀' = stepKemFailDeliver C.F K tr Q j := htr
          rw [htr']
          exact (kemTrackDeliverInv_step C.F K (q - (m + 1)) tr Q j hTr).mono (by omega)
  · refine ⟨?_, ?_⟩
    · dsimp only [simFig8HaltedRawStepC, simHaltedStepDispatchC,
        handlerImpl, e2eSessionCodec, smQenc, smRdec, simFig8OracleSanHalted,
        HAdd.hAdd, QueryImpl.instHAddSumHAddOracleSpec, QueryImpl.add, StateT.run, StateT.mk]
      let ρ0 := Env.cons (t := .prod .bool (.prod (B 32) .bool)) (partyToBool Q, (w, false))
        (.cons (simHaltedEnc (sC, tr))
          (.cons (t := smQT (ℓ := ℓ) (Pt := Pt))
            (Sum.inr (Sum.inr (Sum.inr (Sum.inl (partyToBool Q, w))))) .nil))
      have hj : (Expr.ite (.snd (.snd .v0))
          (findRevHonestIdxE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
            (decT := decT) (lam := lam) q (ssHonest (scBase (.fst .v1))) (.fst .v0) (.fst (.snd .v0)))
          .none).eval ρ0 = (none : Option ℕ) := by
        rw [ite_eval]; rfl
      change (((Comp.ret (.ite (.snd (.snd .v0))
            (findRevHonestIdxE q (ssHonest (scBase (.fst .v1))) (.fst .v0) (.fst (.snd .v0))) .none)).bind
          (.bind (callSub1C cRecv (.pair (.fst .v2) .v1))
            (.ret (.pair (.pair .none (.pair (.fst .v0) .none))
              (.pair (.snd .v0) (kemOnDeliverPostAtomicE q (.fst .v2) .v1 (.fst .v0) (.snd .v3))))))).eval ρ0 >>=
          fun p => pure (p.1.2.1.map recvResultDec, p.2)) = _
      rw [Comp.eval, Comp.eval, hj, pure_bind, Comp.eval, callSub1C_eval]
      have harg : (Expr.pair (.fst .v2) .v1 :
          Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) _ (recvHookInpT ℓ Pt)).eval
          (Env.cons (t := .opt .nat) none ρ0) = (simFullEnc sC, (partyToBool Q, (w, false))) := rfl
      rw [harg, hrecv Q w false, ← simFig8OracleSan_inject_eq C K Dh encPt encT decT lam idA idB qep
        (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000) (25000 * q) Q w sC]
      simp only [bind_map_left, bind_assoc, Functor.map_map]
      rw [map_eq_bind_pure_comp]
      refine OracleComp.bind_congr' rfl fun ⟨res, sC'⟩ => ?_
      let ρ2 := Env.cons (t := recvOutT ℓ Pt) (simRecvOutEnc (res, sC'))
        (Env.cons (t := .opt .nat) none ρ0)
      have hpost := kemOnDeliverPostAtomicE_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) q (.fst .v2) .v1 (.fst .v0) (.snd .v3) ρ2
        Q none res tr rfl rfl rfl rfl hTrQ
      change (pure ((none, ((res.map recvResultEnc, none) : _)),
          (simFullEnc sC', (kemOnDeliverPostAtomicE q (.fst .v2) .v1 (.fst .v0) (.snd .v3)).eval ρ2)) >>=
        fun p => pure (p.1.2.1.map recvResultDec, p.2)) = _
      rw [hpost, pure_bind]; clear hpost
      dsimp only [Function.comp_def, Prod.map, id_eq]; rw [hrrDec res]
      rcases res with _ | (_ | _) <;> rfl
    · rintro ⟨res₀, sC₀, tr₀⟩ hr
      let tr₀' : KemFailTrackState C.F := tr₀
      change HaltedEvalInv C K q m (sC₀, tr₀')
      dsimp only [simFig8OracleSanHalted, HAdd.hAdd, QueryImpl.instHAddSumHAddOracleSpec,
        QueryImpl.add, StateT.run, StateT.mk] at hr
      simp only [support_map, Set.mem_image] at hr
      rcases hr with ⟨⟨res, sC'⟩, hmem, heq⟩
      have heq' : (res, sC', tr) = (res₀, sC₀, tr₀') := heq
      rcases Prod.mk.inj (Prod.mk.inj heq').2 with ⟨rfl, rfl⟩
      obtain ⟨hSim', hExtra'⟩ := hBaseInv (.inl (.inr (Q, w))) hmem
      exact ⟨by omega, hSim', hExtra', hTr.mono (by omega)⟩
  · refine ⟨?_, ?_⟩
    · dsimp only [simFig8HaltedRawStepC, simHaltedStepDispatchC,
        handlerImpl, e2eSessionCodec, smQenc, smRdec, simFig8OracleSanHalted,
        HAdd.hAdd, QueryImpl.instHAddSumHAddOracleSpec, QueryImpl.add, StateT.run, StateT.mk]
      let corrC := simFig8StepCorrC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
        (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB q
      let qEnc : (smQT (ℓ := ℓ) (Pt := Pt)).denote :=
        Sum.inr (Sum.inr (Sum.inr (Sum.inr (partyToBool Q))))
      have hcorr0 := simFig8StepCorrC_run (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) idA idB qep q hℓ Q (simFullEnc sC)
        (by rwa [simFullDec_simFullEnc]) (by rwa [simFullDec_simFullEnc])
      rw [simFullDec_simFullEnc] at hcorr0
      have hcorr := congrArg (Functor.map (Prod.map id (simFullEnc (ℓ := ℓ) (Pt := Pt)))) hcorr0
      rw [Functor.map_map, show (fun a => Prod.map id (simFullEnc (ℓ := ℓ) (Pt := Pt))
          (Prod.map id simFullDec a)) = id from
          funext (fun ⟨g, v⟩ => Prod.ext rfl (simFullEnc_simFullDec v)), id_map] at hcorr
      change (((callSub2C corrC (.fst .v0) .v1).bind
          (.ret (.pair (.fst .v0) (.pair (.snd .v0) (.snd .v1))))).eval
          (.cons (simHaltedEnc (sC, tr)) (.cons qEnc .nil)) >>=
        fun p => pure (p.1.2.2.map id, p.2)) = _
      rw [Comp.eval, callSub2C_eval]
      have hrun_corr : (((corrC.eval (.cons (simFullEnc sC) (.cons qEnc .nil)) >>=
          fun x => pure ((x.1, (x.2, kemTrackAtomicEnc (ℓ := ℓ) (Pt := Pt) (kemTrackEnc tr))))) >>=
          fun p => pure (p.1.2.2.map id, p.2)) : Fig8Comp Pt ℓ _) =
          (fun (g, s_raw') => (g, (s_raw', kemTrackAtomicEnc (ℓ := ℓ) (Pt := Pt) (kemTrackEnc tr)))) <$>
            ((handlerImpl (C := e2eSessionCodec ℓ Pt) corrC (.inr (.inr Q))).run (simFullEnc sC)) := by
        dsimp only [qEnc, handlerImpl, e2eSessionCodec, smQenc, smRdec, StateT.run, StateT.mk]
        simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
      erw [hrun_corr]; rw [hcorr]; simp only [Functor.map_map]
      congr 1
    · rintro ⟨res₀, sC₀, tr₀⟩ hr
      let tr₀' : KemFailTrackState C.F := tr₀
      change HaltedEvalInv C K q m (sC₀, tr₀')
      dsimp only [simFig8OracleSanHalted, HAdd.hAdd, QueryImpl.instHAddSumHAddOracleSpec,
        QueryImpl.add, StateT.run, StateT.mk] at hr
      simp only [support_map, Set.mem_image] at hr
      rcases hr with ⟨⟨res, sC'⟩, hmem, heq⟩
      have heq' : (res, sC', tr) = (res₀, sC₀, tr₀') := heq
      rcases Prod.mk.inj (Prod.mk.inj heq').2 with ⟨rfl, rfl⟩
      obtain ⟨hSim', hExtra'⟩ := hBaseInv (.inr Q) hmem
      exact ⟨by omega, hSim', hExtra', hTr.mono (by omega)⟩

theorem simFig8RedProgHalted_eval_san (hℓ : ℓ < 10 ^ 6)
    (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hq : CryptoGames.SM.MakesAtMostQueries A q) :
    (simFig8RedProgHalted (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam qep q).eval
        (fun _ => A) () =
      simFig8ClampSanHalted (paramsV1 C K idA idB) K ℓ Dh encPt encT decT
        lam qep (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000) (25000 * q) A := by
  unfold simFig8RedProgHalted; simp only [hℓ, ↓reduceIte]
  let initImpl : Unit → Fig8Comp Pt ℓ
      (Unit × (LibsignalToModularSchemeSimState Bytes Pt ℓ × KemFailTrackState C.F)) := fun _ => do
    let pqrKey ← (liftM ($ᵗ BitVec 256 : ProbComp (BitVec 256)) : Fig8Comp Pt ℓ (BitVec 256))
    return ((),
      (initSimC ((paramsV1 C K idA idB).spqr.init .a2b pqrKey)
        ((paramsV1 C K idA idB).spqr.init .b2a pqrKey),
       initKemFailTrack C.F pqrKey))
  have h0 := eval_eq_simulateQ_of_enc
    (simFig8RedProgHaltedReal (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam qep q)
    (simHaltedEnc (ℓ := ℓ) (Pt := Pt)) (HaltedEvalInv C K q) initImpl
    (simFig8OracleSanHalted (paramsV1 C K idA idB) K Dh encPt encT decT lam qep
      (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000) (25000 * q))
    (fun _ b => pure b) q ()
    (simFig8HaltedInitC_eval C K idA idB Dh encPt encT decT lam)
    (fun r hr => by
      simp only [initImpl, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
      rcases hr with ⟨pqrKey, _, rfl⟩
      exact ⟨le_rfl, simCStateInv_initSimC le_rfl _ _, sanSnapExtra_init C K idA idB pqrKey,
        Nat.sub_self q ▸ kemTrackDeliverInv_init C.F K 0 pqrKey⟩)
    (fun n ⟨sC, tr⟩ => by
      dsimp only [simFig8OracleSanHalted, simFig8OracleSan, fig8SmIface, StateT.run, StateT.mk, StateT.lift]
      simp only [map_eq_bind_pure_comp, Function.comp_def]; rfl)
    (simFig8HaltedRawStepC_step hℓ C K idA idB Dh encPt encT decT lam qep q)
    (fun _ b _ => simFig8HaltedFinishC_eval C K Dh encPt encT decT lam _ b)
    (fun _ hmn h => h.mono hmn)
    (fun _ => A) (fun _ => isQueryBoundP_of_makesAtMostQueries hq)
  rw [h0]; dsimp only [initImpl, simFig8ClampSanHalted]
  simp only [bind_assoc, pure_bind, StateT.run'_eq, map_eq_bind_pure_comp, Function.comp_def]
  rfl

end EvalHelpers

end

end Computational.Proofs.Game.PromotedCostedReds.SimFig8HaltedEvalStep
