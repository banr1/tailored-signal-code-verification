/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeHaltedBase
public import Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeHaltedCost -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeHaltedEval -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeHaltedShort -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeHaltedCoupling -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperCKA -- proof-setup: allow-public-import
import Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeSanCouplingBounds

/-!
# Online-Halted Costed `simDeliverForge` Reduction

Packages the tracker-halted costed reduction `simDeliverForgeRedProgHalted`, proves its
`GRedBounded`, query-bound, shortness, and guardedness properties, and couples its `DeliverForge`
cell and bucket advantages directly to `simDeliverForgeTrackHalted`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeHalted

noncomputable section

open _root_.CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey GhostState Params)
open CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart lFig8)
open CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C kemTrackEnc SimCStateBounded deliverForgeSemHook)
open CryptoGames.SM.Construction.DeliverForge (AdversaryDF AdversaryCompDF MakesAtMostQueriesDF)
open CryptoGames.LibsignalSM.Proofs.Refinement
  (KemFailTrackState initKemFailTrack stepKemFailDeliver)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.LibsignalSession (GRedBounded ratchetCostBudget)
open CryptoVerification.E2E (Bytes idsOf paramsV1)
open _root_.ReductionDsl
  (Sig Ops Ty Env Expr Comp Iface CostedReduction handlerImpl atomicSig atomicSessionOps
   e2eSessionCodec GhostStT BV256 fig8SmIfaceDF smQT smRT partyToBool)

open Computational.Proofs.Game.PromotedCostedReds.SanOracleCore
  (semRecvHookS)
open Computational.Proofs.Game.PromotedCostedReds.SessionProgCommon
  (comp_eval_ret comp_eval_bind eval_eq_simulateQ_of_enc isQueryBoundP_of_makesAtMostQueries)
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeSanOracle
  (dfFullT dfFullEnc dfFullDec_dfFullEnc DFStateInv dfStateInv_initSimC
   simDeliverForgeOracleSan simDeliverForgeOracleSan_preserves_dfStateInv
   simDeliverForgeOracleSan_send_run simDeliverForgeOracleSan_chall_run
   simDeliverForgeOracleSan_deliver_run simDeliverForgeOracleSan_inject_run
   simDeliverForgeOracleSan_corrupt_run)
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeSanSem
  (sanSnapExtra_step_df)
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeHaltedBase
  (dfHaltedT wkTop1CompH smRRecvPackEH dfSendArgTH dfRecvArgTH classifySmQEH
   dfSendStepHaltedC dfStepHaltedC simDeliverForgeInitHaltedC simDeliverForgeFinishHaltedC
   simDeliverForgeOracleSanTrackHalted simDeliverForgeOracleSanQTrackHalted
   simDeliverForgeClampSanTrackHalted simDeliverForgeClampSanQTrackHalted
   semSendTrackHalted semSendTrackHalted_support)
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeHaltedEval
  (dfHaltedEnc partyToBool_eq_partyEnc dfFullEnc_dfFullDec dfSendStepHaltedC_eval)
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeHaltedCoupling
  (forgeGuessedAdvantageCellPaper_challSimDF'Paper_simDeliverForgeClampSanQTrackHalted_eq
   forgeBucketAdvantagePaper_challSimDF'Paper_simDeliverForgeClampSanQTrackHalted_eq)
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeSanCoupling
  (idsOf_eq_paramsV1_id)

abbrev simDeliverForgeRedProgHalted {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) :=
  SimDeliverForgeHaltedBase.simDeliverForgeRedProgHalted
    (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam qep q

theorem simDeliverForgeRedProgHalted_makesAtMostQueriesDF
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hq : CryptoGames.SM.MakesAtMostQueries A q) :
    MakesAtMostQueriesDF
      ((simDeliverForgeRedProgHalted ℓ C K idA idB Dh encPt encT decT lam qep q).eval
        (fun _ => A) ()) q :=
  SimDeliverForgeHaltedCost.simDeliverForgeRedProgHalted_makesAtMostQueriesDF
    C K idA idB Dh encPt encT decT lam qep q A hq

theorem simDeliverForgeRedProgHalted_gRedBounded
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) (hqep : qep ≤ q + 10) :
    GRedBounded (simDeliverForgeRedProgHalted ℓ C K idA idB Dh encPt encT decT lam qep q)
      (fun _ => 1) (fun _ => 0) q q (ratchetCostBudget q (qep + 1)) :=
  SimDeliverForgeHaltedCost.simDeliverForgeRedProgHalted_gRedBounded
    C K idA idB Dh encPt encT decT lam qep q hqep

/-! ## Operational `.eval` bridge -/

section StepAndInitEval

open OracleSpec OracleComp
open _root_.ReductionDsl (smQenc smRdec smRrDec recvResultT recvResultEnc recvResultDec)
open CryptoGames.SM (partyEnc RecvResult)
open CryptoGames.Ratchet.LibsignalSimC (LibsignalToModularSchemeSimState initSimC)
open CryptoVerification.E2E (Bytes paramsV1)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge
  (atomicDraw256_eval eval_sessSpqrKemOp)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedInit
  (initKemTrackAtomicE_eval kemTrackEnc_initKemFailTrack kemTrackAtomicEnc)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedDeliverWitnessSub
  (findRevHonestIdxE_eval)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedDeliverWitness
  (KemTrackDeliverInv kemTrackDeliverInv_init kemTrackDeliverInv_step kemTrackDeliverInv_stepSend
   kemOnDeliverPostAtomicE_eval)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8LoopAndCost
  (simFullEnc eval_initSimCE atomicSpqrV1InitOp_lossless honestPairEnc
   simFullDec_simFullEnc fig8CtOfV_fig8CtV)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8SanCoupling
  (SanSnapExtra sanSnapExtra_init)
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeStepSendCorr
  (simDeliverForgeSendCorrSpec dfSendCorrStateDec)
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeStepRecvFwdCost
  (dfRecvOutT dfRecvOutDec)
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeStepRecvFwd
  (dfRecvHookC dfRecvHookC_eval)

private theorem recvResultDec_eq_smRrDec_id {ℓ : ℕ} {Pt : Type}
    (v : (recvResultT (ℓ := ℓ) (Pt := Pt)).denote) :
    recvResultDec v = smRrDec id v := by
  rcases v with ⟨⟩ | ⟨t, i, _ | m⟩ <;> rfl

private theorem recvResultEnc_recvResultDec_local {ℓ : ℕ} {Pt : Type}
    (v : (recvResultT (ℓ := ℓ) (Pt := Pt)).denote) :
    recvResultEnc (ℓ := ℓ) (Pt := Pt) (recvResultDec (ℓ := ℓ) (Pt := Pt) v) = v := by
  rcases v with ⟨⟩ | ⟨t, i, _ | m⟩ <;> rfl

private theorem recvResultDec_recvResultEnc_local {ℓ : ℕ} {Pt : Type}
    (r : RecvResult (Plain ℓ)) :
    recvResultDec (ℓ := ℓ) (Pt := Pt) (recvResultEnc (ℓ := ℓ) (Pt := Pt) r) = r := by
  rcases r with _ | ⟨t, i, _ | m⟩ <;> rfl

private def dfRecvOutEnc {ℓ : ℕ} {Pt : Type}
    (p : Option (RecvResult (Plain ℓ)) ×
      (LibsignalToModularSchemeSimState Bytes Pt ℓ × List (Fig8C Pt))) :
    (dfRecvOutT ℓ Pt).denote :=
  (p.1.map (recvResultEnc (ℓ := ℓ) (Pt := Pt)), dfFullEnc p.2)

private theorem dfRecvOutEnc_dfRecvOutDec {ℓ : ℕ} {Pt : Type}
    (v : (dfRecvOutT ℓ Pt).denote) :
    dfRecvOutEnc (dfRecvOutDec v) = v := by
  rcases v with ⟨_ | r, st⟩
  · exact Prod.ext rfl (dfFullEnc_dfFullDec st)
  · refine Prod.ext (congrArg some ?_) (dfFullEnc_dfFullDec st)
    rw [← recvResultDec_eq_smRrDec_id]; exact recvResultEnc_recvResultDec_local r

private theorem wkTop1CompH_eval {S : Sig} {O : Ops S}
    {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ : List (Ty S)} {a t : Ty S} (c : Comp O I [a] t) (x : a.denote) (ρ : Env Γ) :
    (wkTop1CompH c).eval (.cons x ρ) = c.eval (.cons x .nil) :=
  Comp.renameM_eval c fun ⦃_⦄ v => by cases v with | zero => rfl | succ w => nomatch w

private theorem fig8SmIfaceDF_liftP_eq_liftM {ℓ : ℕ} {Pt : Type} [SampleableType Pt]
    {α : Type} (p : ProbComp α) :
    (fig8SmIfaceDF ℓ Pt).liftP p =
      (liftM p : AdversaryCompDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
        (BitVec 256) (Fig8C Pt) α) := by
  induction p using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind n mx ih =>
    dsimp only [Iface.liftP] at ih ⊢
    rw [simulateQ_bind, simulateQ_query]
    exact bind_congr ih

private theorem dfStepHaltedC_eval
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) (hℓ : ℓ < 10 ^ 6)
    (t : (CryptoGames.SM.spec (CryptoGames.LibsignalSession.GhostState Bytes)
      (Plain ℓ) (BitVec 512) Bytes).Domain)
    (sC : LibsignalToModularSchemeSimState Bytes Pt ℓ) (ex : List (Fig8C Pt))
    (tr : KemFailTrackState C.F)
    (hbnd : SimCStateBounded q sC)
    (hex : ex.length ≤ q)
    (hextra : SanSnapExtra C K sC)
    (htr : KemTrackDeliverInv C.F K q (kemTrackEnc tr)) :
    ((handlerImpl (C := e2eSessionCodec ℓ Pt)
      (dfStepHaltedC ℓ C K idA idB Dh encPt encT decT lam qep q) (.inr t)).run
      (dfHaltedEnc ((sC, ex), tr))) =
    Prod.map id dfHaltedEnc <$>
      (simDeliverForgeOracleSanQTrackHalted (paramsV1 C K idA idB) K Dh encPt encT decT lam
        qep q (.inr t)).run ((sC, ex), tr) := by
  let s_raw : (dfHaltedT ℓ Pt).denote := dfHaltedEnc ((sC, ex), tr)
  let Γs : List (Ty (atomicSig ℓ Pt)) := [dfSendArgTH ℓ Pt, dfHaltedT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
  let Γc : List (Ty (atomicSig ℓ Pt)) :=
    [.bool, .sum (dfRecvArgTH ℓ Pt) .bool, dfHaltedT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
  rcases t with (((⟨Q, m, r⟩ | ⟨Q, m0, m1, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q
  · simp only [StateT.run, StateT.mk, handlerImpl, e2eSessionCodec, smQenc, dfStepHaltedC,
      classifySmQEH, Comp.eval, Expr.eval, Env.get, bind_pure_comp, smRdec,
      simDeliverForgeOracleSanQTrackHalted, simDeliverForgeOracleSanTrackHalted]
    let ρs : Env Γs :=
      .cons (partyToBool Q, (m, (none, r)))
        (.cons s_raw (.cons (t := smQT (ℓ := ℓ) (Pt := Pt)) (.inl (partyToBool Q, (m, r))) .nil))
    have hsend := dfSendStepHaltedC_eval ℓ C K idA idB Dh encPt encT decT lam qep q
      (Γ := Γs) (.var (.succ .zero)) (.fst (.var .zero))
      (.fst (.snd (.var .zero))) (.fst (.snd (.snd (.var .zero)))) (.snd (.snd (.snd (.var .zero))))
      ρs sC ex tr Q rfl (partyToBool_eq_partyEnc Q) hextra (htr.bOk Q) htr.sentB_len
    change (fun a => (a.1.1, a.2)) <$>
      (dfSendStepHaltedC idA idB qep q (.var (.succ .zero)) (.fst (.var .zero))
        (.fst (.snd (.var .zero))) (.fst (.snd (.snd (.var .zero))))
        (.snd (.snd (.snd (.var .zero))))).eval ρs = _
    rw [hsend, Functor.map_map]
    congr 1
  · simp only [StateT.run, StateT.mk, handlerImpl, e2eSessionCodec, smQenc, dfStepHaltedC,
      classifySmQEH, Comp.eval, Expr.eval, Env.get, bind_pure_comp, smRdec,
      simDeliverForgeOracleSanQTrackHalted, simDeliverForgeOracleSanTrackHalted]
    let ρs : Env Γs :=
      .cons (partyToBool Q, (m0, (some m1, r)))
        (.cons s_raw
          (.cons (t := smQT (ℓ := ℓ) (Pt := Pt)) (.inr (.inl (partyToBool Q, (m0, (m1, r))))) .nil))
    have hsend := dfSendStepHaltedC_eval ℓ C K idA idB Dh encPt encT decT lam qep q
      (Γ := Γs) (.var (.succ .zero)) (.fst (.var .zero))
      (.fst (.snd (.var .zero))) (.fst (.snd (.snd (.var .zero)))) (.snd (.snd (.snd (.var .zero))))
      ρs sC ex tr Q rfl (partyToBool_eq_partyEnc Q) hextra (htr.bOk Q) htr.sentB_len
    change (fun a => (a.1.1, a.2)) <$>
      (dfSendStepHaltedC idA idB qep q (.var (.succ .zero)) (.fst (.var .zero))
        (.fst (.snd (.var .zero))) (.fst (.snd (.snd (.var .zero))))
        (.snd (.snd (.snd (.var .zero))))).eval ρs = _
    rw [hsend, Functor.map_map]
    congr 1
  · simp only [StateT.run, StateT.mk, handlerImpl, e2eSessionCodec, smQenc, dfStepHaltedC,
      classifySmQEH, smRRecvPackEH, Comp.eval, Expr.eval, Env.get, pure_bind, wkTop1CompH_eval,
      bind_pure_comp, smRdec, ↓reduceIte,
      simDeliverForgeOracleSanQTrackHalted, simDeliverForgeOracleSanTrackHalted]
    let Γr0 : List (Ty (atomicSig ℓ Pt)) :=
      [dfRecvArgTH ℓ Pt, .sum (dfRecvArgTH ℓ Pt) .bool, dfHaltedT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
    let ρr0 : Env Γr0 :=
      .cons (partyToBool Q, (w, true))
        (.cons (.inl (partyToBool Q, (w, true)))
          (.cons s_raw
            (.cons (t := smQT (ℓ := ℓ) (Pt := Pt)) (.inr (.inr (.inl (partyToBool Q, w)))) .nil)))
    have hfnd := findRevHonestIdxE_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) q (Γ := Γr0)
      (SimFig8State.ssHonest (SimFig8State.scBase (.fst (.fst (.var (.succ (.succ .zero)))))))
      (.fst (.var .zero)) (.fst (.snd (.var .zero)))
      ρr0 sC.base.honest Q w rfl rfl rfl hbnd.base.honest_le
    dsimp only [ρr0] at hfnd
    rw [hfnd, partyToBool_eq_partyEnc Q]
    have hrecv0 := dfRecvHookC_eval C K idA idB Dh encPt encT decT lam qep q hℓ
      (dfFullEnc (sC, ex)) Q w true
      (by simpa [dfFullEnc] using hbnd)
      (by simpa [dfFullEnc] using hex)
      (by simpa [dfFullEnc] using hextra)
    simp only [dfFullEnc, simFullDec_simFullEnc, List.map_map, Function.comp_def,
      fig8CtOfV_fig8CtV, List.map_id'] at hrecv0
    have hrecv :
        (dfRecvHookC C K idA idB Dh encPt encT decT lam qep q).eval
          (.cons (dfFullEnc (sC, ex), (partyEnc Q, (w, true))) .nil) =
        dfRecvOutEnc <$> semRecvHookS (paramsV1 C K idA idB) Dh encPt encT decT lam
          (50000 * q) (25001 * q + 25000)
          (deliverForgeSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ))
          qep (2 ^ 32) sC ex Q w true := by
      rw [← hrecv0, Functor.map_map,
        show (fun a => dfRecvOutEnc (dfRecvOutDec a)) = id from funext dfRecvOutEnc_dfRecvOutDec,
        id_map]
    dsimp only [s_raw, dfHaltedEnc]
    rw [hrecv]
    simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]
    refine bind_congr fun ⟨res, s'⟩ => ?_
    let j? := sC.base.honest.reverse.findIdx? (fun wc =>
      wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
    let out := dfRecvOutEnc (res, s')
    let Γr2 : List (Ty (atomicSig ℓ Pt)) :=
      [dfRecvOutT ℓ Pt, .opt .nat, dfRecvArgTH ℓ Pt, .sum (dfRecvArgTH ℓ Pt) .bool,
        dfHaltedT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
    let ρr2 : Env Γr2 :=
      .cons out
        (.cons j?
          (.cons (partyToBool Q, (w, true))
            (.cons (.inl (partyToBool Q, (w, true)))
              (.cons s_raw
                (.cons (t := smQT (ℓ := ℓ) (Pt := Pt))
                  (.inr (.inr (.inl (partyToBool Q, w)))) .nil)))))
    have hpost := kemOnDeliverPostAtomicE_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) q (Γ := Γr2)
      (.fst (.var (.succ (.succ .zero))))
      (.var (.succ .zero))
      (.fst (.var .zero))
      (.snd (.var (.succ (.succ (.succ (.succ .zero))))))
      ρr2 Q j? res tr rfl rfl rfl rfl htr
    dsimp only [Prod.map]
    congr 1
    apply Prod.ext
    · rcases res with _ | r
      · rfl
      · exact congrArg some (recvResultDec_recvResultEnc_local r)
    · dsimp only [ρr2, out, dfRecvOutEnc, s_raw, dfHaltedEnc] at hpost ⊢
      rw [partyToBool_eq_partyEnc] at hpost
      exact Prod.ext rfl hpost
  · simp only [StateT.run, StateT.mk, handlerImpl, e2eSessionCodec, smQenc, dfStepHaltedC,
      classifySmQEH, smRRecvPackEH, Comp.eval, Expr.eval, Env.get, pure_bind, wkTop1CompH_eval,
      bind_pure_comp, smRdec, Bool.false_eq_true, ↓reduceIte,
      simDeliverForgeOracleSanQTrackHalted, simDeliverForgeOracleSanTrackHalted]
    rw [partyToBool_eq_partyEnc Q]
    have hrecv0 := dfRecvHookC_eval C K idA idB Dh encPt encT decT lam qep q hℓ
      (dfFullEnc (sC, ex)) Q w false
      (by simpa [dfFullEnc] using hbnd)
      (by simpa [dfFullEnc] using hex)
      (by simpa [dfFullEnc] using hextra)
    simp only [dfFullEnc, simFullDec_simFullEnc, List.map_map, Function.comp_def,
      fig8CtOfV_fig8CtV, List.map_id'] at hrecv0
    have hrecv :
        (dfRecvHookC C K idA idB Dh encPt encT decT lam qep q).eval
          (.cons (dfFullEnc (sC, ex), (partyEnc Q, (w, false))) .nil) =
        dfRecvOutEnc <$> semRecvHookS (paramsV1 C K idA idB) Dh encPt encT decT lam
          (50000 * q) (25001 * q + 25000)
          (deliverForgeSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ))
          qep (2 ^ 32) sC ex Q w false := by
      rw [← hrecv0, Functor.map_map,
        show (fun a => dfRecvOutEnc (dfRecvOutDec a)) = id from funext dfRecvOutEnc_dfRecvOutDec,
        id_map]
    dsimp only [s_raw, dfHaltedEnc]
    rw [hrecv]
    simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]
    refine bind_congr fun ⟨res, s'⟩ => ?_
    dsimp only [Prod.map, dfRecvOutEnc]
    congr 1
    apply Prod.ext
    · rcases res with _ | r
      · rfl
      · exact congrArg some (recvResultDec_recvResultEnc_local r)
    · rfl
  · simp only [StateT.run, StateT.mk, handlerImpl, e2eSessionCodec, smQenc, dfStepHaltedC,
      classifySmQEH, Comp.eval, Expr.eval, Env.get, bind_pure_comp, smRdec,
      simDeliverForgeOracleSanQTrackHalted, simDeliverForgeOracleSanTrackHalted]
    let ρc : Env Γc :=
      .cons (partyToBool Q)
        (.cons (t := .sum (dfRecvArgTH ℓ Pt) .bool) (.inr (partyToBool Q))
          (.cons s_raw
            (.cons (t := smQT (ℓ := ℓ) (Pt := Pt))
              (.inr (.inr (.inr (.inr (partyToBool Q))))) .nil)))
    have hcorr := (simDeliverForgeSendCorrSpec ℓ C K idA idB Dh encPt encT decT lam qep q).hcorr_eval
      hℓ (Γ := Γc) (.fst (.var (.succ (.succ .zero)))) (.var .zero) ρc Q
      (partyToBool_eq_partyEnc Q)
      (by simpa [dfSendCorrStateDec, ρc, s_raw, dfHaltedEnc, Env.get, Expr.eval, dfFullEnc] using hbnd)
      (by simpa [dfSendCorrStateDec, ρc, s_raw, dfHaltedEnc, Env.get, Expr.eval, dfFullEnc] using hextra)
    conv at hcorr =>
      rhs
      simp only [ρc, s_raw, dfHaltedEnc, Env.get, Expr.eval,
        dfFullEnc, simFullDec_simFullEnc, List.map_map, Function.comp_def,
        fig8CtOfV_fig8CtV, List.map_id']
    dsimp only [ρc, s_raw, dfHaltedEnc] at hcorr ⊢
    rw [← hcorr]
    simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]
    refine bind_congr fun ⟨r1, s_raw'⟩ => ?_
    dsimp only [Prod.map, dfHaltedEnc]
    congr 1
    exact Prod.ext Option.map_id' (Prod.ext (dfFullEnc_dfFullDec s_raw').symm rfl)

private theorem simDeliverForgeInitHaltedC_eval
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) :
    (simDeliverForgeInitHaltedC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam).eval
      (.cons () .nil) =
    Prod.map id dfHaltedEnc <$>
      (do
        let pqrKey ← (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) :
          AdversaryCompDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
            (BitVec 256) (Fig8C Pt) (BitVec 256))
        let sC₀ : LibsignalToModularSchemeSimState Bytes Pt ℓ :=
          initSimC ((paramsV1 C K idA idB).spqr.init .a2b pqrKey)
            ((paramsV1 C K idA idB).spqr.init .b2a pqrKey)
        let tr₀ := initKemFailTrack C.F pqrKey
        return ((), ((sC₀, ([] : List (Fig8C Pt))), tr₀))) := by
  dsimp only [simDeliverForgeInitHaltedC]
  rw [comp_eval_bind, atomicDraw256_eval, fig8SmIfaceDF_liftP_eq_liftM]
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  refine bind_congr fun pqrKey => ?_
  rw [comp_eval_ret]
  refine congrArg pure ?_
  have hp : ∀ {Γ a b} (e₁ : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ a)
      (e₂ : Expr _ Γ b) (ρ : Env Γ),
      (Expr.pair e₁ e₂).eval ρ = (e₁.eval ρ, e₂.eval ρ) := fun _ _ _ => rfl
  rw [hp, hp, hp, eval_initSimCE, eval_sessSpqrKemOp, eval_sessSpqrKemOp, initKemTrackAtomicE_eval]
  dsimp only [Expr.eval, Env.get, _root_.ReductionDsl.AtomicSpqrKemOp.eval,
    Prod.map, dfHaltedEnc, dfFullEnc]
  rw [atomicSpqrV1InitOp_lossless C K true, atomicSpqrV1InitOp_lossless C K false,
    ← kemTrackEnc_initKemFailTrack]
  rfl

/-- Under `ℓ < 10 ^ 6` and `MakesAtMostQueries A q`, evaluating `simDeliverForgeRedProgHalted`
equals `simDeliverForgeClampSanQTrackHalted` at `paramsV1 C K idA idB`. -/
theorem simDeliverForgeRedProgHalted_eval_sanQ
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) (hℓ : ℓ < 10 ^ 6)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hq : CryptoGames.SM.MakesAtMostQueries A q) :
    (simDeliverForgeRedProgHalted ℓ C K idA idB Dh encPt encT decT lam qep q).eval
      (fun _ => A) () =
    simDeliverForgeClampSanQTrackHalted (paramsV1 C K idA idB) K ℓ Dh encPt encT decT lam
      qep q A := by
  let P := paramsV1 C K idA idB
  let R0 : CostedReduction (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
      (fig8SmIfaceDF ℓ Pt)
      (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (e2eSessionCodec ℓ Pt) .unit .unit .bool .bool :=
    { σ := dfHaltedT ℓ Pt
      init := simDeliverForgeInitHaltedC C K Dh encPt encT decT lam
      handle := dfStepHaltedC ℓ C K idA idB Dh encPt encT decT lam qep q
      finish := simDeliverForgeFinishHaltedC C K Dh encPt encT decT lam }
  have hRed : simDeliverForgeRedProgHalted ℓ C K idA idB Dh encPt encT decT lam qep q = R0 := by
    unfold simDeliverForgeRedProgHalted SimDeliverForgeHaltedBase.simDeliverForgeRedProgHalted
    simp [R0]; omega
  rw [hRed]
  let Inv : ℕ →
      (LibsignalToModularSchemeSimState Bytes Pt ℓ × List (Fig8C Pt)) × KemFailTrackState C.F →
      Prop :=
    fun m s =>
      m ≤ q ∧ DFStateInv q m s.1 ∧ SanSnapExtra C K s.1.1 ∧
        KemTrackDeliverInv C.F K (q - m) (kemTrackEnc s.2)
  let initImpl : Unit → AdversaryCompDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt)
      (Unit × ((LibsignalToModularSchemeSimState Bytes Pt ℓ × List (Fig8C Pt)) ×
        KemFailTrackState C.F)) :=
    fun _ => do
      let pqrKey ← (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) :
        AdversaryCompDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
          (BitVec 256) (Fig8C Pt) (BitVec 256))
      let sC₀ : LibsignalToModularSchemeSimState Bytes Pt ℓ :=
        initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)
      let tr₀ := initKemFailTrack C.F pqrKey
      return ((), ((sC₀, []), tr₀))
  let so := simDeliverForgeOracleSanQTrackHalted (ℓ := ℓ) P K Dh encPt encT decT lam qep q
  have hev := eval_eq_simulateQ_of_enc R0 dfHaltedEnc Inv initImpl so (fun _ b => pure b) q ()
    (simDeliverForgeInitHaltedC_eval ℓ C K idA idB Dh encPt encT decT lam)
    (by
      intro r hr
      simp only [initImpl, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
      obtain ⟨pqrKey, -, rfl⟩ := hr
      exact ⟨le_rfl, dfStateInv_initSimC le_rfl _ _, sanSnapExtra_init C K idA idB pqrKey,
        kemTrackDeliverInv_init C.F K (q - q) pqrKey⟩)
    (fun n s => rfl)
    (by
      intro m t ⟨⟨sC, ex⟩, tr⟩ ⟨hmq, hdf, hextra, htr⟩
      have hbnd := hdf.toBounded
      refine ⟨dfStepHaltedC_eval ℓ C K idA idB Dh encPt encT decT lam qep q hℓ
        t sC ex tr hbnd.1 hbnd.2 hextra (htr.mono (Nat.sub_le q (m + 1))), ?_⟩
      rintro ⟨rr, ⟨sC', ex'⟩, tr_out⟩ hr
      have hm_le : m ≤ q := by omega
      rcases t with (((⟨Q, m₀, rCoins⟩ | ⟨Q, m₀, m₁, rCoins⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q
      · rcases semSendTrackHalted_support P K Dh encPt encT lam qep sC ex tr Q m₀ none rCoins hr with
          ⟨rfl, rfl, rfl, rfl | ⟨rq, rfl⟩⟩ | ⟨rq, hmem0, htr'⟩
        · exact ⟨hm_le, hdf.mono (Nat.le_succ m), hextra, htr.mono (by omega)⟩
        · exact ⟨hm_le, hdf.mono (Nat.le_succ m), hextra,
            ⟨le_trans htr.sentB_len (by omega), htr.bOk, htr.sentB_deser⟩⟩
        · have hmem : (rr, (sC', ex')) ∈ support
              ((simDeliverForgeOracleSan P Dh encPt encT decT lam qep (2 ^ 32)
                (50000 * q) (25001 * q + 25000) (25000 * q)
                (.inr (.inl (.inl (.inl (.inl (Q, m₀, rCoins))))))).run (sC, ex)) := by
            rw [simDeliverForgeOracleSan_send_run]
            exact hmem0
          have hdf' := simDeliverForgeOracleSan_preserves_dfStateInv P Dh encPt encT decT lam
            q m qep (2 ^ 32) (50000 * q) (25001 * q + 25000) (25000 * q)
            (.inl (.inl (.inl (.inl (Q, m₀, rCoins))))) (sC, ex) hdf (rr, (sC', ex')) hmem
          have hex' := sanSnapExtra_step_df C K idA idB Dh encPt encT decT lam
            qep (2 ^ 32) (50000 * q) (25001 * q + 25000) (25000 * q)
            (.inl (.inl (.inl (.inl (Q, m₀, rCoins))))) (sC, ex) hextra (rr, (sC', ex')) hmem
          have htr1 := kemTrackDeliverInv_stepSend C.F K (q - (m + 1)) tr Q rq htr
          change tr_out = CryptoGames.LibsignalSM.Proofs.Refinement.stepKemFailSend C.F K tr Q rq at htr'
          rw [← htr', show q - (m + 1) + 1 = q - m by omega] at htr1
          exact ⟨hm_le, hdf', hex', htr1⟩
      · rcases semSendTrackHalted_support P K Dh encPt encT lam qep sC ex tr Q m₀ (some m₁) rCoins hr with
          ⟨rfl, rfl, rfl, rfl | ⟨rq, rfl⟩⟩ | ⟨rq, hmem0, htr'⟩
        · exact ⟨hm_le, hdf.mono (Nat.le_succ m), hextra, htr.mono (by omega)⟩
        · exact ⟨hm_le, hdf.mono (Nat.le_succ m), hextra,
            ⟨le_trans htr.sentB_len (by omega), htr.bOk, htr.sentB_deser⟩⟩
        · have hmem : (rr, (sC', ex')) ∈ support
              ((simDeliverForgeOracleSan P Dh encPt encT decT lam qep (2 ^ 32)
                (50000 * q) (25001 * q + 25000) (25000 * q)
                (.inr (.inl (.inl (.inl (.inr (Q, m₀, m₁, rCoins))))))).run (sC, ex)) := by
            rw [simDeliverForgeOracleSan_chall_run]
            exact hmem0
          have hdf' := simDeliverForgeOracleSan_preserves_dfStateInv P Dh encPt encT decT lam
            q m qep (2 ^ 32) (50000 * q) (25001 * q + 25000) (25000 * q)
            (.inl (.inl (.inl (.inr (Q, m₀, m₁, rCoins))))) (sC, ex) hdf (rr, (sC', ex')) hmem
          have hex' := sanSnapExtra_step_df C K idA idB Dh encPt encT decT lam
            qep (2 ^ 32) (50000 * q) (25001 * q + 25000) (25000 * q)
            (.inl (.inl (.inl (.inr (Q, m₀, m₁, rCoins))))) (sC, ex) hextra (rr, (sC', ex')) hmem
          have htr1 := kemTrackDeliverInv_stepSend C.F K (q - (m + 1)) tr Q rq htr
          change tr_out = CryptoGames.LibsignalSM.Proofs.Refinement.stepKemFailSend C.F K tr Q rq at htr'
          rw [← htr', show q - (m + 1) + 1 = q - m by omega] at htr1
          exact ⟨hm_le, hdf', hex', htr1⟩
      · dsimp only [so, simDeliverForgeOracleSanQTrackHalted,
          simDeliverForgeOracleSanTrackHalted, StateT.run, StateT.mk] at hr
        obtain ⟨⟨res, s'⟩, hmem0, hr⟩ := Iff.mp (mem_support_bind_iff _ _ _) hr
        cases hr
        have hmem : (res, (sC', ex')) ∈ support
            ((simDeliverForgeOracleSan P Dh encPt encT decT lam qep (2 ^ 32)
              (50000 * q) (25001 * q + 25000) (25000 * q)
              (.inr (.inl (.inl (.inr (Q, w)))))).run (sC, ex)) := by
          rw [simDeliverForgeOracleSan_deliver_run]
          exact hmem0
        have hdf' := simDeliverForgeOracleSan_preserves_dfStateInv P Dh encPt encT decT lam
          q m qep (2 ^ 32) (50000 * q) (25001 * q + 25000) (25000 * q)
          (.inl (.inl (.inr (Q, w)))) (sC, ex) hdf (res, (sC', ex')) hmem
        have hex' := sanSnapExtra_step_df C K idA idB Dh encPt encT decT lam
          qep (2 ^ 32) (50000 * q) (25001 * q + 25000) (25000 * q)
          (.inl (.inl (.inr (Q, w)))) (sC, ex) hextra (res, (sC', ex')) hmem
        refine ⟨hm_le, hdf', hex', ?_⟩
        clear hmem0 hr hmem hdf' hex'
        dsimp only [P]
        suffices ∀ j? : Option ℕ, KemTrackDeliverInv C.F K (q - m) (kemTrackEnc (
            match res, j? with
            | some (.accepted _ _ _), some j => stepKemFailDeliver C.F K tr Q j
            | _, _ => tr)) from this _
        intro j?
        rcases res with _ | (_ | ⟨t0, i0, m?⟩)
        · exact htr.mono (by omega)
        · exact htr.mono (by omega)
        · rcases j? with _ | j
          · exact htr.mono (by omega)
          · exact (kemTrackDeliverInv_step C.F K (q - (m + 1)) tr Q j htr).mono (by omega)
      · dsimp only [so, simDeliverForgeOracleSanQTrackHalted,
          simDeliverForgeOracleSanTrackHalted, StateT.run, StateT.mk] at hr
        obtain ⟨⟨res, s'⟩, hmem0, hr⟩ := Iff.mp (mem_support_bind_iff _ _ _) hr
        cases hr
        have hmem : (res, (sC', ex')) ∈ support
            ((simDeliverForgeOracleSan P Dh encPt encT decT lam qep (2 ^ 32)
              (50000 * q) (25001 * q + 25000) (25000 * q)
              (.inr (.inl (.inr (Q, w))))).run (sC, ex)) := by
          rw [simDeliverForgeOracleSan_inject_run]
          exact hmem0
        exact ⟨hm_le,
          simDeliverForgeOracleSan_preserves_dfStateInv P Dh encPt encT decT lam
            q m qep (2 ^ 32) (50000 * q) (25001 * q + 25000) (25000 * q)
            (.inl (.inr (Q, w))) (sC, ex) hdf (res, (sC', ex')) hmem,
          sanSnapExtra_step_df C K idA idB Dh encPt encT decT lam
            qep (2 ^ 32) (50000 * q) (25001 * q + 25000) (25000 * q)
            (.inl (.inr (Q, w))) (sC, ex) hextra (res, (sC', ex')) hmem,
          htr.mono (by omega)⟩
      · dsimp only [so, simDeliverForgeOracleSanQTrackHalted,
          simDeliverForgeOracleSanTrackHalted, StateT.run, StateT.mk] at hr
        obtain ⟨⟨res, s'⟩, hmem0, hr⟩ := Iff.mp (mem_support_bind_iff _ _ _) hr
        cases hr
        have hmem : (res, (sC', ex')) ∈ support
            ((simDeliverForgeOracleSan P Dh encPt encT decT lam qep (2 ^ 32)
              (50000 * q) (25001 * q + 25000) (25000 * q)
              (.inr (.inr Q))).run (sC, ex)) := by
          rw [simDeliverForgeOracleSan_corrupt_run]
          exact hmem0
        exact ⟨hm_le,
          simDeliverForgeOracleSan_preserves_dfStateInv P Dh encPt encT decT lam
            q m qep (2 ^ 32) (50000 * q) (25001 * q + 25000) (25000 * q)
            (.inr Q) (sC, ex) hdf (res, (sC', ex')) hmem,
          sanSnapExtra_step_df C K idA idB Dh encPt encT decT lam
            qep (2 ^ 32) (50000 * q) (25001 * q + 25000) (25000 * q)
            (.inr Q) (sC, ex) hextra (res, (sC', ex')) hmem,
          htr.mono (by omega)⟩)
    (fun _ _ _ => rfl)
    (fun {_ _} _ hmn ⟨hnq, hdf, hextra, htr⟩ =>
      ⟨le_trans hmn hnq, hdf.mono hmn, hextra, htr.mono (by omega)⟩)
    (fun _ => A)
    (fun _ => isQueryBoundP_of_makesAtMostQueries hq)
  rw [hev]
  simp only [initImpl, simDeliverForgeClampSanQTrackHalted, simDeliverForgeClampSanTrackHalted,
    StateT.run'_eq, bind_assoc, pure_bind, map_eq_bind_pure_comp, Function.comp_def, P, so]
  refine bind_congr fun pqrKey => bind_congr fun ⟨b, s₁⟩ => rfl

end StepAndInitEval

/-! ## Shortness, guardedness, and `DeliverForge` advantage coupling -/

section ShortAndGuarded

open CryptoVerification.LibsignalSession.HeadlineV1 (SendMsgsOkDF GuardedSMDFShort)
open Computational.Proofs.ReductionDsl.Fig8Atomic (atomicShortPubB)
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeHaltedShort
  (simDeliverForgeClampSanTrackHalted_sendAtomicShortDF
   simDeliverForgeClampSanTrackHalted_guardedSMDFShort)

theorem simDeliverForgeRedProgHalted_sendAtomicShortDF
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6) (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hq : CryptoGames.SM.MakesAtMostQueries A q) :
    SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1)
      ((simDeliverForgeRedProgHalted ℓ C K idA idB Dh encPt encT decT lam qep q).eval
        (fun _ => A) ()) := by
  rw [simDeliverForgeRedProgHalted_eval_sanQ ℓ C K idA idB Dh encPt encT decT lam qep q hℓ A hq]
  exact simDeliverForgeClampSanTrackHalted_sendAtomicShortDF hℓ C K idA idB Dh encPt encT decT lam
    qep (2 ^ 32) (50000 * q) (25001 * q + 25000) (25000 * q) A

theorem simDeliverForgeRedProgHalted_guardedSMDFShort
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6) (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hq : CryptoGames.SM.MakesAtMostQueries A q) :
    GuardedSMDFShort
      ((simDeliverForgeRedProgHalted ℓ C K idA idB Dh encPt encT decT lam qep q).eval
        (fun _ => A) ()) := by
  rw [simDeliverForgeRedProgHalted_eval_sanQ ℓ C K idA idB Dh encPt encT decT lam qep q hℓ A hq]
  exact simDeliverForgeClampSanTrackHalted_guardedSMDFShort (paramsV1 C K idA idB) K
    Dh encPt encT decT lam qep (2 ^ 32) (50000 * q) (25001 * q + 25000) (25000 * q) A

/-- Couples `simDeliverForgeRedProgHalted.eval` to `simDeliverForgeTrackHalted` in
`forgeGuessedAdvantageCellPaper`. -/
theorem forgeGuessedAdvantageCellPaper_challSimDF'Paper_simDeliverForgeRedProgHalted_eq
    {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (hℓ : ℓ < 10 ^ 6) (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hq : CryptoGames.SM.MakesAtMostQueries A q)
    (hq32 : 2 * (q + 1) + 25002 < 2 ^ 32) :
    let P := paramsV1 C K idA idB
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT (idsOf idA idB) 25000 lam
    CryptoGames.SM.Construction.DeliverForge.forgeGuessedAdvantageCellPaper fig (qep + 1)
        CryptoGames.SM.Construction.DeliverForge.sameHdrScheme tL t
        (CryptoGames.SM.Construction.DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          ((simDeliverForgeRedProgHalted ℓ C K idA idB Dh encPt encT decT lam qep q).eval
            (fun _ => A) ())) =
      CryptoGames.SM.Construction.DeliverForge.forgeGuessedAdvantageCellPaper fig (qep + 1)
        CryptoGames.SM.Construction.DeliverForge.sameHdrScheme tL t
        (CryptoGames.SM.Construction.DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (CryptoGames.LibsignalSM.Proofs.Refinement.simDeliverForgeTrackHalted
            P K ℓ Dh encPt encT decT (idsOf idA idB) lam qep A)) := by
  dsimp only []
  rw [simDeliverForgeRedProgHalted_eval_sanQ ℓ C K idA idB Dh encPt encT decT lam qep q hℓ A hq]
  exact forgeGuessedAdvantageCellPaper_challSimDF'Paper_simDeliverForgeClampSanQTrackHalted_eq
    (paramsV1 C K idA idB) K Dh encPt encT decT lam qep q tL t (idsOf idA idB)
    (idsOf_eq_paramsV1_id C K idA idB) A hq hq32

/-- Couples `simDeliverForgeRedProgHalted.eval` to `simDeliverForgeTrackHalted` in
`forgeBucketAdvantagePaper`. -/
theorem forgeBucketAdvantagePaper_challSimDF'Paper_simDeliverForgeRedProgHalted_eq
    {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (hℓ : ℓ < 10 ^ 6) (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) (tL : Option ℕ) (par : Bool)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hq : CryptoGames.SM.MakesAtMostQueries A q)
    (hq32 : 2 * (q + 1) + 25002 < 2 ^ 32) :
    let P := paramsV1 C K idA idB
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT (idsOf idA idB) 25000 lam
    CryptoGames.SM.Construction.DeliverForge.forgeBucketAdvantagePaper fig 1 (qep + 1)
        CryptoGames.SM.Construction.DeliverForge.sameHdrScheme tL par
        (CryptoGames.SM.Construction.DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          ((simDeliverForgeRedProgHalted ℓ C K idA idB Dh encPt encT decT lam qep q).eval
            (fun _ => A) ())) =
      CryptoGames.SM.Construction.DeliverForge.forgeBucketAdvantagePaper fig 1 (qep + 1)
        CryptoGames.SM.Construction.DeliverForge.sameHdrScheme tL par
        (CryptoGames.SM.Construction.DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (CryptoGames.LibsignalSM.Proofs.Refinement.simDeliverForgeTrackHalted
            P K ℓ Dh encPt encT decT (idsOf idA idB) lam qep A)) := by
  dsimp only []
  rw [simDeliverForgeRedProgHalted_eval_sanQ ℓ C K idA idB Dh encPt encT decT lam qep q hℓ A hq]
  exact forgeBucketAdvantagePaper_challSimDF'Paper_simDeliverForgeClampSanQTrackHalted_eq
    (paramsV1 C K idA idB) K Dh encPt encT decT lam qep q tL par (idsOf idA idB)
    (idsOf_eq_paramsV1_id C K idA idB) A hq hq32

end ShortAndGuarded

end

end Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeHalted
