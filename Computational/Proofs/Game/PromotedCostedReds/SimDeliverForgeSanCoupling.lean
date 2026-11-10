/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeSanOracle
public import Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeSanSem
public import Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeSanGame
public import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEClamp2
public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperCKA
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNECouple3
import VCVio.EvalDist.Monad.Basic

/-!
# Sanitized-to-Unclamped Coupling for `SimDeliverForge`

Couples `simDeliverForgeClampSanQ` (and `simDeliverForgeProgOfStep.eval`) at `B = 2 ^ 32` to
`Refinement.simDeliverForge` inside `forgeGuessedAdvantageCellPaper` and
`forgeBucketAdvantagePaper`.
-/

@[expose] public section

set_option autoImplicit false

open ReductionDsl (Comp GhostStT atomicSessionOps e2eSessionCodec fig8SmIfaceDF handlerImpl smQT smRT)

namespace Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeSanCoupling

open OracleSpec OracleComp
open _root_.ReductionDsl (Comp handlerImpl atomicSessionOps e2eSessionCodec
  GhostStT fig8SmIfaceDF smQT smRT)
open _root_.CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.Ratchet.LibsignalInst (lFig8)
open CryptoGames.Ratchet.LibsignalSim (SimCStateBounded simDeliverForgeClamp)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey GhostState Params)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.E2E (Bytes idsOf paramsV1
  forgeGuessedAdvantageCellPaper_challSimDF'Paper_simDeliverForgeClamp_eq)
open CryptoVerification.LibsignalSession.HeadlineV1
  (runBaseDFCellTPaper forgeGuessedAdvantageCellPaperT_eq_runBaseDFCellTPaper)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8SanCoupling
  (SanSnapExtra sanSnapExtra_init)
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeSanOracle
  (dfFullT dfFullDec simDeliverForgeOracleSan simDeliverForgeOracleSanQ
   simDeliverForgeClampSan simDeliverForgeClampSanQ
   simDeliverForgeProgOfStep simDeliverForgeProgOfStep_eval_san
   simDeliverForgeProgOfStep_eval_sanQ)
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeSanSem
  (sanSnapExtra_step_df)
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeSanGame
  (runBaseDFCellTPaper_challSimDF'Paper_simDeliverForgeClampSan_eq)

theorem idsOf_eq_paramsV1_id (C : Crypto) (K : MlKem) (idA idB : IdentityKey) :
    idsOf idA idB =
      fun R => if R == CryptoGames.Party.A then (paramsV1 C K idA idB).idA else (paramsV1 C K idA idB).idB := by
  funext R; cases R <;> rfl

theorem runBaseDFCellTPaper_challSimDF'Paper_simDeliverForgeClampSanQ_eq
    {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) (tL : Option ℕ) (t : ℕ) (idOf : Party → IdentityKey)
    (hid : idOf = fun R => if R == CryptoGames.Party.A then P.idA else P.idB)
    (A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) PQC Bytes)
    (hq : CryptoGames.SM.MakesAtMostQueries A q) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    runBaseDFCellTPaper fig (qep + 1) tL t
        CryptoGames.SM.Construction.DeliverForge.sameHdrScheme (CryptoGames.SM.Config.auth t) false
        (CryptoGames.SM.Construction.DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (simDeliverForgeClampSanQ P ℓ Dh encPt encT decT lam qep q A)) =
      runBaseDFCellTPaper fig (qep + 1) tL t
        CryptoGames.SM.Construction.DeliverForge.sameHdrScheme (CryptoGames.SM.Config.auth t) false
        (CryptoGames.SM.Construction.DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (simDeliverForgeClamp P Dh encPt encT decT lam qep (2 ^ 32) A)) :=
  runBaseDFCellTPaper_challSimDF'Paper_simDeliverForgeClampSan_eq
    P Dh encPt encT decT lam qep (2 ^ 32) (50000 * q) (25001 * q + 25000) (25000 * q)
    tL t idOf hid A q hq (by omega) le_rfl le_rfl

theorem simDeliverForgeProgOfStep_eval_san_snap {ℓ : ℕ} {Pt : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (L qep B T Kc Bsk : ℕ) (hℓ : ℓ < 10 ^ 6)
    (step : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIfaceDF ℓ Pt)
      [dfFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (dfFullT ℓ Pt)))
    (hstep : ∀ t (s_raw : (dfFullT ℓ Pt).denote),
      SimCStateBounded L (dfFullDec s_raw).1 → (dfFullDec s_raw).2.length ≤ L →
      SanSnapExtra C K (dfFullDec s_raw).1 →
      (Prod.map id (dfFullDec (ℓ := ℓ) (Pt := Pt)) <$>
        ((handlerImpl (C := e2eSessionCodec ℓ Pt) step (.inr t)).run s_raw)) =
      ((simDeliverForgeOracleSan (paramsV1 C K idA idB) Dh encPt encT decT lam qep B T Kc Bsk
        (.inr t)).run (dfFullDec s_raw)))
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (q : ℕ) (hq : CryptoGames.SM.MakesAtMostQueries A q) (hqL : q ≤ L) :
    (simDeliverForgeProgOfStep C K Dh encPt encT decT lam step).eval (fun _ => A) () =
      simDeliverForgeClampSan (paramsV1 C K idA idB) ℓ Dh encPt encT decT lam qep B T Kc Bsk A :=
  simDeliverForgeProgOfStep_eval_san C K idA idB Dh encPt encT decT lam L qep B T Kc Bsk hℓ
    (SanSnapExtra C K) (sanSnapExtra_init C K idA idB)
    (sanSnapExtra_step_df C K idA idB Dh encPt encT decT lam qep B T Kc Bsk) step hstep A q hq hqL

theorem simDeliverForgeProgOfStep_eval_sanQ_snap {ℓ : ℕ} {Pt : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (qep q : ℕ) (hℓ : ℓ < 10 ^ 6)
    (step : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIfaceDF ℓ Pt)
      [dfFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (dfFullT ℓ Pt)))
    (hstep : ∀ t (s_raw : (dfFullT ℓ Pt).denote),
      SimCStateBounded q (dfFullDec s_raw).1 → (dfFullDec s_raw).2.length ≤ q →
      SanSnapExtra C K (dfFullDec s_raw).1 →
      (Prod.map id (dfFullDec (ℓ := ℓ) (Pt := Pt)) <$>
        ((handlerImpl (C := e2eSessionCodec ℓ Pt) step (.inr t)).run s_raw)) =
      ((simDeliverForgeOracleSanQ (paramsV1 C K idA idB) Dh encPt encT decT lam qep q
        (.inr t)).run (dfFullDec s_raw)))
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hq : CryptoGames.SM.MakesAtMostQueries A q) :
    (simDeliverForgeProgOfStep C K Dh encPt encT decT lam step).eval (fun _ => A) () =
      simDeliverForgeClampSanQ (paramsV1 C K idA idB) ℓ Dh encPt encT decT lam qep q A :=
  simDeliverForgeProgOfStep_eval_sanQ C K idA idB Dh encPt encT decT lam qep q hℓ
    (SanSnapExtra C K) (sanSnapExtra_init C K idA idB)
    (sanSnapExtra_step_df C K idA idB Dh encPt encT decT lam qep
      (2 ^ 32) (50000 * q) (25001 * q + 25000) (25000 * q)) step hstep A hq

theorem forgeGuessedAdvantageCellPaper_challSimDF'Paper_simDeliverForgeClampSan_eq
    {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep T Kc Bsk : ℕ) (tL : Option ℕ) (t : ℕ) (idOf : Party → IdentityKey)
    (hid : idOf = fun R => if R == CryptoGames.Party.A then P.idA else P.idB)
    (A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) PQC Bytes)
    (q : ℕ) (hq : CryptoGames.SM.MakesAtMostQueries A q)
    (hT : 25000 * q ≤ T) (hKc : 25001 * q + 25000 ≤ Kc) (hBsk : 25000 * q ≤ Bsk)
    (hq32 : 2 * (q + 1) + 25002 < 2 ^ 32) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    CryptoGames.SM.Construction.DeliverForge.forgeGuessedAdvantageCellPaper fig (qep + 1)
        CryptoGames.SM.Construction.DeliverForge.sameHdrScheme tL t
        (CryptoGames.SM.Construction.DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (simDeliverForgeClampSan P ℓ Dh encPt encT decT lam qep (2 ^ 32) T Kc Bsk A)) =
      CryptoGames.SM.Construction.DeliverForge.forgeGuessedAdvantageCellPaper fig (qep + 1)
        CryptoGames.SM.Construction.DeliverForge.sameHdrScheme tL t
        (CryptoGames.SM.Construction.DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (CryptoGames.LibsignalSM.Proofs.Refinement.simDeliverForge
            P ℓ Dh encPt encT decT idOf lam qep A)) := by
  dsimp only []
  rw [forgeGuessedAdvantageCellPaperT_eq_runBaseDFCellTPaper,
    runBaseDFCellTPaper_challSimDF'Paper_simDeliverForgeClampSan_eq
      P Dh encPt encT decT lam qep (2 ^ 32) T Kc Bsk tL t idOf hid A q hq hT hKc hBsk,
    ← forgeGuessedAdvantageCellPaperT_eq_runBaseDFCellTPaper]
  exact forgeGuessedAdvantageCellPaper_challSimDF'Paper_simDeliverForgeClamp_eq
    P Dh encPt encT decT lam qep tL t idOf hid A q hq hq32

theorem forgeGuessedAdvantageCellPaper_challSimDF'Paper_simDeliverForgeClampSanQ_eq
    {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) (tL : Option ℕ) (t : ℕ) (idOf : Party → IdentityKey)
    (hid : idOf = fun R => if R == CryptoGames.Party.A then P.idA else P.idB)
    (A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) PQC Bytes)
    (hq : CryptoGames.SM.MakesAtMostQueries A q) (hq32 : 2 * (q + 1) + 25002 < 2 ^ 32) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    CryptoGames.SM.Construction.DeliverForge.forgeGuessedAdvantageCellPaper fig (qep + 1)
        CryptoGames.SM.Construction.DeliverForge.sameHdrScheme tL t
        (CryptoGames.SM.Construction.DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (simDeliverForgeClampSanQ P ℓ Dh encPt encT decT lam qep q A)) =
      CryptoGames.SM.Construction.DeliverForge.forgeGuessedAdvantageCellPaper fig (qep + 1)
        CryptoGames.SM.Construction.DeliverForge.sameHdrScheme tL t
        (CryptoGames.SM.Construction.DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (CryptoGames.LibsignalSM.Proofs.Refinement.simDeliverForge
            P ℓ Dh encPt encT decT idOf lam qep A)) :=
  forgeGuessedAdvantageCellPaper_challSimDF'Paper_simDeliverForgeClampSan_eq
    P Dh encPt encT decT lam qep (50000 * q) (25001 * q + 25000) (25000 * q)
    tL t idOf hid A q hq (by omega) le_rfl le_rfl hq32

theorem forgeGuessedAdvantageCellPaper_challSimDF'Paper_simDeliverForgeProgOfStep_eq
    {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (hℓ : ℓ < 10 ^ 6) (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) (tL : Option ℕ) (t : ℕ)
    (step : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIfaceDF ℓ Pt)
      [dfFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (dfFullT ℓ Pt)))
    (hstep : ∀ t (s_raw : (dfFullT ℓ Pt).denote),
      SimCStateBounded q (dfFullDec s_raw).1 → (dfFullDec s_raw).2.length ≤ q →
      SanSnapExtra C K (dfFullDec s_raw).1 →
      (Prod.map id (dfFullDec (ℓ := ℓ) (Pt := Pt)) <$>
        ((handlerImpl (C := e2eSessionCodec ℓ Pt) step (.inr t)).run s_raw)) =
      ((simDeliverForgeOracleSanQ (paramsV1 C K idA idB) Dh encPt encT decT lam qep q
        (.inr t)).run (dfFullDec s_raw)))
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hq : CryptoGames.SM.MakesAtMostQueries A q) (hq32 : 2 * (q + 1) + 25002 < 2 ^ 32) :
    let P := paramsV1 C K idA idB
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT (idsOf idA idB) 25000 lam
    CryptoGames.SM.Construction.DeliverForge.forgeGuessedAdvantageCellPaper fig (qep + 1)
        CryptoGames.SM.Construction.DeliverForge.sameHdrScheme tL t
        (CryptoGames.SM.Construction.DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          ((simDeliverForgeProgOfStep C K Dh encPt encT decT lam step).eval (fun _ => A) ())) =
      CryptoGames.SM.Construction.DeliverForge.forgeGuessedAdvantageCellPaper fig (qep + 1)
        CryptoGames.SM.Construction.DeliverForge.sameHdrScheme tL t
        (CryptoGames.SM.Construction.DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (CryptoGames.LibsignalSM.Proofs.Refinement.simDeliverForge
            P ℓ Dh encPt encT decT (idsOf idA idB) lam qep A)) := by
  dsimp only []
  rw [simDeliverForgeProgOfStep_eval_sanQ_snap C K idA idB Dh encPt encT decT lam qep q hℓ step hstep A hq]
  exact forgeGuessedAdvantageCellPaper_challSimDF'Paper_simDeliverForgeClampSanQ_eq
    (paramsV1 C K idA idB) Dh encPt encT decT lam qep q tL t (idsOf idA idB)
    (idsOf_eq_paramsV1_id C K idA idB) A hq hq32

/-! ## Bucket advantage coupling -/

noncomputable section BucketCoupling

open _root_.ReductionDsl (isGameQuery)
open _root_.CryptoGames (SMScheme)
open _root_.CryptoGames.Ratchet (RootKey)
open _root_.CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart lFS ratchetKeyAdmissible)
open _root_.CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C SimFig8St SimFig8C GhostChain SimState
  initSim pushChain deliverForgeSemHook inReceiveOnlyEpoch mkPub
  simParseRecvC onAcceptPure onAnswerPure scPostSendPure evalCKClamp semDrawSendCoins semSendHook
  semFwdAnswerHook semResyncHook semFwdEvictHook semFwdHook semRecvHook semCorrHookDedup
  semHandleHookDedup simDeliverForgeOracleDedup makesAtMostQueries_iff_isGameQuery stateT_lift_run)
open _root_.CryptoGames.Ratchet.LibsignalSimC (Kept LibsignalToModularSchemeSimState initSimC)
open _root_.CryptoGames.SM (GameState Config RecvResult partyEnc noBobSendInEpoch0
  noAliceCorrWhileAliceBelowEpoch10 authLosingConditionsAvoided initState)
open _root_.CryptoGames.SM.Thm1 (Mirror)
open _root_.CryptoGames.SM.Construction.DeliverForge (sameHdrScheme challSimDF'Paper specDF
  AdversaryDF AdversaryCompDF simImplDF'Paper simOraclesDF'Paper simTransmitDF'Paper
  simChallDF'Paper simDeliverDF simInjectDF simCorrDFPaper simDeliverForgeDF simCoinsDF
  transmitQueryDF challQueryDF deliverQueryDF injectQueryDF corrQueryDF deliverForgeQuery
  corrImplPaper deliverForgeBaseImpl oracleImplPaper oracleImplBaseDFPaper fullImplBaseDFPaper
  withWinEpDF bucketAuthCfg fullImplBaseDFPaperBucket forgeGameBucketPaper)
open _root_.CryptoGames.LibsignalSM.Proofs.Refinement (sameWireFig8)
open CryptoVerification.LibsignalSession.HeadlineV1 (cellShift fullImplBaseDFCellTPaper
  fullImplBaseDFCellTPaper_of_not_B1 fullImplBaseDFShiftedPaper_zero_eq_fullImplBaseDFPaper)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8SanGame (KeptInv keptInv_unknown keptInv_ofSt
  keptInv_send keptInv_recv fig8PartyInv_receive lFig8_receive_vS_and_idx GameSanInv
  gameSanInv_init gameSanInv_transmitImpl gameSanInv_deliverImpl gameSanInv_injectImpl)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8SanCoupling (simParseRecvC_tryFrom_and_idx
  evalCKClamp_index_le)
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeSanSem
  (simDeliverForgeOracleSan_inr_inl_eq simDeliverForgeOracleSan_inr_inr_eq_of_support
   run'_simulateQ_simDeliverForgeOracleDedup_eq_public)

abbrev BucketState (Pt : Type) (ℓ : ℕ) :=
  Mirror (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt) ×
    (GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt) × Option ℕ)

section BucketDefs
variable {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
  (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
  (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt)
  (qep : ℕ) (tL : Option ℕ) (par : Bool)

def bucketImplDF : QueryImpl
    (unifSpec + specDF (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt))
    (StateT (BucketState Pt ℓ) ProbComp) := fun q s => do
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT (fun R => if R == Party.A then P.idA else P.idB) 25000 lam
  let ((a, mir'), gsw') ←
    (simulateQ (fullImplBaseDFPaperBucket fig 1 (qep + 1) sameHdrScheme tL par)
      ((simImplDF'Paper (2 + 1) (qep + 1) q).run s.1)).run s.2
  return (a, (mir', gsw'))

theorem bucketImplDF_run
    (q : (unifSpec + specDF (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt)).Domain)
    (mir : Mirror (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt))
    (gsw : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt) × Option ℕ) :
    (bucketImplDF P Dh encPt encT lam qep tL par q).run (mir, gsw) =
      (do
        let fig := lFig8 Dh encPt P.C P.codec ℓ encT (fun R => if R == Party.A then P.idA else P.idB) 25000 lam
        let ((a, mir'), gsw') ←
          (simulateQ (fullImplBaseDFPaperBucket fig 1 (qep + 1) sameHdrScheme tL par)
            ((simImplDF'Paper (2 + 1) (qep + 1) q).run mir)).run gsw
        return (a, (mir', gsw'))) := rfl

def runBucketDF {α : Type}
    (oa : AdversaryCompDF (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt) α)
    (ms₀ : BucketState Pt ℓ) : ProbComp (α × BucketState Pt ℓ) :=
  (simulateQ (bucketImplDF P Dh encPt encT lam qep tL par) oa).run ms₀

theorem runBucketDF_bind {α β : Type}
    (x : AdversaryCompDF (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt) α)
    (f : α → AdversaryCompDF (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt) β)
    (s₀ : BucketState Pt ℓ) :
    runBucketDF P Dh encPt encT lam qep tL par (x >>= f) s₀ =
      (runBucketDF P Dh encPt encT lam qep tL par x s₀ >>= fun ⟨a, s'⟩ =>
        runBucketDF P Dh encPt encT lam qep tL par (f a) s') := by
  dsimp only [runBucketDF]; rw [simulateQ_bind, StateT.run_bind]

theorem bucketImplDF_inl (n : unifSpec.Domain) (s : BucketState Pt ℓ) :
    bucketImplDF P Dh encPt encT lam qep tL par (.inl n) s =
      (query (spec := unifSpec) n >>= fun r => pure (r, s)) := by
  rcases s with ⟨mir, gs, w⟩
  unfold bucketImplDF simImplDF'Paper simCoinsDF fullImplBaseDFPaperBucket withWinEpDF fullImplBaseDFPaper
  cases gs.win <;> simp

theorem bucketImplDF_liftM_probComp {α : Type} (p : ProbComp α) (s₀ : BucketState Pt ℓ) :
    (simulateQ (bucketImplDF P Dh encPt encT lam qep tL par)
      (liftM p : AdversaryCompDF
        (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt) α)).run s₀ =
      (p >>= fun a => pure (a, s₀)) := by
  induction p using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t mx ih =>
    change (simulateQ (bucketImplDF P Dh encPt encT lam qep tL par)
      (query (spec := unifSpec +
        specDF (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt))
        (.inl t) >>= fun u => liftM (mx u))).run s₀ =
      ((query (spec := unifSpec) t >>= mx) >>= fun a => pure (a, s₀))
    rw [simulateQ_bind, StateT.run_bind, bind_assoc]
    change (bucketImplDF P Dh encPt encT lam qep tL par (.inl t) s₀ >>=
      fun ⟨u, s₁⟩ => (simulateQ (bucketImplDF P Dh encPt encT lam qep tL par) (liftM (mx u))).run s₁) = _
    rw [bucketImplDF_inl]; simp only [bind_assoc, pure_bind]; exact bind_congr fun u => ih u

private theorem simulateQ_fullImplBaseDFPaperBucket_simImplDF'Paper_eq_runBucketDF {α : Type}
    (oa : AdversaryCompDF (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt) α)
    (mir : Mirror (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt))
    (gsw : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt) × Option ℕ) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT (fun R => if R == Party.A then P.idA else P.idB) 25000 lam
    (simulateQ (fullImplBaseDFPaperBucket fig 1 (qep + 1) sameHdrScheme tL par)
      ((simulateQ (simImplDF'Paper (2 + 1) (qep + 1)) oa).run mir)).run gsw =
    (runBucketDF P Dh encPt encT lam qep tL par oa (mir, gsw) >>=
      fun ⟨a, mir', gsw'⟩ => pure ((a, mir'), gsw')) := by
  dsimp only [runBucketDF]
  induction oa using OracleComp.inductionOn generalizing mir gsw with
  | pure a => simp only [simulateQ_pure, StateT.run_pure, pure_bind]
  | query_bind q u ih =>
    rw [simulateQ_query_bind, simulateQ_query_bind]
    dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift, MonadLift.monadLift]
    rw [StateT.run_bind, simulateQ_bind, StateT.run_bind, StateT.run_bind, bucketImplDF_run]
    simp only [bind_assoc, pure_bind]; exact bind_congr fun ⟨⟨a, mir'⟩, gsw'⟩ => ih a mir' gsw'

theorem forgeGameBucketPaper_challSimDF'Paper_eq_runBucketDF
    (oa : AdversaryDF (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt)) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT (fun R => if R == Party.A then P.idA else P.idB) 25000 lam
    forgeGameBucketPaper fig 1 (qep + 1) sameHdrScheme tL par (challSimDF'Paper (2 + 1) (qep + 1) oa) =
    (do
      let k ← ($ᵗ (RootKey × BitVec 256) : ProbComp (RootKey × BitVec 256))
      let b ← ($ᵗ Bool : ProbComp Bool)
      let (_, _, (gs', winEp')) ← runBucketDF P Dh encPt encT lam qep tL par oa
        ({ st := fun _ => (), b := b }, (initState fig k false, none))
      return match winEp' with
        | none => false
        | some tWin => gs'.win && authLosingConditionsAvoided (2 + 1) tL tWin gs') := by
  dsimp only [forgeGameBucketPaper, challSimDF'Paper]; refine bind_congr fun k => ?_
  rw [simulateQ_bind]
  change ((StateT.lift ($ᵗ Bool : ProbComp Bool) >>= fun b =>
    simulateQ _ ((simulateQ (simImplDF'Paper (2 + 1) (qep + 1)) oa).run'
      { st := fun _ => (), b := b })).run _ >>= _) = _
  simp only [StateT.run_bind, stateT_lift_run, StateT.run'_eq, map_eq_bind_pure_comp,
    Function.comp_def, simulateQ_bind, simulateQ_pure, StateT.run_pure, bind_assoc, pure_bind]
  refine bind_congr fun b => ?_
  have hfl : ∀ x : Bool, (!x && x) = false := by intro x; cases x <;> rfl
  simp only [fullImplBaseDFPaperBucket, hfl, Bool.false_eq_true, ↓reduceIte]
  change ((simulateQ (fullImplBaseDFPaperBucket _ 1 (qep + 1) sameHdrScheme tL par)
    ((simulateQ (simImplDF'Paper (2 + 1) (qep + 1)) oa).run { st := fun _ => (), b := b })).run
      (initState _ k false, none) >>= _) = _
  rw [simulateQ_fullImplBaseDFPaperBucket_simImplDF'Paper_eq_runBucketDF]
  simp only [bind_assoc, pure_bind]
  exact bind_congr fun ⟨_, _, _, _⟩ => rfl

end BucketDefs

private theorem mem_support_simulateQ_withWinEpDF {St Msg Coins C S α : Type}
    (ctEpoch : C → ℕ) (hasWin : S → Bool)
    (impl : QueryImpl (unifSpec + specDF St Msg Coins C) (StateT S ProbComp))
    (oa : AdversaryCompDF St Msg Coins C α) (s : S) (w : Option ℕ) {a : α} {s' : S} {w' : Option ℕ}
    (h : (a, (s', w')) ∈ support ((simulateQ (withWinEpDF ctEpoch hasWin impl) oa).run (s, w))) :
    (a, s') ∈ support ((simulateQ impl oa).run s) := by
  induction oa using OracleComp.inductionOn generalizing s w with
  | pure a₀ =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h ⊢
    exact ⟨h.1, h.2.1⟩
  | query_bind q u ih =>
    rw [simulateQ_query_bind, StateT.run_bind] at h ⊢
    dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift,
      MonadLift.monadLift, withWinEpDF] at h ⊢
    simp only [StateT.run_mk, bind_assoc, pure_bind, mem_support_bind_iff] at h ⊢
    obtain ⟨⟨r, s₁⟩, h1, h2⟩ := h; exact ⟨(r, s₁), h1, ih r s₁ _ h2⟩

theorem fullImplBaseDFPaper_eq_cellT_none_zero
    {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C) (qep : ℕ) (sameHdr : C → C → Bool) (cfg : Config Msg) :
    fullImplBaseDFPaper sm (2 + 1) (qep + 1) sameHdr cfg =
      fullImplBaseDFCellTPaper sm (qep + 1) none 0 sameHdr cfg := by
  have h1 : ¬(2 ≤ 0 ∧ (none : Option ℕ) = some (0 - 2)) := by simp
  have hshift : cellShift none 0 = 0 := by unfold cellShift; simp
  rw [fullImplBaseDFCellTPaper_of_not_B1 sm (qep + 1) none 0 h1 sameHdr cfg, hshift,
    fullImplBaseDFShiftedPaper_zero_eq_fullImplBaseDFPaper]

theorem runBucketDF_inr_bind_mem_base {PQ PQC Pt β : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (lam : Pt) (qep : ℕ) (tL : Option ℕ) (par : Bool)
    (q₀ : (specDF (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt)).Domain)
    (f : (specDF (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt)).Range q₀ → β)
    (ms ms' : BucketState Pt ℓ) {b : β}
    (hy : (b, ms') ∈ support (runBucketDF P Dh encPt encT lam qep tL par
      (query (spec := unifSpec + specDF (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
        (BitVec 256) (SimFig8C Pt)) (.inr q₀) >>= fun r => pure (f r)) ms)) :
    ∃ r, b = f r ∧ ((r, ms'.1), ms'.2.1) ∈ support ((simulateQ
      (fullImplBaseDFPaper (lFig8 Dh encPt P.C P.codec ℓ encT
        (fun R => if R == Party.A then P.idA else P.idB) 25000 lam)
        (2 + 1) (qep + 1) sameHdrScheme (bucketAuthCfg 1 tL par))
      ((simOraclesDF'Paper (2 + 1) (qep + 1) q₀).run ms.1)).run ms.2.1) := by
  rcases ms with ⟨mir, gs, w⟩; rcases ms' with ⟨mir', gs', w'⟩; dsimp only [runBucketDF] at hy
  simp only [query, OracleQuery.input_query, OracleQuery.cont_query, id_map, simulateQ_bind,
    simulateQ_query, simulateQ_pure, StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
    support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hy
  obtain ⟨⟨r, mir₂, gs₂, w₂⟩, hmem, rfl, rfl, rfl, rfl⟩ := hy; rw [bucketImplDF_run] at hmem
  simp only [simImplDF'Paper, QueryImpl.add_apply_inr, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff, Prod.mk.injEq] at hmem
  obtain ⟨⟨⟨r', mir'⟩, gs', w'⟩, hmem, rfl, rfl, rfl, rfl⟩ := hmem
  exact ⟨r, rfl, mem_support_simulateQ_withWinEpDF _ _ _ _ gs w hmem⟩

private theorem gameSanInv_corrImplPaper {Pt : Type} [DecidableEq Pt] {ℓ q m : ℕ}
    {gs gs' : GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {Q : Party} {res : Option (Fig8St Pt)} (hInv : GameSanInv q (m + 1) gs)
    (hmem : (res, gs') ∈ support ((corrImplPaper (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ)
      (C := Fig8C Pt) Q).run gs)) :
    GameSanInv q m gs' ∧ ∀ fig8st, res = some fig8st → fig8st = gs.st Q := by
  have hInv0 := hInv.mono (Nat.le_succ m); unfold corrImplPaper at hmem
  by_cases hw : (gs.win || !(gs.corrAllowedPaper Q)) = true
  · simp only [hw, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩; exact ⟨hInv0, fun _ hc => nomatch hc⟩
  · simp only [hw, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_set,
      StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩; exact ⟨⟨hInv0.hm, hInv0.hparty, hInv0.hvs⟩, fun _ hc => (Option.some.inj hc).symm⟩

private theorem gameSanInv_deliverForgeBaseImpl {Pt : Type} [DecidableEq Pt] [Zero Pt]
    {ℓ q m qep : ℕ} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes} {C : Crypto}
    {codec : CryptoGames.LibsignalSession.SignalMessageProtoCodec} {encT : Pt → PublicKey}
    {idOf : Party → IdentityKey} {lam : Pt} {cfg : Config (LibsignalMsgPublicPart × Plain ℓ)}
    {gs gs' : GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {Q : Party} {c c' : Fig8C Pt} {res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ))}
    (hInv : GameSanInv q (m + 1) gs)
    (hmem : (res, gs') ∈ support ((deliverForgeBaseImpl
      (lFig8 Dh encPt C codec ℓ encT idOf 25000 lam) (2 + 1) (qep + 1) sameHdrScheme cfg (Q, c, c')).run gs)) :
    GameSanInv q m gs' := by
  have hInv0 := hInv.mono (Nat.le_succ m); unfold deliverForgeBaseImpl at hmem
  by_cases hw : gs.win = true
  · simp only [hw, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem; exact hmem.2 ▸ hInv0
  · simp only [hw, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind] at hmem
    rcases htr : gs.inTransit Q.other c with _ | r <;> simp only [htr] at hmem
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem; exact hmem.2 ▸ hInv0
    · by_cases hcnd : ((gs.inTransit Q.other c').isSome || gs.comp.contains r.pos || !(sameHdrScheme c c')) = true
      · simp only [hcnd, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        exact hmem.2 ▸ hInv0
      · simp only [hcnd, Bool.false_eq_true, ↓reduceIte] at hmem
        rcases hrcv : (lFig8 Dh encPt C codec ℓ encT idOf 25000 lam).receive (gs.st Q) c' with
          _ | ⟨st', t', i', m'⟩ <;> simp only [hrcv] at hmem
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem; exact hmem.2 ▸ hInv0
        · by_cases hqep : (decide ((qep + 1) + 1 < t') || t' != r.pos.epoch) = true
          · simp only [hqep, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            exact hmem.2 ▸ hInv0
          · simp only [hqep, Bool.false_eq_true, ↓reduceIte] at hmem
            by_cases htriv : gs.trivial (2 + 1) ⟨Q.other, t', i'⟩ = true
            · simp only [htriv, ↓reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
                support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              rcases hmem with ⟨_, rfl⟩; obtain ⟨hvS_eq, _⟩ := lFig8_receive_vS_and_idx hrcv
              have hm1 : m + 1 ≤ q := hInv.hm; refine ⟨hInv0.hm, fun R => ?_, fun R vs hv => ?_⟩
              · dsimp only [GameState.accept, GameState.delete]; by_cases hR : R = Q
                · subst hR; simp only [Function.update_self]; exact (fig8PartyInv_receive (hInv.hparty R) hrcv).mono (by omega)
                · simp only [Function.update_of_ne hR]; exact hInv0.hparty R
              · dsimp only [GameState.accept, GameState.delete] at hv; by_cases hR : R = Q
                · subst hR; simp only [Function.update_self, hvS_eq] at hv; exact hInv0.hvs R vs hv
                · simp only [Function.update_of_ne hR] at hv; exact hInv0.hvs R vs hv
            · simp only [htriv, Bool.false_eq_true, ↓reduceIte] at hmem
              split_ifs at hmem <;>
                simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
                  support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem <;>
                (rcases hmem with ⟨_, rfl⟩; exact ⟨hInv0.hm, hInv0.hparty, hInv0.hvs⟩)

section BaseBucketHookInv
variable {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ q m qep : ℕ} {tL : Option ℕ} {par : Bool}
  (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt)

theorem runBucketDF_transmitQueryDF_inv (Q : Party) (msg : LibsignalMsgPublicPart × Plain ℓ)
    (rc : Option (BitVec 256)) (ms ms' : BucketState Pt ℓ) (res : Option (Fig8C Pt))
    (hInv : GameSanInv q (m + 1) ms.2.1)
    (hy : (res, ms') ∈ support (runBucketDF P Dh encPt encT lam qep tL par (transmitQueryDF Q msg rc) ms)) :
    GameSanInv q m ms'.2.1 ∧ ∀ c, res = some c → c.2.1 ≤ q - m := by
  have hy' := hy; rw [← bind_pure (transmitQueryDF Q msg rc)] at hy'; dsimp only [transmitQueryDF] at hy'
  obtain ⟨_, rfl, hmem⟩ := runBucketDF_inr_bind_mem_base P Dh encPt encT lam qep tL par _ _ ms ms' hy'
  simp only [simOraclesDF'Paper, QueryImpl.add_apply_inl] at hmem
  unfold simTransmitDF'Paper transmitQueryDF fullImplBaseDFPaper oracleImplBaseDFPaper oracleImplPaper at hmem
  simp only [StateT.run_bind, StateT.run_get, stateT_lift_run, query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map, simulateQ_bind, simulateQ_query, QueryImpl.add_apply_inl,
    QueryImpl.add_apply_inr, pure_bind, bind_assoc, mem_support_bind_iff] at hmem
  obtain ⟨⟨res₁, gs₁⟩, hbase, h2⟩ := hmem
  have hgs : res = res₁ ∧ ms'.2.1 = gs₁ := by
    rcases res₁ with _ | c
    · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h2
      exact ⟨h2.1.1, h2.2⟩
    · rcases hep : ms.1.epMgmt (2 + 1) (qep + 1) Q false with _ | s₁ <;>
        simp only [hep, StateT.run_bind, StateT.run_set, StateT.run_pure, simulateQ_pure,
          pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h2 <;> exact ⟨h2.1.1, h2.2⟩
  rw [hgs.1, hgs.2]; exact gameSanInv_transmitImpl hInv hbase

theorem runBucketDF_challQueryDF_inv (Q : Party) (m₀ m₁ : LibsignalMsgPublicPart × Plain ℓ)
    (rc : Option (BitVec 256)) (ms ms' : BucketState Pt ℓ) (res : Option (Fig8C Pt))
    (hInv : GameSanInv q (m + 1) ms.2.1)
    (hy : (res, ms') ∈ support (runBucketDF P Dh encPt encT lam qep tL par (challQueryDF Q m₀ m₁ rc) ms)) :
    GameSanInv q m ms'.2.1 ∧ ∀ c, res = some c → c.2.1 ≤ q - m := by
  have hy' := hy; rw [← bind_pure (challQueryDF Q m₀ m₁ rc)] at hy'; dsimp only [challQueryDF] at hy'
  obtain ⟨_, rfl, hmem⟩ := runBucketDF_inr_bind_mem_base P Dh encPt encT lam qep tL par _ _ ms ms' hy'
  simp only [simOraclesDF'Paper, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr] at hmem
  unfold simChallDF'Paper transmitQueryDF fullImplBaseDFPaper oracleImplBaseDFPaper oracleImplPaper at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  rcases hep : ms.1.epMgmt (2 + 1) (qep + 1) Q false with _ | s₁ <;> simp only [hep] at hmem
  · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨⟨rfl, -⟩, hms⟩; rw [hms]; exact ⟨hInv.mono (Nat.le_succ m), fun _ hc => nomatch hc⟩
  · cases hsc : s₁.safeCh (2 + 1) Q <;> simp only [hsc] at hmem
    · simp only [Bool.not_false, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨⟨rfl, -⟩, hms⟩; rw [hms]; exact ⟨hInv.mono (Nat.le_succ m), fun _ hc => nomatch hc⟩
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, stateT_lift_run,
        query, OracleQuery.input_query, OracleQuery.cont_query, id_map, simulateQ_bind,
        simulateQ_query, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, bind_assoc, pure_bind,
        mem_support_bind_iff] at hmem
      obtain ⟨⟨res₁, gs₁⟩, hbase, h2⟩ := hmem
      have hgs : res = res₁ ∧ ms'.2.1 = gs₁ := by
        rcases res₁ with _ | c <;>
          simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, simulateQ_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h2 <;> exact ⟨h2.1.1, h2.2⟩
      rw [hgs.1, hgs.2]; exact gameSanInv_transmitImpl hInv hbase

private theorem runBucketDF_onDl_inv [SampleableType PQC] (Q : Party) (c : Fig8C Pt) (ex ex' : List (Fig8C Pt))
    (ms ms' : BucketState Pt ℓ) (res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)))
    (hInv : GameSanInv q (m + 1) ms.2.1)
    (hy : ((res, ex'), ms') ∈ support (runBucketDF P Dh encPt encT lam qep tL par
      ((deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)).onDl Q c ex) ms)) :
    GameSanInv q m ms'.2.1 ∧ ∀ t i pm, res = some (.accepted t i pm) → i = c.2.1 := by
  dsimp only [deliverForgeSemHook, deliverQueryDF] at hy
  obtain ⟨_, hbf, hmem⟩ := runBucketDF_inr_bind_mem_base P Dh encPt encT lam qep tL par _ _ ms ms' hy
  rcases Prod.mk.inj hbf with ⟨rfl, -⟩
  simp only [simOraclesDF'Paper, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr] at hmem
  unfold simDeliverDF deliverQueryDF fullImplBaseDFPaper oracleImplBaseDFPaper oracleImplPaper at hmem
  simp only [StateT.run_bind, StateT.run_get, stateT_lift_run, query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map, simulateQ_bind, simulateQ_query, QueryImpl.add_apply_inl,
    QueryImpl.add_apply_inr, pure_bind, bind_assoc, mem_support_bind_iff] at hmem
  obtain ⟨⟨res₁, gs₁⟩, hbase, h2⟩ := hmem; obtain ⟨hfg', hacc⟩ := gameSanInv_deliverImpl hInv hbase
  have hgs : ms'.2.1 = gs₁ ∧ (∀ t i pm, res = some (.accepted t i pm) →
      ∃ pm', res₁ = some (.accepted t i pm')) := by
    rcases res₁ with _ | (_ | ⟨t', i', pm'⟩)
    · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h2
      exact ⟨h2.2, fun _ _ _ hc => by rw [h2.1.1] at hc; cases hc⟩
    · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h2
      exact ⟨h2.2, fun _ _ _ hc => by rw [h2.1.1] at hc; cases hc⟩
    · rcases htr : ms.1.inTransit Q.other c with _ | r <;>
        simp only [htr, StateT.run_bind, StateT.run_set, StateT.run_pure, simulateQ_pure,
          pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h2 <;>
        exact ⟨h2.2, fun t i pm hc => by rw [h2.1.1] at hc; cases hc; exact ⟨pm', rfl⟩⟩
  rw [hgs.1]; exact ⟨hfg', fun t i pm hc => by obtain ⟨pm', h1⟩ := hgs.2 t i pm hc; exact hacc t i pm' h1⟩

private theorem runBucketDF_onIj_inv [SampleableType PQC] (Q : Party) (c : Fig8C Pt) (ex ex' : List (Fig8C Pt))
    (ms ms' : BucketState Pt ℓ) (res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)))
    (hInv : GameSanInv q (m + 1) ms.2.1)
    (hy : ((res, ex'), ms') ∈ support (runBucketDF P Dh encPt encT lam qep tL par
      ((deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)).onIj Q c ex) ms)) :
    GameSanInv q m ms'.2.1 ∧ ∀ t i pm, res = some (.accepted t i pm) → i = c.2.1 := by
  dsimp only [deliverForgeSemHook, injectQueryDF] at hy
  obtain ⟨_, hbf, hmem⟩ := runBucketDF_inr_bind_mem_base P Dh encPt encT lam qep tL par _ _ ms ms' hy
  rcases Prod.mk.inj hbf with ⟨rfl, -⟩
  simp only [simOraclesDF'Paper, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr] at hmem
  unfold simInjectDF injectQueryDF fullImplBaseDFPaper oracleImplBaseDFPaper oracleImplPaper at hmem
  simp only [StateT.run_bind, StateT.run_get, stateT_lift_run, query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map, simulateQ_bind, simulateQ_query, QueryImpl.add_apply_inl,
    QueryImpl.add_apply_inr, pure_bind, bind_assoc, mem_support_bind_iff] at hmem
  obtain ⟨⟨res₁, gs₁⟩, hbase, h2⟩ := hmem
  have hgs : res = res₁ ∧ ms'.2.1 = gs₁ := by
    rcases res₁ with _ | (_ | ⟨t', i', pm'⟩) <;>
      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, simulateQ_pure, pure_bind,
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h2 <;> exact ⟨h2.1.1, h2.2⟩
  rw [hgs.1, hgs.2]; exact gameSanInv_injectImpl hInv hbase

theorem runBucketDF_onCr_inv [SampleableType PQC] (Q : Party) (ex ex' : List (Fig8C Pt))
    (ms ms' : BucketState Pt ℓ) (res : Option (Fig8St Pt)) (hInv : GameSanInv q (m + 1) ms.2.1)
    (hy : ((res, ex'), ms') ∈ support (runBucketDF P Dh encPt encT lam qep tL par
      ((deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)).onCr Q ex) ms)) :
    GameSanInv q m ms'.2.1 ∧ ∀ fig8st, res = some fig8st → fig8st = ms.2.1.st Q := by
  dsimp only [deliverForgeSemHook, corrQueryDF] at hy
  obtain ⟨_, hbf, hmem⟩ := runBucketDF_inr_bind_mem_base P Dh encPt encT lam qep tL par _ _ ms ms' hy
  rcases Prod.mk.inj hbf with ⟨rfl, -⟩
  simp only [simOraclesDF'Paper, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr] at hmem
  unfold simCorrDFPaper corrQueryDF fullImplBaseDFPaper oracleImplBaseDFPaper oracleImplPaper at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  cases hca : ms.1.corrAllowedPaper Q <;> simp only [hca] at hmem
  · simp only [Bool.not_false, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨⟨rfl, -⟩, hms⟩; rw [hms]; exact ⟨hInv.mono (Nat.le_succ m), fun _ hc => nomatch hc⟩
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, stateT_lift_run,
      query, OracleQuery.input_query, OracleQuery.cont_query, id_map, simulateQ_bind,
      simulateQ_query, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, bind_assoc, pure_bind,
      mem_support_bind_iff] at hmem
    obtain ⟨⟨res₁, gs₁⟩, hbase, h2⟩ := hmem
    have hgs : res = res₁ ∧ ms'.2.1 = gs₁ := by
      rcases res₁ with _ | st' <;>
        simp only [Option.isSome, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
          StateT.run_pure, simulateQ_pure, pure_bind, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at h2 <;> exact ⟨h2.1.1, h2.2⟩
    rw [hgs.1, hgs.2]; exact gameSanInv_corrImplPaper hInv hbase

private theorem runBucketDF_onProbe_inv [SampleableType PQC] (Q : Party) (c' : Fig8C Pt)
    (ex ex' : List (Fig8C Pt)) (ms ms' : BucketState Pt ℓ) (hInv : GameSanInv q (m + 1) ms.2.1)
    (hy : (ex', ms') ∈ support (runBucketDF P Dh encPt encT lam qep tL par
      ((deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)).onProbe Q c' ex) ms)) :
    GameSanInv q m ms'.2.1 := by
  dsimp only [deliverForgeSemHook] at hy
  rcases hfind : ex.find? (fun c => sameWireFig8 c c') with _ | c <;> simp only [hfind] at hy
  · simp only [runBucketDF, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hy; rcases hy with ⟨_, rfl⟩; exact hInv.mono (Nat.le_succ m)
  · dsimp only [deliverForgeQuery] at hy
    obtain ⟨_, -, hmem⟩ := runBucketDF_inr_bind_mem_base P Dh encPt encT lam qep tL par _ _ ms ms' hy
    simp only [simOraclesDF'Paper, QueryImpl.add_apply_inr] at hmem
    unfold simDeliverForgeDF deliverForgeQuery fullImplBaseDFPaper oracleImplBaseDFPaper oracleImplPaper at hmem
    simp only [StateT.run_bind, StateT.run_get, stateT_lift_run, query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, simulateQ_bind, simulateQ_query, QueryImpl.add_apply_inr,
      pure_bind, bind_assoc, mem_support_bind_iff] at hmem
    obtain ⟨⟨res₁, gs₁⟩, hbase, h2⟩ := hmem
    have hgs : ms'.2.1 = gs₁ := by
      rcases res₁ with _ | (_ | ⟨t', i', pm'⟩) <;>
        simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, simulateQ_pure, pure_bind,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h2 <;> exact h2.2
    rw [hgs]; exact gameSanInv_deliverForgeBaseImpl hInv hbase

end BaseBucketHookInv

structure DFBucketSanInv {PQ Pt : Type} {ℓ : ℕ} (q m : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ms : BucketState Pt ℓ) : Prop where
  hgame : GameSanInv q m ms.2.1
  hkept : ∀ R : Party, KeptInv (25000 * (q - m)) (sC.kept R)
  hchains : ∀ R : Party, ∀ g ∈ sC.base.chains R, g.last ≤ 25001 * (q - m)
  hhonest : ∀ wc ∈ sC.base.honest, wc.2.2.1 ≤ q - m

theorem DFBucketSanInv.mono {PQ Pt : Type} {ℓ q m₁ m₂ : ℕ}
    {sC : LibsignalToModularSchemeSimState PQ Pt ℓ} {ms : BucketState Pt ℓ}
    (hle : m₁ ≤ m₂) (h : DFBucketSanInv q m₂ sC ms) : DFBucketSanInv q m₁ sC ms :=
  ⟨h.hgame.mono hle, fun R => (h.hkept R).mono (Nat.mul_le_mul_left 25000 (by omega)),
    fun R g hg => (h.hchains R g hg).trans (Nat.mul_le_mul_left 25001 (by omega)),
    fun wc hwc => (h.hhonest wc hwc).trans (by omega)⟩

theorem dfBucketSanInv_init {PQ PQC Pt : Type} [Zero Pt] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (lam : Pt) (q : ℕ) (k : RootKey × BitVec 256)
    (pqrKey : BitVec 256) (b mirB : Bool) (w₀ : Option ℕ) :
    DFBucketSanInv (PQ := PQ) (Pt := Pt) (ℓ := ℓ) q q
      (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey))
      ({ st := fun _ => (), b := mirB },
        (initState (lFig8 Dh encPt P.C P.codec ℓ encT
          (fun R => if R == Party.A then P.idA else P.idB) 25000 lam) k b, w₀)) where
  hgame := gameSanInv_init Dh encPt P.C P.codec encT
    (fun R => if R == Party.A then P.idA else P.idB) lam q k b
  hkept _ := by simp only [Nat.sub_self, Nat.mul_zero, initSimC]; exact keptInv_unknown 0
  hchains R g hg := by cases R <;> simp [initSimC, initSim] at hg ⊢; subst hg; rfl
  hhonest _ hwc := nomatch hwc

private theorem modify_mem_inv {α : Type} {Pred : α → Prop} {cs : List α} {ci : ℕ} {f : α → α}
    (hcs : ∀ x ∈ cs, Pred x) (hf : ∀ x, Pred x → Pred (f x)) : ∀ y ∈ cs.modify ci f, Pred y := by
  induction cs generalizing ci with
  | nil => intro _ hy; simp at hy
  | cons a xs ih =>
    cases ci <;> (intro y hy; dsimp only [List.modify] at hy; rcases List.mem_cons.mp hy with rfl | hy)
    · exact hf _ (hcs _ (List.mem_cons_self ..))
    · exact hcs y (List.mem_cons_of_mem _ hy)
    · exact hcs _ (List.mem_cons_self ..)
    · exact ih (fun x hx => hcs x (List.mem_cons_of_mem _ hx)) y hy

private theorem onAcceptPure_last_le {PQ Pt : Type} {ℓ M : ℕ} (qep : ℕ) (Q : Party) (w : Bytes)
    (isDel : Bool) (t i : ℕ) (m : Plain ℓ) (ci? : Option ℕ) (Tpk : PublicKey) (pq' : PQ)
    (s : SimState PQ Pt ℓ) (hs : ∀ R, ∀ g ∈ s.chains R, g.last ≤ M) (hi : i ≤ M) :
    ∀ R, ∀ g ∈ (onAcceptPure qep Q w isDel t i m ci? Tpk pq' s).2.chains R, g.last ≤ M := by
  have hacc : ∀ {g : GhostChain}, g.last ≤ M → (g.accept i).last ≤ M := by
    intro g hg; unfold GhostChain.accept; split_ifs <;> assumption
  let cs' : List GhostChain := match ci? with
    | some ci => (s.chains Q).modify ci (·.accept i)
    | none => pushChain (s.chains Q)
        (GhostChain.accept { key := some Tpk, epoch := t, last := 0, skipped := [] } i)
  have hcs : ∀ g ∈ cs', g.last ≤ M := by
    rcases ci? with _ | ci
    · intro g hgm; rcases List.mem_append.mp (List.mem_of_mem_drop hgm) with hm | hm
      · exact hs Q g hm
      · rw [List.mem_singleton.mp hm]; exact hacc (Nat.zero_le M)
    · exact modify_mem_inv (hs Q) (fun _ hg => hacc hg)
  have hu : ∀ R, ∀ g ∈ Function.update s.chains Q cs' R, g.last ≤ M := fun R => by
    by_cases hR : R = Q
    · subst hR; simpa using hcs
    · simpa [Function.update_of_ne hR] using hs R
  unfold onAcceptPure; cases isDel
  · simp only [Bool.false_eq_true, ↓reduceIte]; split_ifs <;> first | exact hs | exact hu
  · simp only [↓reduceIte]; rcases s.mir.inTransit Q.other w with _ | _ <;> first | exact hs | exact hu

private theorem onAnswerPure_last_le {PQ Pt : Type} {ℓ M : ℕ} (qep : ℕ) (Q : Party) (w : Bytes)
    (isDel : Bool) (ci? : Option ℕ) (Tpk : PublicKey) (pq' : PQ)
    (res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ))) (s : SimState PQ Pt ℓ)
    (hs : ∀ R, ∀ g ∈ s.chains R, g.last ≤ M)
    (hres : ∀ t i pm, res = some (.accepted t i pm) → i ≤ M) :
    ∀ R, ∀ g ∈ (onAnswerPure qep Q w isDel ci? Tpk pq' res s).2.chains R, g.last ≤ M := by
  rcases res with _ | (_ | ⟨t, i, pm⟩)
  · exact hs
  · exact hs
  · exact onAcceptPure_last_le qep Q w isDel t i ((pm.map (·.2)).getD default) ci? Tpk pq' s hs
      (hres t i pm rfl)

private theorem getD_mem_of_findIdx?_eq_some {α : Type} {p : α → Bool} {cs : List α} {ci : ℕ}
    (d : α) (h : cs.findIdx? p = some ci) : cs.getD ci d ∈ cs := by
  induction cs generalizing ci with
  | nil => simp at h
  | cons a xs ih =>
    rw [List.findIdx?_cons] at h; by_cases ha : p a = true
    · simp only [ha, ↓reduceIte, Option.some.injEq] at h; subst h; simp [List.getD]
    · simp only [ha, Bool.false_eq_true, ↓reduceIte, Option.map_eq_some_iff] at h
      obtain ⟨j, hj, rfl⟩ := h; exact List.mem_cons_of_mem a (ih hj)

private theorem rejects_false_le {g : GhostChain} {i : ℕ} (h : g.rejects i = false) :
    i ≤ g.last + 25001 := by
  unfold GhostChain.rejects at h; by_cases hle : i ≤ g.last
  · omega
  · simp only [hle, ↓reduceIte, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h; omega

section HookBucketSanInv

variable {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType PQC]
  {ℓ q m qep : ℕ} {tL : Option ℕ} {par : Bool}
  (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
  (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt)

private theorem runBucketDF_semDrawSendCoins {α : Type} (r : Option PQC)
    (k : PQC × Option (BitVec 256) →
      AdversaryCompDF (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt) α)
    (ms : BucketState Pt ℓ) {x : α × BucketState Pt ℓ}
    (hx : x ∈ support (runBucketDF P Dh encPt encT lam qep tL par
      (semDrawSendCoins (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)) r >>= k) ms)) :
    ∃ rq rc, x ∈ support (runBucketDF P Dh encPt encT lam qep tL par (k (rq, rc)) ms) := by
  cases r <;>
    (dsimp only [semDrawSendCoins, deliverForgeSemHook, runBucketDF] at hx ⊢;
     simp only [bind_assoc, pure_bind, simulateQ_bind, StateT.run_bind,
       bucketImplDF_liftM_probComp, mem_support_bind_iff] at hx;
     obtain ⟨c, -, hx⟩ := hx; exact ⟨_, _, hx⟩)

private theorem semSendHook_bucket_dfSanInv
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (Fig8C Pt)) (ms : BucketState Pt ℓ)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC)
    (hInv : DFBucketSanInv q (m + 1) sC ms) :
    ∀ x ∈ support (runBucketDF P Dh encPt encT lam qep tL par
        (semSendHook P Dh encPt encT lam (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)) qep sC ex Q m₀ chal r) ms),
      DFBucketSanInv q m x.1.2.1 x.2 := by
  rintro ⟨⟨out₁, sC₁, ex₁⟩, ms₁⟩ hx; have hm1 : m + 1 ≤ q := hInv.hgame.hm; have hInv0 := hInv.mono (Nat.le_succ m)
  unfold semSendHook at hx
  by_cases href : (sC.base.stopped || sC.base.mir.win || !noBobSendInEpoch0 sC.base.mir Q) = true
  · simp only [href, ↓reduceIte, runBucketDF, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact hInv0
  · simp only [href, Bool.false_eq_true, ↓reduceIte] at hx
    rcases hep : sC.base.mir.epMgmt 3 qep Q r.isSome with _ | s₁ <;> simp only [hep] at hx
    · simp only [runBucketDF, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
      rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact hInv0
    · by_cases hch : (chal.isSome && !s₁.safeCh 3 Q) = true
      · simp only [hch, ↓reduceIte, runBucketDF, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
        rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact hInv0
      · simp only [hch, Bool.false_eq_true, ↓reduceIte] at hx
        obtain ⟨rq, rc, hx⟩ := runBucketDF_semDrawSendCoins P Dh encPt encT lam r _ ms hx
        change _ ∈ support (runBucketDF P Dh encPt encT lam qep tL par (pure (ex, ex) >>= _) ms) at hx; rw [pure_bind] at hx
        rcases hmk : mkPub P sC.base Q rq (if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1) else sC.base.pn Q) with _ | ⟨pq', pub⟩ <;> simp only [hmk] at hx
        · simp only [runBucketDF, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
          rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact hInv0
        · have hpost : ∀ (c : Fig8C Pt), GameSanInv q m ms₁.2.1 → c.2.1 ≤ q - m →
              sC₁ = scPostSendPure P Dh encPt encT lam sC s₁ Q m₀ chal.isSome pq'
                (if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1) else sC.base.pn Q) c →
              DFBucketSanInv q m sC₁ ms₁ := by
            intro c hg' hc hsC₁; subst hsC₁; refine ⟨hg', ?_, hInv0.hchains, ?_⟩
            · intro R; unfold scPostSendPure; by_cases hR : R = Q
              · subst hR; simp only [Function.update_self]; exact (keptInv_send (hInv.hkept R)).mono (Nat.mul_le_mul_left 25000 (by omega))
              · simp only [Function.update_of_ne hR]; exact hInv0.hkept R
            · intro wc hwc; unfold scPostSendPure at hwc; rcases List.mem_cons.mp hwc with rfl | hwc
              · exact hc
              · exact hInv0.hhonest wc hwc
          cases chal with
          | none =>
            dsimp only [deliverForgeSemHook] at hx
            simp only [runBucketDF, simulateQ_bind, StateT.run_bind, bind_assoc, pure_bind, mem_support_bind_iff] at hx
            obtain ⟨⟨res, ms'⟩, htr, hEq⟩ := hx
            obtain ⟨hg', hc⟩ := runBucketDF_transmitQueryDF_inv P Dh encPt encT lam Q (pub, m₀) rc ms ms' res hInv.hgame htr
            rcases res with _ | c <;> simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hEq
            · rcases hEq with ⟨⟨_, rfl, _⟩, rfl⟩; exact ⟨hg', hInv0.hkept, hInv0.hchains, hInv0.hhonest⟩
            · rcases hEq with ⟨⟨_, hsC₁, _⟩, rfl⟩; exact hpost c hg' (hc c rfl) hsC₁
          | some m₁ =>
            dsimp only [deliverForgeSemHook] at hx
            simp only [runBucketDF, simulateQ_bind, StateT.run_bind, bind_assoc, pure_bind, mem_support_bind_iff] at hx
            obtain ⟨⟨res, ms'⟩, hch', hEq⟩ := hx
            obtain ⟨hg', hc⟩ := runBucketDF_challQueryDF_inv P Dh encPt encT lam Q (pub, m₀) (pub, m₁) rc ms ms' res hInv.hgame hch'
            rcases res with _ | c <;> simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hEq
            · rcases hEq with ⟨⟨_, rfl, _⟩, rfl⟩; exact ⟨hg', hInv0.hkept, hInv0.hchains, hInv0.hhonest⟩
            · rcases hEq with ⟨⟨_, hsC₁, _⟩, rfl⟩; exact hpost c hg' (hc c rfl) hsC₁

private theorem semFwdAnswerHook_bucket_dfSanInv (ms : BucketState Pt ℓ) (Q : Party) (w : Bytes)
    (isDel : Bool) (hg : GameSanInv q (m + 1) ms.2.1)
    (sC' : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (Fig8C Pt))
    (ci? : Option ℕ) (Tpk : PublicKey) (pq' : PQ) (c' : SimFig8C Pt)
    (hk' : ∀ R, KeptInv (25000 * (q - (m + 1))) (sC'.kept R))
    (hch' : ∀ R, ∀ g ∈ sC'.base.chains R, g.last ≤ 25001 * (q - m))
    (hhon' : ∀ wc ∈ sC'.base.honest, wc.2.2.1 ≤ q - m) (hc' : c'.2.1 ≤ 25001 * (q - m)) :
    ∀ x ∈ support (runBucketDF P Dh encPt encT lam qep tL par
        (semFwdAnswerHook P Dh encPt encT lam (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)) qep sC' ex Q w isDel ci? Tpk pq' c') ms),
      DFBucketSanInv q m x.1.2.1 x.2 := by
  rintro ⟨⟨_, sC₁, _⟩, ms₁⟩ hx
  let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  have hm1 : m + 1 ≤ q := hg.hm; have hsubK : 25000 * (q - (m + 1)) + 25000 = 25000 * (q - m) := by omega
  unfold semFwdAnswerHook at hx; dsimp only at hx
  have hfin : ∀ (res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ))),
      GameSanInv q m ms₁.2.1 → (∀ t i pm, res = some (.accepted t i pm) → i = c'.2.1) →
      sC₁ = { (match res with
         | some (.accepted _ _ _) => { sC' with kept := Function.update sC'.kept Q (Kept.recv (fig := fig) (fs := lFS P.C P.codec ℓ encT idOf 25000) c' (sC'.kept Q)) }
         | _ => sC') with base := (onAnswerPure qep Q w isDel ci? Tpk pq' res sC'.base).2 } →
      DFBucketSanInv q m sC₁ ms₁ := by
    intro res hg' hi_eq hsC₁; subst hsC₁
    have hhon_oa : ∀ wc ∈ (onAnswerPure qep Q w isDel ci? Tpk pq' res sC'.base).2.honest, wc.2.2.1 ≤ q - m := by
      rcases res with _ | (_ | ⟨t, i, pm⟩)
      · exact hhon'
      · exact hhon'
      · dsimp only [onAnswerPure, onAcceptPure]; cases isDel
        · simp only [Bool.false_eq_true, ↓reduceIte]; split_ifs <;> exact hhon'
        · simp only [↓reduceIte]; rcases sC'.base.mir.inTransit Q.other w with _ | _ <;> exact hhon'
    refine ⟨hg', ?_, onAnswerPure_last_le qep Q w isDel ci? Tpk pq' res sC'.base hch' (fun t i pm hr => (hi_eq t i pm hr) ▸ hc'), hhon_oa⟩
    rcases res with _ | (_ | ⟨t, i, pm⟩)
    · exact fun R => (hk' R).mono (Nat.mul_le_mul_left 25000 (by omega))
    · exact fun R => (hk' R).mono (Nat.mul_le_mul_left 25000 (by omega))
    · intro R; by_cases hR : R = Q
      · subst hR; change KeptInv _ (Function.update sC'.kept R _ R); rw [Function.update_self]; exact hsubK ▸ keptInv_recv (hk' R)
      · change KeptInv _ (Function.update sC'.kept Q _ R); rw [Function.update_of_ne hR]; exact (hk' R).mono (Nat.mul_le_mul_left 25000 (by omega))
  by_cases hinT : (sC'.base.honest.any fun wc => decide (wc.2 = c') && (sC'.base.mir.inTransit Q.other wc.1).isSome) = true
  · simp only [hinT, ↓reduceIte, runBucketDF, simulateQ_bind, StateT.run_bind, mem_support_bind_iff, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    obtain ⟨⟨⟨res, ex₂⟩, ms'⟩, hdl, ⟨_, hsC₁, _⟩, rfl⟩ := hx
    obtain ⟨hg', hi_eq⟩ := runBucketDF_onDl_inv P Dh encPt encT lam Q c' ex ex₂ ms ms₁ res hg hdl; exact hfin res hg' hi_eq hsC₁
  · simp only [hinT, Bool.false_eq_true, ↓reduceIte, runBucketDF, simulateQ_bind, StateT.run_bind, mem_support_bind_iff, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    obtain ⟨⟨⟨res, ex₂⟩, ms'⟩, hij, ⟨_, hsC₁, _⟩, rfl⟩ := hx
    obtain ⟨hg', hi_eq⟩ := runBucketDF_onIj_inv P Dh encPt encT lam Q c' ex ex₂ ms ms₁ res hg hij; exact hfin res hg' hi_eq hsC₁

private theorem semResyncHook_bucket_dfSanInv (ms : BucketState Pt ℓ) (Q : Party) (w : Bytes)
    (hg : GameSanInv q (m + 1) ms.2.1) (sC' : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (ex : List (Fig8C Pt)) (ci? : Option ℕ) (Tpk : PublicKey) (pq' : PQ) (c : SimFig8C Pt)
    (r : Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ)))
    (hk' : ∀ R, KeptInv (25000 * (q - (m + 1))) (sC'.kept R))
    (hch' : ∀ R, ∀ g ∈ sC'.base.chains R, g.last ≤ 25001 * (q - m))
    (hhon' : ∀ wc ∈ sC'.base.honest, wc.2.2.1 ≤ q - m)
    (hr_le : ∀ t_r i_r pm, r = some (t_r, i_r, pm) → i_r ≤ 25001 * (q - m)) :
    ∀ x ∈ support (runBucketDF P Dh encPt encT lam qep tL par
        (semResyncHook P Dh encPt encT lam (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)) qep sC' ex Q w ci? Tpk pq' c r) ms),
      DFBucketSanInv q m x.1.2.1 x.2 := by
  rintro ⟨⟨_, sC₁, _⟩, ms₁⟩ hx; have hm1 : m + 1 ≤ q := hg.hm; have hsubK : 25000 * (q - (m + 1)) + 25000 = 25000 * (q - m) := by omega
  unfold semResyncHook at hx; rcases r with _ | ⟨t_r, i_r, pub_r, m_r⟩
  · simp only [runBucketDF, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact ⟨hg.mono (Nat.le_succ m), fun R => (hk' R).mono (Nat.mul_le_mul_left 25000 (by omega)), hch', hhon'⟩
  · simp only [runBucketDF, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hx
    obtain ⟨⟨⟨res, ex₂⟩, ms'⟩, hdl, hx⟩ := hx; obtain ⟨hg', -⟩ := runBucketDF_onDl_inv P Dh encPt encT lam Q c ex ex₂ ms ms' res hg hdl
    rcases res with _ | (_ | ⟨t', i', pm'⟩) <;> simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    · rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact ⟨hg', fun R => (hk' R).mono (Nat.mul_le_mul_left 25000 (by omega)), hch', hhon'⟩
    · rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact ⟨hg', fun R => (hk' R).mono (Nat.mul_le_mul_left 25000 (by omega)), hch', hhon'⟩
    · rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩
      have hhon_oa : ∀ wc ∈ (onAcceptPure qep Q w true t_r i_r m_r ci? Tpk pq' sC'.base).2.honest, wc.2.2.1 ≤ q - m := by
        dsimp only [onAcceptPure]; rcases sC'.base.mir.inTransit Q.other w with _ | _ <;> exact hhon'
      refine ⟨hg', ?_, onAcceptPure_last_le qep Q w true t_r i_r m_r ci? Tpk pq' sC'.base hch' (hr_le t_r i_r (pub_r, m_r) rfl), hhon_oa⟩
      intro R; dsimp only; by_cases hR : R = Q
      · subst hR; simp only [Function.update_self]; exact hsubK ▸ keptInv_recv (hk' R)
      · simp only [Function.update_of_ne hR]; exact (hk' R).mono (Nat.mul_le_mul_left 25000 (by omega))

private theorem semFwdHook_bucket_dfSanInv (B : ℕ) (ms : BucketState Pt ℓ) (Q : Party) (w : Bytes)
    (isDel : Bool) (hg : GameSanInv q (m + 1) ms.2.1)
    (sC' : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (Fig8C Pt))
    (ci? : Option ℕ) (Tpk : PublicKey) (pq' : PQ) (hc : Option (SimFig8C Pt)) (c' : SimFig8C Pt)
    (hk' : ∀ R, KeptInv (25000 * (q - (m + 1))) (sC'.kept R))
    (hch' : ∀ R, ∀ g ∈ sC'.base.chains R, g.last ≤ 25001 * (q - m))
    (hhon' : ∀ wc ∈ sC'.base.honest, wc.2.2.1 ≤ q - m) (hc' : c'.2.1 ≤ 25001 * (q - m)) :
    ∀ x ∈ support (runBucketDF P Dh encPt encT lam qep tL par
        (semFwdHook P Dh encPt encT lam (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ))
          qep B sC' ex Q w isDel ci? Tpk pq' hc c') ms),
      DFBucketSanInv q m x.1.2.1 x.2 := by
  intro x hx; have hm1 : m + 1 ≤ q := hg.hm; unfold semFwdHook at hx; rcases hc with _ | c
  · exact semFwdAnswerHook_bucket_dfSanInv P Dh encPt encT lam ms Q w isDel hg
      sC' ex ci? Tpk pq' c' hk' hch' hhon' hc' x hx
  · dsimp only at hx; split at hx
    · rcases hev : evalCKClamp P Dh encPt encT lam B sC' Q w c c' with _ | r <;> simp only [hev] at hx
      · rcases x with ⟨⟨_, sC₁, _⟩, ms₁⟩
        simp only [runBucketDF, simulateQ_bind, StateT.run_bind, mem_support_bind_iff,
          simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
        obtain ⟨⟨ex₂, ms'⟩, hpr, ⟨_, rfl, _⟩, rfl⟩ := hx
        exact ⟨runBucketDF_onProbe_inv P Dh encPt encT lam Q c' ex ex₂ ms ms₁ hg hpr,
          fun R => (hk' R).mono (Nat.mul_le_mul_left 25000 (by omega)), hch', hhon'⟩
      · exact semResyncHook_bucket_dfSanInv P Dh encPt encT lam ms Q w hg sC' ex ci? Tpk pq' c r hk' hch'
          hhon' (fun t_r i_r pm hr =>
            (evalCKClamp_index_le P Dh encPt encT lam sC' Q w c c' (hr ▸ hev)).trans hc') x hx
    · exact semFwdAnswerHook_bucket_dfSanInv P Dh encPt encT lam ms Q w isDel hg
        sC' ex ci? Tpk pq' c' hk' hch' hhon' hc' x hx

theorem semRecvHook_bucket_dfSanInv (decT : PublicKey → Option Pt) (B : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (Fig8C Pt)) (ms : BucketState Pt ℓ)
    (Q : Party) (w : Bytes) (isDel : Bool) (hInv : DFBucketSanInv q (m + 1) sC ms) :
    ∀ x ∈ support (runBucketDF P Dh encPt encT lam qep tL par
        (semRecvHook P Dh encPt encT decT lam
          (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)) qep B sC ex Q w isDel) ms),
      DFBucketSanInv q m x.1.2.1 x.2 := by
  rintro ⟨⟨_, sC₁, _⟩, ms₁⟩ hx
  have hm1 : m + 1 ≤ q := hInv.hgame.hm; have hInv0 := hInv.mono (Nat.le_succ m)
  unfold semRecvHook at hx
  by_cases href : (sC.base.stopped || sC.base.mir.win ||
      (isDel && (sC.base.mir.inTransit Q.other w).isNone) ||
      (!isDel && ((sC.base.mir.inTransit Q.other w).isSome ||
        !(sC.base.mir.safeInj 3) || !(ratchetKeyAdmissible P.codec decT encT w)))) = true
  · simp only [href, ↓reduceIte, runBucketDF, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq] at hx; rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact hInv0
  · simp only [href, Bool.false_eq_true, ↓reduceIte] at hx
    rcases hp : simParseRecvC P decT (2 ^ 32) (partyEnc Q) (sC.base.pq Q) w with
      _ | ⟨pq', i, pk, T?, lct⟩ <;> simp only [hp] at hx
    · simp only [runBucketDF, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hx; rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact hInv0
    · obtain ⟨_, -, _, hlct_i, _⟩ :=
        simParseRecvC_tryFrom_and_idx P decT Q (sC.base.pq Q) pq' w i pk T? lct hp
      let hcOpt : Option (SimFig8C Pt) := Option.map (fun (wc : Bytes × SimFig8C Pt) => wc.2)
        (sC.base.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
      have hmkC : ∀ (t : ℕ) (T : Option Pt), i ≤ 25001 * (q - m) →
          (match hcOpt with
            | some c => if c.2.2.2 = lct.2.2 then c else ((t, T), lct)
            | none => ((t, T), lct)).2.1 ≤ 25001 * (q - m) := fun t T hi_le => by
        cases hhc : hcOpt
        · dsimp only; omega
        · obtain ⟨wc, hfind, rfl⟩ := Option.map_eq_some_iff.mp hhc
          have hwc := hInv.hhonest wc (List.mem_of_find?_eq_some hfind)
          dsimp only; by_cases hct : wc.2.2.2.2 = lct.2.2 <;> simp only [hct, ↓reduceIte] <;> omega
      rcases hidx : (sC.base.chains Q).findIdx? (fun g => g.key == some pk) with _ | ci <;>
        simp only [hidx] at hx
      · let sA (amb : Bool) :=
          { sC with base := if amb then { sC.base with amb := sC.base.amb + 1 } else sC.base }
        have hsAmb_k : ∀ amb R, KeptInv (25000 * (q - (m + 1))) ((sA amb).kept R) := by
          intro amb; cases amb <;> exact hInv.hkept
        have hsAmb_c : ∀ amb R, ∀ g ∈ (sA amb).base.chains R, g.last ≤ 25001 * (q - m) := by
          intro amb; cases amb <;> exact hInv0.hchains
        have hsAmb_h : ∀ amb, ∀ wc ∈ (sA amb).base.honest, wc.2.2.1 ≤ q - m := by
          intro amb; cases amb <;> exact hInv0.hhonest
        have hsAmb_inv : ∀ amb, DFBucketSanInv q m (sA amb) ms := fun amb =>
          ⟨hInv0.hgame, fun R => (hsAmb_k amb R).mono (Nat.mul_le_mul_left 25000 (by omega)),
            hsAmb_c amb, hsAmb_h amb⟩
        by_cases hc1 : ((((sC.base.honest.find? fun wc =>
              wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
            fun c => decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) == some true &&
           (((sC.base.honest.find? fun wc =>
              wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
            fun c => decide (c.2.2.2 = lct.2.2)) == some true) = true
        · simp only [hc1, ↓reduceIte, runBucketDF, simulateQ_pure, StateT.run_pure, support_pure,
            Set.mem_singleton_iff, Prod.mk.injEq] at hx; rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact hInv0
        · simp only [hc1, Bool.false_eq_true, ↓reduceIte] at hx
          by_cases hz : (T? == some 0) = true
          · simp only [hz, ↓reduceIte, runBucketDF, simulateQ_pure, StateT.run_pure, support_pure,
              Set.mem_singleton_iff, Prod.mk.injEq] at hx; rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact hInv0
          · simp only [hz, Bool.false_eq_true, ↓reduceIte] at hx
            by_cases hc2 : (inReceiveOnlyEpoch sC.base.mir Q || decide (25000 < i - 1) ||
                decide (2 ^ 32 ≤ i)) = true
            · simp only [hc2, ↓reduceIte, runBucketDF, simulateQ_pure, StateT.run_pure, support_pure,
                Set.mem_singleton_iff, Prod.mk.injEq] at hx; rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact hsAmb_inv _
            · simp only [hc2, Bool.false_eq_true, ↓reduceIte] at hx
              have hnot : ¬ 25000 < i - 1 := fun hlt => hc2 (by simp [hlt])
              have hi_le : i ≤ 25001 * (q - m) := by omega
              rcases hT : T? with _ | T₀ <;> simp only [hT] at hx
              · simp only [runBucketDF, simulateQ_pure, StateT.run_pure, support_pure,
                  Set.mem_singleton_iff, Prod.mk.injEq] at hx; rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact hsAmb_inv _
              · by_cases hev_b : ((((sC.base.honest.find? fun wc =>
                      wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
                    fun c => decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) == some true) = true
                · simp only [hev_b, ↓reduceIte] at hx; unfold semFwdEvictHook at hx
                  have hsAmb_mir : (if (inReceiveOnlyEpoch sC.base.mir Q ||
                        (Q == Party.A && (sC.base.chains Q).any fun x => x.key.isNone)) = true then
                      { sC.base with amb := sC.base.amb + 1 } else sC.base).mir = sC.base.mir := by
                    split_ifs <;> rfl
                  rw [hsAmb_mir] at hx
                  by_cases hev2 : (isDel && !sC.base.mir.safeInj 3) = true
                  · simp only [hev2, ↓reduceIte, runBucketDF, simulateQ_bind, StateT.run_bind,
                      mem_support_bind_iff, simulateQ_pure, StateT.run_pure, support_pure,
                      Set.mem_singleton_iff, Prod.mk.injEq] at hx
                    obtain ⟨⟨ex₂, ms'⟩, hpr, ⟨_, rfl, _⟩, rfl⟩ := hx
                    exact ⟨runBucketDF_onProbe_inv P Dh encPt encT lam Q
                        ((sC.base.mir.epoch Q + 1, some T₀), lct) ex ex₂ ms ms₁ hInv.hgame hpr,
                      (hsAmb_inv _).hkept, hsAmb_c _, hsAmb_h _⟩
                  · simp only [hev2, Bool.false_eq_true, ↓reduceIte] at hx
                    exact semFwdAnswerHook_bucket_dfSanInv P Dh encPt encT lam ms Q w isDel hInv.hgame
                      _ ex none pk pq' ((sC.base.mir.epoch Q + 1, some T₀), lct)
                      (hsAmb_k _) (hsAmb_c _) (hsAmb_h _) (by dsimp only; omega) _ hx
                · simp only [hev_b, Bool.false_eq_true, ↓reduceIte] at hx
                  exact semFwdHook_bucket_dfSanInv P Dh encPt encT lam B ms Q w isDel hInv.hgame
                    _ ex none pk pq' hcOpt _ (hsAmb_k _) (hsAmb_c _) (hsAmb_h _)
                    (hmkC (sC.base.mir.epoch Q + 1) (some T₀) hi_le) _ hx
      · by_cases hrej : ((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).rejects i = true
        · simp only [hrej, ↓reduceIte, runBucketDF, simulateQ_pure, StateT.run_pure, support_pure,
            Set.mem_singleton_iff, Prod.mk.injEq] at hx; rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact hInv0
        · simp only [hrej, Bool.false_eq_true, ↓reduceIte] at hx
          have hgl := hInv.hchains Q _ (getD_mem_of_findIdx?_eq_some ⟨none, 0, 0, []⟩ hidx)
          have hle := rejects_false_le (Bool.eq_false_iff.mpr hrej)
          exact semFwdHook_bucket_dfSanInv P Dh encPt encT lam B ms Q w isDel hInv.hgame
            sC ex (some ci) pk pq' hcOpt _ hInv.hkept hInv0.hchains hInv0.hhonest
            (hmkC (((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).epoch) T? (by omega)) _ hx

theorem semCorrHookDedup_bucket_dfSanInv
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (Fig8C Pt)) (ms : BucketState Pt ℓ)
    (Q : Party) (hInv : DFBucketSanInv q (m + 1) sC ms) :
    ∀ x ∈ support (runBucketDF P Dh encPt encT lam qep tL par
        (semCorrHookDedup P Dh encT (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)) sC ex Q) ms),
      DFBucketSanInv q m x.1.2.1 x.2 := by
  rintro ⟨⟨_, sC₁, _⟩, ms₁⟩ hx
  have hm1 : m + 1 ≤ q := hInv.hgame.hm; have hInv0 := hInv.mono (Nat.le_succ m)
  unfold semCorrHookDedup at hx
  by_cases href : (sC.base.stopped || sC.base.mir.win || !sC.base.mir.corrAllowed Q ||
      inReceiveOnlyEpoch sC.base.mir Q || !noAliceCorrWhileAliceBelowEpoch10 sC.base.mir Q) = true
  · simp only [href, ↓reduceIte, runBucketDF, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq] at hx; rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact hInv0
  · simp only [href, Bool.false_eq_true, ↓reduceIte, runBucketDF, simulateQ_bind, StateT.run_bind,
      mem_support_bind_iff] at hx
    obtain ⟨⟨⟨res, ex₂⟩, ms'⟩, hcr, hx⟩ := hx
    obtain ⟨hg', hst_eq⟩ := runBucketDF_onCr_inv P Dh encPt encT lam Q ex ex₂ ms ms' res hInv.hgame hcr
    rcases res with _ | fig8st <;>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    · rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact ⟨hg', hInv0.hkept, hInv0.hchains, hInv0.hhonest⟩
    · rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; refine ⟨hg', fun R => ?_, fun R g hg => ?_, hInv0.hhonest⟩
      · dsimp only; by_cases hR : R = Q
        · subst hR; simp only [Function.update_self, hst_eq fig8st rfl]
          exact (keptInv_ofSt (hInv.hgame.hparty R)).mono (Nat.mul_le_mul_left 25000 (by omega))
        · simp only [Function.update_of_ne hR]; exact hInv0.hkept R
      · dsimp only at hg
        by_cases hB0 : (Q == Party.B && sC.base.mir.epoch Party.B == 0) = true <;>
          simp only [hB0, ↓reduceIte, Bool.false_eq_true] at hg
        · rcases hγ : fig8st.γ with _ | x <;> simp only [hγ] at hg
          · exact hInv0.hchains R g hg
          · by_cases hR : R = .A
            · subst hR; simp only [Function.update_self, List.mem_map] at hg
              obtain ⟨g₀, hg₀, rfl⟩ := hg; split_ifs <;> exact hInv0.hchains .A g₀ hg₀
            · simp only [Function.update_of_ne hR] at hg; exact hInv0.hchains R g hg
        · exact hInv0.hchains R g hg

private theorem simDeliverForgeOracleDedup_step_bucket_dfSanInv (decT : PublicKey → Option Pt) (B : ℕ)
    (t : (CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) PQC Bytes).Domain)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (Fig8C Pt)) (ms : BucketState Pt ℓ)
    (hInv : DFBucketSanInv q (m + 1) sC ms) :
    ∀ x ∈ support (runBucketDF P Dh encPt encT lam qep tL par
        ((simDeliverForgeOracleDedup P Dh encPt encT decT lam qep B (.inr t)).run (sC, ex)) ms),
      DFBucketSanInv q m x.1.2.1 x.2 := by
  rcases t with ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · exact semSendHook_bucket_dfSanInv P Dh encPt encT lam sC ex ms Q m₀ none r hInv
  · exact semSendHook_bucket_dfSanInv P Dh encPt encT lam sC ex ms Q m₀ (some m₁) r hInv
  · have hstep : ((simDeliverForgeOracleDedup P Dh encPt encT decT lam qep B
        (.inr (.inl (.inl (.inr (Q, w)))))).run (sC, ex)) =
      semRecvHook P Dh encPt encT decT lam
        (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)) qep B sC ex Q w true := by
      dsimp only [simDeliverForgeOracleDedup, StateT.run, StateT.mk, semHandleHookDedup]
      have hpost : (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)).onDeliverPost =
          fun _ _ _ ex' => pure ex' := rfl
      rw [hpost]; simp only [pure_bind, Prod.mk.eta, bind_pure]
    rw [hstep]; exact semRecvHook_bucket_dfSanInv P Dh encPt encT lam decT B sC ex ms Q w true hInv
  · exact semRecvHook_bucket_dfSanInv P Dh encPt encT lam decT B sC ex ms Q w false hInv
  · exact semCorrHookDedup_bucket_dfSanInv P Dh encPt encT lam sC ex ms Q hInv

omit [SampleableType PQC] in
theorem simulateQ_runBucketDF_eq_of_inv {St : Type}
    (O₁ O₂ : QueryImpl (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) PQC Bytes)
      (StateT St (AdversaryCompDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))))
    (proj : St → LibsignalToModularSchemeSimState PQ Pt ℓ)
    (hinl₁ : ∀ n, O₁ (.inl n) = StateT.lift (query (spec := unifSpec +
      specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) (.inl n)))
    (hinl₂ : ∀ n, O₂ (.inl n) = StateT.lift (query (spec := unifSpec +
      specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) (.inl n)))
    (hstepEq : ∀ m' t st ms, DFBucketSanInv q (m' + 1) (proj st) ms →
      runBucketDF P Dh encPt encT lam qep tL par ((O₁ (.inr t)).run st) ms =
        runBucketDF P Dh encPt encT lam qep tL par ((O₂ (.inr t)).run st) ms)
    (hstepInv : ∀ m' t st ms, DFBucketSanInv q (m' + 1) (proj st) ms →
      ∀ x ∈ support (runBucketDF P Dh encPt encT lam qep tL par ((O₂ (.inr t)).run st) ms),
        DFBucketSanInv q m' (proj x.1.2) x.2)
    {α : Type}
    (oa : OracleComp (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) PQC Bytes) α)
    (m : ℕ) (hq : oa.IsQueryBoundP
      (isGameQuery (G := CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) PQC Bytes)) m)
    (st : St) (ms : BucketState Pt ℓ) (hInv : DFBucketSanInv q m (proj st) ms) :
    runBucketDF P Dh encPt encT lam qep tL par ((simulateQ O₁ oa).run st) ms =
      runBucketDF P Dh encPt encT lam qep tL par ((simulateQ O₂ oa).run st) ms := by
  induction oa using OracleComp.inductionOn generalizing m st ms with
  | pure a => simp only [runBucketDF, simulateQ_pure, StateT.run_pure]
  | query_bind q_in mx ih =>
    have hq' := (isQueryBoundP_query_bind_iff _ q_in mx m).mp hq
    dsimp only [runBucketDF] at hstepEq hstepInv ⊢
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind]
    rcases q_in with n | t
    · have hinl : (bucketImplDF P Dh encPt encT lam qep tL par (.inl n)).run ms =
          (query (spec := unifSpec) n >>= fun u => pure (u, ms)) :=
        bucketImplDF_inl P Dh encPt encT lam qep tL par n ms
      rw [hinl₁ n, hinl₂ n]
      simp only [stateT_lift_run, query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        simulateQ_bind, simulateQ_query, simulateQ_pure, StateT.run_bind, StateT.run_pure,
        hinl, bind_assoc, pure_bind]
      exact bind_congr fun u => ih u m (by simpa [isGameQuery] using hq'.2 u) st ms hInv
    · have hm_pos : 0 < m := by simpa [isGameQuery] using hq'.1
      rcases m with _ | m'
      · omega
      rw [hstepEq m' t st ms hInv]
      exact bind_congr_of_forall_mem_support _ fun x hx =>
        ih x.1.1 m' (by simpa [isGameQuery] using hq'.2 x.1.1) x.1.2 x.2
          (hstepInv m' t st ms hInv x hx)

private theorem simulateQ_runBucketDF_simDeliverForgeOracleSan_eq
    (decT : PublicKey → Option Pt) (B T Kc Bsk : ℕ) {α : Type}
    (oa : OracleComp (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) PQC Bytes) α)
    (m : ℕ) (hq : oa.IsQueryBoundP
      (isGameQuery (G := CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) PQC Bytes)) m)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (Fig8C Pt)) (ms : BucketState Pt ℓ)
    (hT : 25000 * q ≤ T) (hKc : 25001 * q + 25000 ≤ Kc) (hBsk : 25000 * q ≤ Bsk)
    (hInv : DFBucketSanInv q m sC ms) :
    runBucketDF P Dh encPt encT lam qep tL par
      ((simulateQ (simDeliverForgeOracleSan P Dh encPt encT decT lam qep B T Kc Bsk) oa).run (sC, ex)) ms =
    runBucketDF P Dh encPt encT lam qep tL par
      ((simulateQ (simDeliverForgeOracleDedup P Dh encPt encT decT lam qep B) oa).run (sC, ex)) ms := by
  refine simulateQ_runBucketDF_eq_of_inv P Dh encPt encT lam _ _ Prod.fst (fun _ => rfl) (fun _ => rfl)
    (fun m' t st ms hInv' => ?_)
    (fun m' t st ms hInv' =>
      simDeliverForgeOracleDedup_step_bucket_dfSanInv P Dh encPt encT lam decT B t st.1 st.2 ms hInv')
    oa m hq (sC, ex) ms hInv
  rcases st with ⟨sC, ex⟩
  have hm1 : m' + 1 ≤ q := hInv'.hgame.hm
  rcases t with t₀ | Q
  · rw [simDeliverForgeOracleSan_inr_inl_eq P Dh encPt encT decT lam qep t₀ (sC, ex)
      (B0 := 25000 * (q - (m' + 1))) (by omega) hInv'.hkept (by omega)
      (fun R g hg => by have := hInv'.hchains R g hg; omega)]
  · refine simDeliverForgeOracleSan_inr_inr_eq_of_support P Dh encPt encT decT lam qep Q
      (sC, ex) (bucketImplDF P Dh encPt encT lam qep tL par) ms
      fun x hx fig8st hres t_ep v hv => ?_
    rcases x with ⟨⟨res, ex'⟩, ms'⟩
    obtain ⟨-, hst_eq⟩ := runBucketDF_onCr_inv P Dh encPt encT lam Q ex ex' ms ms' res hInv'.hgame hx
    rw [hst_eq fig8st hres] at hv; exact ((hInv'.hgame.hparty Q).2 t_ep v hv).mono (by omega)

end HookBucketSanInv

theorem forgeGameBucketPaper_challSimDF'Paper_simDeliverForgeClampSan_eq
    {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B T Kc Bsk : ℕ) (tL : Option ℕ) (par : Bool)
    (idOf : Party → IdentityKey) (hid : idOf = fun R => if R == Party.A then P.idA else P.idB)
    (A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) PQC Bytes)
    (q : ℕ) (hq : CryptoGames.SM.MakesAtMostQueries A q)
    (hT : 25000 * q ≤ T) (hKc : 25001 * q + 25000 ≤ Kc) (hBsk : 25000 * q ≤ Bsk) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    forgeGameBucketPaper fig 1 (qep + 1) sameHdrScheme tL par
        (challSimDF'Paper (2 + 1) (qep + 1)
          (simDeliverForgeClampSan P ℓ Dh encPt encT decT lam qep B T Kc Bsk A)) =
      forgeGameBucketPaper fig 1 (qep + 1) sameHdrScheme tL par
        (challSimDF'Paper (2 + 1) (qep + 1)
          (simDeliverForgeClamp P Dh encPt encT decT lam qep B A)) := by
  subst hid; dsimp only
  have hClamp : simDeliverForgeClamp P Dh encPt encT decT lam qep B A =
      ((liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) :
        AdversaryCompDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt) (BitVec 256)) >>=
        fun pqrKey => (simulateQ (simDeliverForgeOracleDedup P Dh encPt encT decT lam qep B) A).run'
          (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey), [])) :=
    bind_congr fun pqrKey =>
      (run'_simulateQ_simDeliverForgeOracleDedup_eq_public P Dh encPt encT decT lam qep B A _).symm
  rw [hClamp, forgeGameBucketPaper_challSimDF'Paper_eq_runBucketDF,
    forgeGameBucketPaper_challSimDF'Paper_eq_runBucketDF]
  refine bind_congr fun k => bind_congr fun b => ?_
  unfold simDeliverForgeClampSan
  simp only [runBucketDF, simulateQ_bind, StateT.run_bind, bucketImplDF_liftM_probComp,
    StateT.run'_eq, map_eq_bind_pure_comp, Function.comp_def, simulateQ_pure, StateT.run_pure,
    bind_assoc, pure_bind]
  refine bind_congr fun pqrKey => ?_
  have h1 := simulateQ_runBucketDF_simDeliverForgeOracleSan_eq (q := q) (qep := qep) (tL := tL)
    (par := par) P Dh encPt encT lam decT B T Kc Bsk A q
    ((makesAtMostQueries_iff_isGameQuery A q).mp hq)
    (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)) []
    ({ st := fun _ => (), b := b }, (initState _ k false, none))
    hT hKc hBsk (dfBucketSanInv_init P Dh encPt encT lam q k pqrKey false b none)
  dsimp only [runBucketDF] at h1; rw [h1]

end BucketCoupling

end Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeSanCoupling
