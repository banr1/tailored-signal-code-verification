/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeHaltedBase
public import Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeHaltedSanGame -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeSanCoupling -- proof-setup: allow-public-import
public import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEClamp -- proof-setup: allow-public-import
public import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEClamp2 -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperCKA -- proof-setup: allow-public-import
import Computational.Proofs.GameHop.CompDedup
import Computational.Proofs.Game.PromotedCostedReds.SimFig8LoopAndCost
import Computational.Proofs.Game.PromotedCostedReds.SanOracleCore
import Computational.Proofs.Game.PromotedCostedReds.SimFig8SanGame
import Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeSanOracle
import Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeSanSem
import Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeProg

/-!
# Sanitized-to-Unclamped Advantage Coupling for `SimDeliverForgeHalted`

Couples `simDeliverForgeClampSanQTrackHalted` to `simDeliverForgeTrackHalted` inside
`forgeGuessedAdvantageCellPaper` and `forgeBucketAdvantagePaper`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeHaltedCoupling

open OracleSpec OracleComp
open _root_.ReductionDsl (isGameQuery)
open _root_.CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.Ratchet (RootKey)
open CryptoGames.SM (GameState Config RecvResult partyEnc initState noBobSendInEpoch0
  noAliceCorrWhileAliceBelowEpoch10)
open CryptoGames.SM.Thm1 (Mirror)
open CryptoGames.SM.Construction.DeliverForge (AdversaryDF AdversaryCompDF specDF
  simOraclesDF'Paper simImplDF'Paper challSimDF'Paper simTransmitDF'Paper simChallDF'Paper
  simDeliverDF simInjectDF simDeliverForgeDF simCorrDFPaper sameHdrScheme
  forgeGuessedAdvantageCellPaper forgeGameBucketPaper forgeBucketAdvantagePaper
  transmitQueryDF challQueryDF deliverQueryDF injectQueryDF deliverForgeQuery corrQueryDF)
open CryptoGames.LibsignalSession (IdentityKey PublicKey GhostState Params ShaCompress)
open CryptoGames.Ratchet.LibsignalInst
  (LibsignalMsgPublicPart lFig8 lFS ratchetKeyAdmissible)
open CryptoGames.Ratchet.LibsignalSim
  (Fig8St Fig8C SimFig8St SimFig8C SimState SimBaseClampInv SemHook deliverForgeSemHook
   inReceiveOnlyEpoch simParseRecvC evalCKClamp scPostSendPure mkPub toWire
   semFwdAnswerHook semResyncHook semFwdEvictHook semFwdHook semRecvHook semCorrHook
   semHandleHook semHandleHookDedup simDeliverForgeOracleDedup makesAtMostQueries_iff_isGameQuery
   simStateCanon simStateCCanon simStateCCanon_idem stateT_lift_run
   runDFM semHandleHook_deliverForge_eq)
open CryptoGames.Ratchet.LibsignalSimC
  (LibsignalToModularSchemeSimState initSimC liftC guardC runOnBaseState simSendC
   simRecvC simCorrC simImplC)
open CryptoGames.LibsignalSM.Proofs.Refinement
  (KemFailTrackState initKemFailTrack stepKemFailSend stepKemFailDeliver sameWireFig8
   DeliverForgeM fig8ToDFImpl deliverForgeHook simSendCTrackHalted simImplCTrackHalted
   simRunCTrackHaltedWith simDeliverForgeTrackHalted)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.E2E
  (Bytes CellGameClampInv SemHookClampInv simBaseClampInv_init cellGameClampInv_init
   cellGameClampInv_transmitImpl cellGameClampInv_deliverImpl cellGameClampInv_injectImplCellT
   cellGameClampInv_deliverForgeBaseImplCellT cellGameClampInv_corrImplShiftedPaper
   scPostSendPure_clampInv semRecvHook_preserves_clampInv semCorrHook_preserves_clampInv)
open CryptoVerification.LibsignalSession.HeadlineV1
  (cellDelta cellShift oracleImplCellTPaper oracleImplBaseDFCellTPaper fullImplBaseDFCellTPaper
   runBaseDFCellTPaper forgeGuessedAdvantageCellPaperT_eq_runBaseDFCellTPaper)
open Computational.Proofs.GameHop.CompDedup
  (canonComp canonComp_epMgmt canonComp_record run'_simulateQ_eq_of_idem_proj)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8LoopAndCost
  (semHandleHookDedup_simStateCCanon' semHandleHook_simStateCCanon')
open Computational.Proofs.Game.PromotedCostedReds.SanOracleCore (semHandleHookDedupS)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8SanGame (GameSanInv KeptInv keptInv_send)
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeSanOracle (simDeliverForgeOracleSan)
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeSanSem
  (simDeliverForgeOracleSan_inr_inl_eq simDeliverForgeOracleSan_inr_inr_eq_of_support)
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeSanCoupling
  (BucketState bucketImplDF runBucketDF runBucketDF_bind bucketImplDF_inl
   bucketImplDF_liftM_probComp forgeGameBucketPaper_challSimDF'Paper_eq_runBucketDF
   runBucketDF_transmitQueryDF_inv runBucketDF_challQueryDF_inv runBucketDF_onCr_inv
   DFBucketSanInv dfBucketSanInv_init semRecvHook_bucket_dfSanInv semCorrHookDedup_bucket_dfSanInv
   simulateQ_runBucketDF_eq_of_inv)
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeProg
  (BucketEx deliverForgeBucketSemHook deliverForgeBucketSemHookClampInv packBucketDF
   runBucketDF_semRecvHook runBucketDF_semCorrHook)
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeHaltedBase
  (semSendTrackHalted simDeliverForgeOracleSanTrackHalted
   simDeliverForgeClampSanTrackHalted simDeliverForgeClampSanQTrackHalted)
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeHaltedSanGame
  (CellState cellImplDF cellImplDF_run runCellDF cellImplDF_inl cellImplDF_liftM_probComp
   runBaseDFCellTPaper_challSimDF'Paper_eq_runCellDF
   simDeliverForgeOracleDedupTrackHalted simDeliverForgeClampDedupTrackHalted
   runBaseDFCellTPaper_challSimDF'Paper_simDeliverForgeClampSanTrackHalted_eq_dedup)

noncomputable section

/-- Non-dedup `B`-clamped tracker-halted `DeliverForge` semantic oracle (couples directly to
`simImplCTrackHalted` via `semHandleHook_deliverForge_eq`). -/
@[expose] def simDeliverForgeOracleTrackHalted {PQ Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B : ℕ) :
    QueryImpl (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes)
      (StateT ((LibsignalToModularSchemeSimState PQ Pt ℓ × List (Fig8C Pt)) × KemFailTrackState P.C.F)
        (AdversaryCompDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)))
  | .inl n => StateT.lift (query (spec := unifSpec + specDF (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) (.inl n))
  | .inr (.inl (.inl (.inl (.inl (Q, m, r))))) => StateT.mk fun ⟨⟨sC, ex⟩, tr⟩ =>
    semSendTrackHalted P K Dh encPt encT lam qep sC ex tr Q m none r
  | .inr (.inl (.inl (.inl (.inr (Q, m₀, m₁, r))))) => StateT.mk fun ⟨⟨sC, ex⟩, tr⟩ =>
    semSendTrackHalted P K Dh encPt encT lam qep sC ex tr Q m₀ (some m₁) r
  | .inr (.inl (.inl (.inr (Q, w)))) => StateT.mk fun ⟨⟨sC, ex⟩, tr⟩ => do
    let j? := sC.base.honest.reverse.findIdx? (fun wc =>
      wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
    let (res, s') ← semRecvHook P Dh encPt encT decT lam
      (deliverForgeSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ)) qep B sC ex Q w true
    let tr' := match res, j? with
      | some (.accepted _ _ _), some j => stepKemFailDeliver P.C.F K tr Q j
      | _, _ => tr
    return (res, (s', tr'))
  | .inr (.inl (.inr (Q, w))) => StateT.mk fun ⟨⟨sC, ex⟩, tr⟩ => do
    let (res, s') ← semRecvHook P Dh encPt encT decT lam
      (deliverForgeSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ)) qep B sC ex Q w false
    return (res, (s', tr))
  | .inr (.inr Q) => StateT.mk fun ⟨⟨sC, ex⟩, tr⟩ => do
    let (res, s') ← semCorrHook P Dh encT
      (deliverForgeSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ)) sC ex Q
    return (res, (s', tr))

@[expose] def simDeliverForgeClampTrackHalted {PQ Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B : ℕ)
    (A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes) :
    AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt) :=
  show AdversaryCompDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt) Bool from do
    let pqrKey ← (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) :
      AdversaryCompDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt) (BitVec 256))
    let sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ :=
    initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)
    let tr₀ := initKemFailTrack P.C.F pqrKey
    (simulateQ (simDeliverForgeOracleTrackHalted P K Dh encPt encT decT lam qep B) A).run' ((sC₀, []), tr₀)

/-! ## Dedup-to-non-dedup canonicalization -/

private theorem scPostSendPure_simStateCCanon {PQ Pt : Type} [Zero Pt] {ℓ : ℕ}
    (P : Params PQ (BitVec 512)) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (s₁ : GameState Unit (Plain ℓ) Bytes)
    (Q : Party) (m₀ : Plain ℓ) (isChall : Bool) (pq' : PQ) (pn : BitVec 32) (c : Fig8C Pt) :
    simStateCCanon (scPostSendPure P Dh encPt encT lam sC s₁ Q m₀ isChall pq' pn c) =
      simStateCCanon (scPostSendPure P Dh encPt encT lam (simStateCCanon sC) (canonComp s₁) Q m₀ isChall pq' pn c) := by
  unfold scPostSendPure simStateCCanon simStateCanon; dsimp only []; congr 2; exact canonComp_record s₁ 3 Q () _ isChall

private theorem semSendTrackHalted_simStateCCanon' {PQ Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt) (qep : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (Fig8C Pt)) (tr : KemFailTrackState P.C.F)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option (BitVec 512)) :
    Prod.map id (Prod.map (Prod.map simStateCCanon id) id) <$> semSendTrackHalted P K Dh encPt encT lam qep sC ex tr Q m₀ chal r =
      Prod.map id (Prod.map (Prod.map simStateCCanon id) id) <$> semSendTrackHalted P K Dh encPt encT lam qep (simStateCCanon sC) ex tr Q m₀ chal r := by
  unfold semSendTrackHalted
  have h1 : ((simStateCCanon sC).base.stopped || (simStateCCanon sC).base.mir.win || !(noBobSendInEpoch0 (simStateCCanon sC).base.mir Q)) =
    (sC.base.stopped || sC.base.mir.win || !(noBobSendInEpoch0 sC.base.mir Q)) := rfl
  have hep_eq : (simStateCCanon sC).base.mir.epMgmt 3 qep Q r.isSome = Option.map canonComp (sC.base.mir.epMgmt 3 qep Q r.isSome) :=
    (canonComp_epMgmt sC.base.mir 3 qep Q r.isSome).symm
  rw [h1, hep_eq]; cases href : (sC.base.stopped || sC.base.mir.win || !(noBobSendInEpoch0 sC.base.mir Q))
  · simp only [Bool.false_eq_true, ↓reduceIte]; rcases sC.base.mir.epMgmt 3 qep Q r.isSome with _ | s₁
    · simp only [Option.map, map_pure, Prod.map, id_eq, simStateCCanon_idem]
    · dsimp only [Option.map]; have hsc : (canonComp s₁).safeCh 3 Q = s₁.safeCh 3 Q := rfl; rw [hsc]
      cases hch : (chal.isSome && !(s₁.safeCh 3 Q))
      · simp only [Bool.false_eq_true, ↓reduceIte, map_bind]; refine bind_congr fun rq => ?_
        cases hcand : (stepKemFailSend P.C.F K tr Q rq).cand.isSome
        · simp only [Bool.false_eq_true, ↓reduceIte, map_bind]; refine bind_congr fun rc => ?_
          have hpn : (if (canonComp s₁).epoch Q ≠ (simStateCCanon sC).base.mir.epoch Q then BitVec.ofNat 32 ((simStateCCanon sC).base.mir.idx Q - 1) else (simStateCCanon sC).base.pn Q) =
            (if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1) else sC.base.pn Q) := rfl
          have hmk : mkPub (P := P) (simStateCCanon sC).base Q rq (if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1) else sC.base.pn Q) =
            mkPub (P := P) sC.base Q rq (if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1) else sC.base.pn Q) := rfl
          rw [hpn, hmk]; rcases mkPub (P := P) sC.base Q rq _ with _ | ⟨pq', pub⟩
          · simp only [map_pure, Prod.map, id_eq, simStateCCanon_idem]
          · simp only [map_bind]; refine bind_congr fun res => ?_; rcases res with _ | c
            · simp only [map_pure, Prod.map, id_eq, simStateCCanon_idem]
            · simp only [map_pure, Prod.map, id_eq]; rw [scPostSendPure_simStateCCanon]
        · simp only [↓reduceIte, map_pure, Prod.map, id_eq, simStateCCanon_idem]
      · simp only [↓reduceIte, map_pure, Prod.map, id_eq, simStateCCanon_idem]
  · simp only [↓reduceIte, map_pure, Prod.map, id_eq, simStateCCanon_idem]

theorem run'_simulateQ_simDeliverForgeOracleDedupTrackHalted_eq {PQ Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep B : ℕ)
    (A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes)
    (st : (LibsignalToModularSchemeSimState PQ Pt ℓ × List (Fig8C Pt)) × KemFailTrackState P.C.F) :
    (simulateQ (simDeliverForgeOracleDedupTrackHalted P K Dh encPt encT decT lam qep B) A).run' st =
      (simulateQ (simDeliverForgeOracleTrackHalted P K Dh encPt encT decT lam qep B) A).run' st := by
  have hdl_canon : ∀ sC ex Q w,
      Prod.map id (Prod.map simStateCCanon id) <$> semRecvHook P Dh encPt encT decT lam (deliverForgeSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ)) qep B sC ex Q w true =
      Prod.map id (Prod.map simStateCCanon id) <$> semRecvHook P Dh encPt encT decT lam (deliverForgeSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ)) qep B (simStateCCanon sC) ex Q w true := fun sC ex Q w => by
    have h := semHandleHookDedup_simStateCCanon' P Dh encPt encT decT lam (deliverForgeSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ)) qep B (.inl (.inl (.inr (Q, w)))) sC ex
    have hp : (deliverForgeSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ)).onDeliverPost = fun _ _ _ ex' => pure ex' := rfl
    unfold semHandleHookDedup semHandleHook at h; dsimp only [] at h; rw [hp] at h; simpa only [pure_bind, Prod.mk.eta, bind_pure] using h
  have hstep : ∀ {α : Type} (oa₁ oa₂ : AdversaryCompDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt) (α × (LibsignalToModularSchemeSimState PQ Pt ℓ × List (Fig8C Pt)))) (f : α → KemFailTrackState P.C.F),
      Prod.map id (Prod.map simStateCCanon id) <$> oa₁ = Prod.map id (Prod.map simStateCCanon id) <$> oa₂ →
      Prod.map id (Prod.map (Prod.map simStateCCanon id) id) <$> (oa₁ >>= fun x => pure (x.1, (x.2, f x.1))) =
      Prod.map id (Prod.map (Prod.map simStateCCanon id) id) <$> (oa₂ >>= fun x => pure (x.1, (x.2, f x.1))) := fun oa₁ oa₂ f heq => by
    have hp : ∀ (oa : AdversaryCompDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt) (_ × (LibsignalToModularSchemeSimState PQ Pt ℓ × List (Fig8C Pt)))),
        Prod.map id (Prod.map (Prod.map simStateCCanon id) id) <$> (oa >>= fun x => pure (x.1, (x.2, f x.1))) =
        (Prod.map id (Prod.map simStateCCanon id) <$> oa) >>= fun x => pure (x.1, (x.2, f x.1)) := fun oa => by
      rw [map_bind, bind_map_left]; refine bind_congr fun ⟨res, sC₁, ex₁⟩ => ?_; simp [Prod.map]
    rw [hp oa₁, hp oa₂, heq]
  refine run'_simulateQ_eq_of_idem_proj (simDeliverForgeOracleDedupTrackHalted P K Dh encPt encT decT lam qep B)
    (simDeliverForgeOracleTrackHalted P K Dh encPt encT decT lam qep B) (Prod.map (Prod.map simStateCCanon id) id) ?_ ?_ A rfl
  · rintro (n | ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)) ⟨⟨sC, ex⟩, tr⟩
    · simp [simDeliverForgeOracleDedupTrackHalted, simDeliverForgeOracleTrackHalted, StateT.run_lift, Prod.map, simStateCCanon_idem]
    · exact semSendTrackHalted_simStateCCanon' P K Dh encPt encT lam qep sC ex tr Q m₀ none r
    · exact semSendTrackHalted_simStateCCanon' P K Dh encPt encT lam qep sC ex tr Q m₀ (some m₁) r
    · dsimp only [simDeliverForgeOracleDedupTrackHalted, simDeliverForgeOracleTrackHalted, StateT.run, StateT.mk, Prod.map, id_eq]
      exact hstep _ _ (fun res => match res, sC.base.honest.reverse.findIdx? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) with | some (.accepted _ _ _), some j => stepKemFailDeliver P.C.F K tr Q j | _, _ => tr) (hdl_canon sC ex Q w)
    · have hij := semHandleHookDedup_simStateCCanon' P Dh encPt encT decT lam (deliverForgeSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ)) qep B (.inl (.inr (Q, w))) sC ex
      dsimp only [semHandleHookDedup, semHandleHook] at hij; exact hstep _ _ (fun _ => tr) hij
    · have hcr := semHandleHookDedup_simStateCCanon' P Dh encPt encT decT lam (deliverForgeSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ)) qep B (.inr Q) sC ex
      dsimp only [semHandleHookDedup, semHandleHook] at hcr; exact hstep _ _ (fun _ => tr) hcr
  · rintro (n | ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)) ⟨⟨sC, ex⟩, tr⟩
    · simp [simDeliverForgeOracleTrackHalted, StateT.run_lift, Prod.map, simStateCCanon_idem]
    · exact semSendTrackHalted_simStateCCanon' P K Dh encPt encT lam qep sC ex tr Q m₀ none r
    · exact semSendTrackHalted_simStateCCanon' P K Dh encPt encT lam qep sC ex tr Q m₀ (some m₁) r
    · dsimp only [simDeliverForgeOracleTrackHalted, StateT.run, StateT.mk, Prod.map, id_eq]
      exact hstep _ _ (fun res => match res, sC.base.honest.reverse.findIdx? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) with | some (.accepted _ _ _), some j => stepKemFailDeliver P.C.F K tr Q j | _, _ => tr) (hdl_canon sC ex Q w)
    · have hij := semHandleHook_simStateCCanon' P Dh encPt encT decT lam (deliverForgeSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ)) qep B (.inl (.inr (Q, w))) sC ex
      dsimp only [semHandleHook] at hij; exact hstep _ _ (fun _ => tr) hij
    · have hcr := semHandleHook_simStateCCanon' P Dh encPt encT decT lam (deliverForgeSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ)) qep B (.inr Q) sC ex
      dsimp only [semHandleHook] at hcr; exact hstep _ _ (fun _ => tr) hcr

theorem runBaseDFCellTPaper_challSimDF'Paper_simDeliverForgeClampSanTrackHalted_eq {PQ Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B T Kc Bsk : ℕ) (tL : Option ℕ) (t : ℕ) (idOf : Party → IdentityKey) (hid : idOf = fun R => if R == Party.A then P.idA else P.idB)
    (A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes) (q : ℕ) (hq : CryptoGames.SM.MakesAtMostQueries A q)
    (hT : 25000 * q ≤ T) (hKc : 25001 * q + 25000 ≤ Kc) (hBsk : 25000 * q ≤ Bsk) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    runBaseDFCellTPaper fig (qep + 1) tL t sameHdrScheme (Config.auth t) false
        (challSimDF'Paper (2 + 1) (qep + 1) (simDeliverForgeClampSanTrackHalted P K ℓ Dh encPt encT decT lam qep B T Kc Bsk A)) =
      runBaseDFCellTPaper fig (qep + 1) tL t sameHdrScheme (Config.auth t) false
        (challSimDF'Paper (2 + 1) (qep + 1) (simDeliverForgeClampTrackHalted P K Dh encPt encT decT lam qep B A)) := by
  have hDedup : simDeliverForgeClampDedupTrackHalted P K Dh encPt encT decT lam qep B A = simDeliverForgeClampTrackHalted P K Dh encPt encT decT lam qep B A := by
    unfold simDeliverForgeClampDedupTrackHalted simDeliverForgeClampTrackHalted
    exact bind_congr fun pqrKey => run'_simulateQ_simDeliverForgeOracleDedupTrackHalted_eq P K Dh encPt encT decT lam qep B A _
  rw [← hDedup]; exact runBaseDFCellTPaper_challSimDF'Paper_simDeliverForgeClampSanTrackHalted_eq_dedup P K Dh encPt encT decT lam qep B T Kc Bsk tL t idOf hid A q hq hT hKc hBsk

/-! ## Clamp-to-unclamped coupling -/

private theorem simDeliverForgeOracleTrackHalted_inl {PQ Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep B n : ℕ)
    (st : (LibsignalToModularSchemeSimState PQ Pt ℓ × List (Fig8C Pt)) × KemFailTrackState P.C.F) :
    (simDeliverForgeOracleTrackHalted P K Dh encPt encT decT lam qep B (.inl n)).run st =
      (fun u => (u, st)) <$> query (spec := unifSpec + specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) (.inl n) := by
  simp [simDeliverForgeOracleTrackHalted, StateT.run_lift]

private def runDFMTrack {PQ Pt α : Type} {F : ShaCompress} {ℓ : ℕ}
    (m : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ × KemFailTrackState F) (DeliverForgeM Pt ℓ) α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (Fig8C Pt)) (tr : KemFailTrackState F) :
    AdversaryCompDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)
      (α × ((LibsignalToModularSchemeSimState PQ Pt ℓ × List (Fig8C Pt)) × KemFailTrackState F)) :=
  (m.run (sC, tr)).run ex >>= fun ⟨⟨a, sC', tr'⟩, ex'⟩ => pure (a, ((sC', ex'), tr'))

private theorem runDFMTrack_bind {PQ Pt α β : Type} {F : ShaCompress} {ℓ : ℕ}
    (m : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ × KemFailTrackState F) (DeliverForgeM Pt ℓ) α)
    (f : α → StateT (LibsignalToModularSchemeSimState PQ Pt ℓ × KemFailTrackState F) (DeliverForgeM Pt ℓ) β)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (Fig8C Pt)) (tr : KemFailTrackState F) :
    runDFMTrack (m >>= f) sC ex tr = (runDFMTrack m sC ex tr >>= fun ⟨a, ⟨⟨sC', ex'⟩, tr'⟩⟩ => runDFMTrack (f a) sC' ex' tr') := by
  simp only [runDFMTrack, StateT.run_bind, bind_assoc, pure_bind]

private abbrev CellEx (Pt : Type) (ℓ : ℕ) := List (SimFig8C Pt) × CellState Pt ℓ

private def deliverForgeCellSemHook {PQ Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ (BitVec 512)) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt)
    (qep : ℕ) (tL : Option ℕ) (tStar : ℕ) : SemHook (BitVec 512) Pt ℓ unifSpec (CellEx Pt ℓ) where
  sampleBv256 := ($ᵗ (BitVec 256) : ProbComp (BitVec 256))
  samplePqc := ($ᵗ (BitVec 512) : ProbComp (BitVec 512))
  onSendCoins _ _ exs := pure (exs, exs)
  onTr Q m rc exs := do let ((res, ex'), s') ← runCellDF P Dh encPt encT lam qep tL tStar ((deliverForgeSemHook (PQC := BitVec 512)).onTr Q m rc exs.1) exs.2; return (res, (ex', s'))
  onCh Q m₀ m₁ rc exs := do let ((res, ex'), s') ← runCellDF P Dh encPt encT lam qep tL tStar ((deliverForgeSemHook (PQC := BitVec 512)).onCh Q m₀ m₁ rc exs.1) exs.2; return (res, (ex', s'))
  onDl Q c exs := do let ((res, ex'), s') ← runCellDF P Dh encPt encT lam qep tL tStar ((deliverForgeSemHook (PQC := BitVec 512)).onDl Q c exs.1) exs.2; return (res, (ex', s'))
  onIj Q c exs := do let ((res, ex'), s') ← runCellDF P Dh encPt encT lam qep tL tStar ((deliverForgeSemHook (PQC := BitVec 512)).onIj Q c exs.1) exs.2; return (res, (ex', s'))
  onCr Q exs := do let ((res, ex'), s') ← runCellDF P Dh encPt encT lam qep tL tStar ((deliverForgeSemHook (PQC := BitVec 512)).onCr Q exs.1) exs.2; return (res, (ex', s'))
  onProbe Q c' exs := runCellDF P Dh encPt encT lam qep tL tStar ((deliverForgeSemHook (PQC := BitVec 512)).onProbe Q c' exs.1) exs.2
  onDeliverPost _ _ _ exs := pure exs

private theorem deliverForgeCellSemHookClampInv {PQ Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ (BitVec 512)) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt)
    (qep B : ℕ) (tL : Option ℕ) (tStar : ℕ) :
    SemHookClampInv B (fun m (exs : CellEx Pt ℓ) => CellGameClampInv B m exs.2.2)
      (deliverForgeCellSemHook P Dh encPt encT lam qep tL tStar) where
  mono := fun hle h => h.mono hle
  onSendCoins_inv := by
    rintro m Q rq exs h y hy; change y ∈ support (pure (exs, exs)) at hy
    rw [support_pure, Set.mem_singleton_iff] at hy; subst hy; exact ⟨h, h⟩
  onTr_inv := by
    rintro m Q msg rc ⟨ex, mir, gs⟩ h ⟨res, ex', mir', gs'⟩ hy
    dsimp only [deliverForgeCellSemHook, deliverForgeSemHook, runCellDF, transmitQueryDF] at hy
    simp only [query, OracleQuery.input_query, OracleQuery.cont_query, id_map, simulateQ_bind, simulateQ_query, simulateQ_pure, StateT.run_bind, StateT.run_pure, mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hy
    obtain ⟨⟨⟨res', ex₁⟩, mir₁, gs₁⟩, ⟨⟨res₂, mir₂, gs₂⟩, hmem, ⟨rfl, rfl, rfl⟩, rfl⟩, rfl, rfl, rfl, rfl⟩ := hy
    rw [cellImplDF_run] at hmem; simp only [simImplDF'Paper, simOraclesDF'Paper, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr] at hmem
    unfold simTransmitDF'Paper transmitQueryDF fullImplBaseDFCellTPaper oracleImplBaseDFCellTPaper oracleImplCellTPaper at hmem
    simp only [StateT.run_bind, StateT.run_get, stateT_lift_run, query, OracleQuery.input_query, OracleQuery.cont_query, id_map, simulateQ_bind, simulateQ_query, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, pure_bind, bind_assoc, mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    obtain ⟨⟨res₁, gs₁⟩, hbase, ⟨⟨res₂, mir₂⟩, gs₂⟩, h2, hres, _, hgs₀⟩ := hmem; dsimp only at h2
    have hgs : res₂ = res₁ ∧ gs₂ = gs₁ := by
      rcases res₁ with _ | c
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h2; exact ⟨h2.1.1, h2.2⟩
      · rcases hep : mir.epMgmt (2 + 1) (qep + 1) Q false with _ | s₁ <;> simp only [hep, StateT.run_bind, StateT.run_set, StateT.run_pure, simulateQ_pure, pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h2 <;> exact ⟨h2.1.1, h2.2⟩
    rw [hres, hgs.1, hgs₀, hgs.2]
    exact cellGameClampInv_transmitImpl P Dh encPt encT lam (fun R => if R == Party.A then P.idA else P.idB) (cellDelta tL tStar) B m (qep + 1) gs gs₁ Q msg none res₁ h hbase
  onCh_inv := by
    rintro m Q m₀ m₁ rc ⟨ex, mir, gs⟩ h ⟨res, ex', mir', gs'⟩ hy
    dsimp only [deliverForgeCellSemHook, deliverForgeSemHook, runCellDF, challQueryDF] at hy
    simp only [query, OracleQuery.input_query, OracleQuery.cont_query, id_map, simulateQ_bind, simulateQ_query, simulateQ_pure, StateT.run_bind, StateT.run_pure, mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hy
    obtain ⟨⟨⟨res', ex₁⟩, mir₁, gs₁⟩, ⟨⟨res₂, mir₂, gs₂⟩, hmem, ⟨rfl, rfl, rfl⟩, rfl⟩, rfl, rfl, rfl, rfl⟩ := hy
    rw [cellImplDF_run] at hmem; simp only [simImplDF'Paper, simOraclesDF'Paper, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr] at hmem
    unfold simChallDF'Paper transmitQueryDF fullImplBaseDFCellTPaper oracleImplBaseDFCellTPaper oracleImplCellTPaper at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    rcases hep : mir.epMgmt (2 + 1) (qep + 1) Q false with _ | s₁ <;> simp only [hep] at hmem
    · simp only [StateT.run_pure, simulateQ_pure, pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl, rfl⟩; exact ⟨h.mono (Nat.le_succ m), fun _ hc => by cases hc⟩
    · cases hsc : s₁.safeCh (2 + 1) Q <;> simp only [hsc] at hmem
      · simp only [Bool.not_false, ↓reduceIte, StateT.run_pure, simulateQ_pure, pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl, rfl⟩; exact ⟨h.mono (Nat.le_succ m), fun _ hc => by cases hc⟩
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, stateT_lift_run, query, OracleQuery.input_query, OracleQuery.cont_query, id_map, simulateQ_bind, simulateQ_query, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, bind_assoc, pure_bind, mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        obtain ⟨⟨res₁, gs₁⟩, hbase, ⟨⟨res₂, mir₂⟩, gs₂⟩, h2, hres, _, hgs₀⟩ := hmem; dsimp only at h2
        have hgs : res₂ = res₁ ∧ gs₂ = gs₁ := by
          rcases res₁ with _ | c <;> simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, simulateQ_pure, pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h2 <;> exact ⟨h2.1.1, h2.2⟩
        rw [hres, hgs.1, hgs₀, hgs.2]
        exact cellGameClampInv_transmitImpl P Dh encPt encT lam (fun R => if R == Party.A then P.idA else P.idB) (cellDelta tL tStar) B m (qep + 1) gs gs₁ Q (if mir.b then m₁ else m₀) none res₁ h hbase
  onDl_inv := by
    rintro m Q c ⟨ex, mir, gs⟩ _ h ⟨res, ex', mir', gs'⟩ hy
    dsimp only [deliverForgeCellSemHook, deliverForgeSemHook, runCellDF, deliverQueryDF] at hy
    simp only [query, OracleQuery.input_query, OracleQuery.cont_query, id_map, simulateQ_bind, simulateQ_query, simulateQ_pure, StateT.run_bind, StateT.run_pure, mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hy
    obtain ⟨⟨⟨res', ex₁⟩, mir₁, gs₁⟩, ⟨⟨res₂, mir₂, gs₂⟩, hmem, ⟨rfl, rfl, rfl⟩, rfl⟩, rfl, rfl, rfl, rfl⟩ := hy
    rw [cellImplDF_run] at hmem; simp only [simImplDF'Paper, simOraclesDF'Paper, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr] at hmem
    unfold simDeliverDF deliverQueryDF fullImplBaseDFCellTPaper oracleImplBaseDFCellTPaper oracleImplCellTPaper at hmem
    simp only [StateT.run_bind, StateT.run_get, stateT_lift_run, query, OracleQuery.input_query, OracleQuery.cont_query, id_map, simulateQ_bind, simulateQ_query, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, pure_bind, bind_assoc, mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    obtain ⟨⟨res₁, gs₁⟩, hbase, ⟨⟨res₂, mir₂⟩, gs₂⟩, h2, hres, _, hgs₀⟩ := hmem; dsimp only at h2
    obtain ⟨hfg', hacc⟩ := cellGameClampInv_deliverImpl P Dh encPt encT lam (fun R => if R == Party.A then P.idA else P.idB) B m (Config.auth tStar) gs gs₁ Q c res₁ h hbase
    have hgs : gs₂ = gs₁ ∧ (∀ t i pm, res₂ = some (RecvResult.accepted t i pm) → ∃ pm', res₁ = some (RecvResult.accepted t i pm')) := by
      rcases res₁ with _ | (_ | ⟨t', i', pm'⟩)
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h2; exact ⟨h2.2, fun _ _ _ hc => by rw [h2.1.1] at hc; cases hc⟩
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h2; exact ⟨h2.2, fun _ _ _ hc => by rw [h2.1.1] at hc; cases hc⟩
      · rcases htr : mir.inTransit Q.other c with _ | r <;> simp only [htr, StateT.run_bind, StateT.run_set, StateT.run_pure, simulateQ_pure, pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h2 <;>
          (refine ⟨h2.2, fun t i pm hc => ?_⟩; rw [h2.1.1] at hc; cases hc; exact ⟨pm', rfl⟩)
    rw [hgs₀, hgs.1, hres]; exact ⟨hfg', fun t i pm hc => by obtain ⟨pm', h1⟩ := hgs.2 t i pm hc; exact hacc t i pm' h1⟩
  onIj_inv := by
    rintro m Q c ⟨ex, mir, gs⟩ _ h ⟨res, ex', mir', gs'⟩ hy
    dsimp only [deliverForgeCellSemHook, deliverForgeSemHook, runCellDF, injectQueryDF] at hy
    simp only [query, OracleQuery.input_query, OracleQuery.cont_query, id_map, simulateQ_bind, simulateQ_query, simulateQ_pure, StateT.run_bind, StateT.run_pure, mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hy
    obtain ⟨⟨⟨res', ex₁⟩, mir₁, gs₁⟩, ⟨⟨res₂, mir₂, gs₂⟩, hmem, ⟨rfl, rfl, rfl⟩, rfl⟩, rfl, rfl, rfl, rfl⟩ := hy
    rw [cellImplDF_run] at hmem; simp only [simImplDF'Paper, simOraclesDF'Paper, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr] at hmem
    unfold simInjectDF injectQueryDF fullImplBaseDFCellTPaper oracleImplBaseDFCellTPaper oracleImplCellTPaper at hmem
    simp only [StateT.run_bind, StateT.run_get, stateT_lift_run, query, OracleQuery.input_query, OracleQuery.cont_query, id_map, simulateQ_bind, simulateQ_query, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, pure_bind, bind_assoc, mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    obtain ⟨⟨res₁, gs₁⟩, hbase, ⟨⟨res₂, mir₂⟩, gs₂⟩, h2, hres, _, hgs₀⟩ := hmem; dsimp only at h2
    have hgs : res₂ = res₁ ∧ gs₂ = gs₁ := by
      rcases res₁ with _ | (_ | ⟨t', i', pm'⟩) <;> simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, simulateQ_pure, pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h2 <;> exact ⟨h2.1.1, h2.2⟩
    rw [hres, hgs.1, hgs₀, hgs.2]
    exact cellGameClampInv_injectImplCellT P Dh encPt encT lam (fun R => if R == Party.A then P.idA else P.idB) B m (qep + 1) tL tStar (Config.auth tStar) gs gs₁ Q c res₁ h hbase
  onCr_inv := by
    rintro m Q ⟨ex, mir, gs⟩ h ⟨res, ex', mir', gs'⟩ hy
    dsimp only [deliverForgeCellSemHook, deliverForgeSemHook, runCellDF, corrQueryDF] at hy
    simp only [query, OracleQuery.input_query, OracleQuery.cont_query, id_map, simulateQ_bind, simulateQ_query, simulateQ_pure, StateT.run_bind, StateT.run_pure, mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hy
    obtain ⟨⟨⟨res', ex₁⟩, mir₁, gs₁⟩, ⟨⟨res₂, mir₂, gs₂⟩, hmem, ⟨rfl, rfl, rfl⟩, rfl⟩, rfl, rfl, rfl, rfl⟩ := hy
    rw [cellImplDF_run] at hmem; simp only [simImplDF'Paper, simOraclesDF'Paper, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr] at hmem
    unfold simCorrDFPaper corrQueryDF fullImplBaseDFCellTPaper oracleImplBaseDFCellTPaper oracleImplCellTPaper at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    cases hca : mir.corrAllowedPaper Q <;> simp only [hca] at hmem
    · simp only [Bool.not_false, ↓reduceIte, StateT.run_pure, simulateQ_pure, pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl, rfl⟩; exact h.mono (Nat.le_succ m)
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, stateT_lift_run, query, OracleQuery.input_query, OracleQuery.cont_query, id_map, simulateQ_bind, simulateQ_query, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, bind_assoc, pure_bind, mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      obtain ⟨⟨res₁, gs₁⟩, hbase, ⟨⟨res₂, mir₂⟩, gs₂⟩, h2, _, _, hgs₀⟩ := hmem; dsimp only at h2
      have hgs : gs₂ = gs₁ := by
        rcases res₁ with _ | st' <;> simp only [Option.isSome, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure, simulateQ_pure, pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h2 <;> exact h2.2
      rw [hgs₀, hgs]; exact cellGameClampInv_corrImplShiftedPaper B m (cellShift tL tStar) gs gs₁ Q res₁ h hbase
  onProbe_inv := by
    rintro m Q c' ⟨ex, mir, gs⟩ h ⟨ex', mir', gs'⟩ hy; unfold deliverForgeCellSemHook deliverForgeSemHook runCellDF at hy
    rcases hfind : ex.find? (fun c => sameWireFig8 c c') with _ | c
    · simp only [hfind, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hy
      rcases hy with ⟨rfl, rfl, rfl⟩; exact h.mono (Nat.le_succ m)
    · simp only [hfind, deliverForgeQuery, query, OracleQuery.input_query, OracleQuery.cont_query, id_map, simulateQ_bind, simulateQ_query, simulateQ_pure, StateT.run_bind, StateT.run_pure, mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hy
      obtain ⟨⟨res, mir₁, gs₁⟩, hmem, rfl, rfl, rfl⟩ := hy
      rw [cellImplDF_run] at hmem; simp only [simImplDF'Paper, simOraclesDF'Paper, QueryImpl.add_apply_inr] at hmem
      unfold simDeliverForgeDF deliverForgeQuery fullImplBaseDFCellTPaper oracleImplBaseDFCellTPaper oracleImplCellTPaper at hmem
      simp only [StateT.run_bind, StateT.run_get, stateT_lift_run, query, OracleQuery.input_query, OracleQuery.cont_query, id_map, simulateQ_bind, simulateQ_query, QueryImpl.add_apply_inr, pure_bind, bind_assoc, mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      obtain ⟨⟨res₁, gs₁⟩, hbase, ⟨⟨res₂, mir₂⟩, gs₂⟩, h2, _, _, hgs₀⟩ := hmem; dsimp only at h2
      have hgs : gs₂ = gs₁ := by
        rcases res₁ with _ | (_ | ⟨t', i', pm'⟩) <;> simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, simulateQ_pure, pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h2 <;> exact h2.2
      rw [hgs₀, hgs]
      exact cellGameClampInv_deliverForgeBaseImplCellT P Dh encPt encT lam (fun R => if R == Party.A then P.idA else P.idB) B m (qep + 1) tL tStar (Config.auth tStar) gs gs₁ Q c c' res₁ h hbase
  onDeliverPost_inv := by
    rintro m Q j? rr exs h exs' hy; change exs' ∈ support (pure exs) at hy
    rw [support_pure, Set.mem_singleton_iff] at hy; subst hy; exact h

private def packCellDF {PQ Pt α : Type} {ℓ : ℕ}
    (x : (α × (LibsignalToModularSchemeSimState PQ Pt ℓ × List (SimFig8C Pt))) × CellState Pt ℓ) :
    α × (LibsignalToModularSchemeSimState PQ Pt ℓ × CellEx Pt ℓ) :=
  (x.1.1, (x.1.2.1, (x.1.2.2, x.2)))

section CellHookBridge
variable {PQ Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
  (P : Params PQ (BitVec 512)) (Dh : DHFun (BitVec 256) Pt)
  (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt) (qep : ℕ) (tL : Option ℕ) (tStar : ℕ)

private theorem runCellDF_semFwdAnswerHook (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : List (SimFig8C Pt))
    (s₀ : CellState Pt ℓ) (Q : Party) (w : Bytes) (isDel : Bool) (ci? : Option ℕ) (Tpk : PublicKey) (pq' : PQ) (c' : SimFig8C Pt) :
    packCellDF <$> runCellDF P Dh encPt encT lam qep tL tStar (semFwdAnswerHook P Dh encPt encT lam (deliverForgeSemHook (PQC := BitVec 512)) qep sC₀ ex₀ Q w isDel ci? Tpk pq' c') s₀ =
    semFwdAnswerHook P Dh encPt encT lam (deliverForgeCellSemHook P Dh encPt encT lam qep tL tStar) qep sC₀ (ex₀, s₀) Q w isDel ci? Tpk pq' c' := by
  unfold semFwdAnswerHook; dsimp only []; split_ifs <;> simp only [deliverForgeCellSemHook, runCellDF, packCellDF, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]

private theorem runCellDF_semResyncHook (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : List (SimFig8C Pt))
    (s₀ : CellState Pt ℓ) (Q : Party) (w : Bytes) (ci? : Option ℕ) (Tpk : PublicKey) (pq' : PQ) (c : SimFig8C Pt) (r : Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ))) :
    packCellDF <$> runCellDF P Dh encPt encT lam qep tL tStar (semResyncHook P Dh encPt encT lam (deliverForgeSemHook (PQC := BitVec 512)) qep sC₀ ex₀ Q w ci? Tpk pq' c r) s₀ =
    semResyncHook P Dh encPt encT lam (deliverForgeCellSemHook P Dh encPt encT lam qep tL tStar) qep sC₀ (ex₀, s₀) Q w ci? Tpk pq' c r := by
  unfold semResyncHook; rcases r with _ | ⟨t, i, _, m'⟩
  · rfl
  · simp only [deliverForgeCellSemHook, runCellDF, packCellDF, simulateQ_bind, StateT.run_bind, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    refine bind_congr fun ⟨⟨res, ex₁⟩, s₁⟩ => ?_; rcases res with _ | (_ | ⟨t', i', pm'⟩) <;> rfl

private theorem runCellDF_semFwdHook (B : ℕ) (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : List (SimFig8C Pt))
    (s₀ : CellState Pt ℓ) (Q : Party) (w : Bytes) (isDel : Bool) (ci? : Option ℕ) (Tpk : PublicKey) (pq' : PQ) (honestC : Option (SimFig8C Pt)) (c' : SimFig8C Pt) :
    packCellDF <$> runCellDF P Dh encPt encT lam qep tL tStar (semFwdHook P Dh encPt encT lam (deliverForgeSemHook (PQC := BitVec 512)) qep B sC₀ ex₀ Q w isDel ci? Tpk pq' honestC c') s₀ =
    semFwdHook P Dh encPt encT lam (deliverForgeCellSemHook P Dh encPt encT lam qep tL tStar) qep B sC₀ (ex₀, s₀) Q w isDel ci? Tpk pq' honestC c' := by
  unfold semFwdHook; rcases honestC with _ | c
  · exact runCellDF_semFwdAnswerHook P Dh encPt encT lam qep tL tStar sC₀ ex₀ s₀ Q w isDel ci? Tpk pq' c'
  · dsimp only []; split_ifs
    · rcases evalCKClamp P Dh encPt encT lam B sC₀ Q w c c' with _ | r
      · simp only [deliverForgeCellSemHook, runCellDF, packCellDF, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
      · exact runCellDF_semResyncHook P Dh encPt encT lam qep tL tStar sC₀ ex₀ s₀ Q w ci? Tpk pq' c r
    · exact runCellDF_semFwdAnswerHook P Dh encPt encT lam qep tL tStar sC₀ ex₀ s₀ Q w isDel ci? Tpk pq' c'

private theorem runCellDF_semFwdEvictHook (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : List (SimFig8C Pt))
    (s₀ : CellState Pt ℓ) (Q : Party) (w : Bytes) (isDel : Bool) (Tpk : PublicKey) (pq' : PQ) (c' : SimFig8C Pt) :
    packCellDF <$> runCellDF P Dh encPt encT lam qep tL tStar (semFwdEvictHook P Dh encPt encT lam (deliverForgeSemHook (PQC := BitVec 512)) qep sC₀ ex₀ Q w isDel Tpk pq' c') s₀ =
    semFwdEvictHook P Dh encPt encT lam (deliverForgeCellSemHook P Dh encPt encT lam qep tL tStar) qep sC₀ (ex₀, s₀) Q w isDel Tpk pq' c' := by
  unfold semFwdEvictHook; split_ifs
  · simp only [deliverForgeCellSemHook, runCellDF, packCellDF, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  · exact runCellDF_semFwdAnswerHook P Dh encPt encT lam qep tL tStar sC₀ ex₀ s₀ Q w isDel none Tpk pq' c'

private theorem runCellDF_semRecvHook (decT : PublicKey → Option Pt) (B : ℕ)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : List (SimFig8C Pt)) (s₀ : CellState Pt ℓ) (Q : Party) (w : Bytes) (isDel : Bool) :
    packCellDF <$> runCellDF P Dh encPt encT lam qep tL tStar (semRecvHook P Dh encPt encT decT lam (deliverForgeSemHook (PQC := BitVec 512)) qep B sC₀ ex₀ Q w isDel) s₀ =
    semRecvHook P Dh encPt encT decT lam (deliverForgeCellSemHook P Dh encPt encT lam qep tL tStar) qep B sC₀ (ex₀, s₀) Q w isDel := by
  unfold semRecvHook; dsimp only []
  cases href : (sC₀.base.stopped || sC₀.base.mir.win || (isDel && (sC₀.base.mir.inTransit Q.other w).isNone) || (!isDel && ((sC₀.base.mir.inTransit Q.other w).isSome || !(sC₀.base.mir.safeInj 3) || !(ratchetKeyAdmissible P.codec decT encT w))))
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rcases simParseRecvC P decT (2 ^ 32) (partyEnc Q) (sC₀.base.pq Q) w with _ | ⟨pq', i, pk, T?, lct⟩
    · rfl
    · dsimp only []
      rcases hidx : (sC₀.base.chains Q).findIdx? (fun g => g.key == some pk) with _ | ci <;> simp only [hidx]
      · cases h1 : (((Option.map (fun x => x.2) (List.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) sC₀.base.honest)).map fun c => decide (c.1.1 ≠ sC₀.base.mir.epoch Q + 1)) == some true && ((Option.map (fun x => x.2) (List.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) sC₀.base.honest)).map fun c => decide (c.2.2.2 = lct.2.2)) == some true)
        · simp only [Bool.false_eq_true, ↓reduceIte]; cases h2 : (T? == some 0)
          · simp only [Bool.false_eq_true, ↓reduceIte]
            cases h3 : (inReceiveOnlyEpoch sC₀.base.mir Q || decide (25000 < i - 1) || decide (2 ^ 32 ≤ i))
            · simp only [Bool.false_eq_true, ↓reduceIte]; rcases T? with _ | T
              · rfl
              · cases h4 : (((Option.map (fun x => x.2) (List.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) sC₀.base.honest)).map fun c => decide (c.1.1 ≠ sC₀.base.mir.epoch Q + 1)) == some true)
                · simp only [Bool.false_eq_true, ↓reduceIte]; exact runCellDF_semFwdHook P Dh encPt encT lam qep tL tStar B _ ex₀ s₀ Q w isDel none pk pq' _ _
                · simp only [↓reduceIte]; exact runCellDF_semFwdEvictHook P Dh encPt encT lam qep tL tStar _ ex₀ s₀ Q w isDel pk pq' _
            · rfl
          · rfl
        · rfl
      · cases h5 : ((sC₀.base.chains Q).getD ci { key := none, epoch := 0, last := 0, skipped := [] }).rejects i
        · simp only [Bool.false_eq_true, ↓reduceIte]; exact runCellDF_semFwdHook P Dh encPt encT lam qep tL tStar B sC₀ ex₀ s₀ Q w isDel (some ci) pk pq' _ _
        · rfl
  · rfl

private theorem runCellDF_semCorrHook (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : List (SimFig8C Pt)) (s₀ : CellState Pt ℓ) (Q : Party) :
    packCellDF <$> runCellDF P Dh encPt encT lam qep tL tStar (semCorrHook P Dh encT (deliverForgeSemHook (PQC := BitVec 512)) sC₀ ex₀ Q) s₀ =
    semCorrHook P Dh encT (deliverForgeCellSemHook P Dh encPt encT lam qep tL tStar) sC₀ (ex₀, s₀) Q := by
  unfold semCorrHook; dsimp only []
  cases href : (sC₀.base.stopped || sC₀.base.mir.win || !sC₀.base.mir.corrAllowed Q || inReceiveOnlyEpoch sC₀.base.mir Q || !noAliceCorrWhileAliceBelowEpoch10 sC₀.base.mir Q)
  · simp only [Bool.false_eq_true, ↓reduceIte, deliverForgeCellSemHook, runCellDF, packCellDF, simulateQ_bind, StateT.run_bind, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    refine bind_congr fun ⟨⟨res, ex₁⟩, s₁⟩ => ?_; rcases res with _ | fig8st <;> rfl
  · rfl

private theorem runCellDF_bind {α β : Type}
    (x : AdversaryCompDF (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt) α)
    (f : α → AdversaryCompDF (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt) β) (s₀ : CellState Pt ℓ) :
    runCellDF P Dh encPt encT lam qep tL tStar (x >>= f) s₀ =
      (runCellDF P Dh encPt encT lam qep tL tStar x s₀ >>= fun ⟨a, s'⟩ => runCellDF P Dh encPt encT lam qep tL tStar (f a) s') := by
  dsimp only [runCellDF]; rw [simulateQ_bind, StateT.run_bind]

private theorem runCellDF_simDeliverForgeOracleTrackHalted_inl (K : MlKem) (decT : PublicKey → Option Pt) (B : ℕ) (n : unifSpec.Domain)
    (st : (LibsignalToModularSchemeSimState PQ Pt ℓ × List (Fig8C Pt)) × KemFailTrackState P.C.F) (s : CellState Pt ℓ) :
    runCellDF P Dh encPt encT lam qep tL tStar ((simDeliverForgeOracleTrackHalted P K Dh encPt encT decT lam qep B (.inl n)).run st) s =
    (query (spec := unifSpec) n >>= fun r => pure ((r, st), s)) := by
  change (cellImplDF P Dh encPt encT lam qep tL tStar (.inl n) s >>= fun ⟨r, s₁⟩ => pure ((r, st), s₁)) = _
  rw [cellImplDF_inl]; simp only [bind_assoc, pure_bind]

end CellHookBridge

private theorem fig8ToDFImpl_liftM_probComp {Pt α : Type} {ℓ : ℕ} (p : ProbComp α) (ex : List (SimFig8C Pt)) :
    (simulateQ (fig8ToDFImpl Pt ℓ) (liftM p : OracleComp (unifSpec + CryptoGames.SM.spec (SimFig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt)) α)).run ex =
      ((liftM p : AdversaryCompDF (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
          (BitVec 256) (SimFig8C Pt) α) >>= fun a => pure (a, ex)) := by
  induction p using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t mx ih =>
    change (simulateQ (fig8ToDFImpl Pt ℓ) (query (spec := unifSpec + CryptoGames.SM.spec (SimFig8St Pt)
        (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt)) (.inl t) >>= fun u => liftM (mx u))).run ex =
      ((query (spec := unifSpec + specDF (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
        (BitVec 256) (SimFig8C Pt)) (.inl t) >>= fun u => liftM (mx u)) >>= fun a => pure (a, ex))
    rw [simulateQ_bind, StateT.run_bind, bind_assoc]
    change (StateT.lift (query (spec := unifSpec + specDF (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
        (BitVec 256) (SimFig8C Pt)) (.inl t)) >>= fun u => simulateQ (fig8ToDFImpl Pt ℓ) (liftM (mx u))).run ex = _
    simp only [StateT.run_bind, stateT_lift_run, bind_assoc, pure_bind]; exact bind_congr fun u => ih u

private theorem fig8ToDFImpl_transmitQuery {Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    (Q : Party) (m : LibsignalMsgPublicPart × Plain ℓ) (rc : Option (BitVec 256)) (ex : List (SimFig8C Pt)) :
    (simulateQ (fig8ToDFImpl Pt ℓ) (CryptoGames.SM.transmitQuery Q m rc)).run ex =
      (deliverForgeSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ)).onTr Q m rc ex := by
  simp only [CryptoGames.SM.transmitQuery, query, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
    id_map, fig8ToDFImpl, deliverForgeSemHook, StateT.run_bind, stateT_lift_run, pure_bind, bind_assoc]
  exact bind_congr fun res => by cases res <;> rfl

private theorem fig8ToDFImpl_challQuery {Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    (Q : Party) (m₀ m₁ : LibsignalMsgPublicPart × Plain ℓ) (rc : Option (BitVec 256)) (ex : List (SimFig8C Pt)) :
    (simulateQ (fig8ToDFImpl Pt ℓ) (CryptoGames.SM.challQuery Q m₀ m₁ rc)).run ex =
      (deliverForgeSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ)).onCh Q m₀ m₁ rc ex := by
  simp only [CryptoGames.SM.challQuery, query, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
    id_map, fig8ToDFImpl, deliverForgeSemHook, StateT.run_bind, stateT_lift_run, pure_bind, bind_assoc]
  exact bind_congr fun res => by cases res <;> rfl

private theorem runDFMTrack_liftS {PQ Pt α : Type} {F : ShaCompress} {ℓ : ℕ}
    (m : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (DeliverForgeM Pt ℓ) α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (Fig8C Pt)) (tr : KemFailTrackState F) :
    runDFMTrack (do let x ← get; let y ← StateT.lift (m.run x.1); set (y.2, x.2); pure y.1) sC ex tr =
      (runDFM m sC ex >>= fun x => pure (x.1, (x.2, tr))) := by
  simp only [runDFMTrack, runDFM, StateT.run_bind, StateT.run_get, StateT.run_set,
    StateT.run_pure, stateT_lift_run, pure_bind, bind_assoc]

private theorem run'_run'_eq_bind_runDFMTrack {PQ Pt α : Type} {F : ShaCompress} {ℓ : ℕ}
    (x : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ × KemFailTrackState F) (DeliverForgeM Pt ℓ) α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (Fig8C Pt)) (tr : KemFailTrackState F) :
    (x.run' (sC, tr)).run' ex = (runDFMTrack x sC ex tr >>= fun r => pure r.1) := by
  unfold runDFMTrack; simp only [StateT.run'_eq, StateT.run_bind, StateT.run_pure,
    map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]

private theorem semSendTrackHalted_deliverForge_eq {PQ Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt) (qep : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (SimFig8C Pt)) (tr : KemFailTrackState P.C.F)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option (BitVec 512)) :
    semSendTrackHalted P K Dh encPt encT lam qep sC ex tr Q m₀ chal r =
      let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
      runDFMTrack (simSendCTrackHalted P K qep (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (deliverForgeHook Pt ℓ) Q m₀ chal r) sC ex tr := by
  dsimp only []; unfold semSendTrackHalted runDFMTrack simSendCTrackHalted scPostSendPure
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases href : (sC.base.stopped || sC.base.mir.win || !(noBobSendInEpoch0 sC.base.mir Q))
  · simp only [Bool.false_eq_true, ↓reduceIte]; rcases sC.base.mir.epMgmt 3 qep Q r.isSome with _ | s₁
    · simp only [StateT.run_pure, pure_bind]
    · dsimp only []; cases hch : (chal.isSome && !(s₁.safeCh 3 Q))
      · simp only [Bool.false_eq_true, ↓reduceIte]; rcases r with _ | rq
        · simp only [deliverForgeHook, StateT.run_bind, stateT_lift_run, fig8ToDFImpl_liftM_probComp, pure_bind, bind_assoc]
          refine bind_congr fun x => ?_; cases hcand : (stepKemFailSend P.C.F K tr Q x).cand.isSome
          · simp only [Bool.false_eq_true, ↓reduceIte, simulateQ_pure, StateT.run_bind, stateT_lift_run, pure_bind]
            rcases mkPub (P := P) sC.base Q x (if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1) else sC.base.pn Q) with _ | ⟨pq', pub⟩
            · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
            · dsimp only []; cases chal <;> simp only [StateT.run_bind, stateT_lift_run, fig8ToDFImpl_transmitQuery, fig8ToDFImpl_challQuery, deliverForgeSemHook, pure_bind, bind_assoc]
              all_goals
                refine bind_congr fun res => ?_
                rcases res with _ | c
                · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
                · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, List.head?_cons]
                  rcases (sC.kept Q).full with _ | st <;> rfl
          · simp only [↓reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
        · simp only [deliverForgeHook, simulateQ_pure, StateT.run_bind, stateT_lift_run, pure_bind]
          cases hcand : (stepKemFailSend P.C.F K tr Q rq).cand.isSome
          · simp only [Bool.false_eq_true, ↓reduceIte, map_eq_bind_pure_comp, Function.comp_def, simulateQ_bind, simulateQ_pure, StateT.run_bind, stateT_lift_run, fig8ToDFImpl_liftM_probComp, pure_bind, bind_assoc]
            refine bind_congr fun x => ?_
            rcases mkPub (P := P) sC.base Q rq (if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1) else sC.base.pn Q) with _ | ⟨pq', pub⟩
            · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
            · cases chal <;> simp only [StateT.run_bind, stateT_lift_run, fig8ToDFImpl_transmitQuery, fig8ToDFImpl_challQuery, deliverForgeSemHook, pure_bind, bind_assoc]
              all_goals
                refine bind_congr fun res => ?_
                rcases res with _ | c
                · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
                · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, List.head?_cons]
                  rcases (sC.kept Q).full with _ | st <;> rfl
          · simp only [↓reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
      · simp only [↓reduceIte, StateT.run_pure, pure_bind]
  · simp only [↓reduceIte, StateT.run_pure, pure_bind]

private theorem simDeliverForgeTrackHalted_eq_bind_runDFMTrack {PQ Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep : ℕ) (idOf : Party → IdentityKey) (hid : idOf = fun R => if R == Party.A then P.idA else P.idB)
    (A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes) :
    simDeliverForgeTrackHalted P K ℓ Dh encPt encT decT idOf lam qep A =
      ((liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) : AdversaryCompDF (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt) (BitVec 256)) >>=
        fun pqrKey => runDFMTrack (simulateQ (simImplCTrackHalted P K encT decT qep (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (lFS P.C P.codec ℓ encT idOf 25000) (deliverForgeHook Pt ℓ) Dh) A)
          (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)) [] (initKemFailTrack P.C.F pqrKey) >>= fun r => pure r.1) := by
  subst hid; unfold simDeliverForgeTrackHalted simRunCTrackHaltedWith; dsimp only [deliverForgeHook]
  rw [StateT.run'_eq, StateT.run_bind, fig8ToDFImpl_liftM_probComp]
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]; refine bind_congr fun pqrKey => ?_
  simpa only [StateT.run'_eq, map_eq_bind_pure_comp, Function.comp_def] using run'_run'_eq_bind_runDFMTrack (simulateQ _ A) _ [] _

private theorem simDeliverForgeOracleTrackHalted_inl_eq {PQ Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B : ℕ) (n : unifSpec.Domain) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (SimFig8C Pt)) (tr : KemFailTrackState P.C.F) :
    (simDeliverForgeOracleTrackHalted P K Dh encPt encT decT lam qep B (.inl n)).run ((sC, ex), tr) =
      let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
      runDFMTrack (simImplCTrackHalted P K encT decT qep (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (lFS P.C P.codec ℓ encT idOf 25000) (deliverForgeHook Pt ℓ) Dh (.inl n)) sC ex tr := by
  rw [simDeliverForgeOracleTrackHalted_inl]; dsimp only [simImplCTrackHalted, HAdd.hAdd, Add.add, QueryImpl.add, Sum.elim, deliverForgeHook, runDFMTrack]
  rw [stateT_lift_run, StateT.run_bind, fig8ToDFImpl_liftM_probComp]; simp only [StateT.run_pure, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]; rfl

private theorem semSendTrackHalted_preserves_clampInv {PQ Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt)
    (qep B m : ℕ) (tL : Option ℕ) (tStar : ℕ) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (SimFig8C Pt))
    (tr : KemFailTrackState P.C.F) (s : CellState Pt ℓ) (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option (BitVec 512))
    (hBase : SimBaseClampInv B (m + 1) sC.base) (hCell : CellGameClampInv B (m + 1) s.2) :
    ∀ x ∈ support (runCellDF P Dh encPt encT lam qep tL tStar (semSendTrackHalted P K Dh encPt encT lam qep sC ex tr Q m₀ chal r) s),
      SimBaseClampInv B m x.1.2.1.1.base ∧ CellGameClampInv B m x.2.2 := by
  rintro ⟨⟨w?, ⟨⟨sC', ex'⟩, tr'⟩⟩, s'⟩ hx
  have hmono : SimBaseClampInv B m sC.base ∧ CellGameClampInv B m s.2 := ⟨hBase.mono (Nat.le_succ m), hCell.mono (Nat.le_succ m)⟩
  unfold semSendTrackHalted at hx; cases href : (sC.base.stopped || sC.base.mir.win || !(noBobSendInEpoch0 sC.base.mir Q))
  · simp only [href, Bool.false_eq_true, ↓reduceIte] at hx; rcases hep : sC.base.mir.epMgmt 3 qep Q r.isSome with _ | s₁ <;> simp only [hep] at hx
    · simp only [runCellDF, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx; rcases hx with ⟨⟨_, ⟨⟨rfl, _⟩, _⟩⟩, rfl⟩; exact hmono
    · cases hch : (chal.isSome && !(s₁.safeCh 3 Q))
      · simp only [hch, Bool.false_eq_true, ↓reduceIte, runCellDF_bind, mem_support_bind_iff] at hx; obtain ⟨⟨rq, s_rq⟩, hrq, hx⟩ := hx
        have hs_rq : s_rq = s := by
          rcases r with _ | rq₀ <;> simp only [runCellDF, simulateQ_pure, StateT.run_pure, cellImplDF_liftM_probComp, mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hrq
          · obtain ⟨_, _, ⟨_, rfl⟩⟩ := hrq; rfl
          · exact hrq.2
        subst s_rq; dsimp only [] at hx; cases hcand : (stepKemFailSend P.C.F K tr Q rq).cand.isSome
        · simp only [hcand, Bool.false_eq_true, ↓reduceIte, runCellDF_bind, mem_support_bind_iff] at hx; obtain ⟨⟨rc, s_rc⟩, hrc, hx⟩ := hx
          have hs_rc : s_rc = s := by
            rcases r with _ | rq₀ <;> simp only [runCellDF, map_eq_bind_pure_comp, Function.comp_def, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, cellImplDF_liftM_probComp, bind_assoc, pure_bind, mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hrc
            · exact hrc.2
            · obtain ⟨_, _, ⟨_, rfl⟩⟩ := hrc; rfl
          subst s_rc; dsimp only [] at hx
          rcases hmk : mkPub (P := P) sC.base Q rq (if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1) else sC.base.pn Q) with _ | ⟨pq', pub⟩ <;> simp only [hmk] at hx
          · simp only [runCellDF, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx; rcases hx with ⟨⟨_, ⟨⟨rfl, _⟩, _⟩⟩, rfl⟩; exact hmono
          · rw [runCellDF_bind, mem_support_bind_iff] at hx; obtain ⟨⟨res, s_res⟩, hres, hx⟩ := hx
            have hHook : CellGameClampInv B m s_res.2 ∧ ∀ c, res = some c → c.1.1 + m + 1 ≤ B ∧ c.2.1 + m + 1 ≤ B := by
              rcases chal with _ | m₁
              · refine (deliverForgeCellSemHookClampInv P Dh encPt encT lam qep B tL tStar).onTr_inv (Q := Q) (msg := (pub, m₀)) (rc := rc) (ex := (ex, s)) hCell (res, (match res with | some c => c :: ex | none => ex, s_res)) ?_
                simp only [deliverForgeCellSemHook, deliverForgeSemHook, runCellDF_bind, bind_assoc, mem_support_bind_iff]; refine ⟨(res, s_res), hres, ?_⟩
                rcases res with _ | c <;> simp [runCellDF, simulateQ_pure, StateT.run_pure]
              · refine (deliverForgeCellSemHookClampInv P Dh encPt encT lam qep B tL tStar).onCh_inv (Q := Q) (m₀ := (pub, m₀)) (m₁ := (pub, m₁)) (rc := rc) (ex := (ex, s)) hCell (res, (match res with | some c => c :: ex | none => ex, s_res)) ?_
                simp only [deliverForgeCellSemHook, deliverForgeSemHook, runCellDF_bind, bind_assoc, mem_support_bind_iff]; refine ⟨(res, s_res), hres, ?_⟩
                rcases res with _ | c <;> simp [runCellDF, simulateQ_pure, StateT.run_pure]
            rcases res with _ | c <;> simp only [runCellDF, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
            · rcases hx with ⟨⟨_, ⟨⟨rfl, _⟩, _⟩⟩, rfl⟩; exact ⟨hBase.mono (Nat.le_succ m), hHook.1⟩
            · rcases hx with ⟨⟨_, ⟨⟨rfl, _⟩, _⟩⟩, rfl⟩; exact ⟨scPostSendPure_clampInv P Dh encPt encT lam hep m₀ chal.isSome pq' _ c hBase (hHook.2 c rfl), hHook.1⟩
        · simp only [hcand, ↓reduceIte, runCellDF, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx; rcases hx with ⟨⟨_, ⟨⟨rfl, _⟩, _⟩⟩, rfl⟩; exact hmono
      · simp only [hch, ↓reduceIte, runCellDF, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx; rcases hx with ⟨⟨_, ⟨⟨rfl, _⟩, _⟩⟩, rfl⟩; exact hmono
  · simp only [href, ↓reduceIte, runCellDF, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx; rcases hx with ⟨⟨_, ⟨⟨rfl, _⟩, _⟩⟩, rfl⟩; exact hmono

private theorem simImplCTrackHalted_dl_eq {PQ Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B : ℕ) (h232 : 2 ^ 32 ≤ B) (Q : Party) (w : Bytes)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (SimFig8C Pt)) (tr : KemFailTrackState P.C.F)
    (hep : ∀ R, sC.base.mir.epoch R + 1 ≤ B) (hch : ∀ R, ∀ g ∈ sC.base.chains R, g.epoch ≤ B) :
    let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
    runDFMTrack (simImplCTrackHalted P K encT decT qep (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
      (lFS P.C P.codec ℓ encT idOf 25000) (deliverForgeHook Pt ℓ) Dh (.inr (.inl (.inl (.inr (Q, w)))))) sC ex tr =
    (simDeliverForgeOracleTrackHalted P K Dh encPt encT decT lam qep B (.inr (.inl (.inl (.inr (Q, w)))))).run ((sC, ex), tr) := by
  have hStep := semHandleHook_deliverForge_eq (PQC := BitVec 512) P Dh encPt encT decT lam qep B (.inl (.inl (.inr (Q, w)))) sC ex (by omega) hep hch (fun _ => Or.inl h232)
  have hp : (deliverForgeSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ)).onDeliverPost = fun _ _ _ ex₁ => pure ex₁ := rfl
  unfold semHandleHook at hStep; dsimp only [simImplC, HAdd.hAdd, Add.add, QueryImpl.add, Sum.elim] at hStep
  rw [hp] at hStep; simp only [pure_bind, Prod.mk.eta, bind_pure] at hStep
  dsimp only [simImplCTrackHalted, simDeliverForgeOracleTrackHalted, HAdd.hAdd, Add.add, QueryImpl.add, Sum.elim, StateT.run, StateT.mk]
  have hget : runDFMTrack (get : StateT _ (DeliverForgeM Pt ℓ) _) sC ex tr = pure ((sC, tr), ((sC, ex), tr)) := rfl
  rw [runDFMTrack_bind]; change (runDFMTrack get sC ex tr >>= _) = _; rw [hget, pure_bind]; dsimp only []
  rw [runDFMTrack_bind]; erw [runDFMTrack_liftS (guardC _)]; rw [← hStep, bind_assoc]
  refine bind_congr fun ⟨res, sC₁, ex₁⟩ => ?_; simp only [pure_bind]
  suffices ∀ j? : Option ℕ, runDFMTrack (match res, j? with
      | some (.accepted _ _ _), some j => do
          modify fun x : LibsignalToModularSchemeSimState PQ Pt ℓ × KemFailTrackState P.C.F => (x.1, stepKemFailDeliver P.C.F K x.2 Q j)
          pure res
      | _, _ => pure res) sC₁ ex₁ tr =
    pure (res, (sC₁, ex₁), match res, j? with | some (.accepted _ _ _), some j => stepKemFailDeliver P.C.F K tr Q j | _, _ => tr) from
    this (List.findIdx? (fun wc : Bytes × SimFig8C Pt => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) sC.base.honest.reverse)
  intro j?; rcases res with _ | (_ | ⟨t', i', pm'⟩)
  · simp only [runDFMTrack, StateT.run_pure, pure_bind]
  · simp only [runDFMTrack, StateT.run_pure, pure_bind]
  · rcases j? with _ | j
    · simp only [runDFMTrack, StateT.run_pure, pure_bind]
    · have hmod : (modify (fun x : LibsignalToModularSchemeSimState PQ Pt ℓ × KemFailTrackState P.C.F =>
          (x.1, stepKemFailDeliver P.C.F K x.2 Q j)) : StateT _ (DeliverForgeM Pt ℓ) PUnit).run (sC₁, tr) =
        pure ((), (sC₁, stepKemFailDeliver P.C.F K tr Q j)) := rfl
      simp only [runDFMTrack, StateT.run_bind, hmod, pure_bind, StateT.run_pure]

private theorem simImplCTrackHalted_ij_eq {PQ Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B : ℕ) (h232 : 2 ^ 32 ≤ B) (Q : Party) (w : Bytes)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (SimFig8C Pt)) (tr : KemFailTrackState P.C.F)
    (hep : ∀ R, sC.base.mir.epoch R + 1 ≤ B) (hch : ∀ R, ∀ g ∈ sC.base.chains R, g.epoch ≤ B) :
    let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
    runDFMTrack (simImplCTrackHalted P K encT decT qep (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
      (lFS P.C P.codec ℓ encT idOf 25000) (deliverForgeHook Pt ℓ) Dh (.inr (.inl (.inr (Q, w))))) sC ex tr =
    (simDeliverForgeOracleTrackHalted P K Dh encPt encT decT lam qep B (.inr (.inl (.inr (Q, w))))).run ((sC, ex), tr) := by
  have hStep := semHandleHook_deliverForge_eq (PQC := BitVec 512) P Dh encPt encT decT lam qep B (.inl (.inr (Q, w))) sC ex (by omega) hep hch (fun _ => Or.inl h232)
  dsimp only [semHandleHook, simImplC, simImplCTrackHalted, simDeliverForgeOracleTrackHalted, HAdd.hAdd, Add.add, QueryImpl.add, Sum.elim, StateT.run, StateT.mk] at hStep ⊢
  erw [runDFMTrack_liftS (guardC _)]; rw [← hStep]

private theorem simImplCTrackHalted_cr_eq {PQ Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B : ℕ) (h232 : 2 ^ 32 ≤ B) (Q : Party)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (SimFig8C Pt)) (tr : KemFailTrackState P.C.F)
    (hep : ∀ R, sC.base.mir.epoch R + 1 ≤ B) (hch : ∀ R, ∀ g ∈ sC.base.chains R, g.epoch ≤ B) :
    let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
    runDFMTrack (simImplCTrackHalted P K encT decT qep (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
      (lFS P.C P.codec ℓ encT idOf 25000) (deliverForgeHook Pt ℓ) Dh (.inr (.inr Q))) sC ex tr =
    (simDeliverForgeOracleTrackHalted P K Dh encPt encT decT lam qep B (.inr (.inr Q))).run ((sC, ex), tr) := by
  have hStep := semHandleHook_deliverForge_eq (PQC := BitVec 512) P Dh encPt encT decT lam qep B (.inr Q) sC ex (by omega) hep hch (fun _ => Or.inl h232)
  dsimp only [semHandleHook, simImplC, simImplCTrackHalted, simDeliverForgeOracleTrackHalted, HAdd.hAdd, Add.add, QueryImpl.add, Sum.elim, StateT.run, StateT.mk] at hStep ⊢
  erw [runDFMTrack_liftS (guardC _)]; rw [← hStep]

private theorem simulateQ_runCellDF_simDeliverForgeOracleTrackHalted_eq
    {PQ Pt α : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B : ℕ) (tL : Option ℕ) (tStar : ℕ) (h232 : 2 ^ 32 ≤ B)
    (oa : OracleComp (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes) α) (m : ℕ)
    (hm : oa.IsQueryBoundP (isGameQuery (G := CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes)) m)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (SimFig8C Pt))
    (tr : KemFailTrackState P.C.F) (s : CellState Pt ℓ) (hInv : SimBaseClampInv B m sC.base ∧ CellGameClampInv B m s.2) :
    runCellDF P Dh encPt encT lam qep tL tStar ((simulateQ (simDeliverForgeOracleTrackHalted P K Dh encPt encT decT lam qep B) oa).run ((sC, ex), tr)) s =
      let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
      runCellDF P Dh encPt encT lam qep tL tStar (runDFMTrack (simulateQ (simImplCTrackHalted P K encT decT qep (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (lFS P.C P.codec ℓ encT idOf 25000) (deliverForgeHook Pt ℓ) Dh) oa) sC ex tr) s := by
  dsimp only []
  let idOf0 : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf0 25000 lam
  let cellHook := deliverForgeCellSemHook (ℓ := ℓ) P Dh encPt encT lam qep tL tStar
  have hHookInv := deliverForgeCellSemHookClampInv (ℓ := ℓ) P Dh encPt encT lam qep B tL tStar
  induction oa using OracleComp.inductionOn generalizing m sC ex tr s with
  | pure a => simp only [runCellDF, runDFMTrack, simulateQ_pure, StateT.run_pure, pure_bind]
  | query_bind qy u ih =>
    rw [isQueryBoundP_query_bind_iff] at hm; rcases hm with ⟨hq0, hu⟩
    rw [simulateQ_query_bind, simulateQ_query_bind, StateT.run_bind, runDFMTrack_bind, runCellDF_bind, runCellDF_bind]
    dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift, MonadLift.monadLift]
    rcases qy with n | t
    · simp only [isGameQuery, ↓reduceIte] at hu
      rw [← simDeliverForgeOracleTrackHalted_inl_eq P K Dh encPt encT decT lam qep B n sC ex tr]
      refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨r, ⟨⟨sC', ex'⟩, tr'⟩⟩, s'⟩ hmem => ?_
      rw [runCellDF_simDeliverForgeOracleTrackHalted_inl] at hmem
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      obtain ⟨_, _, ⟨_, ⟨⟨rfl, rfl⟩, rfl⟩⟩, rfl⟩ := hmem; exact ih r m (hu r) _ _ _ _ hInv
    · simp only [isGameQuery, ↓reduceIte] at hq0 hu
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by have := hq0.resolve_left (by decide); omega⟩
      have hep : ∀ R, sC.base.mir.epoch R + 1 ≤ B := fun R => by have := hInv.1.hep R; omega
      have hch : ∀ R, ∀ g ∈ sC.base.chains R, g.epoch ≤ B := fun R g hg => by have := hInv.1.hch R g hg; omega
      rcases t with ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
      · change (runCellDF P Dh encPt encT lam qep tL tStar (semSendTrackHalted P K Dh encPt encT lam qep sC ex tr Q m₀ none r) s >>= _) =
          (runCellDF P Dh encPt encT lam qep tL tStar (runDFMTrack (simSendCTrackHalted P K qep fig (deliverForgeHook Pt ℓ) Q m₀ none r) sC ex tr) s >>= _)
        rw [← semSendTrackHalted_deliverForge_eq]
        exact OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨res, ⟨⟨sC', ex'⟩, tr'⟩⟩, s'⟩ hmem =>
          ih res m' (by simpa using hu res) sC' ex' tr' s' (semSendTrackHalted_preserves_clampInv P K Dh encPt encT lam qep B m' tL tStar sC ex tr s Q m₀ none r hInv.1 hInv.2 _ hmem)
      · change (runCellDF P Dh encPt encT lam qep tL tStar (semSendTrackHalted P K Dh encPt encT lam qep sC ex tr Q m₀ (some m₁) r) s >>= _) =
          (runCellDF P Dh encPt encT lam qep tL tStar (runDFMTrack (simSendCTrackHalted P K qep fig (deliverForgeHook Pt ℓ) Q m₀ (some m₁) r) sC ex tr) s >>= _)
        rw [← semSendTrackHalted_deliverForge_eq]
        exact OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨res, ⟨⟨sC', ex'⟩, tr'⟩⟩, s'⟩ hmem =>
          ih res m' (by simpa using hu res) sC' ex' tr' s' (semSendTrackHalted_preserves_clampInv P K Dh encPt encT lam qep B m' tL tStar sC ex tr s Q m₀ (some m₁) r hInv.1 hInv.2 _ hmem)
      · rw [simImplCTrackHalted_dl_eq P K Dh encPt encT decT lam qep B h232 Q w sC ex tr hep hch]
        refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨res, ⟨⟨sC', ex'⟩, tr'⟩⟩, s'⟩ hmem => ?_
        dsimp only [simDeliverForgeOracleTrackHalted, StateT.run, StateT.mk] at hmem
        rw [runCellDF_bind, mem_support_bind_iff] at hmem; obtain ⟨⟨⟨res₁, sC₁, ex₁⟩, s₁⟩, hrec, htail⟩ := hmem
        simp only [runCellDF, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at htail
        rcases htail with ⟨⟨h1, ⟨h2, h3⟩, _⟩, h5⟩; subst res sC' ex' s'
        have hmem' : (res₁, (sC₁, (ex₁, s₁))) ∈ support (semRecvHook P Dh encPt encT decT lam cellHook qep B sC (ex, s) Q w true) := by
          rw [← runCellDF_semRecvHook, support_map]; exact ⟨((res₁, (sC₁, ex₁)), s₁), hrec, rfl⟩
        exact ih res₁ m' (by simpa using hu res₁) sC₁ ex₁ tr' s₁ (semRecvHook_preserves_clampInv P Dh encPt encT decT lam hHookInv m' qep h232 sC (ex, s) Q w true hInv.1 hInv.2 _ hmem')
      · rw [simImplCTrackHalted_ij_eq P K Dh encPt encT decT lam qep B h232 Q w sC ex tr hep hch]
        refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨res, ⟨⟨sC', ex'⟩, tr'⟩⟩, s'⟩ hmem => ?_
        dsimp only [simDeliverForgeOracleTrackHalted, StateT.run, StateT.mk] at hmem
        rw [runCellDF_bind, mem_support_bind_iff] at hmem; obtain ⟨⟨⟨res₁, sC₁, ex₁⟩, s₁⟩, hrec, htail⟩ := hmem
        simp only [runCellDF, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at htail
        rcases htail with ⟨⟨h1, ⟨h2, h3⟩, h4⟩, h5⟩; subst res sC' ex' tr' s'
        have hmem' : (res₁, (sC₁, (ex₁, s₁))) ∈ support (semRecvHook P Dh encPt encT decT lam cellHook qep B sC (ex, s) Q w false) := by
          rw [← runCellDF_semRecvHook, support_map]; exact ⟨((res₁, (sC₁, ex₁)), s₁), hrec, rfl⟩
        exact ih res₁ m' (by simpa using hu res₁) sC₁ ex₁ tr s₁ (semRecvHook_preserves_clampInv P Dh encPt encT decT lam hHookInv m' qep h232 sC (ex, s) Q w false hInv.1 hInv.2 _ hmem')
      · rw [simImplCTrackHalted_cr_eq P K Dh encPt encT decT lam qep B h232 Q sC ex tr hep hch]
        refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨res, ⟨⟨sC', ex'⟩, tr'⟩⟩, s'⟩ hmem => ?_
        dsimp only [simDeliverForgeOracleTrackHalted, StateT.run, StateT.mk] at hmem
        rw [runCellDF_bind, mem_support_bind_iff] at hmem; obtain ⟨⟨⟨res₁, sC₁, ex₁⟩, s₁⟩, hrec, htail⟩ := hmem
        simp only [runCellDF, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at htail
        rcases htail with ⟨⟨h1, ⟨h2, h3⟩, h4⟩, h5⟩; subst res sC' ex' tr' s'
        have hmem' : (res₁, (sC₁, (ex₁, s₁))) ∈ support (semCorrHook P Dh encT cellHook sC (ex, s) Q) := by
          rw [← runCellDF_semCorrHook, support_map]; exact ⟨((res₁, (sC₁, ex₁)), s₁), hrec, rfl⟩
        exact ih res₁ m' (by simpa using hu res₁) sC₁ ex₁ tr s₁ (semCorrHook_preserves_clampInv P Dh encT hHookInv m' sC (ex, s) Q hInv.1 hInv.2 _ hmem')

theorem runBaseDFCellTPaper_challSimDF'Paper_simDeliverForgeClampTrackHalted_eq
    {PQ Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep : ℕ) (tL : Option ℕ) (t : ℕ) (idOf : Party → IdentityKey)
    (hid : idOf = fun R => if R == Party.A then P.idA else P.idB)
    (A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes)
    (q : ℕ) (hq : CryptoGames.SM.MakesAtMostQueries A q)
    (hq32 : 2 * (q + 1) + 25002 < 2 ^ 32) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    runBaseDFCellTPaper fig (qep + 1) tL t sameHdrScheme (Config.auth t) false
        (challSimDF'Paper (2 + 1) (qep + 1)
          (simDeliverForgeClampTrackHalted P K Dh encPt encT decT lam qep (2 ^ 32) A)) =
      runBaseDFCellTPaper fig (qep + 1) tL t sameHdrScheme (Config.auth t) false
        (challSimDF'Paper (2 + 1) (qep + 1)
          (simDeliverForgeTrackHalted P K ℓ Dh encPt encT decT idOf lam qep A)) := by
  subst hid; dsimp only []
  have hqB : q + 3 ≤ 2 ^ 32 := by omega
  have hq' := (makesAtMostQueries_iff_isGameQuery A q).mp hq
  rw [runBaseDFCellTPaper_challSimDF'Paper_eq_runCellDF, runBaseDFCellTPaper_challSimDF'Paper_eq_runCellDF]
  refine bind_congr fun k => bind_congr fun b => ?_
  rw [simDeliverForgeTrackHalted_eq_bind_runDFMTrack P K Dh encPt encT decT lam qep _ rfl A]
  unfold simDeliverForgeClampTrackHalted
  simp only [StateT.run'_eq, map_eq_bind_pure_comp, Function.comp_def, runCellDF_bind, bind_assoc]
  simp only [runCellDF, cellImplDF_liftM_probComp, simulateQ_pure, StateT.run_pure, bind_assoc, pure_bind]
  refine bind_congr fun pqrKey => ?_
  let idOf0 : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf0 25000 lam
  let mir₀ : Mirror (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt) := { st := fun _ => (), b := b }
  let gs₀ := initState fig k false
  let sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ :=
    initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)
  let tr₀ := initKemFailTrack P.C.F pqrKey
  have hSim := simulateQ_runCellDF_simDeliverForgeOracleTrackHalted_eq P K Dh encPt encT decT lam
    qep (2 ^ 32) tL t (Nat.le_refl _) A q hq' sC₀ [] tr₀ (mir₀, gs₀)
    ⟨simBaseClampInv_init (2 ^ 32) q _ _ hqB, cellGameClampInv_init P Dh encPt encT lam idOf0 (2 ^ 32) q k false hqB⟩
  unfold runCellDF at hSim; rw [hSim]

/-- End-to-end `forgeGuessedAdvantageCellPaper` equality coupling
`simDeliverForgeClampSanQTrackHalted` directly to `Refinement.simDeliverForgeTrackHalted`. -/
theorem forgeGuessedAdvantageCellPaper_challSimDF'Paper_simDeliverForgeClampSanQTrackHalted_eq
    {PQ Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    (P : Params PQ (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) (tL : Option ℕ) (t : ℕ) (idOf : Party → IdentityKey)
    (hid : idOf = fun R => if R == Party.A then P.idA else P.idB)
    (A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes)
    (hq : CryptoGames.SM.MakesAtMostQueries A q)
    (hq32 : 2 * (q + 1) + 25002 < 2 ^ 32) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    forgeGuessedAdvantageCellPaper fig (qep + 1) sameHdrScheme tL t
        (challSimDF'Paper (2 + 1) (qep + 1)
          (simDeliverForgeClampSanQTrackHalted P K ℓ Dh encPt encT decT lam qep q A)) =
      forgeGuessedAdvantageCellPaper fig (qep + 1) sameHdrScheme tL t
        (challSimDF'Paper (2 + 1) (qep + 1)
          (simDeliverForgeTrackHalted P K ℓ Dh encPt encT decT idOf lam qep A)) := by
  dsimp only [simDeliverForgeClampSanQTrackHalted]
  rw [forgeGuessedAdvantageCellPaperT_eq_runBaseDFCellTPaper,
    runBaseDFCellTPaper_challSimDF'Paper_simDeliverForgeClampSanTrackHalted_eq
      P K Dh encPt encT decT lam qep (2 ^ 32) (50000 * q) (25001 * q + 25000) (25000 * q)
      tL t idOf hid A q hq (by omega) (by omega) (by omega),
    runBaseDFCellTPaper_challSimDF'Paper_simDeliverForgeClampTrackHalted_eq
      P K Dh encPt encT decT lam qep tL t idOf hid A q hq hq32,
    ← forgeGuessedAdvantageCellPaperT_eq_runBaseDFCellTPaper]

section BucketTrackHalted

private theorem runBucketDF_drawRq {PQ Pt α : Type} [DecidableEq Pt] [Zero Pt] {ℓ qep : ℕ} {tL : Option ℕ} {par : Bool}
    (P : Params PQ (BitVec 512)) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt)
    (r : Option (BitVec 512)) (k : BitVec 512 → AdversaryCompDF (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt) α)
    (ms : BucketState Pt ℓ) {x : α × BucketState Pt ℓ}
    (hx : x ∈ support (runBucketDF P Dh encPt encT lam qep tL par ((match r with | some rq => pure rq | none => liftM ($ᵗ (BitVec 512) : ProbComp (BitVec 512))) >>= k) ms)) :
    ∃ rq, x ∈ support (runBucketDF P Dh encPt encT lam qep tL par (k rq) ms) := by
  cases r with
  | some rq => rw [pure_bind] at hx; exact ⟨rq, hx⟩
  | none => dsimp only [runBucketDF] at hx ⊢; simp only [simulateQ_bind, StateT.run_bind, bucketImplDF_liftM_probComp, bind_assoc, pure_bind, mem_support_bind_iff] at hx; obtain ⟨rq, -, hx⟩ := hx; exact ⟨rq, hx⟩

private theorem runBucketDF_drawRc {PQ Pt α : Type} [DecidableEq Pt] [Zero Pt] {ℓ qep : ℕ} {tL : Option ℕ} {par : Bool}
    (P : Params PQ (BitVec 512)) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt)
    (r : Option (BitVec 512)) (k : Option (BitVec 256) → AdversaryCompDF (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt) α)
    (ms : BucketState Pt ℓ) {x : α × BucketState Pt ℓ}
    (hx : x ∈ support (runBucketDF P Dh encPt encT lam qep tL par ((match r with | some _ => some <$> (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256))) | none => pure none) >>= k) ms)) :
    ∃ rc, x ∈ support (runBucketDF P Dh encPt encT lam qep tL par (k rc) ms) := by
  cases r with
  | none => rw [pure_bind] at hx; exact ⟨none, hx⟩
  | some _ => dsimp only [runBucketDF] at hx ⊢; simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind, simulateQ_bind, StateT.run_bind, bucketImplDF_liftM_probComp, mem_support_bind_iff] at hx; obtain ⟨rc, -, hx⟩ := hx; exact ⟨some rc, hx⟩

private theorem semSendTrackHalted_bucket_dfSanInv {PQ Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ q m qep : ℕ} {tL : Option ℕ} {par : Bool}
    (P : Params PQ (BitVec 512)) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt) (K : MlKem)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (Fig8C Pt)) (tr : KemFailTrackState P.C.F) (ms : BucketState Pt ℓ)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option (BitVec 512)) (hInv : DFBucketSanInv q (m + 1) sC ms) :
    ∀ x ∈ support (runBucketDF P Dh encPt encT lam qep tL par (semSendTrackHalted P K Dh encPt encT lam qep sC ex tr Q m₀ chal r) ms),
      DFBucketSanInv q m x.1.2.1.1 x.2 := by
  rintro ⟨⟨out₁, ⟨sC₁, ex₁⟩, tr₁⟩, ms₁⟩ hx; have hm1 : m + 1 ≤ q := hInv.hgame.hm; have hInv0 := hInv.mono (Nat.le_succ m)
  unfold semSendTrackHalted at hx
  by_cases href : (sC.base.stopped || sC.base.mir.win || !noBobSendInEpoch0 sC.base.mir Q) = true
  · simp only [href, ↓reduceIte, runBucketDF, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx; rcases hx with ⟨⟨_, ⟨rfl, _⟩, _⟩, rfl⟩; exact hInv0
  · simp only [href, Bool.false_eq_true, ↓reduceIte] at hx; rcases hep : sC.base.mir.epMgmt 3 qep Q r.isSome with _ | s₁ <;> simp only [hep] at hx
    · simp only [runBucketDF, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx; rcases hx with ⟨⟨_, ⟨rfl, _⟩, _⟩, rfl⟩; exact hInv0
    · by_cases hch : (chal.isSome && !s₁.safeCh 3 Q) = true
      · simp only [hch, ↓reduceIte, runBucketDF, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx; rcases hx with ⟨⟨_, ⟨rfl, _⟩, _⟩, rfl⟩; exact hInv0
      · simp only [hch, Bool.false_eq_true, ↓reduceIte] at hx; obtain ⟨rq, hx⟩ := runBucketDF_drawRq P Dh encPt encT lam r _ ms hx
        by_cases hcand : (stepKemFailSend P.C.F K tr Q rq).cand.isSome = true
        · simp only [hcand, ↓reduceIte, runBucketDF, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx; rcases hx with ⟨⟨_, ⟨rfl, _⟩, _⟩, rfl⟩; exact hInv0
        · simp only [hcand, Bool.false_eq_true, ↓reduceIte] at hx; obtain ⟨rc, hx⟩ := runBucketDF_drawRc P Dh encPt encT lam r _ ms hx
          rcases hmk : mkPub (P := P) sC.base Q rq (if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1) else sC.base.pn Q) with _ | ⟨pq', pub⟩ <;> simp only [hmk] at hx
          · simp only [runBucketDF, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx; rcases hx with ⟨⟨_, ⟨rfl, _⟩, _⟩, rfl⟩; exact hInv0
          · have hpost : ∀ (c : Fig8C Pt), GameSanInv q m ms₁.2.1 → c.2.1 ≤ q - m →
                sC₁ = scPostSendPure P Dh encPt encT lam sC s₁ Q m₀ chal.isSome pq' (if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1) else sC.base.pn Q) c → DFBucketSanInv q m sC₁ ms₁ := by
              intro c hg' hc hsC₁; subst hsC₁; refine ⟨hg', ?_, hInv0.hchains, ?_⟩
              · intro R; unfold scPostSendPure; by_cases hR : R = Q
                · subst hR; simp only [Function.update_self]; exact (keptInv_send (hInv.hkept R)).mono (Nat.mul_le_mul_left 25000 (by omega))
                · simp only [Function.update_of_ne hR]; exact hInv0.hkept R
              · intro wc hwc; unfold scPostSendPure at hwc; rcases List.mem_cons.mp hwc with rfl | hwc
                · exact hc
                · exact hInv0.hhonest wc hwc
            cases chal with
            | none =>
              simp only [runBucketDF, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hx; obtain ⟨⟨res, ms'⟩, htr, hEq⟩ := hx
              obtain ⟨hg', hc⟩ := runBucketDF_transmitQueryDF_inv P Dh encPt encT lam Q (pub, m₀) rc ms ms' res hInv.hgame htr
              rcases res with _ | c <;> simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hEq
              · rcases hEq with ⟨⟨_, ⟨rfl, _⟩, _⟩, rfl⟩; exact ⟨hg', hInv0.hkept, hInv0.hchains, hInv0.hhonest⟩
              · rcases hEq with ⟨⟨_, ⟨hsC₁, _⟩, _⟩, rfl⟩; exact hpost c hg' (hc c rfl) hsC₁
            | some m₁ =>
              simp only [runBucketDF, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hx; obtain ⟨⟨res, ms'⟩, hch', hEq⟩ := hx
              obtain ⟨hg', hc⟩ := runBucketDF_challQueryDF_inv P Dh encPt encT lam Q (pub, m₀) (pub, m₁) rc ms ms' res hInv.hgame hch'
              rcases res with _ | c <;> simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hEq
              · rcases hEq with ⟨⟨_, ⟨rfl, _⟩, _⟩, rfl⟩; exact ⟨hg', hInv0.hkept, hInv0.hchains, hInv0.hhonest⟩
              · rcases hEq with ⟨⟨_, ⟨hsC₁, _⟩, _⟩, rfl⟩; exact hpost c hg' (hc c rfl) hsC₁

private theorem simDeliverForgeOracleDedupTrackHalted_step_bucket_dfSanInv {PQ Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ q m qep : ℕ} {tL : Option ℕ} {par : Bool}
    (P : Params PQ (BitVec 512)) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt)
    (K : MlKem) (decT : PublicKey → Option Pt) (B : ℕ) (t : (CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (Fig8C Pt)) (tr : KemFailTrackState P.C.F) (ms : BucketState Pt ℓ) (hInv : DFBucketSanInv q (m + 1) sC ms) :
    ∀ x ∈ support (runBucketDF P Dh encPt encT lam qep tL par ((simDeliverForgeOracleDedupTrackHalted P K Dh encPt encT decT lam qep B (.inr t)).run ((sC, ex), tr)) ms),
      DFBucketSanInv q m x.1.2.1.1 x.2 := by
  rcases t with ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · exact semSendTrackHalted_bucket_dfSanInv P Dh encPt encT lam K sC ex tr ms Q m₀ none r hInv
  · exact semSendTrackHalted_bucket_dfSanInv P Dh encPt encT lam K sC ex tr ms Q m₀ (some m₁) r hInv
  · rintro ⟨⟨_, ⟨sC₁, ex₁⟩, _⟩, ms₁⟩ hx; unfold runBucketDF at hx; dsimp only [simDeliverForgeOracleDedupTrackHalted] at hx
    simp only [StateT.run_mk, simulateQ_bind, StateT.run_bind, mem_support_bind_iff, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    obtain ⟨⟨⟨_, _, _⟩, _⟩, hrec, ⟨_, ⟨rfl, rfl⟩, _⟩, rfl⟩ := hx; exact semRecvHook_bucket_dfSanInv P Dh encPt encT lam decT B sC ex ms Q w true hInv _ hrec
  · rintro ⟨⟨_, ⟨sC₁, ex₁⟩, _⟩, ms₁⟩ hx; unfold runBucketDF at hx; dsimp only [simDeliverForgeOracleDedupTrackHalted] at hx
    simp only [StateT.run_mk, simulateQ_bind, StateT.run_bind, mem_support_bind_iff, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    obtain ⟨⟨⟨_, _, _⟩, _⟩, hrec, ⟨_, ⟨rfl, rfl⟩, _⟩, rfl⟩ := hx; exact semRecvHook_bucket_dfSanInv P Dh encPt encT lam decT B sC ex ms Q w false hInv _ hrec
  · rintro ⟨⟨_, ⟨sC₁, ex₁⟩, _⟩, ms₁⟩ hx; unfold runBucketDF at hx; dsimp only [simDeliverForgeOracleDedupTrackHalted] at hx
    simp only [StateT.run_mk, simulateQ_bind, StateT.run_bind, mem_support_bind_iff, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    obtain ⟨⟨⟨_, _, _⟩, _⟩, hcor, ⟨_, ⟨rfl, rfl⟩, _⟩, rfl⟩ := hx; exact semCorrHookDedup_bucket_dfSanInv P Dh encPt encT lam sC ex ms Q hInv _ hcor

private theorem simulateQ_runBucketDF_simDeliverForgeOracleSanTrackHalted_eq {PQ Pt α : Type} [DecidableEq Pt] [Zero Pt] {ℓ q qep : ℕ} {tL : Option ℕ} {par : Bool}
    (P : Params PQ (BitVec 512)) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt)
    (K : MlKem) (decT : PublicKey → Option Pt) (B T Kc Bsk : ℕ)
    (oa : OracleComp (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes) α) (m : ℕ)
    (hq : oa.IsQueryBoundP (isGameQuery (G := CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes)) m)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (Fig8C Pt)) (tr : KemFailTrackState P.C.F) (ms : BucketState Pt ℓ)
    (hT : 25000 * q ≤ T) (hKc : 25001 * q + 25000 ≤ Kc) (hBsk : 25000 * q ≤ Bsk) (hInv : DFBucketSanInv q m sC ms) :
    runBucketDF P Dh encPt encT lam qep tL par ((simulateQ (simDeliverForgeOracleSanTrackHalted P K Dh encPt encT decT lam qep B T Kc Bsk) oa).run ((sC, ex), tr)) ms =
      runBucketDF P Dh encPt encT lam qep tL par ((simulateQ (simDeliverForgeOracleDedupTrackHalted P K Dh encPt encT decT lam qep B) oa).run ((sC, ex), tr)) ms := by
  refine simulateQ_runBucketDF_eq_of_inv P Dh encPt encT lam _ _ (fun st => st.1.1) (fun _ => rfl) (fun _ => rfl)
    (fun m' t st ms hInv' => ?_)
    (fun m' t st ms hInv' => simDeliverForgeOracleDedupTrackHalted_step_bucket_dfSanInv P Dh encPt encT lam K decT B t st.1.1 st.1.2 st.2 ms hInv')
    oa m hq ((sC, ex), tr) ms hInv
  rcases st with ⟨⟨sC, ex⟩, tr⟩; have hm1 : m' + 1 ≤ q := hInv'.hgame.hm
  rcases t with ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · rfl
  · rfl
  · have hdl := simDeliverForgeOracleSan_inr_inl_eq P Dh encPt encT decT lam qep (.inl (.inr (Q, w))) (sC, ex)
      (B0 := 25000 * (q - (m' + 1))) (T := T) (Kc := Kc) (Bsk := Bsk) (B := B) (by omega) hInv'.hkept (by omega) (fun R g hg => by have := hInv'.hchains R g hg; omega)
    have hpost : (deliverForgeSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ)).onDeliverPost = fun _ _ _ ex' => pure ex' := rfl
    dsimp only [simDeliverForgeOracleSan, simDeliverForgeOracleDedup, StateT.run, StateT.mk] at hdl
    unfold semHandleHookDedupS semHandleHookDedup at hdl; dsimp only [] at hdl; rw [hpost] at hdl; simp only [pure_bind, Prod.mk.eta, bind_pure] at hdl
    dsimp only [simDeliverForgeOracleSanTrackHalted, simDeliverForgeOracleDedupTrackHalted, StateT.run, StateT.mk]; rw [hdl]; rfl
  · have hij := simDeliverForgeOracleSan_inr_inl_eq P Dh encPt encT decT lam qep (.inr (Q, w)) (sC, ex)
      (B0 := 25000 * (q - (m' + 1))) (T := T) (Kc := Kc) (Bsk := Bsk) (B := B) (by omega) hInv'.hkept (by omega) (fun R g hg => by have := hInv'.hchains R g hg; omega)
    dsimp only [simDeliverForgeOracleSan, simDeliverForgeOracleDedup, semHandleHookDedupS, semHandleHookDedup, StateT.run, StateT.mk] at hij
    dsimp only [simDeliverForgeOracleSanTrackHalted, simDeliverForgeOracleDedupTrackHalted, StateT.run, StateT.mk]; rw [hij]
  · unfold runBucketDF; dsimp only [simDeliverForgeOracleSanTrackHalted, simDeliverForgeOracleDedupTrackHalted]; simp only [StateT.run_mk]
    rw [simulateQ_bind, StateT.run_bind, simulateQ_bind, StateT.run_bind]; congr 1
    exact simDeliverForgeOracleSan_inr_inr_eq_of_support P Dh encPt encT decT lam qep Q (sC, ex) (bucketImplDF P Dh encPt encT lam qep tL par) ms (T := T) (Kc := Kc) (Bsk := Bsk) (B := B)
      fun x hx fig8st hres t_ep v hv => by
        rcases x with ⟨⟨res, ex'⟩, ms'⟩; obtain ⟨-, hst_eq⟩ := runBucketDF_onCr_inv P Dh encPt encT lam Q ex ex' ms ms' res hInv'.hgame hx
        rw [hst_eq fig8st hres] at hv; exact ((hInv'.hgame.hparty Q).2 t_ep v hv).mono (by omega)

private theorem forgeGameBucketPaper_challSimDF'Paper_simDeliverForgeClampSanTrackHalted_eq {PQ Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B T Kc Bsk : ℕ) (tL : Option ℕ) (par : Bool) (idOf : Party → IdentityKey)
    (hid : idOf = fun R => if R == Party.A then P.idA else P.idB) (A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes)
    (q : ℕ) (hq : CryptoGames.SM.MakesAtMostQueries A q) (hT : 25000 * q ≤ T) (hKc : 25001 * q + 25000 ≤ Kc) (hBsk : 25000 * q ≤ Bsk) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    forgeGameBucketPaper fig 1 (qep + 1) sameHdrScheme tL par (challSimDF'Paper (2 + 1) (qep + 1) (simDeliverForgeClampSanTrackHalted P K ℓ Dh encPt encT decT lam qep B T Kc Bsk A)) =
      forgeGameBucketPaper fig 1 (qep + 1) sameHdrScheme tL par (challSimDF'Paper (2 + 1) (qep + 1) (simDeliverForgeClampTrackHalted P K Dh encPt encT decT lam qep B A)) := by
  subst hid; dsimp only []
  have hDedup : simDeliverForgeClampDedupTrackHalted P K Dh encPt encT decT lam qep B A = simDeliverForgeClampTrackHalted P K Dh encPt encT decT lam qep B A := by
    unfold simDeliverForgeClampDedupTrackHalted simDeliverForgeClampTrackHalted
    exact bind_congr fun pqrKey => run'_simulateQ_simDeliverForgeOracleDedupTrackHalted_eq P K Dh encPt encT decT lam qep B A _
  rw [← hDedup, forgeGameBucketPaper_challSimDF'Paper_eq_runBucketDF, forgeGameBucketPaper_challSimDF'Paper_eq_runBucketDF]
  refine bind_congr fun k => bind_congr fun b => ?_
  unfold simDeliverForgeClampSanTrackHalted simDeliverForgeClampDedupTrackHalted
  simp only [runBucketDF, simulateQ_bind, StateT.run_bind, bucketImplDF_liftM_probComp, StateT.run'_eq, map_eq_bind_pure_comp, Function.comp_def, simulateQ_pure, StateT.run_pure, bind_assoc, pure_bind]
  refine bind_congr fun pqrKey => ?_
  have h1 := simulateQ_runBucketDF_simDeliverForgeOracleSanTrackHalted_eq (q := q) (qep := qep) (tL := tL) (par := par) P Dh encPt encT lam K decT B T Kc Bsk A q
    ((makesAtMostQueries_iff_isGameQuery A q).mp hq) (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)) [] (initKemFailTrack P.C.F pqrKey)
    ({ st := fun _ => (), b := b }, (initState _ k false, none)) hT hKc hBsk (dfBucketSanInv_init P Dh encPt encT lam q k pqrKey false b none)
  dsimp only [runBucketDF] at h1; rw [h1]

private theorem runBucketDF_simDeliverForgeOracleTrackHalted_inl {PQ Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B : ℕ) (tL : Option ℕ) (par : Bool) (n : unifSpec.Domain)
    (st : (LibsignalToModularSchemeSimState PQ Pt ℓ × List (Fig8C Pt)) × KemFailTrackState P.C.F) (s : BucketState Pt ℓ) :
    runBucketDF P Dh encPt encT lam qep tL par ((simDeliverForgeOracleTrackHalted P K Dh encPt encT decT lam qep B (.inl n)).run st) s =
      (query (spec := unifSpec) n >>= fun r => pure ((r, st), s)) := by
  change (bucketImplDF P Dh encPt encT lam qep tL par (.inl n) s >>= fun ⟨r, s₁⟩ => pure ((r, st), s₁)) = _
  rw [bucketImplDF_inl]; simp only [bind_assoc, pure_bind]

private theorem semSendTrackHalted_bucket_preserves_clampInv {PQ Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt)
    (qep B m : ℕ) (tL : Option ℕ) (par : Bool) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (SimFig8C Pt))
    (tr : KemFailTrackState P.C.F) (s : BucketState Pt ℓ) (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option (BitVec 512))
    (hBase : SimBaseClampInv B (m + 1) sC.base) (hCell : CellGameClampInv B (m + 1) s.2.1) :
    ∀ x ∈ support (runBucketDF P Dh encPt encT lam qep tL par (semSendTrackHalted P K Dh encPt encT lam qep sC ex tr Q m₀ chal r) s),
      SimBaseClampInv B m x.1.2.1.1.base ∧ CellGameClampInv B m x.2.2.1 := by
  rintro ⟨⟨w?, ⟨⟨sC', ex'⟩, tr'⟩⟩, s'⟩ hx
  have hmono : SimBaseClampInv B m sC.base ∧ CellGameClampInv B m s.2.1 := ⟨hBase.mono (Nat.le_succ m), hCell.mono (Nat.le_succ m)⟩
  unfold semSendTrackHalted at hx
  cases href : (sC.base.stopped || sC.base.mir.win || !(noBobSendInEpoch0 sC.base.mir Q))
  · simp only [href, Bool.false_eq_true, ↓reduceIte] at hx; rcases hep : sC.base.mir.epMgmt 3 qep Q r.isSome with _ | s₁ <;> simp only [hep] at hx
    · simp only [runBucketDF, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx; rcases hx with ⟨⟨_, ⟨⟨rfl, _⟩, _⟩⟩, rfl⟩; exact hmono
    · cases hch : (chal.isSome && !(s₁.safeCh 3 Q))
      · simp only [hch, Bool.false_eq_true, ↓reduceIte, runBucketDF_bind, mem_support_bind_iff] at hx; obtain ⟨⟨rq, s_rq⟩, hrq, hx⟩ := hx
        have hs_rq : s_rq = s := by
          rcases r with _ | rq₀ <;> simp only [runBucketDF, simulateQ_pure, StateT.run_pure, bucketImplDF_liftM_probComp, mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hrq
          · obtain ⟨_, _, ⟨_, rfl⟩⟩ := hrq; rfl
          · exact hrq.2
        subst s_rq; dsimp only [] at hx; cases hcand : (stepKemFailSend P.C.F K tr Q rq).cand.isSome
        · simp only [hcand, Bool.false_eq_true, ↓reduceIte, runBucketDF_bind, mem_support_bind_iff] at hx; obtain ⟨⟨rc, s_rc⟩, hrc, hx⟩ := hx
          have hs_rc : s_rc = s := by
            rcases r with _ | rq₀ <;> simp only [runBucketDF, map_eq_bind_pure_comp, Function.comp_def, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, bucketImplDF_liftM_probComp, bind_assoc, pure_bind, mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hrc
            · exact hrc.2
            · obtain ⟨_, _, ⟨_, rfl⟩⟩ := hrc; rfl
          subst s_rc; dsimp only [] at hx
          rcases hmk : mkPub (P := P) sC.base Q rq (if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1) else sC.base.pn Q) with _ | ⟨pq', pub⟩ <;> simp only [hmk] at hx
          · simp only [runBucketDF, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx; rcases hx with ⟨⟨_, ⟨⟨rfl, _⟩, _⟩⟩, rfl⟩; exact hmono
          · rw [runBucketDF_bind, mem_support_bind_iff] at hx; obtain ⟨⟨res, s_res⟩, hres, hx⟩ := hx
            have hHook : CellGameClampInv B m s_res.2.1 ∧ ∀ c, res = some c → c.1.1 + m + 1 ≤ B ∧ c.2.1 + m + 1 ≤ B := by
              rcases chal with _ | m₁
              · refine (deliverForgeBucketSemHookClampInv P Dh encPt encT lam qep B tL par).onTr_inv (Q := Q) (msg := (pub, m₀)) (rc := rc) (ex := (ex, s)) hCell (res, (match res with | some c => c :: ex | none => ex, s_res)) ?_
                simp only [deliverForgeBucketSemHook, deliverForgeSemHook, runBucketDF_bind, bind_assoc, mem_support_bind_iff]; refine ⟨(res, s_res), hres, ?_⟩
                rcases res with _ | c <;> simp [runBucketDF, simulateQ_pure, StateT.run_pure]
              · refine (deliverForgeBucketSemHookClampInv P Dh encPt encT lam qep B tL par).onCh_inv (Q := Q) (m₀ := (pub, m₀)) (m₁ := (pub, m₁)) (rc := rc) (ex := (ex, s)) hCell (res, (match res with | some c => c :: ex | none => ex, s_res)) ?_
                simp only [deliverForgeBucketSemHook, deliverForgeSemHook, runBucketDF_bind, bind_assoc, mem_support_bind_iff]; refine ⟨(res, s_res), hres, ?_⟩
                rcases res with _ | c <;> simp [runBucketDF, simulateQ_pure, StateT.run_pure]
            rcases res with _ | c <;> simp only [runBucketDF, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
            · rcases hx with ⟨⟨_, ⟨⟨rfl, _⟩, _⟩⟩, rfl⟩; exact ⟨hBase.mono (Nat.le_succ m), hHook.1⟩
            · rcases hx with ⟨⟨_, ⟨⟨rfl, _⟩, _⟩⟩, rfl⟩; exact ⟨scPostSendPure_clampInv P Dh encPt encT lam hep m₀ chal.isSome pq' _ c hBase (hHook.2 c rfl), hHook.1⟩
        · simp only [hcand, ↓reduceIte, runBucketDF, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx; rcases hx with ⟨⟨_, ⟨⟨rfl, _⟩, _⟩⟩, rfl⟩; exact hmono
      · simp only [hch, ↓reduceIte, runBucketDF, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx; rcases hx with ⟨⟨_, ⟨⟨rfl, _⟩, _⟩⟩, rfl⟩; exact hmono
  · simp only [href, ↓reduceIte, runBucketDF, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx; rcases hx with ⟨⟨_, ⟨⟨rfl, _⟩, _⟩⟩, rfl⟩; exact hmono

private theorem simulateQ_runBucketDF_simDeliverForgeOracleTrackHalted_eq {PQ Pt α : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B : ℕ) (tL : Option ℕ) (par : Bool) (h232 : 2 ^ 32 ≤ B)
    (oa : OracleComp (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes) α) (m : ℕ)
    (hm : oa.IsQueryBoundP (isGameQuery (G := CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes)) m)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (SimFig8C Pt)) (tr : KemFailTrackState P.C.F) (s : BucketState Pt ℓ)
    (hInv : SimBaseClampInv B m sC.base ∧ CellGameClampInv B m s.2.1) :
    runBucketDF P Dh encPt encT lam qep tL par ((simulateQ (simDeliverForgeOracleTrackHalted P K Dh encPt encT decT lam qep B) oa).run ((sC, ex), tr)) s =
      let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
      runBucketDF P Dh encPt encT lam qep tL par (runDFMTrack (simulateQ (simImplCTrackHalted P K encT decT qep (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (lFS P.C P.codec ℓ encT idOf 25000) (deliverForgeHook Pt ℓ) Dh) oa) sC ex tr) s := by
  dsimp only []; let idOf0 : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf0 25000 lam
  let bHook := deliverForgeBucketSemHook (ℓ := ℓ) P Dh encPt encT lam qep tL par
  have hHookInv := deliverForgeBucketSemHookClampInv (ℓ := ℓ) P Dh encPt encT lam qep B tL par
  induction oa using OracleComp.inductionOn generalizing m sC ex tr s with
  | pure a => simp only [runBucketDF, runDFMTrack, simulateQ_pure, StateT.run_pure, pure_bind]
  | query_bind qy u ih =>
    rw [isQueryBoundP_query_bind_iff] at hm; rcases hm with ⟨hq0, hu⟩
    rw [simulateQ_query_bind, simulateQ_query_bind, StateT.run_bind, runDFMTrack_bind, runBucketDF_bind, runBucketDF_bind]
    dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift, MonadLift.monadLift]
    rcases qy with n | t
    · simp only [isGameQuery, ↓reduceIte] at hu
      rw [← simDeliverForgeOracleTrackHalted_inl_eq P K Dh encPt encT decT lam qep B n sC ex tr]
      refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨r, ⟨⟨sC', ex'⟩, tr'⟩⟩, s'⟩ hmem => ?_
      rw [runBucketDF_simDeliverForgeOracleTrackHalted_inl] at hmem
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      obtain ⟨_, _, ⟨_, ⟨⟨rfl, rfl⟩, rfl⟩⟩, rfl⟩ := hmem; exact ih r m (hu r) _ _ _ _ hInv
    · simp only [isGameQuery, ↓reduceIte] at hq0 hu
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by have := hq0.resolve_left (by decide); omega⟩
      have hep : ∀ R, sC.base.mir.epoch R + 1 ≤ B := fun R => by have := hInv.1.hep R; omega
      have hch : ∀ R, ∀ g ∈ sC.base.chains R, g.epoch ≤ B := fun R g hg => by have := hInv.1.hch R g hg; omega
      rcases t with ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
      · change (runBucketDF P Dh encPt encT lam qep tL par (semSendTrackHalted P K Dh encPt encT lam qep sC ex tr Q m₀ none r) s >>= _) =
          (runBucketDF P Dh encPt encT lam qep tL par (runDFMTrack (simSendCTrackHalted P K qep fig (deliverForgeHook Pt ℓ) Q m₀ none r) sC ex tr) s >>= _)
        rw [← semSendTrackHalted_deliverForge_eq]
        exact OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨res, ⟨⟨sC', ex'⟩, tr'⟩⟩, s'⟩ hmem =>
          ih res m' (by simpa using hu res) sC' ex' tr' s' (semSendTrackHalted_bucket_preserves_clampInv P K Dh encPt encT lam qep B m' tL par sC ex tr s Q m₀ none r hInv.1 hInv.2 _ hmem)
      · change (runBucketDF P Dh encPt encT lam qep tL par (semSendTrackHalted P K Dh encPt encT lam qep sC ex tr Q m₀ (some m₁) r) s >>= _) =
          (runBucketDF P Dh encPt encT lam qep tL par (runDFMTrack (simSendCTrackHalted P K qep fig (deliverForgeHook Pt ℓ) Q m₀ (some m₁) r) sC ex tr) s >>= _)
        rw [← semSendTrackHalted_deliverForge_eq]
        exact OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨res, ⟨⟨sC', ex'⟩, tr'⟩⟩, s'⟩ hmem =>
          ih res m' (by simpa using hu res) sC' ex' tr' s' (semSendTrackHalted_bucket_preserves_clampInv P K Dh encPt encT lam qep B m' tL par sC ex tr s Q m₀ (some m₁) r hInv.1 hInv.2 _ hmem)
      · rw [simImplCTrackHalted_dl_eq P K Dh encPt encT decT lam qep B h232 Q w sC ex tr hep hch]
        refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨res, ⟨⟨sC', ex'⟩, tr'⟩⟩, s'⟩ hmem => ?_
        dsimp only [simDeliverForgeOracleTrackHalted, StateT.run, StateT.mk] at hmem
        rw [runBucketDF_bind, mem_support_bind_iff] at hmem; obtain ⟨⟨⟨res₁, sC₁, ex₁⟩, s₁⟩, hrec, htail⟩ := hmem
        simp only [runBucketDF, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at htail
        rcases htail with ⟨⟨h1, ⟨h2, h3⟩, _⟩, h5⟩; subst res sC' ex' s'
        have hmem' : (res₁, (sC₁, (ex₁, s₁))) ∈ support (semRecvHook P Dh encPt encT decT lam bHook qep B sC (ex, s) Q w true) := by
          rw [← runBucketDF_semRecvHook, support_map]; exact ⟨((res₁, (sC₁, ex₁)), s₁), hrec, rfl⟩
        exact ih res₁ m' (by simpa using hu res₁) sC₁ ex₁ tr' s₁ (semRecvHook_preserves_clampInv P Dh encPt encT decT lam hHookInv m' qep h232 sC (ex, s) Q w true hInv.1 hInv.2 _ hmem')
      · rw [simImplCTrackHalted_ij_eq P K Dh encPt encT decT lam qep B h232 Q w sC ex tr hep hch]
        refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨res, ⟨⟨sC', ex'⟩, tr'⟩⟩, s'⟩ hmem => ?_
        dsimp only [simDeliverForgeOracleTrackHalted, StateT.run, StateT.mk] at hmem
        rw [runBucketDF_bind, mem_support_bind_iff] at hmem; obtain ⟨⟨⟨res₁, sC₁, ex₁⟩, s₁⟩, hrec, htail⟩ := hmem
        simp only [runBucketDF, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at htail
        rcases htail with ⟨⟨h1, ⟨h2, h3⟩, h4⟩, h5⟩; subst res sC' ex' tr' s'
        have hmem' : (res₁, (sC₁, (ex₁, s₁))) ∈ support (semRecvHook P Dh encPt encT decT lam bHook qep B sC (ex, s) Q w false) := by
          rw [← runBucketDF_semRecvHook, support_map]; exact ⟨((res₁, (sC₁, ex₁)), s₁), hrec, rfl⟩
        exact ih res₁ m' (by simpa using hu res₁) sC₁ ex₁ tr s₁ (semRecvHook_preserves_clampInv P Dh encPt encT decT lam hHookInv m' qep h232 sC (ex, s) Q w false hInv.1 hInv.2 _ hmem')
      · rw [simImplCTrackHalted_cr_eq P K Dh encPt encT decT lam qep B h232 Q sC ex tr hep hch]
        refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨res, ⟨⟨sC', ex'⟩, tr'⟩⟩, s'⟩ hmem => ?_
        dsimp only [simDeliverForgeOracleTrackHalted, StateT.run, StateT.mk] at hmem
        rw [runBucketDF_bind, mem_support_bind_iff] at hmem; obtain ⟨⟨⟨res₁, sC₁, ex₁⟩, s₁⟩, hrec, htail⟩ := hmem
        simp only [runBucketDF, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at htail
        rcases htail with ⟨⟨h1, ⟨h2, h3⟩, h4⟩, h5⟩; subst res sC' ex' tr' s'
        have hmem' : (res₁, (sC₁, (ex₁, s₁))) ∈ support (semCorrHook P Dh encT bHook sC (ex, s) Q) := by
          rw [← runBucketDF_semCorrHook, support_map]; exact ⟨((res₁, (sC₁, ex₁)), s₁), hrec, rfl⟩
        exact ih res₁ m' (by simpa using hu res₁) sC₁ ex₁ tr s₁ (semCorrHook_preserves_clampInv P Dh encT hHookInv m' sC (ex, s) Q hInv.1 hInv.2 _ hmem')

private theorem forgeGameBucketPaper_challSimDF'Paper_simDeliverForgeClampTrackHalted_eq {PQ Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep : ℕ) (tL : Option ℕ) (par : Bool) (idOf : Party → IdentityKey) (hid : idOf = fun R => if R == Party.A then P.idA else P.idB)
    (A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes) (q : ℕ) (hq : CryptoGames.SM.MakesAtMostQueries A q) (hq32 : 2 * (q + 1) + 25002 < 2 ^ 32) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    forgeGameBucketPaper fig 1 (qep + 1) sameHdrScheme tL par (challSimDF'Paper (2 + 1) (qep + 1) (simDeliverForgeClampTrackHalted P K Dh encPt encT decT lam qep (2 ^ 32) A)) =
      forgeGameBucketPaper fig 1 (qep + 1) sameHdrScheme tL par (challSimDF'Paper (2 + 1) (qep + 1) (simDeliverForgeTrackHalted P K ℓ Dh encPt encT decT idOf lam qep A)) := by
  subst hid; dsimp only []; have hqB : q + 3 ≤ 2 ^ 32 := by omega
  have hq' := (makesAtMostQueries_iff_isGameQuery A q).mp hq
  rw [forgeGameBucketPaper_challSimDF'Paper_eq_runBucketDF, forgeGameBucketPaper_challSimDF'Paper_eq_runBucketDF]
  refine bind_congr fun k => bind_congr fun b => ?_
  rw [simDeliverForgeTrackHalted_eq_bind_runDFMTrack P K Dh encPt encT decT lam qep _ rfl A]
  unfold simDeliverForgeClampTrackHalted
  simp only [StateT.run'_eq, map_eq_bind_pure_comp, Function.comp_def, runBucketDF_bind, bind_assoc]
  simp only [runBucketDF, bucketImplDF_liftM_probComp, simulateQ_pure, StateT.run_pure, bind_assoc, pure_bind]
  refine bind_congr fun pqrKey => ?_
  let idOf0 : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
  have hSim := simulateQ_runBucketDF_simDeliverForgeOracleTrackHalted_eq P K Dh encPt encT decT lam qep (2 ^ 32) tL par (Nat.le_refl _) A q hq'
    (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)) [] (initKemFailTrack P.C.F pqrKey)
    ({ st := fun _ => (), b := b }, (initState _ k false, none))
    ⟨simBaseClampInv_init (2 ^ 32) q _ _ hqB, cellGameClampInv_init P Dh encPt encT lam idOf0 (2 ^ 32) q k false hqB⟩
  unfold runBucketDF at hSim; rw [hSim]

/-- End-to-end `forgeBucketAdvantagePaper` equality coupling
`simDeliverForgeClampSanQTrackHalted` directly to `Refinement.simDeliverForgeTrackHalted`. -/
theorem forgeBucketAdvantagePaper_challSimDF'Paper_simDeliverForgeClampSanQTrackHalted_eq
    {PQ Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    (P : Params PQ (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) (tL : Option ℕ) (par : Bool) (idOf : Party → IdentityKey)
    (hid : idOf = fun R => if R == Party.A then P.idA else P.idB)
    (A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes)
    (hq : CryptoGames.SM.MakesAtMostQueries A q)
    (hq32 : 2 * (q + 1) + 25002 < 2 ^ 32) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    forgeBucketAdvantagePaper fig 1 (qep + 1) sameHdrScheme tL par
        (challSimDF'Paper (2 + 1) (qep + 1)
          (simDeliverForgeClampSanQTrackHalted P K ℓ Dh encPt encT decT lam qep q A)) =
      forgeBucketAdvantagePaper fig 1 (qep + 1) sameHdrScheme tL par
        (challSimDF'Paper (2 + 1) (qep + 1)
          (simDeliverForgeTrackHalted P K ℓ Dh encPt encT decT idOf lam qep A)) := by
  dsimp only [simDeliverForgeClampSanQTrackHalted, forgeBucketAdvantagePaper]
  rw [forgeGameBucketPaper_challSimDF'Paper_simDeliverForgeClampSanTrackHalted_eq
      P K Dh encPt encT decT lam qep (2 ^ 32) (50000 * q) (25001 * q + 25000) (25000 * q)
      tL par idOf hid A q hq (by omega) (by omega) (by omega),
    forgeGameBucketPaper_challSimDF'Paper_simDeliverForgeClampTrackHalted_eq
      P K Dh encPt encT decT lam qep tL par idOf hid A q hq hq32]

end BucketTrackHalted

end

end Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeHaltedCoupling
