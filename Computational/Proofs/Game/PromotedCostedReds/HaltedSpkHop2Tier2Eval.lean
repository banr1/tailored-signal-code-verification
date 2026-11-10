/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.HaltedSpkHop2Tier2Step -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.HaltedSpkDefs
import Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge
import Computational.Proofs.Game.PromotedCostedReds.SessionProgCommon
import Computational.Proofs.Game.PromotedCostedReds.SpkTier2Lift
import Computational.Proofs.Game.PromotedCostedReds.SpkTier2Keys
import Computational.Proofs.Game.PromotedCostedReds.SpkTier2BookkeepingPure
import Computational.Proofs.Game.PromotedCostedReds.SpkTier2BookkeepingProofs
import Computational.Proofs.Game.PromotedCostedReds.SpkTier2BookkeepingBase
import Computational.Proofs.Game.PromotedCostedReds.SpkTier2Bookkeeping
import Computational.Proofs.E2E.Dsl.SmReachInvParty
import Computational.Proofs.SpqrV1Sync.TopStateTight

/-!
# Relational Evaluation Equivalence for Tier-2 Tracker-Halted Hop 2

Proves `OracleCompRel` simulation across initialization and all five query arms for the Tier-2
tracker-halted Hop-2 reductions, establishing `spkHop2PrgProgHaltedTier2_eval` and
`spkHop2PrfProgHaltedTier2_eval`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.HaltedSpkHop2Tier2Eval

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Var Env Ops Iface Expr Comp CostedReduction
  atomicSig atomicSessionOps coinOnlyIface extractPtPrfIface e2eSessionCodec handlerImpl
  partyToBool recvResultEnc recvResultDec
  BV256 BV512 PK PtT GhostStT PlainT B smQT smRT)
open _root_.CryptoGames (Party)
open _root_.CryptoGames.CBC (Plain)
open _root_.CryptoGames.CKA (DHFun)
open _root_.CryptoGames.MACScheme (prfSpec)
open _root_.CryptoGames.Ratchet (extractPRF)
open _root_.CryptoGames.SM (Adversary ConfigR GameState MakesAtMostQueries Pos Record RecvResult
  partyEnc posTy posEnc orE orE_eval pGet pair_eval corrR inWindow)
open _root_.CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey GhostState ShaCompress
  KeyPair SessionState currentVersion maxReceiverChains maxMessageKeys)
open _root_.CryptoGames.Ratchet.LibsignalSim (SimKemCoins SimBraidSt SimKemFailTrack
  simInitKemFailTrack simNextKemCoins simEkSideIsA simAuthNext simBe64
  simStepKemFailSend simStepKemFailDeliver)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.E2E (Bytes Hop2Aux Hop2Comp Hop2Hyb hop2Unif hop2Lift
  hop2Deliver hop2Inject configRefuseEarlyBobCorr paramsIdsWithSpqr sessionSchemeU
  spkSwapHybridCount evalSpkSwapPrgHybrid evalSpkSwapPrfHybrid)
open Computational.Proofs.E2E.Dsl.SmReachInvParty (PartyReachInv partyReachInv_initB
  partyReachInv_send)
open CryptoVerification.SpqrV1Sync.SendTotal (topStateTight_init)
open Computational.Proofs.Game.PromotedCostedReds.SessionProgCommon (letE_eval comp_eval_ret
  comp_eval_bind comp_eval_ite comp_eval_caseOpt comp_eval_caseSum
  isQueryBoundP_of_makesAtMostQueries)
open Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge (liftVal liftEnv
  wk1Expr wk1Expr_eval wk1Comp wk1Comp_eval liftExpr liftExpr_eval
  drSendAtomicC drSendAtomicC_eval_params)
open Computational.Proofs.Game.PromotedCostedReds.SpkTier2Lift (OracleCompRel
  eval_eq_simulateQ_of_rel)
open Computational.Proofs.Game.PromotedCostedReds.SpkTier2Keys (spkMaxWireLen)
open Computational.Proofs.Game.PromotedCostedReds.SpkTier2BookkeepingPure (Tier2Gs Tier2GsRel)
open Computational.Proofs.Game.PromotedCostedReds.SpkTier2BookkeepingProofs (
  hop2TblRel_nil hop2TblRel_cons tier2GsRel_init_pair tier2GsRel_record_preserves)
open Computational.Proofs.Game.PromotedCostedReds.SpkTier2BookkeepingBase (
  e2eSessionCodec_rdec_tier2SmRenc tier2SmRWireE eval_tier2SmRWireE
  tier2RecTy tier2RecEnc tier2RecMk eval_tier2RecMk
  tier2GsTy tier2GsEnc gsStTier2E gsBTier2E gsWinTier2E gsEpochTier2E gsIdxTier2E
  initGsTier2E eval_initGsTier2E safeChTier2E eval_safeChTier2E
  epMgmtTier2E eval_epMgmtTier2E sendOKTier2E eval_sendOKTier2E)
open Computational.Proofs.Game.PromotedCostedReds.SpkTier2Bookkeeping (
  recordCiphertextTier2E eval_recordCiphertextTier2E
  hop2TblTy hop2TblInitE eval_hop2TblInitE hop2TblSetE eval_hop2TblSetE
  sessionSchemeU_send_wire_length_le)
open Computational.Proofs.Game.PromotedCostedReds.SpkHop2RInProg (
  compCoinToPrf compCoinToPrf_wk1Comp compCoinToPrf_eval_eq_liftM eval_redCoinToPrf
  Hop2Mode Hop2EvalSpec prgCoinMode prgLiftedMode prgLiftedMode_evalSpec
  prfOracleMode prfOracleMode_evalSpec
  drawBoolCoin drawBoolCoin_eval draw256Coin draw256Coin_eval
  sPureOp sGroupOp eval_sGroupOp hop2ChallTy
  hop2InitGsE2EE eval_hop2InitGsE2EE)
open Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslBase (simInitKemSessionTrack)
open Computational.Proofs.Game.PromotedCostedReds.KemFailTrackTier2 (
  kemTrackTier2T honestWiresTier2T kemSessionTrackTier2T
  kemTrackTier2Enc honestWiresTier2Enc kemSessionTrackTier2Enc
  KemTrackTier2Inv KemTrackTier2Inv.withCand
  kemTrackTier2Inv_initSim kemTrackTier2Inv_stepSendSim kemTrackTier2Inv_stepDeliverSim
  initKemFailSessionTrackTier2E initKemFailSessionTrackTier2E_eval
  stepKemFailSendTier2C stepKemFailSendTier2C_eval
  recordHonestWireTier2E recordHonestWireTier2E_eval
  findRevHonestWireIdxTier2E findRevHonestWireIdxTier2E_eval
  kemOnDeliverPostTier2E kemOnDeliverPostTier2E_eval)
open Computational.Proofs.Game.PromotedCostedReds.SpkHop2Tier2Prog (
  tier2SamIfNec512C tier2SamIfNec512C_eval
  hop2Tier2AuxTy hop2Tier2FullStTy Hop2AuxTier2Rel Hop2FullTier2Rel
  auxBadTier2 eval_auxBadTier2 auxMkTier2
  stSTier2 stAuxTier2 stMkTier2
  hop2CrArmTier2E hop2CrArmTier2E_rel
  hop2DlArmTier2C hop2DlArmTier2C_rel
  hop2IjArmTier2C hop2IjArmTier2C_rel)
open Computational.Proofs.Game.PromotedCostedReds.HaltedSpkHop2Tier2Step (
  hop2HaltedTier2StTy hst2Base hst2SessionTr hst2Tr hst2Wires hst2Mk
  hop2InitBodyTier2TrackC hop2InitPrfTier2TrackC
  hop2TrArmTier2TrackC hop2ChArmTier2TrackC hop2StepTier2TrackC
  hop2GameTier2TrackRed redCoinToPrf_hop2GameTier2TrackRed_prgCoinMode
  spkHop2PrgProgHaltedTier2Real spkHop2PrgProgHaltedTier2
  spkHop2PrfProgHaltedTier2Real spkHop2PrfProgHaltedTier2)
open Computational.Proofs.E2E.HaltedSpkDefs (
  updateKemFailOnDeliver hop2LiftTrackHalted liftHop2NoTrackM
  hop2DeliverTrackHalted_run hop2ImplTrackHalted hop2GameTrackHalted
  hop2PrgRedKTrackHalted hop2PrfRedKTrackHalted)
open Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge (
  KemFailTrackState KemFailSessionTrack initKemFailTrack stepKemFailSend stepKemFailDeliver
  transmitRTrackHalted challRTrackHalted kemBraidParty)

/-! ## Tracker state projection -/

section SimBridge

private def kemCoinsBridgeEnc : CryptoVerification.SpqrV1Sync.Braid.Coins → SimKemCoins
  | .init => .init | .seed s => .seed s | .both s r => .both s r

private def kemBridgeToSim {F : ShaCompress} (tr : KemFailTrackState F) : SimKemFailTrack F :=
  { e := tr.e, auth := tr.auth, c := kemCoinsBridgeEnc tr.c,
    st := tr.st, sentB := tr.sentB, sendCtr := tr.sendCtr, cand := tr.cand }

private theorem kemCoinsBridgeEnc_nextCoins (F : ShaCompress)
    (c : CryptoVerification.SpqrV1Sync.Braid.Coins) (st : SimBraidSt F) (tape : List (BitVec 8)) :
    kemCoinsBridgeEnc (CryptoVerification.SpqrV1Sync.Braid.nextCoins F c st tape) =
      simNextKemCoins F (kemCoinsBridgeEnc c) st tape := by
  cases c <;> cases st <;>
    simp only [CryptoVerification.SpqrV1Sync.Braid.nextCoins, simNextKemCoins, kemCoinsBridgeEnc]
  all_goals split_ifs <;> rfl

private theorem simEkSideIsA_bne_bridge (e : BitVec 64) (Q : Party) :
    (simEkSideIsA e != (Q == .A)) =
      (CryptoVerification.SpqrV1Sync.Braid.ekSide e != kemBraidParty Q) := by
  cases Q <;> by_cases h : e.toNat % 2 = 1 <;>
    simp only [simEkSideIsA, CryptoVerification.SpqrV1Sync.Braid.ekSide, kemBraidParty, h, ↓reduceIte] <;>
    decide

private theorem kemBridgeToSim_init (F : ShaCompress) (k : BitVec 256) :
    kemBridgeToSim (initKemFailTrack F k) = simInitKemFailTrack F k := rfl

private theorem kemBridgeToSim_cand {F : ShaCompress} (tr : KemFailTrackState F) :
    (kemBridgeToSim tr).cand = tr.cand := rfl

private theorem kemBridgeToSim_withCand {F : ShaCompress} (tr : KemFailTrackState F)
    (c : Option (List.Vector (BitVec 8) 64 × List.Vector (BitVec 8) 32)) :
    kemBridgeToSim { tr with cand := c } = { kemBridgeToSim tr with cand := c } := rfl

private theorem kemBridgeToSim_stepSend (F : ShaCompress) (K : MlKem)
    (tr : KemFailTrackState F) (Q : Party) (r : BitVec 512) :
    kemBridgeToSim (stepKemFailSend F K tr Q r) =
      simStepKemFailSend F K (kemBridgeToSim tr) Q r := by
  unfold stepKemFailSend simStepKemFailSend; dsimp only [kemBridgeToSim]
  rcases (tr.st Q).send K (CryptoVerification.LibsignalSpqrV1.coinBytes r) with err | ⟨out, _⟩ <;>
    simp only [kemCoinsBridgeEnc_nextCoins, simEkSideIsA_bne_bridge] <;>
    congr 1 <;> rcases tr.cand with _ | p <;> rcases tr.c with _ | s | ⟨s, r₀⟩ <;>
    rcases tr.st Q <;> rfl

private theorem kemBridgeToSim_stepDeliver (F : ShaCompress) (K : MlKem)
    (tr : KemFailTrackState F) (Q : Party) (j : ℕ) :
    kemBridgeToSim (stepKemFailDeliver F K tr Q j) =
      simStepKemFailDeliver F K (kemBridgeToSim tr) Q j := by
  unfold stepKemFailDeliver simStepKemFailDeliver; dsimp only [kemBridgeToSim]
  rcases tr.sentB[j]? with _ | ⟨m, ctr⟩
  · rfl
  · dsimp only []
    rcases (tr.st Q).recv K m with err | out
    · rfl
    · dsimp only [CryptoVerification.SpqrV1Sync.Braid.noneMsg]
      by_cases hm : m = { epoch := tr.e + 1#64, payload := .none }
      · rcases tr.c with _ | s | ⟨s, r₀⟩ <;>
          simp [hm, kemCoinsBridgeEnc, simAuthNext, CryptoVerification.SpqrV1Sync.Braid.authNext,
            CryptoVerification.SpqrV1Sync.Braid.secOf, CryptoVerification.SpqrV1Sync.Braid.ss0Of,
            CryptoVerification.SpqrV1Sync.Braid.encOf, CryptoVerification.SpqrV1Sync.InSync.hdrOf,
            simBe64, CryptoVerification.SpqrV1Sync.Braid.be64]
      · simp [hm]

end SimBridge

/-! ## Relational simulation -/

section Tier2TrackEval

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (C : Crypto) (K : MlKem)
  (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
  (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
  (idA idB : IdentityKey) (lam : Pt)

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam

private def Hop2Tier2TrackSimRel (s : BitVec 256) (chall : BitVec 256 × BitVec 256)
    (_m : ℕ) (stV : (hop2HaltedTier2StTy ℓ Pt).denote)
    (gat : (GameState (GhostState Bytes) (Plain ℓ) Bytes × Hop2Aux Pt) ×
      KemFailSessionTrack C.F Bytes) : Prop :=
  Hop2FullTier2Rel (ℓ := ℓ) encT s chall gat.1 stV.1 ∧
  (∀ Q : Party, PartyReachInv C K (gat.1.1.st Q)) ∧
  stV.2.1 = kemTrackTier2Enc (kemBridgeToSim gat.2.1) ∧
  KemTrackTier2Inv C.F K (kemBridgeToSim gat.2.1) ∧
  stV.2.2 = honestWiresTier2Enc ℓ gat.2.2 ∧
  (∀ wp ∈ gat.2.2, wp.1.length ≤ spkMaxWireLen ℓ)

private theorem fst_ev {O0 : Ops ASig} {Γ : List (Ty ASig)} {a b : Ty ASig}
    (x : Expr O0 Γ (.prod a b)) (ρ : Env Γ) : (Expr.fst x).eval ρ = (x.eval ρ).1 := rfl

private theorem pair_ev {O0 : Ops ASig} {Γ : List (Ty ASig)} {a b : Ty ASig}
    (x : Expr O0 Γ a) (y : Expr O0 Γ b) (ρ : Env Γ) :
    (Expr.pair x y).eval ρ = (x.eval ρ, y.eval ρ) := rfl

private theorem some_ev {O0 : Ops ASig} {Γ : List (Ty ASig)} {a : Ty ASig}
    (x : Expr O0 Γ a) (ρ : Env Γ) : (Expr.some x).eval ρ = some (x.eval ρ) := rfl

private theorem none_ev {O0 : Ops ASig} {Γ : List (Ty ASig)} {a : Ty ASig} (ρ : Env Γ) :
    (Expr.none : Expr O0 Γ (.opt a)).eval ρ = none := rfl

private theorem ite_ev {O0 : Ops ASig} {Γ : List (Ty ASig)} {a : Ty ASig}
    (c : Expr O0 Γ .bool) (t e : Expr O0 Γ a) (ρ : Env Γ) :
    (Expr.ite c t e).eval ρ = if c.eval ρ then t.eval ρ else e.eval ρ := rfl

private theorem partyToBool_eq_partyEnc (p : Party) : partyToBool p = partyEnc p := by
  cases p <;> rfl

private theorem eval_pGet_gsStTier2E {O0 : Ops ASig} {Γ : List (Ty ASig)}
    (sE : Expr O0 Γ (tier2GsTy ℓ Pt)) (pE : Expr O0 Γ .bool) (ρ : Env Γ)
    (d : Tier2Gs ℓ) (p : Party)
    (hs : sE.eval ρ = tier2GsEnc Pt d) (hp : pE.eval ρ = partyEnc p) :
    (pGet (gsStTier2E sE) pE).eval ρ = d.st p := by
  cases p <;> simp [pGet, gsStTier2E, Expr.eval, Expr.v0, hs, hp, tier2GsEnc, partyEnc]

private theorem eval_gsBTier2E {O0 : Ops ASig} {Γ : List (Ty ASig)}
    (sE : Expr O0 Γ (tier2GsTy ℓ Pt)) (ρ : Env Γ)
    (d : Tier2Gs ℓ) (hs : sE.eval ρ = tier2GsEnc Pt d) :
    (gsBTier2E sE).eval ρ = d.b := by
  simp [gsBTier2E, Expr.eval, hs, tier2GsEnc]

private theorem eval_gsWinTier2E {O0 : Ops ASig} {Γ : List (Ty ASig)}
    (sE : Expr O0 Γ (tier2GsTy ℓ Pt)) (ρ : Env Γ)
    (d : Tier2Gs ℓ) (hs : sE.eval ρ = tier2GsEnc Pt d) :
    (gsWinTier2E sE).eval ρ = d.win := by
  simp [gsWinTier2E, Expr.eval, hs, tier2GsEnc]

private theorem eval_pGet_gsEpochTier2E {O0 : Ops ASig} {Γ : List (Ty ASig)}
    (sE : Expr O0 Γ (tier2GsTy ℓ Pt)) (pE : Expr O0 Γ .bool) (ρ : Env Γ)
    (d : Tier2Gs ℓ) (p : Party)
    (hs : sE.eval ρ = tier2GsEnc Pt d) (hp : pE.eval ρ = partyEnc p) :
    (pGet (gsEpochTier2E sE) pE).eval ρ = d.epoch p := by
  cases p <;> simp [pGet, gsEpochTier2E, Expr.eval, Expr.v0, hs, hp, tier2GsEnc, partyEnc]

private theorem eval_pGet_gsIdxTier2E {O0 : Ops ASig} {Γ : List (Ty ASig)}
    (sE : Expr O0 Γ (tier2GsTy ℓ Pt)) (pE : Expr O0 Γ .bool) (ρ : Env Γ)
    (d : Tier2Gs ℓ) (p : Party)
    (hs : sE.eval ρ = tier2GsEnc Pt d) (hp : pE.eval ρ = partyEnc p) :
    (pGet (gsIdxTier2E sE) pE).eval ρ = d.idx p := by
  cases p <;> simp [pGet, gsIdxTier2E, Expr.eval, Expr.v0, hs, hp, tier2GsEnc, partyEnc]

private theorem epMgmt_st_eq {gs gs' : GameState (GhostState Bytes) (Plain ℓ) Bytes}
    {Δ qep : ℕ} {p : Party} {bad : Bool} (h : gs.epMgmt Δ qep p bad = some gs') :
    gs'.st = gs.st := by
  unfold GameState.epMgmt at h; split_ifs at h <;> cases h <;> rfl

private theorem partyReachInv_record {gs : GameState (GhostState Bytes) (Plain ℓ) Bytes}
    (hinv : ∀ Q, PartyReachInv C K (gs.st Q))
    (Δ : ℕ) (Q : Party) {st' : GhostState Bytes} (hst' : PartyReachInv C K st')
    (r : Record (Plain ℓ) Bytes) (isChall : Bool) :
    ∀ Q', PartyReachInv C K ((gs.record Δ Q st' r isChall).st Q') := by
  intro Q'; dsimp only [GameState.record]
  by_cases hQ : Q' = Q
  · subst hQ; rw [Function.update_self]; exact hst'
  · rw [Function.update_of_ne hQ]; exact hinv Q'

private theorem liftM_prob_pure {α : Type} (x : α) :
    (liftM (pure x : ProbComp α) : Hop2Comp Pt α) = pure x := by
  simp only [← liftComp_eq_liftM, liftComp_pure]

private theorem liftM_prob_bind {α β : Type} (p : ProbComp α) (f : α → ProbComp β) :
    (liftM (p >>= f) : Hop2Comp Pt β) =
      (liftM p : Hop2Comp Pt α) >>= fun a => (liftM (f a) : Hop2Comp Pt β) := by
  simp only [← liftComp_eq_liftM, liftComp_bind]

private theorem stateT_lift_get_run2 {S₁ S₂ : Type} {M : Type → Type} [Monad M] [LawfulMonad M]
    (s₁ : S₁) (s₂ : S₂) :
    (((StateT.lift get : StateT S₁ (StateT S₂ M) S₂).run s₁).run s₂) = pure ((s₂, s₁), s₂) := by
  simp only [StateT.run_lift, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind]

private theorem stateT_lift_set_run2 {S₁ S₂ : Type} {M : Type → Type} [Monad M] [LawfulMonad M]
    (s₁ : S₁) (s₂ s₂' : S₂) :
    (((StateT.lift (set s₂') : StateT S₁ (StateT S₂ M) PUnit).run s₁).run s₂) =
      pure (((), s₁), s₂') := by
  simp only [StateT.run_lift, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]

private theorem stateT_lift_prob_run2 {S₁ S₂ α : Type}
    (p : ProbComp α) (s₁ : S₁) (s₂ : S₂) :
    (((StateT.lift (liftM p : StateT S₂ ProbComp α) :
        StateT S₁ (StateT S₂ ProbComp) α).run s₁).run s₂) =
      p >>= fun a => pure ((a, s₁), s₂) := by
  simp only [StateT.run_lift, StateT.run_bind, StateT.run_monadLift, monadLift_self,
    StateT.run_pure, bind_assoc, pure_bind]

private theorem stateT_lift_prob_run2_bind {S₁ S₂ α β : Type}
    (p : ProbComp α) (k : α → StateT S₁ (StateT S₂ ProbComp) β) (s₁ : S₁) (s₂ : S₂) :
    ((((StateT.lift (liftM p : StateT S₂ ProbComp α) >>= k).run s₁).run s₂)) =
      p >>= fun a => ((k a).run s₁).run s₂ := by
  simp only [StateT.run_bind, stateT_lift_prob_run2, bind_assoc, pure_bind]

private theorem oracleCompRel_hop2LiftTrackHalted {α β : Type}
    (P_out : α → β → Prop)
    (oa : Hop2Comp Pt (α × ((tier2GsTy ℓ Pt).denote × (kemSessionTrackTier2T ℓ Pt).denote)))
    (m : StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes)
      (StateT (KemFailSessionTrack C.F Bytes) ProbComp) β)
    (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes) (aux : Hop2Aux Pt)
    (thw : KemFailSessionTrack C.F Bytes)
    (h : OracleCompRel
      (fun (r₁ : α × ((tier2GsTy ℓ Pt).denote × (kemSessionTrackTier2T ℓ Pt).denote))
           (r₂ : (β × GameState (GhostState Bytes) (Plain ℓ) Bytes) ×
             KemFailSessionTrack C.F Bytes) =>
        P_out r₁.1 r₂.1.1 ∧
        (∃ d' : Tier2Gs ℓ, r₁.2.1 = tier2GsEnc Pt d' ∧ Tier2GsRel ℓ r₂.1.2 d') ∧
        (∀ Q' : Party, PartyReachInv C K (r₂.1.2.st Q')) ∧
        r₁.2.2.1 = kemTrackTier2Enc (kemBridgeToSim r₂.2.1) ∧
        KemTrackTier2Inv C.F K (kemBridgeToSim r₂.2.1) ∧
        r₁.2.2.2 = honestWiresTier2Enc ℓ r₂.2.2 ∧
        (∀ wp ∈ r₂.2.2, wp.1.length ≤ spkMaxWireLen ℓ))
      oa (liftM (((m.run gs).run thw) : ProbComp _) : Hop2Comp Pt _)) :
    OracleCompRel
      (fun r₁ r₂ =>
        P_out r₁.1 r₂.1.1 ∧ r₂.1.2.2 = aux ∧
        (∃ d' : Tier2Gs ℓ, r₁.2.1 = tier2GsEnc Pt d' ∧ Tier2GsRel ℓ r₂.1.2.1 d') ∧
        (∀ Q' : Party, PartyReachInv C K (r₂.1.2.1.st Q')) ∧
        r₁.2.2.1 = kemTrackTier2Enc (kemBridgeToSim r₂.2.1) ∧
        KemTrackTier2Inv C.F K (kemBridgeToSim r₂.2.1) ∧
        r₁.2.2.2 = honestWiresTier2Enc ℓ r₂.2.2 ∧
        (∀ wp ∈ r₂.2.2, wp.1.length ≤ spkMaxWireLen ℓ))
      oa (((hop2LiftTrackHalted (Pt := Pt) (ℓ := ℓ) m).run (gs, aux)).run thw) := by
  change OracleCompRel _ oa
    ((liftM (((m.run gs).run thw) : ProbComp _) : Hop2Comp Pt _) >>=
      fun z => pure ((z.1.1, (z.1.2, aux)), z.2))
  rw [← bind_pure oa]
  exact OracleCompRel.bind h fun r₁ r₂ ⟨h1, h2, h3, h4, h5, h6, h7⟩ =>
    .pureP ⟨h1, rfl, h2, h3, h4, h5, h6, h7⟩

private theorem hop2SendPostEpTier2Track_rel
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (extractPtPrfIface ℓ Pt))
    {stepOf : BitVec 256 → Pt → Hop2Comp Pt (BitVec 256)} (hM : Hop2EvalSpec M stepOf)
    {tailT : Ty ASig} {Γ : List (Ty ASig)}
    (rdecF : (smRT (ℓ := ℓ) (Pt := Pt) GhostStT).denote → Option Bytes)
    (hrdec : ∀ (w : Option Bytes) {Γ' : List (Ty ASig)} (e : Expr AOps Γ' (.opt (B 32)))
      (ρ' : Env Γ'), e.eval ρ' = w → rdecF ((tier2SmRWireE e).eval ρ') = w)
    (isCh : Bool) (mVal : Plain ℓ) (Q : Party) (tailV : tailT.denote)
    (coins : BitVec 512) (bad : Bool)
    (d d₁ : Tier2Gs ℓ) (gs gs₁ : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (tr : KemFailTrackState C.F) (hw : List (Bytes × Party))
    (ρ : Env Γ)
    (msgE3 : Expr AOps (.prod .bool (kemTrackTier2T ℓ Pt) :: tier2GsTy ℓ Pt :: .prod BV512 .bool ::
      .prod (tier2GsTy ℓ Pt) (.prod (kemSessionTrackTier2T ℓ Pt) (.prod .bool tailT)) :: Γ) PlainT)
    (msgE4 : Expr AOps (.prod GhostStT (B 32) :: .prod .bool (kemTrackTier2T ℓ Pt) ::
      tier2GsTy ℓ Pt :: .prod BV512 .bool ::
      .prod (tier2GsTy ℓ Pt) (.prod (kemSessionTrackTier2T ℓ Pt) (.prod .bool tailT)) :: Γ) PlainT)
    (hmsg3 : ∀ kf, msgE3.eval (.cons kf (.cons (tier2GsEnc Pt d₁) (.cons (coins, bad)
      (.cons (tier2GsEnc Pt d, ((kemTrackTier2Enc (kemBridgeToSim tr), honestWiresTier2Enc ℓ hw),
        (partyEnc Q, tailV))) ρ)))) = mVal)
    (hmsg4 : ∀ out kf, msgE4.eval (.cons out (.cons kf (.cons (tier2GsEnc Pt d₁) (.cons (coins, bad)
      (.cons (tier2GsEnc Pt d, ((kemTrackTier2Enc (kemBridgeToSim tr), honestWiresTier2Enc ℓ hw),
        (partyEnc Q, tailV))) ρ))))) = mVal)
    (hrel : Tier2GsRel ℓ gs d) (hinv : ∀ Q', PartyReachInv C K (gs.st Q'))
    (hrel₁ : Tier2GsRel ℓ gs₁ d₁) (hinv₁ : ∀ Q', PartyReachInv C K (gs₁.st Q'))
    (htrInv : KemTrackTier2Inv C.F K (kemBridgeToSim tr))
    (hhwLen : ∀ wp ∈ hw, wp.1.length ≤ spkMaxWireLen ℓ) :
    let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
    let t0 : Ty ASig :=
      .prod (tier2GsTy ℓ Pt) (.prod (kemSessionTrackTier2T ℓ Pt) (.prod .bool tailT))
    let ρ₂ : Env (S := ASig) (tier2GsTy ℓ Pt :: .prod BV512 .bool :: t0 :: Γ) :=
      .cons (tier2GsEnc Pt d₁) (.cons (coins, bad)
        (.cons (tier2GsEnc Pt d, ((kemTrackTier2Enc (kemBridgeToSim tr), honestWiresTier2Enc ℓ hw),
          (partyEnc Q, tailV))) ρ))
    OracleCompRel
      (fun r₁ r₂ =>
        rdecF r₁.1 = r₂.1.1 ∧
        (∃ d' : Tier2Gs ℓ, r₁.2.1 = tier2GsEnc Pt d' ∧ Tier2GsRel ℓ r₂.1.2 d') ∧
        (∀ Q' : Party, PartyReachInv C K (r₂.1.2.st Q')) ∧
        r₁.2.2.1 = kemTrackTier2Enc (kemBridgeToSim r₂.2.1) ∧
        KemTrackTier2Inv C.F K (kemBridgeToSim r₂.2.1) ∧
        r₁.2.2.2 = honestWiresTier2Enc ℓ r₂.2.2 ∧
        (∀ wp ∈ r₂.2.2, wp.1.length ≤ spkMaxWireLen ℓ))
      (((M.embedCoin (stepKemFailSendTier2C (.fst (.fst (.snd .v2))) (.fst (.snd (.snd .v2)))
          (.fst .v1))).bind
        (Comp.ite (.fst .v0)
          (.ret (.pair (tier2SmRWireE .none)
            (.pair (.fst .v3) (.pair (.snd .v0) (.snd (.fst (.snd .v3)))))))
          ((M.embedCoin (drSendAtomicC (coinOnlyIface ℓ Pt)
              (.pair (pGet (gsStTier2E .v1) (.fst (.snd (.snd .v3))))
                (.pair msgE3 (.fst .v2))))).bind
            (.ret (.pair (tier2SmRWireE (.some (.snd .v0)))
              (.pair
                (recordCiphertextTier2E 3 .v2 (.fst (.snd (.snd .v4))) (.fst .v0)
                  (tier2RecMk
                    (.pair (.fst (.snd (.snd .v4)))
                      (.pair (pGet (gsEpochTier2E .v2) (.fst (.snd (.snd .v4))))
                        (.add (pGet (gsIdxTier2E .v2) (.fst (.snd (.snd .v4)))) (.nat 1))))
                    msgE4 (.snd .v0))
                  (.bool isCh))
                (.pair (.snd .v1)
                  (recordHonestWireTier2E (.snd (.fst (.snd .v4))) (.snd .v0)
                    (.fst (.snd (.snd .v4))))))))))).eval ρ₂)
      (liftM (((do
          let (tr0, hw0) ← StateT.lift (get : StateT (KemFailSessionTrack C.F Bytes) ProbComp _)
          let tr' := stepKemFailSend C.F K tr0 Q coins
          if tr'.cand.isSome then
            StateT.lift (set ({ tr0 with cand := tr'.cand }, hw0))
            pure none
          else
            let out := P.send (gs₁.st Q) mVal.toList coins
            let r : Record (Plain ℓ) Bytes := ⟨⟨Q, gs₁.epoch Q, gs₁.idx Q + 1⟩, mVal, out.2⟩
            set (gs₁.record 3 Q out.1 r isCh)
            StateT.lift (set (tr', (out.2, Q) :: hw0))
            pure (some out.2)).run gs).run (tr, hw))) := by
  intro P t0 ρ₂
  simp only [StateT.run_bind, stateT_lift_get_run2, pure_bind]
  have hkfEval := stepKemFailSendTier2C_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I := coinOnlyIface ℓ Pt)
    (.fst (.fst (.snd .v2))) (.fst (.snd (.snd .v2))) (.fst .v1) ρ₂
    (kemBridgeToSim tr) Q coins rfl (partyToBool_eq_partyEnc Q).symm rfl (htrInv.bOk Q)
  rw [comp_eval_bind, hM.embedCoin_eq, compCoinToPrf_eval_eq_liftM, hkfEval,
    ← liftComp_eq_liftM, liftComp_pure, pure_bind]
  set trBridge' := stepKemFailSend C.F K tr Q coins
  have hStepSim : simStepKemFailSend C.F K (kemBridgeToSim tr) Q coins = kemBridgeToSim trBridge' :=
    (kemBridgeToSim_stepSend C.F K tr Q coins).symm
  rw [comp_eval_ite]
  let kfOut : (Ty.prod .bool (kemTrackTier2T ℓ Pt)).denote :=
    (trBridge'.cand.isSome,
      if trBridge'.cand.isSome then kemTrackTier2Enc { kemBridgeToSim tr with cand := trBridge'.cand }
      else kemTrackTier2Enc (kemBridgeToSim trBridge'))
  have hkfEq :
      (let tr' := simStepKemFailSend C.F K (kemBridgeToSim tr) Q coins
       (tr'.cand.isSome,
         if tr'.cand.isSome then kemTrackTier2Enc (ℓ := ℓ) (Pt := Pt)
           { kemBridgeToSim tr with cand := tr'.cand }
         else kemTrackTier2Enc (ℓ := ℓ) (Pt := Pt) tr')) = kfOut := by
    simp only [kfOut, hStepSim, kemBridgeToSim_cand]
  rw [hkfEq]
  let ρk : Env (S := ASig) (.prod .bool (kemTrackTier2T ℓ Pt) :: tier2GsTy ℓ Pt ::
      .prod BV512 .bool :: t0 :: Γ) := .cons kfOut ρ₂
  have hkfFst : (Expr.fst (Expr.v0 (O := AOps)) : Expr AOps _ .bool).eval ρk =
      trBridge'.cand.isSome := rfl
  change OracleCompRel _
    (if (Expr.fst (Expr.v0 (O := AOps)) : Expr AOps _ .bool).eval ρk then _ else _) _
  rw [hkfFst]
  cases hcand : trBridge'.cand.isSome with
  | true =>
    simp only [↓reduceIte, StateT.run_bind, stateT_lift_set_run2, StateT.run_pure,
      pure_bind, liftM_prob_pure, comp_eval_ret]
    refine OracleCompRel.pureP ⟨?_, ⟨d, rfl, hrel⟩, hinv, ?_,
      by rw [kemBridgeToSim_withCand]; exact htrInv.withCand trBridge'.cand, rfl, hhwLen⟩
    · rw [pair_ev]; exact hrdec none .none _ (none_ev _)
    · simp [kfOut, hcand, kemBridgeToSim_withCand, Expr.eval, Expr.v0]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
      stateT_lift_set_run2, StateT.run_pure, pure_bind, liftM_prob_pure]
    have hinp :
        (Expr.pair (pGet (gsStTier2E .v1) (.fst (.snd (.snd .v3))))
          (.pair msgE3 (.fst .v2)) :
          Expr AOps _ (.prod GhostStT (.prod PlainT BV512))).eval ρk =
        (gs₁.st Q, (mVal, coins)) := by
      rw [pair_ev, eval_pGet_gsStTier2E _ _ ρk d₁ Q rfl rfl, hrel₁.h_st, pair_ev, hmsg3 kfOut]; rfl
    rw [comp_eval_bind, hM.embedCoin_eq, compCoinToPrf_eval_eq_liftM,
      drSendAtomicC_eval_params (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) (coinOnlyIface ℓ Pt) _ ρk idA idB
        (by rw [hinp]; exact hinv₁ Q),
      hinp, ← liftComp_eq_liftM, liftComp_pure, pure_bind, comp_eval_ret]
    let out := (sessionSchemeU P ℓ).send (gs₁.st Q) mVal coins
    have hout_eq : P.send (gs₁.st Q) mVal.toList coins = out := rfl
    rw [hout_eq]
    let ρ₃ : Env (S := ASig)
        (.prod GhostStT (B 32) :: .prod .bool (kemTrackTier2T ℓ Pt) ::
          tier2GsTy ℓ Pt :: .prod BV512 .bool :: t0 :: Γ) := .cons out ρk
    let p0 : Pos := ⟨Q, gs₁.epoch Q, gs₁.idx Q + 1⟩
    have hposE :
        (Expr.pair (.fst (.snd (.snd .v4)))
          (.pair (pGet (gsEpochTier2E .v2) (.fst (.snd (.snd .v4))))
            (.add (pGet (gsIdxTier2E .v2) (.fst (.snd (.snd .v4)))) (.nat 1))) :
          Expr AOps _ posTy).eval ρ₃ = posEnc p0 := by
      rw [pair_ev, pair_ev, eval_pGet_gsEpochTier2E _ _ ρ₃ d₁ Q rfl rfl, hrel₁.h_epoch]
      change (partyEnc Q, (gs₁.epoch Q,
        (pGet (gsIdxTier2E .v2) (.fst (.snd (.snd .v4))) : Expr AOps _ .nat).eval ρ₃ + 1)) = posEnc p0
      rw [eval_pGet_gsIdxTier2E _ _ ρ₃ d₁ Q rfl rfl, hrel₁.h_idx]; rfl
    have hrecE :
        (tier2RecMk
          (.pair (.fst (.snd (.snd .v4)))
            (.pair (pGet (gsEpochTier2E .v2) (.fst (.snd (.snd .v4))))
              (.add (pGet (gsIdxTier2E .v2) (.fst (.snd (.snd .v4)))) (.nat 1))))
          msgE4 (.snd .v0) : Expr AOps _ (tier2RecTy ℓ Pt)).eval ρ₃ =
        tier2RecEnc ⟨p0, mVal, out.2⟩ := by
      rw [eval_tier2RecMk _ _ _ ρ₃ p0 hposE, hmsg4 out kfOut]; rfl
    have hrecGs := eval_recordCiphertextTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) 3
      .v2 (.fst (.snd (.snd .v4))) (.fst .v0)
      (tier2RecMk
        (.pair (.fst (.snd (.snd .v4)))
          (.pair (pGet (gsEpochTier2E .v2) (.fst (.snd (.snd .v4))))
            (.add (pGet (gsIdxTier2E .v2) (.fst (.snd (.snd .v4)))) (.nat 1))))
        msgE4 (.snd .v0))
      (.bool isCh) ρ₃ d₁ Q ⟨p0, mVal, out.2⟩ rfl rfl hrecE
    have hhwEval := recordHonestWireTier2E_eval (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
      (.snd (.fst (.snd .v4))) (.snd .v0) (.fst (.snd (.snd .v4))) ρ₃
      hw out.2 Q rfl rfl (partyToBool_eq_partyEnc Q).symm
    have houtLen : out.2.length ≤ spkMaxWireLen ℓ :=
      sessionSchemeU_send_wire_length_le C K idA idB (gs₁.st Q) mVal coins
    refine OracleCompRel.pureP ⟨?_, ⟨d₁.record 3 Q out.1 ⟨p0, mVal, out.2⟩ isCh, ?_,
      tier2GsRel_record_preserves hrel₁ 3 Q out.1 ⟨p0, mVal, out.2⟩ isCh rfl houtLen⟩,
      partyReachInv_record C K hinv₁ 3 Q
        (partyReachInv_send C K (P := P) rfl (hinv₁ Q) mVal.toList coins) ⟨p0, mVal, out.2⟩ isCh,
      ?_, by rw [← hStepSim]; exact kemTrackTier2Inv_stepSendSim C.F K _ Q coins htrInv,
      ?_, fun wp hwp => by
        rcases List.mem_cons.mp hwp with rfl | hmem
        · exact houtLen
        · exact hhwLen wp hmem⟩
    · rw [pair_ev]; exact hrdec (some out.2) (.some (.snd .v0)) ρ₃ (some_ev _ _)
    · rw [pair_ev, pair_ev, hrecGs]; rfl
    · simp [kfOut, hcand, Expr.eval, Expr.v1]
    · rw [pair_ev, pair_ev, pair_ev, hhwEval]

private theorem hop2TrArmTier2TrackC_rel
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (extractPtPrfIface ℓ Pt))
    {stepOf : BitVec 256 → Pt → Hop2Comp Pt (BitVec 256)} (hM : Hop2EvalSpec M stepOf)
    (qep : ℕ) {Γ : List (Ty ASig)}
    (gsE : Expr AOps Γ (tier2GsTy ℓ Pt))
    (sessTrE : Expr AOps Γ (kemSessionTrackTier2T ℓ Pt))
    (trArg : Expr AOps Γ (.prod .bool (.prod PlainT (.opt BV512)))) (ρ : Env Γ)
    (Q : Party) (msg : Plain ℓ) (optR : Option (BitVec 512))
    (d : Tier2Gs ℓ) (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes) (aux : Hop2Aux Pt)
    (tr : KemFailTrackState C.F) (hw : List (Bytes × Party))
    (hgsE : gsE.eval ρ = tier2GsEnc Pt d)
    (hsessE : sessTrE.eval ρ = (kemTrackTier2Enc (kemBridgeToSim tr), honestWiresTier2Enc ℓ hw))
    (htrE : trArg.eval ρ = (partyEnc Q, (msg, optR)))
    (hrel : Tier2GsRel ℓ gs d)
    (hinv : ∀ Q', PartyReachInv C K (gs.st Q'))
    (htrInv : KemTrackTier2Inv C.F K (kemBridgeToSim tr))
    (hhwLen : ∀ wp ∈ hw, wp.1.length ≤ spkMaxWireLen ℓ) :
    OracleCompRel
      (fun r₁ r₂ =>
        (e2eSessionCodec ℓ Pt).rdec (.inl (.inl (.inl (.inl (Q, msg, optR))))) r₁.1 = r₂.1.1 ∧
        r₂.1.2.2 = aux ∧
        (∃ d' : Tier2Gs ℓ, r₁.2.1 = tier2GsEnc Pt d' ∧ Tier2GsRel ℓ r₂.1.2.1 d') ∧
        (∀ Q' : Party, PartyReachInv C K (r₂.1.2.1.st Q')) ∧
        r₁.2.2.1 = kemTrackTier2Enc (kemBridgeToSim r₂.2.1) ∧
        KemTrackTier2Inv C.F K (kemBridgeToSim r₂.2.1) ∧
        r₁.2.2.2 = honestWiresTier2Enc ℓ r₂.2.2 ∧
        (∀ wp ∈ r₂.2.2, wp.1.length ≤ spkMaxWireLen ℓ))
      ((hop2TrArmTier2TrackC C K Dh encPt encT decT lam M qep gsE sessTrE trArg).eval ρ)
      (((hop2LiftTrackHalted (Pt := Pt) (ℓ := ℓ)
        (transmitRTrackHalted C.F K
          (sessionSchemeU (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ)
          3 qep (configRefuseEarlyBobCorr (Pt := Pt) decT encT) (Q, msg, optR))).run
        (gs, aux)).run (tr, hw)) := by
  let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  let sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain :=
    .inl (.inl (.inl (.inl (Q, msg, optR))))
  apply oracleCompRel_hop2LiftTrackHalted C K (fun x y => (e2eSessionCodec ℓ Pt).rdec sq x = y)
  rw [hop2TrArmTier2TrackC, comp_eval_bind, comp_eval_ret, pure_bind, pair_ev, pair_ev,
    hgsE, hsessE, htrE]
  let sessV : (kemSessionTrackTier2T ℓ Pt).denote :=
    (kemTrackTier2Enc (kemBridgeToSim tr), honestWiresTier2Enc ℓ hw)
  let t0 : Ty ASig :=
    .prod (tier2GsTy ℓ Pt) (.prod (kemSessionTrackTier2T ℓ Pt)
      (.prod .bool (.prod PlainT (.opt BV512))))
  let ρ₀ : Env (S := ASig) (t0 :: Γ) := .cons (tier2GsEnc Pt d, (sessV, (partyEnc Q, (msg, optR)))) ρ
  have hguard :
      (orE (.not (sendOKTier2E (.fst .v0) (.fst (.snd (.snd .v0))))) (gsWinTier2E (.fst .v0)) :
        Expr AOps (t0 :: Γ) .bool).eval ρ₀ =
      (!((configRefuseEarlyBobCorr (Pt := Pt) decT encT :
          ConfigR (GhostState Bytes) (Plain ℓ) Bytes).sendOK gs Q) || gs.win) := by
    rw [orE_eval, eval_gsWinTier2E _ ρ₀ d rfl, hrel.h_win]
    have hsok : (Expr.not (sendOKTier2E (.fst .v0) (.fst (.snd (.snd .v0)))) :
        Expr AOps (t0 :: Γ) .bool).eval ρ₀ =
        !((configRefuseEarlyBobCorr (Pt := Pt) decT encT :
            ConfigR (GhostState Bytes) (Plain ℓ) Bytes).sendOK gs Q) := by
      dsimp only [Expr.eval]; rw [eval_sendOKTier2E decT encT _ _ ρ₀ gs d Q hrel rfl rfl]
    rw [hsok]
  generalize hcfg :
    (configRefuseEarlyBobCorr (Pt := Pt) decT encT :
      ConfigR (GhostState Bytes) (Plain ℓ) Bytes) = cfg at hguard ⊢
  rw [comp_eval_ite]
  change OracleCompRel _
    (if (orE (.not (sendOKTier2E (.fst .v0) (.fst (.snd (.snd .v0))))) (gsWinTier2E (.fst .v0)) :
          Expr AOps (t0 :: Γ) .bool).eval ρ₀ then _ else _)
    (liftM (((transmitRTrackHalted C.F K (sessionSchemeU P ℓ) 3 qep cfg (Q, msg, optR)).run gs).run
      (tr, hw)))
  rw [hguard]
  unfold transmitRTrackHalted
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases hok : cfg.sendOK gs Q with
  | false =>
    simp only [Bool.not_false, Bool.true_or, ↓reduceIte, comp_eval_ret, StateT.run_pure,
      liftM_prob_pure]
    refine OracleCompRel.pureP ⟨?_, ⟨d, rfl, hrel⟩, hinv, rfl, htrInv, rfl, hhwLen⟩
    rw [pair_ev, eval_tier2SmRWireE, none_ev]
    exact e2eSessionCodec_rdec_tier2SmRenc (Pt := Pt) sq none
  | true =>
    simp only [Bool.not_true, Bool.false_or]
    by_cases hwin : gs.win = true
    · simp only [hwin, ↓reduceIte, comp_eval_ret]
      refine OracleCompRel.pureP ⟨?_, ⟨d, rfl, hrel⟩, hinv, rfl, htrInv, rfl, hhwLen⟩
      rw [pair_ev, eval_tier2SmRWireE, none_ev]
      exact e2eSessionCodec_rdec_tier2SmRenc (Pt := Pt) sq none
    · simp only [Bool.not_eq_true] at hwin
      simp only [hwin, Bool.false_eq_true, ↓reduceIte, stateT_lift_prob_run2_bind, liftM_prob_bind]
      rw [comp_eval_bind, tier2SamIfNec512C_eval M hM _ ρ₀ optR rfl]
      refine OracleCompRel.bind_same _ _ _ fun ⟨coins, bad⟩ _ => ?_
      let ρ₁ : Env (S := ASig) (.prod BV512 .bool :: t0 :: Γ) := .cons (coins, bad) ρ₀
      rw [comp_eval_caseOpt, eval_epMgmtTier2E 3 qep _ _ _ ρ₁ d Q rfl rfl]
      have hbad : (Expr.snd (Expr.v0 (O := AOps)) :
          Expr AOps (.prod BV512 .bool :: t0 :: Γ) .bool).eval ρ₁ = bad := rfl
      rw [hbad]
      have ⟨hep_none, hep_rel⟩ := hrel.epMgmt_preserves 3 qep Q bad
      cases hep_gs : gs.epMgmt 3 qep Q bad with
      | none =>
        cases hep_d : d.epMgmt 3 qep Q bad with
        | none =>
          simp only [Option.map_none, StateT.run_pure, liftM_prob_pure, comp_eval_ret]
          refine OracleCompRel.pureP ⟨?_, ⟨d, rfl, hrel⟩, hinv, rfl, htrInv, rfl, hhwLen⟩
          rw [pair_ev, eval_tier2SmRWireE, none_ev]
          exact e2eSessionCodec_rdec_tier2SmRenc (Pt := Pt) sq none
        | some d₁ => simp [hep_gs, hep_d] at hep_none
      | some gs₁ =>
        cases hep_d : d.epMgmt 3 qep Q bad with
        | none => simp [hep_gs, hep_d] at hep_none
        | some d₁ =>
          simp only [Option.map_some]
          exact hop2SendPostEpTier2Track_rel C K Dh encPt encT decT idA idB lam M hM
            (tailT := .prod PlainT (.opt BV512))
            ((e2eSessionCodec ℓ Pt).rdec sq)
            (fun w _ e ρ' he => by
              rw [eval_tier2SmRWireE, he]
              exact e2eSessionCodec_rdec_tier2SmRenc (Pt := Pt) sq w)
            false msg Q (msg, optR) coins bad d d₁ gs gs₁ tr hw ρ
            (.fst (.snd (.snd (.snd .v3)))) (.fst (.snd (.snd (.snd .v4))))
            (fun _ => rfl) (fun _ _ => rfl)
            hrel hinv (hep_rel gs₁ d₁ hep_gs hep_d)
            (fun Q' => by rw [epMgmt_st_eq hep_gs]; exact hinv Q') htrInv hhwLen

private theorem hop2ChArmTier2TrackC_rel
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (extractPtPrfIface ℓ Pt))
    {stepOf : BitVec 256 → Pt → Hop2Comp Pt (BitVec 256)} (hM : Hop2EvalSpec M stepOf)
    (qep : ℕ) {Γ : List (Ty ASig)}
    (gsE : Expr AOps Γ (tier2GsTy ℓ Pt))
    (sessTrE : Expr AOps Γ (kemSessionTrackTier2T ℓ Pt))
    (chArg : Expr AOps Γ (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))))) (ρ : Env Γ)
    (Q : Party) (m₀ m₁ : Plain ℓ) (optR : Option (BitVec 512))
    (d : Tier2Gs ℓ) (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes) (aux : Hop2Aux Pt)
    (tr : KemFailTrackState C.F) (hw : List (Bytes × Party))
    (hgsE : gsE.eval ρ = tier2GsEnc Pt d)
    (hsessE : sessTrE.eval ρ = (kemTrackTier2Enc (kemBridgeToSim tr), honestWiresTier2Enc ℓ hw))
    (hchE : chArg.eval ρ = (partyEnc Q, (m₀, (m₁, optR))))
    (hrel : Tier2GsRel ℓ gs d)
    (hinv : ∀ Q', PartyReachInv C K (gs.st Q'))
    (htrInv : KemTrackTier2Inv C.F K (kemBridgeToSim tr))
    (hhwLen : ∀ wp ∈ hw, wp.1.length ≤ spkMaxWireLen ℓ) :
    OracleCompRel
      (fun r₁ r₂ =>
        (e2eSessionCodec ℓ Pt).rdec (.inl (.inl (.inl (.inr (Q, m₀, m₁, optR))))) r₁.1 = r₂.1.1 ∧
        r₂.1.2.2 = aux ∧
        (∃ d' : Tier2Gs ℓ, r₁.2.1 = tier2GsEnc Pt d' ∧ Tier2GsRel ℓ r₂.1.2.1 d') ∧
        (∀ Q' : Party, PartyReachInv C K (r₂.1.2.1.st Q')) ∧
        r₁.2.2.1 = kemTrackTier2Enc (kemBridgeToSim r₂.2.1) ∧
        KemTrackTier2Inv C.F K (kemBridgeToSim r₂.2.1) ∧
        r₁.2.2.2 = honestWiresTier2Enc ℓ r₂.2.2 ∧
        (∀ wp ∈ r₂.2.2, wp.1.length ≤ spkMaxWireLen ℓ))
      ((hop2ChArmTier2TrackC C K Dh encPt encT decT lam M qep gsE sessTrE chArg).eval ρ)
      (((hop2LiftTrackHalted (Pt := Pt) (ℓ := ℓ)
        (challRTrackHalted C.F K
          (sessionSchemeU (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ)
          3 qep (configRefuseEarlyBobCorr (Pt := Pt) decT encT) (Q, m₀, m₁, optR))).run
        (gs, aux)).run (tr, hw)) := by
  let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  let sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain :=
    .inl (.inl (.inl (.inr (Q, m₀, m₁, optR))))
  apply oracleCompRel_hop2LiftTrackHalted C K (fun x y => (e2eSessionCodec ℓ Pt).rdec sq x = y)
  rw [hop2ChArmTier2TrackC, comp_eval_bind, comp_eval_ret, pure_bind, pair_ev, pair_ev,
    hgsE, hsessE, hchE]
  let sessV : (kemSessionTrackTier2T ℓ Pt).denote :=
    (kemTrackTier2Enc (kemBridgeToSim tr), honestWiresTier2Enc ℓ hw)
  let t0 : Ty ASig :=
    .prod (tier2GsTy ℓ Pt) (.prod (kemSessionTrackTier2T ℓ Pt)
      (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512)))))
  let ρ₀ : Env (S := ASig) (t0 :: Γ) :=
    .cons (tier2GsEnc Pt d, (sessV, (partyEnc Q, (m₀, (m₁, optR))))) ρ
  have hguard :
      (orE (.not (sendOKTier2E (.fst .v0) (.fst (.snd (.snd .v0))))) (gsWinTier2E (.fst .v0)) :
        Expr AOps (t0 :: Γ) .bool).eval ρ₀ =
      (!((configRefuseEarlyBobCorr (Pt := Pt) decT encT :
          ConfigR (GhostState Bytes) (Plain ℓ) Bytes).sendOK gs Q) || gs.win) := by
    rw [orE_eval, eval_gsWinTier2E _ ρ₀ d rfl, hrel.h_win]
    have hsok : (Expr.not (sendOKTier2E (.fst .v0) (.fst (.snd (.snd .v0)))) :
        Expr AOps (t0 :: Γ) .bool).eval ρ₀ =
        !((configRefuseEarlyBobCorr (Pt := Pt) decT encT :
            ConfigR (GhostState Bytes) (Plain ℓ) Bytes).sendOK gs Q) := by
      dsimp only [Expr.eval]; rw [eval_sendOKTier2E decT encT _ _ ρ₀ gs d Q hrel rfl rfl]
    rw [hsok]
  generalize hcfg :
    (configRefuseEarlyBobCorr (Pt := Pt) decT encT :
      ConfigR (GhostState Bytes) (Plain ℓ) Bytes) = cfg at hguard ⊢
  rw [comp_eval_ite]
  change OracleCompRel _
    (if (orE (.not (sendOKTier2E (.fst .v0) (.fst (.snd (.snd .v0))))) (gsWinTier2E (.fst .v0)) :
          Expr AOps (t0 :: Γ) .bool).eval ρ₀ then _ else _)
    (liftM (((challRTrackHalted C.F K (sessionSchemeU P ℓ) 3 qep cfg (Q, m₀, m₁, optR)).run gs).run
      (tr, hw)))
  rw [hguard]
  unfold challRTrackHalted
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases hok : cfg.sendOK gs Q with
  | false =>
    simp only [Bool.not_false, Bool.true_or, ↓reduceIte, comp_eval_ret, StateT.run_pure,
      liftM_prob_pure]
    refine OracleCompRel.pureP ⟨?_, ⟨d, rfl, hrel⟩, hinv, rfl, htrInv, rfl, hhwLen⟩
    rw [pair_ev, eval_tier2SmRWireE, none_ev]
    exact e2eSessionCodec_rdec_tier2SmRenc (Pt := Pt) sq none
  | true =>
    simp only [Bool.not_true, Bool.false_or]
    by_cases hwin : gs.win = true
    · simp only [hwin, ↓reduceIte, comp_eval_ret]
      refine OracleCompRel.pureP ⟨?_, ⟨d, rfl, hrel⟩, hinv, rfl, htrInv, rfl, hhwLen⟩
      rw [pair_ev, eval_tier2SmRWireE, none_ev]
      exact e2eSessionCodec_rdec_tier2SmRenc (Pt := Pt) sq none
    · simp only [Bool.not_eq_true] at hwin
      simp only [hwin, Bool.false_eq_true, ↓reduceIte, stateT_lift_prob_run2_bind, liftM_prob_bind]
      rw [comp_eval_bind, tier2SamIfNec512C_eval M hM _ ρ₀ optR rfl]
      refine OracleCompRel.bind_same _ _ _ fun ⟨coins, bad⟩ _ => ?_
      let ρ₁ : Env (S := ASig) (.prod BV512 .bool :: t0 :: Γ) := .cons (coins, bad) ρ₀
      rw [comp_eval_caseOpt, eval_epMgmtTier2E 3 qep _ _ _ ρ₁ d Q rfl rfl]
      have hbad : (Expr.snd (Expr.v0 (O := AOps)) :
          Expr AOps (.prod BV512 .bool :: t0 :: Γ) .bool).eval ρ₁ = bad := rfl
      rw [hbad]
      have ⟨hep_none, hep_rel⟩ := hrel.epMgmt_preserves 3 qep Q bad
      cases hep_gs : gs.epMgmt 3 qep Q bad with
      | none =>
        cases hep_d : d.epMgmt 3 qep Q bad with
        | none =>
          simp only [Option.map_none, StateT.run_pure, liftM_prob_pure, comp_eval_ret]
          refine OracleCompRel.pureP ⟨?_, ⟨d, rfl, hrel⟩, hinv, rfl, htrInv, rfl, hhwLen⟩
          rw [pair_ev, eval_tier2SmRWireE, none_ev]
          exact e2eSessionCodec_rdec_tier2SmRenc (Pt := Pt) sq none
        | some d₁ => simp [hep_gs, hep_d] at hep_none
      | some gs₁ =>
        cases hep_d : d.epMgmt 3 qep Q bad with
        | none => simp [hep_gs, hep_d] at hep_none
        | some d₁ =>
          have hrel₁ : Tier2GsRel ℓ gs₁ d₁ := hep_rel gs₁ d₁ hep_gs hep_d
          have hinv₁ : ∀ Q', PartyReachInv C K (gs₁.st Q') := by
            intro Q'; rw [epMgmt_st_eq hep_gs]; exact hinv Q'
          simp only [Option.map_some]
          let ρ₂ : Env (S := ASig) (tier2GsTy ℓ Pt :: .prod BV512 .bool :: t0 :: Γ) :=
            .cons (tier2GsEnc Pt d₁) ρ₁
          have hsafe :
              (Expr.not (safeChTier2E 3 .v0 (.fst (.snd (.snd .v2)))) :
                Expr AOps _ .bool).eval ρ₂ = !(gs₁.safeCh 3 Q) := by
            dsimp only [Expr.eval]
            rw [eval_safeChTier2E 3 _ _ ρ₂ d₁ Q rfl rfl, hrel₁.safeCh_eq 3 Q]
          have hcallow : cfg.base.challAllowedIn (gs₁.epoch Q) = true := by rw [← hcfg]; rfl
          have hcmsg : cfg.base.challMsg (gs₁.epoch Q) = none := by rw [← hcfg]; rfl
          rw [comp_eval_ite, hsafe, hcallow]
          simp only [Bool.not_true, Bool.or_false]
          cases hsc : gs₁.safeCh 3 Q with
          | false =>
            simp only [Bool.not_false, ↓reduceIte, StateT.run_pure, liftM_prob_pure, comp_eval_ret]
            refine OracleCompRel.pureP ⟨?_, ⟨d, rfl, hrel⟩, hinv, rfl, htrInv, rfl, hhwLen⟩
            rw [pair_ev, eval_tier2SmRWireE, none_ev]
            exact e2eSessionCodec_rdec_tier2SmRenc (Pt := Pt) sq none
          | true =>
            simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hcmsg, Option.getD_none]
            exact hop2SendPostEpTier2Track_rel C K Dh encPt encT decT idA idB lam M hM
              (tailT := .prod PlainT (.prod PlainT (.opt BV512)))
              ((e2eSessionCodec ℓ Pt).rdec sq)
              (fun w _ e ρ' he => by
                rw [eval_tier2SmRWireE, he]
                exact e2eSessionCodec_rdec_tier2SmRenc (Pt := Pt) sq w)
              true (if gs.b then m₁ else m₀) Q (m₀, (m₁, optR)) coins bad d d₁ gs gs₁ tr hw ρ
              (.ite (gsBTier2E (.fst .v3)) (.fst (.snd (.snd (.snd (.snd .v3)))))
                (.fst (.snd (.snd (.snd .v3)))))
              (.ite (gsBTier2E (.fst .v4)) (.fst (.snd (.snd (.snd (.snd .v4)))))
                (.fst (.snd (.snd (.snd .v4)))))
              (fun kf => by rw [ite_ev, eval_gsBTier2E _ _ d rfl, hrel.h_b]; rfl)
              (fun out kf => by rw [ite_ev, eval_gsBTier2E _ _ d rfl, hrel.h_b]; rfl)
              hrel hinv hrel₁ hinv₁ htrInv hhwLen

private def flattenStateT {S₁ S₂ : Type} {M : Type → Type} [Monad M] {α : Type}
    (m : StateT S₁ (StateT S₂ M) α) : StateT (S₁ × S₂) M α :=
  StateT.mk fun s => do
    let z ← (m.run s.1).run s.2
    pure (z.1.1, (z.1.2, z.2))

private theorem simulateQ_flattenStateT {ι : Type} {ospec : OracleSpec.{0, 0} ι}
    {S₁ S₂ α : Type} {M : Type → Type} [Monad M] [LawfulMonad M]
    (impl : QueryImpl ospec (StateT S₁ (StateT S₂ M)))
    (oa : OracleComp ospec α) (s₁ : S₁) (s₂ : S₂) :
    (simulateQ (fun q => flattenStateT (impl q)) oa).run (s₁, s₂) =
      (fun z => (z.1.1, (z.1.2, z.2))) <$> (((simulateQ impl oa).run s₁).run s₂) := by
  induction oa using OracleComp.inductionOn generalizing s₁ s₂ with
  | pure a => simp [flattenStateT]
  | query_bind q k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_eq, StateT.run_bind, flattenStateT, StateT.run_mk,
      map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    congr 1; funext z
    simpa only [flattenStateT, map_eq_bind_pure_comp, Function.comp_def] using ih z.1.1 z.1.2 z.2

private theorem recvResultEnc_recvResultDec
    (v : (_root_.ReductionDsl.recvResultT (ℓ := ℓ) (Pt := Pt)).denote) :
    recvResultEnc (recvResultDec (ℓ := ℓ) (Pt := Pt) v) = v := by
  rcases v with ⟨⟨⟩⟩ | ⟨t, i, _ | m⟩ <;> rfl

private theorem rdec_deliver_map_recvResultEnc (Q : Party) (c : Bytes)
    (smOut : (smRT (ℓ := ℓ) (Pt := Pt) GhostStT).denote) (rr? : Option (RecvResult (Plain ℓ)))
    (h : (e2eSessionCodec ℓ Pt).rdec (.inl (.inl (.inr (Q, c)))) smOut = rr?) :
    smOut.2.1 = rr?.map recvResultEnc := by
  have hdec : smOut.2.1.map (recvResultDec (ℓ := ℓ) (Pt := Pt)) = rr? := h
  rw [← hdec, Option.map_map]
  rcases smOut.2.1 with _ | v
  · rfl
  · simp [Function.comp_def, recvResultEnc_recvResultDec]

private theorem hop2StepTier2TrackC_rel
    (hinj : Function.Injective encT) (hℓ : ℓ < 10 ^ 6)
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (extractPtPrfIface ℓ Pt))
    {stepOf : BitVec 256 → Pt → Hop2Comp Pt (BitVec 256)} (hM : Hop2EvalSpec M stepOf)
    (qep k m : ℕ) (s : BitVec 256) (chall : BitVec 256 × BitVec 256)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (stV : (hop2HaltedTier2StTy ℓ Pt).denote)
    (gat : (GameState (GhostState Bytes) (Plain ℓ) Bytes × Hop2Aux Pt) ×
      KemFailSessionTrack C.F Bytes)
    (hs : Hop2Tier2TrackSimRel C K encT s chall (m + 1) stV gat) :
    OracleCompRel
      (fun r₁ r₂ =>
        r₁.1 = r₂.1 ∧ Hop2Tier2TrackSimRel C K encT s chall m r₁.2 r₂.2)
      (((hop2GameTier2TrackRed (ℓ := ℓ) C K Dh encPt encT decT idA idB lam M qep k).impl
          (.inr sq)).run stV)
      ((flattenStateT
        (hop2ImplTrackHalted (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
          K Dh encT decT qep s ⟨k, chall, stepOf chall.1⟩ (.inr sq))).run gat) := by
  rcases gat with ⟨⟨gs, aux⟩, ⟨tr, hw⟩⟩
  rcases stV with ⟨⟨sV, gsV, auxV, challV⟩, ⟨trV, hwV⟩⟩
  rcases hs with ⟨⟨hsEq, ⟨d, rfl, hrel⟩, haux, hchallEq⟩, hinv, htrV, htrInv, hhwV, hhwLen⟩
  dsimp only at hsEq hchallEq htrV hhwV
  subst sV; subst challV; subst trV; subst hwV
  let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  let hyb : Hop2Hyb Pt := ⟨k, chall, stepOf chall.1⟩
  let fullV : (hop2Tier2FullStTy ℓ Pt).denote := (s, (tier2GsEnc Pt d, (auxV, chall)))
  let sessV : (kemSessionTrackTier2T ℓ Pt).denote :=
    (kemTrackTier2Enc (kemBridgeToSim tr), honestWiresTier2Enc ℓ hw)
  let hstV : (hop2HaltedTier2StTy ℓ Pt).denote := (fullV, sessV)
  dsimp only [CostedReduction.impl, handlerImpl, hop2GameTier2TrackRed]
  let ρs : Env (S := ASig) [hop2HaltedTier2StTy ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)] :=
    .cons hstV (.cons ((e2eSessionCodec ℓ Pt).qenc sq) .nil)
  change OracleCompRel _
    ((hop2StepTier2TrackC C K Dh encPt encT decT lam M qep k).eval ρs >>=
      fun p => pure ((e2eSessionCodec ℓ Pt).rdec sq p.1, p.2)) _
  rcases sq with ((((⟨Q, msg, optR⟩ | ⟨Q, m₀, m₁, optR⟩) | ⟨Q, c⟩) | ⟨Q, c⟩) | Q)
  · dsimp only [hop2StepTier2TrackC, hop2ImplTrackHalted, flattenStateT, ρs,
      e2eSessionCodec, _root_.ReductionDsl.smQenc]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Expr.v1, Env.get]
    rw [comp_eval_bind]
    simp only [partyToBool_eq_partyEnc, bind_assoc]
    exact OracleCompRel.bind
      (hop2TrArmTier2TrackC_rel C K Dh encPt encT decT idA idB lam M hM qep
        (.fst (.snd (hst2Base C K Dh encPt encT decT lam .v1)))
        (hst2SessionTr C K Dh encPt encT decT lam .v1) .v0 _
        Q msg optR d gs aux tr hw rfl rfl rfl hrel hinv htrInv hhwLen)
      fun r₁ r₂ ⟨hr1, hauxEq, hd', hinv', htr', htrInv', hhw', hhwLen'⟩ => by
        rw [comp_eval_ret, pure_bind]
        exact .pureP ⟨hr1, ⟨rfl, hd', hauxEq ▸ haux, rfl⟩, hinv', htr', htrInv', hhw', hhwLen'⟩
  · dsimp only [hop2StepTier2TrackC, hop2ImplTrackHalted, flattenStateT, ρs,
      e2eSessionCodec, _root_.ReductionDsl.smQenc]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Expr.v1, Env.get]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Expr.v0, Env.get]
    rw [comp_eval_bind]
    simp only [partyToBool_eq_partyEnc, bind_assoc]
    exact OracleCompRel.bind
      (hop2ChArmTier2TrackC_rel C K Dh encPt encT decT idA idB lam M hM qep
        (.fst (.snd (hst2Base C K Dh encPt encT decT lam .v2)))
        (hst2SessionTr C K Dh encPt encT decT lam .v2) .v0 _
        Q m₀ m₁ optR d gs aux tr hw rfl rfl rfl hrel hinv htrInv hhwLen)
      fun r₁ r₂ ⟨hr1, hauxEq, hd', hinv', htr', htrInv', hhw', hhwLen'⟩ => by
        rw [comp_eval_ret, pure_bind]
        exact .pureP ⟨hr1, ⟨rfl, hd', hauxEq ▸ haux, rfl⟩, hinv', htr', htrInv', hhw', hhwLen'⟩
  · have hdlRhs :
        (flattenStateT
          (hop2ImplTrackHalted (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
            K Dh encT decT qep s ⟨k, chall, stepOf chall.1⟩
            (.inr (.inl (.inl (.inr (Q, c))))))).run ((gs, aux), (tr, hw)) =
        (((fun r => (r, updateKemFailOnDeliver C.F K (tr, hw) (Q, c) r.1)) <$>
            (hop2Deliver P Dh encT decT s hyb (Q, c)).run (gs, aux)) >>=
          fun z => pure (z.1.1, (z.1.2, z.2))) :=
      congrArg
        (fun (m : Hop2Comp Pt
            ((Option (RecvResult (Plain ℓ)) ×
                (GameState (GhostState Bytes) (Plain ℓ) Bytes × Hop2Aux Pt)) ×
              KemFailSessionTrack C.F Bytes)) =>
          m >>= fun z => pure (z.1.1, (z.1.2, z.2)))
        (hop2DeliverTrackHalted_run P K Dh encT decT s hyb (Q, c) (gs, aux) (tr, hw))
    have hcongr {α β : Type} {R : α → β → Prop} {x : Hop2Comp Pt α} {y₁ y₂ : Hop2Comp Pt β}
        (h : y₁ = y₂) (hr : OracleCompRel R x y₂) : OracleCompRel R x y₁ := h ▸ hr
    apply hcongr hdlRhs
    dsimp only [hop2StepTier2TrackC, ρs, e2eSessionCodec, _root_.ReductionDsl.smQenc]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Expr.v1, Env.get]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Expr.v0, Env.get]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Env.get]
    rw [comp_eval_bind, comp_eval_ret, pure_bind]
    rw [findRevHonestWireIdxTier2E_eval (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) hℓ
      (hst2Wires C K Dh encPt encT decT lam .v3) (.fst (.var .zero)) (.snd (.var .zero)) _
      hw Q c ?_ ?_ ?_ hhwLen]
    rotate_left
    · rfl
    · rfl
    · rfl
    rw [comp_eval_bind, comp_eval_ret, pure_bind, comp_eval_bind, wk1Comp_eval]
    simp only [hst2Base, Expr.eval, Expr.v4, Env.get, partyToBool_eq_partyEnc,
      hstV, fullV, sessV, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    have hFindEq :
        List.findIdx?
          (fun wp : Bytes × Party =>
            @BEq.beq Bytes instBEqOfDecidableEq wp.1 c && wp.2 == Q.other)
          hw.reverse =
        hw.reverse.findIdx? (fun wp => wp.1 == c && wp.2 == Q.other) := by
      congr 1; ext ⟨w, p⟩
      have hbeq : @BEq.beq Bytes instBEqOfDecidableEq w c = (w == c) :=
        Bool.eq_iff_iff.mpr (by simp only [beq_iff_eq])
      rw [hbeq]
    exact OracleCompRel.bind
      (hop2DlArmTier2C_rel C K Dh encPt encT decT idA idB lam hinj hℓ M hM k s chall Q c
        fullV gs aux ⟨rfl, ⟨d, rfl, hrel⟩, haux, rfl⟩ hinv)
      fun r₁ r₂ ⟨hr1, hfull', hinv'⟩ => by
        rw [comp_eval_ret, pure_bind]
        have hrrMap : r₁.1.2.1 = r₂.1.map recvResultEnc :=
          rdec_deliver_map_recvResultEnc Q c r₁.1 r₂.1 hr1
        refine OracleCompRel.pureP ⟨hr1, hfull', hinv', ?_, ?_, ?_, ?_⟩
        · refine Eq.trans (kemOnDeliverPostTier2E_eval (C := C) (K := K) (Dh := Dh)
            (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
            (.fst .v3) .v2 (.fst (.snd (.fst (.var .zero))))
            (hst2Tr C K Dh encPt encT decT lam .v6) _
            Q (hw.reverse.findIdx? (fun wp => wp.1 == c && wp.2 == Q.other))
            r₂.1 (kemBridgeToSim tr) ?_ ?_ hrrMap ?_ htrInv) ?_
          · exact (partyToBool_eq_partyEnc Q).symm
          · rfl
          · rfl
          · unfold updateKemFailOnDeliver; dsimp only; rw [hFindEq]
            rcases r₂.1 with _ | (_ | ⟨_, _, _⟩)
            · rfl
            · rfl
            · cases hw.reverse.findIdx? (fun wp => wp.1 == c && wp.2 == Q.other) with
              | none => rfl
              | some j => simp only [kemBridgeToSim_stepDeliver]
        · unfold updateKemFailOnDeliver; dsimp only; rw [hFindEq]
          rcases r₂.1 with _ | (_ | ⟨_, _, _⟩)
          · exact htrInv
          · exact htrInv
          · cases hw.reverse.findIdx? (fun wp => wp.1 == c && wp.2 == Q.other) with
            | none => exact htrInv
            | some j =>
              simpa only [kemBridgeToSim_stepDeliver] using
                kemTrackTier2Inv_stepDeliverSim C.F K (kemBridgeToSim tr) Q j htrInv
        · unfold updateKemFailOnDeliver; split <;> rfl
        · unfold updateKemFailOnDeliver; split <;> exact hhwLen
  · dsimp only [hop2StepTier2TrackC, hop2ImplTrackHalted, flattenStateT, ρs,
      e2eSessionCodec, _root_.ReductionDsl.smQenc]
    simp only [liftHop2NoTrackM, StateT.run_mk, StateT.run_lift]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Expr.v1, Env.get]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Expr.v0, Env.get]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Env.get]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Env.get]
    rw [comp_eval_bind, comp_eval_ret, pure_bind, comp_eval_bind, wk1Comp_eval]
    simp only [hst2Base, hst2SessionTr, Expr.eval, Expr.v4, Env.get,
      partyToBool_eq_partyEnc, hstV, fullV, sessV, bind_assoc, pure_bind]
    exact OracleCompRel.bind
      (hop2IjArmTier2C_rel C K Dh encPt encT decT idA idB lam hinj hℓ M hM qep k s chall Q c
        fullV gs aux ⟨rfl, ⟨d, rfl, hrel⟩, haux, rfl⟩ hinv)
      fun r₁ r₂ ⟨hr1, hfull', hinv'⟩ => by
        rw [comp_eval_ret, pure_bind]
        exact OracleCompRel.pureP ⟨hr1, hfull', hinv', rfl, htrInv, rfl, hhwLen⟩
  · dsimp only [hop2StepTier2TrackC, hop2ImplTrackHalted, flattenStateT, ρs,
      e2eSessionCodec, _root_.ReductionDsl.smQenc]
    simp only [liftHop2NoTrackM, StateT.run_mk, StateT.run_lift]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Expr.v1, Env.get]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Expr.v0, Env.get]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Env.get]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Env.get]
    rw [comp_eval_ret]
    simp only [pure_bind, bind_assoc]
    let tDl : Ty ASig := .prod .bool (B 32)
    let tCh : Ty ASig := .prod .bool (.prod PlainT (.prod PlainT (.opt BV512)))
    let ρ_cr : Env (S := ASig)
        [.bool, .sum tDl .bool, .sum tDl (.sum tDl .bool),
          .sum tCh (.sum tDl (.sum tDl .bool)),
          hop2HaltedTier2StTy ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)] :=
      .cons (partyEnc Q)
        (.cons (Sum.inr (partyEnc Q))
          (.cons (Sum.inr (Sum.inr (partyEnc Q)))
            (.cons (Sum.inr (Sum.inr (Sum.inr (partyEnc Q))))
              (.cons hstV (.cons ((e2eSessionCodec ℓ Pt).qenc (.inr Q)) .nil)))))
    have hcr := hop2CrArmTier2E_rel C K Dh encPt encT decT lam
      (.fst (.snd (hst2Base C K Dh encPt encT decT lam .v4))) .v0 ρ_cr Q d gs aux
      rfl rfl hrel hinv
    let outCr := (hop2CrArmTier2E C K Dh encPt encT decT lam
      (.fst (.snd (hst2Base C K Dh encPt encT decT lam .v4))) .v0).eval ρ_cr
    rw [letE_eval]
    change OracleCompRel _
      (pure ((e2eSessionCodec ℓ Pt).rdec (.inr Q) outCr.1,
        ((s, (outCr.2, (auxV, chall))), sessV)))
      ((StateT.run (hop2Lift (corrR (configRefuseEarlyBobCorr decT encT) Q)) (gs, aux)) >>=
        fun r₂ => pure (r₂.1, (r₂.2, (tr, hw))))
    have hlhs :
        (pure ((e2eSessionCodec ℓ Pt).rdec (.inr Q) outCr.1,
          ((s, (outCr.2, (auxV, chall))), sessV)) : Hop2Comp Pt _) =
        ((pure outCr : Hop2Comp Pt _) >>= fun r₁ =>
          pure ((e2eSessionCodec ℓ Pt).rdec (.inr Q) r₁.1,
            ((s, (r₁.2, (auxV, chall))), sessV))) := (pure_bind _ _).symm
    rw [hlhs]
    exact OracleCompRel.bind hcr fun r₁ r₂ ⟨hr1, hauxEq, hd', hinv'⟩ =>
      .pureP ⟨hr1, ⟨rfl, hd', hauxEq ▸ haux, rfl⟩, hinv', rfl, htrInv, rfl, hhwLen⟩

private noncomputable def hop2InitBridgeTrackImplLocal (k : ℕ)
    (sc : BitVec 256 × (BitVec 256 × BitVec 256)) :
    Hop2Comp Pt
      (Unit × ((GameState (GhostState Bytes) (Plain ℓ) Bytes × Hop2Aux Pt) ×
        KemFailSessionTrack C.F Bytes)) := do
  let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  let b ← (liftM ($ᵗ Bool : ProbComp Bool) : Hop2Comp Pt Bool)
  let ck0 ← hop2Unif (Pt := Pt)
  let x ← hop2Unif (Pt := Pt)
  let alice ← hop2Unif (Pt := Pt)
  let pqr ← hop2Unif (Pt := Pt)
  let u1 ← hop2Unif (Pt := Pt)
  let ck1 := if k = 0 then sc.2.2 else u1
  let I0 := Dh.dh x (Dh.dh alice Dh.base)
  let spk := (KeyPair.generate P.C x).publicKey
  let sessA := ((SessionState.new currentVersion P.idA P.idB 0
    (P.spqr.init .a2b pqr)).addReceiverChain spk ⟨ck0, 0⟩).setSenderChain
    (KeyPair.generate P.C alice) ⟨ck1, 0⟩
  let stA : GhostState Bytes := ⟨.A, sessA.setUnacknowledgedPreKeyMessage, 0, [0]⟩
  let stB := P.initB ⟨0, ck0, x, alice, pqr⟩
  let initSt : GameState (GhostState Bytes) (Plain ℓ) Bytes :=
    { st := fun Q => match Q with | .A => stA | .B => stB, b := b }
  let aux0 : Hop2Aux Pt :=
    { made := [((0, I0), ck1)]
      idx := fun Q => match Q with | .A => some 1 | .B => some 0
      coins := fun Q => match Q with | .A => alice | .B => x }
  return ((), ((initSt, aux0), (initKemFailTrack C.F pqr, [])))

private theorem hop2InitBodyTier2TrackC_rel
    (hinj : Function.Injective encT) (qAdv k : ℕ)
    (s : BitVec 256) (chall : BitVec 256 × BitVec 256) :
    OracleCompRel
      (fun r₁ r₂ =>
        r₁.1 = r₂.1 ∧ Hop2Tier2TrackSimRel C K encT s chall qAdv r₁.2 r₂.2)
      ((compCoinToPrf
        (hop2InitBodyTier2TrackC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k)).eval
        (.cons (s, chall) .nil))
      (hop2InitBridgeTrackImplLocal (ℓ := ℓ) (Pt := Pt) C K Dh idA idB k (s, chall)) := by
  let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  dsimp only [hop2InitBodyTier2TrackC, hop2InitBridgeTrackImplLocal, compCoinToPrf]
  simp only [comp_eval_bind, comp_eval_ret,
    compCoinToPrf_eval_eq_liftM, drawBoolCoin_eval, draw256Coin_eval]
  have hunif :
      (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) : Hop2Comp Pt (BitVec 256)) =
      hop2Unif (Pt := Pt) := rfl
  simp only [hunif]
  refine OracleCompRel.bind_same _ _ _ fun b _ => ?_
  refine OracleCompRel.bind_same _ _ _ fun ck0 _ => ?_
  refine OracleCompRel.bind_same _ _ _ fun x _ => ?_
  refine OracleCompRel.bind_same _ _ _ fun alice _ => ?_
  refine OracleCompRel.bind_same _ _ _ fun pqr _ => ?_
  refine OracleCompRel.bind_same _ _ _ fun u1 _ => ?_
  let ck1 : BitVec 256 := if k = 0 then chall.2 else u1
  let I0 : Pt := Dh.dh x (Dh.dh alice Dh.base)
  let spk := (KeyPair.generate P.C x).publicKey
  let sessA := ((SessionState.new currentVersion P.idA P.idB 0
    (P.spqr.init .a2b pqr)).addReceiverChain spk ⟨ck0, 0⟩).setSenderChain
    (KeyPair.generate P.C alice) ⟨ck1, 0⟩
  let stA : GhostState Bytes := ⟨.A, sessA.setUnacknowledgedPreKeyMessage, 0, [0]⟩
  let stB := P.initB ⟨0, ck0, x, alice, pqr⟩
  let Γ6 := [BV256, BV256, BV256, BV256, BV256, .bool, .prod BV256 (hop2ChallTy ℓ Pt)]
  let ρ6 : Env Γ6 :=
    .cons u1 (.cons pqr (.cons alice (.cons x (.cons ck0 (.cons b (.cons (s, chall) .nil))))))
  have hck1Eval :
      (if k = 0 then (Expr.snd (.snd (.v6 (O := AOps)))) else .v0).eval ρ6 = ck1 := by
    dsimp only [ck1]; split_ifs <;> rfl
  have hl := liftExpr_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (hop2InitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB)
    (.cons (t := Computational.Proofs.Game.PromotedCostedReds.SpkHop2RInProg.hop2InitArgT ℓ)
      (b, (x, ((0, ck1), (ck0, (alice, pqr))))) .nil)
  have hgs := eval_hop2InitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
    idA idB b x 0 ck1 ck0 alice pqr
  let argE : Expr AOps Γ6 _ :=
    .pair .v5 (.pair .v3 (.pair (.pair (sPureOp (.bv256Lit 0) .unit)
      (if k = 0 then (.snd (.snd .v6)) else .v0)) (.pair .v4 (.pair .v2 .v1))))
  have harg : argE.eval ρ6 =
      liftVal (Pt := Pt)
        (t := Computational.Proofs.Game.PromotedCostedReds.SpkHop2RInProg.hop2InitArgT ℓ)
        (b, (x, ((0, ck1), (ck0, (alice, pqr))))) := by
    simp only [argE, pair_eval, hck1Eval]; rfl
  let abE : Expr AOps Γ6 _ :=
    .fst (.letE argE (wk1Expr (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam)
      (hop2InitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB))))
  have habEval : abE.eval ρ6 = (stA, stB) := by
    have henv : (Env.cons (liftVal (Pt := Pt)
          (t := Computational.Proofs.Game.PromotedCostedReds.SpkHop2RInProg.hop2InitArgT ℓ)
          (b, (x, ((0, ck1), (ck0, (alice, pqr)))))) .nil : Env (S := ASig) [_]) =
      liftEnv (Pt := Pt)
        (.cons (t := Computational.Proofs.Game.PromotedCostedReds.SpkHop2RInProg.hop2InitArgT ℓ)
          (b, (x, ((0, ck1), (ck0, (alice, pqr))))) .nil) := rfl
    dsimp only [abE]; rw [fst_ev, letE_eval, harg, wk1Expr_eval, henv, hl, hgs]; rfl
  have hgs0Eval :
      (Expr.letE abE (initGsTier2E (.fst .v0) (.snd .v0) .v6)).eval ρ6 =
      tier2GsEnc Pt (Tier2Gs.init stA stB b) := by
    rw [letE_eval, habEval, eval_initGsTier2E]; rfl
  have hi0Eval :
      (sGroupOp (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam)
        .ptDh (.pair .v3 (sGroupOp .ptDh (.pair .v2 (sGroupOp .ptBase .unit))))).eval ρ6 = I0 := by
    rw [eval_sGroupOp, pair_eval, eval_sGroupOp, pair_eval, eval_sGroupOp]; rfl
  have hsessTr0 := initKemFailSessionTrackTier2E_eval (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) .v1 ρ6 pqr rfl
  change OracleCompRel _ (pure ((Expr.pair .unit _).eval ρ6)) _
  refine OracleCompRel.pureP ⟨trivial, ⟨rfl, ⟨Tier2Gs.init stA stB b, hgs0Eval,
    tier2GsRel_init_pair stA stB b⟩, ?_, rfl⟩, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨hop2TblRel_nil encT, ?_, rfl, rfl, rfl⟩
    simpa only [stMkTier2, auxMkTier2, pair_eval, eval_hop2TblSetE, eval_hop2TblInitE,
      hi0Eval, hck1Eval, Expr.eval] using
      hop2TblRel_cons hinj (hop2TblRel_nil encT) 0 I0 ck1
  · intro Q
    cases Q with
    | A =>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simpa [stA, sessA, P, paramsIdsWithSpqr, spqrV1SessionUniformCoins, SessionState.new,
          SessionState.addReceiverChain, SessionState.setSenderChain,
          SessionState.setUnacknowledgedPreKeyMessage] using topStateTight_init C.F K .a2b pqr
      · simp [SessionState.new, SessionState.addReceiverChain,
          SessionState.setSenderChain, SessionState.setUnacknowledgedPreKeyMessage, maxReceiverChains]
      · intro rch hrch
        simp only [SessionState.new, SessionState.addReceiverChain, SessionState.setSenderChain,
          SessionState.setUnacknowledgedPreKeyMessage, maxReceiverChains] at hrch
        have hrch' :
            rch = { senderRatchetKey := spk,
                    chainKey := some { key := ck0, index := 0 }, messageKeys := [] } := by
          simpa using hrch
        subst hrch'; simp [maxMessageKeys]
      · intro rch hrch mk hmk
        simp only [SessionState.new, SessionState.addReceiverChain, SessionState.setSenderChain,
          SessionState.setUnacknowledgedPreKeyMessage, maxReceiverChains] at hrch
        have hrch' :
            rch = { senderRatchetKey := spk,
                    chainKey := some { key := ck0, index := 0 }, messageKeys := [] } := by
          simpa using hrch
        subst hrch'; simp at hmk
      · simp [SessionState.new, SessionState.addReceiverChain,
          SessionState.setSenderChain, SessionState.setUnacknowledgedPreKeyMessage, maxReceiverChains]
    | B => exact partyReachInv_initB C K (P := P) rfl ⟨0, ck0, x, alice, pqr⟩
  · change ((initKemFailSessionTrackTier2E (C := C) (K := K) (Dh := Dh)
        (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) .v1).eval ρ6).1 = _
    rw [hsessTr0, kemBridgeToSim_init]; rfl
  · rw [kemBridgeToSim_init]; exact kemTrackTier2Inv_initSim C.F K pqr
  · change ((initKemFailSessionTrackTier2E (C := C) (K := K) (Dh := Dh)
        (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) .v1).eval ρ6).2 = _
    rw [hsessTr0]; rfl
  · intro wp hwp; cases hwp

private theorem hop2GameTier2TrackRed_eval
    (hinj : Function.Injective encT) (hℓ : ℓ < 10 ^ 6)
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (extractPtPrfIface ℓ Pt))
    {stepOf : BitVec 256 → Pt → Hop2Comp Pt (BitVec 256)} (hM : Hop2EvalSpec M stepOf)
    (q qep k : ℕ) (s : BitVec 256) (chall : BitVec 256 × BitVec 256)
    (A : Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hA : MakesAtMostQueries A q) :
    (hop2GameTier2TrackRed (ℓ := ℓ) C K Dh encPt encT decT idA idB lam M qep k).eval
        (fun _ => A) (s, chall) =
      hop2GameTrackHalted (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
        K ℓ Dh encT decT qep s ⟨k, chall, stepOf chall.1⟩ A := by
  let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  let hyb : Hop2Hyb Pt := ⟨k, chall, stepOf chall.1⟩
  let so : QueryImpl
      (unifSpec + CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (StateT ((GameState (GhostState Bytes) (Plain ℓ) Bytes × Hop2Aux Pt) ×
        KemFailSessionTrack C.F Bytes) (Hop2Comp Pt)) :=
    fun q' => flattenStateT (hop2ImplTrackHalted (ℓ := ℓ) P K Dh encT decT qep s hyb q')
  have hinit : OracleCompRel
      (fun r₁ r₂ => r₁.1 = r₂.1 ∧ Hop2Tier2TrackSimRel C K encT s chall q r₁.2 r₂.2)
      ((hop2GameTier2TrackRed (ℓ := ℓ) C K Dh encPt encT decT idA idB lam M qep k).init.eval
        (.cons (s, chall) .nil))
      (hop2InitBridgeTrackImplLocal (ℓ := ℓ) (Pt := Pt) C K Dh idA idB k (s, chall)) := by
    dsimp only [hop2GameTier2TrackRed]; rw [hM.embedCoin_eq]
    exact hop2InitBodyTier2TrackC_rel C K Dh encPt encT decT idA idB lam hinj q k s chall
  have hfin : ∀ (stV : (hop2HaltedTier2StTy ℓ Pt).denote)
      (gat : (GameState (GhostState Bytes) (Plain ℓ) Bytes × Hop2Aux Pt) ×
        KemFailSessionTrack C.F Bytes) (b' : Bool),
      Hop2Tier2TrackSimRel C K encT s chall 0 stV gat →
      (hop2GameTier2TrackRed (ℓ := ℓ) C K Dh encPt encT decT idA idB lam M qep k).finish.eval
        (Env.cons (S := ASig) stV (.cons b' .nil)) =
      (pure gat.1.2.bad : Hop2Comp Pt Bool) := by
    intro stV gat b' ⟨⟨_, _, haux, _⟩, _⟩
    dsimp only [hop2GameTier2TrackRed]
    rw [comp_eval_ret, eval_auxBadTier2 (haux := haux) (ha := rfl)]
  rw [eval_eq_simulateQ_of_rel
    (R := hop2GameTier2TrackRed (ℓ := ℓ) C K Dh encPt encT decT idA idB lam M qep k)
    (Rel := Hop2Tier2TrackSimRel C K encT s chall)
    (initImpl := hop2InitBridgeTrackImplLocal (ℓ := ℓ) (Pt := Pt) C K Dh idA idB k)
    (so := so) (finishImpl := fun gat _ => (pure gat.1.2.bad : Hop2Comp Pt Bool))
    (qAdv := q) (x := (s, chall)) (hinit := hinit)
    (hU := fun u ⟨ga, trS⟩ => by
      dsimp only [so, flattenStateT, hop2ImplTrackHalted, extractPtPrfIface,
        _root_.ReductionDsl.atomicPrfIface]
      simp only [StateT.run_mk, StateT.run_lift]; rfl)
    (hstep := fun m sq stV gat hs =>
      hop2StepTier2TrackC_rel C K Dh encPt encT decT idA idB lam
        hinj hℓ M hM qep k m s chall sq stV gat hs)
    (hfin := hfin) (hmono := fun _ h => h) (A := fun _ => A)
    (hb := fun _ => isQueryBoundP_of_makesAtMostQueries hA)]
  unfold hop2GameTrackHalted hop2InitBridgeTrackImplLocal
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun _ => bind_congr fun _ => bind_congr fun _ =>
    bind_congr fun _ => bind_congr fun _ => bind_congr fun _ => ?_
  dsimp only [so]
  have hsim := simulateQ_flattenStateT (S₂ := KemFailSessionTrack C.F Bytes)
    (hop2ImplTrackHalted (ℓ := ℓ) P K Dh encT decT qep s hyb) A
  rw [hsim]
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  refine bind_congr fun x => by rcases x with ⟨⟨_, _, _⟩, _⟩; rfl

/-- Exact `evalSpkSwapPrgHybrid` agreement of `spkHop2PrgProgHaltedTier2` under `Injective encT`. -/
theorem spkHop2PrgProgHaltedTier2_eval (ℓ q qep k : ℕ) (s : BitVec 256)
    (A : Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hinj : Function.Injective encT)
    (hk : k < spkSwapHybridCount) (hA : MakesAtMostQueries A q) (hℓ : ℓ < 10 ^ 6) :
    evalSpkSwapPrgHybrid
        (spkHop2PrgProgHaltedTier2 (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k) s A =
      hop2PrgRedKTrackHalted
        (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
        K ℓ Dh encPt encT decT qep s k A := by
  funext chall
  have hk16 : k < 16 := Nat.lt_trans hk (by decide)
  dsimp only [evalSpkSwapPrgHybrid, hop2PrgRedKTrackHalted]
  simp only [spkHop2PrgProgHaltedTier2, hℓ, hk16, and_self, ↓reduceIte,
    spkHop2PrgProgHaltedTier2Real]
  let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  let prfReal : QueryImpl (prfSpec Pt (BitVec 256)) ProbComp := fun I =>
    (pure ((extractPRF P.C.F encPt).tag chall.1 I) : ProbComp (BitVec 256))
  rw [eval_redCoinToPrf _ prfReal, redCoinToPrf_hop2GameTier2TrackRed_prgCoinMode,
    hop2GameTier2TrackRed_eval C K Dh encPt encT decT idA idB lam hinj hℓ
      (prgLiftedMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
        (encPt := encPt) (encT := encT) (decT := decT) (lam := lam))
      (prgLiftedMode_evalSpec (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
        (encPt := encPt) (encT := encT) (decT := decT) (lam := lam))
      q qep k s chall A hA]
  rfl

theorem spkHop2PrgProgHaltedTier2_eval_of_dec (ℓ q qep k : ℕ) (s : BitVec 256)
    (A : Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hdec : ∀ T, decT (encT T) = some T)
    (hk : k < spkSwapHybridCount) (hA : MakesAtMostQueries A q) (hℓ : ℓ < 10 ^ 6) :
    evalSpkSwapPrgHybrid
        (spkHop2PrgProgHaltedTier2 (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k) s A =
      hop2PrgRedKTrackHalted
        (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
        K ℓ Dh encPt encT decT qep s k A := by
  have hinj : Function.Injective encT := fun a b h => by
    have ha := hdec a; rw [h, hdec b] at ha; exact (Option.some.inj ha).symm
  exact spkHop2PrgProgHaltedTier2_eval C K Dh encPt encT decT idA idB lam ℓ q qep k s A hinj hk hA hℓ

/-- Exact `evalSpkSwapPrfHybrid` agreement of `spkHop2PrfProgHaltedTier2` under `Injective encT`. -/
theorem spkHop2PrfProgHaltedTier2_eval (ℓ q qep k : ℕ) (s : BitVec 256)
    (A : Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hinj : Function.Injective encT)
    (hk : k < spkSwapHybridCount) (hA : MakesAtMostQueries A q) (hℓ : ℓ < 10 ^ 6) :
    evalSpkSwapPrfHybrid
        (spkHop2PrfProgHaltedTier2 (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k) s A =
      hop2PrfRedKTrackHalted
        (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
        K ℓ Dh encT decT qep s k A := by
  have hk16 : k < 16 := Nat.lt_trans hk (by decide)
  dsimp only [evalSpkSwapPrfHybrid]
  simp only [spkHop2PrfProgHaltedTier2, hℓ, hk16, and_self, ↓reduceIte]
  let RG := hop2GameTier2TrackRed (ℓ := ℓ) C K Dh encPt encT decT idA idB lam
    (prfOracleMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)) qep k
  have hinit :
      (hop2InitPrfTier2TrackC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k).eval
        (.cons s .nil) =
      (do
        let r ← hop2Unif (Pt := Pt)
        let c ← hop2Unif (Pt := Pt)
        RG.init.eval (.cons (s, (r, c)) .nil)) := by
    dsimp only [hop2InitPrfTier2TrackC, RG, hop2GameTier2TrackRed, prfOracleMode, compCoinToPrf]
    rw [compCoinToPrf_wk1Comp]
    simp only [comp_eval_bind, compCoinToPrf_eval_eq_liftM, draw256Coin_eval, wk1Comp_eval]
    rfl
  dsimp only [CostedReduction.eval, spkHop2PrfProgHaltedTier2Real, RG, hop2GameTier2TrackRed] at hinit ⊢
  rw [hinit]
  simp only [bind_assoc]
  unfold hop2PrfRedKTrackHalted
  refine bind_congr fun r => bind_congr fun c => ?_
  exact hop2GameTier2TrackRed_eval C K Dh encPt encT decT idA idB lam hinj hℓ
    (prfOracleMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam))
    prfOracleMode_evalSpec q qep k s (r, c) A hA

theorem spkHop2PrfProgHaltedTier2_eval_of_dec (ℓ q qep k : ℕ) (s : BitVec 256)
    (A : Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hdec : ∀ T, decT (encT T) = some T)
    (hk : k < spkSwapHybridCount) (hA : MakesAtMostQueries A q) (hℓ : ℓ < 10 ^ 6) :
    evalSpkSwapPrfHybrid
        (spkHop2PrfProgHaltedTier2 (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k) s A =
      hop2PrfRedKTrackHalted
        (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
        K ℓ Dh encT decT qep s k A := by
  have hinj : Function.Injective encT := fun a b h => by
    have ha := hdec a; rw [h, hdec b] at ha; exact (Option.some.inj ha).symm
  exact spkHop2PrfProgHaltedTier2_eval C K Dh encPt encT decT idA idB lam ℓ q qep k s A hinj hk hA hℓ

end Tier2TrackEval

end Computational.Proofs.Game.PromotedCostedReds.HaltedSpkHop2Tier2Eval
